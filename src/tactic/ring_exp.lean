/-
Copyright (c) 2019 Tim Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Tim Baanen.

Solve equations in commutative (semi)rings with exponents.
-/
import tactic.norm_num
import tactic.well_founded_tactics
/-!
  # ring_exp tactic

  A tactic for solving equations in commutative (semi)rings,
  where the exponents can also contain variables.

  More precisely, expressions of the following form are supported:
  - constants (non-negative integers)
  - variables
  - coefficients (any rational number, embedded into the (semi)ring)
  - addition of expressions
  - multiplication of expressions
  - exponentiation of expressions (the exponent must have type `ℕ`)
  - subtraction and negation of expressions (if the base is a full ring)

  The motivating example is proving `2 * 2^n * b = b * 2^(n+1)`,
  something that the `ring` tactic cannot do, but `ring_exp` can.

  ## Implementation notes

  The basic approach to prove equalities is to normalise both sides and check for equality.
  The normalisation is guided by building a value in the type `ex` at the meta level,
  together with a proof (at the base level) that the original value is equal to
  the normalised version.
  The normalised version and normalisation proofs are also stored in the `ex` type.

  The outline of the file:
  - Define an inductive family of types `ex`, parametrised over `ex_type`,
    which can represent expressions with `+`, `*`, `^` and rational numerals.
    The parametrisation over `ex_type` ensures that associativity and distributivity are applied,
    by restricting which kinds of subexpressions appear as arguments to the various operators.
  - Represent addition, multiplication and exponentiation in the `ex` type,
    thus allowing us to map expressions to `ex` (the `eval` function drives this).
    We apply associativity and distributivity of the operators here (helped by `ex_type`)
    and commutativity as well (but unfortunately not helped by anything).
    Any expression not of the above formats is treated as an atom (the same as a variable).

  There are some details we glossed over which make the plan more complicated:
  - The order on atoms is not initially obvious.
    We construct a list containing them in order of initial appearance in the expression,
    then use the index into the list as a key to order on.
  - In the tactic, a normalized expression `ps : ex` lives in the meta-world,
    but the normalization proofs live in the real world.
    Thus, we cannot directly say `ps.orig = ps.pretty` anywhere,
    but we have to carefully construct the proof when we compute `ps`.
    This was a major source of bugs in development!
  - For `pow`, the exponent must be a natural number, while the base can be any semiring `α`.
    We swap out operations for the base ring `α` with those for the exponent ring `ℕ`
    as soon as we deal with exponents.
    This is accomplished by the `in_exponent` function and is relatively painless since
    we work in a `reader` monad.
  - The normalized form of an expression is the one that is useful for the tactic,
    but not as nice to read. To remedy this, the user-facing normalization calls `ex.simp`.

  ## Caveats and future work

  Subtraction cancels out identical terms, but division does not.
  That is: `a - a = 0 := by ring_exp` solves the goal,
  but `a / a := 1 by ring_exp` doesn't.
  Note that `0 / 0` is generally defined to be `0`,
  so division cancelling out is not true in general.

  Multiplication of powers can be simplified a little bit further:
  `2 ^ n * 2 ^ n = 4 ^ n := by ring_exp` could be implemented
  in a similar way that `2 * a + 2 * a = 4 * a := by ring_exp` already works.
  This feature wasn't needed yet, so it's not implemented yet.
-/

namespace tactic.ring_exp
open nat

-- The base ring `α` will have a universe level `u`.
-- We do not introduce `α` as a variable yet,
-- in order to make it explicit or implicit as required.
universes u

/--
  The `atom` structure is used to represent atomic expressions:
  those which `ring_exp` cannot parse any further.

  For instance, `a + (a % b)` has `a` and `(a % b)` as atoms.
  The `ring_exp_eq` tactic does not normalize the subexpressions in atoms,
  but `ring_exp` does if `ring_exp_eq` was not sufficient.

  Atoms in fact represent equivalence classes of expressions,
  modulo definitional equality.
  The field `index : ℕ` should be a unique number for each class,
  while `value : expr` contains a representative of this class.
  The function `resolve_atom` determines the appropriate atom
  for a given expression.
-/
meta structure atom : Type := (value : expr) (index : ℕ)
namespace atom
/--
  The `eq` operation on `atom`s works modulo definitional equality,
  ignoring their `value`s.
  The invariants on `atom` ensure indices are unique per value.
  Thus, `eq` indicates equality as long as the `atom`s come from the same context.
-/
meta def eq (a b : atom) : bool := a.index = b.index
/--
  We order `atom`s on the order of appearance in the main expression.
-/
meta def lt (a b : atom) : bool := a.index < b.index
meta instance : has_repr atom := ⟨λ x, "(atom " ++ repr x.2 ++ ")"⟩
end atom

section expression
/-! In this section, we define the `ex` type and its basic operations.

  First, we introduce the supporting types `coeff`, `ex_type` and `ex_info`.
  For understanding the code, it's easier to check out `ex` itself first,
  then refer back to the supporting types.

  The arithmetic operations on `ex` need additional definitions,
  so they are defined in a later section.
-/

/--
  Coefficients in the expression are stored in a wrapper structure,
  allowing for easier modification of the data structures.
  The modifications might be caching of the result of `expr.of_rat`,
  or using a different meta representation of numerals.
-/
@[derive decidable_eq]
structure coeff : Type := (value {} : ℚ)

/--
  The `ex` type is structured according to a parameter `et : ex_type`.

  Instead of allowing each operand to have arbitrary subexpressions as argument,
  we have a single `ex_type` allowed for each argument.
  This e.g. enforces that `+` associates to the right,
  and `+` distributes over `*`.
  -/
inductive ex_type : Type
| base : ex_type
| sum : ex_type
| prod : ex_type
| exp : ex_type
open ex_type

/--
  Each `ex` stores information for its normalization proof.

  The `orig` expression is the expression that was passed to `eval`.

  The `pretty` expression is the normalised form that the `ex` represents.
  (I didn't call this something like `norm`, because there are already
  too many things called `norm` in mathematics!)

  The field `proof` contains an optional proof term of type `%%orig = %%pretty`.
  The value `none` for the proof indicates that everything reduces to reflexivity.
  (Which saves space in quite a lot of cases.)
-/
meta structure ex_info : Type :=
(orig : expr) (pretty : expr) (proof : option expr)

/--
  The `ex` type is an abstract representation of an expression with `+`, `*` and `^`.
  Those operators are mapped to the `sum`, `prod` and `exp` constructors respectively.

  The `zero` constructor is the base case for `ex sum`, e.g. `1 + 2` is represented
  by (something along the lines of) `sum 1 (sum 2 zero)`.

  The `coeff` constructor is the base case for `ex prod`, and is used for numerals.
  The code maintains the invariant that the coefficient is never `0`.

  The `var` constructor is the base case for `ex exp`, and is used for atoms.

  The `sum_b` constructor allows for addition in the base of an exponentiation;
  it serves a similar purpose as the parentheses in `(a + b)^c`.
  The code maintains the invariant that the argument to `sum_b` is not `zero`
  or `sum _ zero`.

  All of the constructors contain an `ex_info` field,
  used to carry around (arguments to) proof terms.

  While the `ex_type` parameter enforces some simplification invariants,
  the following ones must be manually maintained at the risk of insufficient power:
   - the argument to `coeff` must be nonzero (to ensure `0 = 0 * 1`)
   - the argument to `sum_b` must be of the form `sum a (sum b bs)` (to ensure `(a + 0)^n = a^n`)
   - normalisation proofs of subexpressions must be `refl ps.pretty`
   - if we replace `sum` with `cons` and `zero` with `nil`, the resulting list is sorted
     according to the `lt` relation defined further down; similarly for `prod` and `coeff`
     (to ensure `a + b = b + a`).

  The first two invariants could be encoded in a subtype of `ex`,
  but aren't (yet) to spare some implementation burden.
  The other invariants cannot be encoded because we need the `tactic` monad to check them.
  (For example, the correct equality check of `expr` is `is_def_eq : expr → expr → tactic unit`.)
-/
meta inductive ex : ex_type → Type
| zero  {} (info : ex_info) : ex sum
| sum   {} (info : ex_info) : ex prod → ex sum → ex sum
| coeff {} (info : ex_info) : coeff → ex prod
| prod  {} (info : ex_info) : ex exp → ex prod → ex prod
| var   {} (info : ex_info) : atom → ex base
| sum_b {} (info : ex_info) : ex sum → ex base
| exp   {} (info : ex_info) : ex base → ex prod → ex exp

/--
  Return the proof information associated to the `ex`.
-/
meta def ex.info : Π {et : ex_type} (ps : ex et), ex_info
| sum  (ex.zero  i)     := i
| sum  (ex.sum   i _ _) := i
| prod (ex.coeff i _)   := i
| prod (ex.prod  i _ _) := i
| base (ex.var   i _)   := i
| base (ex.sum_b i _)   := i
| exp  (ex.exp   i _ _) := i

/--
  Return the original, non-normalized version of this `ex`.

  Note that arguments to another `ex` are always "pre-normalized":
  their `orig` and `pretty` are equal, and their `proof` is reflexivity.
-/
meta def ex.orig {et : ex_type} (ps : ex et) : expr := ps.info.orig
/--
  Return the normalized version of this `ex`.
-/
meta def ex.pretty {et : ex_type} (ps : ex et) : expr := ps.info.pretty
/--
  Return the normalisation proof of the given expression.
  If the proof is `refl`, we give `none` instead,
  which helps to control the size of proof terms.
  To get an actual term, use `ex.proof_term`,
  or use `mk_proof` with the correct set of arguments.
-/
meta def ex.proof {et : ex_type} (ps : ex et) : option expr := ps.info.proof

/--
  Update the `orig` and `proof` fields of the `ex_info`.
  Intended for use in `ex.set_info`.
-/
meta def ex_info.set (i : ex_info) (o : option expr) (pf : option expr) : ex_info :=
-- TODO: is there an equivalent to Haskell's (maybe : α → option α → α)
{orig := match o with | none := i.pretty | (some o) := o end, proof := pf, .. i}

/--
  Update the `ex_info` of the given expression.

  We use this to combine intermediate normalisation proofs.
  Since `pretty` only depends on the subexpressions,
  which do not change, we do not set `pretty`.
-/
meta def ex.set_info : Π {et : ex_type} (ps : ex et), option expr → option expr → ex et
| sum  (ex.zero  i)      o pf := ex.zero  (i.set o pf)
| sum  (ex.sum   i p ps) o pf := ex.sum   (i.set o pf) p ps
| prod (ex.coeff i x)    o pf := ex.coeff (i.set o pf) x
| prod (ex.prod  i p ps) o pf := ex.prod  (i.set o pf) p ps
| base (ex.var   i x)    o pf := ex.var   (i.set o pf) x
| base (ex.sum_b i ps)   o pf := ex.sum_b (i.set o pf) ps
| exp  (ex.exp   i p ps) o pf := ex.exp   (i.set o pf) p ps

instance coeff_has_repr : has_repr coeff := ⟨λ x, repr x.1⟩

meta def ex.repr : Π {et : ex_type}, ex et → string
| sum  (ex.zero _)      := "0"
| sum  (ex.sum _ p ps)  := ex.repr p ++ " + " ++ ex.repr ps
| prod (ex.coeff _ x)   := repr x
| prod (ex.prod _ p ps) := ex.repr p ++ " * " ++ ex.repr ps
| base (ex.var _ x)     := repr x
| base (ex.sum_b _ ps)  := "(" ++ ex.repr ps ++ ")"
| exp  (ex.exp _ p ps)  := ex.repr p ++ " ^ " ++ ex.repr ps
meta instance {et : ex_type} : has_repr (ex et) := ⟨ex.repr⟩

/--
  Equality test for expressions.

  Since equivalence of `atom`s is not the same as equality,
  we cannot make a true `(=)` operator for `ex` either.
-/
meta def ex.eq : Π {et : ex_type}, ex et → ex et → bool
| sum  (ex.zero _)      (ex.zero _)      := tt
| sum  (ex.zero _)      (ex.sum _ _ _)   := ff
| sum  (ex.sum _ _ _)   (ex.zero _)      := ff
| sum  (ex.sum _ p ps)  (ex.sum _ q qs)  := p.eq q && ps.eq qs
| prod (ex.coeff _  x)  (ex.coeff _ y)   := x = y
| prod (ex.coeff _ _)   (ex.prod _ _ _)  := ff
| prod (ex.prod _ _ _)  (ex.coeff _ _)   := ff
| prod (ex.prod _ p ps) (ex.prod _ q qs) := p.eq q && ps.eq qs
| base (ex.var _ x)     (ex.var _ y)     := x.eq y
| base (ex.var _ _)     (ex.sum_b _ _)   := ff
| base (ex.sum_b _ _)   (ex.var _ _)     := ff
| base (ex.sum_b _ ps)  (ex.sum_b _ qs)  := ps.eq qs
| exp  (ex.exp _ p ps)  (ex.exp _ q qs)  := p.eq q && ps.eq qs

/--
  The ordering on expressions.

  As for `ex.eq`, this is a linear order only in one context.
-/
meta def ex.lt : Π {et : ex_type}, ex et → ex et → bool
| sum  _                (ex.zero _)      := ff
| sum  (ex.zero _)      _                := tt
| sum  (ex.sum _ p ps)  (ex.sum _ q qs)  := p.lt q || (p.eq q && ps.lt qs)
| prod _                (ex.coeff _ _)   := ff -- TODO: do we need to compare two coefficients?
| prod (ex.coeff _ _)   _                := tt
| prod (ex.prod _ p ps) (ex.prod _ q qs) := p.lt q || (p.eq q && ps.lt qs)
| base (ex.var _ x)     (ex.var _ y)     := x.lt y
| base (ex.var _ _)     (ex.sum_b _ _)   := tt
| base (ex.sum_b _ _)   (ex.var _ _)     := ff
| base (ex.sum_b _ ps)  (ex.sum_b _ qs)  := ps.lt qs
| exp  (ex.exp _ p ps)  (ex.exp _ q qs)  := p.lt q || (p.eq q && ps.lt qs)

end expression

section operations
/-!
  This section defines the operations (on `ex`) that use tactics.
  They live in the `ring_exp_m` monad,
  which adds a cache and a list of encountered atoms to the `tactic` monad.

  Throughout this section, we will be constructing proof terms.
  The lemmas used in the construction are all defined over a commutative semiring α.
-/
variables {α : Type u} [comm_semiring α]

open tactic
open ex_type

/--
  Stores the information needed in the `eval` function and its dependencies,
  so they can (re)construct expressions.

  The `eval_info` structure stores this information for one type,
  and the `context` combines the two types, one for bases and one for exponents.
-/
meta structure eval_info :=
  (α : expr) (univ : level)
  -- Cache the instances for optimization and consistency
  (csr_instance : expr) (ha_instance : expr) (hm_instance : expr) (hp_instance : expr)
  -- Optional instances (only required for (-) and (/) respectively)
  (cr_instance : option expr) (dr_instance : option expr)
  -- Cache common constants.
  (zero : expr) (one : expr)

/--
  The `context` contains the full set of information needed for the `eval` function.

  This structure has two copies of `eval_info`:
  one is for the base (typically some semiring `α`) and another for the exponent (always `ℕ`).
  When evaluating an exponent, we put `info_e` in `info_b`.
-/
meta structure context :=
  (info_b : eval_info) (info_e : eval_info)

/--
  The `ring_exp_m` monad is used instead of `tactic` to store the context.
-/
meta def ring_exp_m (α : Type) : Type := reader_t context (state_t (list atom) tactic) α

-- Basic operations on `ring_exp_m`:
meta instance : monad ring_exp_m := by { dunfold ring_exp_m, apply_instance }
meta instance : alternative ring_exp_m := by { dunfold ring_exp_m, apply_instance }
meta def get_context : ring_exp_m context := reader_t.read
meta def lift {α} (m : tactic α) : ring_exp_m α := reader_t.lift (state_t.lift m)

/--
  Change the context of the given computation,
  so that expressions are evaluated in the exponent ring,
  instead of the base ring.
-/
meta def in_exponent {α} (mx : ring_exp_m α) : ring_exp_m α := do
  ctx <- get_context,
  reader_t.lift $ mx.run ⟨ctx.info_e, ctx.info_e⟩

/--
  Specialized version of mk_app where the first two arguments are {α} [comm_semiring α].
  Should be faster because it can use the cached instances.
 -/
meta def mk_app_csr (f : name) (args : list expr) : ring_exp_m expr := do
  ctx <- get_context,
  pure $ (@expr.const tt f [ctx.info_b.univ] ctx.info_b.α ctx.info_b.csr_instance).mk_app args
/--
  Specialized version of `mk_app ``has_add.add`.
  Should be faster because it can use the cached instances.
  -/
  meta def mk_add (args : list expr) : ring_exp_m expr := do
  ctx <- get_context,
  pure $ (@expr.const tt ``has_add.add
    [ctx.info_b.univ]
    ctx.info_b.α
    ctx.info_b.ha_instance).mk_app args
/--
  Specialized version of `mk_app ``has_mul.mul`.
  Should be faster because it can use the cached instances.
  -/
  meta def mk_mul (args : list expr) : ring_exp_m expr := do
  ctx <- get_context,
  pure $ (@expr.const tt ``has_mul.mul
    [ctx.info_b.univ]
    ctx.info_b.α
    ctx.info_b.hm_instance).mk_app args
/--
  Specialized version of `mk_app ``has_pow.pow`.
  Should be faster because it can use the cached instances.
  -/
  meta def mk_pow (args : list expr) : ring_exp_m expr := do
  ctx <- get_context,
  pure $ (@expr.const tt ``has_pow.pow
    [ctx.info_b.univ, ctx.info_e.univ]
    ctx.info_b.α ctx.info_e.α
    ctx.info_b.hp_instance).mk_app args

/-- Construct a normalization proof term or return the cached one. -/
meta def ex_info.proof_term (ps : ex_info) : ring_exp_m expr :=
match ps.proof with
| none := lift $ tactic.mk_eq_refl ps.pretty
| (some p) := pure p
end
/-- Construct a normalization proof term or return the cached one. -/
meta def ex.proof_term {et : ex_type} (ps : ex et) : ring_exp_m expr := ps.info.proof_term

/--
  If all `ex_info` have trivial proofs, return a trivial proof.
  Otherwise, construct all proof terms.

  Useful in applications where trivial proofs combine to another trivial proof,
  most importantly to pass to `mk_proof_or_refl`.
-/
meta def none_or_proof_term : list ex_info → ring_exp_m (option (list expr))
| [] := pure none
| (x :: xs) := do
  xs_pfs <- none_or_proof_term xs,
  match (x.proof, xs_pfs) with
  | (none, none) := pure none
  | (some x_pf, none) := do
    xs_pfs <- traverse ex_info.proof_term xs,
    pure (some (x_pf :: xs_pfs))
  | (_, some xs_pfs) := do
    x_pf <- x.proof_term,
    pure (some (x_pf :: xs_pfs))
  end

/--
  Use the proof terms as arguments to the given lemma.
  If the lemma could reduce to reflexivity, consider using `mk_proof_or_refl.`
  -/
meta def mk_proof (lem : name) (args : list expr) (hs : list ex_info) : ring_exp_m expr := do
  hs' <- traverse ex_info.proof_term hs,
  mk_app_csr lem (args ++ hs')

/--
  Use the proof terms as arguments to the given lemma.
  Often, we construct a proof term using congruence where reflexivity suffices.
  To solve this, the following function tries to get away with reflexivity.
-/
meta def mk_proof_or_refl (term : expr) (lem : name) (args : list expr) (hs : list ex_info) :
ring_exp_m expr := do
  hs_full <- none_or_proof_term hs,
  match hs_full with
  | none := lift $ mk_eq_refl term
  | (some hs') := mk_app_csr lem (args ++ hs')
  end

/-- A shortcut for adding the original terms of two expressions. -/
meta def add_orig {et et'} (ps : ex et) (qs : ex et') : ring_exp_m expr :=
mk_add [ps.orig, qs.orig]
/-- A shortcut for multiplying the original terms of two expressions. -/
meta def mul_orig {et et'} (ps : ex et) (qs : ex et') : ring_exp_m expr :=
mk_mul [ps.orig, qs.orig]
/-- A shortcut for exponentiating the original terms of two expressions. -/
meta def pow_orig {et et'} (ps : ex et) (qs : ex et') : ring_exp_m expr :=
mk_pow [ps.orig, qs.orig]

/-- Congruence lemma for constructing `ex.sum`. -/
def sum_congr {p p' ps ps' : α} : p = p' → ps = ps' → p + ps = p' + ps' := by cc
/-- Congruence lemma for constructing `ex.prod`. -/
def prod_congr {p p' ps ps' : α} : p = p' → ps = ps' → p * ps = p' * ps' := by cc
/-- Congruence lemma for constructing `ex.exp`. -/
def exp_congr {p p' : α} {ps ps' : ℕ} : p = p' → ps = ps' → p ^ ps = p' ^ ps' := by cc

/-- Constructs `ex.zero` with the correct arguments. -/
meta def ex_zero : ring_exp_m (ex sum) := do
  ctx <- get_context,
  pure $ ex.zero ⟨ctx.info_b.zero, ctx.info_b.zero, none⟩
/-- Constructs `ex.sum` with the correct arguments. -/
meta def ex_sum (p : ex prod) (ps : ex sum) : ring_exp_m (ex sum) := do
  pps_o <- add_orig p ps,
  pps_p <- mk_add [p.pretty, ps.pretty],
  pps_pf <- mk_proof_or_refl pps_p ``sum_congr
    [p.orig, p.pretty, ps.orig, ps.pretty]
    [p.info, ps.info],
  pure (ex.sum ⟨pps_o, pps_p, pps_pf⟩ (p.set_info none none) (ps.set_info none none))
/--
  Constructs `ex.coeff` with the correct arguments.

  There are more efficient constructors for specific numerals:
  if `x = 0`, you should use `ex_zero`; if `x = 1`, use `ex_one`.
-/
meta def ex_coeff (x : rat) : ring_exp_m (ex prod) := do
  ctx <- get_context,
  x_p <- lift $ expr.of_rat ctx.info_b.α x,
  pure (ex.coeff ⟨x_p, x_p, none⟩ ⟨x⟩)
/--
  Constructs `ex.coeff 1` with the correct arguments.
  This is a special case for optimization purposes.
-/
meta def ex_one : ring_exp_m (ex prod) := do
  ctx <- get_context,
  pure $ ex.coeff ⟨ctx.info_b.one, ctx.info_b.one, none⟩ ⟨1⟩
/-- Constructs `ex.prod` with the correct arguments. -/
meta def ex_prod (p : ex exp) (ps : ex prod) : ring_exp_m (ex prod) := do
  pps_o <- mul_orig p ps,
  pps_p <- mk_mul [p.pretty, ps.pretty],
  pps_pf <- mk_proof_or_refl pps_p ``prod_congr
    [p.orig, p.pretty, ps.orig, ps.pretty]
    [p.info, ps.info],
  pure (ex.prod ⟨pps_o, pps_p, pps_pf⟩ (p.set_info none none) (ps.set_info none none))
/-- Constructs `ex.var` with the correct arguments. -/
meta def ex_var (p : atom) : ring_exp_m (ex base) := pure (ex.var ⟨p.1, p.1, none⟩ p)
/-- Constructs `ex.sum_b` with the correct arguments. -/
meta def ex_sum_b (ps : ex sum) : ring_exp_m (ex base) := do
  pure (ex.sum_b ps.info (ps.set_info none none))
/-- Constructs `ex.exp` with the correct arguments. -/
meta def ex_exp (p : ex base) (ps : ex prod) : ring_exp_m (ex exp) := do
  ctx <- get_context,
  pps_o <- pow_orig p ps,
  pps_p <- mk_pow [p.pretty, ps.pretty],
  pps_pf <- mk_proof_or_refl pps_p ``exp_congr
    [p.orig, p.pretty, ps.orig, ps.pretty]
    [p.info, ps.info],
  pure (ex.exp ⟨pps_o, pps_p, pps_pf⟩ (p.set_info none none) (ps.set_info none none))

lemma base_to_exp_pf {p p' : α} : p = p' → p = p' ^ 1 := by simp
/-- Conversion from `ex base` to `ex exp`. -/
meta def base_to_exp (p : ex base) : ring_exp_m (ex exp) := do
  o <- in_exponent $ ex_one,
  ps <- ex_exp p o,
  pf <- mk_proof ``base_to_exp_pf [p.orig, p.pretty] [p.info],
  pure $ ps.set_info p.orig pf
lemma exp_to_prod_pf {p p' : α} : p = p' → p = p' * 1 := by simp
/-- Conversion from `ex exp` to `ex prod`. -/
meta def exp_to_prod (p : ex exp) : ring_exp_m (ex prod) := do
  o <- ex_one,
  ps <- ex_prod p o,
  pf <- mk_proof ``exp_to_prod_pf [p.orig, p.pretty] [p.info],
  pure $ ps.set_info p.orig pf
lemma prod_to_sum_pf {p p' : α} : p = p' → p = p' + 0 := by simp
/-- Conversion from `ex prod` to `ex sum`. -/
meta def prod_to_sum (p : ex prod) : ring_exp_m (ex sum) := do
  z <- ex_zero,
  ps <- ex_sum p z,
  pf <- mk_proof ``prod_to_sum_pf [p.orig, p.pretty] [p.info],
  pure $ ps.set_info p.orig pf
lemma atom_to_sum_pf (p : α) : p = p ^ 1 * 1 + 0 := by simp
/--
  A more efficient conversion from `atom` to `ex sum`.

  The result should be the same as `ex_var p >>= base_to_exp >>= exp_to_prod >>= prod_to_sum`,
  except we need to calculate less intermediate steps.
-/
meta def atom_to_sum (p : atom) : ring_exp_m (ex sum) := do
  p' <- ex_var p,
  o <- in_exponent $ ex_one,
  p' <- ex_exp p' o,
  o <- ex_one,
  p' <- ex_prod p' o,
  z <- ex_zero,
  p' <- ex_sum p' z,
  pf <- mk_proof ``atom_to_sum_pf [p.1] [],
  pure $ p'.set_info p.1 pf

/--
  Compute the sum of two coefficients.
  Note that the result might not be a valid expression:
  if `p = -q`, then the result should be `ex.zero : ex sum` instead.
  The caller must detect when this happens!
  TODO: can we guarantee a valid expression?

  The returned value is of the form `ex.coeff _ (p + q)`,
  with the proof of `expr.of_rat p + expr.of_rat q = expr.of_rat (p + q)`.
-/
meta def add_coeff (p_p q_p : expr) (p q : coeff) : ring_exp_m (ex prod) := do
  ctx <- get_context,
  pq' <- mk_add [p_p, q_p],
  (pq_p, pq_pf) <- lift $ norm_num.derive pq',
  pure $ (ex.coeff ⟨pq_p, pq_p, pq_pf⟩ ⟨p.1 + q.1⟩)
/--
  Compute the product of two coefficients.

  The returned value is of the form `ex.coeff _ (p * q)`,
  with the proof of `expr.of_rat p * expr.of_rat q = expr.of_rat (p * q)`.
-/
meta def mul_coeff (p_p q_p : expr) (p q : coeff) : ring_exp_m (ex prod) := do
  ctx <- get_context,
  pq' <- mk_mul [p_p, q_p],
  (pq_p, pq_pf) <- lift $ norm_num.derive pq',
  pure $ (ex.coeff ⟨pq_p, pq_p, pq_pf⟩ ⟨p.1 * q.1⟩)

/--
  Represents the way in which two products are equal except coefficient.

  This type is used in the function `add_overlap`.
  In order to deal with equations of the form `a * 2 + a = 3 * a`,
  the `add` function will add up overlapping producs,
  turning `a * 2 + a` into `a * 3`.
  We need to distinguish `a * 2 + a` from `a * 2 + b` in order to do this,
  and the `overlap` type carrues the information on how it overlaps.

  The case `none` corresponds to non-overlapping products, e.g. `a * 2 + b`;
  the case `nonzero` to overlapping products adding to non-zero, e.g. `a * 2 + a`
  (the `ex prod` field will then look like `a * 3` with a proof that `a * 2 + a = a * 3`);
  the case `zero` to overlapping products adding to zero, e.g. `a * 2 + a * -2`.
  We distinguish those two cases because in the second, the whole product reduces to `0`.

  TODO: we can also do this for the base of exponents,
  e.g. to show `2^n * 2^n = 4^n`.
-/
meta inductive overlap : Type
| none {} : overlap
| nonzero : ex prod → overlap
| zero : ex sum → overlap

lemma add_overlap_pf {ps qs pq} (p : α) : ps + qs = pq → p * ps + p * qs = p * pq := λ pq_pf, calc
  p * ps + p * qs = p * (ps + qs) : symm (mul_add _ _ _)
  ... = p * pq : by rw pq_pf
lemma add_overlap_pf_zero {ps qs} (p : α) : ps + qs = 0 → p * ps + p * qs = 0 := λ pq_pf, calc
  p * ps + p * qs = p * (ps + qs) : symm (mul_add _ _ _)
  ... = p * 0 : by rw pq_pf
  ... = 0 : mul_zero _
/--
  Given arguments `ps`, `qs` of the form `ps' * x` and `ps' * y` respectively
  return `ps + qs = ps' * (x + y)` (with `x` and `y` arbitrary coefficients).
  For other arguments, return `overlap.none`.
-/
meta def add_overlap : ex prod → ex prod → ring_exp_m overlap
| (ex.coeff x_i x) (ex.coeff y_i y) := do
  xy@(ex.coeff _ xy_c) <- add_coeff x_i.pretty y_i.pretty x y
    | lift $ fail "internal error: add_coeff should return ex.coeff",
  if xy_c.1 = 0
  then do
    z <- ex_zero,
    pure $ overlap.zero (z.set_info xy.orig xy.proof)
  else pure $ overlap.nonzero xy
| (ex.prod _ _ _) (ex.coeff _ _) := pure overlap.none
| (ex.coeff _ _) (ex.prod _ _ _) := pure overlap.none
| pps@(ex.prod _ p ps) qqs@(ex.prod _ q qs) := if p.eq q
  then do
    pq_ol <- add_overlap ps qs,
    pqs_o <- add_orig pps qqs,
    match pq_ol with
    | overlap.none := pure overlap.none
    | (overlap.nonzero pq) := do
      pqs <- ex_prod p pq,
      pf <- mk_proof ``add_overlap_pf
        [ps.pretty, qs.pretty, pq.pretty, p.pretty]
        [pq.info],
      pure $ overlap.nonzero (pqs.set_info pqs_o pf)
    | (overlap.zero pq) := do
      z <- ex_zero,
      pf <- mk_proof ``add_overlap_pf_zero
        [ps.pretty, qs.pretty, p.pretty]
        [pq.info],
      pure $ overlap.zero (z.set_info pqs_o pf)
    end
  else pure overlap.none

section addition
lemma add_pf_z_sum {ps qs qs' : α} : ps = 0 → qs = qs' → ps + qs = qs' := λ ps_pf qs_pf, calc
  ps + qs = 0 + qs' : by rw [ps_pf, qs_pf]
  ... = qs' : zero_add _
lemma add_pf_sum_z {ps ps' qs : α} : ps = ps' → qs = 0 → ps + qs = ps' := λ ps_pf qs_pf, calc
  ps + qs = ps' + 0 : by rw [ps_pf, qs_pf]
  ... = ps' : add_zero _
lemma add_pf_sum_overlap {pps p ps qqs q qs pq pqs : α} :
  pps = p + ps → qqs = q + qs → p + q = pq → ps + qs = pqs → pps + qqs = pq + pqs := by cc
lemma add_pf_sum_overlap_zero {pps p ps qqs q qs pqs : α} :
  pps = p + ps → qqs = q + qs → p + q = 0 → ps + qs = pqs → pps + qqs = pqs :=
λ pps_pf qqs_pf pq_pf pqs_pf, calc
  pps + qqs = (p + ps) + (q + qs) : by rw [pps_pf, qqs_pf]
  ... = (p + q) + (ps + qs) : by simp
  ... = 0 + pqs : by rw [pq_pf, pqs_pf]
  ... = pqs : zero_add _
lemma add_pf_sum_lt {pps p ps qqs pqs : α} :
  pps = p + ps → ps + qqs = pqs → pps + qqs = p + pqs := by cc
lemma add_pf_sum_gt {pps qqs q qs pqs : α} :
  qqs = q + qs → pps + qs = pqs → pps + qqs = q + pqs := by cc
/--
  Add two expressions.

   * `0 + qs = 0`
   * `ps + 0 = 0`
   * `ps * x + ps * y = ps * (x + y)` (for `x`, `y` coefficients; uses `add_overlap`)
   * `(p + ps) + (q + qs) = p + (ps + (q + qs))` (if `p.lt q`)
   * `(p + ps) + (q + qs) = q + ((p + ps) + qs)` (if not `p.lt q`)
-/
meta def add : ex sum → ex sum → ring_exp_m (ex sum)
| ps@(ex.zero ps_i) qs := do
  pf <- mk_proof ``add_pf_z_sum [ps.orig, qs.orig, qs.pretty] [ps.info, qs.info],
  pqs_o <- add_orig ps qs,
  pure $ qs.set_info pqs_o pf
| ps qs@(ex.zero qs_i) := do
  pf <- mk_proof ``add_pf_sum_z [ps.orig, ps.pretty, qs.orig] [ps.info, qs.info],
  pqs_o <- add_orig ps qs,
  pure $ ps.set_info pqs_o pf
| pps@(ex.sum pps_i p ps) qqs@(ex.sum qqs_i q qs) := do
  ol <- add_overlap p q,
  ppqqs_o <- add_orig pps qqs,
  match ol with
  | (overlap.nonzero pq) := do
    pqs <- add ps qs,
    pqqs <- ex_sum pq pqs,
    qqs_pf <- qqs.proof_term,
    pf <- mk_proof ``add_pf_sum_overlap
      [pps.orig, p.pretty, ps.pretty, qqs.orig, q.pretty, qs.pretty, pq.pretty, pqs.pretty]
      [pps.info, qqs.info, pq.info, pqs.info],
    pure $ pqqs.set_info ppqqs_o pf
  | (overlap.zero pq) := do
    pqs <- add ps qs,
    pf <- mk_proof ``add_pf_sum_overlap_zero
      [pps.orig, p.pretty, ps.pretty, qqs.orig, q.pretty, qs.pretty, pqs.pretty]
      [pps.info, qqs.info, pq.info, pqs.info],
    pure $ pqs.set_info ppqqs_o pf
  | overlap.none := if p.lt q
  then do
    pqs <- add ps qqs,
    ppqs <- ex_sum p pqs,
    pf <- mk_proof ``add_pf_sum_lt
      [pps.orig, p.pretty, ps.pretty, qqs.orig, pqs.pretty]
      [pps.info, pqs.info],
    pure $ ppqs.set_info ppqqs_o pf
  else do
    pqs <- add pps qs,
    pqqs <- ex_sum q pqs,
    pf <- mk_proof ``add_pf_sum_gt
      [pps.orig, qqs.orig, q.pretty, qs.pretty, pqs.pretty]
      [qqs.info, pqs.info],
    pure $ pqqs.set_info ppqqs_o pf
  end
end addition

section multiplication
lemma mul_pf_c_c {ps ps' qs qs' pq : α} :
ps = ps' → qs = qs' → ps' * qs' = pq → ps * qs = pq := by cc
lemma mul_pf_c_prod {ps qqs q qs pqs : α} :
qqs = q * qs → ps * qs = pqs → ps * qqs = q * pqs := by cc
lemma mul_pf_prod_c {pps p ps qs pqs : α} :
pps = p * ps → ps * qs = pqs → pps * qs = p * pqs := by cc
lemma mul_pp_pf_prod_lt {pps p ps qqs pqs : α} :
  pps = p * ps → ps * qqs = pqs → pps * qqs = p * pqs := by cc
lemma mul_pp_pf_prod_gt {pps qqs q qs pqs : α} :
  qqs = q * qs → pps * qs = pqs → pps * qqs = q * pqs := by cc
/--
  Multiply two expressions.

  * `x * y = (x * y)` (for `x`, `y` coefficients)
  * `x * (q * qs) = q * (qs * x)` (for `x` coefficient)
  * `(p * ps) * y = p * (ps * y)` (for `y` coefficient)
  * `(p * ps) * (q * qs) = p * (ps * (q * qs))` (if `p.lt q`)
  * `(p * ps) * (q * qs) = q * ((p * ps) * qs)` (if not `p.lt q`)
-/
meta def mul_pp : ex prod → ex prod → ring_exp_m (ex prod)
| ps@(ex.coeff _ x) qs@(ex.coeff _ y) := do
  pq <- mul_coeff ps.pretty qs.pretty x y,
  pq_o <- mul_orig ps qs,
  pf <- mk_proof_or_refl pq.pretty ``mul_pf_c_c
    [ps.orig, ps.pretty, qs.orig, qs.pretty, pq.pretty]
    [ps.info, qs.info, pq.info],
  pure $ pq.set_info pq_o pf
| ps@(ex.coeff _ x) qqs@(ex.prod _ q qs) := do
  pqs <- mul_pp ps qs,
  pqqs <- ex_prod q pqs,
  pqqs_o <- mul_orig ps qqs,
  pf <- mk_proof ``mul_pf_c_prod
    [ps.orig, qqs.orig, q.pretty, qs.pretty, pqs.pretty]
    [qqs.info, pqs.info],
  pure $ pqqs.set_info pqqs_o pf
| pps@(ex.prod _ p ps) qs@(ex.coeff _ y) := do
  pqs <- mul_pp ps qs,
  ppqs <- ex_prod p pqs,
  ppqs_o <- mul_orig pps qs,
  pf <- mk_proof ``mul_pf_prod_c
    [pps.orig, p.pretty, ps.pretty, qs.orig, pqs.pretty]
    [pps.info, pqs.info],
  pure $ ppqs.set_info ppqs_o pf
| pps@(ex.prod _ p ps) qqs@(ex.prod _ q qs) := do
  ppqqs_o <- mul_orig pps qqs,
  if p.lt q
  then do
    pqs <- mul_pp ps qqs,
    ppqs <- ex_prod p pqs,
    pf <- mk_proof ``mul_pp_pf_prod_lt
      [pps.orig, p.pretty, ps.pretty, qqs.orig, pqs.pretty]
      [pps.info, pqs.info],
    pure $ ppqs.set_info ppqqs_o pf
  else do
    pqs <- mul_pp pps qs,
    pqqs <- ex_prod q pqs,
    pf <- mk_proof ``mul_pp_pf_prod_gt
      [pps.orig, qqs.orig, q.pretty, qs.pretty, pqs.pretty]
      [qqs.info, pqs.info],
    pure $ pqqs.set_info ppqqs_o pf

lemma mul_p_pf_zero {ps qs qs' : α} : ps = 0 → qs = qs' → ps * qs = 0 :=
λ ps_pf _, by rw [ps_pf, zero_mul]
lemma mul_p_pf_sum {pps p ps qs ppsqs : α} : pps = p + ps →
  p * qs + ps * qs = ppsqs → pps * qs = ppsqs := λ pps_pf ppsqs_pf, calc
  pps * qs = (p + ps) * qs : by rw [pps_pf]
  ... = p * qs + ps * qs : add_mul _ _ _
  ... = ppsqs : ppsqs_pf
/--
Multiply two expressions.

  * `0 * qs = 0`
  * `(p + ps) * qs = (p * qs) + (ps * qs)`
-/
meta def mul_p : ex sum → ex prod → ring_exp_m (ex sum)
| ps@(ex.zero ps_i) qs := do
  z <- ex_zero,
  z_o <- mul_orig ps qs,
  pf <- mk_proof ``mul_p_pf_zero [ps.orig, qs.orig, qs.pretty] [ps.info, qs.info],
  pure $ z.set_info z_o pf
| pps@(ex.sum pps_i p ps) qs := do
  pqs <- mul_pp p qs >>= prod_to_sum,
  psqs <- mul_p ps qs,
  ppsqs <- add pqs psqs,
  pps_pf <- pps.proof_term,
  ppsqs_o <- mul_orig pps qs,
  ppsqs_pf <- ppsqs.proof_term,
  pf <- mk_proof ``mul_p_pf_sum
    [pps.orig, p.pretty, ps.pretty, qs.orig, ppsqs.pretty]
    [pps.info, ppsqs.info],
  pure $ ppsqs.set_info ppsqs_o pf

lemma mul_pf_zero {ps ps' qs : α} : ps = ps' → qs = 0 → ps * qs = 0 :=
λ _ qs_pf, by rw [qs_pf, mul_zero]
lemma mul_pf_sum {ps qqs q qs psqqs : α} : qqs = q + qs → ps * q + ps * qs = psqqs →
  ps * qqs = psqqs := λ qs_pf psqqs_pf, calc
  ps * qqs = ps * (q + qs) : by rw [qs_pf]
  ... = ps * q + ps * qs : mul_add _ _ _
  ... = psqqs : psqqs_pf
/--
  Multiply two expressions.

  * `ps * 0 = 0`
  * `ps * (q + qs) = (ps * q) + (ps * qs)`
-/
meta def mul : ex sum → ex sum → ring_exp_m (ex sum)
| ps qs@(ex.zero qs_i) := do
  z <- ex_zero,
  z_o <- mul_orig ps qs,
  pf <- mk_proof ``mul_pf_zero
    [ps.orig, ps.pretty, qs.orig]
    [ps.info, qs.info],
  pure $ z.set_info z_o pf
| ps qqs@(ex.sum qqs_i q qs) := do
  psq <- mul_p ps q,
  psqs <- mul ps qs,
  psqqs <- add psq psqs,
  psqqs_o <- mul_orig ps qqs,
  pf <- mk_proof ``mul_pf_sum
    [ps.orig, qqs.orig, q.orig, qs.orig, psqqs.pretty]
    [qqs.info, psqqs.info],
  pure $ psqqs.set_info psqqs_o pf
end multiplication

section exponentiation
lemma pow_e_pf_exp {pps p : α} {ps qs psqs : ℕ} :
  pps = p ^ ps → ps * qs = psqs → pps ^ qs = p ^ psqs :=
λ pps_pf psqs_pf, calc
  pps ^ qs = (p ^ ps) ^ qs : by rw [pps_pf]
  ... = p ^ (ps * qs) : symm (pow_mul _ _ _)
  ... = p ^ psqs : by rw [psqs_pf]
/--
  Exponentiate two expressions.

  * `(p ^ ps) ^ qs = p ^ (ps * qs)`
-/
meta def pow_e : ex exp → ex prod → ring_exp_m (ex exp)
| pps@(ex.exp pps_i p ps) qs := do
  psqs <- in_exponent $ mul_pp ps qs,
  ppsqs <- ex_exp p psqs,
  ppsqs_o <- pow_orig pps qs,
  pf <- mk_proof ``pow_e_pf_exp
    [pps.orig, p.pretty, ps.pretty, qs.orig, psqs.pretty]
    [pps.info, psqs.info],
  pure $ ppsqs.set_info ppsqs_o pf

lemma pow_pp_pf_one {ps : α} {qs qs' : ℕ} : ps = 1 → qs = qs' → ps ^ qs = 1 :=
λ ps_pf _, by rw [ps_pf, _root_.one_pow]
lemma pow_pp_pf_c {ps ps' pqs : α} {qs qs' : ℕ} :
  ps = ps' → qs = qs' → ps' ^ qs' = pqs → ps ^ qs = pqs * 1 :=
by simp; cc
lemma pow_pp_pf_prod {pps p ps pqs psqs : α} {qs : ℕ} : pps = p * ps →
  p ^ qs = pqs → ps ^ qs = psqs → pps ^ qs = pqs * psqs :=
λ pps_pf pqs_pf psqs_pf, calc
    pps ^ qs = (p * ps) ^ qs : by rw [pps_pf]
    ... = p ^ qs * ps ^ qs : mul_pow _ _ _
    ... = pqs * psqs : by rw [pqs_pf, psqs_pf]
/--
  Exponentiate two expressions.

  * `1 ^ qs = 1`
  * `x ^ qs = x ^ qs` (for `x` coefficient)
  * `(p * ps) ^ qs = p ^ qs + ps ^ qs`
-/
meta def pow_pp : ex prod → ex prod → ring_exp_m (ex prod)
| ps@(ex.coeff ps_i ⟨⟨1, 1, _, _⟩⟩) qs := do
  o <- ex_one,
  o_o <- pow_orig ps qs,
  pf <- mk_proof ``pow_pp_pf_one [ps.orig, qs.orig, qs.pretty] [ps.info, qs.info],
  pure $ o.set_info o_o pf
| ps@(ex.coeff ps_i x) qs := do
  ps'' <- pure ps >>= prod_to_sum >>= ex_sum_b,
  pqs <- ex_exp ps'' qs,
  pqs_o <- pow_orig ps qs,
  pf <- mk_proof_or_refl pqs.pretty ``pow_pp_pf_c
    [ps.orig, ps.pretty, pqs.pretty, qs.orig, qs.pretty]
    [ps.info, qs.info, pqs.info],
  pqs' <- exp_to_prod pqs,
  pure $ pqs'.set_info pqs_o pf
| pps@(ex.prod pps_i p ps) qs := do
  pqs <- pow_e p qs,
  psqs <- pow_pp ps qs,
  ppsqs <- ex_prod pqs psqs,
  ppsqs_o <- pow_orig pps qs,
  pf <- mk_proof ``pow_pp_pf_prod
    [pps.orig, p.pretty, ps.pretty, pqs.pretty, psqs.pretty, qs.orig]
    [pps.info, pqs.info, psqs.info],
  pure $ ppsqs.set_info ppsqs_o pf

lemma pow_p_pf_one {ps ps' : α} {qs : ℕ} : ps = ps' → qs = succ zero → ps ^ qs = ps' :=
λ ps_pf qs_pf, calc
  ps ^ qs = ps' ^ 1 : by rw [ps_pf, qs_pf]
  ... = ps' : pow_one _
lemma pow_p_pf_zero {ps : α} {qs qs' : ℕ} : ps = 0 → qs = succ qs' → ps ^ qs = 0 :=
λ ps_pf qs_pf, calc
  ps ^ qs = 0 ^ (succ qs') : by rw [ps_pf, qs_pf]
  ... = 0 : zero_pow (succ_pos qs')
lemma pow_p_pf_succ {ps pqqs : α} {qs qs' : ℕ} :
  qs = succ qs' → ps * ps ^ qs' = pqqs → ps ^ qs = pqqs :=
λ qs_pf pqqs_pf, calc
  ps ^ qs = ps ^ succ qs' : by rw [qs_pf]
  ... = ps * ps ^ qs' : pow_succ _ _
  ... = pqqs : by rw [pqqs_pf]
lemma pow_p_pf_singleton {pps p pqs : α} {qs : ℕ} :
  pps = p + 0 → p ^ qs = pqs → pps ^ qs = pqs :=
λ pps_pf pqs_pf, by rw [pps_pf, add_zero, pqs_pf]
lemma pow_p_pf_cons {ps ps' : α} {qs qs' : ℕ} :
  ps = ps' → qs = qs' → ps ^ qs = ps' ^ qs' := by cc
/--
  Exponentiate two expressions.

  * `ps ^ 1 = ps`
  * `0 ^ qs = 0` (note that this is handled *after* `ps ^ 0 = 1`)
  * `ps ^ (qs + 1) = ps * ps ^ qs`
  * `(p + 0) ^ qs = ps ^ qs`
  * `ps ^ qs = ps ^ qs` (otherwise)
-/
meta def pow_p : ex sum → ex prod → ring_exp_m (ex sum)
| ps qs@(ex.coeff qs_i ⟨⟨1, 1, _, _⟩⟩) := do
  ps_o <- pow_orig ps qs,
  pf <- mk_proof ``pow_p_pf_one [ps.orig, ps.pretty, qs.orig] [ps.info, qs.info],
  pure $ ps.set_info ps_o pf
| ps@(ex.zero ps_i) qs@(ex.coeff qs_i y) := do
  z <- ex_zero,
  pf <- mk_proof ``pow_p_pf_zero [ps.orig, qs.orig, qs.pretty] [ps.info, qs.info],
  z_o <- pow_orig ps qs,
  pure $ z.set_info z_o pf
| ps qs@(ex.coeff qs_i ⟨⟨int.of_nat (succ n), 1, den_pos, _⟩⟩) := do
  qs' <- in_exponent $ ex_coeff ⟨int.of_nat n, 1, den_pos, coprime_one_right _⟩,
  pqs <- pow_p ps qs',
  pqqs <- mul ps pqs,
  pqqs_o <- pow_orig ps qs,
  pf <- mk_proof ``pow_p_pf_succ
    [ps.orig, pqqs.pretty, qs.orig, qs'.pretty]
    [qs.info, pqqs.info],
  pure $ pqqs.set_info pqqs_o pf
| pps@(ex.sum pps_i p (ex.zero _)) qqs := do
  pqs <- pow_pp p qqs,
  pqs_o <- pow_orig pps qqs,
  pf <- mk_proof ``pow_p_pf_singleton
    [pps.orig, p.pretty, pqs.pretty, qqs.orig]
    [pps.info, pqs.info],
  prod_to_sum $ pqs.set_info pqs_o pf
| pps qqs := do -- fallback: treat them as atoms
  pps' <- ex_sum_b pps,
  psqs <- ex_exp pps' qqs,
  psqs_o <- pow_orig pps qqs,
  pf <- mk_proof_or_refl psqs.pretty ``pow_p_pf_cons
    [pps.orig, pps.pretty, qqs.orig, qqs.pretty]
    [pps.info, qqs.info],
  exp_to_prod (psqs.set_info psqs_o pf) >>= prod_to_sum

lemma pow_pf_zero {ps ps' : α} {qs : ℕ} : ps = ps' → qs = 0 → ps ^ qs = 1 := λ _ qs_pf, calc
  ps ^ qs = ps ^ 0 : by rw [qs_pf]
  ... = 1 : pow_zero _
lemma pow_pf_sum {ps psqqs : α} {qqs q qs : ℕ} : qqs = q + qs →
  ps ^ q * ps ^ qs = psqqs → ps ^ qqs = psqqs := λ qqs_pf psqqs_pf, calc
    ps ^ qqs = ps ^ (q + qs) : by rw [qqs_pf]
    ... = ps ^ q * ps ^ qs : pow_add _ _ _
    ... = psqqs : psqqs_pf
/--
  Exponentiate two expressions.

  * `ps ^ 0 = 1`
  * `ps ^ (q + qs) = ps ^ q * ps ^ qs`
-/
meta def pow : ex sum → ex sum → ring_exp_m (ex sum)
| ps qs@(ex.zero qs_i) := do
  o <- ex_one,
  o_o <- pow_orig ps qs,
  pf <- mk_proof ``pow_pf_zero [ps.orig, ps.pretty, qs.orig] [ps.info, qs.info],
  prod_to_sum $ o.set_info o_o pf
| ps qqs@(ex.sum qqs_i q qs) := do
  psq <- pow_p ps q,
  psqs <- pow ps qs,
  psqqs <- mul psq psqs,
  psqqs_o <- pow_orig ps qqs,
  pf <- mk_proof ``pow_pf_sum
    [ps.orig, psqqs.pretty, qqs.orig, q.pretty, qs.pretty]
    [qqs.info, psqqs.info],
  pure $ psqqs.set_info psqqs_o pf
 end exponentiation

lemma simple_pf_sum_zero {p p' : α} : p = p' → p + 0 = p' := by simp
lemma simple_pf_prod_one {p p' : α} : p = p' → p * 1 = p' := by simp
lemma simple_pf_prod_neg_one [comm_ring α] {p p' : α} : p = p' → p * -1 = - p' := by simp
lemma simple_pf_var_one (p : α) : p ^ 1 = p := by simp
lemma simple_pf_exp_one {p p' : α} : p = p' → p ^ 1 = p' := by simp
/--
  Give a simpler, more human-readable representation of the normalized expression.

  Normalized expressions might have the form `a^1 * 1 + 0`,
  since the dummy operations reduce special cases in pattern-matching.
  Humans prefer to read `a` instead.
  This tactic gets rid of the dummy additions, multiplications and exponentiations.
-/
meta def ex.simple : Π {et : ex_type}, ex et → ring_exp_m (expr × expr)
| sum pps@(ex.sum pps_i p (ex.zero _)) := do
  (p_p, p_pf) <- p.simple,
  pf <- mk_app_csr ``simple_pf_sum_zero [p.pretty, p_p, p_pf],
  pure $ (p_p, pf)
| sum (ex.sum pps_i p ps) := do
  (p_p, p_pf) <- p.simple,
  (ps_p, ps_pf) <- ps.simple,
  pps_p <- mk_add [p_p, ps_p],
  pf <- mk_app_csr ``sum_congr [p.pretty, p_p, ps.pretty, ps_p, p_pf, ps_pf],
  pure $ (pps_p, pf)
| prod (ex.prod pps_i p (ex.coeff _ ⟨⟨1, 1, _, _⟩⟩)) := do
  (p_p, p_pf) <- p.simple,
  pf <- mk_app_csr ``simple_pf_prod_one [p.pretty, p_p, p_pf],
  pure $ (p_p, pf)
| prod pps@(ex.prod pps_i p (ex.coeff _ ⟨⟨-1, 1, _, _⟩⟩)) := do
  ctx <- get_context,
  match ctx.info_b.cr_instance with
  | none := do
    pf <- pps.proof_term,
    pure $ (pps.pretty, pf)
  | (some cri) := do
    (p_p, p_pf) <- p.simple,
    p' <- lift $ mk_app ``has_neg.neg [p_p],
    pf <- mk_app_csr ``simple_pf_prod_neg_one [cri, p.pretty, p_p, p_pf],
    pure $ (p', pf)
  end
| prod (ex.prod pps_i p ps) := do
  (p_p, p_pf) <- p.simple,
  (ps_p, ps_pf) <- ps.simple,
  pps_p <- mk_mul [p_p, ps_p],
  pf <- mk_app_csr ``prod_congr [p.pretty, p_p, ps.pretty, ps_p, p_pf, ps_pf],
  pure $ (pps_p, pf)
| base (ex.sum_b pps_i ps) := ps.simple
| exp (ex.exp pps_i p (ex.coeff _ ⟨⟨1, 1, _, _⟩⟩)) := do
  (p_p, p_pf) <- p.simple,
  pf <- mk_app_csr ``simple_pf_exp_one [p.pretty, p_p, p_pf],
  pure $ (p_p, pf)
| exp (ex.exp pps_i p ps) := do
  (p_p, p_pf) <- p.simple,
  (ps_p, ps_pf) <- in_exponent $ ps.simple,
  pps_p <- mk_pow [p_p, ps_p],
  pf <- mk_app_csr ``exp_congr [p.pretty, p_p, ps.pretty, ps_p, p_pf, ps_pf],
  pure $ (pps_p, pf)
| et ps := do
  pf <- ps.proof_term,
  pure $ (ps.pretty, pf)

/--
  Performs a lookup of the atom `a` in the list of known atoms,
  or allocates a new one.

  If `a` is not definitionally equal to any of the list's entries,
  a new atom is appended to the list and returned.
  The index of this atom is kept track of in the second inductive argument.

  This function is mostly useful in `resolve_atom`,
  which updates the state with the new list of atoms.
-/
meta def resolve_atoms (a : expr) : list atom → ℕ → ring_exp_m (atom × list atom)
| [] n := let atm : atom := ⟨a, n⟩ in pure (atm, [atm])
| bas@(b :: as) n := do
  (lift $ is_def_eq a b.value >> pure (b , bas)) <|> do
  (atm, as') <- resolve_atoms as (succ n),
  pure (atm, b :: as')

/--
  Convert the expression to an atom:
  either look up a definitionally equal atom,
  or allocate it as a new atom.

  You probably want to use `eval_base` if `eval` doesn't work
  instead of directly calling `resolve_atom`,
  since `eval_base` can also handle numerals.
-/
meta def resolve_atom (a : expr) : ring_exp_m atom := do
  atoms <- reader_t.lift $ state_t.get,
  (atm, atoms') <- resolve_atoms a atoms 0,
  reader_t.lift $ state_t.put atoms',
  pure atm

/--
  Treat the expression atomically: as a coefficient or atom.

  Handles cases where `eval` cannot treat the expression as a known operation
  because it is just a number or single variable.
-/
meta def eval_base (ps : expr) : ring_exp_m (ex sum) :=
match ps.to_rat with
| some ⟨0, 1, _, _⟩ := ex_zero
| some x := ex_coeff x >>= prod_to_sum
| none := do
  a <- resolve_atom ps,
  atom_to_sum a
end

lemma negate_pf {α} {ps ps' : α} [comm_ring α] : (-1) * ps = ps' → -ps = ps' := by simp
/--
  Negate an expression by multiplying with `-1`.

  Only works if there is a `comm_ring` instance; otherwise it will `fail`.
-/
meta def negate (ps : ex sum) : ring_exp_m (ex sum) := do
  ctx <- get_context,
  match ctx.info_b.cr_instance with
  | none := lift $ fail "internal error: negate called in semiring"
  | (some cr_instance) := do
    minus_one <- ex_coeff (-1) >>= prod_to_sum,
    ps' <- mul minus_one ps,
    ps_pf <- ps'.proof_term,
    -- We can't use mk_app at the next line because it would cause a timeout.
    pf <- lift $ to_expr ``(@negate_pf _ _ _ %%cr_instance %%ps_pf),
    ps'_o <- lift $ mk_app ``has_neg.neg [ps.orig],
    pure $ ps'.set_info ps'_o pf
  end

lemma inverse_pf [division_ring α] {ps ps_u ps_p e' e'' : α} :
  ps = ps_u → ps_u = ps_p → ps_p ⁻¹ = e' → e' = e'' → ps ⁻¹ = e'' :=
by cc
/--
  Invert an expression by simplifying, applying `has_inv.inv` and treating the result as an atom.

  Only works if there is a `division_ring` instance; otherwise it will `fail`.
-/
meta def inverse (ps : ex sum) : ring_exp_m (ex sum) := do
  ctx <- get_context,
  dri <- match ctx.info_b.dr_instance with
  | none := lift $ fail "division is only supported in a division ring"
  | (some dri) := pure dri
  end,
  (ps_simple, ps_simple_pf) <- ps.simple,
  e <- lift $ mk_app ``has_inv.inv [ps_simple],
  (e', e_pf) <- lift (norm_num.derive e) <|> ((λ e_pf, (e, e_pf)) <$> lift (mk_eq_refl e)),
  e'' <- eval_base e',
  ps_pf <- ps.proof_term,
  pf <- mk_proof_or_refl e''.pretty ``inverse_pf
    [dri, ps.orig, ps.pretty, ps_simple, e', e''.pretty, ps_pf, ps_simple_pf, e_pf]
    [e''.info],
  e''_o <- lift $ mk_app ``has_inv.inv [ps.orig],
  pure $ e''.set_info e''_o pf

lemma sub_pf [comm_ring α] {ps qs psqs : α} : ps + -qs = psqs → ps - qs = psqs := id
lemma div_pf [division_ring α] {ps qs psqs : α} : ps * qs⁻¹ = psqs → ps / qs = psqs := id

end operations

section wiring
/-!
  This section deals with going from `expr` to `ex` and back.

  The main attraction is `eval`, which uses `add`, `mul`, etc.
  to calculate an `ex` from a given `expr`.
  Other functions use `ex`es to produce `expr`s together with a proof,
  or produce the context to run `ring_exp_m` from an `expr`.
-/

open tactic
open ex_type

meta def eval : expr → ring_exp_m (ex sum)
| e@`(%%ps + %%qs) := do
  ps' <- eval ps,
  qs' <- eval qs,
  add ps' qs'
| e@`(%%ps - %%qs) := (do
  ctx <- get_context,
  cri <- match ctx.info_b.cr_instance with
  | none := lift $ fail "subtraction is not directly supported in a semiring"
  | (some cri) := pure cri
  end,
  ps' <- eval ps,
  qs' <- eval qs >>= negate,
  psqs <- add ps' qs',
  pf <- mk_proof_or_refl psqs.pretty ``sub_pf [cri, ps, qs, psqs.pretty] [psqs.info],
  pure (psqs.set_info e pf)) <|> eval_base e
| e@`(- %%ps) := (do
  ps' <- eval ps,
  negate ps') <|> eval_base e
| e@`(%%ps * %%qs) := do
  ps' <- eval ps,
  qs' <- eval qs,
  mul ps' qs'
| e@`(has_inv.inv %%ps) := (do
  ps' <- eval ps,
  inverse ps') <|> eval_base e
| e@`(%%ps / %%qs) := (do
  ctx <- get_context,
  dri <- match ctx.info_b.dr_instance with
  | none := lift $ fail "division is only directly supported in a division ring"
  | (some dri) := pure dri
  end,
  ps' <- eval ps,
  qs' <- eval qs >>= inverse,
  psqs <- mul ps' qs',
  pf <- mk_proof_or_refl psqs.pretty ``div_pf [dri, ps, qs, psqs.pretty] [psqs.info],
  pure (psqs.set_info e pf)) <|> eval_base e
| e@`(@has_pow.pow _ _ %%hp_instance %%ps %%qs) := (do
  has_pow_pf <-
  match hp_instance with
  | `(monoid.has_pow) := lift $ mk_eq_refl e
  | `(nat.has_pow) := lift $ mk_app ``nat.pow_eq_pow [ps, qs] >>= mk_eq_symm
  | _ := lift $ fail "has_pow instance must be nat.has_pow or monoid.has_pow"
  end,
  ps' <- eval ps,
  qs' <- in_exponent $ eval qs,
  psqs <- pow ps' qs',
  psqs_pf <- psqs.proof_term,
  pf <- lift $ mk_eq_trans has_pow_pf psqs_pf,
  pure $ psqs.set_info e pf) <|> eval_base e
| ps := eval_base ps

/--
  Run `eval` on the expression and return the result together with normalization proof.

  See also `eval_simple` if you want something that behaves like `norm_num`.
-/
meta def eval_with_proof (e : expr) : ring_exp_m (ex sum × expr) := do
  e' <- eval e,
  e_pf <- e'.proof_term,
  pure (e', e_pf)

/--
  Run `eval` on the expression and simplify the result.

  Returns a simplified normalized expression, together with an equality proof.

  See also `eval_with_proof` if you just want to check the equality of two expressions.
-/
meta def eval_simple (e : expr) : ring_exp_m (expr × expr) := do
  (complicated, complicated_pf) <- eval_with_proof e,
  (simple, simple_pf) <- complicated.simple,
  pf <- lift $ mk_eq_trans complicated_pf simple_pf,
  pure (simple, pf)

/-- Compute the `eval_info` for a given type `α`. -/
meta def make_eval_info (α : expr) : tactic eval_info := do
  u ← mk_meta_univ,
  infer_type α >>= unify (expr.sort (level.succ u)),
  u ← get_univ_assignment u,
  csr_instance ← mk_app ``comm_semiring [α] >>= mk_instance,
  cr_instance ← (some <$> (mk_app ``comm_ring [α] >>= mk_instance) <|> pure none),
  dr_instance ← (some <$> (mk_app ``division_ring [α] >>= mk_instance) <|> pure none),
  ha_instance ← mk_app ``has_add [α] >>= mk_instance,
  hm_instance ← mk_app ``has_mul [α] >>= mk_instance,
  hp_instance ← mk_mapp ``monoid.has_pow [some α, none],
  z ← mk_mapp ``has_zero.zero [α, none],
  o ← mk_mapp ``has_one.one [α, none],
  pure ⟨α, u, csr_instance, ha_instance, hm_instance, hp_instance, cr_instance, dr_instance, z, o⟩

/-- Use `e` to build the context for running `mx`. -/
meta def run_ring_exp {α} (e : expr) (mx : ring_exp_m α) : tactic α := do
  info_b <- infer_type e >>= make_eval_info,
  info_e <- mk_const ``nat >>= make_eval_info,
  (λ x : (_ × _), x.1) <$> (state_t.run (reader_t.run mx ⟨info_b, info_e⟩) [])

end wiring
end tactic.ring_exp

namespace tactic.interactive
open interactive interactive.types lean.parser tactic tactic.ring_exp
/-- Repeatedly apply `eval_simple` on (sub)expressions. -/
meta def normalize (e : expr) : tactic (expr × expr) := do
  (_, e', pf') ← ext_simplify_core () {}
  simp_lemmas.mk (λ _, failed) (λ _ _ _ _ e, do
    (e'', pf) <- run_ring_exp e $ eval_simple e,
    guard (¬ e'' =ₐ e),
    return ((), e'', some pf, ff))
  (λ _ _ _ _ _, failed) `eq e,
  pure (e', pf')

/-- Tactic for solving equations of *commutative* (semi)rings,
    allowing variables in the exponent.
    This version of `ring_exp` fails if the target is not an equality.
  -/
meta def ring_exp_eq : tactic unit := do
  `(eq %%ps %%qs) ← target >>= whnf,

  (ps', ps_pf, qs', qs_pf) <- run_ring_exp ps (do
    (ps', ps_pf) <- eval_with_proof ps,
    (qs', qs_pf) <- eval_with_proof qs,
    pure (ps', ps_pf, qs', qs_pf)),

  if ps'.eq qs'
  then do
    qs_pf_inv <- mk_eq_symm qs_pf,
    pf <- mk_eq_trans ps_pf qs_pf_inv,
    tactic.interactive.exact ``(%%pf)
  else do
    trace ps'.pretty,
    trace qs'.pretty,
    fail "ring_exp failed to prove equality"

/-- Tactic for solving equations of *commutative* (semi)rings,
    allowing variables in the exponent.
    This version of `ring_exp` fails if the target is not an equality.
  -/
meta def ring_exp (loc : parse location) : tactic unit :=
  match loc with
  | interactive.loc.ns [none] := ring_exp_eq
  | _ := failed
  end <|>
  do ns ← loc.get_locals,
  tt ← tactic.replace_at normalize ns loc.include_goal
  | fail "ring_exp failed to simplify",
  when loc.include_goal $ try tactic.reflexivity
end tactic.interactive
