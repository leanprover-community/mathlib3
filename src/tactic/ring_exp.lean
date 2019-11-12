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
  - exponentiation of expressions (the exponent must be a natural number)
  - subtraction and negation of expressions (if the base is a full ring)

  The motivating example is proving `2 * 2^n * b = b * 2^(n+1)`,
  something that the `ring` tactic cannot do, but `ring_exp` can.

  ## Implementation notes

  The basic approach to prove equalities is to normalise both sides and check for equality.
  The normalisation is guided by building a value in the type `ex` at the meta level,
  together with a proof (at the base level) that the unnormalised value is equal to
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
  - In the tactic, polynomials live in the meta-world, but the proofs live in the real world.
    Thus, we cannot directly say `ps = ps'.pretty` anywhere,
    but we have to carefully construct the proof when we compute `ps'`.
    This was a major source of bugs in development!
  - For `pow`, the exponent must be a natural number, while the base can be any semiring `α`.
    We swap out operations for `α` with those for `ℕ` as soon as we deal with exponents.
    This is accomplished by the `in_exponent` function and is relatively painless since
    we work in a `reader` monad.

  ## Caveats and future work
  
  Any subtraction (for non-rings) or division is treated as an atom,
  but we could at least normalise its subexpressions before doing so.

  The representation is less efficient than that used by `ring`,
  meaning you should probably try `ring` first, then apply this tactic if `ring` fails.
-/

universes u

-- We represent atoms as elements of a list of expressions.
namespace list
end list

namespace tactic.ring_exp
open nat

/- Define the `ex` type and its basic operations. -/

/-!
  Coefficients are stored in a wrapper structure, for easier modification of the data structures.
  The modifications might be caching of the result of `expr.of_rat`,
  or using a different meta representation of numerals.
-/
@[derive decidable_eq]
structure coeff : Type := (value {} : ℚ)

-- Values of `ex_type` are used in `ex` to e.g. enforce that + associates to the right.
inductive ex_type : Type
| base : ex_type
| sum : ex_type
| prod : ex_type
| exp : ex_type
open ex_type

/-!
  The `ex` type is an abstract representation of an expression with `+`, `*` and `^`.
  Those operators are mapped to the `sum`, `prod` and `exp` constructors respectively.
  The `zero` constructor is the base case for `ex sum`, e.g. `1 + 2` is represented
  by (something along the lines of) `sum 1 (sum 2 zero)`.
  The `coeff` constructor is the base case for `ex prod`, and is used for numerals.
  The `var` constructor is the base case for `ex exp`, and is used for variables (and other atoms).
  The `sum_b` constructor allows for addition in the base of an exponentiation;
  it serves a similar purpose as the parentheses in `(a + b)^c`.

  All of the constructors contain two expressions `pretty` and `proof`.
  The `pretty` expression is the normalised form that the `ex` represents.
  `proof` contains a proof term that the original expression equals the `pretty` expression.

  While the `ex_type` parameter enforces some simplification invariants,
  the following ones must be manually maintained at the risk of insufficient power:
   - the argument to `coeff` must be nonzero (to ensure `0 = 0 * 1`)
   - the argument to `sum_b` must be of the form `sum a (sum b bs)` (to ensure `(a + 0)^n = a^n`)
   - normalisation proofs of subexpressions must be `refl ps.pretty`
   - if we replace `sum` with `cons` and `zero` with `nil`, the resulting list is sorted
     according to the `lt` relation defined further down; similarly for `prod` and `coeff`
     (to ensure `a + b = b + a`).
  The first two invariants could be encoded in a subtype of `ex`,
  but aren't (yet) to spare some implementation burend.
  The other invariants cannot be encoded because we need the `tactic` monad to check them.
  (For example, the correct equality check of `expr` is `is_def_eq : expr → expr → tactic unit`.)
-/
meta inductive ex (α : Type u) : ex_type → Type u
| zero  {} (pretty proof : expr) : ex sum
| sum   {} (pretty proof : expr) : ex prod → ex sum → ex sum
| coeff {} (pretty proof : expr) : coeff → ex prod
| prod  {} (pretty proof : expr) : ex exp → ex prod → ex prod
| var   {} (pretty proof : expr) : α → ex base
| sum_b {} (pretty proof : expr) : ex sum → ex base
| exp   {} (pretty proof : expr) : ex base → ex prod → ex exp

/-!
  Return the normalised form of the given expression.
-/
meta def ex.pretty {α} : Π {et : ex_type} (ps : ex α et), expr
| sum (ex.zero ps_p _ ) := ps_p
| sum (ex.sum ps_p _ _ _) := ps_p
| prod (ex.coeff ps_p _ _) := ps_p
| prod (ex.prod ps_p _ _ _) := ps_p
| base (ex.var ps_p _ _) := ps_p
| base (ex.sum_b ps_p _ _) := ps_p
| exp (ex.exp ps_p _ _ _) := ps_p

/-!
  Return the normalisation proof of the given expression.
-/
meta def ex.proof {α} : Π {et : ex_type} (ps : ex α et), expr
| sum (ex.zero _ ps_pf) := ps_pf
| sum (ex.sum _ ps_pf _ _) := ps_pf
| prod (ex.coeff _ ps_pf _) := ps_pf
| prod (ex.prod _ ps_pf _ _) := ps_pf
| base (ex.var _ ps_pf _) := ps_pf
| base (ex.sum_b _ ps_pf _) := ps_pf
| exp (ex.exp _ ps_pf _ _) := ps_pf
/-!
  Setter for the normalisation proof of the given expression.
  We use this to combine intermediate normalisation proofs.
-/
meta def ex.set_proof {α} : Π {et : ex_type} (ps : ex α et), expr → ex α et
| sum (ex.zero ps_p ps_pf) pf := ex.zero ps_p pf
| sum (ex.sum ps_p ps_pf p ps) pf := ex.sum ps_p pf p ps
| prod (ex.coeff ps_p ps_pf x) pf := ex.coeff ps_p pf x
| prod (ex.prod ps_p ps_pf p ps) pf := ex.prod ps_p pf p ps
| base (ex.var ps_p ps_pf x) pf := ex.var ps_p pf x
| base (ex.sum_b ps_p ps_pf ps) pf := ex.sum_b ps_p pf ps
| exp (ex.exp ps_p ps_pf p ps) pf := ex.exp ps_p pf p ps

section instances
variables {α : Type u}

instance coeff_has_repr : has_repr coeff := ⟨λ x, repr x.1⟩

meta def ex.repr [has_repr α] : Π {et : ex_type}, ex α et → string
| sum (ex.zero _ _) := "0"
| sum (ex.sum _ _ p ps) := ex.repr p ++ "+" ++ ex.repr ps
| prod (ex.coeff _ _ x) := repr x
| prod (ex.prod _ _ p ps) := ex.repr p ++ "*" ++ ex.repr ps
| base (ex.var _ _ x) := repr x
| base (ex.sum_b _ _ ps) := "(" ++ ex.repr ps ++ ")"
| exp (ex.exp _ _ p ps) := ex.repr p ++ "^" ++ ex.repr ps
meta instance [has_repr α] {et : ex_type} : has_repr (ex α et) := ⟨ex.repr⟩

meta def ex.eq (eq : α → α → bool) : Π {et : ex_type}, ex α et → ex α et → bool
| sum (ex.zero _ _) (ex.zero _ _) := tt
| sum (ex.zero _ _) (ex.sum _ _ _ _) := ff
| sum (ex.sum _ _ _ _) (ex.zero _ _) := ff
| sum (ex.sum _ _ p ps) (ex.sum _ _ q qs) := p.eq q && ps.eq qs
| prod (ex.coeff _ _  x) (ex.coeff _ _ y) := x = y
| prod (ex.coeff _ _ _) (ex.prod _ _ _ _) := ff
| prod (ex.prod _ _ _ _) (ex.coeff _ _ _) := ff
| prod (ex.prod _ _ p ps) (ex.prod _ _ q qs) := p.eq q && ps.eq qs
| base (ex.var _ _ x) (ex.var _ _ y) := eq x y
| base (ex.var _ _ _) (ex.sum_b _ _ _) := ff
| base (ex.sum_b _ _ _) (ex.var _ _ _) := ff
| base (ex.sum_b _ _ ps) (ex.sum_b _ _ qs) := ps.eq qs
| exp (ex.exp _ _ p ps) (ex.exp _ _ q qs) := p.eq q && ps.eq qs

meta def ex.lt (eq lt : α → α → bool) : Π {et : ex_type}, ex α et → ex α et → bool
| sum ps (ex.zero _ _) := ff
| sum (ex.zero _ _) qs := tt
| sum (ex.sum _ _ p ps) (ex.sum _ _ q qs) := p.lt q || (p.eq eq q && ps.lt qs)
| prod ps (ex.coeff _ _ _) := ff
| prod (ex.coeff _ _ _) qs := tt
| prod (ex.prod _ _ p ps) (ex.prod _ _ q qs) := p.lt q || (p.eq eq q && ps.lt qs)
| base (ex.var _ _ x) (ex.var _ _ y) := lt x y
| base (ex.var _ _ _) (ex.sum_b _ _ _) := tt
| base (ex.sum_b _ _ _) (ex.var _ _ _) := ff
| base (ex.sum_b _ _ ps) (ex.sum_b _ _ qs) := ps.lt qs
| exp (ex.exp _ _ p ps) (ex.exp _ _ q qs) := p.lt q || (p.eq eq q && ps.lt qs)
end instances

meta structure atom : Type :=
(value : expr) (index : ℕ)
namespace atom
meta def eq (a b : atom) : bool := a.index = b.index
meta def lt (a b : atom) : bool := a.index < b.index
end atom

section operations
open tactic
/-!
  Stores the information needed in the `eval` function and its dependencies.

  The `eval_info` structure stores this information for one type.
-/
meta structure eval_info :=
  (α : expr) (csr_instance : expr) (cr_instance : option expr)
/-!
  The full set of information needed for the `eval` function.

  The `context` structure has two copies of `eval_info`:
  one is for the base (typically some semiring `α`) and another for the exponent (always `ℕ`).
  When evaluating an exponent, we put `info_e` in `info_b`.
-/
meta structure context :=
  (info_b : eval_info) (info_e : eval_info)
meta def ring_exp_m (α : Type) : Type := reader_t context (state_t (list atom) tactic) α

meta instance : monad ring_exp_m := by { dunfold ring_exp_m, apply_instance }
meta instance : alternative ring_exp_m := by { dunfold ring_exp_m, apply_instance }
meta def get_context : ring_exp_m context := reader_t.read
meta def lift {α} (m : tactic α) : ring_exp_m α :=
reader_t.lift (state_t.lift m)
meta def in_exponent {α} (mx : ring_exp_m α) : ring_exp_m α := do
  ctx <- get_context,
  reader_t.lift $ mx.run ⟨ctx.info_e, ctx.info_e⟩

variables {α : Type u} [comm_semiring α]

meta def ex_pf (et : ex_type) := ex atom et

-- Some useful congruence lemmas for simplifying.
def sum_congr {p p' ps ps' : α} : p = p' → ps = ps' → p + ps = p' + ps' := by cc
def prod_congr {p p' ps ps' : α} : p = p' → ps = ps' → p * ps = p' * ps' := by cc
def exp_congr {p p' : α} {ps ps' : ℕ} : p = p' → ps = ps' → p ^ ps = p' ^ ps' := by cc

def pretty_pf_sum_zero {p p' : α} : p = p' → p + 0 = p' := by simp
def pretty_pf_prod_one {p p' : α} : p = p' → p * 1 = p' := by simp
def pretty_pf_prod_neg_one [comm_ring α] {p p' : α} : p = p' → p * -1 = - p' := by simp
def pretty_pf_var_one (p : α) : p ^ 1 = p := by simp
def pretty_pf_exp_one {p p' : α} : p = p' → p ^ 1 = p' := by simp
-- Format an expression `e` nicely as `e_p`.
meta def ex.simple : Π {et : ex_type}, ex_pf et → ring_exp_m (expr × expr)
| sum pps@(ex.sum pps_p pps_pf p (ex.zero _ _)) := do
  (p_p, p_pf) <- p.simple,
  pf <- lift $ mk_app ``pretty_pf_sum_zero [p_pf],
  pure $ (p_p, pf)
| sum (ex.sum pps_p pps_pf p ps) := do
  (p_p, p_pf) <- p.simple,
  (ps_p, ps_pf) <- ps.simple,
  pps_p <- lift $ mk_app ``has_add.add [p_p, ps_p],
  pf <- lift $ mk_app ``sum_congr [p_pf, ps_pf],
  pure $ (pps_p, pf)
| prod (ex.prod pps_p pps_pf p (ex.coeff _ _ ⟨⟨1, 1, _, _⟩⟩)) := do
  (p_p, p_pf) <- p.simple,
  pf <- lift $ mk_app ``pretty_pf_prod_one [p_pf],
  pure $ (p_p, pf)
| prod (ex.prod pps_p pps_pf p (ex.coeff _ _ ⟨⟨-1, 1, _, _⟩⟩)) := do
  (p_p, p_pf) <- p.simple,
  p' <- lift $ mk_app ``has_neg.neg [p_p],
  pf <- lift $ mk_app ``pretty_pf_prod_neg_one [p_pf],
  pure $ (p', pf)
| prod (ex.prod pps_p pps_pf p ps) := do
  (p_p, p_pf) <- p.simple,
  (ps_p, ps_pf) <- ps.simple,
  pps_p <- lift $ mk_app ``has_mul.mul [p_p, ps_p],
  pf <- lift $ mk_app ``prod_congr [p_pf, ps_pf],
  pure $ (pps_p, pf)
| base (ex.sum_b pps_p pps_pf ps) := ps.simple
| exp (ex.exp pps_p pps_pf p (ex.coeff _ _ ⟨⟨1, 1, _, _⟩⟩)) := do
  (p_p, p_pf) <- p.simple,
  pf <- lift $ mk_app ``pretty_pf_exp_one [p_pf],
  pure $ (p_p, pf)
| exp (ex.exp pps_p pps_pf p ps) := do
  (p_p, p_pf) <- p.simple,
  (ps_p, ps_pf) <- in_exponent $ ps.simple,
  ctx <- get_context,
  m_hp <- lift $ mk_mapp ``monoid.has_pow [some ctx.info_b.α, none],
  pps_p <- lift $ mk_app ``has_pow.pow [m_hp, p_p, ps_p],
  pf <- lift $ mk_app ``exp_congr [p_pf, ps_pf],
  pure $ (pps_p, pf)
| et ps := do
  pure $ (ps.pretty, ps.proof)

-- Constructors for ex_pf that use the ring_exp_m monad to fill in the proofs.
meta def ex_zero : ring_exp_m (ex_pf sum) := do
  ctx <- get_context,
  x_p <- lift $ expr.of_rat ctx.info_b.α 0,
  x_pf <- lift $ mk_eq_refl x_p,
  pure (ex.zero x_p x_pf)
meta def ex_sum (p : ex_pf prod) (ps : ex_pf sum) : ring_exp_m (ex_pf sum) := do
  p_pf <- lift $ mk_eq_refl p.pretty,
  ps_pf <- lift $ mk_eq_refl ps.pretty,
  pps_p <- lift $ mk_app ``has_add.add [p.pretty, ps.pretty],
  pps_pf <- lift $ mk_app ``sum_congr [p.proof, ps.proof],
  pure (ex.sum pps_p pps_pf (p.set_proof p_pf) (ps.set_proof ps_pf))
meta def ex_coeff (x : rat) : ring_exp_m (ex_pf prod) := do
  ctx <- get_context,
  x_p <- lift $ expr.of_rat ctx.info_b.α x,
  x_pf <- lift $ mk_eq_refl x_p,
  pure (ex.coeff x_p x_pf ⟨x⟩)
meta def ex_one : ring_exp_m (ex_pf prod) := ex_coeff 1
meta def ex_prod (p : ex_pf exp) (ps : ex_pf prod) : ring_exp_m (ex_pf prod) := do
  p_pf <- lift $ mk_eq_refl p.pretty,
  ps_pf <- lift $ mk_eq_refl ps.pretty,
  pps_p <- lift $ mk_app ``has_mul.mul [p.pretty, ps.pretty],
  pps_pf <- lift $ mk_app ``prod_congr [p.proof, ps.proof],
  pure (ex.prod pps_p pps_pf (p.set_proof p_pf) (ps.set_proof ps_pf))
meta def ex_var (p : atom) : ring_exp_m (ex_pf base) := do
  pf <- lift $ mk_eq_refl p.1,
  pure (ex.var p.1 pf p)
meta def ex_sum_b (ps : ex_pf sum) : ring_exp_m (ex_pf base) := do
  ps_pf <- lift $ mk_eq_refl ps.pretty,
  pure (ex.sum_b ps.pretty ps.proof (ps.set_proof ps_pf))
meta def ex_exp (p : ex_pf base) (ps : ex_pf prod) : ring_exp_m (ex_pf exp) := do
  p_pf <- lift $ mk_eq_refl p.pretty,
  ps_pf <- lift $ mk_eq_refl ps.pretty,
  ctx <- get_context,
  m_hp <- lift $ mk_mapp ``monoid.has_pow [some ctx.info_b.α, none],
  pps_p <- lift $ mk_app ``has_pow.pow [m_hp, p.pretty, ps.pretty],
  pps_pf <- lift $ mk_app ``exp_congr [p.proof, ps.proof],
  pure (ex.exp pps_p pps_pf (p.set_proof p_pf) (ps.set_proof ps_pf))

def base_to_exp_pf {p ps' : α} : p ^ 1 = ps' → p = ps' := by simp
meta def base_to_exp (p : ex_pf base) : ring_exp_m (ex_pf exp) := do
  o <- in_exponent $ ex_one,
  ps <- ex_exp p o,
  pf <- lift $ mk_app ``base_to_exp_pf [ps.proof],
  pure $ ps.set_proof pf
def exp_to_prod_pf {p ps' : α} : p * 1 = ps' → p = ps' := by simp
meta def exp_to_prod (p : ex_pf exp) : ring_exp_m (ex_pf prod) := do
  o <- ex_one,
  ps <- ex_prod p o,
  pf <- lift $ mk_app ``exp_to_prod_pf [ps.proof],
  pure $ ps.set_proof pf
def prod_to_sum_pf {p ps' : α} : p + 0 = ps' → p = ps' := by simp
meta def prod_to_sum (p : ex_pf prod) : ring_exp_m (ex_pf sum) := do
  z <- ex_zero,
  ps <- ex_sum p z,
  pf <- lift $ mk_app ``prod_to_sum_pf [ps.proof],
  pure $ ps.set_proof pf

-- Make an expression with the sum/product of given coefficients.
meta def add_coeff (p q : coeff) : ring_exp_m (ex_pf prod) := do
  ctx <- get_context,
  p' <- lift $ expr.of_rat ctx.info_b.α p.1,
  q' <- lift $ expr.of_rat ctx.info_b.α q.1,
  pq' <- lift $ mk_app ``has_add.add [p', q'],
  (pq_p, pq_pf) <- lift $ norm_num pq',
  pure $ (ex.coeff pq_p pq_pf ⟨p.1 + q.1⟩)
meta def mul_coeff (p q : coeff) : ring_exp_m (ex_pf prod) := do
  ctx <- get_context,
  p' <- lift $ expr.of_rat ctx.info_b.α p.1,
  q' <- lift $ expr.of_rat ctx.info_b.α q.1,
  pq' <- lift $ mk_app ``has_mul.mul [p', q'],
  (pq_p, pq_pf) <- lift $ norm_num pq',
  pure $ (ex.coeff pq_p pq_pf ⟨p.1 * q.1⟩)

meta inductive overlap : Type
| none {} : overlap
| nonzero : ex_pf prod → overlap
| zero : ex_pf sum → overlap

-- If ps and qs are identical except coefficient, add them to make one expression.
-- TODO: we can also do this for the base of exponents.
def add_overlap_pf {ps qs pq} (p : α) : ps + qs = pq → p * ps + p * qs = p * pq := λ pq_pf, calc
  p * ps + p * qs = p * (ps + qs) : symm (mul_add _ _ _)
  ... = p * pq : by rw pq_pf
def add_overlap_pf_zero {ps qs} (p : α) : ps + qs = 0 → p * ps + p * qs = 0 := λ pq_pf, calc
  p * ps + p * qs = p * (ps + qs) : symm (mul_add _ _ _)
  ... = p * 0 : by rw pq_pf
  ... = 0 : mul_zero _
meta def add_overlap : ex_pf prod → ex_pf prod → ring_exp_m overlap
| (ex.coeff _ _ x) (ex.coeff _ _ y) := do
  xy@(ex.coeff _ _ xy_c) <- add_coeff x y | lift $ fail "internal error: add_coeff should return ex.coeff",
  if xy_c.1 = 0
  then do
    z <- ex_zero,
    pure $ (overlap.zero (z.set_proof xy.proof))
  else pure $ overlap.nonzero xy
| (ex.prod _ _ _ _) (ex.coeff _ _ _) := pure overlap.none
| (ex.coeff _ _ _) (ex.prod _ _ _ _) := pure overlap.none
| (ex.prod _ _ p ps) (ex.prod _ _ q qs) := if p.eq atom.eq q
  then do
    pq_ol <- add_overlap ps qs,
    match pq_ol with
    | overlap.none := pure overlap.none
    | (overlap.nonzero pq) := do
      pqs <- ex_prod p pq,
      pf <- lift $ mk_app ``add_overlap_pf [p.pretty, pq.proof],
      pure $ overlap.nonzero (pqs.set_proof pf)
    | (overlap.zero pq) := do
      z <- ex_zero,
      pf <- lift $ mk_app ``add_overlap_pf_zero [p.pretty, pq.proof],
      pure $ overlap.zero (z.set_proof pf)
    end
  else pure overlap.none

def add_pf_z_sum {ps qs qs' : α} : ps = 0 → qs = qs' → ps + qs = qs' := λ ps_pf qs_pf, calc
  ps + qs = 0 + qs' : by rw [ps_pf, qs_pf]
  ... = qs' : zero_add _
def add_pf_sum_z {ps ps' qs : α} : ps = ps' → qs = 0 → ps + qs = ps' := λ ps_pf qs_pf, calc
  ps + qs = ps' + 0 : by rw [ps_pf, qs_pf]
  ... = ps' : add_zero _
def add_pf_sum_overlap {pps p ps qqs q qs pq pqs : α} :
  pps = p + ps → qqs = q + qs → p + q = pq → ps + qs = pqs → pps + qqs = pq + pqs := by cc
def add_pf_sum_overlap_zero {pps p ps qqs q qs pqs : α} :
  pps = p + ps → qqs = q + qs → p + q = 0 → ps + qs = pqs → pps + qqs = pqs :=
λ pps_pf qqs_pf pq_pf pqs_pf, calc
  pps + qqs = (p + ps) + (q + qs) : by rw [pps_pf, qqs_pf]
  ... = (p + q) + (ps + qs) : by simp
  ... = 0 + pqs : by rw [pq_pf, pqs_pf]
  ... = pqs : zero_add _
def add_pf_sum_lt {pps p ps qqs q qs pqs : α} :
  pps = p + ps → qqs = q + qs → ps + qqs = pqs → pps + qqs = p + pqs := by cc
def add_pf_sum_gt {pps p ps qqs q qs pqs : α} :
  pps = p + ps → qqs = q + qs → pps + qs = pqs → pps + qqs = q + pqs := by cc
meta def add : ex_pf sum → ex_pf sum → ring_exp_m (ex_pf sum)
| (ex.zero ps_p ps_pf) qs := do
  pf <- lift $ mk_app ``add_pf_z_sum [ps_pf, qs.proof],
  pure $ qs.set_proof pf
| ps (ex.zero qs_p qs_pf) := do
  pf <- lift $ mk_app ``add_pf_sum_z [ps.proof, qs_pf],
  pure $ ps.set_proof pf
| pps@(ex.sum pps_p pps_pf p ps) qqs@(ex.sum qqs_p qqs_pf q qs) := do
  ol <- add_overlap p q,
  match ol with
  | (overlap.nonzero pq) := do
    pqs <- add ps qs,
    pqqs <- ex_sum pq pqs,
    pf <- lift $ mk_app ``add_pf_sum_overlap [pps_pf, qqs_pf, pq.proof, pqs.proof],
    pure $ pqqs.set_proof pf
  | (overlap.zero pq) := do
    pqs <- add ps qs,
    pf <- lift $ mk_app ``add_pf_sum_overlap_zero [pps_pf, qqs_pf, pq.proof, pqs.proof],
    pure $ pqs.set_proof pf
  | overlap.none := if p.lt atom.eq atom.lt q
  then do
    pqs <- add ps qqs,
    ppqs <- ex_sum p pqs,
    pf <- lift $ mk_app ``add_pf_sum_lt [pps_pf, qqs_pf, pqs.proof],
    pure $ ppqs.set_proof pf
  else do
    pqs <- add pps qs,
    pqqs <- ex_sum q pqs,
    pf <- lift $ mk_app ``add_pf_sum_gt [pps_pf, qqs_pf, pqs.proof],
    pure $ pqqs.set_proof pf
  end

-- TODO: this is the same structure as add, with some different names. Generalise?
def mul_pf_c_c {ps ps' qs qs' pq : α} : ps = ps' → qs = qs' → ps' * qs' = pq → ps * qs = pq := by cc
def mul_pf_c_prod {ps qqs q qs pqs : α} : qqs = q * qs → ps * qs = pqs → ps * qqs = q * pqs := by cc
def mul_pf_prod_c {pps p ps qs pqs : α} : pps = p * ps → ps * qs = pqs → pps * qs = p * pqs := by cc
def mul_pp_pf_prod_lt {pps p ps qqs q qs pqs : α} :
  pps = p * ps → qqs = q * qs → ps * qqs = pqs → pps * qqs = p * pqs := by cc
def mul_pp_pf_prod_gt {pps p ps qqs q qs pqs : α} :
  pps = p * ps → qqs = q * qs → pps * qs = pqs → pps * qqs = q * pqs := by cc
meta def mul_pp : ex_pf prod → ex_pf prod → ring_exp_m (ex_pf prod)
| (ex.coeff ps_p ps_pf x) (ex.coeff qs_p qs_pf y) := do
  pq <- mul_coeff x y,
  pf <- lift $ mk_app ``mul_pf_c_c [ps_pf, qs_pf, pq.proof],
  pure $ pq.set_proof pf
| ps@(ex.coeff ps_p ps_pf x) (ex.prod qqs_p qqs_pf q qs) := do
  pqs <- mul_pp ps qs,
  pqqs <- ex_prod q pqs,
  pf <- lift $ mk_app ``mul_pf_c_prod [qqs_pf, pqs.proof],
  pure $ pqqs.set_proof pf
| (ex.prod pps_p pps_pf p ps) qs@(ex.coeff qs_p qs_pf y) := do
  pqs <- mul_pp ps qs,
  ppqs <- ex_prod p pqs,
  pf <- lift $ mk_app ``mul_pf_prod_c [pps_pf, pqs.proof],
  pure $ ppqs.set_proof pf
| pps@(ex.prod pps_p pps_pf p ps) qqs@(ex.prod qqs_p qqs_pf q qs) := do
  if p.lt atom.eq atom.lt q
  then do
    pqs <- mul_pp ps qqs,
    ppqs <- ex_prod p pqs,
    pf <- lift $ mk_app ``mul_pp_pf_prod_lt [pps_pf, qqs_pf, pqs.proof],
    pure $ ppqs.set_proof pf
  else do
    pqs <- mul_pp pps qs,
    pqqs <- ex_prod q pqs,
    pf <- lift $ mk_app ``mul_pp_pf_prod_gt [pps_pf, qqs_pf, pqs.proof],
    pure $ pqqs.set_proof pf

def mul_p_pf_zero {ps qs qs' : α} : ps = 0 → qs = qs' → ps * qs = 0 := λ ps_pf qs_pf, calc
  ps * qs = 0 * qs' : by rw [ps_pf, qs_pf]
  ... = 0 : zero_mul _
def mul_p_pf_sum {pps p ps qs qs' ppsqs : α} : pps = p + ps → qs = qs' →
  p * qs + ps * qs = ppsqs → pps * qs = ppsqs := λ pps_pf qs_pf ppsqs_pf, calc
  pps * qs = (p + ps) * qs : by rw [pps_pf]
  ... = p * qs + ps * qs : add_mul _ _ _
  ... = ppsqs : ppsqs_pf
meta def mul_p : ex_pf sum → ex_pf prod → ring_exp_m (ex_pf sum)
| (ex.zero ps_p ps_pf) qs := do
  z <- ex_zero,
  pf <- lift $ mk_app ``mul_p_pf_zero [ps_pf, qs.proof],
  pure $ z.set_proof pf
| (ex.sum pps_p pps_pf p ps) qs := do
  pqs <- mul_pp p qs >>= prod_to_sum,
  psqs <- mul_p ps qs,
  ppsqs <- add pqs psqs,
  pf <- lift $ mk_app ``mul_p_pf_sum [pps_pf, qs.proof, ppsqs.proof],
  pure $ ppsqs.set_proof pf

def mul_pf_zero {ps ps' qs : α} : ps = ps' → qs = 0 → ps * qs = 0 := λ ps_pf qs_pf, calc
  ps * qs = ps' * 0 : by rw [ps_pf, qs_pf]
  ... = 0 : mul_zero _
def mul_pf_sum {ps ps' qqs q qs psqqs : α} : ps = ps' → qqs = q + qs →
  ps * q + ps * qs = psqqs → ps * qqs = psqqs := λ ps_pf qs_pf psqqs_pf, calc
  ps * qqs = ps * (q + qs) : by rw [qs_pf]
  ... = ps * q + ps * qs : mul_add _ _ _
  ... = psqqs : psqqs_pf
meta def mul : ex_pf sum → ex_pf sum → ring_exp_m (ex_pf sum)
| ps (ex.zero qs_p qs_pf) := do
  z <- ex_zero,
  pf <- lift $ mk_app ``mul_pf_zero [ps.proof, qs_pf],
  pure $ z.set_proof pf
| ps (ex.sum qqs_p qqs_pf q qs) := do
  psq <- mul_p ps q,
  psqs <- mul ps qs,
  psqqs <- add psq psqs,
  pf <- lift $ mk_app ``mul_pf_sum [ps.proof, qqs_pf, psqqs.proof],
  pure $ psqqs.set_proof pf

def pow_e_pf_var {pps p : α} {ps qs psqs : ℕ} : pps = p ^ ps → ps * qs = psqs → pps ^ qs = p ^ psqs := λ pps_pf psqs_pf, calc
  pps ^ qs = (p ^ ps) ^ qs : by rw [pps_pf]
  ... = p ^ (ps * qs) : symm (pow_mul _ _ _)
  ... = p ^ psqs : by rw [psqs_pf]
def pow_e_pf_exp {pps p : α} {ps qs psqs : ℕ} : pps = p ^ ps → ps * qs = psqs → pps ^ qs = p ^ psqs := λ pps_pf psqs_pf, calc
  pps ^ qs = (p ^ ps) ^ qs : by rw [pps_pf]
  ... = p ^ (ps * qs) : symm (pow_mul _ _ _)
  ... = p ^ psqs : by rw [psqs_pf]
meta def pow_e : ex_pf exp → ex_pf prod → ring_exp_m (ex_pf exp)
| (ex.exp pps_p pps_pf p ps) qs := do
  psqs <- in_exponent $ mul_pp ps qs,
  ppsqs <- ex_exp p psqs,
  pf <- lift $ mk_app ``pow_e_pf_exp [pps_pf, psqs.proof],
  pure $ ppsqs.set_proof pf

def pow_pp_pf_one {ps : α} {qs qs' : ℕ} : ps = 1 → qs = qs' → ps ^ qs = 1 := λ ps_pf qs_pf, calc
  ps ^ qs = 1 ^ qs' : by rw [ps_pf, qs_pf]
  ... = 1 : one_pow _
def pow_pp_pf_c {ps ps' pqs : α} {qs qs' : ℕ} : ps = ps' → qs = qs' → ps' ^ qs' = pqs → ps ^ qs = pqs := by cc
def pow_pp_pf_prod {pps p ps pqs psqs : α} {qs qs' : ℕ} : pps = p * ps → qs = qs' →
  p ^ qs = pqs → ps ^ qs = psqs → pps ^ qs = pqs * psqs := λ pps_pf qs_pf pqs_pf psqs_pf, calc
    pps ^ qs = (p * ps) ^ qs : by rw [pps_pf]
    ... = p ^ qs * ps ^ qs : mul_pow _ _ _
    ... = pqs * psqs : by rw [pqs_pf, psqs_pf]
meta def pow_pp : ex_pf prod → ex_pf prod → ring_exp_m (ex_pf prod)
| (ex.coeff ps_p ps_pf ⟨⟨1, 1, _, _⟩⟩) qs := do
  o <- ex_one,
  pf <- lift $ mk_app ``pow_pp_pf_one [ps_pf, qs.proof],
  pure $ o.set_proof pf
| (ex.coeff ps_p ps_pf x) qs := do
  ps' <- ex_coeff x.1,
  ps'' <- (prod_to_sum $ ps'.set_proof ps_pf) >>= ex_sum_b,
  pqs <- ex_exp ps'' qs,
  pf <- lift $ mk_app ``pow_pp_pf_c [ps_pf, qs.proof, pqs.proof],
  exp_to_prod $ pqs.set_proof pf
| (ex.prod pps_p pps_pf p ps) qs := do
  pqs <- pow_e p qs,
  psqs <- pow_pp ps qs,
  ppsqs <- ex_prod pqs psqs,
  pf <- lift $ mk_app ``pow_pp_pf_prod [pps_pf, qs.proof, pqs.proof, psqs.proof],
  pure $ ppsqs.set_proof pf

def pow_p_pf_one {ps ps' : α} {qs : ℕ} : ps = ps' → qs = succ zero → ps ^ qs = ps' := λ ps_pf qs_pf, calc
  ps ^ qs = ps' ^ 1 : by rw [ps_pf, qs_pf]
  ... = ps' : pow_one _
def pow_p_pf_zero {ps : α} {qs qs' : ℕ} : ps = 0 → qs = succ qs' → ps ^ qs = 0 := λ ps_pf qs_pf, calc
  ps ^ qs = 0 ^ (succ qs') : by rw [ps_pf, qs_pf]
  ... = 0 : zero_pow (succ_pos qs')
def pow_p_pf_succ {ps ps' pqqs : α} {qs qs' : ℕ} : ps = ps' → qs = succ qs' → ps * ps ^ qs' = pqqs → ps ^ qs = pqqs := λ ps_pf qs_pf pqqs_pf, calc
  ps ^ qs = ps ^ succ qs' : by rw [qs_pf]
  ... = ps * ps ^ qs' : pow_succ _ _
  ... = pqqs : by rw [pqqs_pf]
def pow_p_pf_singleton {pps p pqs : α} {qs : ℕ} : pps = p + 0 → p ^ qs = pqs → pps ^ qs = pqs := λ pps_pf pqs_pf, by rw [pps_pf, add_zero, pqs_pf]
def pow_p_pf_cons {ps ps' : α} {qs qs' : ℕ} : ps = ps' → qs = qs' → ps ^ qs = ps' ^ qs' := by cc
meta def pow_p : ex_pf sum → ex_pf prod → ring_exp_m (ex_pf sum)
| ps (ex.coeff qs_p qs_pf ⟨⟨1, 1, _, _⟩⟩) := do
  pf <- lift $ mk_app ``pow_p_pf_one [ps.proof, qs_pf],
  pure $ ps.set_proof pf
| (ex.zero ps_p ps_pf) (ex.coeff qs_p qs_pf y) := do
  z <- ex_zero,
  pf <- lift $ mk_app ``pow_p_pf_zero [ps_pf, qs_pf],
  pure $ z.set_proof pf
| ps (ex.coeff qs_p qs_pf ⟨⟨int.of_nat (succ n), 1, den_pos, _⟩⟩) := do
  qs' <- in_exponent $ ex_coeff ⟨int.of_nat n, 1, den_pos, coprime_one_right _⟩,
  pqs <- pow_p ps qs',
  pqqs <- mul ps pqs,
  pf <- lift $ mk_app ``pow_p_pf_succ [ps.proof, qs_pf, pqqs.proof],
  pure $ pqqs.set_proof pf
| (ex.sum pps_p pps_pf p (ex.zero _ _)) qqs := do
  pqs <- pow_pp p qqs,
  pf <- lift $ mk_app ``pow_p_pf_singleton [pps_pf, pqs.proof],
  prod_to_sum $ pqs.set_proof pf
| pps qqs := do -- fallback: treat them as atoms
  pps' <- ex_sum_b pps,
  pf <- lift $ mk_app ``pow_p_pf_cons [pps.proof, qqs.proof],
  psqs <- ex_exp  pps' qqs,
  exp_to_prod (psqs.set_proof pf) >>= prod_to_sum

def pow_pf_zero {ps ps' : α} {qs : ℕ} : ps = ps' → qs = 0 → ps ^ qs = 1 := λ ps_pf qs_pf, calc
  ps ^ qs = ps' ^ 0 : by rw [ps_pf, qs_pf]
  ... = 1 : pow_zero _
def pow_pf_sum {ps ps' psqqs : α} {qqs q qs : ℕ} : ps = ps' → qqs = q + qs →
  ps ^ q * ps ^ qs = psqqs → ps ^ qqs = psqqs := λ ps_pf qqs_pf psqqs_pf, calc
    ps ^ qqs = ps ^ (q + qs) : by rw [qqs_pf]
    ... = ps ^ q * ps ^ qs : pow_add _ _ _
    ... = psqqs : psqqs_pf
meta def pow : ex_pf sum → ex_pf sum → ring_exp_m (ex_pf sum)
| ps (ex.zero qs_p qs_pf) := do
  o <- ex_one,
  pf <- lift $ mk_app ``pow_pf_zero [ps.proof, qs_pf],
  prod_to_sum $ o.set_proof pf
| ps (ex.sum qqs_p qqs_pf q qs) := do
  psq <- pow_p ps q,
  psqs <- pow ps qs,
  psqqs <- mul psq psqs,
  pf <- lift $ mk_app ``pow_pf_sum [ps.proof, qqs_pf, psqqs.proof],
  pure $ psqqs.set_proof pf

def negate_pf {α} {ps ps' : α} [comm_ring α] : (-1) * ps = ps' → -ps = ps' := by simp
meta def negate (ps : ex_pf sum) : ring_exp_m (ex_pf sum) := do
  ctx <- get_context,
  match ctx.info_b.cr_instance with
  | (some cr_instance) := do
    minus_one <- ex_coeff (-1) >>= prod_to_sum,
    ps' <- mul minus_one ps,
    -- We can't use mk_app at the next line because it would cause a timeout.
    pf <- lift $ to_expr ``(@negate_pf _ _ _ %%cr_instance %%ps'.proof),
    pure $ ps'.set_proof pf
  | none := lift $ fail "internal error: negate called in semiring"
  end
end operations

open tactic
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
 -/
meta def resolve_atom (a : expr) : ring_exp_m atom := do
  atoms <- reader_t.lift $ state_t.get,
  (atm, atoms') <- resolve_atoms a atoms 0,
  reader_t.lift $ state_t.put atoms',
  pure atm

def sub_pf {α} [comm_ring α] {ps qs psqs : α} : ps + -qs = psqs → ps - qs = psqs := by simp
def divide_pf {α} [has_div α] {ps qs ps_u qs_u ps_p qs_p e' e'' : α} :
  ps = ps_u → qs = qs_u → ps_u = ps_p → qs_u = qs_p → ps_p / qs_p = e' → e' = e'' → ps / qs = e''
:= by cc

meta def eval_atom (ps : expr) : ring_exp_m (ex_pf sum) :=
  match ps.to_rat with
  | some ⟨0, 1, _, _⟩ := ex_zero
  | some x := ex_coeff x >>= prod_to_sum
  | none := do
    a <- resolve_atom ps,
    ex_var a >>= base_to_exp >>= exp_to_prod >>= prod_to_sum
  end

meta def eval : expr → ring_exp_m (ex_pf sum)
| `(%%ps + %%qs) := do
  ps' <- eval ps,
  qs' <- eval qs,
  add ps' qs'
| e@`(%%ps - %%qs) := (do
  ps' <- eval ps,
  qs' <- eval qs >>= negate,
  psqs <- add ps' qs',
  pf <- lift $ mk_app ``sub_pf [psqs.proof],
  pure (psqs.set_proof pf)) <|> eval_atom e
| `(- %%ps) := eval ps >>= λ ps', negate ps' <|> eval_atom ps
| `(%%ps * %%qs) := do
  ps' <- eval ps,
  qs' <- eval qs,
  mul ps' qs'
| `(%%ps / %%qs) := do
  ps_ugly <- eval ps,
  qs_ugly <- eval qs,
  (ps_pretty, ps_pretty_pf) <- ps_ugly.simple,
  (qs_pretty, qs_pretty_pf) <- qs_ugly.simple,
  e <- lift $ mk_app ``has_div.div [ps_pretty, qs_pretty],
  (e', e_pf) <- lift (norm_num.derive e) <|> ((λ e_pf, (e, e_pf)) <$> lift (mk_eq_refl e)),
  e'' <- eval_atom e',
  pf <- lift $ mk_app ``divide_pf [ps_ugly.proof, qs_ugly.proof, ps_pretty_pf, qs_pretty_pf, e_pf, e''.proof],
  pure $ e''.set_proof pf
| p'@`(@has_pow.pow _ _ %%hp_instance %%ps %%qs) := (do
  has_pow_pf <-
  match hp_instance with
  | `(monoid.has_pow) := lift $ mk_eq_refl p'
  | `(nat.has_pow) := lift $ mk_app ``nat.pow_eq_pow [ps, qs] >>= mk_eq_symm
  | _ := lift $ fail "unsupported has_pow instance"
  end,
  ps' <- eval ps,
  qs' <- in_exponent $ eval qs,
  psqs <- pow ps' qs',
  pf <- lift $ mk_eq_trans has_pow_pf psqs.proof,
  pure $ psqs.set_proof pf) <|> eval_atom ps
| ps := eval_atom ps

meta def make_eval_info (α : expr) : tactic eval_info := do
  csr_instance ← mk_app ``comm_semiring [α] >>= mk_instance,
  cr_instance ← (some <$> (mk_app ``comm_ring [α] >>= mk_instance) <|> pure none),
  pure (eval_info.mk α csr_instance cr_instance)

meta def run_ring_exp {α} (e : expr) (mx : ring_exp_m α) : tactic α := do
  info_b <- infer_type e >>= make_eval_info,
  info_e <- mk_const ``nat >>= make_eval_info,
  (λ x : (_ × _), x.1) <$> (state_t.run (reader_t.run mx ⟨info_b, info_e⟩) [])

end tactic.ring_exp

namespace tactic.interactive
open interactive interactive.types lean.parser tactic tactic.ring_exp
meta def normalize (e : expr) : tactic (expr × expr) := do
  (_, e', pf') ← ext_simplify_core () {}
  simp_lemmas.mk (λ _, failed) (λ _ _ _ _ e, do
    ugly <- run_ring_exp e $ eval e,
    (pretty, pf_pretty) <- run_ring_exp e $ ex.simple ugly,
    guard (¬ pretty =ₐ e),
    pf <- mk_eq_trans ugly.proof pf_pretty,
    return ((), pretty, some pf, ff))
  (λ _ _ _ _ _, failed) `eq e,
  pure (e', pf')

/-- Tactic for solving equations of *commutative* (semi)rings,
    allowing variables in the exponent.
    This version of `ring_exp` fails if the target is not an equality.
  -/
meta def ring_exp_eq : tactic unit := do
  `(eq %%ps %%qs) ← target >>= whnf,

  (ps', qs') <- run_ring_exp ps (do
    ps' <- eval ps,
    qs' <- eval qs,
    pure (ps' , qs')),

  if ps'.eq atom.eq qs'
  then do
    qs_pf_inv <- mk_eq_symm qs'.proof,
    pf <- mk_eq_trans ps'.proof qs_pf_inv,
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
  | trace "ring_exp failed to simplify" >> failed,
  when loc.include_goal $ try tactic.reflexivity
end tactic.interactive

set_option trace.app_builder true
-- Tests for addition.
example (a b : ℚ) : a = a := by ring_exp
example (a b : ℚ) : a + b = a + b := by ring_exp
example (a b : ℚ) : b + a = a + b := by ring_exp
example (a b : ℤ) : a + b + b = b + (a + b) := by ring_exp
example (a b c : ℕ) : a + b + b + (c + c) = c + (b + c) + (a + b) := by ring_exp
-- Tests for constants.
example (a : ℕ) : a + 5 + 5 = 0 + a + 10 := by ring_exp
example (a : ℤ) : a + 5 + 5 = 0 + a + 10 := by ring_exp
-- Tests for multiplication.
example (a : ℕ) : 0 = a * 0 := by ring_exp_eq
example (a : ℕ) : a = a * 1 := by ring_exp
example (a : ℕ) : a + a = a * 2 := by ring_exp
example (a b : ℤ) : a * b = b * a := by ring_exp
example (a b : ℕ) : a * 4 * b + a = a * (4 * b + 1) := by ring_exp
-- Tests for exponentiation.
example : 0 ^ 1 = 0 := by ring_exp
example (a : ℕ) : a ^ 0 = 1 := by ring_exp
example (a : ℕ) : a ^ 1 = a := by ring_exp
example (a : ℕ) : a ^ 2 = a * a := by ring_exp
example (a b : ℕ) : a ^ b = a ^ b := by ring_exp
example (a b : ℕ) : a ^ (b + 1) = a * a ^ b := by ring_exp
example (n : ℕ) (a m : ℕ) : a * a^n * m = a^(n+1) * m := by ring_exp
example (n : ℕ) (a m : ℕ) : m * a^n * a = a^(n+1) * m := by ring_exp
example (n : ℕ) (a m : ℤ) : a * a^n * m = a^(n+1) * m := by ring_exp
example (n : ℕ) (m : ℤ) : 2 * 2^n * m = 2^(n+1) * m := by ring_exp
example (n : ℕ) (m : ℤ) : 2^(n+1) * m = 2 * 2^n * m := by ring_exp
example (n m : ℕ) (a : ℤ) : (a ^ n)^m = a^(n * m) := by ring_exp
example (n m : ℕ) (a : ℤ) : a^(n^0) = a^1 := by ring_exp
example (n : ℕ) : 0^(n + 1) = 0 := by ring_exp
-- Powers of sums
example (a b : ℤ) : (a + b)^2 = a^2 + b^2 + a * b + b * a := by ring_exp
example (a b : ℤ) (n : ℕ) : (a + b)^(n + 2) = (a^2 + b^2 + a * b + b * a) * (a + b)^n := by ring_exp
-- Coefficients and negation
example (a : ℚ) : (1/2) * a + (1/2) * a = a := by ring_exp
example {α} [comm_ring α] (a : α) : a - a = 0 := by ring_exp_eq
example (a : ℤ) : a - a = 0 := by ring_exp
example (a : ℤ) : a + - a = 0 := by ring_exp
example (a : ℤ) : - a = (-1) * a := by ring_exp
example (a b : ℕ) : a - b + a + a = a - b + 2 * a := by ring_exp -- Here, (a - b) is treated as an atom.

example {α} [comm_ring α] (a b c : α) : b ^ 0 = 1 := by ring_exp_eq
example {α} [comm_ring α] (a b c : α) : b ^ 2 - 4 * a * c = 4 * a * 0 + b * b - 4 * a * c := by ring_exp_eq
constant f {α} : α → α
example {α : Type} [linear_ordered_field α] (x : α) :
  2 * x + 1 * 1 - (2 * f (x + 1 / 2) + 2 * 1) + (1 * 1 - (2 * x - 2 * f (x + 1 / 2))) = 0
:= by ring_exp_eq
example {α : Type u} [linear_ordered_field α] (x : α) :
  f (x + 1 / 2) ^ 1 * -2 + (f (x + 1 / 2) ^ 1 * 2 + 0) = 0
:= by ring_exp_eq

example {α} [linear_ordered_field α] (a b c : α) : a*(-c/b)*(-c/b) + b*(-c/b) + c = a*((c/b)*(c/b)) := by ring_exp

/-
-- Counterexamples:
example : 0 = 1 := by ring_exp
example : 10 = 1 := by ring_exp
example (a : ℕ) : a = 1 := by ring_exp
example (a b : ℕ) : a = b := by ring_exp
example (a b : ℕ) : a + b = a := by ring_exp
example (a b : ℕ) : a + b = a * b := by ring_exp
example (a b : ℕ) : a ^ 2 + b ^ 2 = (a + b)^2 := by ring_exp
example (a b n : ℕ) : (a + b)^n = a^n + b^n := by ring_exp

-- This also includes constants as the base (which is harder to fix):
example (n : ℕ) : 4^n = 2^n * 2^n := by ring_exp
example (n : ℕ) : (2 * 2)^n = 2^n * 2^n := by ring_exp
example (n : ℕ) : 4^n = (2 * 2)^n := by ring
example (n : ℕ) : 4^n = (2 * 2)^n := by ring_exp

example (n : ℕ) : 0^n = 0 := by ring_exp -- (since 0^0 evaluates to 1, this equality does not always hold!)

-- Negative numbers in exponents probably aren't worth the trouble.
example (a : ℤ) (n : ℕ) : a * a^(2^n - 1) = a^(2^n) := by ring_exp
-/
