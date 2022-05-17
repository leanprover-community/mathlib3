--import tactic.interactive
--import data.finset.basic
--import algebra.gcd_monoid.finset
import algebra.big_operators.basic

example : Σ (α : Type), finset ℕ → α :=
begin
  let α := _,
  refine ⟨α, _⟩,
  apply λ s : finset ℕ, s.sum _,  -- three goals: `add_comm_monoid α`, `ℕ → α`, `Type`
  show ℕ → α, exact id,
  apply_instance,
end


namespace tactic.interactive
open tactic interactive
setup_tactic_parser

meta def decomp : expr → expr → expr → tactic unit
| (expr.app f e) (expr.app f0 e0) (expr.app f1 e1) :=
  match e with
  | (expr.mvar _ _ _) := do
    el ← mk_app `eq [e0, e1],
    n ← get_unused_name "h",
    assert n el,
    swap,
    decomp f f0 f1,
    rotate_right 1
  | _ := do decomp f f0 f1 *> decomp e e0 e1
  end
| _ _ _ := skip

meta def refine' (e : parse texpr) : tactic unit :=
do
  tgt ← target,
  e' ← to_expr e tt ff >>= infer_type,
  decomp e' tgt e',
  unify e' tgt,
  apply e

end tactic.interactive

example (α : Type*) : finset ℕ → α :=
begin
  refine' (λ s : finset ℕ, s.sum _),
/-2 goals
α: Type ?
s: finset ℕ
⊢ add_comm_monoid α
α: Type ?
s: finset ℕ
⊢ ℕ → α
-/
end


#exit
-- old and not working
import tactic.interactive
import algebra.gcd_monoid.finset

namespace tactic.interactive
open tactic
setup_tactic_parser

meta def decomp : expr → expr → expr → tactic unit
| (expr.app f e) (expr.app f0 e0) (expr.app f1 e1) := do --trace e,
  match e with
  | (expr.mvar _ _ _) := do trace 0, trace e0, trace e1,
    el ← mk_app `eq [e0, e1],
    n ← get_unused_name "h",
    assert n el, get_goals >>= trace,
    swap,
    decomp f f0 f1
--    rotate_right 1
  | _ := do trace e *> skip --do decomp f f0 f1 *> decomp e e0 e1
  end
| (expr.lam a' b' f' e') (expr.lam a0' b0' f0' e0') (expr.lam a1' b1' f1' e1') := do trace e',
  el ← mk_app `eq [e0', e1'],
  n ← get_unused_name "h",
  assert n el, get_goals >>= trace,
  swap,
  decomp f' f0' f1'
--  rotate_right 1
| (expr.pi a' b' f' e') (expr.pi a0' b0' f0' e0') (expr.pi a1' b1' f1' e1') := do trace e',trace e0',
  unify e0' e1',
  el ← mk_app `eq [e0', e1'],
  n ← get_unused_name "h",
  assert n el, get_goals >>= trace,
  swap,
  decomp f' f0' f1'
--  rotate_right 1
--  | _ := do trace e *> skip --do decomp f f0 f1 *> decomp e e0 e1
| _ _ _ := skip

meta def refine' (e : parse texpr) : tactic unit :=
do
  tgt ← target, --trace tgt,
  e' ← to_expr e tt ff >>= infer_type,
  trace e',
  decomp e' tgt e',
  unify e' tgt,
  trace e',
  instantiate_mvars e',
  trace e',
  tactic.apply e' >> skip

/-
  meta def refine'' (e : parse texpr) : tactic unit :=
  do
    tgt ← target,
    e' ← to_expr e tt ff,   --    <---  added the ascription `tt ff` to `to_expr`
    decomp e' e' tgt,
    unify e' tgt,  --  added unification, since I mistakenly removed it from the copied code
    tactic.apply e' >> skip --  `apply` not `exact`!
-/


end tactic.interactive

example (α : Type*) : finset ℕ → α :=
begin
  refine' (λ s : finset ℕ, s.sum _),
/-2 goals
α: Type ?
s: finset ℕ
⊢ add_comm_monoid α
α: Type ?
s: finset ℕ
⊢ ℕ → α
-/
end

example : Σ (α : Type), finset ℕ → α :=
begin
  let α := _,
  refine ⟨α, _⟩,
  refine' λ s : finset ℕ, s.sum _, -- invalid apply tactic, failed to unify `finset ℕ → α` with  `Type`
  show ℕ → α, exact id,
  apply_instance,
end

/-  Does not work, as the Type α is not
example (α : Type*) : finset ℕ → α :=
begin
  refine' (λ s : finset ℕ, s.sum _),
  show ℕ → α, exact id,
  apply_instance,
end
-/

#exit


/-
import data.polynomial.laurent
open polynomial add_monoid_algebra finsupp polynomial
open_locale polynomial

local notation R`[T;T⁻¹]`:9000 := laurent_polynomial R

variables {R : Type*} [semiring R]

namespace laurent_polynomial

section set_semiring

/--  `to_set_semiring f` maps a Laurent polynomial `f` to
the sum of the singletons in the support of `f`. -/
def to_set_semiring (f : R[T;T⁻¹]) : set.set_semiring ℤ := (f.support : set ℤ)

lemma to_set_semiring_add (f g : R[T;T⁻¹]) :
  to_set_semiring (f + g) ≤ to_set_semiring f + to_set_semiring g :=
begin
  convert @finsupp.support_add ℤ R _ _ f g,
  simp only [finset.union_val, multiset.mem_union],
  refl,
end

lemma to_set_semiring_mul (f g : R[T;T⁻¹]) :
  to_set_semiring (f * g) ≤ to_set_semiring f * to_set_semiring g :=
begin

  revert g,
  apply f.induction_on'; clear f,
  intros f g hfg hg1 h,

  rw add_mul,
  refine (to_set_semiring_add _ _).trans _,
  simp only [to_set_semiring, set.le_eq_subset],
  unfold has_mul.mul,
  simp,
  intros n hn,
  have := finsupp.mem_support_iff.mp hn,
  have sfg := support_mul f g,
  have mn := set.mem_of_mem_of_subset hn sfg,
  simp at mn,
  rcases mn with ⟨a, ha, b, hb, rfl⟩,
  unfold has_mul.mul,
  apply set.mem_of_mem_of_subset hn _,
  have : f n ≠ 0 ∧ g n ≠ 0,
   contrapose! this,
   rcases eq_or_ne (f n) 0 with f0 | f0,

   simp at this ⊢,
  rw mul_apply_antidiagonal f g n (f.support.product g.support) (by {
    simp only [finset.mem_product, finsupp.mem_support_iff, ne.def, prod.forall],
    intros a b,

  }) at this,
  rw set.mem_mul,
  refine finsupp.mem_support_iff.mpr _,
  simp,
  simp at hn,
  convert @finsupp.support_mul ℤ R _ _ f g,
  simp only [finset.union_val, multiset.mem_union],
  refl,
end

--#check set.finset_semiring

end set_semiring


#exit


lemma nat_degree_add_le_iff_left {n : ℕ} (f g : R[X]) (gn : g.nat_degree ≤ n) :
  (f + g).nat_degree ≤ n ↔ f.nat_degree ≤ n :=
begin
  refine ⟨λ h, _, λ h, nat_degree_add_le_of_degree_le h gn⟩,
  refine nat_degree_le_iff_coeff_eq_zero.mpr (λ m hm, _),
  convert nat_degree_le_iff_coeff_eq_zero.mp h m hm using 1,
  rw [coeff_add, nat_degree_le_iff_coeff_eq_zero.mp gn _ hm, add_zero],
end

lemma nat_degree_add_le_iff_right {n : ℕ} (f g : R[X]) (fn : f.nat_degree ≤ n) :
  (f + g).nat_degree ≤ n ↔ g.nat_degree ≤ n :=
begin
  rw add_comm,
  exact nat_degree_add_le_iff_left _ _ fn,
end


Copyright (c) 2022 Arthur Paulino, Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Damiano Testa
-/
import tactic.core
import data.polynomial.degree.lemmas
import data.polynomial.algebra_map
/-!
# `move_add`: a tactic for moving summands

Calling `move_add [a, ← b, c]`, recursively looks inside the goal for expressions involving a sum.
Whenever it finds one, it moves the summands that unify to `a, b, c`, removing all parentheses.

See the doc-string for `tactic.interactive.move_add` for more information.

##  Implementation notes

The implementation of `move_add` only moves the terms specified by the user (and rearranges
parentheses).

An earlier version of this tactic also had a relation on `expr` that performed a sorting on the
terms that were not specified by the user.  This is very easy to implement, if desired, but is not
part of this tactic.  We had used the order given by the `≤` on `string` and a small support for
sorting `monomial`s by increasing degree.

Note that the tactic `abel` already implements a very solid heuristic for normalizing terms in an
additive commutative semigroup and produces expressions in more or less standard form.
The scope of `move_add` is different: it is designed to make it easy to move individual terms
around a sum.

##  Future work

* Add support for `neg` and additive groups?
* Add optional different operations than `+`, most notably `*`?
* Add functionality for moving terms across the two sides of an in/dis/equality.
  E.g. it might be desirable to have `to_lhs [a]` that converts `b + c = a + d` to `a + b + c = d`.
* Add more tests.
-/

open tactic

/--  Given a list `un` of `α`s and a list `bo` of `bool`s, return the sublist of `un`
consisting of the entries of `un` whose corresponding entry in `bo` is `tt`.

Used for error management: `un` is the list of user inputs, `bo` is the list encoding which input
is unused (`tt`) and which input is used (`ff`).
`list.return_unused` returns the unused user inputs. -/
def list.return_unused {α : Type*} : list α → list bool → list α
| un [] := un
| [] bo := []
| (u::us) (b::bs) := if b then ([u] ++ (us.return_unused bs)) else (us.return_unused bs)

/--  Given a list `lp` of `bool × pexpr` and a list `sl` of `expr`, scan the elements of `lp` one
at a time and produce 3 sublists of `sl`.

If `(tf,pe)` is the first element of `lp`, we look for the first element of `sl` that unifies with
`pe.to_expr`.  If no such element exists, then we discard `(tf,pe)` and move along.
If `eu ∈ sl` is the first element of `sl` that unifies with `pe.to_expr`, then we add `eu` as the
next element of either the first or the second list, depending on the boolean `tf` and we remove
`eu` from the list `sl`.  In this case, we continue our scanning with the next element of `lp`,
replacing `sl` by `sl.erase eu`.

Once we exhaust the elements of `lp`, we return the three lists:
* first the list of elements of `sl` that came from an element of `lp` whose boolean was `tt`,
* next the list of elements of `sl` that came from an element of `lp` whose boolean was `ff`, and
* finally the ununified elements of `sl`.

The ununified elements of `sl` get used for error management: they keep track of which user inputs
are superfluous. -/
meta def list.unify_list : list (bool × expr) → list expr → list bool →
  tactic (list expr × list expr × list expr × list bool)
| [] sl is_unused      := return ([], [], sl, is_unused)
| (be::l) sl is_unused :=
  do (ex :: hs) ← sl.mfilter $ λ e', succeeds $ unify be.2 e' |
    l.unify_list sl (is_unused.append [tt]),
  (l1, l2, l3, is_unused) ← l.unify_list (sl.erase ex) (is_unused.append [ff]),
  if be.1 then return (ex::l1, l2, l3, is_unused) else return (l1, ex::l2, l3, is_unused)

/--  Given a list of pairs `bool × pexpr`, we convert it to a list of `bool × expr`. -/
meta def list.convert_to_expr (lp : list (bool × pexpr)) : tactic (list (bool × expr)) :=
lp.mmap $ λ x : bool × pexpr, do
  e ← to_expr x.2 tt ff,
  return (x.1, e)

/--  We combine the previous steps.
1. we convert a list pairs `bool × pexpr` to a list of pairs `bool × expr`,
2. we use the extra input `sl : list expr` to perform the unification and sorting step
   `list.unify_list`,
3. we jam the third factor inside the first two.
-/
meta def list.combined (lp : list (bool × pexpr)) (sl : list expr) :
  tactic (list expr × list bool) :=
do
  to_exp : list (bool × expr) ← list.convert_to_expr lp,
  (l1, l2, l3, is_unused) ← to_exp.unify_list sl [],
  return (l1 ++ l3 ++ l2, is_unused)

meta def extr_vars_dup : expr → tactic (list expr)
| (expr.app `(bit0) a) := extr_vars_dup a
| (expr.app `(bit1) a) := extr_vars_dup a
| `(has_add.add %%a %%b) := do va ← extr_vars_dup a, vb ← extr_vars_dup b, return (va ++ vb)
| `(has_mul.mul %%a %%b) := do va ← extr_vars_dup a, vb ← extr_vars_dup b, return (va ++ vb)
| `(has_pow.pow %%a %%n) := extr_vars_dup a
| `(has_zero.zero) := return []
| `(has_one.one) := return []
| a := return [a]

meta def extr_vars (e : expr) : tactic (list expr) :=
do vv ← extr_vars_dup e,
  return vv.dedup
#check polynomial.aeval
meta def to_self : expr → tactic expr
| (expr.app `(bit0) a) := do pa ← to_self a, mk_app `bit0 [pa]
| (expr.app `(bit1) a) := do pa ← to_self a, mk_app `bit1 [pa]
| `(has_add.add %%a %%b) := do pa ← to_self a, pb ← to_self b, mk_app `has_add.add [pa, pb]
| `(has_mul.mul %%a %%b) := do pa ← to_self a, pb ← to_self b, mk_app `has_mul.mul [pa, pb]
| `(has_pow.pow %%a %%n) := do pa ← to_self a, mk_app `has_pow.pow [pa, n]
| `(has_zero.zero) := do p0 ← to_expr ``(@has_zero.zero (polynomial ℕ) _), return p0
| `(has_one.one) := do p1 ← to_expr ``(@has_one.one (polynomial  ℕ) _), return p1
| a := do pX ← to_expr ``(@polynomial.X ℕ _), return pX
--trace a *> fail "not supported"
#check polynomial.eval

def myn {R : Type*} [semiring R] : ℕ →+* R := by begin
  refine algebra_map ℕ R,
end
#check polynomial.eval₂
#check polynomial.eval₂_ring_hom'
#check list.length
meta def lift_to_poly (e : expr) : tactic unit :=
do vs ← extr_vars e,
  match vs with
  | (_::_::_) := fail "currently, only one variable is supported"
  | []  := fail "Either there are no variables, or something else went wrong!"
  | [n] := do trace "there is a single variable",
    pol ← to_self e,
    tn ← infer_type n,
    alm ← to_expr ``(algebra_map ℕ %%tn),
    evX ← mk_app `polynomial.eval₂ [alm, n, pol],
    eq_evX ← mk_app `eq [e, evX],
    hp ← get_unused_name "hp",
    tactic.assert hp eq_evX,
    `[simp only [add_zero, eval₂_add, eval₂_X_pow, eval₂_mul, eval₂_bit0, eval₂_bit1, eval₂_one,
        eval₂_X]]

--    `[ simp only [eval_add, eval_pow, eval_X, eval_mul, eval_bit0, eval_bit1, eval_one, eval_zero];
--      refl ]
--  | _ := fail "currently the tactic only supports a single variable"
  end

namespace tactic.interactive
open tactic
setup_tactic_parser

meta def mca (arg : parse ident) : tactic unit :=
do t ← target,
pex ← parser.pexpr tac_rbp ff arg,
  guess ← to_expr arg,
  unify t
--sorry
#exit
meta def mca (arg : parse ident) : tactic unit :=
do t ← target,
sorry
end tactic.interactive


open polynomial
open_locale polynomial
open tactic interactive
#check list.dedup

@[simp] lemma natpol (n : ℕ) : (n : ℕ[X]).coeff 0 = n :=
begin
  simp only [nat_cast_coeff_zero, nat.cast_id],
end

set_option trace.app_builder true
example {R : Type*} [comm_semiring R] : 5 ^ 2 + 0 = 0 :=
begin
  (do t ← target,
    `(%%tl = %%tr) ← target,
    lift_to_poly tl
  ),
  simp only [eq_nat_cast, nat.cast_one, eval₂_at_zero, nat.cast_id, nat.cast_zero, eval₂_zero, add_zero],
  apply C_inj.mp,
  simp [eval₂_at_zero, eq_nat_cast, nat.cast_id, add_left_inj],
  convert (@nat_cast_coeff_zero (5 ^ 2) _ _).symm,
  simp only [nat.cast_pow, nat.cast_bit1, nat.cast_bit0, nat.cast_one],


  convert_to 5 ^ 2 = (C (5 ^ 2) : ℕ[X]).coeff 0,
  simp only [eq_nat_cast, nat.cast_pow, nat.cast_bit1, nat.cast_bit0, nat.cast_one],
  norm_num,
  simp [coeff_bit0_mul, coeff_bit1_mul],
  simp,
  simp only [eq_nat_cast, nat.cast_pow, nat.cast_bit1, nat.cast_bit0, nat.cast_one],
  show_term{norm_cast},
  simp [← nat.cast_bit1, ← nat.cast_bit0],
  simp only [add_zero, eval₂_add, eval₂_X_pow, eval₂_mul, eval₂_bit0, eval₂_bit1, eval₂_one, eval₂_X],
end


example {R : Type*} [comm_semiring R] {m n : R} : n ^ 20 + 30 * n ^ 2 + 20*15 + n + 0 = 0 :=
begin
  (do t ← target,
    `(%%tl = %%tr) ← target,
--    extr_vars tl >>= trace,
    lift_to_poly tl
  --  local_context >>= trace,
  --  tactic.interactive.rotate,
  --  local_context >>= trace
  ),
  simp,
  simp only [add_zero, eval₂_add, eval₂_X_pow, eval₂_mul, eval₂_bit0, eval₂_bit1, eval₂_one, eval₂_X],

  simp only [eval_add, eval_pow, eval_X, eval_mul, eval_bit0, eval_bit1, eval_one, eval_zero],
--    to_self tl >>= infer_type >>= trace,
--    to_self tl >>= trace
  --sorry

end


meta def to_poly : expr → tactic expr
| (expr.app `((@bit0 %%R %%inst)) a) := do pa ← to_poly a, mk_app `bit0 [pa]
| (expr.app `((@bit1 %%R %%inst)) a) := do pa ← to_poly a, mk_app `bit1 [pa]
| `(has_add.add %%a %%b) := do pa ← to_poly a, pb ← to_poly b, mk_app `has_add.add [pa, pb]
| `(has_mul.mul %%a %%b) := do pa ← to_poly a, pb ← to_poly b, mk_app `has_mul.mul [pa, pb]
| `(has_zero.zero) := do p0 ← to_expr ``(@has_zero.zero (polynomial ℕ) _), return p0
| `(has_one.one) := do p1 ← to_expr ``(@has_one.one (polynomial ℕ) _), return p1
| a := trace a *> fail "not supported"


example : (0 : polynomial ℤ) + 1 + 1 = 0 :=
begin
  do t ← target,
    `(%%tl = %%tr) ← target,
    trace tl,
    top ← to_poly tl,
    trace top, infer_type top >>= trace
end

#check bit0

/--  Takes an `expr` and returns a list of its summands. -/
meta def get_summands : expr → list expr
| `(%%a + %%b) := get_summands a ++ get_summands b
| a            := [a]

/-- `sorted_sum` takes an optional location name `hyp` for where it will be applied, a list `ll` of
`bool × pexpr` (arising as the user-provided input to `move_add`) and an expression `e`.

`sorted_sum hyp ll e` returns an ordered sum of the terms of `e`, where the order is
determined using the `list.combined` applied to `ll` and `e`.

We use this function for expressions in an additive commutative semigroup. -/
meta def sorted_sum (hyp : option name) (ll : list (bool × pexpr)) (e : expr) :
  tactic (list bool) :=
do
  (sli, is_unused) ← ll.combined (get_summands e),
  match sli with
  | []       := return is_unused
  | (eₕ::es) := do
    e' ← es.mfoldl (λ eₗ eᵣ, mk_app `has_add.add [eₗ, eᵣ]) eₕ,
    e_eq ← mk_app `eq [e, e'],
    n ← get_unused_name,
    assert n e_eq,
    e_eq_fmt ← pp e_eq,
    reflexivity <|>
      `[{ simp only [add_comm, add_assoc, add_left_comm], done, }] <|>
      -- `[{ abel, done, }] <|> -- this works too. it's more robust but also a bit slower
        fail format!"failed to prove:\n\n{e_eq_fmt}",
    h ← get_local n,
    match hyp with
    | some loc := do
      ln ← get_local loc,
      ltyp ← infer_type ln,
      rewrite_hyp h ln,
      tactic.clear h,
      pure is_unused
    | none     := do
      rewrite_target h,
      tactic.clear h,
      pure is_unused
    end
  end

/-- Partially traverses an expression in search for a sum of terms.
When `recurse_on_expr` finds a sum, it sorts it using `sorted_sum`. -/
meta def recurse_on_expr (hyp : option name) (ll : list (bool × pexpr)) : expr → tactic (list bool)
| e@`(%%_ + %%_)     := sorted_sum hyp ll e
| (expr.lam _ _ _ e) := recurse_on_expr e
| (expr.pi  _ _ _ e) := recurse_on_expr e
| e                  := do
  li_unused ← e.get_app_args.mmap recurse_on_expr,
  let unused_summed := li_unused.transpose.map list.band,
  return unused_summed

/-- Passes the user input `ll` to `recurse_on_expr` at a single location, that could either be
`none` (referring to the goal) or `some name` (referring to hypothesis `name`).  Returns a pair
consisting of a boolean and a further list of booleans.  The single boolean is `tt` if the tactic
did *not* change the goal on which it was acting.  The list of booleans records which variable in
`ll` has been unified in the application: `tt` means that the corresponding variable has *not* been
unified.

This definition is useful to streamline error catching. -/
meta def move_add_with_errors (ll : list (bool × pexpr)) : option name → tactic (bool × list bool)
| (some hyp) := do
  lhyp ← get_local hyp,
  thyp ←  infer_type lhyp,
  is_unused ← recurse_on_expr hyp ll thyp,
  nhyp ← get_local hyp,
  nthyp ← infer_type nhyp,
  if (thyp = nthyp) then return (tt, is_unused) else return (ff, is_unused)
| none       := do
  t ← target,
  is_unused ← recurse_on_expr none ll t,
  tn ← target,
  if (t = tn) then return (tt, is_unused) else return (ff, is_unused)

/-- `move_add_arg` is a single elementary argument that `move_add` takes for the
variables to be moved.  It is either a `pexpr`, or a `pexpr` preceded by a `←`. -/
meta def move_add_arg (prec : nat) : parser (bool × pexpr) :=
prod.mk <$> (option.is_some <$> (tk "<-")?) <*> parser.pexpr prec

/-- `move_pexpr_list_or_texpr` is either a list of `move_add_arg`, possibly empty, or a single
`move_add_arg`. -/
meta def move_pexpr_list_or_texpr : parser (list (bool × pexpr)) :=
list_of (move_add_arg 0) <|> list.ret <$> (move_add_arg tac_rbp) <|> return []

/--  Out of a list of `option name`, returns a list of `name`s of target, discarding, if present
`none`, which corresponds to the goal. -/
meta def to_hyps : list (option name) → tactic (list expr)
| []           := pure []
| (some n::ns) := do ln ← get_local n, fina ← to_hyps ns, return (ln::fina)
| (none::ns)   := to_hyps ns

/--
Calling `move_add [a, ← b, c]`, recursively looks inside the goal for expressions involving a sum.
Whenever it finds one, it moves the summands that unify to `a, b, c`, removing all parentheses.
Repetitions are allowed, and are processed following the user-specified ordering.
The terms preceded by a `←` get placed to the left, the ones without the arrow get placed to the
right.  Unnamed terms stay in place.  Due to re-parenthesizing, doing `move_add` with no argument
may change the goal. Also, the *order* in which the terms are provided matters: the tactic reads
them from left to right.  This is especially important if there are multiple matches for the typed
terms in the given expressions.

A single call of `move_add` moves terms across different sums in the same expression.
Here is an example.

```lean
import tactic.move_add

example {a b c d : ℕ} (h : c = d) : c + b + a = b + a + d :=
begin
  move_add [← a, b],  -- Goal: `a + c + b = a + d + b`  -- both sides changed
  congr,
  exact h
end

example {a b c d : ℕ} (h : c = d) : c + b * c + a * c = a * d + d + b * d :=
begin
  move_add [_ * c, ← _ * c], -- Goal: `a * c + c + b * c = a * d + d + b * d`
  -- the first `_ * c` unifies with `b * c` and moves it to the right
  -- the second `_ * c` unifies with `a * c` and moves it to the left
  congr;
  assumption
end
```

The list of expressions that `move_add` takes is optional and a single expression can be passed
without brackets.  Thus `move_add ← f` and `move_add [← f]` mean the same.

Finally, `move_add` can also target one or more hypotheses.  If `hp₁, hp₂` are in the
local context, then `move_add [f, ← g] at hp₁ hp₂` performs the rearranging at `hp₁` and `hp₂`.
As usual, passing `⊢` refers to acting on the goal as well.

##  Reporting sub-optimal usage

The tactic never fails (really? TODO), but flags three kinds of unwanted use.
1. `move_add [vars]? at *` reports gloally unused variables and whether *all* goals
   are unchanged, not *each unchanged goal*.
2. If a target of `move_add` is left unchanged by the tactic, then this will be flagged (unless
   we are using `at *`).
3. If a user-provided expression never unifies, then the variable is flagged.

The tactic does not produce an error, but reports unused inputs and unchanged targets.

For instance, `move_add ← _` always reports an unchanged goal, but never an unused variable.

##  Comparison with existing tactics

* `tactive.interactive.abel`
  performs a "reduction to normal form" that allows it to close goals involving sums with higher
  success rate than `move_add`.  If the goal is an equality of two sums that are simply obtained by
  reparenthesizing and permuting summands, then `move_add [appropriate terms]` can close the goal.
  Compared to `abel`, `move_add` has the advantage of allowing the user to specify the beginning and
  the end of the final sum, so that from there the user can continue with the proof.

* `tactic.interactive.ac_change`
  supports a wide variety of operations.  At the moment, `move_add` only works with addition.
  Still, on several experiments, `move_add` had a much quicker performance than `ac_change`.
  Also, for `move_add` the user need only specify a few terms: the tactic itself takes care of
  producing the full rearrangement and proving it "behind the scenes".

###  Remark:
It is still possible that the same output of `move_add [exprs]` can be achieved by a proper sublist
of `[exprs]`, even if the tactic does not flag anything.  For instance, giving the full re-ordering
of the expressions in the target that we want to achieve will not complain that there are unused
variables, since all the user-provided variables have been matched.  Of course, specifying the order
of all-but-the-last variable suffices to determine the permutation.  E.g., with a goal of
`a + b = 0`, applying either one of `move_add [b,a]`, or `move_add a`, or `move_add ← b` has the
same effect and changes the goal to `b + a = 0`.  These are all valid uses of `move_add`.
-/
meta def move_add (args : parse move_pexpr_list_or_texpr) (locat : parse location) :
  tactic unit :=
match locat with
| loc.wildcard := do
  ctx ← local_context,
  err_rep ← ctx.mmap (λ e, move_add_with_errors args e.local_pp_name),
  er_t ← move_add_with_errors args none,
  if ff ∉ ([er_t.1] ++ err_rep.map (λ e, e.1)) then
    trace "'move_add at *' changed nothing" else skip,
  let li_unused := ([er_t.2] ++ err_rep.map (λ e, e.2)),
  let li_unused_clear := li_unused.filter (≠ []),
  let li_tf_vars := li_unused_clear.transpose.map list.band,
  match ((args.return_unused li_tf_vars).map (λ e : bool × pexpr, e.2)) with
  | []   := skip
  | [pe] := trace format!"'{pe}' is an unused variable"
  | pes  := trace format!"'{pes}' are unused variables"
  end,
  assumption <|> try (tactic.reflexivity reducible)
| loc.ns names := do
  err_rep ← names.mmap $ move_add_with_errors args,
  let conds := err_rep.map (λ e, e.1),
  linames ← to_hyps (names.return_unused conds),
  if linames ≠ [] then trace
    format!"'{linames}' did not change" else skip,
  if none ∈ names.return_unused conds then trace
    "Goal did not change" else skip,
  let li_unused := (err_rep.map (λ e, e.2)),
  let li_unused_clear := li_unused.filter (≠ []),
  let li_tf_vars := li_unused_clear.transpose.map list.band,
  match ((args.return_unused li_tf_vars).map (λ e : bool × pexpr, e.2)) with
  | []   := skip
  | [pe] := trace format!"'{pe}' is an unused variable"
  | pes  := trace format!"'{pes}' are unused variables"
  end,
  assumption <|> try (tactic.reflexivity reducible)
  end

add_tactic_doc
{ name := "move_add",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.move_add],
  tags := ["arithmetic"] }

end tactic.interactive
