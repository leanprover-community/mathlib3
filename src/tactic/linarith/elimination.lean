/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/

import tactic.linarith.datatypes

/-!
# The Fourier-Motzkin elimination procedure

The Fourier-Motzkin procedure is a variable elimination method for linear inequalities.
<https://en.wikipedia.org/wiki/Fourier%E2%80%93Motzkin_elimination>

Given a set of linear inequalities `comps = {tᵢ Rᵢ 0}`,
we aim to eliminate a single variable `a` from the set.
We partition `comps` into `comps_pos`, `comps_neg`, and `comps_zero`,
where `comps_pos` contains the comparisons `tᵢ Rᵢ 0` in which
the coefficient of `a` in `tᵢ` is positive, and similar.

For each pair of comparisons `tᵢ Rᵢ 0 ∈ comps_pos`, `tⱼ Rⱼ 0 ∈ comps_neg`,
we compute coefficients `vᵢ, vⱼ ∈ ℕ` such that `vᵢ*tᵢ + vⱼ*tⱼ` cancels out `a`.
We collect these sums `vᵢ*tᵢ + vⱼ*tⱼ R' 0` in a set `S` and set `comps' = S ∪ comps_zero`,
a new set of comparisons in which `a` has been eliminated.

Theorem: `comps` and `comps'` are equisatisfiable.

We recursively eliminate all variables from the system. If we derive an empty clause `0 < 0`,
we conclude that the original system was unsatisfiable.
-/

open native
namespace linarith

/-!
### Datatypes

The `comp_source` and `pcomp` datatypes are specific to the FM elimination routine;
they are not shared with other components of `linarith`.
-/

/--
`comp_source` tracks the source of a comparison.
The atomic source of a comparison is an assumption, indexed by a natural number.
Two comparisons can be added to produce a new comparison,
and one comparison can be scaled by a natural number to produce a new comparison.
 -/
@[derive inhabited]
inductive comp_source : Type
| assump : ℕ → comp_source
| add : comp_source → comp_source → comp_source
| scale : ℕ → comp_source → comp_source

/--
Given a `comp_source` `cs`, `cs.flatten` maps an assumption index
to the number of copies of that assumption that appear in the history of `cs`.

For example, suppose `cs` is produced by scaling assumption 2 by 5,
and adding to that the sum of assumptions 1 and 2.
`cs.flatten` maps `1 ↦ 1, 2 ↦ 6`.
 -/
meta def comp_source.flatten : comp_source → rb_map ℕ ℕ
| (comp_source.assump n) := mk_rb_map.insert n 1
| (comp_source.add c1 c2) := (comp_source.flatten c1).add (comp_source.flatten c2)
| (comp_source.scale n c) := (comp_source.flatten c).map (λ v, v * n)

/-- Formats a `comp_source` for printing. -/
def comp_source.to_string : comp_source → string
| (comp_source.assump e) := to_string e
| (comp_source.add c1 c2) := comp_source.to_string c1 ++ " + " ++ comp_source.to_string c2
| (comp_source.scale n c) := to_string n ++ " * " ++ comp_source.to_string c

meta instance comp_source.has_to_format : has_to_format comp_source :=
⟨λ a, comp_source.to_string a⟩

/--
A `pcomp` stores a linear comparison `Σ cᵢ*xᵢ R 0`,
along with information about how this comparison was derived.
The original expressions fed into `linarith` are each assigned a unique natural number label.
The *historical set* `pcomp.history` stores the labels of expressions
that were used in deriving the current `pcomp`.
Variables are also indexed by natural numbers. The sets `pcomp.effective`, `pcomp.implicit`,
and `pcomp.vars` contain variable indices.
* `pcomp.vars` contains the variables that appear in `pcomp.c`. We store them in `pcomp` to
  avoid recomputing the set, which requires folding over a list. (TODO: is this really needed?)
* `pcomp.effective` contains the variables that have been effectively eliminated from `pcomp`.
  A variable `n` is said to be *effectively eliminated* in `pcomp` if the elimination of `n`
  produced at least one of the ancestors of `pcomp`.
* `pcomp.implicit` contains the variables that have been implicitly eliminated from `pcomp`.
  A variable `n` is said to be *implicitly eliminated* in `pcomp` if it satisfies the following
  properties:
  - There is some `ancestor` of `pcomp` such that `n` appears in `ancestor.vars`.
  - `n` does not appear in `pcomp.vars`.
  - `n` was not effectively eliminated.

We track these sets in order to compute whether the history of a `pcomp` is *minimal*.
Checking this directly is expensive, but effective approximations can be defined in terms of these
sets. During the variable elimination process, a `pcomp` with non-minimal history can be discarded.
-/
meta structure pcomp : Type :=
(c : comp)
(src : comp_source)
(history : rb_set ℕ)
(effective : rb_set ℕ)
(implicit : rb_set ℕ)
(vars : rb_set ℕ)

/--
Any comparison whose history is not minimal is redundant,
and need not be included in the new set of comparisons.
`elimed_ge : ℕ` is a natural number such that all variables with index ≥ `elimed_ge` have been
removed from the system.

This test is an overapproximation to minimality. It gives necessary but not sufficient conditions.
If the history of `c` is minimal, then `c.maybe_minimal` is true,
but `c.maybe_minimal` may also be true for some `c` with minimal history.
Thus, if `c.maybe_minimal` is false, `c` is known not to be minimal and must be redundant.
See http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.51.493&rep=rep1&type=pdf p.13
(Theorem 7).
The condition described there considers only implicitly eliminated variables that have been
officially eliminated from the system. This is not the case for every implicitly eliminated
variable. Consider eliminating `z` from `{x + y + z < 0, x - y - z < 0}`. The result is the set
`{2*x < 0}`; `y` is implicitly but not officially eliminated.

This implementation of Fourier-Motzkin elimination processes variables in decreasing order of
indices. Immediately after a step that eliminates variable `k`, variable `k'` has been eliminated
iff `k' ≥ k`. Thus we can compute the intersection of officially and implicitly eliminated variables
by taking the set of implicitly eliminated variables with indices ≥ `elimed_ge`.
-/
meta def pcomp.maybe_minimal (c : pcomp) (elimed_ge : ℕ) : bool :=
c.history.size ≤ 1 + ((c.implicit.filter (≥ elimed_ge)).union c.effective).size

/--
The `comp_source` field is ignored when comparing `pcomp`s. Two `pcomp`s proving the same
comparison, with different sources, are considered equivalent.
-/
meta def pcomp.cmp (p1 p2 : pcomp) : ordering :=
p1.c.cmp p2.c

/-- `pcomp.scale c n` scales the coefficients of `c` by `n` and notes this in the `comp_source`. -/
meta def pcomp.scale (c : pcomp) (n : ℕ) : pcomp :=
{c with c := c.c.scale n, src := c.src.scale n}

/--
`pcomp.add c1 c2 elim_var` creates the result of summing the linear comparisons `c1` and `c2`,
during the process of eliminating the variable `elim_var`.
The computation assumes, but does not enforce, that `elim_var` appears in both `c1` and `c2`
and does not appear in the sum.
Computing the sum of the two comparisons is easy; the complicated details lie in tracking the
additional fields of `pcomp`.
* The historical set `pcomp.history` of `c1 + c2` is the union of the two historical sets.
* We recompute the variables that appear in `c1 + c2` from the newly created `linexp`,
  since some may have been implicitly eliminated.
* The effectively eliminated variables of `c1 + c2` are the union of the two effective sets,
  with `elim_var` inserted.
* The implicitly eliminated variables of `c1 + c2` are those that appear in at least one of
  `c1.vars` and `c2.vars` but not in `(c1 + c2).vars`, excluding `elim_var`.
-/
meta def pcomp.add (c1 c2 : pcomp) (elim_var : ℕ) : pcomp :=
let c := c1.c.add c2.c,
    src := c1.src.add c2.src,
    history := c1.history.union c2.history,
    vars := native.rb_set.of_list c.vars,
    effective := (c1.effective.union c2.effective).insert elim_var,
    implicit := ((c1.vars.union c2.vars).sdiff vars).erase elim_var in
⟨c, src, history, effective, implicit, vars⟩

/--
`pcomp.assump c n` creates a `pcomp` whose comparison is `c` and whose source is
`comp_source.assump n`, that is, `c` is derived from the `n`th hypothesis.
The history is the singleton set `{n}`.
No variables have been eliminated (effectively or implicitly).
-/
meta def pcomp.assump (c : comp) (n : ℕ) : pcomp :=
{ c := c,
  src := comp_source.assump n,
  history := mk_rb_set.insert n,
  effective := mk_rb_set,
  implicit := mk_rb_set,
  vars := rb_set.of_list c.vars }

meta instance pcomp.to_format : has_to_format pcomp :=
⟨λ p, to_fmt p.c.coeffs ++ to_string p.c.str ++ "0"⟩


/-- Creates an empty set of `pcomp`s, sorted using `pcomp.cmp`. This should always be used instead
of `mk_rb_map` for performance reasons. -/
meta def mk_pcomp_set : rb_set pcomp :=
rb_map.mk_core unit pcomp.cmp

/-! ### Elimination procedure -/

/-- If `c1` and `c2` both contain variable `a` with opposite coefficients,
produces `v1` and `v2` such that `a` has been cancelled in `v1*c1 + v2*c2`. -/
meta def elim_var (c1 c2 : comp) (a : ℕ) : option (ℕ × ℕ) :=
let v1 := c1.coeff_of a,
    v2 := c2.coeff_of a in
if v1 * v2 < 0 then
  let vlcm :=  nat.lcm v1.nat_abs v2.nat_abs,
      v1' := vlcm / v1.nat_abs,
      v2' := vlcm / v2.nat_abs in
  some ⟨v1', v2'⟩
else none

/--
`pelim_var p1 p2` calls `elim_var` on the `comp` components of `p1` and `p2`.
If this returns `v1` and `v2`, it creates a new `pcomp` equal to `v1*p1 + v2*p2`,
and tracks this in the `comp_source`.
-/
meta def pelim_var (p1 p2 : pcomp) (a : ℕ) : option pcomp :=
do (n1, n2) ← elim_var p1.c p2.c a,
   return $ (p1.scale n1).add (p2.scale n2) a

/--
A `pcomp` represents a contradiction if its `comp` field represents a contradiction.
-/
meta def pcomp.is_contr (p : pcomp) : bool := p.c.is_contr

/--
`elim_var_with_set a p comps` collects the result of calling `pelim_var p p' a`
for every `p' ∈ comps`.
-/
meta def elim_with_set (a : ℕ) (p : pcomp) (comps : rb_set pcomp) : rb_set pcomp :=
comps.fold mk_pcomp_set $ λ pc s,
match pelim_var p pc a with
| some pc := if pc.maybe_minimal a then s.insert pc else s
| none := s
end

/--
The state for the elimination monad.
* `max_var`: the largest variable index that has not been eliminated.
* `comps`: a set of comparisons

The elimination procedure proceeds by eliminating variable `v` from `comps` progressively
in decreasing order.
-/
meta structure linarith_structure : Type :=
(max_var : ℕ)
(comps : rb_set pcomp)

/--
The linarith monad extends an exceptional monad with a `linarith_structure` state.
An exception produces a contradictory `pcomp`.
-/
@[reducible, derive [monad, monad_except pcomp]] meta def linarith_monad : Type → Type :=
state_t linarith_structure (except_t pcomp id)

/-- Returns the current max variable. -/
meta def get_max_var : linarith_monad ℕ :=
linarith_structure.max_var <$> get

/-- Return the current comparison set. -/
meta def get_comps : linarith_monad (rb_set pcomp) :=
linarith_structure.comps <$> get

/-- Throws an exception if a contradictory `pcomp` is contained in the current state. -/
meta def validate : linarith_monad unit :=
do ⟨_, comps⟩ ← get,
match comps.to_list.find (λ p : pcomp, p.is_contr) with
| none := return ()
| some c := throw c
end

/--
Updates the current state with a new max variable and comparisons,
and calls `validate` to check for a contradiction.
-/
meta def update (max_var : ℕ) (comps : rb_set pcomp) : linarith_monad unit :=
state_t.put ⟨max_var, comps⟩ >> validate

/--
`split_set_by_var_sign a comps` partitions the set `comps` into three parts.
* `pos` contains the elements of `comps` in which `a` has a positive coefficient.
* `neg` contains the elements of `comps` in which `a` has a negative coefficient.
* `not_present` contains the elements of `comps` in which `a` has coefficient 0.

Returns `(pos, neg, not_present)`.
-/
meta def split_set_by_var_sign (a : ℕ) (comps : rb_set pcomp) :
  rb_set pcomp × rb_set pcomp × rb_set pcomp :=
comps.fold ⟨mk_pcomp_set, mk_pcomp_set, mk_pcomp_set⟩ $ λ pc ⟨pos, neg, not_present⟩,
  let n := pc.c.coeff_of a in
  if n > 0 then ⟨pos.insert pc, neg, not_present⟩
  else if n < 0 then ⟨pos, neg.insert pc, not_present⟩
  else ⟨pos, neg, not_present.insert pc⟩

/--
`monad.elim_var a` performs one round of Fourier-Motzkin elimination, eliminating the variable `a`
from the `linarith` state.
-/
meta def monad.elim_var (a : ℕ) : linarith_monad unit :=
do vs ← get_max_var,
   when (a ≤ vs) $
do ⟨pos, neg, not_present⟩ ← split_set_by_var_sign a <$> get_comps,
   let cs' := pos.fold not_present (λ p s, s.union (elim_with_set a p neg)),
   update (vs - 1) cs'

/--
`elim_all_vars` eliminates all variables from the linarith state, leaving it with a set of
ground comparisons. If this succeeds without exception, the original `linarith` state is consistent.
-/
meta def elim_all_vars : linarith_monad unit :=
do mv ← get_max_var,
   (list.range $ mv + 1).reverse.mmap' monad.elim_var

/--
`mk_linarith_structure hyps vars` takes a list of hypotheses and the largest variable present in
those hypotheses. It produces an initial state for the elimination monad.
-/
meta def mk_linarith_structure (hyps : list comp) (max_var : ℕ) : linarith_structure :=
let pcomp_list : list pcomp := hyps.enum.map $ λ ⟨n, cmp⟩, pcomp.assump cmp n,
    pcomp_set := rb_set.of_list_core mk_pcomp_set pcomp_list in
⟨max_var, pcomp_set⟩

/--
`produce_certificate hyps vars` tries to derive a contradiction from the comparisons in `hyps`
by eliminating all variables ≤ `max_var`.
If successful, it returns a map `coeff : ℕ → ℕ` as a certificate.
This map represents that we can find a contradiction by taking the sum  `∑ (coeff i) * hyps[i]`.
-/
meta def fourier_motzkin.produce_certificate : certificate_oracle :=
λ hyps max_var,
let state := mk_linarith_structure hyps max_var in
match except_t.run (state_t.run (validate >> elim_all_vars) state) with
| (except.ok (a, _)) := tactic.failed
| (except.error contr) := return contr.src.flatten
end

end linarith
