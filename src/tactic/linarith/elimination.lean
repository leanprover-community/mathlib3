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
meta inductive comp_source : Type
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
meta def comp_source.to_string : comp_source → string
| (comp_source.assump e) := to_string e
| (comp_source.add c1 c2) := comp_source.to_string c1 ++ " + " ++ comp_source.to_string c2
| (comp_source.scale n c) := to_string n ++ " * " ++ comp_source.to_string c

meta instance comp_source.has_to_format : has_to_format comp_source :=
⟨λ a, comp_source.to_string a⟩

/-- `pcomp` pairs a zero comparison with its history. -/
meta structure pcomp :=
(c : comp)
(src : comp_source)

/--
The `comp_source` field is ignored when comparing `pcomp`s. Two `pcomp`s proving the same
comparison, with different sources, are considered equivalent.
-/
meta def pcomp.cmp (p1 p2 : pcomp) : ordering :=
p1.c.cmp p2.c

/-- `pcomp.scale c n` scales the coefficients of `c` by `n` and notes this in the `comp_source`. -/
meta def pcomp.scale (c : pcomp) (n : ℕ) : pcomp :=
⟨c.c.scale n, comp_source.scale n c.src⟩

/-- `pcomp.add c1 c2` adds the coefficients of `c1` to `c2`, and notes this in the `comp_source`. -/
meta def pcomp.add (c1 c2 : pcomp) : pcomp :=
⟨c1.c.add c2.c, comp_source.add c1.src c2.src⟩

meta instance pcomp.to_format : has_to_format pcomp :=
⟨λ p, to_fmt p.c.coeffs ++ to_string p.c.str ++ "0"⟩


/-- Creates an empty set of `pcomp`s, sorted using `pcomp.cmp`. This should always be used instead
of `mk_rb_map` for performance reasons. -/
meta def mk_pcomp_set : rb_set pcomp :=
rb_map.mk_core unit pcomp.cmp

/-! ### Elimination procedure -/

/-- If `c1` and `c2` both contain variable `a` with opposite coefficients,
produces `v1` and `v2`, such that `a` has been canceled in `v1*c1 + v2*c2`. -/
meta def elim_var (c1 c2 : comp) (a : ℕ) : option (ℕ × ℕ × comp) :=
let v1 := c1.coeff_of a,
    v2 := c2.coeff_of a in
if v1 * v2 < 0 then
  let vlcm :=  nat.lcm v1.nat_abs v2.nat_abs,
      v1' := vlcm / v1.nat_abs,
      v2' := vlcm / v2.nat_abs in
  some ⟨v1', v2', comp.add (c1.scale v1') (c2.scale v2')⟩
else none

/--
`pelim_var p1 p2` calls `elim_var` on the `comp` components of `p1` and `p2`.
If this returns `v1` and `v2`, it creates a new `pcomp` equal to `v1*p1 + v2*p2`,
and tracks this in the `comp_source`.
-/
meta def pelim_var (p1 p2 : pcomp) (a : ℕ) : option pcomp :=
do (n1, n2, c) ← elim_var p1.c p2.c a,
   return ⟨c, comp_source.add (p1.src.scale n1) (p2.src.scale n2)⟩

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
| some pc := s.insert pc
| none := s
end

/--
The state for the elimination monad.
* `vars`: the set of variables that have not been officially eliminated
* `comps`: a set of comparisons

The elimination procedure proceeds by eliminating variable `v` from `comps` progressively
for each `v ∈ vars`.

Note: variables are eliminated in decreasing order. Instead of storing `vars` as an `rb_set`,
we could store the largest `n : N` that has not yet been eliminated.
This is not done yet for historical reasons, and is a negligible performance gain.
-/
meta structure linarith_structure :=
(vars : rb_set ℕ)
(comps : rb_set pcomp)

/--
The linarith monad extends an exceptional monad with a `linarith_structure` state.
An exception produces a contradictory `pcomp`.
-/
@[reducible, derive [monad, monad_except pcomp]] meta def linarith_monad :=
state_t linarith_structure (except_t pcomp id)

/-- Return the set of active variables. -/
meta def get_vars : linarith_monad (rb_set ℕ) :=
linarith_structure.vars <$> get

/-- Return the list of active variables. -/
meta def get_var_list : linarith_monad (list ℕ) :=
rb_set.to_list <$> get_vars

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
Updates the current state with a new set of variables and comparisons,
and calls `validate` to check for a contradiction.
-/
meta def update (vars : rb_set ℕ) (comps : rb_set pcomp) : linarith_monad unit :=
state_t.put ⟨vars, comps⟩ >> validate

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
do vs ← get_vars,
   when (vs.contains a) $
do ⟨pos, neg, not_present⟩ ← split_set_by_var_sign a <$> get_comps,
   let cs' := pos.fold not_present (λ p s, s.union (elim_with_set a p neg)),
   update (vs.erase a) $ cs'

/--
`elim_all_vars` eliminates all variables from the linarith state, leaving it with a set of
ground comparisons. If this succeeds without exception, the original `linarith` state is consistent.
-/
meta def elim_all_vars : linarith_monad unit :=
get_var_list >>= list.mmap' monad.elim_var

/--
`mk_linarith_structure hyps vars` takes a list of hypotheses and a set of the variables present in
those hypotheses. It produces an initial state for the elimination monad.
-/
meta def mk_linarith_structure (hyps : list comp) (vars : rb_set ℕ) : linarith_structure :=
let pcomp_list : list pcomp := hyps.enum.map $ λ ⟨n, cmp⟩, ⟨cmp, comp_source.assump n⟩,
    pcomp_set := rb_set.of_list_core mk_pcomp_set pcomp_list in
⟨vars, pcomp_set⟩

/--
`produce_certificate hyps vars` tries to derive a contradiction from the comparisons in `hyps`
by eliminating the variables in `vars`.
If successful, it returns a map `coeff : ℕ → ℕ` as a certificate.
This map represents that we can find a contradiction by taking the sum  `∑ (coeff i) * hyps[i]`.
-/
meta def fourier_motzkin.produce_certificate (hyps : list comp) (vars : rb_set ℕ) :
  option (rb_map ℕ ℕ) :=
let state := mk_linarith_structure hyps vars in
match except_t.run (state_t.run (validate >> elim_all_vars) state) with
| (except.ok (a, _)) := none
| (except.error contr) := contr.src.flatten
end

end linarith
