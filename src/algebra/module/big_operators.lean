/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov, Yaël Dillies
-/
import algebra.module.basic
import group_theory.group_action.big_operators

/-!
# Finite sums over modules over a ring

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

open_locale big_operators

variables {α β R M ι : Type*}

section add_comm_monoid
variables [semiring R] [add_comm_monoid M] [module R M] (r s : R) (x y : M)

lemma list.sum_smul {l : list R} {x : M} : l.sum • x = (l.map (λ r, r • x)).sum :=
((smul_add_hom R M).flip x).map_list_sum l

lemma multiset.sum_smul {l : multiset R} {x : M} : l.sum • x = (l.map (λ r, r • x)).sum :=
((smul_add_hom R M).flip x).map_multiset_sum l

lemma multiset.sum_smul_sum {s : multiset R} {t : multiset M} :
  s.sum • t.sum = ((s ×ˢ t).map $ λ p : R × M, p.fst • p.snd).sum :=
begin
  induction s using multiset.induction with a s ih,
  { simp },
  { simp [add_smul, ih, ←multiset.smul_sum] }
end

lemma finset.sum_smul {f : ι → R} {s : finset ι} {x : M} :
  (∑ i in s, f i) • x = (∑ i in s, (f i) • x) :=
((smul_add_hom R M).flip x).map_sum f s

lemma finset.sum_smul_sum {f : α → R} {g : β → M} {s : finset α} {t : finset β} :
  (∑ i in s, f i) • (∑ i in t, g i) = ∑ p in s ×ˢ t, f p.fst • g p.snd :=
by { rw [finset.sum_product, finset.sum_smul, finset.sum_congr rfl], intros, rw finset.smul_sum }

end add_comm_monoid

lemma finset.cast_card [comm_semiring R] (s : finset α) : (s.card : R) = ∑ a in s, 1 :=
by rw [finset.sum_const, nat.smul_one_eq_coe]
