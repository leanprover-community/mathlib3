/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import set_theory.cardinal.finite

namespace enat

open enat

lemma succ_le_iff {n : ℕ} {e : enat} : ↑n.succ ≤ e ↔ ↑n < e:=
begin
  rw [coe_lt_iff, coe_le_iff],
  apply forall_congr, intro a, rw nat.succ_le_iff,
end

lemma coe_nat_le_iff {n : ℕ} {c : cardinal} :
   ↑n ≤ cardinal.to_enat c ↔ ↑n ≤ c :=
begin
  cases lt_or_ge c cardinal.aleph_0,
  { obtain ⟨m, hm⟩ := cardinal.lt_aleph_0.mp h,
    rw hm, simp only [cardinal.to_enat_cast, coe_le_coe, cardinal.nat_cast_le] },
  { apply iff_of_true,
    { rw cardinal.to_enat_apply_of_aleph_0_le h,
      exact le_top },
    { apply le_trans (le_of_lt _) h,
      rw cardinal.lt_aleph_0,
      use n } }
end

lemma coe_nat_lt_coe_iff {n : ℕ} {c : cardinal} :
   ↑n < cardinal.to_enat c ↔ ↑n < c :=
begin
  cases lt_or_ge c cardinal.aleph_0,
  { obtain ⟨m, hm⟩ := cardinal.lt_aleph_0.mp h,
    rw hm,
    simp only [cardinal.to_enat_cast, coe_lt_coe, cardinal.nat_cast_lt],
    },
  { apply iff_of_true,
    { rw cardinal.to_enat_apply_of_aleph_0_le h,
      exact coe_lt_top n },
    { refine lt_of_lt_of_le _ h,
      rw cardinal.lt_aleph_0,
      use n } }
end

lemma card_le_one_iff_subsingleton (α : Type*) : enat.card α ≤ 1 ↔ subsingleton α :=
begin
  rw ← cardinal.le_one_iff_subsingleton,
  unfold enat.card,
  cases lt_or_ge (cardinal.mk α) (cardinal.aleph_0),
  { obtain ⟨n, hn⟩ := cardinal.lt_aleph_0.mp h,
    rw hn,
    simp only [cardinal.to_enat_cast],
    rw ← nat.cast_one, rw le_coe_iff,
    simp only [dom_coe, get_coe', exists_true_left],
    rw ← cardinal.nat_cast_le,
    simp only [nat.cast_one] },
  { rw ← not_iff_not,
    simp only [not_le],
    apply iff_of_true,
    { rw cardinal.to_enat_apply_of_aleph_0_le h,
      rw ← nat.cast_one,
      apply coe_lt_top },
    { apply lt_of_lt_of_le _ h,
      refine cardinal.one_lt_aleph_0 } }
end
end enat

#lint
