/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import set_theory.cardinal.finite

open_locale cardinal

open part_enat cardinal


set_option pp.universes true

universes u v w
variable {α : Type u}

namespace cardinal

lemma to_nat_eq_iff_eq_of_lt_aleph_0 {c d : cardinal} (hc : c < ℵ₀) (hd : d < ℵ₀) :
  c.to_nat = d.to_nat ↔ c = d :=
by rw [←nat_cast_inj, cast_to_nat_of_lt_aleph_0 hc, cast_to_nat_of_lt_aleph_0 hd]

lemma to_part_enat_lift (c : cardinal.{v}) : (cardinal.lift.{u v} c).to_part_enat = c.to_part_enat :=
begin
  cases lt_or_ge c ℵ₀ with hc hc,
  { rw [to_part_enat_apply_of_lt_aleph_0 hc, cardinal.to_part_enat_apply_of_lt_aleph_0 _],
    simp only [to_nat_lift],
    rw [← lift_aleph_0, lift_lt], exact hc },
  { rw [to_part_enat_apply_of_aleph_0_le hc, cardinal.to_part_enat_apply_of_aleph_0_le _],
  rw [← lift_aleph_0, lift_le], exact hc }
end

lemma to_part_enat_congr {β : Type v} (e : α ≃ β) : (#α).to_part_enat = (#β).to_part_enat :=
by rw [←to_part_enat_lift, lift_mk_eq.mpr ⟨e⟩, to_part_enat_lift]

end cardinal

namespace part_enat

lemma card_congr {α : Type*} {β : Type*} (f : α ≃ β) :
  part_enat.card α = part_enat.card β :=
cardinal.to_part_enat_congr f

lemma card_ulift (α : Type*) : card (ulift α) = card α :=
card_congr equiv.ulift

@[simp] lemma card_plift (α : Type*) : card (plift α) = card α :=
card_congr equiv.plift

lemma card_image_of_inj_on {α : Type u} {β : Type v} (f : α → β) (s : set α) (h : set.inj_on f s) :
  card (f '' s) = card s :=
card_congr (equiv.set.image_of_inj_on f s h).symm

lemma card_image_of_injective {α : Type u} {β : Type v}
  (f : α → β) (s : set α) (h : function.injective f) :
  card (f '' s) = card s :=
card_congr (equiv.set.image_of_inj_on f s (set.inj_on_of_injective h s)).symm

-- Add other similar lemmas?

lemma succ_le_iff {n : ℕ} {e : part_enat} : ↑n.succ ≤ e ↔ ↑n < e:=
begin
  rw [coe_lt_iff, coe_le_iff],
  apply forall_congr, intro a, rw nat.succ_le_iff,
end

/- The line
-- obtain ⟨m, hm⟩ := cardinal.lt_aleph_0.mp h,
extract an integer m from a cardinal c such that h : c < ℵ₀
It may appear easier to use than the rewrites I finally use … -/

lemma coe_nat_le_iff_le {n : ℕ} {c : cardinal} :
   ↑n ≤ to_part_enat c ↔ ↑n ≤ c :=
begin
  cases lt_or_ge c ℵ₀,
  { rw [to_part_enat_apply_of_lt_aleph_0 h, coe_le_coe, ← to_nat_cast n],
    rw to_nat_le_iff_le_of_lt_aleph_0 (nat_lt_aleph_0 n) h,
    simp only [to_nat_cast] },
  { apply iff_of_true,
    { rw to_part_enat_apply_of_aleph_0_le h,
      exact le_top },
    { apply le_trans (le_of_lt _) h,
      rw lt_aleph_0,
      use n } }
end

lemma le_coe_nat_iff_le {c : cardinal} {n : ℕ} :
   to_part_enat c ≤ n ↔ c ≤ n :=
begin
  cases lt_or_ge c ℵ₀,
  { rw [to_part_enat_apply_of_lt_aleph_0 h, coe_le_coe, ← to_nat_cast n],
    rw to_nat_le_iff_le_of_lt_aleph_0 h (nat_lt_aleph_0 n),
    simp only [to_nat_cast] },
  { apply iff_of_false,
    { rw to_part_enat_apply_of_aleph_0_le h,
      simp only [top_le_iff, coe_ne_top, not_false_iff] },
    { rw not_le,
      apply lt_of_lt_of_le (nat_lt_aleph_0 n) h } }
end

lemma coe_nat_eq_iff_eq {n : ℕ} {c : cardinal} :
   ↑n = to_part_enat c ↔ ↑n = c :=
begin
  cases lt_or_ge c cardinal.aleph_0,
  { rw [to_part_enat_apply_of_lt_aleph_0 h, coe_inj],
    rw ← to_nat_cast n,
    rw cardinal.to_nat_eq_iff_eq_of_lt_aleph_0 (nat_lt_aleph_0 n) h,
    simp only [to_nat_cast] },
  { apply iff_of_false,
    { rw cardinal.to_part_enat_apply_of_aleph_0_le h,
      exact coe_ne_top n },
    { apply ne_of_lt,
      apply lt_of_lt_of_le (cardinal.nat_lt_aleph_0 n) h } }
end

lemma eq_coe_nat_iff_eq {c : cardinal} {n : ℕ} :
   cardinal.to_part_enat c = n ↔ c = n:=
begin
  split,
  { intro h, apply symm, exact coe_nat_eq_iff_eq.mp h.symm },
  { intro h, apply symm, exact coe_nat_eq_iff_eq.mpr h.symm }
end

lemma coe_nat_lt_coe_iff_lt {n : ℕ} {c : cardinal} :
   ↑n < to_part_enat c ↔ ↑n < c :=
begin
  cases lt_or_ge c ℵ₀,
  { rw [to_part_enat_apply_of_lt_aleph_0 h, coe_lt_coe, ← to_nat_cast n],
    rw to_nat_lt_iff_lt_of_lt_aleph_0 (nat_lt_aleph_0 n) h,
    simp only [to_nat_cast] },
  { apply iff_of_true,
    { rw to_part_enat_apply_of_aleph_0_le h, exact coe_lt_top n },
    { exact lt_of_lt_of_le (nat_lt_aleph_0 n) h } }
end

lemma lt_coe_nat_iff_lt {n : ℕ} {c : cardinal} :
   to_part_enat c < n ↔ c < n :=
begin
  cases lt_or_ge c ℵ₀,
  { rw [to_part_enat_apply_of_lt_aleph_0 h, coe_lt_coe, ← to_nat_cast n],
    rw to_nat_lt_iff_lt_of_lt_aleph_0 h (nat_lt_aleph_0 n),
    simp only [to_nat_cast] },
  { apply iff_of_false,
    { rw to_part_enat_apply_of_aleph_0_le h,
      simp },
    { rw not_lt,
      refine le_trans (le_of_lt (nat_lt_aleph_0 n)) h } }
end

lemma card_eq_zero_iff_empty (α : Type*) : card α = 0 ↔ is_empty α :=
begin
  rw ← cardinal.mk_eq_zero_iff,
  conv_rhs { rw ← nat.cast_zero },
  rw ← eq_coe_nat_iff_eq,
  unfold part_enat.card,
  simp only [nat.cast_zero]
end

lemma card_le_one_iff_subsingleton (α : Type*) : card α ≤ 1 ↔ subsingleton α :=
begin
  rw ← le_one_iff_subsingleton,
  conv_rhs { rw ← nat.cast_one},
  rw ← le_coe_nat_iff_le,
  unfold part_enat.card,
  simp only [nat.cast_one]
end

lemma one_lt_card_iff_nontrivial (α : Type*) : 1 < card α ↔ nontrivial α :=
begin
  rw ← cardinal.one_lt_iff_nontrivial,
  conv_rhs { rw ← nat.cast_one},
  rw ← coe_nat_lt_coe_iff_lt,
  unfold part_enat.card,
  simp only [nat.cast_one]
end


lemma of_fintype (α : Type*) [fintype α] : card α = fintype.card α :=
begin
  unfold part_enat.card,
  rw cardinal.mk_fintype,
  simp only [cardinal.to_part_enat_cast]
end
/-
lemma is_finite_of_card (α : Type) {n : ℕ} (hα : part_enat.card α = n) :
  fintype α :=
begin
  cases (fintype_or_infinite α) with h h; resetI,
  exact h,
  rw part_enat.card_eq_top_of_infinite at hα,
  exfalso, apply part_enat.coe_ne_top n, rw hα,
end -/

end part_enat

#lint
