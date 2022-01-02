/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import analysis.normed_space.ordered

/-!
# Modulus and characteristic of convexity
-/

namespace set
section
variables {α : Type*} {s : set α} {a : α}

lemma subsingleton_of_subset_singleton (h : s ⊆ {a}) : s.subsingleton :=
λ b hb c hc, (h hb).trans (h hc).symm

protected lemma subsingleton.bdd_above [preorder α] [nonempty α] (h : s.subsingleton) :
  bdd_above s :=
h.eq_empty_or_singleton.elim (λ h, h.substr bdd_above_empty) $
  by { rintro ⟨a, rfl⟩, exact bdd_above_singleton }

protected lemma subsingleton.bdd_below [preorder α] [nonempty α] (h : s.subsingleton) :
  bdd_below s :=
h.eq_empty_or_singleton.elim (λ h, h.substr bdd_below_empty) $
  by { rintro ⟨a, rfl⟩, exact bdd_below_singleton }

end

variables {ι : Sort*} {α : Type*}

lemma range_const_subsingleton (a : α) : (set.range (λ i : ι, a)).subsingleton :=
set.subsingleton_of_subset_singleton set.range_const_subset

end set

lemma div_eq_one_iff {α : Type*} [group_with_zero α] {x y : α} (hy : y ≠ 0) :
  x / y = 1 ↔ x = y :=
by rw [div_eq_iff hy, one_mul]

section conditionally_complete_lattice
variables {ι : Sort*} {α : Type*} [conditionally_complete_lattice α] {f g : ι → α} {p q : ι → Prop}
  {s : set α} {r : ℝ} {a b : α}

lemma bcsupr_mono_right (hg : bdd_above (set.range g)) (hfg : ∀ i, p i → f i ≤ g i) :
  (⨆ (i : ι) (hi : p i), f i) ≤ ⨆ (i : ι) (hi : p i), g i :=
csupr_le_csupr begin
  obtain ⟨x, hx⟩ := hg,
  refine ⟨Sup ∅ ⊔ x, _⟩,
  rintro _ ⟨i, rfl⟩,
  casesI is_empty_or_nonempty (p i),
  { convert le_sup_left,
    exact (set.range_eq_empty _).symm },
  { exact (csupr_le $ λ _, hx $ set.mem_range_self _).trans le_sup_right }
end $ λ a, csupr_le_csupr (set.range_const_subsingleton _).bdd_above $ hfg _

lemma le_bcsupr {f : ι → α} (hf : bdd_above (set.range f)) (i : ι) (hi : p i) :
  f i ≤ ⨆ (i : ι) (hi : p i), f i :=
le_csupr_of_le begin
  obtain ⟨x, hx⟩ := hf,
  refine ⟨Sup ∅ ⊔ x, _⟩,
  rintro _ ⟨i, rfl⟩,
  casesI is_empty_or_nonempty (p i),
  { convert le_sup_left,
    exact (set.range_eq_empty _).symm },
  { exact (csupr_le $ λ _, hx $ set.mem_range_self _).trans le_sup_right }
end i $ le_csupr hf hi

lemma le_bcsupr_of_le {f : Π i, p i → α} (i : ι) (hi : p i) (ha : a ≤ f i hi) :
  a ≤ ⨆ (i : ι) (hi : p i), f i hi :=
begin

end

end conditionally_complete_lattice

namespace real
variables {α : Sort*} {f g : α → ℝ} {p q : α → Prop} {S : set ℝ} {r : ℝ} {a : α}

lemma csupr_zero (hf : ∀ a, f a = 0) : (⨆ a, f a) = 0 :=
by { convert csupr_const_zero, exact funext hf }

lemma bsupr_zero (hf : ∀ a, p a → f a = 0) : (⨆ (a : α) (ha : p a), f a) = 0 :=
csupr_zero $ λ a, csupr_zero $ hf a

lemma Sup_nonneg' (h : r ∈ S) (hr : 0 ≤ r) : 0 ≤ Sup S :=
begin
  by_cases hs : bdd_above S,
  { exact le_cSup_of_le hs h hr },
  { exact (Sup_of_not_bdd_above hs).ge }
end

lemma csupr_nonneg' (ha : 0 ≤ f a) : 0 ≤ ⨆ a, f a := Sup_nonneg' (set.mem_range_self _) ha

lemma csupr_nonneg (hf : ∀ a, 0 ≤ f a) : 0 ≤ ⨆ a, f a :=
begin
  refine real.Sup_nonneg _ _,
  rintro _ ⟨a, _, rfl⟩,
  exact hf a,
end

lemma bsupr_nonneg' (ha : 0 ≤ f a) : 0 ≤ ⨆ (a : α) (ha : p a), f a :=
csupr_nonneg' $ csupr_nonneg $ λ _, ha

lemma bsupr_nonneg (hf : ∀ a, p a → 0 ≤ f a) : 0 ≤ ⨆ (a : α) (ha : p a), f a :=
csupr_nonneg $ λ a, csupr_nonneg $ hf _

lemma Sup_le_of_nonneg {s : set ℝ} (hr : 0 ≤ r) (h : ∀ a ∈ s, a ≤ r) : Sup s ≤ r :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { rwa Sup_empty },
  { exact cSup_le hs h }
end

lemma csupr_le_of_nonneg (hr : 0 ≤ r) (hf : ∀ a, f a ≤ r) : (⨆ a, f a) ≤ r :=
begin
  casesI is_empty_or_nonempty α,
  { rwa csupr_empty },
  { exact csupr_le hf }
end

lemma bsupr_le_of_nonneg (hr : 0 ≤ r) (hf : ∀ a, p a → f a ≤ r) : (⨆ (a : α) (ha : p a), f a) ≤ r :=
csupr_le_of_nonneg hr $ λ a, csupr_le_of_nonneg hr $ hf _

lemma bsupr_mono (hg : bdd_above (set.range g)) (hg' : ∀ a, q a → 0 ≤ g a) (hfg : ∀ a, f a ≤ g a)
  (hpq : ∀ a, p a → q a) :
  (⨆ (a : α) (ha : p a), f a) ≤ ⨆ (a : α) (ha : q a), g a :=
csupr_le_csupr begin
  obtain ⟨x, hx⟩ := hg,
  refine ⟨max 0 x, _⟩,
  rintro _ ⟨a, rfl⟩,
  casesI is_empty_or_nonempty (q a),
  { dsimp,
    rw csupr_empty,
    exact le_max_left _ _ },
  { exact (csupr_le $ λ _, hx $ set.mem_range_self _).trans (le_max_right _ _) }
end $ λ a, begin
  casesI is_empty_or_nonempty (p a),
  { rw csupr_empty,
    exact csupr_nonneg (hg' _) },
  casesI is_empty_or_nonempty (q a),
  { haveI := function.is_empty (hpq a),
    rwa [csupr_empty, csupr_empty] },
  { exact csupr_le (λ ha, (hfg _).trans csupr_const.ge) }
end

lemma Inf_le_of_nonneg {s : set ℝ} {a : ℝ} (ha : a ∈ s) (h : 0 ≤ a) : Inf s ≤ a :=
begin
  by_cases hs : bdd_below s,
  { exact cInf_le hs ha },
  { rwa Inf_of_not_bdd_below hs }
end

lemma Inf_le_of_le_of_nonneg {s : set ℝ} {a b : ℝ} (hb : b ∈ s) (ha : 0 ≤ a) (h : b ≤ a) :
  Inf s ≤ a :=
begin
  by_cases hs : bdd_below s,
  { exact cInf_le_of_le hs hb h },
  { rwa Inf_of_not_bdd_below hs }
end

end real

open real

variables {E : Type*} {ε : ℝ}

section semi_normed_group
variables (E ε) [semi_normed_group E]

/-- Modulus of convexity. -/
noncomputable def convex_mod (ε : ℝ) : ℝ :=
1 - (⨆ (x : E) (hx : ∥x∥ ≤ 1) (y : E) (hy : ∥y∥ ≤ 1) (hxy : ε ≤ dist x y), ∥x + y∥) / 2

/-- Characteristic of convexity. -/
noncomputable def convex_char : ℝ := Sup {ε | convex_mod E ε = 0}

lemma convex_mod_nonneg : 0 ≤ convex_mod E ε :=
begin
  refine sub_nonneg_of_le ((div_le_one _).2 _),
  { exact zero_lt_two },
  refine bsupr_le_of_nonneg zero_le_two (λ x hx, bsupr_le_of_nonneg zero_le_two $ λ y hy,
    csupr_le_of_nonneg zero_le_two $ λ h, _),
  rw [←sub_neg_eq_add, ←one_add_one_eq_two],
  exact (norm_sub_le _ _).trans (add_le_add hx $ by rwa norm_neg),
end

lemma convex_mod_le_one : convex_mod E ε ≤ 1 :=
sub_le_self _ $ div_nonneg
  (bsupr_nonneg $ λ x _, bsupr_nonneg $ λ y _, csupr_nonneg $ λ _, norm_nonneg _) zero_le_two

lemma convex_mod_mono : monotone (convex_mod E) :=
begin
  rintro a b hab,
  refine sub_le_sub_left (div_le_div_of_le zero_le_two _) _,
  refine bsupr_mono_right _ _,
  sorry,
  sorry
end

lemma convex_mod_of_nonpos {ε : ℝ} (hε : ε ≤ 0) : convex_mod E ε = 0 :=
begin
  refine le_antisymm (sub_nonpos_of_le $ (one_le_div _).2 _) (convex_mod_nonneg E ε),
  { exact zero_lt_two },
  sorry
end

lemma convex_mod_of_two_lt {ε : ℝ} (hε : 2 < ε) : convex_mod E ε = 1 :=
begin
  rw [convex_mod, bsupr_zero (λ x hx, _), zero_div, sub_zero],
  refine bsupr_zero (λ y hy, csupr_zero $ λ h, _),
  refine (hε.not_le $ h.trans $ (dist_le_norm_add_norm _ _).trans _).elim,
  rw ←one_add_one_eq_two,
  exact add_le_add hx hy,
end

variables {E}

@[simp] lemma convex_mod_zero {x : E} (hx : ∥x∥ = 1) : convex_mod E 0 = 0 :=
begin
  refine le_antisymm (sub_nonpos_of_le $ (one_le_div $ @zero_lt_two ℝ _ _).2 _)
    (convex_mod_nonneg E 0),
  refine le_bcsupr_of_le _ _ _,
  refine le_bsupr_of_le
  have := (1 : E),
  refine sub_eq_zero.2 _,
  rw [eq_comm, div_eq_one_iff (@two_ne_zero ℝ _ _)],
  refine le_antisymm,
end

lemma convex_char_nonneg {x : E} (hx : ∥x∥ = 1) : 0 ≤ convex_char E :=
Sup_nonneg' (convex_mod_zero hx) le_rfl

variables (E)

lemma convex_char_le_two : convex_char E ≤ 2 :=
Sup_le_of_nonneg zero_le_two $ λ ε hε, le_of_not_lt $ λ h,
  zero_ne_one $ hε.symm.trans $ convex_mod_of_two_lt E h

lemma convex_mod_eq_one_sub_supr_sphere :
  convex_mod E ε = 1 - (⨆ (x : E) (hx : ∥x∥ = 1) (y : E) (hy : ∥y∥ = 1) (hxy : ε ≤ dist x y),
    ∥x + y∥) / 2 :=
begin
  sorry
  -- congr' 2,
end

@[simp] lemma convex_mod_eq_zero_iff : convex_mod E ε = 0 ↔ ε ≤ convex_char E :=
sorry

@[simp] lemma convex_mod_pos_iff : 0 < convex_mod E ε ↔ convex_char E < ε :=
sorry

lemma convex_char_eq_Inf : convex_char E = Inf {ε | 0 < convex_mod E ε} :=
begin

end

end semi_normed_group
