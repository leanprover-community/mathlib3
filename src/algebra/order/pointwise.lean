/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Yaël Dillies
-/
import algebra.bounds

/-!
# Pointwise operations on ordered algebraic objects

This file contains lemmas about the effect of pointwise operations on sets with an order structure.

## TODO

`Sup (s • t) = Sup s • Sup t` and `Inf (s • t) = Inf s • Inf t` hold as well but
`covariant_class` is currently not polymorphic enough to state it.
-/

open function set
open_locale pointwise

section
variables {α β γ : Type*} [preorder α] [preorder β] [preorder γ] {f : α → β → γ} {s : set α}
  {t : set β} {a : α} {b : β}

lemma mem_upper_bounds_image2 (h₀ : ∀ b, monotone (swap f b)) (h₁ : ∀ a, monotone (f a))
  (ha : a ∈ upper_bounds s) (hb : b ∈ upper_bounds t) :
  f a b ∈ upper_bounds (image2 f s t) :=
forall_image2_iff.2 $ λ x hx y hy, (h₀ _ $ ha hx).trans $ h₁ _ $ hb hy

lemma mem_lower_bounds_image2 (h₀ : ∀ b, monotone (swap f b)) (h₁ : ∀ a, monotone (f a))
  (ha : a ∈ lower_bounds s) (hb : b ∈ lower_bounds t) :
  f a b ∈ lower_bounds (image2 f s t) :=
forall_image2_iff.2 $ λ x hx y hy, (h₀ _ $ ha hx).trans $ h₁ _ $ hb hy

lemma image2_upper_bounds_subset_upper_bounds_image2 (h₀ : ∀ b, monotone (swap f b)) (h₁ : ∀ a, monotone (f a)) :
  image2 f (upper_bounds s) (upper_bounds t) ⊆ upper_bounds (image2 f s t) :=
by { rintro _ ⟨a, b, ha, hb, rfl⟩, exact mem_upper_bounds_image2 h₀ h₁ ha hb }

lemma image2_lower_bounds_subset_lower_bounds_image2 (h₀ : ∀ b, monotone (swap f b)) (h₁ : ∀ a, monotone (f a)) :
  image2 f (lower_bounds s) (lower_bounds t) ⊆ lower_bounds (image2 f s t) :=
by { rintro _ ⟨a, b, ha, hb, rfl⟩, exact mem_lower_bounds_image2 h₀ h₁ ha hb }

lemma bdd_above.image2 (h₀ : ∀ b, monotone (swap f b)) (h₁ : ∀ a, monotone (f a)) :
  bdd_above s → bdd_above t → bdd_above (image2 f s t) :=
by { rintro ⟨a, ha⟩ ⟨b, hb⟩, exact ⟨f a b, mem_upper_bounds_image2 h₀ h₁ ha hb⟩ }

lemma bdd_below.image2 (h₀ : ∀ b, monotone (swap f b)) (h₁ : ∀ a, monotone (f a)) :
  bdd_below s → bdd_below t → bdd_below (image2 f s t) :=
by { rintro ⟨a, ha⟩ ⟨b, hb⟩, exact ⟨f a b, mem_lower_bounds_image2 h₀ h₁ ha hb⟩ }

end

section
variables {α β γ : Type*} [complete_lattice α] [complete_lattice β] [complete_lattice γ]
  {f : α → β → γ} {s : set α} {t : set β}

open order_dual

lemma bsupr_prod {f : α × β → γ} : (⨆ x ∈ s ×ˢ t, f x) = ⨆ (a ∈ s) (b ∈ t), f (a, b) :=
by { simp_rw [supr_prod, mem_prod, supr_and], exact supr_congr (λ _, supr_comm) }

lemma binfi_prod {f : α × β → γ} : (⨅ x ∈ s ×ˢ t, f x) = ⨅ (a ∈ s) (b ∈ t), f (a, b) :=
by { simp_rw [infi_prod, mem_prod, infi_and], exact infi_congr (λ _, infi_comm) }

lemma Sup_image2 : Sup (image2 f s t) = ⨆ (a ∈ s) (b ∈ t), f a b :=
by rw [←image_prod, Sup_image, bsupr_prod]

lemma Inf_image2 : Inf (image2 f s t) = ⨅ (a ∈ s) (b ∈ t), f a b :=
by rw [←image_prod, Inf_image, binfi_prod]

variables {l u : α → β → γ} {l₁ u₁ : β → γ → α} {l₂ u₂ : α → γ → β}

lemma Sup_image2_eq_Sup_Sup (h₁ : ∀ b, galois_connection (swap l b) (u₁ b))
  (h₂ : ∀ a, galois_connection (l a) (u₂ a)) :
  Sup (image2 l s t) = l (Sup s) (Sup t) :=
by simp_rw [Sup_image2, ←(h₂ _).l_Sup, ←(h₁ _).l_Sup]

lemma Sup_image2_eq_Sup_Inf (h₁ : ∀ b, galois_connection (swap l b) (u₁ b))
  (h₂ : ∀ a, galois_connection (l a ∘ of_dual) (to_dual ∘ u₂ a)) :
  Sup (image2 l s t) = l (Sup s) (Inf t) :=
@Sup_image2_eq_Sup_Sup _ βᵒᵈ _ _ _ _ _ _ _ _ _ h₁ h₂

lemma Sup_image2_eq_Inf_Sup (h₁ : ∀ b, galois_connection (swap l b ∘ of_dual) (to_dual ∘ u₁ b))
  (h₂ : ∀ a, galois_connection (l a) (u₂ a)) :
  Sup (image2 l s t) = l (Inf s) (Sup t) :=
@Sup_image2_eq_Sup_Sup αᵒᵈ _ _ _ _ _ _ _ _ _ _ h₁ h₂

lemma Sup_image2_eq_Inf_Inf (h₁ : ∀ b, galois_connection (swap l b ∘ of_dual) (to_dual ∘ u₁ b))
  (h₂ : ∀ a, galois_connection (l a ∘ of_dual) (to_dual ∘ u₂ a)) :
  Sup (image2 l s t) = l (Inf s) (Inf t) :=
@Sup_image2_eq_Sup_Sup αᵒᵈ βᵒᵈ _ _ _ _ _ _ _ _ _ h₁ h₂

lemma Inf_image2_eq_Inf_Inf (h₁ : ∀ b, galois_connection (l₁ b) (swap u b))
  (h₂ : ∀ a, galois_connection (l₂ a) (u a)) :
  Inf (image2 u s t) = u (Inf s) (Inf t) :=
by simp_rw [Inf_image2, ←(h₂ _).u_Inf, ←(h₁ _).u_Inf]

lemma Inf_image2_eq_Inf_Sup (h₁ : ∀ b, galois_connection (l₁ b) (swap u b))
  (h₂ : ∀ a, galois_connection (to_dual ∘ l₂ a) (u a ∘ of_dual)) :
  Inf (image2 u s t) = u (Inf s) (Sup t) :=
@Inf_image2_eq_Inf_Inf _ βᵒᵈ _ _ _ _ _ _ _ _ _ h₁ h₂

lemma Inf_image2_eq_Sup_Inf (h₁ : ∀ b, galois_connection (to_dual ∘ l₁ b) (swap u b ∘ of_dual))
  (h₂ : ∀ a, galois_connection (l₂ a) (u a)) :
  Inf (image2 u s t) = u (Sup s) (Inf t) :=
@Inf_image2_eq_Inf_Inf αᵒᵈ _ _ _ _ _ _ _ _ _ _ h₁ h₂

lemma Inf_image2_eq_Sup_Sup (h₁ : ∀ b, galois_connection (to_dual ∘ l₁ b) (swap u b ∘ of_dual))
  (h₂ : ∀ a, galois_connection (to_dual ∘ l₂ a) (u a ∘ of_dual)) :
  Inf (image2 u s t) = u (Sup s) (Sup t) :=
@Inf_image2_eq_Inf_Inf αᵒᵈ βᵒᵈ _ _ _ _ _ _ _ _ _ h₁ h₂

end

open set

section
variables {α β γ : Type*} [conditionally_complete_lattice α] [conditionally_complete_lattice β]
  [conditionally_complete_lattice γ] {f : α → β → γ} {s : set α} {t : set β}

open order_dual

lemma csupr_le_iff {ι : Sort*} [nonempty ι] {f : ι → α} {a : α} (hf : bdd_above (range f)) :
  supr f ≤ a ↔ ∀ i, f i ≤ a :=
(is_lub_le_iff $ is_lub_csupr hf).trans forall_range_iff

lemma le_cinfi_iff {ι : Sort*} [nonempty ι] {f : ι → α} {a : α} (hf : bdd_below (range f)) :
  a ≤ infi f ↔ ∀ i, a ≤ f i :=
(le_is_glb_iff $ is_glb_cinfi hf).trans forall_range_iff

lemma bcsupr_le_iff {ι : Type*} {s : set ι} {f : ι → α} {a : α} (hs : s.nonempty)
  (hf : bdd_above (f '' s)) :
  (⨆ i : s, f i) ≤ a ↔ ∀ i ∈ s, f i ≤ a :=
(is_lub_le_iff $ is_lub_csupr_set hf hs).trans ball_image_iff

lemma le_bcinfi_iff {ι : Type*} {s : set ι} {f : ι → α} {a : α} (hs : s.nonempty)
  (hf : bdd_below (f '' s)) :
  a ≤ (⨅ i : s, f i) ↔ ∀ i ∈ s, a ≤ f i :=
(le_is_glb_iff $ is_glb_cinfi_set hf hs).trans ball_image_iff

variables {l u : α → β → γ} {l₁ u₁ : β → γ → α} {l₂ u₂ : α → γ → β}

lemma cSup_image2_eq_cSup_cSup (h₁ : ∀ b, galois_connection (swap l b) (u₁ b))
  (h₂ : ∀ a, galois_connection (l a) (u₂ a))
  (hs₀ : s.nonempty) (hs₁ : bdd_above s) (ht₀ : t.nonempty) (ht₁ : bdd_above t) :
  Sup (image2 l s t) = l (Sup s) (Sup t) :=
begin
  refine eq_of_forall_ge_iff (λ c, _),
  rw [cSup_le_iff (hs₁.image2 (λ _, (h₁ _).monotone_l) (λ _, (h₂ _).monotone_l) ht₁)
    (hs₀.image2 ht₀), forall_image2_iff, forall₂_swap, (h₂ _).le_iff_le, cSup_le_iff ht₁ ht₀],
  simp_rw [←(h₂ _).le_iff_le, (h₁ _).le_iff_le, cSup_le_iff hs₁ hs₀],
end

lemma cSup_image2_eq_cSup_cInf (h₁ : ∀ b, galois_connection (swap l b) (u₁ b))
  (h₂ : ∀ a, galois_connection (l a ∘ of_dual) (to_dual ∘ u₂ a)) :
  s.nonempty → bdd_above s → t.nonempty → bdd_below t → Sup (image2 l s t) = l (Sup s) (Inf t) :=
@cSup_image2_eq_cSup_cSup _ βᵒᵈ _ _ _ _ _ _ _ _ _ h₁ h₂

lemma cSup_image2_eq_cInf_cSup (h₁ : ∀ b, galois_connection (swap l b ∘ of_dual) (to_dual ∘ u₁ b))
  (h₂ : ∀ a, galois_connection (l a) (u₂ a)) :
  s.nonempty → bdd_below s → t.nonempty → bdd_above t → Sup (image2 l s t) = l (Inf s) (Sup t) :=
@cSup_image2_eq_cSup_cSup αᵒᵈ _ _ _ _ _ _ _ _ _ _ h₁ h₂

lemma cSup_image2_eq_cInf_cInf (h₁ : ∀ b, galois_connection (swap l b ∘ of_dual) (to_dual ∘ u₁ b))
  (h₂ : ∀ a, galois_connection (l a ∘ of_dual) (to_dual ∘ u₂ a)) :
  s.nonempty → bdd_below s → t.nonempty → bdd_below t → Sup (image2 l s t) = l (Inf s) (Inf t) :=
@cSup_image2_eq_cSup_cSup αᵒᵈ βᵒᵈ _ _ _ _ _ _ _ _ _ h₁ h₂

lemma cInf_image2_eq_cInf_cInf (h₁ : ∀ b, galois_connection (l₁ b) (swap u b))
  (h₂ : ∀ a, galois_connection (l₂ a) (u a)) :
  s.nonempty → bdd_below s → t.nonempty → bdd_below t →
  Inf (image2 u s t) = u (Inf s) (Inf t) :=
@cSup_image2_eq_cSup_cSup αᵒᵈ βᵒᵈ γᵒᵈ _ _ _ _ _ _ l₁ l₂ (λ _, (h₁ _).dual) (λ _, (h₂ _).dual)

lemma cInf_image2_eq_cInf_cSup (h₁ : ∀ b, galois_connection (l₁ b) (swap u b))
  (h₂ : ∀ a, galois_connection (to_dual ∘ l₂ a) (u a ∘ of_dual)) :
  s.nonempty → bdd_below s → t.nonempty → bdd_above t → Inf (image2 u s t) = u (Inf s) (Sup t) :=
@cInf_image2_eq_cInf_cInf _ βᵒᵈ _ _ _ _ _ _ _ _ _ h₁ h₂

lemma cInf_image2_eq_cSup_cInf (h₁ : ∀ b, galois_connection (to_dual ∘ l₁ b) (swap u b ∘ of_dual))
  (h₂ : ∀ a, galois_connection (l₂ a) (u a)) :
  s.nonempty → bdd_above s → t.nonempty → bdd_below t → Inf (image2 u s t) = u (Sup s) (Inf t) :=
@cInf_image2_eq_cInf_cInf αᵒᵈ _ _ _ _ _ _ _ _ _ _ h₁ h₂

lemma cInf_image2_eq_cSup_cSup (h₁ : ∀ b, galois_connection (to_dual ∘ l₁ b) (swap u b ∘ of_dual))
  (h₂ : ∀ a, galois_connection (to_dual ∘ l₂ a) (u a ∘ of_dual)) :
  s.nonempty →  bdd_above s → t.nonempty → bdd_above t → Inf (image2 u s t) = u (Sup s) (Sup t) :=
@cInf_image2_eq_cInf_cInf αᵒᵈ βᵒᵈ _ _ _ _ _ _ _ _ _ h₁ h₂

end

variables {α : Type*}

section conditionally_complete_lattice
variables [conditionally_complete_lattice α]

section has_one
variables [has_one α]

@[simp, to_additive] lemma cSup_one : Sup (1 : set α) = 1 := cSup_singleton _
@[simp, to_additive] lemma cInf_one : Inf (1 : set α) = 1 := cInf_singleton _

end has_one

section group
variables [group α] [covariant_class α α (*) (≤)] [covariant_class α α (swap (*)) (≤)] {s t : set α}

@[to_additive] lemma cSup_inv (hs₀ : s.nonempty) (hs₁ : bdd_below s) : Sup s⁻¹ = (Inf s)⁻¹ :=
by { rw ←image_inv, exact ((order_iso.inv α).map_cInf' hs₀ hs₁).symm }

@[to_additive] lemma cInf_inv (hs₀ : s.nonempty) (hs₁ : bdd_above s) : Inf s⁻¹ = (Sup s)⁻¹ :=
by { rw ←image_inv, exact ((order_iso.inv α).map_cSup' hs₀ hs₁).symm }

@[to_additive] lemma cSup_mul :
  s.nonempty → bdd_above s → t.nonempty → bdd_above t → Sup (s * t) = Sup s * Sup t :=
cSup_image2_eq_cSup_cSup (λ _, (order_iso.mul_right _).to_galois_connection) $
  λ _, (order_iso.mul_left _).to_galois_connection

@[to_additive] lemma cInf_mul :
  s.nonempty → bdd_below s → t.nonempty → bdd_below t → Inf (s * t) = Inf s * Inf t :=
cInf_image2_eq_cInf_cInf (λ _, (order_iso.mul_right _).symm.to_galois_connection) $
  λ _, (order_iso.mul_left _).symm.to_galois_connection

@[to_additive] lemma cSup_div (hs₀ : s.nonempty) (hs₁ : bdd_above s) (ht₀ : t.nonempty)
  (ht₁ : bdd_below t) :
  Sup (s / t) = Sup s / Inf t :=
by rw [div_eq_mul_inv, cSup_mul hs₀ hs₁ ht₀.inv ht₁.inv, cSup_inv ht₀ ht₁, div_eq_mul_inv]

@[to_additive] lemma cInf_div (hs₀ : s.nonempty) (hs₁ : bdd_below s) (ht₀ : t.nonempty)
  (ht₁ : bdd_above t) :
  Inf (s / t) = Inf s / Sup t :=
by rw [div_eq_mul_inv, cInf_mul hs₀ hs₁ ht₀.inv ht₁.inv, cInf_inv ht₀ ht₁, div_eq_mul_inv]

end group
end conditionally_complete_lattice

section complete_lattice
variables [complete_lattice α]

section has_one
variables [has_one α]

@[simp, to_additive] lemma Sup_one : Sup (1 : set α) = 1 := Sup_singleton
@[simp, to_additive] lemma Inf_one : Inf (1 : set α) = 1 := Inf_singleton

end has_one

section group
variables [group α] [covariant_class α α (*) (≤)] [covariant_class α α (swap (*)) (≤)] (s t : set α)

@[to_additive] lemma Sup_inv (s : set α) : Sup s⁻¹ = (Inf s)⁻¹ :=
by { rw [←image_inv, Sup_image], exact ((order_iso.inv α).map_Inf _).symm }

@[to_additive] lemma Inf_inv (s : set α) : Inf s⁻¹ = (Sup s)⁻¹ :=
by { rw [←image_inv, Inf_image], exact ((order_iso.inv α).map_Sup _).symm }

@[to_additive] lemma Sup_mul : Sup (s * t) = Sup s * Sup t :=
Sup_image2_eq_Sup_Sup (λ _, (order_iso.mul_right _).to_galois_connection) $
  λ _, (order_iso.mul_left _).to_galois_connection

@[to_additive] lemma Inf_mul : Inf (s * t) = Inf s * Inf t :=
Inf_image2_eq_Inf_Inf (λ _, (order_iso.mul_right _).symm.to_galois_connection) $
  λ _, (order_iso.mul_left _).symm.to_galois_connection

@[to_additive] lemma Sup_div : Sup (s / t) = Sup s / Inf t :=
by simp_rw [div_eq_mul_inv, Sup_mul, Sup_inv]

@[to_additive] lemma Inf_div : Inf (s / t) = Inf s / Sup t :=
by simp_rw [div_eq_mul_inv, Inf_mul, Inf_inv]

end group
end complete_lattice

namespace linear_ordered_field

variables {K : Type*} [linear_ordered_field K] {a b r : K} (hr : 0 < r)
open set

include hr

lemma smul_Ioo : r • Ioo a b = Ioo (r • a) (r • b) :=
begin
  ext x,
  simp only [mem_smul_set, smul_eq_mul, mem_Ioo],
  split,
  { rintro ⟨a, ⟨a_h_left_left, a_h_left_right⟩, rfl⟩, split,
    exact (mul_lt_mul_left hr).mpr a_h_left_left,
    exact (mul_lt_mul_left hr).mpr a_h_left_right, },
  { rintro ⟨a_left, a_right⟩,
    use x / r,
    refine ⟨⟨(lt_div_iff' hr).mpr a_left, (div_lt_iff' hr).mpr a_right⟩, _⟩,
    rw mul_div_cancel' _ (ne_of_gt hr), }
end

lemma smul_Icc : r • Icc a b = Icc (r • a) (r • b) :=
begin
  ext x,
  simp only [mem_smul_set, smul_eq_mul, mem_Icc],
  split,
  { rintro ⟨a, ⟨a_h_left_left, a_h_left_right⟩, rfl⟩, split,
    exact (mul_le_mul_left hr).mpr a_h_left_left,
    exact (mul_le_mul_left hr).mpr a_h_left_right, },
  { rintro ⟨a_left, a_right⟩,
    use x / r,
    refine ⟨⟨(le_div_iff' hr).mpr a_left, (div_le_iff' hr).mpr a_right⟩, _⟩,
    rw mul_div_cancel' _ (ne_of_gt hr), }
end

lemma smul_Ico : r • Ico a b = Ico (r • a) (r • b) :=
begin
  ext x,
  simp only [mem_smul_set, smul_eq_mul, mem_Ico],
  split,
  { rintro ⟨a, ⟨a_h_left_left, a_h_left_right⟩, rfl⟩, split,
    exact (mul_le_mul_left hr).mpr a_h_left_left,
    exact (mul_lt_mul_left hr).mpr a_h_left_right, },
  { rintro ⟨a_left, a_right⟩,
    use x / r,
    refine ⟨⟨(le_div_iff' hr).mpr a_left, (div_lt_iff' hr).mpr a_right⟩, _⟩,
    rw mul_div_cancel' _ (ne_of_gt hr), }
end

lemma smul_Ioc : r • Ioc a b = Ioc (r • a) (r • b) :=
begin
  ext x,
  simp only [mem_smul_set, smul_eq_mul, mem_Ioc],
  split,
  { rintro ⟨a, ⟨a_h_left_left, a_h_left_right⟩, rfl⟩, split,
    exact (mul_lt_mul_left hr).mpr a_h_left_left,
    exact (mul_le_mul_left hr).mpr a_h_left_right, },
  { rintro ⟨a_left, a_right⟩,
    use x / r,
    refine ⟨⟨(lt_div_iff' hr).mpr a_left, (div_le_iff' hr).mpr a_right⟩, _⟩,
    rw mul_div_cancel' _ (ne_of_gt hr), }
end

lemma smul_Ioi : r • Ioi a = Ioi (r • a) :=
begin
  ext x,
  simp only [mem_smul_set, smul_eq_mul, mem_Ioi],
  split,
  { rintro ⟨a_w, a_h_left, rfl⟩,
    exact (mul_lt_mul_left hr).mpr a_h_left, },
  { rintro h,
    use x / r,
    split,
    exact (lt_div_iff' hr).mpr h,
    exact mul_div_cancel' _ (ne_of_gt hr), }
end

lemma smul_Iio : r • Iio a = Iio (r • a) :=
begin
  ext x,
  simp only [mem_smul_set, smul_eq_mul, mem_Iio],
  split,
  { rintro ⟨a_w, a_h_left, rfl⟩,
    exact (mul_lt_mul_left hr).mpr a_h_left, },
  { rintro h,
    use x / r,
    split,
    exact (div_lt_iff' hr).mpr h,
    exact mul_div_cancel' _ (ne_of_gt hr), }
end

lemma smul_Ici : r • Ici a = Ici (r • a) :=
begin
  ext x,
  simp only [mem_smul_set, smul_eq_mul, mem_Ioi],
  split,
  { rintro ⟨a_w, a_h_left, rfl⟩,
    exact (mul_le_mul_left hr).mpr a_h_left, },
  { rintro h,
    use x / r,
    split,
    exact (le_div_iff' hr).mpr h,
    exact mul_div_cancel' _ (ne_of_gt hr), }
end

lemma smul_Iic : r • Iic a = Iic (r • a) :=
begin
  ext x,
  simp only [mem_smul_set, smul_eq_mul, mem_Iio],
  split,
  { rintro ⟨a_w, a_h_left, rfl⟩,
    exact (mul_le_mul_left hr).mpr a_h_left, },
  { rintro h,
    use x / r,
    split,
    exact (div_le_iff' hr).mpr h,
    exact mul_div_cancel' _ (ne_of_gt hr), }
end
end linear_ordered_field
