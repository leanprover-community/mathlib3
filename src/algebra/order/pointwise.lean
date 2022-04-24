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

variables {α : Type*}

section has_one
variables [has_one α]

section conditionally_complete_lattice
variables [conditionally_complete_lattice α]

@[simp, to_additive] lemma cSup_one : Sup (1 : set α) = 1 := cSup_singleton _
@[simp, to_additive] lemma cInf_one : Inf (1 : set α) = 1 := cInf_singleton _

end conditionally_complete_lattice

variables [complete_lattice α]

@[simp, to_additive] lemma Sup_one : Sup (1 : set α) = 1 := Sup_singleton
@[simp, to_additive] lemma Inf_one : Inf (1 : set α) = 1 := Inf_singleton

end has_one

section group
variables [group α]

section conditionally_complete_lattice
variables [conditionally_complete_lattice α] [covariant_class α α (*) (≤)]
  [covariant_class α α (swap (*)) (≤)] {s : set α}

@[to_additive] lemma cSup_inv (hs₀ : s.nonempty) (hs₁ : bdd_below s) : Sup s⁻¹ = (Inf s)⁻¹ :=
by { rw ←image_inv, exact ((order_iso.inv α).map_cInf' hs₀ hs₁).symm }

@[to_additive] lemma cInf_inv (hs₀ : s.nonempty) (hs₁ : bdd_above s) : Inf s⁻¹ = (Sup s)⁻¹ :=
by { rw ←image_inv, exact ((order_iso.inv α).map_cSup' hs₀ hs₁).symm }

end conditionally_complete_lattice

variables [complete_lattice α] [covariant_class α α (*) (≤)] [covariant_class α α (swap (*)) (≤)]

@[to_additive] lemma Sup_inv (s : set α) : Sup s⁻¹ = (Inf s)⁻¹ :=
by { rw [←image_inv, Sup_image], exact ((order_iso.inv α).map_Inf _).symm }

@[to_additive] lemma Inf_inv (s : set α) : Inf s⁻¹ = (Sup s)⁻¹ :=
by { rw [←image_inv, Inf_image], exact ((order_iso.inv α).map_Sup _).symm }

end group

section comm_group
variables [comm_group α]

section conditionally_complete_linear_order
variables [conditionally_complete_linear_order α] [covariant_class α α (*) (≤)] {s t : set α}

@[to_additive] lemma cSup_mul (hs₀ : s.nonempty) (hs₁ : bdd_above s) (ht₀ : t.nonempty)
  (ht₁ : bdd_above t) :
  Sup (s * t) = Sup s * Sup t :=
begin
  refine cSup_eq_of_forall_le_of_forall_lt_exists_gt (hs₀.mul ht₀) _ (λ a ha, _),
  { rintro f ⟨a, b, ha, hb, rfl⟩,
    exact mul_le_mul' (le_cSup hs₁ ha) (le_cSup ht₁ hb) },
  { obtain ⟨b, hb, hab⟩ := exists_lt_of_lt_cSup hs₀ (div_lt_iff_lt_mul.2 ha),
    obtain ⟨c, hc, hbc⟩ := exists_lt_of_lt_cSup ht₀ (div_lt''.1 hab),
    exact ⟨b * c, mul_mem_mul hb hc, div_lt_iff_lt_mul'.1 hbc⟩ }
end

@[to_additive] lemma cInf_mul (hs₀ : s.nonempty) (hs₁ : bdd_below s) (ht₀ : t.nonempty)
  (ht₁ : bdd_below t) :
  Inf (s * t) = Inf s * Inf t :=
begin
  refine cInf_eq_of_forall_ge_of_forall_gt_exists_lt (hs₀.mul ht₀) _ (λ a ha, _),
  { rintro f ⟨a, b, ha, hb, rfl⟩,
    exact mul_le_mul' (cInf_le hs₁ ha) (cInf_le ht₁ hb) },
  { obtain ⟨b, hb, hab⟩ := exists_lt_of_cInf_lt hs₀ (lt_div_iff_mul_lt.2 ha),
    obtain ⟨c, hc, hbc⟩ := exists_lt_of_cInf_lt ht₀ (lt_div''.1 hab),
    exact ⟨b * c, mul_mem_mul hb hc, lt_div_iff_mul_lt'.1 hbc⟩ }
end

@[to_additive] lemma cSup_div (hs₀ : s.nonempty) (hs₁ : bdd_above s) (ht₀ : t.nonempty)
  (ht₁ : bdd_below t) :
  Sup (s / t) = Sup s / Inf t :=
by rw [div_eq_mul_inv, cSup_mul hs₀ hs₁ ht₀.inv ht₁.inv, cSup_inv ht₀ ht₁, div_eq_mul_inv]

@[to_additive] lemma cInf_div (hs₀ : s.nonempty) (hs₁ : bdd_below s) (ht₀ : t.nonempty)
  (ht₁ : bdd_above t) :
  Inf (s / t) = Inf s / Sup t :=
by rw [div_eq_mul_inv, cInf_mul hs₀ hs₁ ht₀.inv ht₁.inv, cInf_inv ht₀ ht₁, div_eq_mul_inv]

end conditionally_complete_linear_order

variables [complete_linear_order α] [covariant_class α α (*) (≤)]

@[to_additive] lemma Sup_mul (s t : set α) : Sup (s * t) = Sup s * Sup t :=
begin
  refine Sup_eq_of_forall_le_of_forall_lt_exists_gt _ (λ a ha, _),
  { rintro f ⟨a, b, ha, hb, rfl⟩,
    exact mul_le_mul' (le_Sup ha) (le_Sup hb) },
  { obtain ⟨b, hb, hab⟩ := lt_Sup_iff.1 (div_lt_iff_lt_mul.2 ha),
    obtain ⟨c, hc, hbc⟩ := lt_Sup_iff.1 (div_lt''.1 hab),
    exact ⟨b * c, mul_mem_mul hb hc, div_lt_iff_lt_mul'.1 hbc⟩ }
end

@[to_additive] lemma Inf_mul (s t : set α) : Inf (s * t) = Inf s * Inf t :=
begin
  refine Inf_eq_of_forall_ge_of_forall_gt_exists_lt _ (λ a ha, _),
  { rintro f ⟨a, b, ha, hb, rfl⟩,
    exact mul_le_mul' (Inf_le ha) (Inf_le hb) },
  { obtain ⟨b, hb, hab⟩ := Inf_lt_iff.1 (lt_div_iff_mul_lt.2 ha),
    obtain ⟨c, hc, hbc⟩ := Inf_lt_iff.1 (lt_div''.1 hab),
    exact ⟨b * c, mul_mem_mul hb hc, lt_div_iff_mul_lt'.1 hbc⟩ }
end

@[to_additive] lemma Sup_div (s t : set α) : Sup (s / t) = Sup s / Inf t :=
by simp_rw [div_eq_mul_inv, Sup_mul, Sup_inv]

@[to_additive] lemma Inf_div (s t : set α) : Inf (s / t) = Inf s / Sup t :=
by simp_rw [div_eq_mul_inv, Inf_mul, Inf_inv]

end comm_group

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
