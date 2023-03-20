/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yaël Dillies
-/
import analysis.normed.group.basic
import topology.metric_space.hausdorff_distance

/-!
# Properties of pointwise addition of sets in normed groups

We explore the relationships between pointwise addition of sets in normed groups, and the norm.
Notably, we show that the sum of bounded sets remain bounded.
-/

open metric set
open_locale pointwise topology

variables {E : Type*}

section seminormed_group
variables [seminormed_group E] {ε δ : ℝ} {s t : set E} {x y : E}

@[to_additive] lemma metric.bounded.mul (hs : bounded s) (ht : bounded t) : bounded (s * t) :=
begin
  obtain ⟨Rs, hRs⟩ : ∃ R, ∀ x ∈ s, ‖x‖ ≤ R := hs.exists_norm_le',
  obtain ⟨Rt, hRt⟩ : ∃ R, ∀ x ∈ t, ‖x‖ ≤ R := ht.exists_norm_le',
  refine bounded_iff_forall_norm_le'.2 ⟨Rs + Rt, _⟩,
  rintro z ⟨x, y, hx, hy, rfl⟩,
  exact norm_mul_le_of_le (hRs x hx) (hRt y hy),
end

@[to_additive] lemma metric.bounded.inv : bounded s → bounded s⁻¹ :=
by { simp_rw [bounded_iff_forall_norm_le', ←image_inv, ball_image_iff, norm_inv'], exact id }

@[to_additive] lemma metric.bounded.div (hs : bounded s) (ht : bounded t) : bounded (s / t) :=
(div_eq_mul_inv _ _).symm.subst $ hs.mul ht.inv

end seminormed_group

section seminormed_comm_group
variables [seminormed_comm_group E] {ε δ : ℝ} {s t : set E} {x y : E}

section emetric
open emetric

@[to_additive]
lemma inf_edist_inv (x : E) (s : set E) : inf_edist x⁻¹ s = inf_edist x s⁻¹ :=
eq_of_forall_le_iff $ λ r, by simp_rw [le_inf_edist, ←image_inv, ball_image_iff, edist_inv]

@[simp, to_additive]
lemma inf_edist_inv_inv (x : E) (s : set E) : inf_edist x⁻¹ s⁻¹ = inf_edist x s :=
by rw [inf_edist_inv, inv_inv]

end emetric

variables (ε δ s t x y)

@[simp, to_additive] lemma inv_thickening : (thickening δ s)⁻¹ = thickening δ s⁻¹ :=
by { simp_rw [thickening, ←inf_edist_inv], refl }

@[simp, to_additive] lemma inv_cthickening : (cthickening δ s)⁻¹ = cthickening δ s⁻¹ :=
by { simp_rw [cthickening, ←inf_edist_inv], refl }

@[simp, to_additive] lemma inv_ball : (ball x δ)⁻¹ = ball x⁻¹ δ :=
by { simp_rw [ball, ←dist_inv], refl }

@[simp, to_additive] lemma inv_closed_ball : (closed_ball x δ)⁻¹ = closed_ball x⁻¹ δ :=
by { simp_rw [closed_ball, ←dist_inv], refl }

@[to_additive] lemma singleton_mul_ball : {x} * ball y δ = ball (x * y) δ :=
by simp only [preimage_mul_ball, image_mul_left, singleton_mul, div_inv_eq_mul, mul_comm y x]

@[to_additive] lemma singleton_div_ball : {x} / ball y δ = ball (x / y) δ :=
by simp_rw [div_eq_mul_inv, inv_ball, singleton_mul_ball]

@[to_additive] lemma ball_mul_singleton : ball x δ * {y} = ball (x * y) δ :=
by rw [mul_comm, singleton_mul_ball, mul_comm y]

@[to_additive] lemma ball_div_singleton : ball x δ / {y} = ball (x / y) δ :=
by simp_rw [div_eq_mul_inv, inv_singleton, ball_mul_singleton]

@[to_additive] lemma singleton_mul_ball_one : {x} * ball 1 δ = ball x δ := by simp

@[to_additive] lemma singleton_div_ball_one : {x} / ball 1 δ = ball x δ :=
by simp [singleton_div_ball]

@[to_additive] lemma ball_one_mul_singleton : ball 1 δ * {x} = ball x δ :=
by simp [ball_mul_singleton]

@[to_additive] lemma ball_one_div_singleton : ball 1 δ / {x} = ball x⁻¹ δ :=
by simp [ball_div_singleton]

@[to_additive] lemma smul_ball_one : x • ball 1 δ = ball x δ :=
by { ext, simp [mem_smul_set_iff_inv_smul_mem, inv_mul_eq_div, dist_eq_norm_div] }

@[simp, to_additive]
lemma singleton_mul_closed_ball : {x} * closed_ball y δ = closed_ball (x * y) δ :=
by simp only [mul_comm y x, preimage_mul_closed_ball, image_mul_left, singleton_mul, div_inv_eq_mul]

@[simp, to_additive]
lemma singleton_div_closed_ball : {x} / closed_ball y δ = closed_ball (x / y) δ :=
by simp_rw [div_eq_mul_inv, inv_closed_ball, singleton_mul_closed_ball]

@[simp, to_additive]
lemma closed_ball_mul_singleton : closed_ball x δ * {y} = closed_ball (x * y) δ :=
by simp [mul_comm _ {y}, mul_comm y]

@[simp, to_additive]
lemma closed_ball_div_singleton : closed_ball x δ / {y} = closed_ball (x / y) δ :=
by simp [div_eq_mul_inv]

@[to_additive]
lemma singleton_mul_closed_ball_one : {x} * closed_ball 1 δ = closed_ball x δ := by simp

@[to_additive]
lemma singleton_div_closed_ball_one : {x} / closed_ball 1 δ = closed_ball x δ := by simp

@[to_additive]
lemma closed_ball_one_mul_singleton : closed_ball 1 δ * {x} = closed_ball x δ := by simp

@[to_additive]
lemma closed_ball_one_div_singleton : closed_ball 1 δ / {x} = closed_ball x⁻¹ δ := by simp

-- This is the `to_additive` version of the below, but it will later follow as a special case of
-- `vadd_closed_ball` for `normed_add_torsor`s, so we give it higher simp priority.
-- (There is no `normed_mul_torsor`, hence the asymmetry between additive and multiplicative
-- versions.)
@[simp, priority 1100] lemma vadd_closed_ball_zero {E : Type*} [seminormed_add_comm_group E] (δ : ℝ)
  (x : E) :
  x +ᵥ metric.closed_ball 0 δ = metric.closed_ball x δ :=
by { ext, simp [mem_vadd_set_iff_neg_vadd_mem, neg_add_eq_sub, dist_eq_norm_sub] }

@[simp] lemma smul_closed_ball_one : x • closed_ball 1 δ = closed_ball x δ :=
by { ext, simp [mem_smul_set_iff_inv_smul_mem, inv_mul_eq_div, dist_eq_norm_div] }

attribute [to_additive] smul_closed_ball_one

@[to_additive] lemma mul_ball_one : s * ball 1 δ = thickening δ s :=
begin
  rw thickening_eq_bUnion_ball,
  convert Union₂_mul (λ x (_ : x ∈ s), {x}) (ball (1 : E) δ),
  exact s.bUnion_of_singleton.symm,
  ext x y,
  simp_rw [singleton_mul_ball, mul_one],
end

@[to_additive]
lemma div_ball_one : s / ball 1 δ = thickening δ s := by simp [div_eq_mul_inv, mul_ball_one]

@[to_additive]
lemma ball_mul_one : ball 1 δ * s = thickening δ s := by rw [mul_comm, mul_ball_one]

@[to_additive]
lemma ball_div_one : ball 1 δ / s = thickening δ s⁻¹ := by simp [div_eq_mul_inv, ball_mul_one]

@[simp, to_additive] lemma mul_ball : s * ball x δ = x • thickening δ s :=
by rw [←smul_ball_one, mul_smul_comm, mul_ball_one]

@[simp, to_additive] lemma div_ball : s / ball x δ = x⁻¹ • thickening δ s :=
by simp [div_eq_mul_inv]

@[simp, to_additive] lemma ball_mul : ball x δ * s = x • thickening δ s :=
by rw [mul_comm, mul_ball]

@[simp, to_additive] lemma ball_div : ball x δ / s = x • thickening δ s⁻¹ :=
by simp [div_eq_mul_inv]

variables {ε δ s t x y}

@[to_additive] lemma is_compact.mul_closed_ball_one (hs : is_compact s) (hδ : 0 ≤ δ) :
  s * closed_ball 1 δ = cthickening δ s :=
begin
  rw hs.cthickening_eq_bUnion_closed_ball hδ,
  ext x,
  simp only [mem_mul, dist_eq_norm_div, exists_prop, mem_Union, mem_closed_ball,
    exists_and_distrib_left, mem_closed_ball_one_iff, ← eq_div_iff_mul_eq'', exists_eq_right],
end

@[to_additive] lemma is_compact.div_closed_ball_one (hs : is_compact s) (hδ : 0 ≤ δ) :
  s / closed_ball 1 δ = cthickening δ s :=
by simp [div_eq_mul_inv, hs.mul_closed_ball_one hδ]

@[to_additive] lemma is_compact.closed_ball_one_mul (hs : is_compact s) (hδ : 0 ≤ δ) :
  closed_ball 1 δ * s = cthickening δ s :=
by rw [mul_comm, hs.mul_closed_ball_one hδ]

@[to_additive] lemma is_compact.closed_ball_one_div (hs : is_compact s) (hδ : 0 ≤ δ) :
  closed_ball 1 δ / s = cthickening δ s⁻¹ :=
by simp [div_eq_mul_inv, mul_comm, hs.inv.mul_closed_ball_one hδ]

@[to_additive] lemma is_compact.mul_closed_ball (hs : is_compact s) (hδ : 0 ≤ δ) (x : E) :
  s * closed_ball x δ = x • cthickening δ s :=
by rw [←smul_closed_ball_one, mul_smul_comm, hs.mul_closed_ball_one hδ]

@[to_additive] lemma is_compact.div_closed_ball (hs : is_compact s) (hδ : 0 ≤ δ) (x : E) :
  s / closed_ball x δ = x⁻¹ • cthickening δ s :=
by simp [div_eq_mul_inv, mul_comm, hs.mul_closed_ball hδ]

@[to_additive] lemma is_compact.closed_ball_mul (hs : is_compact s) (hδ : 0 ≤ δ) (x : E) :
  closed_ball x δ * s = x • cthickening δ s :=
by rw [mul_comm, hs.mul_closed_ball hδ]

@[to_additive] lemma is_compact.closed_ball_div (hs : is_compact s) (hδ : 0 ≤ δ) (x : E) :
  closed_ball x δ * s = x • cthickening δ s :=
by simp [div_eq_mul_inv, mul_comm, hs.closed_ball_mul hδ]

end seminormed_comm_group
