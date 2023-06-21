/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison
-/
import topology.algebra.ring.basic
import topology.algebra.group_with_zero
import topology.local_extr
import field_theory.subfield

/-!
# Topological fields

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A topological division ring is a topological ring whose inversion function is continuous at every
non-zero element.

-/


variables {K : Type*} [division_ring K] [topological_space K]

/-- Left-multiplication by a nonzero element of a topological division ring is proper, i.e.,
inverse images of compact sets are compact. -/
lemma filter.tendsto_cocompact_mul_left₀ [has_continuous_mul K] {a : K} (ha : a ≠ 0) :
  filter.tendsto (λ x : K, a * x) (filter.cocompact K) (filter.cocompact K) :=
filter.tendsto_cocompact_mul_left (inv_mul_cancel ha)

/-- Right-multiplication by a nonzero element of a topological division ring is proper, i.e.,
inverse images of compact sets are compact. -/
lemma filter.tendsto_cocompact_mul_right₀ [has_continuous_mul K] {a : K} (ha : a ≠ 0) :
  filter.tendsto (λ x : K, x * a) (filter.cocompact K) (filter.cocompact K) :=
filter.tendsto_cocompact_mul_right (mul_inv_cancel ha)

variables (K)

/-- A topological division ring is a division ring with a topology where all operations are
    continuous, including inversion. -/
class topological_division_ring extends topological_ring K, has_continuous_inv₀ K : Prop

section subfield

variables {α : Type*} [field α] [topological_space α] [topological_division_ring α]

/-- The (topological-space) closure of a subfield of a topological field is
itself a subfield. -/
def subfield.topological_closure (K : subfield α) : subfield α :=
{ carrier := closure (K : set α),
  inv_mem' := λ x hx,
  begin
    rcases eq_or_ne x 0 with (rfl | h),
    { rwa [inv_zero] },
    { rw [← inv_coe_set, ← set.image_inv],
      exact mem_closure_image (continuous_at_inv₀ h) hx },
  end,
  ..K.to_subring.topological_closure, }

lemma subfield.le_topological_closure (s : subfield α) :
  s ≤ s.topological_closure := subset_closure

lemma subfield.is_closed_topological_closure (s : subfield α) :
  is_closed (s.topological_closure : set α) := is_closed_closure

lemma subfield.topological_closure_minimal
  (s : subfield α) {t : subfield α} (h : s ≤ t) (ht : is_closed (t : set α)) :
  s.topological_closure ≤ t := closure_minimal h ht

end subfield

section affine_homeomorph
/-!
This section is about affine homeomorphisms from a topological field `𝕜` to itself.
Technically it does not require `𝕜` to be a topological field, a topological ring that
happens to be a field is enough.
-/
variables {𝕜 : Type*} [field 𝕜] [topological_space 𝕜] [topological_ring 𝕜]

/--
The map `λ x, a * x + b`, as a homeomorphism from `𝕜` (a topological field) to itself, when `a ≠ 0`.
-/
@[simps]
def affine_homeomorph (a b : 𝕜) (h : a ≠ 0) : 𝕜 ≃ₜ 𝕜 :=
{ to_fun := λ x, a * x + b,
  inv_fun := λ y, (y - b) / a,
  left_inv := λ x, by { simp only [add_sub_cancel], exact mul_div_cancel_left x h, },
  right_inv := λ y, by { simp [mul_div_cancel' _ h], }, }

end affine_homeomorph

section local_extr

variables {α β : Type*} [topological_space α] [linear_ordered_semifield β] {a : α}
open_locale topology

lemma is_local_min.inv {f : α → β} {a : α} (h1 : is_local_min f a) (h2 : ∀ᶠ z in 𝓝 a, 0 < f z) :
  is_local_max f⁻¹ a :=
by filter_upwards [h1, h2] with z h3 h4 using (inv_le_inv h4 h2.self_of_nhds).mpr h3

end local_extr

section preconnected
/-! Some results about functions on preconnected sets valued in a ring or field with a topology. -/

open set
variables {α 𝕜 : Type*} {f g : α → 𝕜} {S : set α}
  [topological_space α] [topological_space 𝕜] [t1_space 𝕜]

/-- If `f` is a function `α → 𝕜` which is continuous on a preconnected set `S`, and
`f ^ 2 = 1` on `S`, then either `f = 1` on `S`, or `f = -1` on `S`. -/
lemma is_preconnected.eq_one_or_eq_neg_one_of_sq_eq [ring 𝕜] [no_zero_divisors 𝕜]
  (hS : is_preconnected S) (hf : continuous_on f S) (hsq : eq_on (f ^ 2) 1 S) :
  (eq_on f 1 S) ∨ (eq_on f (-1) S) :=
begin
  simp_rw [eq_on, pi.one_apply, pi.pow_apply, sq_eq_one_iff] at hsq,
  -- First deal with crazy case where `S` is empty.
  by_cases hSe : ∀ (x:α), x ∉ S,
  { left, intros x hx,
    exfalso, exact hSe x hx, },
  push_neg at hSe,
  choose y hy using hSe,
  suffices : ∀ (x:α), x ∈ S → f x = f y,
  { rcases (hsq hy),
    { left, intros z hz, rw [pi.one_apply z, ←h], exact this z hz, },
    { right, intros z hz, rw [pi.neg_apply, pi.one_apply, ←h], exact this z hz, } },
  refine λ x hx, hS.constant_of_maps_to hf (λ z hz, _) hx hy,
  show f z ∈ ({-1, 1} : set 𝕜),
  { exact mem_insert_iff.mpr (hsq hz).symm,  },
  exact discrete_of_t1_of_finite,
end

/-- If `f, g` are functions `α → 𝕜`, both continuous on a preconnected set `S`, with
`f ^ 2 = g ^ 2` on `S`, and `g z ≠ 0` all `z ∈ S`, then either `f = g` or `f = -g` on
`S`. -/
lemma is_preconnected.eq_or_eq_neg_of_sq_eq [field 𝕜] [has_continuous_inv₀ 𝕜] [has_continuous_mul 𝕜]
  (hS : is_preconnected S) (hf : continuous_on f S) (hg : continuous_on g S)
  (hsq : eq_on (f ^ 2) (g ^ 2) S) (hg_ne : ∀ {x:α}, x ∈ S → g x ≠ 0) :
  (eq_on f g S) ∨ (eq_on f (-g) S) :=
begin
  rcases hS.eq_one_or_eq_neg_one_of_sq_eq (hf.div hg (λ z hz, hg_ne hz)) (λ x hx, _) with h | h,
  { refine or.inl (λ x hx, _),
    rw ←div_eq_one_iff_eq (hg_ne hx),
    exact h hx },
  { refine or.inr (λ x hx, _),
    specialize h hx,
    rwa [pi.div_apply, pi.neg_apply, pi.one_apply, div_eq_iff (hg_ne hx), neg_one_mul] at h,  },
  { rw [pi.one_apply, div_pow, pi.div_apply, hsq hx, div_self],
    exact pow_ne_zero _ (hg_ne hx) },
end

/-- If `f, g` are functions `α → 𝕜`, both continuous on a preconnected set `S`, with
`f ^ 2 = g ^ 2` on `S`, and `g z ≠ 0` all `z ∈ S`, then as soon as `f = g` holds at
one point of `S` it holds for all points. -/
lemma is_preconnected.eq_of_sq_eq [field 𝕜] [has_continuous_inv₀ 𝕜] [has_continuous_mul 𝕜]
  (hS : is_preconnected S) (hf : continuous_on f S) (hg : continuous_on g S)
  (hsq : eq_on (f ^ 2) (g ^ 2) S) (hg_ne : ∀ {x:α}, x ∈ S → g x ≠ 0)
  {y : α} (hy : y ∈ S) (hy' : f y = g y) : eq_on f g S :=
λ x hx, begin
  rcases hS.eq_or_eq_neg_of_sq_eq hf hg @hsq @hg_ne with h | h,
  { exact h hx },
  { rw [h hy, eq_comm, ←sub_eq_zero, sub_eq_add_neg, pi.neg_apply,
      neg_neg, ←mul_two, mul_eq_zero] at hy',
    cases hy', -- need to handle case of `char 𝕜 = 2` separately
    { exfalso, exact hg_ne hy hy' },
    { rw [h hx, pi.neg_apply, eq_comm, ←sub_eq_zero, sub_eq_add_neg, neg_neg,
       ←mul_two, hy', mul_zero], } },
end

end preconnected
