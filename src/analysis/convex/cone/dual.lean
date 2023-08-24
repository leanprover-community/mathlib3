/-
Copyright (c) 2021 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
import analysis.convex.cone.basic
import analysis.inner_product_space.projection

/-!
# Convex cones in inner product spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define `set.inner_dual_cone` to be the cone consisting of all points `y` such that for
all points `x` in a given set `0 ≤ ⟪ x, y ⟫`.

## Main statements

We prove the following theorems:
* `convex_cone.inner_dual_cone_of_inner_dual_cone_eq_self`:
  The `inner_dual_cone` of the `inner_dual_cone` of a nonempty, closed, convex cone is itself.

-/


open set linear_map
open_locale classical pointwise

variables {𝕜 E F G : Type*}


/-! ### The dual cone -/

section dual
variables {H : Type*} [normed_add_comm_group H] [inner_product_space ℝ H] (s t : set H)
open_locale real_inner_product_space

/-- The dual cone is the cone consisting of all points `y` such that for
all points `x` in a given set `0 ≤ ⟪ x, y ⟫`. -/
def set.inner_dual_cone (s : set H) : convex_cone ℝ H :=
{ carrier := { y | ∀ x ∈ s, 0 ≤ ⟪ x, y ⟫ },
  smul_mem' := λ c hc y hy x hx,
  begin
    rw real_inner_smul_right,
    exact mul_nonneg hc.le (hy x hx)
  end,
  add_mem' := λ u hu v hv x hx,
  begin
    rw inner_add_right,
    exact add_nonneg (hu x hx) (hv x hx)
  end }

@[simp] lemma mem_inner_dual_cone (y : H) (s : set H) :
  y ∈ s.inner_dual_cone ↔ ∀ x ∈ s, 0 ≤ ⟪ x, y ⟫ := iff.rfl

@[simp] lemma inner_dual_cone_empty : (∅ : set H).inner_dual_cone = ⊤ :=
eq_top_iff.mpr $ λ x hy y, false.elim

/-- Dual cone of the convex cone {0} is the total space. -/
@[simp] lemma inner_dual_cone_zero : (0 : set H).inner_dual_cone = ⊤ :=
eq_top_iff.mpr $ λ x hy y (hy : y = 0), hy.symm ▸ (inner_zero_left _).ge

/-- Dual cone of the total space is the convex cone {0}. -/
@[simp] lemma inner_dual_cone_univ : (univ : set H).inner_dual_cone = 0 :=
begin
  suffices : ∀ x : H, x ∈ (univ : set H).inner_dual_cone → x = 0,
  { apply set_like.coe_injective,
    exact eq_singleton_iff_unique_mem.mpr ⟨λ x hx, (inner_zero_right _).ge, this⟩ },
  exact λ x hx, by simpa [←real_inner_self_nonpos] using hx (-x) (mem_univ _),
end

lemma inner_dual_cone_le_inner_dual_cone (h : t ⊆ s) :
  s.inner_dual_cone ≤ t.inner_dual_cone :=
λ y hy x hx, hy x (h hx)

lemma pointed_inner_dual_cone : s.inner_dual_cone.pointed :=
λ x hx, by rw inner_zero_right

/-- The inner dual cone of a singleton is given by the preimage of the positive cone under the
linear map `λ y, ⟪x, y⟫`. -/
lemma inner_dual_cone_singleton (x : H) :
  ({x} : set H).inner_dual_cone = (convex_cone.positive ℝ ℝ).comap (innerₛₗ ℝ x) :=
convex_cone.ext $ λ i, forall_eq

lemma inner_dual_cone_union (s t : set H) :
  (s ∪ t).inner_dual_cone = s.inner_dual_cone ⊓ t.inner_dual_cone :=
le_antisymm
  (le_inf (λ x hx y hy, hx _ $ or.inl hy) (λ x hx y hy, hx _ $ or.inr hy))
  (λ x hx y, or.rec (hx.1 _) (hx.2 _))

lemma inner_dual_cone_insert (x : H) (s : set H) :
  (insert x s).inner_dual_cone = set.inner_dual_cone {x} ⊓ s.inner_dual_cone :=
by rw [insert_eq, inner_dual_cone_union]

lemma inner_dual_cone_Union {ι : Sort*} (f : ι → set H) :
  (⋃ i, f i).inner_dual_cone = ⨅ i, (f i).inner_dual_cone :=
begin
  refine le_antisymm (le_infi $ λ i x hx y hy, hx _ $ mem_Union_of_mem _ hy) _,
  intros x hx y hy,
  rw [convex_cone.mem_infi] at hx,
  obtain ⟨j, hj⟩ := mem_Union.mp hy,
  exact hx _ _ hj,
end

lemma inner_dual_cone_sUnion (S : set (set H)) :
  (⋃₀ S).inner_dual_cone = Inf (set.inner_dual_cone '' S) :=
by simp_rw [Inf_image, sUnion_eq_bUnion, inner_dual_cone_Union]

/-- The dual cone of `s` equals the intersection of dual cones of the points in `s`. -/
lemma inner_dual_cone_eq_Inter_inner_dual_cone_singleton :
  (s.inner_dual_cone : set H) = ⋂ i : s, (({i} : set H).inner_dual_cone : set H) :=
by rw [←convex_cone.coe_infi, ←inner_dual_cone_Union, Union_of_singleton_coe]

lemma is_closed_inner_dual_cone : is_closed (s.inner_dual_cone : set H) :=
begin
  -- reduce the problem to showing that dual cone of a singleton `{x}` is closed
  rw inner_dual_cone_eq_Inter_inner_dual_cone_singleton,
  apply is_closed_Inter,
  intros x,

  -- the dual cone of a singleton `{x}` is the preimage of `[0, ∞)` under `inner x`
  have h : ↑({x} : set H).inner_dual_cone = (inner x : H → ℝ) ⁻¹' set.Ici 0,
  { rw [inner_dual_cone_singleton, convex_cone.coe_comap, convex_cone.coe_positive,
      innerₛₗ_apply_coe] },

  -- the preimage is closed as `inner x` is continuous and `[0, ∞)` is closed
  rw h,
  exact is_closed_Ici.preimage (by continuity),
end

lemma convex_cone.pointed_of_nonempty_of_is_closed (K : convex_cone ℝ H)
  (ne : (K : set H).nonempty) (hc : is_closed (K : set H)) : K.pointed :=
begin
  obtain ⟨x, hx⟩ := ne,
  let f : ℝ → H := (• x),

  -- f (0, ∞) is a subset of K
  have fI : f '' set.Ioi 0 ⊆ (K : set H),
  { rintro _ ⟨_, h, rfl⟩,
    exact K.smul_mem (set.mem_Ioi.1 h) hx },

  -- closure of f (0, ∞) is a subset of K
  have clf : closure (f '' set.Ioi 0) ⊆ (K : set H) := hc.closure_subset_iff.2 fI,

  -- f is continuous at 0 from the right
  have fc : continuous_within_at f (set.Ioi (0 : ℝ)) 0 :=
    (continuous_id.smul continuous_const).continuous_within_at,

  -- 0 belongs to the closure of the f (0, ∞)
  have mem₀ := fc.mem_closure_image (by rw [closure_Ioi (0 : ℝ), mem_Ici]),

  -- as 0 ∈ closure f (0, ∞) and closure f (0, ∞) ⊆ K, 0 ∈ K.
  have f₀ : f 0 = 0 := zero_smul ℝ x,
  simpa only [f₀, convex_cone.pointed, ← set_like.mem_coe] using mem_of_subset_of_mem clf mem₀,
end

section complete_space
variables [complete_space H]

/-- This is a stronger version of the Hahn-Banach separation theorem for closed convex cones. This
is also the geometric interpretation of Farkas' lemma. -/
theorem convex_cone.hyperplane_separation_of_nonempty_of_is_closed_of_nmem (K : convex_cone ℝ H)
  (ne : (K : set H).nonempty) (hc : is_closed (K : set H)) {b : H} (disj : b ∉ K) :
  ∃ (y : H), (∀ x : H, x ∈ K → 0 ≤ ⟪x, y⟫_ℝ) ∧ ⟪y, b⟫_ℝ < 0 :=
begin
  -- let `z` be the point in `K` closest to `b`
  obtain ⟨z, hzK, infi⟩ := exists_norm_eq_infi_of_complete_convex ne hc.is_complete K.convex b,

  -- for any `w` in `K`, we have `⟪b - z, w - z⟫_ℝ ≤ 0`
  have hinner := (norm_eq_infi_iff_real_inner_le_zero K.convex hzK).1 infi,

  -- set `y := z - b`
  use z - b,

  split,
  { -- the rest of the proof is a straightforward calculation
    rintros x hxK,
    specialize hinner _ (K.add_mem hxK hzK),
    rwa [add_sub_cancel, real_inner_comm, ← neg_nonneg, neg_eq_neg_one_mul,
         ← real_inner_smul_right, neg_smul, one_smul, neg_sub] at hinner },
  { -- as `K` is closed and non-empty, it is pointed
    have hinner₀ := hinner 0 (K.pointed_of_nonempty_of_is_closed ne hc),

    -- the rest of the proof is a straightforward calculation
    rw [zero_sub, inner_neg_right, right.neg_nonpos_iff] at hinner₀,
    have hbz : b - z ≠ 0 := by { rw sub_ne_zero, contrapose! hzK, rwa ← hzK },
    rw [← neg_zero, lt_neg, ← neg_one_mul, ← real_inner_smul_left, smul_sub, neg_smul, one_smul,
      neg_smul, neg_sub_neg, one_smul],
    calc 0 < ⟪b - z, b - z⟫_ℝ : lt_of_not_le ((iff.not real_inner_self_nonpos).2 hbz)
    ... = ⟪b - z, b - z⟫_ℝ + 0 : (add_zero _).symm
    ... ≤ ⟪b - z, b - z⟫_ℝ + ⟪b - z, z⟫_ℝ : add_le_add rfl.ge hinner₀
    ... = ⟪b - z, b - z + z⟫_ℝ : (inner_add_right _ _ _).symm
    ... = ⟪b - z, b⟫_ℝ : by rw sub_add_cancel },
end

/-- The inner dual of inner dual of a non-empty, closed convex cone is itself.  -/
theorem convex_cone.inner_dual_cone_of_inner_dual_cone_eq_self (K : convex_cone ℝ H)
  (ne : (K : set H).nonempty) (hc : is_closed (K : set H)) :
  ((K : set H).inner_dual_cone : set H).inner_dual_cone = K :=
begin
  ext x,
  split,
  { rw [mem_inner_dual_cone, ← set_like.mem_coe],
    contrapose!,
    exact K.hyperplane_separation_of_nonempty_of_is_closed_of_nmem ne hc },
  { rintro hxK y h,
    specialize h x hxK,
    rwa real_inner_comm },
end

end complete_space
end dual
