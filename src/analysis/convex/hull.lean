/-
Copyright (c) 2020 Yury Kudriashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudriashov, Yaël Dillies
-/
import analysis.convex.basic
import order.closure

/-!
# Convex hull

This file defines the convex hull of a set `s` in a module. `convex_hull 𝕜 s` is the smallest convex
set containing `s`. In order theory speak, this is a closure operator.

## Implementation notes

`convex_hull` is defined as a closure operator. This gives access to the `closure_operator` API
while the impact on writing code is minimal as `convex_hull 𝕜 s` is automatically elaborated as
`⇑(convex_hull 𝕜) s`.
-/

open set

variables {𝕜 E F : Type*}

section convex_hull
section ordered_semiring
variables [ordered_semiring 𝕜]

section add_comm_monoid
variables (𝕜) [add_comm_monoid E] [add_comm_monoid F] [module 𝕜 E] [module 𝕜 F]

/-- The convex hull of a set `s` is the minimal convex set that includes `s`. -/
def convex_hull : closure_operator (set E) :=
closure_operator.mk₃
  (λ s, ⋂ (t : set E) (hst : s ⊆ t) (ht : convex 𝕜 t), t)
  (convex 𝕜)
  (λ s, set.subset_Inter (λ t, set.subset_Inter $ λ hst, set.subset_Inter $ λ ht, hst))
  (λ s, convex_Inter $ λ t, convex_Inter $ λ ht, convex_Inter id)
  (λ s t hst ht, set.Inter_subset_of_subset t $ set.Inter_subset_of_subset hst $
  set.Inter_subset _ ht)

variables (s : set E)

lemma subset_convex_hull : s ⊆ convex_hull 𝕜 s := (convex_hull 𝕜).le_closure s

lemma convex_convex_hull : convex 𝕜 (convex_hull 𝕜 s) := closure_operator.closure_mem_mk₃ s

variables {𝕜 s} {t : set E}

lemma convex_hull_min (hst : s ⊆ t) (ht : convex 𝕜 t) : convex_hull 𝕜 s ⊆ t :=
closure_operator.closure_le_mk₃_iff (show s ≤ t, from hst) ht

@[mono] lemma convex_hull_mono (hst : s ⊆ t) : convex_hull 𝕜 s ⊆ convex_hull 𝕜 t :=
(convex_hull 𝕜).monotone hst

lemma convex.convex_hull_eq {s : set E} (hs : convex 𝕜 s) : convex_hull 𝕜 s = s :=
closure_operator.mem_mk₃_closed hs

@[simp] lemma convex_hull_univ : convex_hull 𝕜 (univ : set E) = univ :=
closure_operator.closure_top (convex_hull 𝕜)

@[simp] lemma convex_hull_empty : convex_hull 𝕜 (∅ : set E) = ∅ := convex_empty.convex_hull_eq

@[simp] lemma convex_hull_empty_iff : convex_hull 𝕜 s = ∅ ↔ s = ∅ :=
begin
  split,
  { intro h,
    rw [←set.subset_empty_iff, ←h],
    exact subset_convex_hull 𝕜 _ },
  { rintro rfl,
    exact convex_hull_empty }
end

@[simp] lemma convex_hull_nonempty_iff : (convex_hull 𝕜 s).nonempty ↔ s.nonempty :=
begin
  rw [←ne_empty_iff_nonempty, ←ne_empty_iff_nonempty, ne.def, ne.def],
  exact not_congr convex_hull_empty_iff,
end

@[simp]
lemma convex_hull_singleton {x : E} : convex_hull 𝕜 ({x} : set E) = {x} :=
(convex_singleton x).convex_hull_eq

lemma convex.convex_remove_iff_not_mem_convex_hull_remove {s : set E} (hs : convex 𝕜 s) (x : E) :
  convex 𝕜 (s \ {x}) ↔ x ∉ convex_hull 𝕜 (s \ {x}) :=
begin
  split,
  { rintro hsx hx,
    rw hsx.convex_hull_eq at hx,
    exact hx.2 (mem_singleton _) },
  rintro hx,
  suffices h : s \ {x} = convex_hull 𝕜 (s \ {x}), { convert convex_convex_hull 𝕜 _ },
  exact subset.antisymm (subset_convex_hull 𝕜 _) (λ y hy, ⟨convex_hull_min (diff_subset _ _) hs hy,
    by { rintro (rfl : y = x), exact hx hy }⟩),
end

lemma is_linear_map.image_convex_hull {f : E → F} (hf : is_linear_map 𝕜 f) :
  f '' (convex_hull 𝕜 s) = convex_hull 𝕜 (f '' s) :=
begin
  apply set.subset.antisymm ,
  { rw set.image_subset_iff,
    exact convex_hull_min (set.image_subset_iff.1 $ subset_convex_hull 𝕜 $ f '' s)
      ((convex_convex_hull 𝕜 (f '' s)).is_linear_preimage hf) },
  { exact convex_hull_min (set.image_subset _ $ subset_convex_hull 𝕜 s)
     ((convex_convex_hull 𝕜 s).is_linear_image hf) }
end

lemma linear_map.image_convex_hull (f : E →ₗ[𝕜] F) :
  f '' (convex_hull 𝕜 s) = convex_hull 𝕜 (f '' s) :=
f.is_linear.image_convex_hull

lemma is_linear_map.convex_hull_image {f : E → F} (hf : is_linear_map 𝕜 f) (s : set E) :
  convex_hull 𝕜 (f '' s) = f '' convex_hull 𝕜 s :=
set.subset.antisymm (convex_hull_min (image_subset _ (subset_convex_hull 𝕜 s)) $
  (convex_convex_hull 𝕜 s).is_linear_image hf)
  (image_subset_iff.2 $ convex_hull_min
    (image_subset_iff.1 $ subset_convex_hull 𝕜 _)
    ((convex_convex_hull 𝕜 _).is_linear_preimage hf))

lemma linear_map.convex_hull_image (f : E →ₗ[𝕜] F) (s : set E) :
  convex_hull 𝕜 (f '' s) = f '' convex_hull 𝕜 s :=
f.is_linear.convex_hull_image s

end add_comm_monoid
end ordered_semiring

section ordered_ring
variables [ordered_ring 𝕜]

section add_comm_group
variables [add_comm_group E] [add_comm_group F] [module 𝕜 E] [module 𝕜 F] (s : set E)

lemma affine_map.image_convex_hull (f : E →ᵃ[𝕜] F) :
  f '' (convex_hull 𝕜 s) = convex_hull 𝕜 (f '' s) :=
begin
  apply set.subset.antisymm,
  { rw set.image_subset_iff,
    refine convex_hull_min _ ((convex_convex_hull 𝕜 (⇑f '' s)).affine_preimage f),
    rw ← set.image_subset_iff,
    exact subset_convex_hull 𝕜 (f '' s) },
  { exact convex_hull_min (set.image_subset _ (subset_convex_hull 𝕜 s))
    ((convex_convex_hull 𝕜 s).affine_image f) }
end

lemma convex_hull_subset_affine_span : convex_hull 𝕜 s ⊆ (affine_span 𝕜 s : set E) :=
convex_hull_min (subset_affine_span 𝕜 s) (affine_span 𝕜 s).convex

@[simp] lemma affine_span_convex_hull : affine_span 𝕜 (convex_hull 𝕜 s) = affine_span 𝕜 s :=
begin
  refine le_antisymm _ (affine_span_mono 𝕜 (subset_convex_hull 𝕜 s)),
  rw affine_span_le,
  exact convex_hull_subset_affine_span s,
end

end add_comm_group
end ordered_ring
end convex_hull
