/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import topology.continuous_function.bounded
import analysis.normed_space.linear_isometry
import tactic.equiv_rw

/-!
# Continuous functions on a compact space

Continuous functions `C(α, β)` from a compact space `α` to a metric space `β`
are automatically bounded, and so gain various structures inherited from `α →ᵇ β`.

This file transfers these structures, and restates some, but not all of the lemmas
characterising these structures.

If you need a lemma which is proved about `α →ᵇ β` but not for `C(α, β)` when `α` is compact,
you should restate it here. You can also use
`bounded_continuous_function.equiv_continuous_map_of_compact` to functions back and forth.

-/

noncomputable theory
open_locale topological_space classical nnreal bounded_continuous_function

open set filter metric

variables (α : Type*) (β : Type*) [topological_space α] [compact_space α] [normed_group β]

namespace bounded_continuous_function

/--
When `α` is compact, the bounded continuous maps `α →ᵇ 𝕜` are
equivalent to `C(α, 𝕜)`.
-/
@[simps]
def equiv_continuous_map_of_compact [compact_space α] : (α →ᵇ β) ≃ C(α, β) :=
⟨forget_boundedness α β, mk_of_compact, λ f, by { ext, refl, }, λ f, by { ext, refl, }⟩

/--
When `α` is compact, the bounded continuous maps `α →ᵇ 𝕜` are
additively equivalent to `C(α, 𝕜)`.
-/
@[simps]
def add_equiv_continuous_map_of_compact : (α →ᵇ β) ≃+ C(α, β) :=
{ ..forget_boundedness_add_hom α β,
  ..equiv_continuous_map_of_compact α β, }

@[simp]
lemma add_equiv_continuous_map_of_compact_to_equiv :
  (add_equiv_continuous_map_of_compact α β).to_equiv = equiv_continuous_map_of_compact α β :=
rfl

end bounded_continuous_function

open bounded_continuous_function

namespace continuous_map

instance : metric_space C(α,β) :=
metric_space.induced
  (equiv_continuous_map_of_compact α β).symm
  (equiv_continuous_map_of_compact α β).symm.injective
  (by apply_instance)

variables (α β)
/--
When `α` is compact, and `β` is a metric space, the bounded continuous maps `α →ᵇ β` are
isometric to `C(α, β)`.
-/
@[simps]
def isometric_continuous_map_of_compact :
  (α →ᵇ β) ≃ᵢ C(α, β) :=
{ isometry_to_fun := λ x y, rfl,
  to_equiv := equiv_continuous_map_of_compact α β }

-- TODO at some point we will need lemmas characterising this norm!
-- At the moment the only way to reason about it is to transfer `f : C(α,β)` back to `α →ᵇ β`.
instance : has_norm C(α,β) :=
{ norm := λ x, dist x 0 }

instance : normed_group C(α,β) :=
{ dist_eq := λ x y,
  begin
    change dist x y = dist (x-y) 0,
     -- it would be nice if `equiv_rw` could rewrite in multiple places at once
    equiv_rw (equiv_continuous_map_of_compact α β).symm at x,
    equiv_rw (equiv_continuous_map_of_compact α β).symm at y,
    have p : dist x y = dist (x-y) 0, { rw dist_eq_norm, rw dist_zero_right, },
    convert p,
    exact ((add_equiv_continuous_map_of_compact α β).map_sub _ _).symm,
  end, }

variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 β]

instance : normed_space 𝕜 C(α,β) :=
{ norm_smul_le := λ c f,
  begin
    equiv_rw (equiv_continuous_map_of_compact α β).symm at f,
    exact le_of_eq (norm_smul c f),
  end }

variables {R : Type*} [normed_ring R]

instance : normed_ring C(α,R) :=
{ norm_mul := λ f g,
  begin
    equiv_rw (equiv_continuous_map_of_compact α R).symm at f,
    equiv_rw (equiv_continuous_map_of_compact α R).symm at g,
    exact norm_mul_le f g,
  end,
  ..(infer_instance : normed_group C(α,R)) }

variables (α 𝕜)

/--
When `α` is compact and `𝕜` is a normed field,
the `𝕜`-algebra of bounded continuous maps `α →ᵇ 𝕜` is
`𝕜`-linearly isometric to `C(α, 𝕜)`.
-/
def linear_isometry_continuous_map_of_compact :
  (α →ᵇ 𝕜) ≃ₗᵢ[𝕜] C(α, 𝕜) :=
{ map_smul' := λ c f, by { ext, simp, },
  norm_map' := λ f, rfl,
  ..add_equiv_continuous_map_of_compact α 𝕜 }

@[simp]
lemma isometric_continuous_map_of_compact_to_isometric :
  (linear_isometry_continuous_map_of_compact α 𝕜).to_isometric =
    isometric_continuous_map_of_compact α 𝕜 :=
rfl

@[simp]
lemma linear_isometry_continuous_map_of_compact_to_add_equiv :
  (linear_isometry_continuous_map_of_compact α 𝕜).to_linear_equiv.to_add_equiv =
    add_equiv_continuous_map_of_compact α 𝕜 :=
rfl

@[simp]
lemma linear_isometry_continuous_map_of_compact_to_equiv :
  (linear_isometry_continuous_map_of_compact α 𝕜).to_linear_equiv.to_equiv =
    equiv_continuous_map_of_compact α 𝕜 :=
rfl

end continuous_map
