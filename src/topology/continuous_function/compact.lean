/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import topology.continuous_function.bounded
import topology.uniform_space.compact_separated
import tactic.equiv_rw

/-!
# Continuous functions on a compact space

Continuous functions `C(α, β)` from a compact space `α` to a metric space `β`
are automatically bounded, and so acquire various structures inherited from `α →ᵇ β`.

This file transfers these structures, and restates some lemmas
characterising these structures.

If you need a lemma which is proved about `α →ᵇ β` but not for `C(α, β)` when `α` is compact,
you should restate it here. You can also use
`bounded_continuous_function.equiv_continuous_map_of_compact` to move functions back and forth.

-/

noncomputable theory
open_locale topological_space classical nnreal bounded_continuous_function

open set filter metric

open bounded_continuous_function

namespace continuous_map

variables {α β E : Type*} [topological_space α] [compact_space α] [metric_space β] [normed_group E]

section

variables (α β)

/--
When `α` is compact, the bounded continuous maps `α →ᵇ β` are
equivalent to `C(α, β)`.
-/
@[simps { fully_applied := ff }]
def equiv_bounded_of_compact : C(α, β) ≃ (α →ᵇ β) :=
⟨mk_of_compact, forget_boundedness α β, λ f, by { ext, refl, }, λ f, by { ext, refl, }⟩

/--
When `α` is compact, the bounded continuous maps `α →ᵇ 𝕜` are
additively equivalent to `C(α, 𝕜)`.
-/
@[simps apply symm_apply { fully_applied := ff }]
def add_equiv_bounded_of_compact [add_monoid β] [has_lipschitz_add β] :
  C(α, β) ≃+ (α →ᵇ β) :=
({ .. forget_boundedness_add_hom α β,
   .. (equiv_bounded_of_compact α β).symm, } : (α →ᵇ β) ≃+ C(α, β)).symm

instance : metric_space C(α, β) :=
metric_space.induced
  (equiv_bounded_of_compact α β)
  (equiv_bounded_of_compact α β).injective
  (by apply_instance)

/--
When `α` is compact, and `β` is a metric space, the bounded continuous maps `α →ᵇ β` are
isometric to `C(α, β)`.
-/
@[simps to_equiv apply symm_apply { fully_applied := ff }]
def isometric_bounded_of_compact :
  C(α, β) ≃ᵢ (α →ᵇ β) :=
{ isometry_to_fun := λ x y, rfl,
  to_equiv := equiv_bounded_of_compact α β }

end

@[simp] lemma _root_.bounded_continuous_function.dist_mk_of_compact (f g : C(α, β)) :
  dist (mk_of_compact f) (mk_of_compact g) = dist f g := rfl

@[simp] lemma _root_.bounded_continuous_function.dist_forget_boundedness (f g : α →ᵇ β) :
  dist (f.forget_boundedness _ _) (g.forget_boundedness _ _) = dist f g := rfl

open bounded_continuous_function

section
variables {α β} {f g : C(α, β)} {C : ℝ}

/-- The pointwise distance is controlled by the distance between functions, by definition. -/
lemma dist_apply_le_dist (x : α) : dist (f x) (g x) ≤ dist f g :=
by simp only [← dist_mk_of_compact, dist_coe_le_dist, ← mk_of_compact_apply]

/-- The distance between two functions is controlled by the supremum of the pointwise distances -/
lemma dist_le (C0 : (0 : ℝ) ≤ C) : dist f g ≤ C ↔ ∀x:α, dist (f x) (g x) ≤ C :=
by simp only [← dist_mk_of_compact, dist_le C0, mk_of_compact_apply]

lemma dist_le_iff_of_nonempty [nonempty α] :
  dist f g ≤ C ↔ ∀ x, dist (f x) (g x) ≤ C :=
by simp only [← dist_mk_of_compact, dist_le_iff_of_nonempty, mk_of_compact_apply]

lemma dist_lt_iff_of_nonempty [nonempty α] :
  dist f g < C ↔ ∀x:α, dist (f x) (g x) < C :=
by simp only [← dist_mk_of_compact, dist_lt_iff_of_nonempty_compact, mk_of_compact_apply]

lemma dist_lt_of_nonempty [nonempty α] (w : ∀x:α, dist (f x) (g x) < C) : dist f g < C :=
(dist_lt_iff_of_nonempty).2 w

lemma dist_lt_iff (C0 : (0 : ℝ) < C) :
  dist f g < C ↔ ∀x:α, dist (f x) (g x) < C :=
by simp only [← dist_mk_of_compact, dist_lt_iff_of_compact C0, mk_of_compact_apply]

end

instance [complete_space β] : complete_space (C(α, β)) :=
(isometric_bounded_of_compact α β).complete_space

@[continuity] lemma continuous_eval : continuous (λ p : C(α, β) × α, p.1 p.2) :=
continuous_eval.comp ((isometric_bounded_of_compact α β).continuous.prod_map continuous_id)

@[continuity] lemma continuous_evalx (x : α) : continuous (λ f : C(α, β), f x) :=
continuous_eval.comp (continuous_id.prod_mk continuous_const)

lemma continuous_coe : @continuous (C(α, β)) (α → β) _ _ coe_fn :=
continuous_pi continuous_evalx

-- TODO at some point we will need lemmas characterising this norm!
-- At the moment the only way to reason about it is to transfer `f : C(α,E)` back to `α →ᵇ E`.
instance : has_norm C(α, E) :=
{ norm := λ x, dist x 0 }

@[simp] lemma _root_.bounded_continuous_function.norm_mk_of_compact (f : C(α, E)) :
  ∥mk_of_compact f∥ = ∥f∥ := rfl

@[simp] lemma _root_.bounded_continuous_function.norm_forget_boundedness_eq (f : α →ᵇ E) :
  ∥forget_boundedness α E f∥ = ∥f∥ :=
rfl

open bounded_continuous_function

instance : normed_group C(α, E) :=
{ dist_eq := λ x y,
  begin
    rw [← norm_mk_of_compact, ← dist_mk_of_compact, dist_eq_norm],
    congr' 1,
    exact ((add_equiv_bounded_of_compact α E).map_sub _ _).symm
  end, }

section
variables (f : C(α, E))
-- The corresponding lemmas for `bounded_continuous_function` are stated with `{f}`,
-- and so can not be used in dot notation.

lemma norm_coe_le_norm (x : α) : ∥f x∥ ≤ ∥f∥ :=
(mk_of_compact f).norm_coe_le_norm x

/-- Distance between the images of any two points is at most twice the norm of the function. -/
lemma dist_le_two_norm (x y : α) : dist (f x) (f y) ≤ 2 * ∥f∥ :=
(mk_of_compact f).dist_le_two_norm x y

/-- The norm of a function is controlled by the supremum of the pointwise norms -/
lemma norm_le {C : ℝ} (C0 : (0 : ℝ) ≤ C) : ∥f∥ ≤ C ↔ ∀x:α, ∥f x∥ ≤ C :=
@bounded_continuous_function.norm_le _ _ _ _
  (mk_of_compact f) _ C0

lemma norm_le_of_nonempty [nonempty α] {M : ℝ} : ∥f∥ ≤ M ↔ ∀ x, ∥f x∥ ≤ M :=
@bounded_continuous_function.norm_le_of_nonempty _ _ _ _ _ (mk_of_compact f) _

lemma norm_lt_iff {M : ℝ} (M0 : 0 < M) : ∥f∥ < M ↔ ∀ x, ∥f x∥ < M :=
@bounded_continuous_function.norm_lt_iff_of_compact _ _ _ _ _ (mk_of_compact f) _ M0

lemma norm_lt_iff_of_nonempty [nonempty α] {M : ℝ} :
  ∥f∥ < M ↔ ∀ x, ∥f x∥ < M :=
@bounded_continuous_function.norm_lt_iff_of_nonempty_compact _ _ _ _ _ _ (mk_of_compact f) _

lemma apply_le_norm (f : C(α, ℝ)) (x : α) : f x ≤ ∥f∥ :=
le_trans (le_abs.mpr (or.inl (le_refl (f x)))) (f.norm_coe_le_norm x)

lemma neg_norm_le_apply (f : C(α, ℝ)) (x : α) : -∥f∥ ≤ f x :=
le_trans (neg_le_neg (f.norm_coe_le_norm x)) (neg_le.mp (neg_le_abs_self (f x)))

lemma norm_eq_supr_norm : ∥f∥ = ⨆ x : α, ∥f x∥ :=
(mk_of_compact f).norm_eq_supr_norm

end

section
variables {R : Type*} [normed_ring R]

instance : normed_ring C(α,R) :=
{ norm_mul := λ f g, norm_mul_le (mk_of_compact f) (mk_of_compact g),
  ..(infer_instance : normed_group C(α,R)) }

end

section
variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 E]

instance : normed_space 𝕜 C(α,E) :=
{ norm_smul_le := λ c f, le_of_eq (norm_smul c (mk_of_compact f)) }

section
variables (α 𝕜 E)

/--
When `α` is compact and `𝕜` is a normed field,
the `𝕜`-algebra of bounded continuous maps `α →ᵇ β` is
`𝕜`-linearly isometric to `C(α, β)`.
-/
def linear_isometry_bounded_of_compact :
  C(α, E) ≃ₗᵢ[𝕜] (α →ᵇ E) :=
{ map_smul' := λ c f, by { ext, simp, },
  norm_map' := λ f, rfl,
  .. add_equiv_bounded_of_compact α E }

end

-- this lemma and the next are the analogues of those autogenerated by `@[simps]` for
-- `equiv_bounded_of_compact`, `add_equiv_bounded_of_compact`
@[simp] lemma linear_isometry_bounded_of_compact_symm_apply (f : α →ᵇ E) :
  (linear_isometry_bounded_of_compact α E 𝕜).symm f = f.forget_boundedness α E :=
rfl

@[simp] lemma linear_isometry_bounded_of_compact_apply_apply (f : C(α, E)) (a : α) :
  (linear_isometry_bounded_of_compact α E 𝕜 f) a = f a :=
rfl


@[simp]
lemma linear_isometry_bounded_of_compact_to_isometric :
  (linear_isometry_bounded_of_compact α E 𝕜).to_isometric = (isometric_bounded_of_compact α E) :=
rfl

@[simp]
lemma linear_isometry_bounded_of_compact_to_add_equiv :
  (linear_isometry_bounded_of_compact α E 𝕜).to_linear_equiv.to_add_equiv =
    (add_equiv_bounded_of_compact α E) :=
rfl

@[simp]
lemma linear_isometry_bounded_of_compact_of_compact_to_equiv :
  (linear_isometry_bounded_of_compact α E 𝕜).to_linear_equiv.to_equiv =
    (equiv_bounded_of_compact α E) :=
rfl

end

section
variables {𝕜 : Type*} {γ : Type*} [normed_field 𝕜] [normed_ring γ] [normed_algebra 𝕜 γ]

instance [nonempty α] : normed_algebra 𝕜 C(α, γ) :=
{ norm_algebra_map_eq := λ c, (norm_algebra_map_eq (α →ᵇ γ) c : _), }

end

end continuous_map

namespace continuous_map

section uniform_continuity
variables {α β : Type*}
variables [metric_space α] [compact_space α] [metric_space β]

/-!
We now set up some declarations making it convenient to use uniform continuity.
-/

lemma uniform_continuity
  (f : C(α, β)) (ε : ℝ) (h : 0 < ε) :
  ∃ δ > 0, ∀ {x y}, dist x y < δ → dist (f x) (f y) < ε :=
metric.uniform_continuous_iff.mp
  (compact_space.uniform_continuous_of_continuous f.continuous) ε h

/--
An arbitrarily chosen modulus of uniform continuity for a given function `f` and `ε > 0`.
-/
-- This definition allows us to separate the choice of some `δ`,
-- and the corresponding use of `dist a b < δ → dist (f a) (f b) < ε`,
-- even across different declarations.
def modulus (f : C(α, β)) (ε : ℝ) (h : 0 < ε) : ℝ :=
classical.some (uniform_continuity f ε h)

lemma modulus_pos (f : C(α, β)) {ε : ℝ} {h : 0 < ε} : 0 < f.modulus ε h :=
(classical.some_spec (uniform_continuity f ε h)).fst

lemma dist_lt_of_dist_lt_modulus
  (f : C(α, β)) (ε : ℝ) (h : 0 < ε) {a b : α} (w : dist a b < f.modulus ε h) :
  dist (f a) (f b) < ε :=
(classical.some_spec (uniform_continuity f ε h)).snd w

end uniform_continuity

end continuous_map

section comp_left
variables (X : Type*) {𝕜 β γ : Type*} [topological_space X] [compact_space X]
  [nondiscrete_normed_field 𝕜]
variables [normed_group β] [normed_space 𝕜 β] [normed_group γ] [normed_space 𝕜 γ]

open continuous_map

/--
Postcomposition of continuous functions into a normed module by a continuous linear map is a
continuous linear map.
Transferred version of `continuous_linear_map.comp_left_continuous_bounded`,
upgraded version of `continuous_linear_map.comp_left_continuous`,
similar to `linear_map.comp_left`. -/
protected def continuous_linear_map.comp_left_continuous_compact (g : β →L[𝕜] γ) :
  C(X, β) →L[𝕜] C(X, γ) :=
(linear_isometry_bounded_of_compact X γ 𝕜).symm.to_linear_isometry.to_continuous_linear_map.comp $
(g.comp_left_continuous_bounded X).comp $
(linear_isometry_bounded_of_compact X β 𝕜).to_linear_isometry.to_continuous_linear_map

@[simp] lemma continuous_linear_map.to_linear_comp_left_continuous_compact (g : β →L[𝕜] γ) :
  (g.comp_left_continuous_compact X : C(X, β) →ₗ[𝕜] C(X, γ)) = g.comp_left_continuous 𝕜 X :=
by { ext f, refl }

@[simp] lemma continuous_linear_map.comp_left_continuous_compact_apply (g : β →L[𝕜] γ)
  (f : C(X, β)) (x : X) :
  g.comp_left_continuous_compact X f x = g (f x) :=
rfl

end comp_left

namespace continuous_map
/-!
We now setup variations on `comp_right_* f`, where `f : C(X, Y)`
(that is, precomposition by a continuous map),
as a morphism `C(Y, T) → C(X, T)`, respecting various types of structure.

In particular:
* `comp_right_continuous_map`, the bundled continuous map (for this we need `X Y` compact).
* `comp_right_homeomorph`, when we precompose by a homeomorphism.
* `comp_right_alg_hom`, when `T = R` is a topological ring.
-/
section comp_right

/--
Precomposition by a continuous map is itself a continuous map between spaces of continuous maps.
-/
def comp_right_continuous_map {X Y : Type*} (T : Type*)
  [topological_space X] [compact_space X] [topological_space Y] [compact_space Y] [normed_group T]
  (f : C(X, Y)) : C(C(Y, T), C(X, T)) :=
{ to_fun := λ g, g.comp f,
  continuous_to_fun :=
  begin
    refine metric.continuous_iff.mpr _,
    intros g ε ε_pos,
    refine ⟨ε, ε_pos, λ g' h, _⟩,
    rw continuous_map.dist_lt_iff ε_pos at h ⊢,
    { exact λ x, h (f x), },
  end }

@[simp] lemma comp_right_continuous_map_apply {X Y : Type*} (T : Type*)
  [topological_space X] [compact_space X] [topological_space Y] [compact_space Y] [normed_group T]
  (f : C(X, Y)) (g : C(Y, T)) :
  (comp_right_continuous_map T f) g = g.comp f :=
rfl

/--
Precomposition by a homeomorphism is itself a homeomorphism between spaces of continuous maps.
-/
def comp_right_homeomorph {X Y : Type*} (T : Type*)
  [topological_space X] [compact_space X] [topological_space Y] [compact_space Y] [normed_group T]
  (f : X ≃ₜ Y) : C(Y, T) ≃ₜ C(X, T) :=
{ to_fun := comp_right_continuous_map T f.to_continuous_map,
  inv_fun := comp_right_continuous_map T f.symm.to_continuous_map,
  left_inv := by tidy,
  right_inv := by tidy, }

/--
Precomposition of functions into a normed ring by continuous map is an algebra homomorphism.
-/
def comp_right_alg_hom {X Y : Type*} (R : Type*)
  [topological_space X] [topological_space Y] [normed_comm_ring R] (f : C(X, Y)) :
  C(Y, R) →ₐ[R] C(X, R) :=
{ to_fun := λ g, g.comp f,
  map_zero' := by { ext, simp, },
  map_add' := λ g₁ g₂, by { ext, simp, },
  map_one' := by { ext, simp, },
  map_mul' := λ g₁ g₂, by { ext, simp, },
  commutes' := λ r, by { ext, simp, }, }

@[simp] lemma comp_right_alg_hom_apply {X Y : Type*} (R : Type*)
  [topological_space X] [topological_space Y] [normed_comm_ring R] (f : C(X, Y)) (g : C(Y, R)) :
  (comp_right_alg_hom R f) g = g.comp f :=
rfl

lemma comp_right_alg_hom_continuous {X Y : Type*} (R : Type*)
  [topological_space X] [compact_space X] [topological_space Y] [compact_space Y]
  [normed_comm_ring R] (f : C(X, Y)) :
  continuous (comp_right_alg_hom R f) :=
begin
  change continuous (comp_right_continuous_map R f),
  continuity,
end

end comp_right

end continuous_map
