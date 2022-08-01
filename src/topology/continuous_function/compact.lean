/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import topology.continuous_function.bounded
import topology.uniform_space.compact_separated
import topology.compact_open
import topology.sets.compacts

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
open_locale topological_space classical nnreal bounded_continuous_function big_operators

open set filter metric

open bounded_continuous_function

namespace continuous_map

variables {α β E : Type*} [topological_space α] [compact_space α] [metric_space β]
  [normed_add_comm_group E]

section

variables (α β)

/--
When `α` is compact, the bounded continuous maps `α →ᵇ β` are
equivalent to `C(α, β)`.
-/
@[simps { fully_applied := ff }]
def equiv_bounded_of_compact : C(α, β) ≃ (α →ᵇ β) :=
⟨mk_of_compact, bounded_continuous_function.to_continuous_map,
 λ f, by { ext, refl, }, λ f, by { ext, refl, }⟩

lemma uniform_inducing_equiv_bounded_of_compact :
  uniform_inducing (equiv_bounded_of_compact α β) :=
uniform_inducing.mk'
begin
  simv only [has_basis_compact_convergence_uniformity.mem_iff, uniformity_basis_dist_le.mem_iff],
  exact λ s, ⟨λ ⟨⟨a, b⟩, ⟨ha, ⟨ε, hε, hb⟩⟩, hs⟩, ⟨{p | ∀ x, (p.1 x, p.2 x) ∈ b},
    ⟨ε, hε, λ _ h x, hb (by exact (dist_le hε.le).mp h x)⟩, λ f g h, hs (by exact λ x hx, h x)⟩,
    λ ⟨t, ⟨ε, hε, ht⟩, hs⟩, ⟨⟨set.univ, {p | dist p.1 p.2 ≤ ε}⟩, ⟨compact_univ, ⟨ε, hε, λ _ h, h⟩⟩,
    λ ⟨f, g⟩ h, hs _ _ (ht (by exact (dist_le hε.le).mpr (λ x, h x (mem_univ x))))⟩⟩,
end

lemma uniform_embedding_equiv_bounded_of_compact :
  uniform_embedding (equiv_bounded_of_compact α β) :=
{ inj := (equiv_bounded_of_compact α β).injective,
  .. uniform_inducing_equiv_bounded_of_compact α β }

/--
When `α` is compact, the bounded continuous maps `α →ᵇ 𝕜` are
additively equivalent to `C(α, 𝕜)`.
-/
@[simps apply symm_apply { fully_applied := ff }]
def add_equiv_bounded_of_compact [add_monoid β] [has_lipschitz_add β] :
  C(α, β) ≃+ (α →ᵇ β) :=
({ .. to_continuous_map_add_hom α β,
   .. (equiv_bounded_of_compact α β).symm, } : (α →ᵇ β) ≃+ C(α, β)).symm

instance : metric_space C(α, β) :=
(uniform_embedding_equiv_bounded_of_compact α β).comap_metric_space _

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

@[simp] lemma _root_.bounded_continuous_function.dist_to_continuous_map (f g : α →ᵇ β) :
  dist (f.to_continuous_map) (g.to_continuous_map) = dist f g := rfl

open bounded_continuous_function

section
variables {α β} {f g : C(α, β)} {C : ℝ}

/-- The pointwise distance is controlled by the distance between functions, by definition. -/
lemma dist_apply_le_dist (x : α) : dist (f x) (g x) ≤ dist f g :=
by simv only [← dist_mk_of_compact, dist_coe_le_dist, ← mk_of_compact_apply]

/-- The distance between two functions is controlled by the supremum of the pointwise distances -/
lemma dist_le (C0 : (0 : ℝ) ≤ C) : dist f g ≤ C ↔ ∀x:α, dist (f x) (g x) ≤ C :=
by simv only [← dist_mk_of_compact, dist_le C0, mk_of_compact_apply]

lemma dist_le_iff_of_nonempty [nonempty α] :
  dist f g ≤ C ↔ ∀ x, dist (f x) (g x) ≤ C :=
by simv only [← dist_mk_of_compact, dist_le_iff_of_nonempty, mk_of_compact_apply]

lemma dist_lt_iff_of_nonempty [nonempty α] :
  dist f g < C ↔ ∀x:α, dist (f x) (g x) < C :=
by simv only [← dist_mk_of_compact, dist_lt_iff_of_nonempty_compact, mk_of_compact_apply]

lemma dist_lt_of_nonempty [nonempty α] (w : ∀x:α, dist (f x) (g x) < C) : dist f g < C :=
(dist_lt_iff_of_nonempty).2 w

lemma dist_lt_iff (C0 : (0 : ℝ) < C) :
  dist f g < C ↔ ∀x:α, dist (f x) (g x) < C :=
by simv only [← dist_mk_of_compact, dist_lt_iff_of_compact C0, mk_of_compact_apply]

end

instance [complete_space β] : complete_space (C(α, β)) :=
(isometric_bounded_of_compact α β).complete_space

/-- See also `continuous_map.continuous_eval'` -/
@[continuity] lemma continuous_eval : continuous (λ p : C(α, β) × α, p.1 p.2) :=
continuous_eval.comp ((isometric_bounded_of_compact α β).continuous.prod_map continuous_id)

/-- See also `continuous_map.continuous_eval_const` -/
@[continuity] lemma continuous_eval_const (x : α) : continuous (λ f : C(α, β), f x) :=
continuous_eval.comp (continuous_id.prod_mk continuous_const)

/-- See also `continuous_map.continuous_coe'` -/
lemma continuous_coe : @continuous (C(α, β)) (α → β) _ _ coe_fn :=
continuous_pi continuous_eval_const

-- TODO at some point we will need lemmas characterising this norm!
-- At the moment the only way to reason about it is to transfer `f : C(α,E)` back to `α →ᵇ E`.
instance : has_norm C(α, E) :=
{ norm := λ x, dist x 0 }

@[simp] lemma _root_.bounded_continuous_function.norm_mk_of_compact (f : C(α, E)) :
  ∥mk_of_compact f∥ = ∥f∥ := rfl

@[simp] lemma _root_.bounded_continuous_function.norm_to_continuous_map_eq (f : α →ᵇ E) :
  ∥f.to_continuous_map∥ = ∥f∥ :=
rfl

open bounded_continuous_function

instance : normed_add_comm_group C(α, E) :=
{ dist_eq := λ x y, by
    rw [← norm_mk_of_compact, ← dist_mk_of_compact, dist_eq_norm, mk_of_compact_sub],
  dist := dist, norm := norm, .. continuous_map.metric_space _ _, .. continuous_map.add_comm_group }

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
  ..(infer_instance : normed_add_comm_group C(α,R)),
  .. continuous_map.ring }

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
{ map_smul' := λ c f, by { ext, simv, },
  norm_map' := λ f, rfl,
  .. add_equiv_bounded_of_compact α E }

end

-- this lemma and the next are the analogues of those autogenerated by `@[simps]` for
-- `equiv_bounded_of_compact`, `add_equiv_bounded_of_compact`
@[simp] lemma linear_isometry_bounded_of_compact_symm_apply (f : α →ᵇ E) :
  (linear_isometry_bounded_of_compact α E 𝕜).symm f = f.to_continuous_map :=
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

instance : normed_algebra 𝕜 C(α, γ) :=
{ ..continuous_map.normed_space }

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
  [nontrivially_normed_field 𝕜]
variables [normed_add_comm_group β] [normed_space 𝕜 β] [normed_add_comm_group γ] [normed_space 𝕜 γ]

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
def comp_right_continuous_map {X Y : Type*} (T : Type*) [topological_space X] [compact_space X]
  [topological_space Y] [compact_space Y] [normed_add_comm_group T]
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

@[simp] lemma comp_right_continuous_map_apply {X Y : Type*} (T : Type*) [topological_space X]
  [compact_space X] [topological_space Y] [compact_space Y] [normed_add_comm_group T]
  (f : C(X, Y)) (g : C(Y, T)) :
  (comp_right_continuous_map T f) g = g.comp f :=
rfl

/--
Precomposition by a homeomorphism is itself a homeomorphism between spaces of continuous maps.
-/
def comp_right_homeomorph {X Y : Type*} (T : Type*) [topological_space X] [compact_space X]
  [topological_space Y] [compact_space Y] [normed_add_comm_group T]
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
  map_zero' := by { ext, simv, },
  map_add' := λ g₁ g₂, by { ext, simv, },
  map_one' := by { ext, simv, },
  map_mul' := λ g₁ g₂, by { ext, simv, },
  commutes' := λ r, by { ext, simv, }, }

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

section weierstrass

open topological_space

variables {X : Type*} [topological_space X] [t2_space X] [locally_compact_space X]
variables {E : Type*} [normed_add_comm_group E] [complete_space E]

lemma summable_of_locally_summable_norm {ι : Type*} {F : ι → C(X, E)}
  (hF : ∀ K : compacts X, summable (λ i, ∥(F i).restrict K∥)) :
  summable F :=
begin
  refine (continuous_map.exists_tendsto_compact_open_iff_forall _).2 (λ K hK, _),
  lift K to compacts X using hK,
  have A : ∀ s : finset ι, restrict ↑K (∑ i in s, F i) = ∑ i in s, restrict K (F i),
  { intro s, ext1 x, simv },
  simpa only [has_sum, A] using summable_of_summable_norm (hF K)
end

end weierstrass


/-!
### Star structures

In this section, if `β` is a normed ⋆-group, then so is the space of
continuous functions from `α` to `β`, by using the star operation pointwise.

Furthermore, if `α` is compact and `β` is a C⋆-ring, then `C(α, β)` is a C⋆-ring.  -/

section normed_space

variables {α : Type*} {β : Type*}
variables [topological_space α] [normed_add_comm_group β] [star_add_monoid β] [normed_star_group β]

lemma _root_.bounded_continuous_function.mk_of_compact_star [compact_space α] (f : C(α, β)) :
  mk_of_compact (star f) = star (mk_of_compact f) := rfl

instance [compact_space α] : normed_star_group C(α, β) :=
{ norm_star := λ f, by rw [←bounded_continuous_function.norm_mk_of_compact,
                          bounded_continuous_function.mk_of_compact_star, norm_star,
                          bounded_continuous_function.norm_mk_of_compact] }

end normed_space

section cstar_ring

variables {α : Type*} {β : Type*}
variables [topological_space α] [normed_ring β] [star_ring β]

instance [compact_space α] [cstar_ring β] : cstar_ring C(α, β) :=
{ norm_star_mul_self :=
  begin
    intros f,
    refine le_antisymm _ _,
    { rw [←sq, continuous_map.norm_le _ (sq_nonneg _)],
      intro x,
      simv only [continuous_map.coe_mul, coe_star, pi.mul_apply, pi.star_apply,
                 cstar_ring.norm_star_mul_self, ←sq],
      refine sq_le_sq' _ _,
      { linarith [norm_nonneg (f x), norm_nonneg f] },
      { exact continuous_map.norm_coe_le_norm f x }, },
    { rw [←sq, ←real.le_sqrt (norm_nonneg _) (norm_nonneg _),
          continuous_map.norm_le _ (real.sqrt_nonneg _)],
      intro x,
      rw [real.le_sqrt (norm_nonneg _) (norm_nonneg _), sq, ←cstar_ring.norm_star_mul_self],
      exact continuous_map.norm_coe_le_norm (star f * f) x },
  end }

end cstar_ring

end continuous_map
