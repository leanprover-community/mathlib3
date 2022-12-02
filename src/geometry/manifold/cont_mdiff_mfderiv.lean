/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import geometry.manifold.mfderiv

/-!
### Interactions between differentiability, smoothness and manifold derivatives

We give the relation between `mdifferentiable`, `cont_mdiff`, `mfderiv`, `tangent_map`
and related notions.

## Main statements

* `cont_mdiff_on.cont_mdiff_on_tangent_map_within` states that the bundled derivative
  of a `Cⁿ` function in a domain is `Cᵐ` when `m + 1 ≤ n`.
* `cont_mdiff.cont_mdiff_tangent_map` states that the bundled derivative
  of a `Cⁿ` function is `Cᵐ` when `m + 1 ≤ n`.
-/

open set function filter charted_space smooth_manifold_with_corners
open_locale topological_space manifold

/-! ### Definition of smooth functions between manifolds -/

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
-- declare a smooth manifold `M` over the pair `(E, H)`.
{E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
{M : Type*} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M]
-- declare a smooth manifold `M'` over the pair `(E', H')`.
{E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
{H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
{M' : Type*} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M']
-- declare a smooth manifold `N` over the pair `(F, G)`.
{F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
{G : Type*} [topological_space G] {J : model_with_corners 𝕜 F G}
{N : Type*} [topological_space N] [charted_space G N] [Js : smooth_manifold_with_corners J N]
-- declare a smooth manifold `N'` over the pair `(F', G')`.
{F' : Type*} [normed_add_comm_group F'] [normed_space 𝕜 F']
{G' : Type*} [topological_space G'] {J' : model_with_corners 𝕜 F' G'}
{N' : Type*} [topological_space N'] [charted_space G' N'] [J's : smooth_manifold_with_corners J' N']
-- declare functions, sets, points and smoothness indices
{f f₁ : M → M'} {s s₁ t : set M} {x : M} {m n : ℕ∞}

/-! ### Deducing differentiability from smoothness -/

lemma cont_mdiff_within_at.mdifferentiable_within_at
  (hf : cont_mdiff_within_at I I' n f s x) (hn : 1 ≤ n) :
  mdifferentiable_within_at I I' f s x :=
begin
  suffices h : mdifferentiable_within_at I I' f (s ∩ (f ⁻¹' (ext_chart_at I' (f x)).source)) x,
  { rwa mdifferentiable_within_at_inter' at h,
    apply (hf.1).preimage_mem_nhds_within,
    exact ext_chart_at_source_mem_nhds I' (f x) },
  rw mdifferentiable_within_at_iff,
  exact ⟨hf.1.mono (inter_subset_left _ _),
    (hf.2.differentiable_within_at hn).mono (by mfld_set_tac)⟩,
end

lemma cont_mdiff_at.mdifferentiable_at (hf : cont_mdiff_at I I' n f x) (hn : 1 ≤ n) :
  mdifferentiable_at I I' f x :=
mdifferentiable_within_at_univ.1 $ cont_mdiff_within_at.mdifferentiable_within_at hf hn

lemma cont_mdiff_on.mdifferentiable_on (hf : cont_mdiff_on I I' n f s) (hn : 1 ≤ n) :
  mdifferentiable_on I I' f s :=
λ x hx, (hf x hx).mdifferentiable_within_at hn

lemma cont_mdiff.mdifferentiable (hf : cont_mdiff I I' n f) (hn : 1 ≤ n) :
  mdifferentiable I I' f :=
λ x, (hf x).mdifferentiable_at hn

lemma smooth_within_at.mdifferentiable_within_at
  (hf : smooth_within_at I I' f s x) : mdifferentiable_within_at I I' f s x :=
hf.mdifferentiable_within_at le_top

lemma smooth_at.mdifferentiable_at (hf : smooth_at I I' f x) : mdifferentiable_at I I' f x :=
hf.mdifferentiable_at le_top

lemma smooth_on.mdifferentiable_on (hf : smooth_on I I' f s) : mdifferentiable_on I I' f s :=
hf.mdifferentiable_on le_top

lemma smooth.mdifferentiable (hf : smooth I I' f) : mdifferentiable I I' f :=
cont_mdiff.mdifferentiable hf le_top

lemma smooth.mdifferentiable_at (hf : smooth I I' f) : mdifferentiable_at I I' f x :=
hf.mdifferentiable x

lemma smooth.mdifferentiable_within_at (hf : smooth I I' f) :
  mdifferentiable_within_at I I' f s x :=
hf.mdifferentiable_at.mdifferentiable_within_at

section mfderiv

variables [smooth_manifold_with_corners I M] [smooth_manifold_with_corners I' M']

/-! ### Computations with `mfderiv` -/

/-- For a function `f` from a manifold `M` to a normed space `E'`, the `mfderiv` of `-f` is the
negation of the `mfderiv` of `f` (abusing the identification of the tangent spaces to `E'` at `f x`
and `- f x` with `E'`). -/
lemma mfderiv_neg (f : M → E') (x : M) :
  (mfderiv I 𝓘(𝕜, E') (-f) x : tangent_space I x →L[𝕜] E') =
  (- mfderiv I 𝓘(𝕜, E') f x : tangent_space I x →L[𝕜] E') :=
begin
  classical,
  simp only [mfderiv, dite_eq_ite] with mfld_simps,
  by_cases hf : mdifferentiable_at I 𝓘(𝕜, E') f x,
  { have hf_neg : mdifferentiable_at I 𝓘(𝕜, E') (-f) x :=
      ((cont_diff_neg.cont_mdiff _).mdifferentiable_at (le_refl _)).comp _ hf,
    rw [if_pos hf, if_pos hf_neg],
    apply fderiv_within_neg (I.unique_diff _ (set.mem_range_self _)) },
  { have hf_neg : ¬ mdifferentiable_at I 𝓘(𝕜, E') (-f) x,
    { intros h,
      apply hf,
      convert ((cont_diff_neg.cont_mdiff _).mdifferentiable_at (le_refl _)).comp _ h,
      ext,
      simp only [comp_app, pi.neg_apply, neg_neg] },
    rw [if_neg hf, if_neg hf_neg, neg_zero] },
end

/-- The derivative of the projection `M × M' → M` is the projection `TM × TM' → TM` -/
lemma mfderiv_fst (x : M × M') :
  mfderiv (I.prod I') I prod.fst x = continuous_linear_map.fst 𝕜 E E' :=
begin
  simp_rw [mfderiv, dif_pos smooth_at_fst.mdifferentiable_at, written_in_ext_chart_at,
    ext_chart_at_prod, function.comp, local_equiv.prod_coe, local_equiv.prod_coe_symm],
  have : unique_diff_within_at 𝕜 (range (I.prod I')) (ext_chart_at (I.prod I') x x) :=
  (I.prod I').unique_diff _ (mem_range_self _),
  refine (filter.eventually_eq.fderiv_within_eq this _ _).trans _,
  swap 3,
  { exact (ext_chart_at I x.1).right_inv ((ext_chart_at I x.1).maps_to $
      mem_ext_chart_source I x.1) },
  { refine eventually_of_mem (ext_chart_at_target_mem_nhds_within (I.prod I') x)
      (λ y hy, local_equiv.right_inv _ _),
    rw [ext_chart_at_prod] at hy,
    exact hy.1 },
  exact fderiv_within_fst this,
end

/-- The derivative of the projection `M × M' → M'` is the projection `TM × TM' → TM'` -/
lemma mfderiv_snd (x : M × M') :
  mfderiv (I.prod I') I' prod.snd x = continuous_linear_map.snd 𝕜 E E' :=
begin
  simp_rw [mfderiv, dif_pos smooth_at_snd.mdifferentiable_at, written_in_ext_chart_at,
    ext_chart_at_prod, function.comp, local_equiv.prod_coe, local_equiv.prod_coe_symm],
  have : unique_diff_within_at 𝕜 (range (I.prod I')) (ext_chart_at (I.prod I') x x) :=
  (I.prod I').unique_diff _ (mem_range_self _),
  refine (filter.eventually_eq.fderiv_within_eq this _ _).trans _,
  swap 3,
  { exact (ext_chart_at I' x.2).right_inv ((ext_chart_at I' x.2).maps_to $
      mem_ext_chart_source I' x.2) },
  { refine eventually_of_mem (ext_chart_at_target_mem_nhds_within (I.prod I') x)
      (λ y hy, local_equiv.right_inv _ _),
    rw [ext_chart_at_prod] at hy,
    exact hy.2 },
  exact fderiv_within_snd this,
end

end mfderiv

/-! ### The tangent map of a smooth function is smooth -/

section tangent_map

include Is I's

/-- If a function is `C^n` on a domain with unique derivatives, then its bundled derivative
is `C^m` when `m+1 ≤ n`. -/
theorem cont_mdiff_on.cont_mdiff_on_tangent_map_within
  (hf : cont_mdiff_on I I' n f s) (hmn : m + 1 ≤ n) (hs : unique_mdiff_on I s) :
  cont_mdiff_on I.tangent I'.tangent m (tangent_map_within I I' f s)
  ((tangent_bundle.proj I M) ⁻¹' s) :=
begin
  sorry
end

/-- If a function is `C^n` on a domain with unique derivatives, with `1 ≤ n`, then its bundled
derivative is continuous there. -/
theorem cont_mdiff_on.continuous_on_tangent_map_within
  (hf : cont_mdiff_on I I' n f s) (hmn : 1 ≤ n) (hs : unique_mdiff_on I s) :
  continuous_on (tangent_map_within I I' f s) ((tangent_bundle.proj I M) ⁻¹' s) :=
begin
  have : cont_mdiff_on I.tangent I'.tangent 0 (tangent_map_within I I' f s)
         ((tangent_bundle.proj I M) ⁻¹' s) :=
    hf.cont_mdiff_on_tangent_map_within hmn hs,
  exact this.continuous_on
end

/-- If a function is `C^n`, then its bundled derivative is `C^m` when `m+1 ≤ n`. -/
theorem cont_mdiff.cont_mdiff_tangent_map
  (hf : cont_mdiff I I' n f) (hmn : m + 1 ≤ n) :
  cont_mdiff I.tangent I'.tangent m (tangent_map I I' f) :=
begin
  rw ← cont_mdiff_on_univ at hf ⊢,
  convert hf.cont_mdiff_on_tangent_map_within hmn unique_mdiff_on_univ,
  rw tangent_map_within_univ
end

/-- If a function is `C^n`, with `1 ≤ n`, then its bundled derivative is continuous. -/
theorem cont_mdiff.continuous_tangent_map
  (hf : cont_mdiff I I' n f) (hmn : 1 ≤ n) :
  continuous (tangent_map I I' f) :=
begin
  rw ← cont_mdiff_on_univ at hf,
  rw continuous_iff_continuous_on_univ,
  convert hf.continuous_on_tangent_map_within hmn unique_mdiff_on_univ,
  rw tangent_map_within_univ
end

end tangent_map

/-! ### Smoothness of the projection in a basic smooth bundle -/

namespace bundle

variables
  (Z : M → Type*) [topological_space (total_space Z)] [∀ b, topological_space (Z b)]
  [∀ b, add_comm_monoid (Z b)] [∀ b, module 𝕜 (Z b)]
  [fiber_bundle E' Z] [vector_bundle 𝕜 E' Z] [smooth_vector_bundle E' Z I]

/-- A version of `cont_mdiff_at_iff_target` when the codomain is the total space of
  a `basic_smooth_vector_bundle_core`. The continuity condition in the RHS is weaker. -/
lemma cont_mdiff_at_iff_target {f : N → total_space Z}
  {x : N} {n : ℕ∞} :
  cont_mdiff_at J (I.prod 𝓘(𝕜, E')) n f x ↔ continuous_at (bundle.total_space.proj ∘ f) x ∧
    cont_mdiff_at J 𝓘(𝕜, E × E') n (ext_chart_at (I.prod 𝓘(𝕜, E')) (f x) ∘ f) x :=
begin
  rw [cont_mdiff_at_iff_target, and.congr_left_iff],
  refine λ hf, ⟨λ h, (continuous_proj E' Z).continuous_at.comp h, λ h, _⟩,
  refine (trivialization_at E' Z _).continuous_at_of_comp_left h
    (mem_base_set_trivialization_at E' Z _) _,
  suffices : continuous_at (λ x, ((f x).1, (trivialization_at E' Z (f x).proj (f x)).2)) x,
  { refine this.congr sorry, },
  refine h.prod _, sorry,
end

lemma smooth_iff_target {f : N → total_space Z} :
  smooth J (I.prod 𝓘(𝕜, E')) f ↔ continuous (bundle.total_space.proj ∘ f) ∧
  ∀ x, smooth_at J 𝓘(𝕜, E × E') (ext_chart_at (I.prod 𝓘(𝕜, E')) (f x) ∘ f) x :=
by simp_rw [smooth, smooth_at, cont_mdiff, bundle.cont_mdiff_at_iff_target Z, forall_and_distrib,
  continuous_iff_continuous_at]

lemma cont_mdiff_proj :
  cont_mdiff (I.prod 𝓘(𝕜, E')) I n (@total_space.proj M Z) :=
begin
  assume x,
  rw [cont_mdiff_at, cont_mdiff_within_at_iff'],
  refine ⟨(continuous_proj E' Z).continuous_within_at, _⟩,
  simp only [(∘), fiber_bundle.charted_space_chart_at] with mfld_simps,
  apply cont_diff_within_at_fst.congr,
  { rintros ⟨a, b⟩ hab,
    simp only with mfld_simps at hab,
    simp only [hab] with mfld_simps },
  { simp only with mfld_simps }
end

lemma smooth_proj : smooth (I.prod 𝓘(𝕜, E')) I (@total_space.proj M Z) :=
cont_mdiff_proj Z

lemma cont_mdiff_on_proj {s : set (total_space Z)} :
  cont_mdiff_on (I.prod 𝓘(𝕜, E')) I n (@total_space.proj M Z) s :=
(bundle.cont_mdiff_proj Z).cont_mdiff_on

lemma smooth_on_proj {s : set (total_space Z)} :
  smooth_on (I.prod 𝓘(𝕜, E')) I (@total_space.proj M Z) s :=
cont_mdiff_on_proj Z

lemma cont_mdiff_at_proj {p : total_space Z} :
  cont_mdiff_at (I.prod 𝓘(𝕜, E')) I n
    (@total_space.proj M Z) p :=
(bundle.cont_mdiff_proj Z).cont_mdiff_at

lemma smooth_at_proj {p : total_space Z} :
  smooth_at (I.prod 𝓘(𝕜, E')) I (@total_space.proj M Z) p :=
bundle.cont_mdiff_at_proj Z

lemma cont_mdiff_within_at_proj
  {s : set (total_space Z)}
  {p : total_space Z} :
  cont_mdiff_within_at (I.prod 𝓘(𝕜, E')) I n
    (@total_space.proj M Z) s p :=
(bundle.cont_mdiff_at_proj Z).cont_mdiff_within_at

lemma smooth_within_at_proj
  {s : set (total_space Z)}
  {p : total_space Z} :
  smooth_within_at (I.prod 𝓘(𝕜, E')) I
    (@total_space.proj M Z) s p :=
bundle.cont_mdiff_within_at_proj Z

/-- If an element of `E'` is invariant under all coordinate changes, then one can define a
corresponding section of the fiber bundle, which is smooth. This applies in particular to the
zero section of a vector bundle. Another example (not yet defined) would be the identity
section of the endomorphism bundle of a vector bundle. -/
lemma smooth_const_section (v : E')
  (h : ∀ (i j : atlas H M), ∀ x ∈ i.1.source ∩ j.1.source, Z.coord_change i j (i.1 x) v = v) :
  smooth I (I.prod 𝓘(𝕜, E'))
    (show M → total_space Z, from λ x, ⟨x, v⟩) :=
begin
  assume x,
  rw [cont_mdiff_at, cont_mdiff_within_at_iff'],
  split,
  { apply continuous.continuous_within_at,
    apply fiber_bundle_core.continuous_const_section,
    assume i j y hy,
    exact h _ _ _ hy },
  { have : cont_diff 𝕜 ⊤ (λ (y : E), (y, v)) := cont_diff_id.prod cont_diff_const,
    apply this.cont_diff_within_at.congr,
    { assume y hy,
      simp only with mfld_simps at hy,
      simp only [chart, hy, chart_at, prod.mk.inj_iff, to_vector_bundle_core]
        with mfld_simps,
      apply h,
      simp only [hy, subtype.val_eq_coe] with mfld_simps },
    { simp only [chart, chart_at, prod.mk.inj_iff, to_vector_bundle_core]
        with mfld_simps,
      apply h,
      simp only [subtype.val_eq_coe] with mfld_simps } }
end

end bundle

/-! ### Smoothness of the tangent bundle projection -/

namespace tangent_bundle

include Is

lemma cont_mdiff_proj :
  cont_mdiff I.tangent I n (proj I M) :=
bundle.cont_mdiff_proj _

lemma smooth_proj : smooth I.tangent I (proj I M) :=
bundle.smooth_proj _

lemma cont_mdiff_on_proj {s : set (tangent_bundle I M)} :
  cont_mdiff_on I.tangent I n (proj I M) s :=
bundle.cont_mdiff_on_proj _

lemma smooth_on_proj {s : set (tangent_bundle I M)} :
  smooth_on I.tangent I (proj I M) s :=
bundle.smooth_on_proj _

lemma cont_mdiff_at_proj {p : tangent_bundle I M} :
  cont_mdiff_at I.tangent I n
    (proj I M) p :=
bundle.cont_mdiff_at_proj _

lemma smooth_at_proj {p : tangent_bundle I M} :
  smooth_at I.tangent I (proj I M) p :=
bundle.smooth_at_proj _

lemma cont_mdiff_within_at_proj
  {s : set (tangent_bundle I M)} {p : tangent_bundle I M} :
  cont_mdiff_within_at I.tangent I n
    (proj I M) s p :=
bundle.cont_mdiff_within_at_proj _

lemma smooth_within_at_proj
  {s : set (tangent_bundle I M)} {p : tangent_bundle I M} :
  smooth_within_at I.tangent I
    (proj I M) s p :=
bundle.smooth_within_at_proj _

variables (I M)
/-- The zero section of the tangent bundle -/
def zero_section : M → tangent_bundle I M := λ x, ⟨x, 0⟩
variables {I M}

lemma smooth_zero_section : smooth I I.tangent (zero_section I M) :=
begin
  apply bundle.smooth_const_section (tangent_bundle_core I M) 0,
  assume i j x hx,
  simp only [tangent_bundle_core, continuous_linear_map.map_zero, continuous_linear_map.coe_coe]
    with mfld_simps,
end

open bundle

/-- The derivative of the zero section of the tangent bundle maps `⟨x, v⟩` to `⟨⟨x, 0⟩, ⟨v, 0⟩⟩`.

Note that, as currently framed, this is a statement in coordinates, thus reliant on the choice
of the coordinate system we use on the tangent bundle.

However, the result itself is coordinate-dependent only to the extent that the coordinates
determine a splitting of the tangent bundle.  Moreover, there is a canonical splitting at each
point of the zero section (since there is a canonical horizontal space there, the tangent space
to the zero section, in addition to the canonical vertical space which is the kernel of the
derivative of the projection), and this canonical splitting is also the one that comes from the
coordinates on the tangent bundle in our definitions. So this statement is not as crazy as it
may seem.

TODO define splittings of vector bundles; state this result invariantly. -/
lemma tangent_map_tangent_bundle_pure (p : tangent_bundle I M) :
  tangent_map I I.tangent (tangent_bundle.zero_section I M) p = ⟨⟨p.1, 0⟩, ⟨p.2, 0⟩⟩ :=
begin
  rcases p with ⟨x, v⟩,
  have N : I.symm ⁻¹' (chart_at H x).target ∈ 𝓝 (I ((chart_at H x) x)),
  { apply is_open.mem_nhds,
    apply (local_homeomorph.open_target _).preimage I.continuous_inv_fun,
    simp only with mfld_simps },
  have A : mdifferentiable_at I I.tangent (λ x, @total_space_mk M (tangent_space I) x 0) x :=
    tangent_bundle.smooth_zero_section.mdifferentiable_at,
  have B : fderiv_within 𝕜 (λ (x_1 : E), (x_1, (0 : E))) (set.range ⇑I) (I ((chart_at H x) x)) v
    = (v, 0),
  { rw [fderiv_within_eq_fderiv, differentiable_at.fderiv_prod],
    { simp },
    { exact differentiable_at_id' },
    { exact differentiable_at_const _ },
    { exact model_with_corners.unique_diff_at_image I },
    { exact differentiable_at_id'.prod (differentiable_at_const _) } },
  simp only [tangent_bundle.zero_section, tangent_map, mfderiv,
    A, dif_pos, chart_at, fiber_bundle.charted_space_chart_at,
    tangent_bundle_core, function.comp, continuous_linear_map.map_zero] with mfld_simps,
  rw ← fderiv_within_inter N (I.unique_diff (I ((chart_at H x) x)) (set.mem_range_self _)) at B,
  rw [← fderiv_within_inter N (I.unique_diff (I ((chart_at H x) x)) (set.mem_range_self _)), ← B],
  congr' 2,
  apply fderiv_within_congr _ (λ y hy, _),
  { simp only [prod.mk.inj_iff] with mfld_simps },
  { apply unique_diff_within_at.inter (I.unique_diff _ _) N,
    simp only with mfld_simps },
  { simp only with mfld_simps at hy,
    simp only [hy, prod.mk.inj_iff] with mfld_simps },
end

end tangent_bundle
