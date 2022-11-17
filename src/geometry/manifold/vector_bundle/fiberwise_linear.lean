/-
Copyright (c) 2022 Floris van Doorn, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
import geometry.manifold.cont_mdiff

/-! # The groupoid of smooth, fibrewise-linear maps

This file contains preliminaries for the definition of a smooth vector bundle: an associated
`structure_groupoid`, the groupoid of `smooth_fibrewise_linear` functions.
-/

noncomputable theory

open set topological_space
open_locale manifold topological_space


variables {𝕜 B F : Type*} [topological_space B]
variables [nontrivially_normed_field 𝕜] [normed_add_comm_group F] [normed_space 𝕜 F]

/-- For `B` a topological space and `F` a `𝕜`-normed space, a map from `U : set B` to `F ≃L[𝕜] F`
determines a local homeomorphism from `B × F` to itself by its action fibrewise. -/
def fiberwise_linear.local_homeomorph (φ : B → F ≃L[𝕜] F) {U : set B} (hU : is_open U)
  (hφ : continuous_on (λ x, φ x : B → F →L[𝕜] F) U)
  (h2φ : continuous_on (λ x, (φ x).symm : B → F →L[𝕜] F) U) :
  local_homeomorph (B × F) (B × F) :=
{ to_fun := λ x, (x.1, φ x.1 x.2),
  inv_fun := λ x, (x.1, (φ x.1).symm x.2),
  source := U ×ˢ univ,
  target := U ×ˢ univ,
  map_source' := λ x hx, mk_mem_prod hx.1 (mem_univ _),
  map_target' := λ x hx, mk_mem_prod hx.1 (mem_univ _),
  left_inv' := λ x _, prod.ext rfl (continuous_linear_equiv.symm_apply_apply _ _),
  right_inv' := λ x _, prod.ext rfl (continuous_linear_equiv.apply_symm_apply _ _),
  open_source := hU.prod is_open_univ,
  open_target := hU.prod is_open_univ,
  continuous_to_fun := begin
    have : continuous_on (λ p : B × F, ((φ p.1 : F →L[𝕜] F), p.2)) (U ×ˢ univ),
    { exact hφ.prod_map continuous_on_id },
    exact continuous_on_fst.prod (is_bounded_bilinear_map_apply.continuous.comp_continuous_on this),
  end,
  continuous_inv_fun := begin
    have : continuous_on (λ p : B × F, (((φ p.1).symm : F →L[𝕜] F), p.2)) (U ×ˢ univ),
    { exact h2φ.prod_map continuous_on_id },
    exact continuous_on_fst.prod (is_bounded_bilinear_map_apply.continuous.comp_continuous_on this),
  end, }


lemma fiberwise_linear.source_trans_local_homeomorph {φ : B → (F ≃L[𝕜] F)}
  {U : set B}
  (hU : is_open U)
  (hφ : continuous_on (λ x, φ x : B → F →L[𝕜] F) U)
  (h2φ : continuous_on (λ x, (φ x).symm : B → F →L[𝕜] F) U)
  {φ' : B → (F ≃L[𝕜] F)}
  {U' : set B}
  (hU' : is_open U')
  (hφ' : continuous_on (λ x, φ' x : B → F →L[𝕜] F) U')
  (h2φ' : continuous_on (λ x, (φ' x).symm : B → F →L[𝕜] F) U') :
  (fiberwise_linear.local_homeomorph φ hU hφ h2φ ≫ₕ
      fiberwise_linear.local_homeomorph φ' hU' hφ' h2φ').source = (U ∩ U') ×ˢ univ :=
begin
  dsimp [fiberwise_linear.local_homeomorph],
  mfld_set_tac,
end

lemma fiberwise_linear.trans_local_homeomorph_apply {φ : B → (F ≃L[𝕜] F)}
  {U : set B}
  (hU : is_open U)
  (hφ : continuous_on (λ x, φ x : B → F →L[𝕜] F) U)
  (h2φ : continuous_on (λ x, (φ x).symm : B → F →L[𝕜] F) U)
  {φ' : B → (F ≃L[𝕜] F)}
  {U' : set B}
  (hU' : is_open U')
  (hφ' : continuous_on (λ x, φ' x : B → F →L[𝕜] F) U')
  (h2φ' : continuous_on (λ x, (φ' x).symm : B → F →L[𝕜] F) U')
  {b : B}
  (v : F) :
  (fiberwise_linear.local_homeomorph φ hU hφ h2φ ≫ₕ
      fiberwise_linear.local_homeomorph φ' hU' hφ' h2φ') ⟨b, v⟩ = ⟨b, φ' b (φ b v)⟩ :=
rfl

variables {EB : Type*} [normed_add_comm_group EB] [normed_space 𝕜 EB]
  {HB : Type*} [topological_space HB] [charted_space HB B] {IB : model_with_corners 𝕜 EB HB}

lemma smooth_fibrewise_linear.locality_aux₂ {e : local_homeomorph (B × F) (B × F)}
  {U : set B}
  (h : ∀ x ∈ U, ∃ (φ : B → (F ≃L[𝕜] F)) (u : set B) (hu : is_open u) (hUu : u ⊆ U) (hux : x ∈ u)
    (hφ : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ x, (φ x : F →L[𝕜] F)) u)
    (h2φ : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ x, ((φ x).symm : F →L[𝕜] F)) u),
    (e.restr (u ×ˢ univ)).eq_on_source
      (fiberwise_linear.local_homeomorph φ hu hφ.continuous_on h2φ.continuous_on)) :
  ∃ (φ : U → B → (F ≃L[𝕜] F))
  (u : U → set B)
  (hu : ∀ x, is_open (u x))
  (hφ : ∀ x, smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ y, (φ x y : F →L[𝕜] F)) (u x))
  (h2φ : ∀ x, smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ (y : B), ((φ x y).symm : F →L[𝕜] F)) (u x)),
  (∀ x, u x ⊆ U) ∧
  (∀ x, ↑x ∈ u x) ∧
  (∀ x, eq_on e (λ q, (q.1, φ x q.1 q.2)) (u x ×ˢ univ)) :=
begin
  rw set_coe.forall' at h,
  choose! φ u hu hUu hux hφ h2φ heφ using h,
  have heuφ : ∀ x : U, eq_on e (λ q, (q.1, φ x q.1 q.2)) (u x ×ˢ univ),
  { intros x p hp,
    refine (heφ x).2 _,
    rw (heφ x).1,
    exact hp },
  exact ⟨φ, u, hu, hφ, h2φ, hUu, hux, heuφ⟩
end

lemma smooth_fibrewise_linear.locality_aux₃ {e : local_homeomorph (B × F) (B × F)}
  {U : set B}
  (hU : e.source = U ×ˢ univ)
  {φ : U → B → (F ≃L[𝕜] F)}
  {u : U → set B}
  (hUu : ∀ x, u x ⊆ U)
  (hux : ∀ x, ↑x ∈ u x)
  (heuφ : ∀ x, eq_on e (λ q, (q.1, φ x q.1 q.2)) (u x ×ˢ univ)) :
  (U = ⋃ i, u i) ∧
  ∃ (Φ : B → (F ≃L[𝕜] F)),
    (∀ x : U, ∀ y ∈ u x, Φ y = φ x y) ∧
    eq_on e (λ x, (x.1, Φ x.1 x.2)) e.source :=
begin
  classical,
  have huφ : ∀ (x x' : U) (y : B) (hyx : y ∈ u x) (hyx' : y ∈ u x'), φ x y = φ x' y,
  { intros p p' y hyp hyp',
    ext v,
    have h1 : e (y, v) = (y, φ p y v) := heuφ _ ⟨(id hyp : (y, v).fst ∈ u p), trivial⟩,
    have h2 : e (y, v) = (y, φ p' y v) := heuφ _ ⟨(id hyp' : (y, v).fst ∈ u p'), trivial⟩,
    exact congr_arg prod.snd (h1.symm.trans h2) },
  have hUu' : U = ⋃ i, u i,
  { ext x,
    rw mem_Union,
    refine ⟨λ h, ⟨⟨x, h⟩, hux _⟩, _⟩,
    rintros ⟨x, hx⟩,
    exact hUu x hx },
  let Φ₀ : U → F ≃L[𝕜] F := Union_lift u (λ x, (φ x) ∘ coe) huφ U hUu'.le,
  let Φ : B → F ≃L[𝕜] F := λ y, if hy : y ∈ U then Φ₀ ⟨y, hy⟩ else continuous_linear_equiv.refl 𝕜 F,
  have hΦ : ∀ (y) (hy : y ∈ U), Φ y = Φ₀ ⟨y, hy⟩ := λ y hy, dif_pos hy,
  have hΦφ : ∀ x : U, ∀ y ∈ u x, Φ y = φ x y,
  { intros x y hyu,
    refine (hΦ y (hUu x hyu)).trans _,
    exact Union_lift_mk ⟨y, hyu⟩ _ },
  refine ⟨hUu', ⟨Φ, hΦφ, _⟩⟩,
  intros p hp,
  rw [hU] at hp,
  rw heuφ ⟨p.fst, hp.1⟩ ⟨hux _, hp.2⟩,
  congrm (_, _),
  rw hΦφ,
  exact hux _
end

/-- Let `e` be a local homeomorphism of `B × F` whose source is `U ×ˢ univ`, for some set `U` in
`B`, and which, at any point `x` in `U`, admits a neighbourhood `u` of `x` such that `e` is equal on
`u ×ˢ univ` to the application fibrewise of a function `φ : B → (F ≃L[𝕜] F)` which is smooth and has
smooth inverse.

This is the key mathematical point of the `locality` condition in the construction of the
`structure_groupoid` of bi-smooth fibrewise linear local homeomorphisms.  The proof is by gluing
together the various bi-smooth fibrewise linear local homeomorphism which exist locally.

This proof is broken into four parts to fight timeouts. -/
lemma smooth_fibrewise_linear.locality_aux₄ {e : local_homeomorph (B × F) (B × F)}
  {U : set B}
  (hU : e.source = U ×ˢ univ)
  {φ : U → B → (F ≃L[𝕜] F)}
  {u : U → set B}
  (hUu : ∀ x, u x ⊆ U)
  (hux : ∀ x, ↑x ∈ u x)
  (heuφ : ∀ x, eq_on e (λ q, (q.1, φ x q.1 q.2)) (u x ×ˢ univ))
  (hu : ∀ x, is_open (u x))
  (hφ : ∀ x, smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ y, (φ x y : F →L[𝕜] F)) (u x))
  (h2φ : ∀ x, smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ (y : B), ((φ x y).symm : F →L[𝕜] F)) (u x)) :
  ∃ (hU' : is_open U) (Φ : B → (F ≃L[𝕜] F))
    (hΦ : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ x, (Φ x : F →L[𝕜] F)) U)
    (h2Φ : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ x, ((Φ x).symm : F →L[𝕜] F)) U),
    e.eq_on_source (fiberwise_linear.local_homeomorph Φ hU' hΦ.continuous_on h2Φ.continuous_on) :=
begin
  obtain ⟨hUu', ⟨Φ, hΦφ, H⟩⟩ := smooth_fibrewise_linear.locality_aux₃ hU hUu hux heuφ,
  have hU' : is_open U,
  { rw hUu',
    apply is_open_Union hu },
  have hΦ : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ y, (Φ y : F →L[𝕜] F)) U,
  { apply cont_mdiff_on_of_locally_cont_mdiff_on,
    intros x hx,
    refine ⟨u ⟨x, hx⟩, hu ⟨x, hx⟩, hux _, _⟩,
    refine (cont_mdiff_on.congr (hφ ⟨x, hx⟩) _).mono (inter_subset_right _ _),
    intros y hy,
    rw hΦφ ⟨x, hx⟩ y hy },
  have h2Φ : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ y, ((Φ y).symm : F →L[𝕜] F)) U,
  { apply cont_mdiff_on_of_locally_cont_mdiff_on,
    intros x hx,
    refine ⟨u ⟨x, hx⟩, hu ⟨x, hx⟩, hux _, _⟩,
    refine (cont_mdiff_on.congr (h2φ ⟨x, hx⟩) _).mono (inter_subset_right _ _),
    intros y hy,
    rw hΦφ ⟨x, hx⟩ y hy },
  exact ⟨hU', Φ, hΦ, h2Φ, ⟨hU, H⟩⟩,
end

/-- Let `e` be a local homeomorphism of `B × F`.  Suppose that at every point `p` in the source of
`e`, there is some neighbourhood `s` of `p` on which `e` is equal to a bi-smooth fibrewise linear
local homeomorphism.

Then the source of `e` is of the form `U ×ˢ univ`, for some set `U` in `B`, and, at any point `x` in
`U`, admits a neighbourhood `u` of `x` such that `e` is equal on `u ×ˢ univ` to some bi-smooth
fibrewise linear local homeomorphism. -/
lemma smooth_fibrewise_linear.locality_aux₁ (e : local_homeomorph (B × F) (B × F))
  (h : ∀ p ∈ e.source, ∃ s : set (B × F), is_open s ∧ p ∈ s ∧
    ∃ (φ : B → (F ≃L[𝕜] F)) (u : set B) (hu : is_open u)
      (hφ : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ x, (φ x : F →L[𝕜] F)) u)
      (h2φ : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ x, ((φ x).symm : F →L[𝕜] F)) u),
      (e.restr s).eq_on_source
            (fiberwise_linear.local_homeomorph φ hu hφ.continuous_on h2φ.continuous_on)) :
  ∃ (U : set B) (hU : e.source = U ×ˢ univ),
  ∀ x ∈ U, ∃ (φ : B → (F ≃L[𝕜] F)) (u : set B) (hu : is_open u) (huU : u ⊆ U) (hux : x ∈ u)
    (hφ : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ x, (φ x : F →L[𝕜] F)) u)
    (h2φ : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ x, ((φ x).symm : F →L[𝕜] F)) u),
    (e.restr (u ×ˢ univ)).eq_on_source
      (fiberwise_linear.local_homeomorph φ hu hφ.continuous_on h2φ.continuous_on) :=
begin
  rw set_coe.forall' at h,
  choose! s hs hsp φ u hu hφ h2φ heφ using h,
  have hesu : ∀ p : e.source, e.source ∩ s p = u p ×ˢ univ,
  { intros p,
    rw ← e.restr_source' (s _) (hs _),
    exact (heφ p).1 },
  have hu' : ∀ p : e.source, (p : B × F).fst ∈ u p,
  { intros p,
    have : (p : B × F) ∈ e.source ∩ s p := ⟨p.prop, hsp p⟩,
    simpa only [hesu, mem_prod, mem_univ, and_true] using this },
  have heu : ∀ p : e.source, ∀ q : B × F, q.fst ∈ u p → q ∈ e.source,
  { intros p q hq,
    have : q ∈ u p ×ˢ (univ : set F) := ⟨hq, trivial⟩,
    rw ← hesu p at this,
    exact this.1 },
  have he : e.source = (prod.fst '' e.source) ×ˢ (univ : set F),
  { ext p,
    simp_rw [mem_prod, mem_image, mem_univ, and_true],
    split,
    { intros hp,
      exact ⟨p, hp, rfl⟩ },
    { rintros ⟨q, hq, hpq⟩,
      apply heu,
      rw ← hpq,
      exact hu' ⟨q, hq⟩ } },
  refine ⟨prod.fst '' e.source, he, _⟩,
  rintros x ⟨p, hp, rfl⟩,
  let q : e.to_local_equiv.source := ⟨p, hp⟩,
  refine ⟨φ q, u q, hu q, _, hu' _, hφ q, h2φ q, _⟩,
  { intros y hy,
    refine ⟨(y, 0), heu q _ _, rfl⟩,
    exact hy },
  { rw [← hesu, e.restr_source_inter],
    exact heφ q },
end

lemma smooth_fibrewise_linear.trans_aux
  {e e' : local_homeomorph (B × F) (B × F)}
  {φ : B → (F ≃L[𝕜] F)}
  {U : set B}
  (hU : is_open U)
  (hφ : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ x, φ x : B → F →L[𝕜] F) U)
  (h2φ : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ x, (φ x).symm : B → F →L[𝕜] F) U)
  {φ' : B → (F ≃L[𝕜] F)}
  {U' : set B}
  (hU' : is_open U')
  (hφ' : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ x, φ' x : B → F →L[𝕜] F) U')
  (h2φ' : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ x, (φ' x).symm : B → F →L[𝕜] F) U')
  (heφ : e.eq_on_source
    (fiberwise_linear.local_homeomorph φ hU hφ.continuous_on h2φ.continuous_on))
  (heφ' : e'.eq_on_source
    (fiberwise_linear.local_homeomorph φ' hU' hφ'.continuous_on h2φ'.continuous_on)) :
  ∃ (φ'' : B → (F ≃L[𝕜] F)) (U'' : set B) (hU'' : is_open U'')
  (hφ'' : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ x, φ'' x : B → F →L[𝕜] F) U'')
  (h2φ'' : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ x, (φ'' x).symm : B → F →L[𝕜] F) U''),
    (e ≫ₕ e').eq_on_source
    (fiberwise_linear.local_homeomorph φ'' hU'' hφ''.continuous_on h2φ''.continuous_on) :=
begin
  refine ⟨λ b, (φ b).trans (φ' b), _, hU.inter hU', _, _, setoid.trans (heφ.trans' heφ') ⟨_, _⟩⟩,
  { have : smooth_on IB 𝓘(𝕜, (F →L[𝕜] F) × (F →L[𝕜] F))
      (λ x, ((φ' x : F →L[𝕜] F), (φ x : F →L[𝕜] F))) (U ∩ U'),
    { exact (hφ'.mono (inter_subset_right _ _)).prod_mk (hφ.mono (inter_subset_left _ _)) },
    exact is_bounded_bilinear_map_comp.cont_diff.cont_mdiff.comp_cont_mdiff_on this },
  { have : smooth_on IB 𝓘(𝕜, (F →L[𝕜] F) × (F →L[𝕜] F))
      (λ x, (((φ x).symm : F →L[𝕜] F), ((φ' x).symm : F →L[𝕜] F))) (U ∩ U'),
    { exact (h2φ.mono (inter_subset_left _ _)).prod_mk (h2φ'.mono (inter_subset_right _ _)) },
    exact is_bounded_bilinear_map_comp.cont_diff.cont_mdiff.comp_cont_mdiff_on this },
  { apply fiberwise_linear.source_trans_local_homeomorph },
  { rintros ⟨b, v⟩ hb,
    apply fiberwise_linear.trans_local_homeomorph_apply }
end

variables (F B IB)

/-- For `B` a manifold and `F` a normed space, the groupoid on `B × F` consisting of local
homeomorphisms which are bi-smooth and fibrewise linear. -/
def smooth_fiberwise_linear : structure_groupoid (B × F) :=
{ members := ⋃ (φ : B → F ≃L[𝕜] F) (U : set B) (hU : is_open U)
  (hφ : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ x, φ x : B → F →L[𝕜] F) U)
  (h2φ : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ x, (φ x).symm : B → F →L[𝕜] F) U),
  {e | e.eq_on_source (fiberwise_linear.local_homeomorph φ hU hφ.continuous_on h2φ.continuous_on)},
  trans' := begin -- the hard work has been extracted to `trans_aux`
    simp_rw [mem_Union],
    rintros e e' ⟨φ, U, hU, hφ, h2φ, heφ⟩ ⟨φ', U', hU', hφ', h2φ', heφ'⟩,
    exact smooth_fibrewise_linear.trans_aux hU hφ h2φ hU' hφ' h2φ' heφ heφ',
  end,
  symm' := begin
    simp_rw [mem_Union],
    rintros e ⟨φ, U, hU, hφ, h2φ, heφ⟩,
    refine ⟨λ b, (φ b).symm, U, hU, h2φ, _, heφ.symm'⟩,
    simp_rw continuous_linear_equiv.symm_symm,
    exact hφ
  end,
  id_mem' := begin
    simp_rw [mem_Union],
    refine ⟨λ b, continuous_linear_equiv.refl 𝕜 F, univ, is_open_univ, _, _, ⟨_, λ b hb, _⟩⟩,
    { apply cont_mdiff_on_const },
    { apply cont_mdiff_on_const },
    { simp only [fiberwise_linear.local_homeomorph] with mfld_simps },
    { simp only [fiberwise_linear.local_homeomorph, continuous_linear_equiv.coe_refl', prod.mk.eta]
        with mfld_simps, },
  end,
  locality' := begin -- the hard work has been extracted to `locality_aux₁` thru `locality_aux₄`
    simp_rw [mem_Union],
    intros e he,
    obtain ⟨U, hU, h⟩ := smooth_fibrewise_linear.locality_aux₁ e he,
    obtain ⟨φ, u, hu, hφ, h2φ, hUu, hux, heuφ⟩ := smooth_fibrewise_linear.locality_aux₂ h,
    obtain ⟨hU', Φ, hΦ⟩ := smooth_fibrewise_linear.locality_aux₄ hU hUu hux heuφ hu hφ h2φ,
    exact ⟨Φ, U, hU', hΦ⟩,
  end,
  eq_on_source' := begin
    simp_rw [mem_Union],
    rintros e e' ⟨φ, U, hU, hφ, h2φ, heφ⟩ hee',
    exact ⟨φ, U, hU, hφ, h2φ, setoid.trans hee' heφ⟩,
  end }
