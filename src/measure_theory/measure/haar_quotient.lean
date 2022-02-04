/-
Copyright (c) 2022 Alex Kontorovich and Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth
-/

import measure_theory.measure.haar
import measure_theory.group.fundamental_domain
import topology.compact_open
import algebra.group.opposite

/-!
# Haar quotient measure

In this file, we consider properties of fundamental domains and measures for the action of a
subgroup of a group `G` on `G` itself.

## Main results

* `measure_theory.is_fundamental_domain.smul_invariant_measure_map `: given a subgroup `Γ` of a
  topological group `G`, the pushforward to the coset space `G ⧸ Γ` of the restriction of a both
  left- and right-invariant measure on `G` to a fundamental domain `𝓕` is a `G`-invariant measure
  on `G ⧸ Γ`.

* `measure_theory.is_fundamental_domain.is_mul_left_invariant_map `: given a normal subgroup `Γ` of
  a topological group `G`, the pushforward to the quotient group `G ⧸ Γ` of the restriction of
  a both left- and right-invariant measure on `G` to a fundamental domain `𝓕` is a left-invariant
  measure on `G ⧸ Γ`.

Note that a group `G` with Haar measure that is both left and right invariant is called
**unimodular**.
-/

-- THIS GOES ELSEWHERE
open_locale pointwise

theorem measure_theory.is_fundamental_domain.set_integral_eq_tsum {G : Type*} {α : Type*} [group G]
  [mul_action G α] [measurable_space α] {s : set α} {μ : measure_theory.measure α}
  [measurable_space G] [has_measurable_smul G α] [measure_theory.smul_invariant_measure G α μ]
  [encodable G] {E : Type*} [normed_group E] [normed_space ℝ E] [measurable_space E]
  [borel_space E] [complete_space E] [topological_space.second_countable_topology E]
  (h : measure_theory.is_fundamental_domain G s μ) (f : α → E) (t : set α) :
∫ (x : α) in t, f x ∂μ = ∑' (g : G), ∫ (x : α) in g • t ∩ s, f (g⁻¹ • x) ∂μ :=
sorry

theorem measure_theory.integral_tsum {α : Type*} {β : Type*} {m : measurable_space α}
  {μ : measure_theory.measure α} [encodable β] {E : Type*} [normed_group E] [normed_space ℝ E]
  [measurable_space E] [borel_space E] [complete_space E]
  [topological_space.second_countable_topology E] {f : β → α → E}
  (hf : ∀ (i : β), measurable (f i)) :
∫ (a : α), (∑' (i : β), f i a) ∂μ = ∑' (i : β), ∫ (a : α), f i a ∂μ :=
sorry



open set measure_theory topological_space

variables {G : Type*} [group G] [measurable_space G] [topological_space G]
  [topological_group G] [borel_space G]
  (μ : measure G)
  (Γ : subgroup G)

/-- Given a subgroup `Γ` of `G` and a right invariant measure `μ` on `G`, the measure is also
  invariant under the action of `Γ` on `G` by **right** multiplication. -/
@[to_additive "Given a subgroup `Γ` of an additive group `G` and a right invariant measure `μ` on
  `G`, the measure is also invariant under the action of `Γ` on `G` by **right** addition."]
lemma subgroup.smul_invariant_measure [μ.is_mul_right_invariant] :
  smul_invariant_measure Γ.opposite G μ :=
{ measure_preimage_smul :=
begin
  rintros ⟨c, hc⟩ s hs,
  dsimp [(•)],
  refine measure_preimage_mul_right μ (mul_opposite.unop c) s,
end}

variables {Γ} {μ}

/-- Measurability of the action of the topological group `G` on the left-coset space `G/Γ`. -/
@[to_additive "Measurability of the action of the additive topological group `G` on the left-coset
  space `G/Γ`."]
instance quotient_group.has_measurable_smul [measurable_space (G ⧸ Γ)] [borel_space (G ⧸ Γ)] :
  has_measurable_smul G (G ⧸ Γ) :=
{ measurable_const_smul := λ g, (continuous_smul₂ g).measurable,
  measurable_smul_const := λ x, (quotient_group.continuous_smul₁ x).measurable }

variables {𝓕 : set G} (h𝓕 : is_fundamental_domain Γ.opposite 𝓕 μ)
include h𝓕

/-- If `𝓕` is a fundamental domain for the action by right multiplication of a subgroup `Γ` of a
  topological group `G`, then its left-translate by an element of `g` is also a fundamental
  domain. -/
@[to_additive "If `𝓕` is a fundamental domain for the action by right addition of a subgroup `Γ`
  of an additive topological group `G`, then its left-translate by an element of `g` is also a
  fundamental domain."]
lemma measure_theory.is_fundamental_domain.smul (g : G) [μ.is_mul_left_invariant] :
  is_fundamental_domain ↥Γ.opposite (has_mul.mul g ⁻¹' 𝓕) μ :=
{ measurable_set := measurable_set_preimage (measurable_const_mul g) (h𝓕.measurable_set),
  ae_covers := begin
    let s := {x : G | ¬∃ (γ : ↥(Γ.opposite)), γ • x ∈ 𝓕},
    have μs_eq_zero : μ s = 0 := h𝓕.2,
    change μ {x : G | ¬∃ (γ : ↥(Γ.opposite)), g * γ • x ∈ 𝓕} = 0,
    have : {x : G | ¬∃ (γ : ↥(Γ.opposite)), g * γ • x ∈ 𝓕} = has_mul.mul g ⁻¹' s,
    { ext,
      simp [s, subgroup.left_right_mul], },
    rw [this, measure_preimage_mul μ g s, μs_eq_zero],
  end,
  ae_disjoint := begin
    intros γ γ_ne_one,
    have μs_eq_zero : μ (((λ x, γ • x) '' 𝓕) ∩ 𝓕) = 0 := h𝓕.3 γ γ_ne_one,
    change μ (((λ x, γ • x) '' (has_mul.mul g ⁻¹' 𝓕)) ∩ (has_mul.mul g ⁻¹' 𝓕)) = 0,
    have : ((λ x, γ • x) '' (has_mul.mul g ⁻¹' 𝓕)) ∩ (has_mul.mul g ⁻¹' 𝓕) =
      has_mul.mul g ⁻¹' (((λ x, γ • x) '' 𝓕) ∩ 𝓕),
    { ext,
      simp only [mem_inter_eq, image_smul, and.congr_left_iff, mem_preimage],
      intros gx,
      convert subgroup.left_right_mem_preimage x g γ 𝓕, },
    rw [this, measure_preimage_mul μ g _, μs_eq_zero],
  end }

variables [encodable Γ] [measurable_space (G ⧸ Γ)] [borel_space (G ⧸ Γ)]

/-- The pushforward to the coset space `G ⧸ Γ` of the restriction of a both left- and right-
  invariant measure on `G` to a fundamental domain `𝓕` is a `G`-invariant measure on `G ⧸ Γ`. -/
@[to_additive "The pushforward to the coset space `G ⧸ Γ` of the restriction of a both left- and
  right-invariant measure on an additive topological group `G` to a fundamental domain `𝓕` is a
  `G`-invariant measure on `G ⧸ Γ`."]
lemma measure_theory.is_fundamental_domain.smul_invariant_measure_map
  [μ.is_mul_left_invariant] [μ.is_mul_right_invariant] :
  smul_invariant_measure G (G ⧸ Γ) (measure.map (@quotient_group.mk G _ Γ) (μ.restrict 𝓕)) :=
{ measure_preimage_smul :=
  begin
    let π : G → G ⧸ Γ := @quotient_group.mk G _ Γ ,
    have meas_π : measurable π :=
      continuous.measurable continuous_quotient_mk,
    have 𝓕meas : measurable_set 𝓕 := h𝓕.measurable_set,
    intros g A hA,
    have meas_πA : measurable_set (π ⁻¹' A) := measurable_set_preimage meas_π hA,
    rw [measure.map_apply meas_π hA,
      measure.map_apply meas_π (measurable_set_preimage (measurable_const_smul g) hA),
      measure.restrict_apply' 𝓕meas, measure.restrict_apply' 𝓕meas],
    set π_preA := π ⁻¹' A,
    have : (quotient_group.mk ⁻¹' ((λ (x : G ⧸ Γ), g • x) ⁻¹' A)) = has_mul.mul g ⁻¹' π_preA :=
      by ext1; simp,
    rw this,
    have : μ (has_mul.mul g ⁻¹' π_preA ∩ 𝓕) = μ (π_preA ∩ has_mul.mul (g⁻¹) ⁻¹' 𝓕),
    { transitivity μ (has_mul.mul g ⁻¹' (π_preA ∩ has_mul.mul g⁻¹ ⁻¹' 𝓕)),
      { rw preimage_inter,
        congr,
        rw [← preimage_comp, comp_mul_left, mul_left_inv],
        ext,
        simp, },
      rw measure_preimage_mul, },
    rw this,
    have h𝓕_translate_fundom : is_fundamental_domain Γ.opposite (has_mul.mul g⁻¹ ⁻¹' 𝓕) μ :=
      h𝓕.smul (g⁻¹),
    haveI : smul_invariant_measure ↥(Γ.opposite) G μ := Γ.smul_invariant_measure μ,
    rw h𝓕.measure_set_eq h𝓕_translate_fundom meas_πA,
    rintros ⟨γ, γ_in_Γ⟩,
    ext,
    have : π (x * (mul_opposite.unop γ)) = π (x) := by simpa [quotient_group.eq'] using γ_in_Γ,
    simp [(•), this],
  end }

/-- Assuming `Γ` is a normal subgroup of a topological group `G`, the pushforward to the quotient
  group `G ⧸ Γ` of the restriction of a both left- and right-invariant measure on `G` to a
  fundamental domain `𝓕` is a left-invariant measure on `G ⧸ Γ`. -/
@[to_additive "Assuming `Γ` is a normal subgroup of an additive topological group `G`, the
  pushforward to the quotient group `G ⧸ Γ` of the restriction of a both left- and right-invariant
  measure on `G` to a fundamental domain `𝓕` is a left-invariant measure on `G ⧸ Γ`."]
def measure_theory.is_fundamental_domain.is_mul_left_invariant_map [subgroup.normal Γ]
  [μ.is_mul_left_invariant] [μ.is_mul_right_invariant] :
  (measure.map (quotient_group.mk' Γ) (μ.restrict 𝓕)).is_mul_left_invariant :=
{ map_mul_left_eq_self := begin
    intros x,-- A hA,
    apply measure.ext,
    intros A hA,
    obtain ⟨x₁, _⟩ := @quotient.exists_rep _ (quotient_group.left_rel Γ) x,
    haveI := h𝓕.smul_invariant_measure_map,
    convert measure_preimage_smul x₁ ((measure.map quotient_group.mk) (μ.restrict 𝓕)) A using 1,
    rw [← h, measure.map_apply],
    { refl, },
    { exact measurable_const_mul _, },
    { exact hA, },
  end }

variables [t2_space (G ⧸ Γ)] [topological_space.second_countable_topology (G ⧸ Γ)]
  (K : topological_space.positive_compacts (G ⧸ Γ))

/-- Given a normal subgroup `Γ` of a topological group `G` with Haar measure `μ`, which is also
  right-invariant, and a finite volume fundamental domain `𝓕`, the pushforward to the quotient
  group `G ⧸ Γ` of the restriction of `μ` to `𝓕` is a multiple of Haar measure on `G ⧸ Γ`. -/
@[to_additive "Given a normal subgroup `Γ` of an additive topological group `G` with Haar measure
  `μ`, which is also right-invariant, and a finite volume fundamental domain `𝓕`, the pushforward
  to the quotient group `G ⧸ Γ` of the restriction of `μ` to `𝓕` is a multiple of Haar measure on
  `G ⧸ Γ`."]
lemma measure_theory.is_fundamental_domain.map_restrict_quotient [subgroup.normal Γ]
  [measure_theory.measure.is_haar_measure μ] [μ.is_mul_right_invariant]
  (h𝓕_finite : μ 𝓕 < ⊤) : measure.map (quotient_group.mk' Γ) (μ.restrict 𝓕)
  = (μ (𝓕 ∩ (quotient_group.mk' Γ) ⁻¹' K.val)) • (measure_theory.measure.haar_measure K) :=
begin
  let π : G →* G ⧸ Γ := quotient_group.mk' Γ,
  have meas_π : measurable π :=
    continuous.measurable continuous_quotient_mk, -- projection notation doesn't work here?
  have 𝓕meas : measurable_set 𝓕 := h𝓕.measurable_set,
  haveI : is_finite_measure (μ.restrict 𝓕) :=
    ⟨by { rw [measure.restrict_apply' 𝓕meas, univ_inter], exact h𝓕_finite }⟩,
  -- the measure is left-invariant, so by the uniqueness of Haar measure it's enough to show that
  -- it has the stated size on the reference compact set `K`.
  haveI : (measure.map (quotient_group.mk' Γ) (μ.restrict 𝓕)).is_mul_left_invariant :=
    h𝓕.is_mul_left_invariant_map,
  rw [measure.haar_measure_unique (measure.map (quotient_group.mk' Γ) (μ.restrict 𝓕)) K,
    measure.map_apply meas_π, measure.restrict_apply' 𝓕meas, inter_comm],
  exact K.prop.1.measurable_set,
end







---------------------------- UNFOLDING TRICK ---------------

open_locale big_operators

theorem disjoint.inter {α : Type*} {s t : set α} (u : set α) (h : disjoint s t) :
disjoint (u ∩ s) (u ∩ t) := by apply_rules [disjoint.inter_right', disjoint.inter_left']

theorem disjoint.inter' {α : Type*} {s t : set α} (u : set α) (h : disjoint s t) :
disjoint (s ∩ u) (t ∩ u) := by apply_rules [disjoint.inter_left, disjoint.inter_right]


/-
-- see if this exists in fundamental domain
lemma integral_Union {ι : Type*} [encodable ι] {s : ι → set ℝ } (f : ℝ  → ℂ )
  (hm : ∀ i, measurable_set (s i)) (hd : pairwise (disjoint on s)) (hfi : integrable f  ) :
  (∫ a in (⋃ n, s n), f a ) = ∑' n, ∫ a in s n, f a  :=
sorry
-/

local notation `μ_𝓕` := measure.map (@quotient_group.mk G _ Γ) (μ.restrict 𝓕)


/-- This is the "unfolding" trick -/
lemma unfolding_trick [μ.is_mul_left_invariant] [μ.is_mul_right_invariant]
  (f : G → ℂ) (hf : measurable f) (g : G ⧸ Γ → ℂ) (hg : measurable g) (F : G ⧸ Γ → ℂ)
  (hF : measurable F) (hFf : ∀ (x : G), F (x : G ⧸ Γ) = ∑' (γ : Γ.opposite), f(γ • x)) :
  ∫ (x : G), f x * g (x : G ⧸ Γ) ∂μ = ∫ (x : G ⧸ Γ), F(x) * g(x) ∂ μ_𝓕 :=
begin
  have hFf' : ∀ (x : G), F (x : G ⧸ Γ) = ∑' (γ : Γ.opposite), f(γ⁻¹ • x),
  {
    intros x,
    sorry,
  },
  rw integral_map,
  have : ∀ (x : G), F (x : G ⧸ Γ) * g (x) = ∑' (γ : Γ.opposite), f(γ⁻¹ • x) * g (x),
  {
    intros x,
    rw hFf' x,
--    refine tsum_smul_const _,
    sorry,
    --simp [hFf],
  },
  refine eq.trans _ (integral_congr_ae (filter.eventually_of_forall this)).symm,
  rw measure_theory.integral_tsum,
  haveI := h𝓕.smul_invariant_measure_map,
  haveI : smul_invariant_measure ↥(Γ.opposite) G μ := Γ.smul_invariant_measure μ,
  convert measure_theory.is_fundamental_domain.set_integral_eq_tsum h𝓕 (λ x, f x * g x) univ,
  { simp, },
  {
    ext1 γ,
    simp only [smul_set_univ, univ_inter],
    congr,
    ext1 x,
    have : g ↑(γ⁻¹ • x) = g x,
    {

      sorry,
    },
    rw this,
  },
  {
    intros γ,
    sorry,
    --- use hf, hg
  },
  {
    sorry,
  },
  {
    sorry,
  },
end
/-

  rw integral_map,
    {
      symmetry,
      calc
      ∫ (x : ℝ) in Ico 0 1, F (↑x) * g (↑x)
      = ∫ (x : ℝ) in Ico 0 1, (∑' (n:ℤ ), f ((n:ℝ)+x)) * g (↑x) : _
      ... = ∑' (n : ℤ), ∫ (x : ℝ) in Ico 0 1,  f (↑n+x) * g (↑x) : _
      ... = ∑' (n : ℤ), ∫ (x : ℝ) in Ico 0 1,
              (λ x, f (x) * g (↑x)) (has_add.add n x) : _
      ... = ∑' (n : ℤ), ∫ (x : ℝ), f (x) * g (↑x)
              ∂(measure_theory.measure.map (has_add.add (n:ℝ))
              (volume.restrict (Ico (0:ℝ) 1))) : _
      ... = ∑' (n : ℤ), ∫ (x : ℝ) in (has_add.add (-(n:ℝ))) ⁻¹' (Ico 0 1),
              f (x) * g (↑x) : _
      ... = ∫ (x : ℝ) in ⋃ (n : ℤ), (λ x:ℝ, -(n:ℝ)+x) ⁻¹' (Ico 0 1), f x * g x : _
      ... = ∫ (x : ℝ), f x * g x : _,

      { congr' 1,
        ext1,
        rw (_ : F (↑x) = (∑' (n : ℤ), f (↑n+x))),
        convert hFf x, },
      { -- dominated convergence, need to reverse sum (n:ℤ ) int_0^1
        sorry, },
      { congr' 1,
        ext1 n,
        congr' 1,
        ext1 x,
        rw ←  (_ : g (↑(↑n + x)) = g (↑x)),
        congr' 1,
        rw quotient_add_group.eq,
        use -n,
        simp, },
      {
        congr' 1,
        ext1 n,
        rw measure_theory.integral_map,
        { exact measurable_const_add (↑n), },
        sorry,
        -- need ae measurable f * g
      },
      {
        congr' 1, ext1 n,
        congr' 1,

        transitivity (map (has_add.add (n:ℝ)) volume).restrict (has_add.add ↑(-n) ⁻¹' Ico 0 1),

        {
          convert (@measure_theory.measure.restrict_map _ _ _ _ (volume : measure ℝ)
            (has_add.add (n:ℝ)) _ ((has_add.add ↑(-n) ⁻¹' Ico 0 1)) _).symm,

          { rw ← set.preimage_comp ,
            convert ( set.preimage_id).symm,
            ext1 x,
            simp, },

          { exact measurable_const_add ↑n, },

          sorry, -- measurability of Ico
        },



        rw real.map_volume_add_left,
        congr,
        norm_cast,
      },
      {
        symmetry,
        refine integral_Union (λ x, f x * g x) _ _ _,
        { intros n,
          sorry,
          --exact measurable_set_Ico,
          },
        { rintros i j ineqj x ⟨ hx1, hx2⟩ ,
          exact ineqj (RmodZuniqueRep' hx1 hx2), },
        { --  integrable volume
          sorry, }, },
      { congr' 1,
        convert measure.restrict_univ using 2,
        rw set.eq_univ_iff_forall ,
        intros x,
        rw set.mem_Union,
        let n := floor x,
        use n,
        have := floor_eq_on_Ico'',
        refine floor_eq_on_Ico'' _ _ _,
        dsimp only [n],
        refl, }, },
    { -- measurable quotient_add_group.mk
      -- continuous by definition. no content
      sorry,
    },
    {
      -- ae_measurable, no content
      sorry,
    },
  },
  { exact measurable_set_Ico, },
  { exact RmodZuniqueRep, },
  sorry,
end
  -/


/-
lemma real_to_haar (f : Schwarz) : ∫ (x : ℝ), f x = ∑' (n : ℤ), ∫ x in set.Icc (0:ℝ) (1:ℝ), f( x + n) :=
begin
  -- need lemma relating tsum to partial sums, same on the other side. then take limits (dominated convergence)

  have :∀ᶠ n in (filter.cofinite), ae_measurable (indicator (set.Icc (n:ℝ) (n+1)) f ),
  {
--    intros n,
   sorry,
  },
  have h2 : ae_measurable f,
  {
    sorry,
  },
  have :=  measure_theory.tendsto_integral_filter_of_dominated_convergence (λ x, complex.abs (f x)) _ this h2 _ _,

  repeat {sorry},
end

-- Schwarz are integrable,
-- they are almost everywhere measurable
-- Multiply by |⬝|=1 and get another Schwarz function.


-- pushforward under expm of rest_Lebesgue = haar
-- map under expm ...
lemma pushforward_is_Haar :
measure_theory.measure.map exp_map_circle (volume.restrict (Icc (0:ℝ) 1))
=
haar_circle
:=
begin

  --  measure_theory.measure.map
  sorry,
end



lemma unfolding_trick (f : Schwarz ) ( y : ℝ ) (m : ℤ ) :
cof f (quotient.mk' y) m = Fourier_transform f (m:ℝ ) * complex.exp (-2 * real.pi * complex.I * m * y) :=
begin
  rw cof,
  simp,
  dsimp [inner],
  have : ∫ (a : ↥circle), complex.conj ((fourier_Lp 2 m) a) * (auto_descend''' f (quotient.mk' y)) a ∂haar_circle
  =
  ∫ (a : ↥circle), complex.conj ((fourier m) a) * (auto_descend'' f (quotient.mk' y)) a ∂haar_circle
  := sorry,
  rw this,
  clear this,
  simp,
  rw auto_descend'',
  rw auto_descend,
  simp,
  dsimp [auto_descend, auto_descend', automorphic_point_pair_invariant'],
  rw real_to_haar,
--  simp,

  sorry,
end

theorem Poisson_summation (f : Schwarz) : ∑' (n:ℤ), f n = ∑' (m:ℤ), (Fourier_transform f) m :=
begin
--  let K := (auto_descend f) ∘ (expm × expm) ,

  sorry,
end
-/
