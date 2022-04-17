/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import number_theory.weight_space
import number_theory.dirichlet_character
import number_theory.general_bernoullli_number
import ring_theory.roots_of_unity

/-!
# Special values of the p-adic L-function

This file determines the special values the p-adic L-function takes at negative integers, in terms
of generalized Bernoulli numbers. We first define Dirichlet characters over ℤ and then relate them
to multiplicative homomorphisms over ℤ/nℤ for any n divisible by the conductor. We then define the
generalized Bernoulli numbers related to Dirichlet characters.

## Main definitions
 * `p_adic_L_function'`

## Implementation notes
TODO (optional)

## References
Introduction to Cyclotomic Fields, Washington (Chapter 12, Section 2)

## Tags
p-adic, L-function, Bernoulli measure, Dirichlet character
-/

/-- The Teichmuller character defined on 𝔽ₚ*. -/
noncomputable abbreviation teichmuller_character_mod_p (p : ℕ) [fact (nat.prime p)] :
  dirichlet_character ℤ_[p] p :=
units.map (((witt_vector.equiv p).to_monoid_hom).comp (witt_vector.teichmuller p))

lemma units.map_injective {M N : Type*} [monoid M] [monoid N] (f : M →* N)
  (hf : function.injective f) : function.injective (units.map f) :=
λ a b h, begin
  rw ←units.eq_iff at *, rw [units.coe_map, units.coe_map] at h,
  apply hf h,
end

lemma teichmuller_character_mod_p_injective (p : ℕ) [fact (nat.prime p)] :
  function.injective (teichmuller_character_mod_p p) :=
begin
  delta teichmuller_character_mod_p,
  rw units.map_comp,
  change function.injective (function.comp (units.map (witt_vector.equiv p).to_monoid_hom)
    (units.map (@witt_vector.teichmuller p (zmod p) _ _))),
  apply function.injective.comp,
  { apply units.map_injective _ _,
    apply (equiv.injective (witt_vector.equiv p).to_equiv), },
  { apply units.map_injective _ _,
    intros a b h,
    rw witt_vector.ext_iff at h,
    specialize h 0,
    repeat { rw witt_vector.teichmuller_coeff_zero p at h, },
    assumption, },
end

lemma teichmuller_character_mod_p_ne_one (p : ℕ) [fact (nat.prime p)] (hp : 2 < p) :
  teichmuller_character_mod_p p ≠ 1 :=
λ h, begin
  have := teichmuller_character_mod_p_injective p,
  rw h at this,
  haveI : nontrivial (units (zmod p)),
  { refine fintype.one_lt_card_iff_nontrivial.mp _,
    rw zmod.card_units p,
    exact lt_sub_iff_left.mpr hp, },
  have h' := function.injective.exists_ne this 1,
  simp only [eq_self_iff_true, exists_false, monoid_hom.one_apply, not_true, ne.def] at h',
  assumption,
end

instance : fact (nat.prime 2) := by { apply fact_iff.2 nat.prime_two, }

lemma teichmuller_character_mod_p_two : teichmuller_character_mod_p 2 = 1 :=
begin
  rw monoid_hom.ext_iff,
  intro x,
  simp only [units.coe_map, units.coe_one, function.comp_app, monoid_hom.one_apply,
    padic_int.coe_one, monoid_hom.coe_comp],
  convert (teichmuller_character_mod_p 2).map_one,
end

lemma is_primitive_teichmuller_character_zmod_p (p : ℕ) [fact (nat.prime p)] (hp : 2 < p) :
  (teichmuller_character_mod_p p).is_primitive :=
begin
  have dvd := dirichlet_character.conductor_dvd (teichmuller_character_mod_p p),
  rw nat.dvd_prime _ at dvd,
  { cases dvd,
    { exfalso, apply teichmuller_character_mod_p_ne_one p hp
      (dirichlet_character.conductor_eq_one _ dvd), },
    { exact dvd, }, },
  { apply fact.out, },
end

/-lemma is_primitive_teichmuller_character_mod_p_pow (p : ℕ) [fact (nat.prime p)] (m : ℕ) :
  (teichmuller_character_mod_p p^m).is_primitive :=
begin
  have f1 := (teichmuller_character_mod_p p ^ m).conductor_dvd,
  rw nat.dvd_prime _ at f1,
  { cases f1,
    { have f2 := dirichlet_character.conductor_eq_one _ f1,
      exfalso, apply zero_ne_one f2, },
    { exact f1, }, },
  { apply fact.out, },
end-/

/-lemma is_primitive_teich_char_comp (p : ℕ) [fact (nat.prime p)] (m : ℕ)
  {S : Type*} [comm_monoid_with_zero S] [nontrivial S] (f : units ℤ_[p] →* units S) :
  (dirichlet_character.comp (teichmuller_character_mod_p p^m) f).is_primitive :=
begin
  rw dirichlet_character.is_primitive_def,
  obtain ⟨h1, ψ, h2⟩ :=
    (dirichlet_character.comp (teichmuller_character_mod_p p^m) f).factors_through_conductor,
  rw nat.dvd_prime _ at h1,
  { cases h1,
    { rw h1_1,
      have := dirichlet_character.conductor_eq_one _ h1,
      exfalso,
      apply zero_ne_one this, },
    { assumption, }, },
  { apply fact.out, },
end-/

open_locale big_operators
local attribute [instance] zmod.topological_space

variables (p : ℕ) [fact (nat.prime p)] (d : ℕ) (R : Type*) [normed_comm_ring R] (m : ℕ)
(hd : d.gcd p = 1) (χ : dirichlet_character R (d*(p^m))) {c : ℕ} (hc : c.gcd p = 1)
(hc' : c.gcd d = 1) (na : ∀ (n : ℕ) (f : ℕ → R),
  ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
(w : weight_space (units (zmod d) × units ℤ_[p]) R)

/-- Similar to `pri_dir_char_extend`, except it takes as input a monoid_hom and returns a
  monoid_hom. -/
noncomputable abbreviation pri_dir_char_extend' : ((units (zmod d)) × (units ℤ_[p])) →* units R :=
monoid_hom.comp χ (monoid_hom.comp (monoid_hom.comp (units.map (zmod.chinese_remainder
(nat.coprime_pow_spl p d m hd)).symm.to_monoid_hom)
(mul_equiv.to_monoid_hom (mul_equiv.symm mul_equiv.prod_units)) ) -- units (zmod d) × units (zmod p^m) →* units (zmod d × zmod p^m) →* units zmod (d * p^m)
 (monoid_hom.prod_map (monoid_hom.id (units (zmod d))) (units.map (padic_int.to_zmod_pow m).to_monoid_hom ) ) ) -- units (zmod d) × units ℤ_[p] →* units (zmod d) × units (zmod p^m)

lemma pri_dir_char_extend'_continuous [fact (0 < d)] : continuous (pri_dir_char_extend' p d R m hd χ) :=
begin
  refine continuous.comp _ (continuous.comp (continuous.comp (continuous.comp _ _) _)
    (continuous_id)),
  { convert continuous_of_discrete_topology, exact disc_top_units (d * p ^ m), },
  { convert continuous_of_discrete_topology, exact units_prod_disc, },
  { convert continuous_of_discrete_topology,
    convert prod.discrete_topology,
    { exact disc_top_units _, },
    { convert disc_top_units _, apply fact_iff.2 _,
      convert mul_prime_pow_pos p 1 m, rw one_mul, }, },
  { simp only [monoid_hom.id_apply, ring_hom.to_monoid_hom_eq_coe, monoid_hom.coe_prod_map,
      prod_map],
    refine continuous_fst.prod_mk (continuous.comp _ continuous_snd),
    refine cont_units_map (cont_inv p) _ (padic_int.continuous_to_zmod_pow p m),
    convert continuous_of_discrete_topology,
    refine discrete_topology_induced (λ a b h, units.eq_iff.1 h), },
end

variables [semi_normed_algebra ℚ_[p] R] [fact (0 < m)]

/-- Returns ω⁻¹ = ω^(p - 2) : ℤ/(d * p^m)ℤ* →* R*. -/
noncomputable abbreviation teichmuller_character_mod_p_change_level : dirichlet_character R (d * p^m) :=
  dirichlet_character.change_level (((units.map ((algebra_map ℚ_[p] R).comp
  (padic_int.coe.ring_hom)).to_monoid_hom).comp (teichmuller_character_mod_p p) : dirichlet_character R p)^(p - 2) )
  (begin apply dvd_mul_of_dvd_right (dvd_pow_self p (ne_of_gt (fact.out _))), apply_instance, end)

/-noncomputable abbreviation weight_space_extend :=
  monoid_hom.comp (units.map w.to_monoid_hom)
    (mul_equiv.to_monoid_hom (mul_equiv.symm mul_equiv.prod_units))-/

lemma inv_prod_eq_prod_inv : (units.inv : units (zmod d × ℤ_[p]) → zmod d × ℤ_[p]) =
      (prod.map (units.inv : units (zmod d) → zmod d) (units.inv : units ℤ_[p] → ℤ_[p])) ∘
      mul_equiv.prod_units.to_fun :=
begin
  ext,
  { rw mul_equiv.prod_units,
    simp only [monoid_hom.coe_fst, monoid_hom.prod_apply, units.coe_map_inv,
      function.comp_app, units.inv_eq_coe_inv, prod.map_mk], },
  { rw mul_equiv.prod_units,
    simp only [monoid_hom.prod_apply, units.coe_map_inv, monoid_hom.coe_snd,
      function.comp_app, units.inv_eq_coe_inv, prod.map_mk], },
end

/-- Defines a homeomorphism between (α × β) × (γ × δ) and (α × γ) × (β × δ). -/
def homeomorph.prod_prod_comm (α β γ δ : Type*) [topological_space α] [topological_space β]
  [topological_space γ] [topological_space δ] : (α × β) × (γ × δ) ≃ₜ (α × γ) × (β × δ) :=
homeomorph.trans (homeomorph.prod_assoc _ _ _)
  (homeomorph.symm (homeomorph.trans (homeomorph.prod_assoc _ _ _)
  (homeomorph.prod_congr (homeomorph.refl α)
  (homeomorph.trans (homeomorph.prod_assoc _ _ _).symm (homeomorph.symm (homeomorph.trans
  (homeomorph.prod_assoc _ _ _).symm (homeomorph.trans (homeomorph.prod_comm _ _)
  (homeomorph.symm (homeomorph.trans (homeomorph.prod_comm _ _)
  (homeomorph.prod_congr (homeomorph.refl δ) (homeomorph.prod_comm _ _)))))))))))

/-- Defines a homeomorphism between α and αᵒᵖ. -/
def homeomorph.op {α : Type*} [topological_space α] : α ≃ₜ αᵒᵖ :=
begin
  refine homeomorph.homeomorph_of_continuous_open opposite.equiv_to_opposite continuous_op _,
  { change is_open_map opposite.op,
    apply is_open_map.of_inverse,
    { apply continuous_unop, },
    { tauto, },
    { tauto, }, },
end

/-- Defines a homeomorphism between (α × β) × (α × β)ᵒᵖ and (α × αᵒᵖ) × (β × βᵒᵖ). -/
def homeomorph.prod_op_comm {α β : Type*} [topological_space α] [topological_space β] :
 ((α × β) × (α × β)ᵒᵖ) ≃ₜ ((α × αᵒᵖ) × (β × βᵒᵖ)) :=
homeomorph.symm (homeomorph.trans (homeomorph.prod_prod_comm α β (αᵒᵖ) (βᵒᵖ)).symm
  (homeomorph.prod_congr (homeomorph.refl _) (homeomorph.symm
  (homeomorph.trans homeomorph.op.symm (homeomorph.prod_congr homeomorph.op homeomorph.op)))))

/- lemma mul_equiv.prod_units_is_open_map : is_open_map (@mul_equiv.prod_units (zmod d) ℤ_[p] _ _) :=
begin
  rintros s hs,
  rw is_open_induced_iff at hs,
  rcases hs with ⟨t, h1, h2⟩,
  set t' : set ((zmod d × (zmod d)ᵒᵖ) × (ℤ_[p] × ℤ_[p]ᵒᵖ)) := (homeomorph.prod_op_comm)'' t
    with ht',
  rw is_open_prod_iff, rintros a b h,
  rw ←(set.preimage_eq_iff_eq_image _) at ht',
  { rw ←ht' at h2,
/-    have image_s : (@mul_equiv.prod_units (zmod d) ℤ_[p] _ _)'' s =
      prod ((embed_product (zmod d))⁻¹' ((prod.fst)'' t')) ((embed_product (ℤ_[p]))⁻¹' ((prod.snd)'' t')),-/
    refine ⟨({a} : set (units (zmod d))), (embed_product (ℤ_[p]))⁻¹' ((prod.snd)'' t'),
      _, _, set.mem_singleton a, _, λ y hy, _⟩,
    { convert is_open_discrete _, exact disc_top_units d, },
    { refine is_open_induced_iff.mpr ⟨(prod.snd '' t'), _, rfl⟩,
      apply is_open_map_snd, exact homeomorph.prod_op_comm.is_open_image.mpr h1, },
    { rw ←h2 at h, rw set.mem_preimage, sorry, },
    { --simp at hy,
      simp only [set.mem_image],
      refine ⟨mul_equiv.prod_units.symm y, _, _⟩,
      { rw ←set.mem_preimage, rw mul_equiv.inv_fun_eq_symm,
        simp only [set.mem_preimage, set.mem_image, set.mem_singleton_iff, set.mem_prod,
          prod.exists] at hy, sorry, },
      { rw mul_equiv.apply_symm_apply, }, }, },
  { exact homeomorph.prod_op_comm.bijective, },
end

lemma mul_equiv.prod_units_embedding : embedding (@mul_equiv.prod_units (zmod d) ℤ_[p] _ _) :=
begin
  fconstructor,
  { fconstructor, ext,
    refine ⟨λ hx, _, λ hx, _⟩,
    { rw is_open_induced_iff',
      refine ⟨(@mul_equiv.prod_units (zmod d) ℤ_[p] _ _)'' x, _, _⟩,
      { apply mul_equiv.prod_units_is_open_map, exact hx, },
      { convert equiv.preimage_image (@mul_equiv.prod_units (zmod d) ℤ_[p] _ _).to_equiv _, }, },
    { rw is_open_induced_iff' at hx,
      refine is_open_implies_is_open_iff.mpr _ x _,

      sorry, }, },
  { exact mul_equiv.prod_units.injective, },
end

lemma continuous_prod_units : continuous (@mul_equiv.prod_units (zmod d) ℤ_[p] _ _) :=
begin
/-  rw mul_equiv.prod_units, simp,
  refine continuous_iff_le_induced.mpr _,
  intros s hs, rcases hs with ⟨t, h1, h2⟩,
  rw set.preimage_eq_iff_eq_image _ at h2,
  rw h2 at h1,
  rw is_open_prod_iff at h1,

  refine ⟨_, _⟩,-/
  rw mul_equiv.prod_units,
  simp only [mul_equiv.coe_mk],

  apply continuous.prod_mk,
  { simp only,
    fconstructor, rintros s hs,
    rw units.map, simp,
    apply cont_units_map,
    { fconstructor,
        rintros s hs, rw is_open_iff_forall_mem_open,
  rintros x hx,rw set.mem_preimage at hx,
  rw metric.is_open_iff at hs,

      rintros s hs,
      rw is_open_prod_iff at hs,
      refine is_open_induced_eq.mpr _, simp,
      refine ⟨_, _, _⟩,
      sorry,
      sorry,
      {  }, },
    { apply discrete_topology_induced, },
    sorry, },
end

lemma continuous_weight_space_extend : continuous (weight_space_extend p d R w) :=
begin
  refine continuous.comp (cont_units_map _ _ w.continuous_to_fun) _,
  { rw inv_prod_eq_prod_inv,
    apply continuous.comp _ _,
    swap, { continuity, },
    sorry, },
  { sorry, },
  { simp only [mul_equiv.coe_to_monoid_hom],
    sorry, },
end -/

/-noncomputable instance peace (p : ℕ) [fact (nat.prime p)] {R : Type*} [semi_normed_comm_ring R]
  [semi_normed_algebra ℚ_[p] R] [has_scalar ℚ R] [is_scalar_tower ℚ ℚ_[p] R] :
  semi_normed_algebra ℚ R :=
begin
  haveI : semi_normed_algebra ℚ ℚ_[p], sorry,
  haveI : algebra ℚ R,
  {
    refine ring_hom.to_algebra' (ring_hom.comp (algebra_map ℚ_[p] R) (algebra_map ℚ ℚ_[p]))
      (λ c x, _),
    simp only [function.comp_app, ring_hom.coe_comp], rw mul_comm, },
  fconstructor, intro x,
  rw ←norm_algebra_map_eq ℚ_[p] x,
  have := norm_algebra_map_eq R ((algebra_map ℚ ℚ_[p]) x),
  symmetry, convert this.symm,
  rw algebra_map,
  change ∥(algebra_map ℚ_[p] R) ((algebra_map ℚ ℚ_[p]) x)∥ = ∥x∥,
  sorry
end -/


/-- Given a natural number s, defines the monoid homomorphism <a>^s taking a ∈ ℤ/dℤ* × ℤₚ* to
  (a * ω⁻¹ (a.2 (mod p)))^(-s) in R. -/
noncomputable abbreviation neg_pow'_to_hom (s : ℕ) :
  monoid_hom (units (zmod d) × units ℤ_[p]) R :=
  ((algebra_map ℚ_[p] R).to_monoid_hom).comp ((
    (@padic_int.coe.ring_hom p _).to_monoid_hom).comp ((units.coe_hom ℤ_[p]).comp
    (gpow_group_hom (-s) ((monoid_hom.snd (units (zmod d)) (units ℤ_[p])) * (monoid_hom.comp
    (monoid_hom.comp ((teichmuller_character_mod_p p)^(p - 2))
    (units.map padic_int.to_zmod.to_monoid_hom))
    (monoid_hom.snd (units (zmod d)) (units ℤ_[p]))) ))) )
/-{
  to_fun := λ x, (units.map (algebra_map ℚ_[p] R).to_monoid_hom) (units.map
    (@padic_int.coe.ring_hom p _).to_monoid_hom (gpow_group_hom (-s) (monoid_hom.snd (units (zmod d)) (units ℤ_[p]) x))),
    --(units.map ((@padic_int.coe.ring_hom p _).to_monoid_hom _)),
  map_one' := by simp only [one_inv, one_gpow, prod.snd_one, monoid_hom.map_one],
  map_mul' := begin rw pow_monoid_hom, end,
}-/
-- to figure out : is ℤ/dℤ* × ℤ_[p] → ℤ_[p] with projection onto the 2nd coord the same as
-- going down to ℤ/dp^n ℤ and using CRT and then going mod p^n?

--instance : topological_group (units R) := units.topological_group

--instance : metric_space (units ℤ_[p]) := infer_instance

lemma padic_int.continuous_units_gpow (s : ℤ) : continuous (gpow s : units ℤ_[p] → units ℤ_[p]) :=
begin
  suffices : continuous ((units.coe_hom ℤ_[p]) ∘ (gpow s)),
  { fconstructor, rintros t ht,
    rw continuous_def at this,
    specialize this ((units.coe_hom ℤ_[p])'' t) (is_open_coe p t ht),
    rw [set.preimage_comp, set.preimage_image_eq _] at this,
    { assumption, },
    { convert units.ext, }, }, -- if composition of a map with an open inj map is cont, then map is cont
  { cases s,
    { change continuous (λ x, ((x^s : units ℤ_[p]) : ℤ_[p])),
      simp only [units.coe_pow],
      continuity, apply units.continuous_coe, },
    { change continuous (λ x, ((x^(-[1+ s]) : units ℤ_[p]) : ℤ_[p])),
      simp only [gpow_neg_succ_of_nat],
      conv { congr, funext, rw ←units.inv_eq_coe_inv, },
      refine continuous.comp _ (continuous_pow s.succ),
      change continuous (units.val ∘ units.has_inv.inv),
      refine continuous.comp _ continuous_id'.inv, change continuous coe,
      apply units.continuous_coe, }, },
end
-- this can be generalized to whenever inv is continuous?

lemma neg_pow'_continuous (s : ℕ) : continuous (neg_pow'_to_hom p d R s) :=
begin
  refine continuous.comp _ _,
  { simp only [ring_hom.coe_monoid_hom, ring_hom.to_monoid_hom_eq_coe],
    rw algebra.algebra_map_eq_smul_one',
    exact continuous_id'.smul continuous_const, },
  { refine continuous.comp (continuous_induced_dom.comp (continuous.comp
      (continuous.comp units.continuous_coe (continuous.comp (continuous.comp
      (padic_int.continuous_units_gpow p _)
      (continuous.comp (continuous.mul continuous_snd
      (continuous.comp (continuous.comp (continuous.comp _
      (cont_units_map (cont_inv p) _ (continuous_to_zmod p)))
      continuous_snd) continuous_id)) continuous_id))
      continuous_id)) continuous_id))
      continuous_id,
    { convert continuous_of_discrete_topology, exact disc_top_units _, },
    { convert continuous_of_discrete_topology,
      refine discrete_topology_induced units.ext, }, },
end
-- why can't i use the dot notation?
-- maybe make a separate lemma saying any Dir char is cont?

/-- The element of weight space corresponding to neg_pow'_to_hom. -/
noncomputable abbreviation neg_pow' (s : ℕ) :
  weight_space (units (zmod d) × units ℤ_[p]) R :=
⟨(neg_pow'_to_hom p d R s).to_fun, (neg_pow'_to_hom p d R s).map_one', (neg_pow'_to_hom p d R s).map_mul',
  neg_pow'_continuous p d R s⟩

variable [fact (0 < d)]

theorem cont_paLf' : continuous
((units.coe_hom R).comp (pri_dir_char_extend' p d R m hd (χ *
  (teichmuller_character_mod_p_change_level p d R m))) * w.to_monoid_hom) :=
  continuous.mul (units.continuous_coe.comp (pri_dir_char_extend'_continuous p d R m hd _))
  w.continuous_to_fun
  /- continuous.comp units.continuous_coe (continuous.mul
    (pri_dir_char_extend'_continuous p d R m hd _)
    w.continuous_to_fun) -/
--why is this taking so long / not anymore haha
-- we chose target as R instead of units R so did we did not have to show continuity of
-- units.map _ (recall that showing inv is continuous is hard for R without extra assumptions)

/-continuous ((pri_dir_char_extend' p d R m hd
    (χ * (dirichlet_character.change_level
      ( ( (units.map ((algebra_map ℚ_[p] R).comp
      (padic_int.coe.ring_hom)).to_monoid_hom).comp (teichmuller_character_mod_p p) )^(p - 2))
      (begin sorry end) )) ) * w).to_fun := sorry -/

/- theorem cont_paLf' (p : ℕ) [fact (nat.prime p)] (d : ℕ) [fact (0 < d)] (hd : d.gcd p = 1)
(R : Type*) [normed_comm_ring R] [complete_space R] [char_zero R] [semi_normed_algebra ℚ_[p] R]
(m : ℕ) [fact (0 < m)]
(χ : dirichlet_character R (d * p ^ m)) --(hcond : χ.is_primitive)
(w : weight_space (units (zmod d) × units ℤ_[p]) R) :
continuous ((pri_dir_char_extend' p d R m hd
    (χ * (dirichlet_character.change_level
      ( ( (units.map ((algebra_map ℚ_[p] R).comp
      (padic_int.coe.ring_hom)).to_monoid_hom).comp (teichmuller_character_mod_p p) )^(p - 2))
      (begin sorry end) )) ) * w).to_fun := sorry -/

variables [complete_space R] [char_zero R]

/-- The p-adic L- function, as defined in Thm 12.2, absorbing the (1 - χ(c)<c>^(-n)) term
  (since it appears as it is in the Iwasawa Main Conjecture). -/
noncomputable def p_adic_L_function' [semi_normed_algebra ℚ R] : R :=
    (measure.integral (bernoulli_measure' p d R hc hc' hd na)
      ⟨(units.coe_hom R).comp (pri_dir_char_extend' p d R m hd (χ *
  (teichmuller_character_mod_p_change_level p d R m))) * w.to_monoid_hom,
       cont_paLf' p d R m hd χ w⟩)
-- technically bernoulli_measure lands in units R, you should not have to use (units.coe_hom R),
-- unless (units R) is not a complete space?

lemma is_unit_iff_not_dvd (z : ℕ) (h : ¬ p ∣ z) : is_unit (z : ℤ_[p]) :=
begin
  contrapose h, rw not_not,
  have := padic_int.mem_nonunits.1 h,
  rw ←int.coe_nat_dvd,
  rw ←padic_int.norm_int_lt_one_iff_dvd,
  convert this using 1,
end

theorem p_adic_L_function_eval_neg_int [semi_normed_algebra ℚ R] (n : ℕ) :
  (n : R) * (p_adic_L_function' p d R m hd χ hc hc' na (neg_pow' p d R (n - 1))) =
  -(1 - (χ (zmod.unit_of_coprime c (nat.coprime_mul_iff_right.2 ⟨hc', nat.coprime_pow_spl p c m hc⟩))
  * (neg_pow' p d R n (zmod.unit_of_coprime c hc', is_unit.unit ((is_unit_iff_not_dvd p c)
  ((nat.prime.coprime_iff_not_dvd (fact.out _)).1 (nat.coprime.symm hc))
    )) ))) * (1 - ((asso_dirichlet_character (dirichlet_character.mul χ
    ((teichmuller_character_mod_p_change_level p d R m)^n))) p * p^(n - 1)) ) *
  (general_bernoulli_number (dirichlet_character.mul χ
    ((teichmuller_character_mod_p_change_level p d R m)^n)) n) :=
begin
  sorry
end
-- don't really need to change level to d*p^m for ω, right?
