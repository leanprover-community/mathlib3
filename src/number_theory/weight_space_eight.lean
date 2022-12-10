/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import number_theory.weight_space_seven

/-!
# Bernoulli measure and the p-adic L-function

This file defines the Bernoulli distribution on `zmod d × ℤ_[p]`. One of the main theorems is that
this p-adic distribution is indeed a p-adic measure. As a consequence, we are also able to define
the p-adic L-function in terms of a p-adic integral.

## Main definitions
 * `bernoulli_measure_of_measure`
 * `p_adic_L_function`

## Implementation notes
TODO (optional)

## References
Introduction to Cyclotomic Fields, Washington (Chapter 12, Section 2)

## Tags
p-adic, L-function, Bernoulli measure
-/

local attribute [instance] zmod.topological_space

variables (X : Type*) [mul_one_class X] [topological_space X]
variables (A : Type*) [topological_space A] [mul_one_class A] (p : ℕ) [fact p.prime] (d : ℕ)
variables (R : Type*) [normed_comm_ring R] [complete_space R] [char_zero R] (inj : ℤ_[p] → R) (m : ℕ)
  (χ : mul_hom (units (zmod (d*(p^m)))) R) (w : weight_space (units (zmod d) × units (ℤ_[p])) R)
variables {c : ℕ} [fact (0 < d)]
variables [algebra ℚ R] [normed_algebra ℚ_[p] R] [norm_one_class R]

set_option old_structure_cmd true

open_locale big_operators

open padic_int zmod nat locally_constant
open_locale pointwise -- needed for has_add (set ℤ_[p])

lemma preimage_to_zmod (x : zmod (p)) : (@to_zmod p _) ⁻¹' {x} =
 {(x : ℤ_[p])} + (((@to_zmod p _).ker : ideal ℤ_[p]) : set ℤ_[p]) :=
begin
 ext y,
    simp only [set.image_add_left, set.mem_preimage, set.singleton_add,
      set.mem_singleton_iff, set_like.mem_coe],
    split,
    { intro h, rw ring_hom.mem_ker, simp [h], },
    { intro h, rw ring_hom.mem_ker at h, simp at *, rw neg_add_eq_zero at h, exact h.symm, },
end

lemma continuous_to_zmod : continuous (@padic_int.to_zmod p _) :=
begin
  refine topological_space.is_topological_basis.continuous discrete_topology.is_topological_basis _ _,
  rintros s hs, simp only [set.mem_range] at hs, cases hs with x hx,
  change {x} = s at hx, rw ←hx,
  rw [preimage_to_zmod, ker_to_zmod],
  refine is_open.add_left _, convert is_open_span p 1,
  rw pow_one, rw maximal_ideal_eq_span_p,
end

lemma units_prod_disc {m n : ℕ} : discrete_topology (units (zmod m × zmod n)) :=
begin
  apply @discrete_topology_induced _ _ _ _ _ _,
  { apply @prod.discrete_topology _ _ _ _ _ _,
    { exact prod.discrete_topology, },
    { apply @discrete_topology_induced _ _ _ _ _ _,
      { exact prod.discrete_topology, },
      { exact mul_opposite.unop_injective, }, }, },
  { rintros x y h,
    rw units.embed_product at h,
    simp only [prod.mk.inj_iff, opposite.op_inj_iff, monoid_hom.coe_mk] at h,
    rw units.ext_iff,
    rw h.1, },
end

lemma cont_units_map {α β : Type*} [topological_space α] [monoid α] [topological_space β] [monoid β]
  (ha : @continuous _ _ (topological_space.induced (units.coe_hom α) infer_instance)
      infer_instance (@units.inv α _))
  (hb : @continuous _ _ (topological_space.induced (units.coe_hom β) infer_instance)
      infer_instance (@units.inv β _))
  {f : α →* β} (hf : continuous f) : continuous (units.map f) :=
begin
  constructor,
  rintros s hs,
  rw (top_eq_iff_cont_inv.2 _).symm,
  { rw (top_eq_iff_cont_inv.2 _).symm at hs,
    { rw is_open_induced_iff at hs,
      rcases hs with ⟨t, ht, hs⟩, rw ←hs,
      convert_to is_open ((units.coe_hom α)⁻¹' (f⁻¹' t)),
      { rw top_eq_iff_cont_inv, apply ha, },
      { rw ←set.preimage_comp,
        apply continuous.is_open_preimage _ t ht,
        apply continuous.comp,
        { apply hf, },
        { apply units.continuous_coe, }, }, },
    apply hb, },
  apply ha,
end

example {α β : Type*} [topological_space α] [topological_space β] [monoid α] [monoid β]
  (f g : α →* β) (hf : continuous f) (hg : continuous g) : continuous (f.prod_map g) :=
by { --simp,
refine continuous.prod_map hf hg, }

lemma cont_paLf [fact (0 < m)] (h : d.gcd p = 1) (cont : continuous inj) :
  continuous (λ (a : (units (zmod d) × units ℤ_[p])), ((pri_dir_char_extend p d R m h χ) a) *
  (inj (teichmuller_character p (a.snd)))^(p - 2) * (w.to_fun a : R)) :=
begin
  continuity,
  { --rw pri_dir_char_extend,
    apply continuous.comp,
    { apply continuous.comp,
      { convert continuous_of_discrete_topology,
        apply @disc_top_units _ _,
        apply fact_iff.2, apply mul_prime_pow_pos, },
      { apply continuous.comp _ continuous_id,
        apply continuous.comp,
        { convert continuous_of_discrete_topology, apply units_prod_disc, },
        { apply continuous.comp _ continuous_id,
          apply continuous.comp,
          { convert continuous_of_discrete_topology,
            apply @prod.discrete_topology _ _ _ _ _ _,
            { exact disc_top_units d, },
            { apply @disc_top_units _ _,
              apply fact_iff.2, apply pow_pos _ _,
              apply nat.prime.pos, apply fact.out, }, },
          { apply continuous.comp _ continuous_id,
            rw monoid_hom.to_mul_hom_coe,
            simp,
            refine continuous.prod_map _ _,
--           apply continuous.prod_mk,
            { convert continuous_id, },
              -- apply continuous.comp _ continuous_id,
              -- apply continuous.comp,
              -- { convert continuous_id, },
              -- { convert continuous_fst, }, },
            { --apply continuous.comp _ continuous_id,
              --apply continuous.comp,
              { apply cont_units_map,
                { apply cont_inv, },
                { apply @continuous_of_discrete_topology _ _ _ _ _,
                  apply discrete_topology_induced,
                  rintros x y hxy, rw units.ext_iff, convert hxy, },
                  --refine @disc_top_units (p^m) (fact_iff.2 (pow_pos (nat.prime.pos (fact_iff.1 _)) m)), },
                { change continuous ((to_zmod_pow m)),
                  apply continuous_to_zmod_pow, }, }, }, }, }, }, },
              -- { apply continuous.comp _ continuous_id,
              --   convert continuous_snd, }, }, }, }, }, },
    { apply continuous_id, }, },
  { --rw teichmuller_character,
    simp only [monoid_hom.coe_mk],
    --convert continuous.comp (continuous_pow (p - 2)) _,
    --{ apply_instance, },
    { --apply continuous.comp cont,
      conv { congr, funext, rw ←function.comp_apply (witt_vector.equiv p) _, },
      apply continuous.comp,
      { exact continuous_bot, },
      { apply continuous.comp (continuous_to_zmod p),
        { apply continuous.comp,
          { exact units.continuous_coe, },
          { exact continuous_id, }, }, }, }, },
{ change continuous w,
  apply (weight_space.to_continuous_map w).continuous_to_fun, },
end

--lemma is_unit_mul_pow (hc : c.gcd p = 1) (hc' : c.gcd d = 1) : is_unit (c : zmod (d * p^m)) := sorry

example {α β : Type*} [mul_one_class α] [mul_one_class β] (h : α ≃* β) : α →* β := by refine mul_equiv.to_monoid_hom h

lemma is_unit_padic_of_is_unit_zmod {x : ℕ} (hx : is_unit (x : zmod p)) (h : x.coprime p) :
  is_unit (x : ℤ_[p]) :=
begin
  contrapose h,
  rw is_unit_iff at h,
  have hx' := lt_of_le_of_ne (norm_le_one _) h,
  change ∥((x : ℤ) : ℤ_[p])∥ < 1 at hx',
  rw norm_int_lt_one_iff_dvd at hx',
  norm_cast at hx',
  rw nat.coprime_comm,
  rw nat.prime.coprime_iff_not_dvd _,
  { rw not_not, assumption, },
  { apply fact.out, },
end

/-- Constant used in `p_adic_L_function`. -/
noncomputable def f' (hd : d.gcd p = 1) [fact (0 < m)] (hc : c.gcd p = 1) (hc' : c.gcd d = 1)
 (χ : mul_hom (units (zmod (d*(p^m)))) R) (w : weight_space (units (zmod d) × units ℤ_[p]) R) : R := -- why is χ not getting recognized
begin
    --convert is_unit.map (monoid_hom.comp ((((witt_vector.equiv p).to_mul_equiv)).to_monoid_hom)
      --(witt_vector.teichmuller p)) _,
    have f2 : is_unit (c : ℤ_[p]),
    { apply is_unit_padic_of_is_unit_zmod, rw ←zmod.coe_unit_of_coprime _ hc,
      apply units.is_unit, rw nat.coprime_iff_gcd_eq_one, apply hc, },
  set c' := (zmod.unit_of_coprime c hc', is_unit.unit f2) with hc',
  refine ((((pri_dir_char_extend p d R m hd χ) c') * (w.to_fun c') - 1)),
end
--  -((1 - ((pri_dir_char_extend p d R m hd χ) c) * (w.to_fun c)))⁻¹

noncomputable def f (hd : d.gcd p = 1) [fact (0 < m)] (hc : c.gcd p = 1) (hc' : c.gcd d = 1)
  (hu : is_unit (f' p d R m hd hc hc' χ w)) : R :=
  units.inv (is_unit.unit hu)

--h wont go in the system if you put it in [], is this independent of c? is it accurate to say that ω⁻¹ = ω^(p - 2)? I think so
/-- The `p_adic_L_function` defined in terms of the p-adic integral and the
  Bernoulli measure `E_c`. -/
noncomputable def p_adic_L_function (hd : d.gcd p = 1) [fact (0 < m)] (h : function.injective inj)
  (cont : continuous inj) (hc : c.gcd p = 1) (hc' : c.gcd d = 1) (na : ∀ (n : ℕ) (f : ℕ → R),
     ∥∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥) (hu : is_unit (f' p d R m hd hc hc' χ w)) :=
 (f p d R m χ w hd hc hc' hu) * (measure.integral (bernoulli_measure' p d R hc hc' hd na)
⟨(λ (a : (units (zmod d) × units ℤ_[p])), ((pri_dir_char_extend p d R m hd χ) a) *
  (inj (teichmuller_character p a.snd))^(p - 2) * (w.to_fun a : R)), cont_paLf p d R inj m χ w hd cont⟩)
--independent of c, remove that!
-- make R a ℚ_[p]-algebra or a ℚ-algebra?
-- make χ and s explicit
