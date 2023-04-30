/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import group_theory.quotient_group
import group_theory.abelianization

variables {G : Type*} [group G]


open subgroup

lemma mem_commutator_set_of_is_conj_sq {G : Type*} [group G] {g : G} (hg : is_conj g (g ^ 2)) : g ∈ commutator_set G :=
begin
    obtain ⟨h, hg⟩ := hg, rw semiconj_by at hg,
    use ↑h, use g,
    rw [commutator_element_def, hg],
    simp only [is_unit.mul_inv_cancel_right, units.is_unit, mul_inv_eq_iff_eq_mul, pow_two],
end

lemma subgroup.map_top_eq_range {G H : Type*} [group H] [group G] (f : H →* G) :
  subgroup.map f ⊤ = f.range :=
begin
  suffices : (map f ⊤ : set G) = (f.range : set G),
  refine set_like.ext' this,
  simp only [coe_map, coe_top, set.image_univ, monoid_hom.coe_range],
end

lemma subgroup.map_commutator_eq {G H : Type*} [group H] [group G] (f : H →* G) :
  subgroup.map f (commutator H) = ⁅f.range, f.range⁆ :=
by rw [commutator_def H, subgroup.map_commutator, subgroup.map_top_eq_range]

lemma subgroup.commutator_eq' {G : Type*} [group G] (H : subgroup G) :
  subgroup.map H.subtype (commutator H) = ⁅H, H⁆ :=
by rw [subgroup.map_commutator_eq, subgroup.subtype_range]

/-- If G and H have multiplications *
and φ : G → H is a surjective multiplicative map,
and if G is commutative, then H is commutative.

Since I only use it with groups,
I should probably use function.surjective.comm_semigroup
--/
lemma surj_to_comm {G H : Type*} [has_mul G] [has_mul H] (φ: mul_hom G H)
   (is_surj : function.surjective φ) (is_comm : is_commutative G (*)) :
    is_commutative H (*) :=
begin
  apply is_commutative.mk,
  intros a b,
    obtain ⟨a', ha'⟩ := is_surj a, obtain ⟨b', hb'⟩ := is_surj b,
    rw ← ha', rw ← hb',
    let z := ⇑φ, let z₂ := φ.to_fun, have : z = z₂  , by refl,
    rw ← mul_hom.map_mul φ a' b',
    rw ← mul_hom.map_mul φ b' a',
    apply φ.congr_arg,
    refine is_commutative.cases_on is_comm _, intro,
    exact comm a' b',
end

theorem  quotient_comm_contains_commutators_iff {N : subgroup G} (nN : N.normal) :
  is_commutative (G ⧸ N) (*) -- (∀ (a b : G ⧸ N), a * b = b * a)
   ↔ commutator G ≤ N :=
begin
  resetI,
  split,
  { intro hcomm,
    rw commutator_eq_normal_closure,
    rw ← subgroup.normal_closure_subset_iff,
    intros x hx,
    obtain ⟨p, q, rfl⟩ := hx,
    simp only [set_like.mem_coe],
    rw ← quotient_group.eq_one_iff,
    rw commutator_element_def,
    simp only [quotient_group.coe_mul, quotient_group.coe_inv],
    rw ← commutator_element_def,
    rw commutator_element_eq_one_iff_mul_comm,
    apply hcomm.comm },
  { intro hGN, refine is_commutative.mk _,
    intro x', obtain ⟨x, rfl⟩ := quotient_group.mk'_surjective N x',
    intro y', obtain ⟨y, rfl⟩ := quotient_group.mk'_surjective N y',
    rw [← commutator_element_eq_one_iff_mul_comm, ← map_commutator_element],
    simp only [quotient_group.mk'_apply],
    rw quotient_group.eq_one_iff ,
    apply hGN,
    rw commutator_eq_closure,
    apply subgroup.subset_closure ,
    exact commutator_mem_commutator_set x y, },
end

/-- If N is a normal subgroup, H a commutative subgroup such that H ⊔ N = ⊤,
then N contains the derived subgroup. -/
lemma contains_commutators_of (N : subgroup G) (nN : N.normal)
    (H : subgroup G) (hHN : N ⊔ H = ⊤) (hH: subgroup.is_commutative H) :
    commutator G ≤ N :=
begin
  -- Il suffit de prouver que Q = G ⧸ N est commutatif
  -- let Q := quotient_group.quotient N,
  rw ← quotient_comm_contains_commutators_iff nN,

  -- Q is a quotient of H
  let φ : H →* G ⧸ N := monoid_hom.comp (quotient_group.mk' N) (subgroup.subtype H),
  -- Il suffit de prouver que φ est surjective
  refine surj_to_comm φ.to_mul_hom _ hH.is_comm,
  suffices hφ : function.surjective φ, exact hφ,

  -- On prouve que l'image de φ est égale à ⊤
  rw ← monoid_hom.range_top_iff_surjective,
  -- let R := monoid_hom.range φ,
  /-  j : H → G, p : G → G/N,  φ = p o j, on veut prouver que φ est surjective.
    R = im(φ), S = p⁻¹(R) ⊆ G -/

  /- Il va suffire de prouver que S = ⊤, car p est surjective -/
  -- let S := φ.range.comap (quotient_group.mk' N),
  suffices S_top : φ.range.comap (quotient_group.mk' N) = ⊤,
  { rw eq_top_iff,
    intros x _ ,
    let y := quotient.out' x,
    have hy : y ∈ φ.range.comap (quotient_group.mk' N),
    { rw S_top, exact subgroup.mem_top y, },
    rw ← quotient_group.out_eq' x,
    exact subgroup.mem_comap.mp hy, },

  rw [eq_top_iff,← hHN, sup_le_iff],
  split,

  -- have lN : N ≤ φ.range.comap (quotient_group.mk' N),
  { intros g hg,
    rw subgroup.mem_comap,
    suffices : quotient_group.mk' N g = 1,
    simp only [this, (monoid_hom.range φ).one_mem],
    simp only [hg, quotient_group.mk'_apply, quotient_group.eq_one_iff], },

  -- S contient H = j(H)
  -- have lH : H ≤ φ.range.comap (quotient_group.mk' N),
  { intros h hh,
    simp only [subgroup.mem_comap, monoid_hom.mem_range, monoid_hom.coe_comp, quotient_group.coe_mk', subgroup.coe_subtype, function.comp_app],
    use h, exact hh,
    simp only [subgroup.coe_mk], },
end


#lint
