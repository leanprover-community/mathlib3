/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import group_theory.quotient_group
import group_theory.abelianization

variables {G : Type*} [group G]

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
    intros x hx, rw set.mem_set_of_eq at hx,
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
    simp only [set.mem_set_of_eq],
    use x, use y },
end

/--  N a normal subgroup.
If there exists a commutative subgroup H, such that H ⊔ N = ⊤,
then N contains the derived subgroup.
-/
lemma contains_commutators_of (N : subgroup G) (nN : N.normal)
    (H : subgroup G) (hHN : N ⊔ H = ⊤) (hH: subgroup.is_commutative H) :
    commutator G ≤ N :=
begin
 -- let Q := quotient_group.quotient N,

  -- Q is a quotient of H
    let φ : H →* G ⧸ N := monoid_hom.comp (quotient_group.mk' N) (subgroup.subtype H),

    have hφ : function.surjective φ,

    -- On prouve que l'image de φ est égale à ⊤
    apply monoid_hom.range_top_iff_surjective.mp,
    let R := monoid_hom.range φ,
/-  j : H → G, p : G → G/N,  φ = p o j, on veut prouver que φ est surjective.
    R = im(φ), S = p⁻¹(R) ⊆ G -/

    /- Il va suffire de prouver que S = ⊤, car p est surjective -/
    let S := subgroup.comap (quotient_group.mk' N) R,
    have S_top : S = ⊤,
    {
      -- S contient N
      have lN : N ≤ S,
      { intros g hg,
        apply subgroup.mem_comap.2,
        have : (quotient_group.mk' N) g = 1,
        by simp only [hg, quotient_group.mk'_apply, quotient_group.eq_one_iff],
        rw this, exact R.one_mem', },

      -- S contient H = j(H)
      have lH : H ≤ S,
      { intros h hh,
        apply subgroup.mem_comap.2,
        apply set.mem_range.2, use h, exact hh,
        simp only [subgroup.coe_subtype, function.comp_app,
          monoid_hom.coe_comp, subgroup.coe_mk], },

      -- donc S = ⊤ puisque hHN : N ⊔ H = ⊤
      apply eq_top_iff.2,
      rw ← hHN,
      exact sup_le_iff.2 ⟨lN, lH⟩, },

    -- Ceci fait, il reste à prouver que R = ⊤
    { apply eq_top_iff.2,
      intros x _ ,
      let y := quotient.out' x,
      have hy : y ∈ S,
      { rw S_top, exact subgroup.mem_top y, },
      rw ← quotient_group.out_eq' x,
      exact subgroup.mem_comap.1 hy,
    },

  -- Q is commutative as a surjective image of H
  have hc : is_commutative (G ⧸ N) (*) :=
    surj_to_comm (monoid_hom.to_mul_hom φ) hφ hH.is_comm,

  -- Deduce that commutator G ≤ N
  exact (quotient_comm_contains_commutators_iff nN).1 hc,
end


#lint
