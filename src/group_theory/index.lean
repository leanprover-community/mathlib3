/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import group_theory.coset
import set_theory.cardinal

/-!
# Index of a Subgroup

In this file we define the index of a subgroup, and prove several divisibility properties.

## Main definitions

- `H.index` : the index of `H : subgroup G`

# Main results

- `index_mul_card` : `H.index * fintype.card H = fintype.card G`
- `index_dvd_card` : `H.index ∣ fintype.card G`
- `index_eq_mul_of_le` : If `H ≤ K`, then `H.index = K.index * (H.subgroup_of K).index`
- `index_dvd_of_le` : If `H ≤ K`, then `K.index ∣ H.index`

-/

namespace subgroup

variables {G : Type*} [group G] (H : subgroup G)

/-- The index of a subgroup as a natural number -/
noncomputable def index : ℕ :=
(cardinal.mk (quotient_group.quotient H)).to_nat

lemma index_eq_card [fintype (quotient_group.quotient H)] :
  H.index = fintype.card (quotient_group.quotient H) :=
cardinal.mk_to_nat_eq_card

lemma index_mul_card [fintype G] [fintype H] :
  H.index * fintype.card H = fintype.card G :=
begin
  classical,
  rw H.index_eq_card,
  convert H.card_eq_card_quotient_mul_card_subgroup.symm,
end

lemma index_dvd_card [fintype G] : H.index ∣ fintype.card G :=
begin
  classical,
  rw H.index_eq_card,
  convert H.card_quotient_dvd_card,
end

variables {H} {K : subgroup G}

/-- If `H ≤ K` then `G/H ≃ G/K × K/H` -/
@[simps] def quotient_equiv_prod_of_le' (h_le : H ≤ K) (f : quotient_group.quotient K → G)
  (hf : function.right_inverse f quotient_group.mk) :
  quotient_group.quotient H ≃
  quotient_group.quotient K × quotient_group.quotient (H.subgroup_of K) :=
{ to_fun := λ a, ⟨a.map' id (by exact λ b c h, h_le h),
    a.map' (λ g : G, ⟨(f (quotient.mk' g))⁻¹ * g, quotient.exact' (hf g)⟩) (λ b c h, by
    { change ((f b)⁻¹ * b)⁻¹ * ((f c)⁻¹ * c) ∈ H,
      have key : f b = f c := congr_arg f (quotient.sound' (h_le h)),
      rwa [key, mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] })⟩,
  inv_fun := λ a, a.2.map' (λ b, f a.1 * b) (λ b c h, by
  { change (f a.1 * b)⁻¹ * (f a.1 * c) ∈ H,
    rwa [mul_inv_rev, mul_assoc, inv_mul_cancel_left] }),
  left_inv := by
  { refine quotient.ind' (λ a, _),
    simp_rw [quotient.map'_mk', id.def, K.coe_mk, mul_inv_cancel_left] },
  right_inv := by
  { refine prod.rec _,
    refine quotient.ind' (λ a, _),
    refine quotient.ind' (λ b, _),
    have key : quotient.mk' (f (quotient.mk' a) * b) = quotient.mk' a :=
    (quotient_group.mk_mul_of_mem (f a) ↑b b.2).trans (hf a),
    simp_rw [quotient.map'_mk', id.def, key, inv_mul_cancel_left, subtype.coe_eta] } }

/-- If `H ≤ K` then `G/H ≃ G/K × K/H` -/
@[simps] noncomputable def quotient_equiv_prod_of_le (h_le : H ≤ K) : quotient_group.quotient H ≃
  quotient_group.quotient K × quotient_group.quotient (H.subgroup_of K) :=
quotient_equiv_prod_of_le' h_le quotient.out' quotient.out_eq'

lemma index_eq_mul_of_le (h_le : H ≤ K) : H.index = K.index * (H.subgroup_of K).index :=
(congr_arg cardinal.to_nat (by exact cardinal.eq_congr (quotient_equiv_prod_of_le h_le))).trans
  (cardinal.to_nat_mul _ _)

lemma index_dvd_of_le (h_le : H ≤ K) : K.index ∣ H.index :=
⟨(H.subgroup_of K).index, index_eq_mul_of_le h_le⟩

end subgroup
