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

- `H.index` : the index of `H : subgroup G` as a natural number,
  and returns 0 if the index is infinite.

# Main results

- `index_mul_card` : `H.index * fintype.card H = fintype.card G`
- `index_dvd_card` : `H.index ∣ fintype.card G`
- `index_eq_mul_of_le` : If `H ≤ K`, then `H.index = K.index * (H.subgroup_of K).index`
- `index_dvd_of_le` : If `H ≤ K`, then `K.index ∣ H.index`

-/

namespace subgroup

variables {G : Type*} [group G] (H : subgroup G)

/-- The index of a subgroup as a natural number, and returns 0 if the index is infinite. -/
@[to_additive "The index of a subgroup as a natural number,
and returns 0 if the index is infinite."]
noncomputable def index : ℕ :=
(cardinal.mk (quotient_group.quotient H)).to_nat

@[to_additive] lemma index_comap_of_surjective {G' : Type*} [group G'] {f : G' →* G}
  (hf : function.surjective f) : (H.comap f).index = H.index :=
begin
  letI := quotient_group.left_rel H,
  letI := quotient_group.left_rel (H.comap f),
  have key : ∀ x y : G', setoid.r x y ↔ setoid.r (f x) (f y) :=
  λ x y, iff_of_eq (congr_arg (∈ H) (by rw [f.map_mul, f.map_inv])),
  refine cardinal.to_nat_congr (equiv.of_bijective (quotient.map' f (λ x y, (key x y).mp)) ⟨_, _⟩),
  { simp_rw [←quotient.eq'] at key,
    refine quotient.ind' (λ x, _),
    refine quotient.ind' (λ y, _),
    exact (key x y).mpr },
  { refine quotient.ind' (λ x, _),
    obtain ⟨y, hy⟩ := hf x,
    exact ⟨y, (quotient.map'_mk' f _ y).trans (congr_arg quotient.mk' hy)⟩ },
end

@[to_additive] lemma index_eq_card [fintype (quotient_group.quotient H)] :
  H.index = fintype.card (quotient_group.quotient H) :=
cardinal.mk_to_nat_eq_card

@[to_additive] lemma index_mul_card [fintype G] [hH : fintype H] :
  H.index * fintype.card H = fintype.card G :=
begin
  classical,
  rw H.index_eq_card,
  apply H.card_eq_card_quotient_mul_card_subgroup.symm,
end

@[to_additive] lemma index_dvd_card [fintype G] : H.index ∣ fintype.card G :=
begin
  classical,
  exact ⟨fintype.card H, H.index_mul_card.symm⟩,
end

variables {H} {K : subgroup G}

@[to_additive] lemma index_eq_mul_of_le (h : H ≤ K) :
  H.index = K.index * (H.subgroup_of K).index :=
(congr_arg cardinal.to_nat (by exact (quotient_equiv_prod_of_le h).cardinal_eq)).trans
  (cardinal.to_nat_mul _ _)

@[to_additive] lemma index_dvd_of_le (h : H ≤ K) : K.index ∣ H.index :=
⟨(H.subgroup_of K).index, index_eq_mul_of_le h⟩

end subgroup
