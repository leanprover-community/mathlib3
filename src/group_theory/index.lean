/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import group_theory.quotient_group
import set_theory.fincard

/-!
# Index of a Subgroup

In this file we define the index of a subgroup, and prove several divisibility properties.

## Main definitions

- `H.index` : the index of `H : subgroup G` as a natural number,
  and returns 0 if the index is infinite.
- `H.relindex K` : the relative index of `H : subgroup G` in `K : subgroup G` as a natural number,
  and returns 0 if the relative index is infinite.

# Main results

- `index_mul_card` : `H.index * fintype.card H = fintype.card G`
- `index_dvd_card` : `H.index ∣ fintype.card G`
- `index_eq_mul_of_le` : If `H ≤ K`, then `H.index = K.index * (H.subgroup_of K).index`
- `index_dvd_of_le` : If `H ≤ K`, then `K.index ∣ H.index`
- `relindex_mul_relindex` : `relindex` is multiplicative in towers

-/

namespace subgroup

open_locale cardinal

variables {G : Type*} [group G] (H K L : subgroup G)

/-- The index of a subgroup as a natural number, and returns 0 if the index is infinite. -/
@[to_additive "The index of a subgroup as a natural number,
and returns 0 if the index is infinite."]
noncomputable def index : ℕ :=
nat.card (quotient_group.quotient H)

/-- The relative index of a subgroup as a natural number,
  and returns 0 if the relative index is infinite. -/
@[to_additive "The relative index of a subgroup as a natural number,
  and returns 0 if the relative index is infinite."]
noncomputable def relindex : ℕ :=
(H.subgroup_of K).index

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

@[to_additive] lemma index_comap {G' : Type*} [group G'] (f : G' →* G) :
  (H.comap f).index = H.relindex f.range :=
eq.trans (congr_arg index (by refl))
  ((H.subgroup_of f.range).index_comap_of_surjective f.range_restrict_surjective)

variables {H K L}

@[to_additive] lemma relindex_mul_index (h : H ≤ K) : H.relindex K * K.index = H.index :=
((mul_comm _ _).trans (cardinal.to_nat_mul _ _).symm).trans
  (congr_arg cardinal.to_nat (equiv.cardinal_eq (quotient_equiv_prod_of_le h))).symm

@[to_additive] lemma index_dvd_of_le (h : H ≤ K) : K.index ∣ H.index :=
dvd_of_mul_left_eq (H.relindex K) (relindex_mul_index h)

@[to_additive] lemma relindex_subgroup_of (hKL : K ≤ L) :
  (H.subgroup_of L).relindex (K.subgroup_of L) = H.relindex K :=
((index_comap (H.subgroup_of L) (inclusion hKL)).trans (congr_arg _ (inclusion_range hKL))).symm

@[to_additive] lemma relindex_mul_relindex (hHK : H ≤ K) (hKL : K ≤ L) :
  H.relindex K * K.relindex L = H.relindex L :=
begin
  rw [←relindex_subgroup_of hKL],
  exact relindex_mul_index (λ x hx, hHK hx),
end

variables (H K L)

lemma inf_relindex_right : (H ⊓ K).relindex K = H.relindex K :=
begin
  rw [←subgroup_of_map_subtype, relindex, relindex, subgroup_of, comap_map_eq_self_of_injective],
  exact subtype.coe_injective,
end

lemma inf_relindex_left : (H ⊓ K).relindex H = K.relindex H :=
by rw [inf_comm, inf_relindex_right]

lemma inf_relindex_eq_relindex_sup [K.normal] : (H ⊓ K).relindex H = K.relindex (H ⊔ K) :=
cardinal.to_nat_congr (quotient_group.quotient_inf_equiv_prod_normal_quotient H K).to_equiv

lemma relindex_eq_relindex_sup [K.normal] : K.relindex H = K.relindex (H ⊔ K) :=
by rw [←inf_relindex_left, inf_relindex_eq_relindex_sup]

variables {H K}

lemma relindex_dvd_of_le_left (hHK : H ≤ K) :
  K.relindex L ∣ H.relindex L :=
begin
  apply dvd_of_mul_left_eq ((H ⊓ L).relindex (K ⊓ L)),
  rw [←inf_relindex_right H L, ←inf_relindex_right K L],
  exact relindex_mul_relindex (inf_le_inf_right L hHK) inf_le_right,
end

variables (H K)

@[simp, to_additive] lemma index_top : (⊤ : subgroup G).index = 1 :=
cardinal.to_nat_eq_one_iff_unique.mpr ⟨quotient_group.subsingleton_quotient_top, ⟨1⟩⟩

@[simp, to_additive] lemma index_bot : (⊥ : subgroup G).index = nat.card G :=
cardinal.to_nat_congr (quotient_group.quotient_bot.to_equiv)

@[to_additive] lemma index_bot_eq_card [fintype G] : (⊥ : subgroup G).index = fintype.card G :=
index_bot.trans nat.card_eq_fintype_card

@[simp, to_additive] lemma relindex_top_left : (⊤ : subgroup G).relindex H = 1 :=
index_top

@[simp, to_additive] lemma relindex_top_right : H.relindex ⊤ = H.index :=
by rw [←relindex_mul_index (show H ≤ ⊤, from le_top), index_top, mul_one]

@[simp, to_additive] lemma relindex_bot_left : (⊥ : subgroup G).relindex H = nat.card H :=
by rw [relindex, bot_subgroup_of, index_bot]

@[to_additive] lemma relindex_bot_left_eq_card [fintype H] :
  (⊥ : subgroup G).relindex H = fintype.card H :=
H.relindex_bot_left.trans nat.card_eq_fintype_card

@[simp, to_additive] lemma relindex_bot_right : H.relindex ⊥ = 1 :=
by rw [relindex, subgroup_of_bot_eq_top, index_top]

@[simp, to_additive] lemma relindex_self : H.relindex H = 1 :=
by rw [relindex, subgroup_of_self, index_top]

@[to_additive] lemma card_mul_index : nat.card H * H.index = nat.card G :=
by { rw [←relindex_bot_left, ←index_bot], exact relindex_mul_index bot_le }

@[to_additive] lemma index_eq_card [fintype (quotient_group.quotient H)] :
  H.index = fintype.card (quotient_group.quotient H) :=
nat.card_eq_fintype_card

@[to_additive] lemma index_mul_card [fintype G] [hH : fintype H] :
  H.index * fintype.card H = fintype.card G :=
by rw [←relindex_bot_left_eq_card, ←index_bot_eq_card, mul_comm]; exact relindex_mul_index bot_le

@[to_additive] lemma index_dvd_card [fintype G] : H.index ∣ fintype.card G :=
begin
  classical,
  exact ⟨fintype.card H, H.index_mul_card.symm⟩,
end

variables {H}

@[simp] lemma index_eq_one : H.index = 1 ↔ H = ⊤ :=
⟨λ h, quotient_group.subgroup_eq_top_of_subsingleton H (cardinal.to_nat_eq_one_iff_unique.mp h).1,
  λ h, (congr_arg index h).trans index_top⟩

lemma index_ne_zero_of_fintype [hH : fintype (quotient_group.quotient H)] : H.index ≠ 0 :=
by { rw index_eq_card, exact fintype.card_ne_zero }

lemma one_lt_index_of_ne_top [fintype (quotient_group.quotient H)] (hH : H ≠ ⊤) : 1 < H.index :=
nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨index_ne_zero_of_fintype, mt index_eq_one.mp hH⟩

end subgroup
