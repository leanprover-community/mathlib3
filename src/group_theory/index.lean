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
Several theorems proved in this file are known as Lagrange's theorem.

## Main definitions

- `H.index` : the index of `H : subgroup G` as a natural number,
  and returns 0 if the index is infinite.
- `H.relindex K` : the relative index of `H : subgroup G` in `K : subgroup G` as a natural number,
  and returns 0 if the relative index is infinite.

# Main results

- `card_mul_index` : `nat.card H * H.index = nat.card G`
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
nat.card (G ⧸ H)

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

variables (H K L)

@[to_additive] lemma relindex_mul_relindex (hHK : H ≤ K) (hKL : K ≤ L) :
  H.relindex K * K.relindex L = H.relindex L :=
begin
  rw [←relindex_subgroup_of hKL],
  exact relindex_mul_index (λ x hx, hHK hx),
end

lemma inf_relindex_right : (H ⊓ K).relindex K = H.relindex K :=
begin
  rw [←subgroup_of_map_subtype, relindex, relindex, subgroup_of, comap_map_eq_self_of_injective],
  exact subtype.coe_injective,
end

lemma inf_relindex_left : (H ⊓ K).relindex H = K.relindex H :=
by rw [inf_comm, inf_relindex_right]

lemma relindex_inf_mul_relindex : H.relindex (K ⊓ L) * K.relindex L = (H ⊓ K).relindex L :=
by rw [←inf_relindex_right H (K ⊓ L), ←inf_relindex_right K L, ←inf_relindex_right (H ⊓ K) L,
  inf_assoc, relindex_mul_relindex (H ⊓ (K ⊓ L)) (K ⊓ L) L inf_le_right inf_le_right]

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
  exact relindex_mul_relindex (H ⊓ L) (K ⊓ L) L (inf_le_inf_right L hHK) inf_le_right,
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

@[simp, to_additive card_mul_index]
lemma card_mul_index : nat.card H * H.index = nat.card G :=
by { rw [←relindex_bot_left, ←index_bot], exact relindex_mul_index bot_le }

@[to_additive] lemma index_map {G' : Type*} [group G'] (f : G →* G') :
  (H.map f).index = (H ⊔ f.ker).index * f.range.index :=
by rw [←comap_map_eq, index_comap, relindex_mul_index (H.map_le_range f)]

@[to_additive] lemma index_map_dvd {G' : Type*} [group G'] {f : G →* G'}
  (hf : function.surjective f) : (H.map f).index ∣ H.index :=
begin
  rw [index_map, f.range_top_of_surjective hf, index_top, mul_one],
  exact index_dvd_of_le le_sup_left,
end

@[to_additive] lemma dvd_index_map {G' : Type*} [group G'] {f : G →* G'}
  (hf : f.ker ≤ H) : H.index ∣ (H.map f).index :=
begin
  rw [index_map, sup_of_le_left hf],
  apply dvd_mul_right,
end

@[to_additive] lemma index_map_eq {G' : Type*} [group G'] {f : G →* G'}
  (hf1 : function.surjective f) (hf2 : f.ker ≤ H) : (H.map f).index = H.index :=
nat.dvd_antisymm (H.index_map_dvd hf1) (H.dvd_index_map hf2)

@[to_additive] lemma index_eq_card [fintype (G ⧸ H)] :
  H.index = fintype.card (G ⧸ H) :=
nat.card_eq_fintype_card

@[to_additive index_mul_card] lemma index_mul_card [fintype G] [hH : fintype H] :
  H.index * fintype.card H = fintype.card G :=
by rw [←relindex_bot_left_eq_card, ←index_bot_eq_card, mul_comm]; exact relindex_mul_index bot_le

@[to_additive] lemma index_dvd_card [fintype G] : H.index ∣ fintype.card G :=
begin
  classical,
  exact ⟨fintype.card H, H.index_mul_card.symm⟩,
end

variables {H K L}

lemma relindex_eq_zero_of_le_left (hHK : H ≤ K) (hKL : K.relindex L = 0) : H.relindex L = 0 :=
by rw [←inf_relindex_right, ←relindex_mul_relindex (H ⊓ L) (K ⊓ L) L
  (inf_le_inf_right L hHK) inf_le_right, inf_relindex_right, hKL, mul_zero]

lemma relindex_eq_zero_of_le_right (hKL : K ≤ L) (hHK : H.relindex K = 0) : H.relindex L = 0 :=
cardinal.to_nat_apply_of_omega_le (le_trans (le_of_not_lt (λ h, cardinal.mk_ne_zero _
  ((cardinal.cast_to_nat_of_lt_omega h).symm.trans (cardinal.nat_cast_inj.mpr hHK))))
    (quotient_subgroup_of_embedding_of_le H hKL).cardinal_le)

lemma relindex_ne_zero_trans (hHK : H.relindex K ≠ 0) (hKL : K.relindex L ≠ 0) :
  H.relindex L ≠ 0 :=
λ h, mul_ne_zero (mt (relindex_eq_zero_of_le_right (show K ⊓ L ≤ K, from inf_le_left)) hHK) hKL
  ((relindex_inf_mul_relindex H K L).trans (relindex_eq_zero_of_le_left inf_le_left h))

@[simp] lemma index_eq_one : H.index = 1 ↔ H = ⊤ :=
⟨λ h, quotient_group.subgroup_eq_top_of_subsingleton H (cardinal.to_nat_eq_one_iff_unique.mp h).1,
  λ h, (congr_arg index h).trans index_top⟩

lemma index_ne_zero_of_fintype [hH : fintype (G ⧸ H)] : H.index ≠ 0 :=
by { rw index_eq_card, exact fintype.card_ne_zero }

lemma one_lt_index_of_ne_top [fintype (G ⧸ H)] (hH : H ≠ ⊤) : 1 < H.index :=
nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨index_ne_zero_of_fintype, mt index_eq_one.mp hH⟩

end subgroup
