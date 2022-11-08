/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import data.real.basic
import group_theory.schreier
import group_theory.specific_groups.dihedral

/-!
# Commuting Probability
This file introduces the commuting probability of finite groups.

## Main definitions
* `comm_prob`: The commuting probability of a finite type with a multiplication operation.
-/

noncomputable theory
open_locale classical
open_locale big_operators
open_locale pointwise

universe u

def mul_equiv.restrict_of_comap {G : Type u} [group G] (ϕ : G ≃* G) (H : subgroup G)
  (hH : H.comap ϕ.to_monoid_hom = H) : H ≃* H :=
monoid_hom.to_mul_equiv
  ((ϕ.to_monoid_hom.restrict H).cod_restrict H (λ h, let hH := hH.ge in hH h.2))
  ((ϕ.symm.to_monoid_hom.restrict H).cod_restrict H
    (λ h, let hH := ((H.comap_equiv_eq_map_symm ϕ).symm.trans hH).le in hH ⟨h, h.2, rfl⟩))
  (monoid_hom.ext (λ h, subtype.ext (ϕ.symm_apply_apply h)))
  (monoid_hom.ext (λ h, subtype.ext (ϕ.apply_symm_apply h)))

def mul_equiv.restrict_of_map {G : Type u} [group G] (ϕ : G ≃* G) (H : subgroup G)
  (hH : H.map ϕ.to_monoid_hom = H) : H ≃* H :=
monoid_hom.to_mul_equiv
  ((ϕ.to_monoid_hom.restrict H).cod_restrict H (λ h, let hH := hH.le in hH ⟨h, h.2, rfl⟩))
  ((ϕ.symm.to_monoid_hom.restrict H).cod_restrict H
    (λ h, let hH := ((H.map_equiv_eq_comap_symm ϕ).symm.trans hH).ge in hH h.2))
  (monoid_hom.ext (λ h, subtype.ext (ϕ.symm_apply_apply h)))
  (monoid_hom.ext (λ h, subtype.ext (ϕ.apply_symm_apply h)))

def mul_equiv.restrict {G : Type u} [group G] (ϕ : G ≃* G) (H : subgroup G)
  [hH : H.characteristic] : H ≃* H :=
ϕ.restrict_of_comap H (hH.fixed ϕ)

instance characteristic_of_characteristic {G : Type u} [group G] {H : subgroup G}
  [hH : H.characteristic] {K : subgroup H} [hK : K.characteristic] :
    (K.map H.subtype).characteristic :=
begin
  refine subgroup.characteristic_iff_map_eq.mpr (λ ϕ, _),
  have : ϕ.to_monoid_hom.comp H.subtype = H.subtype.comp (ϕ.restrict H).to_monoid_hom := rfl,
  rw [K.map_map, this, ←K.map_map, subgroup.characteristic_iff_map_eq.mp hK],
end

open fintype

variables (M : Type*) [has_mul M]

/-- The commuting probability of a finite type with a multiplication operation -/
def comm_prob : ℚ := nat.card {p : M × M // p.1 * p.2 = p.2 * p.1} / nat.card M ^ 2

lemma comm_prob_def :
  comm_prob M = nat.card {p : M × M // p.1 * p.2 = p.2 * p.1} / nat.card M ^ 2 :=
rfl

variables [finite M]

lemma comm_prob_pos [h : nonempty M] : 0 < comm_prob M :=
h.elim (λ x, div_pos (nat.cast_pos.mpr (finite.card_pos_iff.mpr ⟨⟨(x, x), rfl⟩⟩))
  (pow_pos (nat.cast_pos.mpr finite.card_pos) 2))

lemma comm_prob_le_one : comm_prob M ≤ 1 :=
begin
  refine div_le_one_of_le _ (sq_nonneg (nat.card M)),
  rw [←nat.cast_pow, nat.cast_le, sq, ←nat.card_prod],
  apply finite.card_subtype_le,
end

variables {M}

lemma comm_prob_eq_one_iff [h : nonempty M] : comm_prob M = 1 ↔ commutative ((*) : M → M → M) :=
begin
  haveI := fintype.of_finite M,
  rw [comm_prob, ←set.coe_set_of, nat.card_eq_fintype_card, nat.card_eq_fintype_card],
  rw [div_eq_one_iff_eq, ←nat.cast_pow, nat.cast_inj, sq, ←card_prod,
      set_fintype_card_eq_univ_iff, set.eq_univ_iff_forall],
  { exact ⟨λ h x y, h (x, y), λ h x, h x.1 x.2⟩ },
  { exact pow_ne_zero 2 (nat.cast_ne_zero.mpr card_ne_zero) },
end

variables (G : Type*) [group G] [finite G]

lemma card_comm_eq_card_conj_classes_mul_card :
  nat.card {p : G × G // p.1 * p.2 = p.2 * p.1} = nat.card (conj_classes G) * nat.card G :=
begin
  haveI := fintype.of_finite G,
  simp only [nat.card_eq_fintype_card],
  convert calc card {p : G × G // p.1 * p.2 = p.2 * p.1} = card (Σ g, {h // g * h = h * g}) :
  card_congr (equiv.subtype_prod_equiv_sigma_subtype (λ g h : G, g * h = h * g))
... = ∑ g, card {h // g * h = h * g} : card_sigma _
... = ∑ g, card (mul_action.fixed_by (conj_act G) G g) : sum_equiv conj_act.to_conj_act.to_equiv
  _ _ (λ g, card_congr' $ congr_arg _ $ funext $ λ h, mul_inv_eq_iff_eq_mul.symm.to_eq)
... = card (quotient (mul_action.orbit_rel (conj_act G) G)) * card G :
  mul_action.sum_card_fixed_by_eq_card_orbits_mul_card_group (conj_act G) G
... = card (quotient (is_conj.setoid G)) * card G :
  have this : mul_action.orbit_rel (conj_act G) G = is_conj.setoid G :=
    setoid.ext (λ g h, (setoid.comm' _).trans is_conj_iff.symm),
  by cc
end

lemma comm_prob_def' : comm_prob G = nat.card (conj_classes G) / nat.card G :=
begin
  rw [comm_prob, card_comm_eq_card_conj_classes_mul_card, nat.cast_mul, sq],
  exact mul_div_mul_right _ _ (nat.cast_ne_zero.mpr finite.card_pos.ne'),
end

variables {G} (H : subgroup G)

lemma subgroup.comm_prob_subgroup_le : comm_prob H ≤ comm_prob G * H.index ^ 2 :=
begin
  /- After rewriting with `comm_prob_def`, we reduce to showing that `G` has at least as many
    commuting pairs as `H`. -/
  rw [comm_prob_def, comm_prob_def,  div_le_iff, mul_assoc, ←mul_pow, ←nat.cast_mul,
      mul_comm H.index, H.card_mul_index, div_mul_cancel, nat.cast_le],
  { refine finite.card_le_of_injective (λ p, ⟨⟨p.1.1, p.1.2⟩, subtype.ext_iff.mp p.2⟩) _,
    exact λ p q h, by simpa only [subtype.ext_iff, prod.ext_iff] using h },
  { exact pow_ne_zero 2 (nat.cast_ne_zero.mpr finite.card_pos.ne') },
  { exact pow_pos (nat.cast_pos.mpr finite.card_pos) 2 },
end

lemma subgroup.comm_prob_quotient_le [H.normal] : comm_prob (G ⧸ H) ≤ comm_prob G * nat.card H :=
begin
  /- After rewriting with `comm_prob_def'`, we reduce to showing that `G` has at least as many
    conjugacy classes as `G ⧸ H`. -/
  rw [comm_prob_def', comm_prob_def', div_le_iff, mul_assoc, ←nat.cast_mul, ←subgroup.index,
      H.card_mul_index, div_mul_cancel, nat.cast_le],
  { apply finite.card_le_of_surjective,
    show function.surjective (conj_classes.map (quotient_group.mk' H)),
    exact (conj_classes.map_surjective quotient.surjective_quotient_mk') },
  { exact nat.cast_ne_zero.mpr finite.card_pos.ne' },
  { exact nat.cast_pos.mpr finite.card_pos },
end

variables (G)

lemma inv_card_commutator_le_comm_prob : (↑(nat.card (commutator G)))⁻¹ ≤ comm_prob G :=
(inv_pos_le_iff_one_le_mul (by exact nat.cast_pos.mpr finite.card_pos)).mpr
  (le_trans (ge_of_eq (comm_prob_eq_one_iff.mpr (abelianization.comm_group G).mul_comm))
    (commutator G).comm_prob_quotient_le)

section neumann

open subgroup

variables (ε : ℝ)

def weak_neumann_subgroup (ε : ℝ) : subgroup G :=
closure ({g : G | ↑(nat.card (centralizer (zpowers g))) ≥ ε / 2 * nat.card G})

namespace weak_neumann_subgroup

-- Waiting on Schur
def commutator_bound : ℝ → ℕ := sorry

def index_bound : ℝ → ℕ := λ ε, nat.ceil (2 / ε)

-- Waiting on Schur
lemma card_commutator_le (h : ↑(comm_prob G) ≥ ε) :
  nat.card (commutator (weak_neumann_subgroup G ε)) ≤ commutator_bound ε :=
begin
  sorry,
end

lemma index_le (h : ↑(comm_prob G) ≥ ε) :
  (weak_neumann_subgroup G ε).index ≤ index_bound ε :=
begin
  rw index_bound,
  refine nat.cast_le.mp (le_trans _ (nat.le_ceil (2 / ε))),
  sorry,
end

open_locale pointwise

lemma smul_centralizer {G : Type*} [group G] {α : Type*} [group α] [mul_distrib_mul_action α G]
  (a : α) (H : subgroup G) :
  a • H.centralizer = (a • H).centralizer :=
begin
  ext g,
  refine ⟨_, λ hg, ⟨a⁻¹ • g, λ h hh, _, smul_inv_smul a g⟩⟩,
  { rintros ⟨g, hg, rfl⟩ - ⟨h, hh, rfl⟩,
    rw [←map_mul, ←map_mul, hg h hh] },
  { rw [←smul_left_cancel_iff a, smul_mul', smul_mul', smul_inv_smul],
    exact hg (a • h) ⟨h, hh, rfl⟩ },
end

lemma smul_zpowers {G : Type*} [group G] {α : Type*} [group α] [mul_distrib_mul_action α G]
  (a : α) (g : G) : a • (zpowers g) = zpowers (a • g) :=
begin
  simp_rw [set_like.ext_iff, mem_pointwise_smul_iff_inv_smul_mem, mem_zpowers_iff,
    eq_inv_smul_iff],
  refine λ x, exists_congr (λ n, eq_iff_eq_cancel_right.mpr _),
  exact map_zpow (mul_distrib_mul_action.to_monoid_End α G a) g n,
end

instance characteristic : (weak_neumann_subgroup G ε).characteristic :=
begin
  rw [weak_neumann_subgroup, characteristic_iff_map_le],
  intro ϕ,
  rw monoid_hom.map_closure,
  apply closure_mono,
  rintros - ⟨g, hg : _ ≤ _, rfl⟩,
  refine le_of_le_of_eq hg (congr_arg coe (nat.card_congr _)),
  rw [mul_equiv.coe_to_monoid_hom, ←mul_aut.smul_def, ←smul_zpowers, ←smul_centralizer],
  exact equiv_smul ϕ (zpowers g).centralizer,
end

end weak_neumann_subgroup

@[derive characteristic] def strong_neumann_subgroup (ε : ℝ) : subgroup G :=
(commutator (weak_neumann_subgroup G ε)).centralizer.map (weak_neumann_subgroup G ε).subtype

lemma strong_neumann_subgroup_le_weak_neumann_subgroup (ε : ℝ) :
  strong_neumann_subgroup G ε ≤ weak_neumann_subgroup G ε :=
(commutator (weak_neumann_subgroup G ε)).centralizer.map_subtype_le

namespace strong_neumann_subgroup

def commutator_bound : ℝ → ℕ := weak_neumann_subgroup.commutator_bound

def index_bound : ℝ → ℕ :=
λ ε, weak_neumann_subgroup.index_bound ε * (weak_neumann_subgroup.commutator_bound ε).factorial

lemma _root_.subgroup.card_dvd_of_le' {G : Type*} [group G] {H K : subgroup G} (h : H ≤ K) :
  nat.card H ∣ nat.card K :=
begin
  rw [←relindex_bot_left, ←relindex_bot_left],
  exact ⟨H.relindex K, (relindex_mul_relindex ⊥ H K bot_le h).symm⟩,
end

lemma commutator_map {G H : Type*} [group G] [group H] (f : G →* H) :
  (commutator G).map f = ⁅f.range, f.range⁆ :=
by rw [commutator, map_commutator, f.range_eq_map]

lemma commutator_map_subtype {G : Type*} [group G] (H : subgroup G) :
  (commutator H).map H.subtype = ⁅H, H⁆ :=
by rw [commutator_map, H.subtype_range]

lemma card_commutator_eq {G : Type*} [group G] (H : subgroup G) :
  nat.card (commutator H) = nat.card ↥⁅H, H⁆ :=
nat.card_congr (((commutator H).equiv_map_of_injective H.subtype H.subtype_injective).trans
  (mul_equiv.subgroup_congr (commutator_map_subtype H)))

lemma card_commutator_le (h : ↑(comm_prob G) ≥ ε) :
  nat.card (commutator (strong_neumann_subgroup G ε)) ≤ commutator_bound ε :=
begin
  refine le_trans _ (weak_neumann_subgroup.card_commutator_le G ε h),
  rw [card_commutator_eq, card_commutator_eq],
  let h := strong_neumann_subgroup_le_weak_neumann_subgroup G ε,
  refine nat.le_of_dvd finite.card_pos (subgroup.card_dvd_of_le' (subgroup.commutator_mono h h)),
end

lemma index_le (h : ↑(comm_prob G) ≥ ε) :
  (strong_neumann_subgroup G ε).index ≤ index_bound ε :=
begin
  sorry,
end

lemma commutator_le_center :
  commutator (strong_neumann_subgroup G ε) ≤ (strong_neumann_subgroup G ε).center :=
begin
  rw [strong_neumann_subgroup, ←subgroup.map_subtype_le_map_subtype, commutator_map_subtype],
  have key := commutator_centralizer_commutator_le_center (weak_neumann_subgroup G ε),
  rw [←subgroup.map_subtype_le_map_subtype, subgroup.map_commutator] at key,
  refine key.trans _,
  rintros - ⟨g, hg, rfl⟩,
  refine ⟨⟨g, g, λ h hh, hg h, rfl⟩, _, rfl⟩,
  rintros ⟨-, h, hh, rfl⟩,
  specialize hg h,
  rwa subtype.ext_iff at hg ⊢,
end

end strong_neumann_subgroup

end neumann

section reciprocal_group

def reciprocal_factors : ℕ → list ℕ
| 0 := [0]
| 1 := []
| n@(nat.succ (nat.succ _)) :=
have n / 2 < n, from (nat.div_lt_self' _ _),
have (n + 3) / 4 < n, from sorry,
have (n + 1) / 4 < n, from lt_of_le_of_lt
  (nat.div_le_div_right (le_self_add : n + 1 ≤ (n + 1) + 2)) this,
if n % 2 = 0 then (reciprocal_factors (n / 2)).cons 3 else
if n % 4 = 1 then (reciprocal_factors ((n + 3) / 4)).cons n else
            (reciprocal_factors ((n + 1) / 4)).cons (3 * n)

@[derive group] def reciprocal_group (n : ℕ) : Type :=
Π i : fin (reciprocal_factors n).length, dihedral_group ((reciprocal_factors n).nth_le i i.2)

lemma comm_prob_reciprocal_group (n : ℕ) : comm_prob (reciprocal_group n) = 1 / n :=
begin
  sorry,
end

end reciprocal_group

section set

def comm_prob_set : submonoid ℝ :=
{ carrier := {p | ∃ (G : Type*) (h : group G), p = @comm_prob G ⟨h.mul⟩},
  one_mem' := sorry,
  mul_mem' := sorry }

instance : monoid_with_zero comm_prob_set :=
{ zero := ⟨0, sorry⟩,
  zero_mul := sorry,
  mul_zero := sorry,
  .. comm_prob_set.to_monoid }

end set
