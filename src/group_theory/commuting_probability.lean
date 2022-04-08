/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import data.finset.pointwise
import group_theory.complement
import group_theory.finiteness
import group_theory.group_action.conj_act
import group_theory.index
import group_theory.schreier
import group_theory.solvable

/-!
# Commuting Probability
This file introduces the commuting probability of finite groups.

## Main definitions
* `comm_prob`: The commuting probability of a finite type with a multiplication operation.

## Todo
* Neumann's theorem.
-/

section for_mathlib

@[to_additive] instance subgroup.centralizer.characteristic
  {G : Type*} [group G] (H : subgroup G) [hH : H.characteristic] :
  H.centralizer.characteristic :=
begin
  refine subgroup.characteristic_iff_comap_le.mpr (λ ϕ g hg h hh, ϕ.injective _),
  rw [map_mul, map_mul],
  exact hg (ϕ h) (subgroup.characteristic_iff_le_comap.mp hH ϕ hh),
end

instance subgroup.commutator.characteristic (G : Type*) [group G] : (commutator G).characteristic :=
subgroup.characteristic_iff_le_map.mpr (λ ϕ, commutator_le_map_commutator
  (ge_of_eq (subgroup.map_top_of_surjective ϕ.to_monoid_hom ϕ.surjective))
  (ge_of_eq (subgroup.map_top_of_surjective ϕ.to_monoid_hom ϕ.surjective)))

end for_mathlib

noncomputable theory
open_locale classical
open_locale big_operators
open_locale pointwise

open fintype

section technical

namespace subgroup

/-- **Schreier's Lemma** -/
lemma closure_mul_eq_top' {G : Type*} [group G] {H : subgroup G} {R S : finset G}
  (hR : (R : set G) ∈ right_transversals (H : set G)) (hR1 : (1 : G) ∈ R)
  (hS : closure (S : set G) = ⊤) :
  closure ((((R * S).image (λ g, ⟨g * (mem_right_transversals.to_fun hR g)⁻¹,
    mem_right_transversals.mul_inv_to_fun_mem hR g⟩)) : finset H) : set H) = ⊤ :=
begin
  rw [finset.coe_image, finset.coe_mul, eq_top_iff, ←map_subtype_le_map_subtype,
      ←monoid_hom.range_eq_map, subtype_range, monoid_hom.map_closure, set.image_image],
  exact ge_of_eq (closure_mul_eq hR hR1 hS),
end

lemma fintype_of_index_ne_zero {G : Type*} [group G] {H : subgroup G} (hH : H.index ≠ 0) :
  fintype (G ⧸ H) :=
(cardinal.lt_omega_iff_fintype.mp (lt_of_not_ge (mt cardinal.to_nat_apply_of_omega_le hH))).some

instance tada {G : Type*} [group G] (H : subgroup G) [fintype (G ⧸ H)] :
  fintype (quotient (quotient_group.right_rel H)) :=
fintype.of_equiv (G ⧸ H)
{ to_fun := quotient.map' (λ g, g⁻¹) (λ a b h, (congr_arg (∈ H) (by group)).mp (H.inv_mem h)),
  inv_fun := quotient.map' (λ g, g⁻¹) (λ a b h, (congr_arg (∈ H) (by group)).mp (H.inv_mem h)),
  left_inv := begin
    refine λ g, quotient.induction_on' g (λ g, quotient.sound' _),
    simp only [inv_inv],
    refine quotient.exact' rfl,
  end,
  right_inv := begin
    refine λ g, quotient.induction_on' g (λ g, quotient.sound' _),
    simp only [inv_inv],
    refine quotient.exact' rfl,
  end, }

lemma card_quotient_right_rel_eq {G : Type*} [group G] (H : subgroup G) [fintype (G ⧸ H)] :
  fintype.card (quotient (quotient_group.right_rel H)) = fintype.card (G ⧸ H) :=
fintype.of_equiv_card _

lemma fg_of_index_ne_zero {G : Type*} [group G] [hG : group.fg G] {H : subgroup G}
  (hH : H.index ≠ 0) : group.fg H :=
begin
  obtain ⟨S, hS⟩ := hG.1,
  obtain ⟨R₀, hR : R₀ ∈ right_transversals (H : set G), hR1⟩ := exists_right_transversal (1 : G),
  haveI : fintype (G ⧸ H) := fintype_of_index_ne_zero hH,
  haveI : fintype R₀ := fintype.of_equiv _ (mem_right_transversals.to_equiv hR),
  let R : finset G := set.to_finset R₀,
  replace hR : (R : set G) ∈ right_transversals (H : set G) := by rwa set.coe_to_finset,
  replace hR1 : (1 : G) ∈ R := by rwa set.mem_to_finset,
  exact ⟨⟨_, closure_mul_eq_top' hR hR1 hS⟩⟩,
end

lemma schreier_aux3 {G : Type*} [group G] [hG : group.fg G] {H : subgroup G}
  (hH : H.index ≠ 0) : @group.rank H _ (fg_of_index_ne_zero hH) _ ≤ H.index * group.rank G :=
begin
  obtain ⟨S, hS₀, hS⟩ := group.rank_spec G,
  obtain ⟨R₀, hR : R₀ ∈ right_transversals (H : set G), hR1⟩ := exists_right_transversal (1 : G),
  haveI : fintype (G ⧸ H) := fintype_of_index_ne_zero hH,
  haveI : fintype R₀ := fintype.of_equiv _ (mem_right_transversals.to_equiv hR),
  let R : finset G := set.to_finset R₀,
  replace hR : (R : set G) ∈ right_transversals (H : set G) := by rwa set.coe_to_finset,
  replace hR1 : (1 : G) ∈ R := by rwa set.mem_to_finset,
  letI hH' : group.fg H := ⟨⟨_, closure_mul_eq_top' hR hR1 hS⟩⟩,
  change @group.rank H _ hH' _ ≤ H.index * group.rank G,
  calc group.rank H ≤ _ : group.rank_le H (closure_mul_eq_top' hR hR1 hS)
  ... ≤ (R * S).card : finset.card_image_le
  ... ≤ (R.product S).card : finset.card_image_le
  ... = R.card * S.card : R.card_product S
  ... = H.index * group.rank G : congr_arg2 (*) _ hS₀,
  calc R.card = fintype.card R : (fintype.card_coe R).symm
  ... = _ : (fintype.card_congr (mem_right_transversals.to_equiv hR)).symm
  ... = fintype.card (G ⧸ H) : H.card_quotient_right_rel_eq
  ... = H.index : H.index_eq_card.symm,
end

end subgroup

end technical

variables (M : Type*) [fintype M] [has_mul M]

/-- The commuting probability of a finite type with a multiplication operation -/
def comm_prob : ℚ := card {p : M × M // p.1 * p.2 = p.2 * p.1} / card M ^ 2

lemma comm_prob_def : comm_prob M = card {p : M × M // p.1 * p.2 = p.2 * p.1} / card M ^ 2 :=
rfl

lemma comm_prob_pos [h : nonempty M] : 0 < comm_prob M :=
h.elim (λ x, div_pos (nat.cast_pos.mpr (card_pos_iff.mpr ⟨⟨(x, x), rfl⟩⟩))
  (pow_pos (nat.cast_pos.mpr card_pos) 2))

lemma comm_prob_le_one : comm_prob M ≤ 1 :=
begin
  refine div_le_one_of_le _ (sq_nonneg (card M)),
  rw [←nat.cast_pow, nat.cast_le, sq, ←card_prod],
  apply set_fintype_card_le_univ,
end

variables {M}

lemma comm_prob_eq_one_iff [h : nonempty M] : comm_prob M = 1 ↔ commutative ((*) : M → M → M) :=
begin
  change (card {p : M × M | p.1 * p.2 = p.2 * p.1} : ℚ) / _ = 1 ↔ _,
  rw [div_eq_one_iff_eq, ←nat.cast_pow, nat.cast_inj, sq, ←card_prod,
      set_fintype_card_eq_univ_iff, set.eq_univ_iff_forall],
  { exact ⟨λ h x y, h (x, y), λ h x, h x.1 x.2⟩ },
  { exact pow_ne_zero 2 (nat.cast_ne_zero.mpr card_ne_zero) },
end

variables (G : Type*) [group G] [fintype G]

lemma card_comm_eq_card_conj_classes_mul_card :
  card {p : G × G // p.1 * p.2 = p.2 * p.1} = card (conj_classes G) * card G :=
calc card {p : G × G // p.1 * p.2 = p.2 * p.1} = card (Σ g, {h // g * h = h * g}) :
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

lemma comm_prob_def' : comm_prob G = card (conj_classes G) / card G :=
begin
  rw [comm_prob, card_comm_eq_card_conj_classes_mul_card, nat.cast_mul, sq],
  exact mul_div_mul_right (card (conj_classes G)) (card G) (nat.cast_ne_zero.mpr card_ne_zero),
end

variables {G} (H : subgroup G)

lemma subgroup.comm_prob_subgroup_le : comm_prob H ≤ comm_prob G * H.index ^ 2 :=
begin
  /- After rewriting with `comm_prob_def`, we reduce to showing that `G` has at least as many
    commuting pairs as `H`. -/
  rw [comm_prob_def, comm_prob_def, div_le_iff, mul_assoc, ←mul_pow, ←nat.cast_mul,
      H.index_mul_card, div_mul_cancel, nat.cast_le],
  { apply card_le_of_injective _ _,
    exact λ p, ⟨⟨p.1.1, p.1.2⟩, subtype.ext_iff.mp p.2⟩,
    exact λ p q h, by simpa only [subtype.ext_iff, prod.ext_iff] using h },
  { exact pow_ne_zero 2 (nat.cast_ne_zero.mpr card_ne_zero) },
  { exact pow_pos (nat.cast_pos.mpr card_pos) 2 },
end

lemma subgroup.comm_prob_quotient_le [H.normal] : comm_prob (G ⧸ H) ≤ comm_prob G * card H :=
begin
  /- After rewriting with `comm_prob_def'`, we reduce to showing that `G` has at least as many
    conjugacy classes as `G ⧸ H`. -/
  rw [comm_prob_def', comm_prob_def', div_le_iff, mul_assoc, ←nat.cast_mul, mul_comm (card H),
      ←subgroup.card_eq_card_quotient_mul_card_subgroup, div_mul_cancel, nat.cast_le],
  { exact card_le_of_surjective (conj_classes.map (quotient_group.mk' H))
      (conj_classes.map_surjective quotient.surjective_quotient_mk') },
  { exact nat.cast_ne_zero.mpr card_ne_zero },
  { exact nat.cast_pos.mpr card_pos },
end

variables (G)

lemma inv_card_commutator_le_comm_prob : (↑(card (commutator G)))⁻¹ ≤ comm_prob G :=
(inv_pos_le_iff_one_le_mul (by exact nat.cast_pos.mpr card_pos)).mpr
  (le_trans (ge_of_eq (comm_prob_eq_one_iff.mpr (abelianization.comm_group G).mul_comm))
    (commutator G).comm_prob_quotient_le)

section neumann

def weak_neumann_commutator_bound : ℚ → ℕ := sorry

def weak_neumann_index_bound : ℚ → ℕ := sorry

lemma weak_neumann :
  ∃ K : subgroup G, K.normal ∧
  card (commutator K) ≤ weak_neumann_commutator_bound (comm_prob G)
  ∧ K.index ≤ weak_neumann_index_bound (comm_prob G) :=
begin
  sorry
end

def strong_neumann_commutator_bound : ℚ → ℕ := weak_neumann_commutator_bound

def strong_neumann_index_bound : ℚ → ℕ :=
λ q, weak_neumann_index_bound q * (weak_neumann_commutator_bound q).factorial

lemma strong_neumann :
  ∃ K : subgroup G, K.normal ∧ commutator K ≤ K.center ∧
  card (commutator K) ≤ strong_neumann_commutator_bound (comm_prob G)
  ∧ K.index ≤ strong_neumann_index_bound (comm_prob G) :=
begin
  obtain ⟨K, hK1, hK2, hK3⟩ := weak_neumann G,
  refine ⟨(commutator K).centralizer.map K.subtype, _, _, _, _⟩,
  { haveI : (commutator K).characteristic := by apply_instance,
    -- why doesn't apply_instance work directly?
    apply_instance },
  { rw [commutator_def, commutator_def, ←subgroup.map_subtype_le_map_subtype,
        subgroup.map_commutator, ←monoid_hom.range_eq_map, subgroup.subtype_range],
    have key := commutator_centralizer_commutator_le_center K,
    rw [commutator_def, ←subgroup.map_subtype_le_map_subtype, subgroup.map_commutator] at key,
    refine key.trans _,
    rintros - ⟨g, hg, rfl⟩,
    refine ⟨⟨g, g, λ h hh, hg h, rfl⟩, _, rfl⟩,
    rintros ⟨-, h, hh, rfl⟩,
    exact subtype.ext (show _, from subtype.ext_iff.mp (hg h)) },
  { have key : ∀ H : subgroup G, card (commutator H) = card ↥⁅H, H⁆,
    { intro H,
      conv_rhs { rw [←H.subtype_range, monoid_hom.range_eq_map, ←subgroup.map_commutator] },
      exact fintype.card_congr
        ((commutator H).equiv_map_of_injective H.subtype subtype.coe_injective).to_equiv },
    rw key at hK2 ⊢,
    exact let h := (commutator ↥K).centralizer.map_subtype_le in
    (nat.le_of_dvd card_pos (subgroup.card_dvd_of_le (subgroup.commutator_mono h h))).trans hK2 },
  {
    sorry },
end

end neumann
