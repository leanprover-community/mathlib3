/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import group_theory.group_action.conj_act
import group_theory.index
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

/-- The `centralizer` of `H` is the subgroup of `g : G` commuting with every `h : H`. -/
@[to_additive "The `centralizer` of `H` is the subgroup of `g : G` commuting with every `h : H`."]
def subgroup.centralizer {G : Type*} [group G] (H : subgroup G) : subgroup G :=
{ carrier := {g : G | ∀ h ∈ H, g * h * g⁻¹ * h⁻¹ = 1},
  one_mem' := sorry,
  mul_mem' := sorry,
  inv_mem' := sorry }

@[to_additive] instance subgroup.centralizer.characteristic
  {G : Type*} [group G] (H : subgroup G) [H.characteristic] :
  H.centralizer.characteristic := sorry

instance subgroup.commutator.characteristic (G : Type*) [group G] :
  (commutator G).characteristic := sorry

lemma general_commutator_eq_bot_iff_le_centralizer {G : Type*} [group G] {H K : subgroup G} :
  ⁅H, K⁆ = ⊥ ↔ H ≤ K.centralizer :=
sorry

lemma general_commutator_le_commutator {G : Type*} [group G] (H K : subgroup G) :
  ⁅H, K⁆ ≤ commutator G := sorry

lemma centralizer_top_eq_center (G : Type*) [group G] :
  (⊤ : subgroup G).centralizer = subgroup.center G :=
begin
  sorry
end

lemma centralizer_mono {G : Type*} [group G] {H K : subgroup G} (h : H ≤ K) :
  K.centralizer ≤ H.centralizer := sorry

lemma three_subgroups_lemma {G : Type*} [group G] {X Y Z : subgroup G}
  (h1 : ⁅⁅X, Y⁆, Z⁆ = ⊥) (h2 : ⁅⁅Y, Z⁆, X⁆ = ⊥) : ⁅⁅Z, X⁆, Y⁆ = ⊥ :=
begin
  rw [general_commutator_eq_bot_iff_le_centralizer, general_commutator_le] at h1 h2 ⊢,
  intros z hz x hx y hy,
  have key : z * x * z⁻¹ * x⁻¹ * y * (z * x * z⁻¹ * x⁻¹)⁻¹ * y⁻¹ =
    z * x * (x⁻¹ * y * x⁻¹⁻¹ * y⁻¹ * z⁻¹ * (x⁻¹ * y * x⁻¹⁻¹ * y⁻¹)⁻¹ * z⁻¹⁻¹)⁻¹ * x⁻¹
    * y * (y⁻¹ * z⁻¹ * y⁻¹⁻¹ * z⁻¹⁻¹ * x * (y⁻¹ * z⁻¹ * y⁻¹⁻¹ * z⁻¹⁻¹)⁻¹ * x⁻¹)⁻¹ * y⁻¹ * z⁻¹ :=
  by group,
  rw [key, h1 _ (X.inv_mem hx) y hy _ (Z.inv_mem hz), h2 _ (Y.inv_mem hy) _ (Z.inv_mem hz) x hx,
    one_inv, mul_one, mul_one, mul_inv_cancel_right, mul_inv_cancel_right, mul_inv_self],
end

lemma commutator_centralizer_commutator_le_center (G : Type*) [group G] :
  ⁅(commutator G).centralizer, (commutator G).centralizer⁆ ≤ subgroup.center G :=
begin
  rw [←centralizer_top_eq_center, ←general_commutator_eq_bot_iff_le_centralizer],
  suffices : ⁅⁅⊤, (commutator G).centralizer⁆, (commutator G).centralizer⁆ = ⊥,
  { exact three_subgroups_lemma (by rwa general_commutator_comm (commutator G).centralizer) this },
  rw [general_commutator_comm, general_commutator_eq_bot_iff_le_centralizer],
  apply centralizer_mono,
  apply general_commutator_le_commutator,
end

end for_mathlib

noncomputable theory
open_locale classical
open_locale big_operators

open fintype

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

def weak_neumann_commutator_index_bound : ℚ → ℕ := sorry

lemma weak_neumann :
  ∃ K : subgroup G, K.normal ∧
  card (commutator K) ≤ weak_neumann_commutator_bound (comm_prob G)
  ∧ K.index ≤ weak_neumann_commutator_index_bound (comm_prob G) :=
begin
  sorry
end

def strong_neumann_commutator_bound : ℚ → ℕ := weak_neumann_commutator_bound

def strong_neumann_commutator_index_bound : ℚ → ℕ :=
λ q, weak_neumann_commutator_index_bound q * (weak_neumann_commutator_bound q).factorial

lemma strong_neumann :
  ∃ K : subgroup G, K.normal ∧ commutator K ≤ K.center ∧
  card (commutator K) ≤ strong_neumann_commutator_bound (comm_prob G)
  ∧ K.index ≤ strong_neumann_commutator_index_bound (comm_prob G) :=
begin
  obtain ⟨K, hK1, hK2, hK3⟩ := weak_neumann G,
  refine ⟨(commutator K).centralizer.map K.subtype, _, _, _, _⟩,
  { haveI : (commutator K).characteristic := by apply_instance,
    -- why doesn't apply_instance work directly?
    apply_instance },
  { have key := commutator_centralizer_commutator_le_center K,
    -- three subgroups lemma
    sorry },
  { refine le_trans _ hK2,
    refine nat.le_of_dvd card_pos _,
    sorry },
  { sorry },
end

end neumann
