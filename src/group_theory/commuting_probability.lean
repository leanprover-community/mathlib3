/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import group_theory.complement
import group_theory.finiteness
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

@[to_additive] instance subgroup.centralizer.characteristic
  {G : Type*} [group G] (H : subgroup G) [H.characteristic] :
  H.centralizer.characteristic := sorry

instance subgroup.commutator.characteristic (G : Type*) [group G] :
  (commutator G).characteristic := sorry

end for_mathlib

noncomputable theory
open_locale classical
open_locale big_operators

open fintype

section technical

open_locale pointwise

namespace mem_left_transversals

def to_equiv {G : Type*} [group G] {H : subgroup G} {S : set G}
  (hS : S ∈ subgroup.left_transversals (H : set G)) : G ⧸ H ≃ S :=
(equiv.of_bijective _ (subgroup.mem_left_transversals_iff_bijective.mp hS)).symm

lemma mk'_to_equiv {G : Type*} [group G] {H : subgroup G} {S : set G}
  (hS : S ∈ subgroup.left_transversals (H : set G)) (q : G ⧸ H) :
  quotient.mk' (to_equiv hS q : G) = q :=
(to_equiv hS).symm_apply_apply q

def to_fun {G : Type*} [group G] {H : subgroup G} {S : set G}
  (hS : S ∈ subgroup.left_transversals (H : set G)) : G → S :=
to_equiv hS ∘ quotient.mk'

lemma inv_to_fun_mul_mem {G : Type*} [group G] {H : subgroup G} {S : set G}
  (hS : S ∈ subgroup.left_transversals (H : set G)) (g : G) : (to_fun hS g : G)⁻¹ * g ∈ H :=
quotient.exact' (mk'_to_equiv hS g)

lemma inv_mul_to_fun_mem {G : Type*} [group G] {H : subgroup G} {S : set G}
  (hS : S ∈ subgroup.left_transversals (H : set G)) (g : G) : g⁻¹ * to_fun hS g ∈ H :=
(congr_arg (∈ H) (by rw [mul_inv_rev, inv_inv])).mp (H.inv_mem (inv_to_fun_mul_mem hS g))

end mem_left_transversals

namespace mem_right_transversals

def to_equiv {G : Type*} [group G] {H : subgroup G} {S : set G}
  (hS : S ∈ subgroup.right_transversals (H : set G)) : quotient (quotient_group.right_rel H) ≃ S :=
(equiv.of_bijective _ (subgroup.mem_right_transversals_iff_bijective.mp hS)).symm

lemma mk'_to_equiv {G : Type*} [group G] {H : subgroup G} {S : set G}
  (hS : S ∈ subgroup.right_transversals (H : set G)) (q : quotient (quotient_group.right_rel H)) :
  quotient.mk' (to_equiv hS q : G) = q :=
(to_equiv hS).symm_apply_apply q

def to_fun {G : Type*} [group G] {H : subgroup G} {S : set G}
  (hS : S ∈ subgroup.right_transversals (H : set G)) : G → S :=
to_equiv hS ∘ quotient.mk'

lemma mul_inv_to_fun_mem {G : Type*} [group G] {H : subgroup G} {S : set G}
  (hS : S ∈ subgroup.right_transversals (H : set G)) (g : G) : g * (to_fun hS g : G)⁻¹ ∈ H :=
quotient.exact' (mk'_to_equiv hS _)

lemma to_fun_mul_inv_mem {G : Type*} [group G] {H : subgroup G} {S : set G}
  (hS : S ∈ subgroup.right_transversals (H : set G)) (g : G) : (to_fun hS g : G) * g⁻¹ ∈ H :=
(congr_arg (∈ H) (by rw [mul_inv_rev, inv_inv])).mp (H.inv_mem (mul_inv_to_fun_mem hS g))

end mem_right_transversals

lemma group.fg_iff' {G : Type*} [group G] : group.fg G ↔ ∃ S : finset G, subgroup.closure (S : set G) = ⊤ :=
group.fg_def

lemma group.fg_iff'' {G : Type*} [group G] :
  group.fg G ↔ ∃ n (S : finset G), S.card = n ∧ subgroup.closure (S : set G) = ⊤ :=
group.fg_iff'.trans ⟨λ ⟨S, hS⟩, ⟨S.card, S, rfl, hS⟩, λ ⟨n, S, hn, hS⟩, ⟨S, hS⟩⟩

def group.min_generators (G : Type*) [group G] [h : group.fg G] :=
nat.find (group.fg_iff''.mp h)

class subgroup.finite_index {G : Type*} [group G] (H : subgroup G) : Prop :=
(finite_index : H.index ≠ 0)

namespace subgroup

lemma exists_left_transversal {G : Type*} [group G] {H : subgroup G} {h : G} (hh : h ∈ H) :
  ∃ S ∈ left_transversals (H : set G), h ∈ S :=
begin
  sorry
end

lemma exists_right_transversal {G : Type*} [group G] {H : subgroup G} {h : G} (hh : h ∈ H) :
  ∃ S ∈ right_transversals (H : set G), h ∈ S :=
begin
  sorry
end

lemma closure_induction_left {G : Type*} [group G] {S : set G} {p : G → Prop} {x : G}
  (h : x ∈ closure S) (H1 : p 1) (Hmul : ∀ (x ∈ S) y, p y → p (x * y))
  (Hinv : ∀ (x ∈ S) y, p y → p (x⁻¹ * y)) : p x :=
begin
  have := le_of_eq (closure_to_submonoid S),
  obtain ⟨l, hl, rfl⟩ := submonoid.exists_list_of_mem_closure (this h),
  induction l with g l ih generalizing hl,
  { exact H1 },
  { rw list.prod_cons,
    rw list.forall_mem_cons at hl,
    specialize ih ((closure S).list_prod_mem (λ g hg, (hl.2 g hg).elim (λ hg, subset_closure hg)
      (λ hg, (closure S).inv_mem_iff.mp (subset_closure hg)))) hl.2,
    exact hl.1.elim (λ hg, Hmul g hg _ ih) (λ hg, (congr_arg _ (inv_inv g)).mp (Hinv _ hg _ ih)) },
end

lemma closure_induction_right {G : Type*} [group G] {S : set G} {p : G → Prop} {x : G}
  (h : x ∈ closure S) (H1 : p 1) (Hmul : ∀ x (y ∈ S), p x → p (x * y))
  (Hinv : ∀ x (y ∈ S), p x → p (x * y⁻¹)) : p x :=
begin
  let q : G → Prop := λ g, p g⁻¹,
  have q_def : ∀ g, q g = p g⁻¹ := λ g, rfl,
  rw ← inv_inv x,
  change q x⁻¹,
  apply closure_induction_left ((closure S).inv_mem h),
  { rwa [q_def, one_inv] },
  { intros x hx y hy,
    rw [q_def, mul_inv_rev],
    exact Hinv y⁻¹ x hx hy },
  { intros x hx y hy,
    rw [q_def, mul_inv_rev, inv_inv],
    exact Hmul y⁻¹ x hx hy },
end

lemma schreier' {G : Type*} [group G] {H : subgroup G} {R S : set G}
  (hR : R ∈ right_transversals (H : set G)) (hR1 : (1 : G) ∈ R) (hS : closure S = ⊤) :
  (closure ((R * S).image (λ g, g * (mem_right_transversals.to_fun hR g)⁻¹)) : set G) * R = ⊤ :=
begin
  let f : G → R := λ g, mem_right_transversals.to_fun hR g,
  let U : set G := (R * S).image (λ g, g * (f g)⁻¹),
  change (closure U : set G) * R = ⊤,
  refine top_le_iff.mp (λ g hg, _),
  apply closure_induction_right (eq_top_iff.mp hS (mem_top g)),
  { exact ⟨1, 1, (closure U).one_mem, hR1, one_mul 1⟩ },
  { rintros - s hs ⟨u, r, hu, hr, rfl⟩,
    rw show u * r * s = u * ((r * s) * (f (r * s))⁻¹) * f (r * s), by group,
    refine set.mul_mem_mul ((closure U).mul_mem hu _) (f (r * s)).coe_prop,
    exact subset_closure ⟨r * s, set.mul_mem_mul hr hs, rfl⟩ },
  { rintros - s hs ⟨u, r, hu, hr, rfl⟩,
    rw show u * r * s⁻¹ = u * (f (r * s⁻¹) * s * r⁻¹)⁻¹ * f (r * s⁻¹), by group,
    refine set.mul_mem_mul ((closure U).mul_mem hu ((closure U).inv_mem _)) (f (r * s⁻¹)).2,
    refine subset_closure ⟨f (r * s⁻¹) * s, set.mul_mem_mul (f (r * s⁻¹)).2 hs, _⟩,
    rw [mul_right_inj, inv_inj],
    have key : (f (r * s⁻¹) : G) * (r * s⁻¹)⁻¹ ∈ H :=
    mem_right_transversals.to_fun_mul_inv_mem hR (r * s⁻¹),
    rw [mul_inv_rev, inv_inv, ←mul_assoc] at key,
    have key : f (f (r * s⁻¹) * s) = ⟨r, hr⟩,
    exact (mem_right_transversals_iff_exists_unique_mul_inv_mem.mp hR (f (r * s⁻¹) * s)).unique
      (mem_right_transversals.mul_inv_to_fun_mem hR (f (r * s⁻¹) * s)) key,
    exact subtype.ext_iff.mp key },
end

/-- **Schreier's Lemma** -/
lemma schreier {G : Type*} [group G] {H : subgroup G} {R S : set G}
  (hR : R ∈ right_transversals (H : set G)) (hR1 : (1 : G) ∈ R) (hS : closure S = ⊤) :
  closure ((R * S).image (λ g, g * (mem_right_transversals.to_fun hR g)⁻¹)) = H :=
begin
  let U : set G := (R * S).image (λ g, g * (mem_right_transversals.to_fun hR g)⁻¹),
  change closure U = H,
  have hU : closure U ≤ H,
  { rw closure_le,
    rintros - ⟨g, -, rfl⟩,
    exact mem_right_transversals.mul_inv_to_fun_mem hR g },
  refine le_antisymm hU (λ h hh, _),
  have h_mem : h ∈ (closure U : set G) * R := eq_top_iff.mp (schreier' hR hR1 hS) (mem_top h),
  obtain ⟨g, r, hg, hr, rfl⟩ := h_mem,
  have h_eq : (⟨r, hr⟩ : R) = (⟨1, hR1⟩ : R),
  { refine (mem_right_transversals_iff_exists_unique_mul_inv_mem.mp hR r).unique _ _,
    { rw [subtype.coe_mk, mul_inv_self],
      exact H.one_mem },
    { rw [subtype.coe_mk, one_inv, mul_one],
      exact (H.mul_mem_cancel_left (hU hg)).mp hh } },
  replace h_eq : r = 1 := subtype.ext_iff.mp h_eq,
  rwa [h_eq, mul_one],
end

/-- **Schreier's Lemma** -/
lemma schreier_aux1 {G : Type*} [group G] {H : subgroup G} {R S : finset G}
  (hR : (R : set G) ∈ right_transversals (H : set G)) (hR1 : (1 : G) ∈ R)
  (hS : closure (S : set G) = ⊤) :
  closure ((((R * S).image (λ g, g * (mem_right_transversals.to_fun hR g)⁻¹)) : finset G) : set G) = H :=
begin
  rw [finset.coe_image, finset.coe_mul],
  exact schreier hR hR1 hS,
end

/-- **Schreier's Lemma** -/
lemma schreier_aux4 {G : Type*} [group G] {H : subgroup G} {R S : finset G}
  (hR : (R : set G) ∈ right_transversals (H : set G)) (hR1 : (1 : G) ∈ R)
  (hS : closure (S : set G) = ⊤) :
  closure ((((R * S).image (λ g, ⟨g * (mem_right_transversals.to_fun hR g)⁻¹,
    mem_right_transversals.mul_inv_to_fun_mem hR g⟩)) : finset H) : set H) = ⊤ :=
begin
  rw [finset.coe_image, finset.coe_mul, eq_top_iff, ←map_subtype_le_map_subtype,
      ←monoid_hom.range_eq_map, subtype_range, monoid_hom.map_closure, set.image_image],
  exact ge_of_eq (schreier hR hR1 hS),
end

instance schreier_aux2 {G : Type*} [group G] [hG : group.fg G] {H : subgroup G}
  [hH : finite_index H] : group.fg H :=
begin
  obtain ⟨S, hS⟩ := hG.1,
  obtain ⟨R₀, hR : R₀ ∈ right_transversals (H : set G), hR1⟩ := exists_right_transversal H.one_mem,
  haveI : fintype (quotient (quotient_group.right_rel H)) := sorry,
  haveI : fintype R₀ := fintype.of_equiv _ (mem_right_transversals.to_equiv hR),
  let R : finset G := set.to_finset R₀,
  replace hR : (R : set G) ∈ right_transversals (H : set G) := by rwa set.coe_to_finset,
  replace hR1 : (1 : G) ∈ R := by rwa set.mem_to_finset,
  exact ⟨⟨_, schreier_aux4 hR hR1 hS⟩⟩,
end

lemma schreier_aux3 {G : Type*} [group G] [hG : finitely_generated G] {H : subgroup G}
  [hH : finite_index H] : min_generators H ≤ H.index * min_generators G :=
begin
  sorry
end

end subgroup

lemma fintype.card_image_le {α β : Type*} (f : α → β) (s : set α) [fintype s] :
  fintype.card (f '' s) ≤ fintype.card s :=
fintype.card_le_of_surjective (s.image_factorization f) set.surjective_onto_image

lemma fintype.card_image2_le {α β γ : Type*} (f : α → β → γ) (s : set α) (t : set β) [fintype s] [fintype t] :
  fintype.card (set.image2 f s t) ≤ fintype.card s * fintype.card t :=
sorry

def card_mul_le {α : Type*} [has_mul α] [decidable_eq α] (s t : set α) [hs : fintype s] [ht : fintype t] :
  card (s * t : set α) ≤ card s * card t :=
by convert fintype.card_image2_le _ s t

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
