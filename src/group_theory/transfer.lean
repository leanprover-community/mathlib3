/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import data.zmod.basic
import group_theory.complement
import group_theory.group_action.basic
import group_theory.index

/-!
# The Transfer Homomorphism

In this file we construct the transfer homomorphism.

## Main definitions

- `diff ϕ S T` : The difference of two left transversals `S` and `T` under the homomorphism `ϕ`.
- `transfer ϕ` : The transfer homomorphism induced by `ϕ`.
-/

section quotient_action

lemma mk_smul_out' {α β : Type*} [group α] [monoid β] [mul_action β α] (H : subgroup α)
  [mul_action.quotient_action β H] (b : β) (q : α ⧸ H) :
  quotient_group.mk (b • q.out') = b • q :=
by rw [←mul_action.quotient.smul_mk, quotient_group.out_eq']

lemma coe_smul_out' {α β : Type*} [group α] [monoid β] [mul_action β α] (H : subgroup α)
  [mul_action.quotient_action β H] (b : β) (q : α ⧸ H) :
  ↑(b • q.out') = b • q :=
mk_smul_out' H b q

/-lemma lem20 {G : Type*} [group G] {H : subgroup G}
  {F : Type*} [group F] [mul_action F G] [mul_action.quotient_action F H]
  (f : F) {ϕ : G ⧸ H → G} (hϕ : ∀ q, ↑(ϕ q) = q) (q : G ⧸ H) :
  ↑((f • ϕ) (f⁻¹ • q)) = q :=
by rw [pi.smul_apply, ←mul_action.quotient.smul_coe, hϕ, smul_inv_smul]

lemma lem21 {G : Type*} [group G] {H : subgroup G}
  {F : Type*} [group F] [mul_action F G] [mul_action.quotient_action F H]
  (f : F) {ϕ : G ⧸ H → G} (hϕ : ∀ q, ↑(ϕ q) = q) (q : G ⧸ H) :
  (subgroup.mem_left_transversals.to_equiv
    (subgroup.range_mem_left_transversals (lem20 f hϕ)) q : G) =
      f • subgroup.mem_left_transversals.to_equiv (subgroup.range_mem_left_transversals hϕ) (f⁻¹ • q) :=
begin
  rw [subgroup.mem_left_transversals.range_to_equiv_apply,
      subgroup.mem_left_transversals.range_to_equiv_apply,
      pi.smul_apply],
end-/

end quotient_action

section equiv_stuff

section lemmaa

open function

-- todo: move and golf the other iterate lemmas
@[to_additive] lemma smul_iterate {G S : Type*} [monoid G] [mul_action G S] (x : G) (s : S) (n : ℕ) :
  has_scalar.smul x^[n] s = (x ^ n) • s :=
nat.rec_on n (by rw [iterate_zero, id.def, pow_zero, one_smul])
  (λ n ih, by rw [iterate_succ', comp_app, ih, pow_succ, mul_smul])

#print pow_injective_of_lt_order_of

-- todo: use this to golf lemma in `order_of_element` (pow_injective_of_lt, or something like that?)
lemma iterate_injective_of_lt_minimal_period {α : Type*} {f : α → α} {x : α}
  {m n : ℕ} (hm : m < minimal_period f x) (hn : n < minimal_period f x)
  (hf : (f^[m] x) = (f^[n] x)) :
  m = n :=
begin
  wlog h_le : m ≤ n,
  have : (f^[(minimal_period f x - n) + m] x) = x,
  by rw [iterate_add_apply, hf, ←iterate_add_apply, nat.sub_add_cancel hn.le,
    iterate_eq_mod_minimal_period, nat.mod_self, iterate_zero_apply],
  have key := is_periodic_pt.minimal_period_le (nat.add_pos_left (nat.sub_pos_of_lt hn) m) this,
  rw [←nat.sub_add_comm hn.le, le_tsub_iff_right, add_le_add_iff_left] at key,
  exact le_antisymm h_le key,
  refine hn.le.trans (nat.le_add_right _ _),
end

end lemmaa

noncomputable def orbit_zpowers_equiv
  {α β : Type*} [group α] (a : α) [mul_action α β] (b : β) :
  mul_action.orbit (subgroup.zpowers a) b ≃ zmod (function.minimal_period ((•) a) b) :=
equiv.symm (equiv.of_bijective (λ k, (⟨a, subgroup.mem_zpowers a⟩ : subgroup.zpowers a) ^ (k : ℤ) •
  ⟨b, mul_action.mem_orbit_self b⟩) begin
  let a' : subgroup.zpowers a := ⟨a, subgroup.mem_zpowers a⟩,
  let b' : mul_action.orbit α b := ⟨b, mul_action.mem_orbit_self b⟩,
  have key : function.minimal_period ((•) a) b = function.minimal_period ((•) a') b',
  { sorry },
  -- ^ this stuff might not be necessary ^ --
  split,
  { intros k k' h,
    replace h : a ^ (k : ℤ) • b = a ^ (k' : ℤ) • b := subtype.ext_iff.mp h,
    rw [←smul_iterate, ←smul_iterate] at h,
    refine iterate_injective_of_lt_minimal_period _ _ h,
    sorry },
  { rintros ⟨-, ⟨-, k, rfl⟩, rfl⟩,
    refine ⟨k, subtype.ext _⟩,
    change a ^ (k : zmod _).val • b = a ^ k • b,
    sorry },
end)

lemma orbit_zpowers_equiv_symm_apply {α β : Type*} [group α] (a : α) [mul_action α β] (b : β)
  (k : zmod (function.minimal_period ((•) a) b)) :
  (orbit_zpowers_equiv a b).symm k =
  (⟨a, subgroup.mem_zpowers a⟩ : subgroup.zpowers a) ^ (k : ℤ) • ⟨b, mul_action.mem_orbit_self b⟩ :=
rfl

universe u

noncomputable def key_equiv {G : Type u} [group G] (H : subgroup G) (g : G) :
  G ⧸ H ≃ Σ (q : quotient (mul_action.orbit_rel (subgroup.zpowers g) (G ⧸ H))),
  zmod (function.minimal_period ((•) g) q.out') :=
(mul_action.self_equiv_sigma_orbits (subgroup.zpowers g) (G ⧸ H)).trans
  (equiv.sigma_congr_right (λ q, orbit_zpowers_equiv g q.out'))

lemma key_equiv_symm_apply {G : Type u} [group G] (H : subgroup G) (g : G)
  (q : quotient (mul_action.orbit_rel (subgroup.zpowers g) (G ⧸ H)))
  (k : zmod (function.minimal_period ((•) g) q.out')) :
  (key_equiv H g).symm ⟨q, k⟩ = g ^ (k : ℤ) • q.out' :=
rfl

end equiv_stuff

section transversal_stuff

def key_transversal {G : Type*} [group G] (H : subgroup G) (g : G) : subgroup.left_transversals (H : set G) :=
⟨set.range (λ q, g ^ ((key_equiv H g q).2 : ℤ) * (key_equiv H g q).1.out'.out'),
  subgroup.range_mem_left_transversals (λ q, by rw [←smul_eq_mul, coe_smul_out',
    ←key_equiv_symm_apply, sigma.eta, equiv.symm_apply_apply])⟩

lemma key_transversal_apply {G : Type*} [group G] (H : subgroup G) (g : G) (q : G ⧸ H) :
  ↑(subgroup.mem_left_transversals.to_equiv (key_transversal H g).2 q) =
    g ^ ((key_equiv H g q).2 : ℤ) * (key_equiv H g q).1.out'.out' :=
subgroup.mem_left_transversals.range_to_equiv_apply (λ q, by rw [←smul_eq_mul, coe_smul_out',
  ←key_equiv_symm_apply, sigma.eta, equiv.symm_apply_apply]) q

lemma key_transversal_apply' {G : Type*} [group G] (H : subgroup G)
  (g : G) (q : quotient (mul_action.orbit_rel (subgroup.zpowers g) (G ⧸ H)))
  (k : zmod (function.minimal_period ((•) g) q.out')) :
  ↑(subgroup.mem_left_transversals.to_equiv (key_transversal H g).2 (g ^ (k : ℤ) • q.out')) =
    g ^ (k : ℤ) * q.out'.out' :=
by rw [←key_equiv_symm_apply, key_transversal_apply, equiv.apply_symm_apply]

lemma key_transversal_apply'' {G : Type*} [group G] (H : subgroup G)
  (g : G) (q : quotient (mul_action.orbit_rel (subgroup.zpowers g) (G ⧸ H)))
  (k : zmod (function.minimal_period ((•) g) q.out')) :
  ↑(subgroup.mem_left_transversals.to_equiv (g • key_transversal H g).2 (g ^ k.val • q.out')) =
    if k = 0 then g ^ (function.minimal_period ((•) g) q.out') * q.out'.out'
      else g ^ (k : ℤ) * q.out'.out' :=
begin
  rw subgroup.smul_apply_eq_smul_apply_inv_smul,
  rw key_transversal_apply,
  sorry
end

end transversal_stuff

open_locale big_operators

variables {G : Type*} [group G] {H : subgroup G} {A : Type*} [comm_group A] (ϕ : H →* A)

namespace subgroup

namespace left_transversals

open finset mul_action

open_locale pointwise

variables (R S T : left_transversals (H : set G)) [fintype (G ⧸ H)]

/-- The difference of two left transversals -/
@[to_additive "The difference of two left transversals"]
noncomputable def diff : A :=
let α := mem_left_transversals.to_equiv S.2, β := mem_left_transversals.to_equiv T.2 in
∏ q, ϕ ⟨(α q)⁻¹ * β q, quotient.exact' ((α.symm_apply_apply q).trans (β.symm_apply_apply q).symm)⟩

@[to_additive] lemma diff_mul_diff : diff ϕ R S * diff ϕ S T = diff ϕ R T :=
prod_mul_distrib.symm.trans (prod_congr rfl (λ q hq, (ϕ.map_mul _ _).symm.trans (congr_arg ϕ
  (by simp_rw [subtype.ext_iff, coe_mul, coe_mk, mul_assoc, mul_inv_cancel_left]))))

@[to_additive] lemma diff_self : diff ϕ T T = 1 :=
mul_right_eq_self.mp (diff_mul_diff ϕ T T T)

@[to_additive] lemma diff_inv : (diff ϕ S T)⁻¹ = diff ϕ T S :=
inv_eq_of_mul_eq_one ((diff_mul_diff ϕ S T S).trans (diff_self ϕ S))

@[to_additive] lemma smul_diff_smul (g : G) : diff ϕ (g • S) (g • T) = diff ϕ S T :=
prod_bij' (λ q _, g⁻¹ • q) (λ _ _, mem_univ _) (λ _ _, congr_arg ϕ (by simp_rw [coe_mk,
  smul_apply_eq_smul_apply_inv_smul, smul_eq_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]))
  (λ q _, g • q) (λ _ _, mem_univ _) (λ q _, smul_inv_smul g q) (λ q _, inv_smul_smul g q)

end left_transversals

end subgroup

namespace monoid_hom

variables [fintype (G ⧸ H)]

open subgroup subgroup.left_transversals

/-- Given `ϕ : H →* A` from `H : subgroup G` to a commutative group `A`,
the transfer homomorphism is `transfer ϕ : G →* A`. -/
@[to_additive "Given `ϕ : H →+ A` from `H : add_subgroup G` to an additive commutative group `A`,
the transfer homomorphism is `transfer ϕ : G →+ A`."]
noncomputable def transfer : G →* A :=
let T : left_transversals (H : set G) := inhabited.default in
{ to_fun := λ g, diff ϕ T (g • T),
  map_one' := by rw [one_smul, diff_self],
  map_mul' := λ g h, by rw [mul_smul, ←diff_mul_diff, smul_diff_smul] }

variables (T : left_transversals (H : set G))

@[to_additive] lemma transfer_def (g : G) : transfer ϕ g = diff ϕ T (g • T) :=
by rw [transfer, ←diff_mul_diff, ←smul_diff_smul, mul_comm, diff_mul_diff]; refl

section explicit_computation

variables (H)

open_locale classical

lemma transfer_computation (g : G) : transfer ϕ g =
  ∏ (q : quotient (mul_action.orbit_rel (zpowers g) (G ⧸ H))),
    ϕ ⟨q.out'.out'⁻¹ * g ^ (function.minimal_period ((•) g) q.out') * q.out'.out', sorry⟩ :=
begin
  haveI : ∀ q : quotient (mul_action.orbit_rel (zpowers g) (G ⧸ H)), fintype
    (zmod (function.minimal_period ((•) g) q.out')) := sorry,
  calc transfer ϕ g = ∏ (q : G ⧸ H), _ : transfer_def ϕ (key_transversal H g) g
  ... = _ : ((key_equiv H g).symm.prod_comp _).symm
  ... = _ : finset.prod_sigma _ _ _
  ... = _ : fintype.prod_congr _ _ (λ q, _),
  simp only [key_equiv_symm_apply, key_transversal_apply', key_transversal_apply''],
  rw fintype.prod_eq_single (0 : zmod _),
  { simp only [if_pos, ←mul_assoc, zmod.val_zero, pow_zero, one_mul], },
  { intros k hk,
    simp only [if_neg hk, inv_mul_self],
    exact ϕ.map_one },
  by apply_instance,
end

end explicit_computation

section explicit_computation

lemma _root_.subgroup.pow_index_mem
  {G : Type*} [group G] (H : subgroup G) [H.normal] [fintype (G ⧸ H)] (g : G) :
  g ^ H.index ∈ H :=
begin
  rw [←quotient_group.eq_one_iff, quotient_group.coe_pow, index_eq_card, pow_card_eq_one],
end

lemma _root_.subgroup.pow_index_mem_of_le_center
  {G : Type*} [group G] (H : subgroup G) (hH : H ≤ center G) [fintype (G ⧸ H)] (g : G) :
  g ^ H.index ∈ H :=
begin
  haveI : normal H := sorry,
  exact H.pow_index_mem g,
end


lemma transfer_eq_pow [fintype (G ⧸ H)] (hH : H ≤ center G) [fintype (G ⧸ H)] (g : G) :
  transfer ϕ g = ϕ ⟨g ^ H.index, H.pow_index_mem_of_le_center hH g⟩ :=
begin
  rw transfer_computation,
  sorry,
end

noncomputable def transfer_pow (hH : H ≤ center G) [fintype (G ⧸ H)] : G →* H :=
{ to_fun := λ g, ⟨g ^ H.index, H.pow_index_mem_of_le_center hH g⟩,
  map_one' := subtype.ext (one_pow H.index),
  map_mul' := λ a b, begin
    letI : is_commutative H := ⟨⟨λ a b, subtype.ext (hH b.2 a)⟩⟩,
    simp_rw [←show ∀ g, (_ : H) = ⟨_, _⟩, from transfer_eq_pow (id H) hH, map_mul],
  end }

noncomputable def transfer_pow' (hH : H ≤ center G) (hH₀ : H.index ≠ 0) : G →* H :=
begin
  haveI : fintype (G ⧸ H) := fintype_of_index_ne_zero hH₀,
  exact transfer_pow hH,
end

end explicit_computation

end monoid_hom
