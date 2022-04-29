/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import data.zmod.quotient
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

section equiv_stuff

open add_subgroup add_monoid_hom add_equiv add_action quotient_add_group quotient function

variables {α β : Type*} [add_group α] (a : α) [add_action α β] (b : β)

-- PRed
noncomputable def zmultiples_quotient_stabilizer_equiv :
  zmultiples a ⧸ stabilizer (zmultiples a) b ≃+ zmod (minimal_period ((+ᵥ) a) b) :=
(symm (of_bijective (map _ (stabilizer (zmultiples a) b)
  (zmultiples_hom (zmultiples a) ⟨a, mem_zmultiples a⟩) (by
  { rw [zmultiples_le, mem_comap, mem_stabilizer_iff,
        zmultiples_hom_apply, coe_nat_zsmul, ←vadd_iterate],
    exact is_periodic_pt_minimal_period ((+ᵥ) a) b })) ⟨(ker_eq_bot_iff _).mp (le_bot_iff.mp
    (λ q, induction_on' q (λ n hn, (eq_zero_iff n).mpr (int.mem_zmultiples_iff.mpr
    (zsmul_vadd_eq_iff_minimal_period_dvd.mp ((eq_zero_iff _).mp hn)))))),
    λ q, induction_on' q (λ ⟨_, n, rfl⟩, ⟨n, rfl⟩)⟩)).trans
  (int.quotient_zmultiples_nat_equiv_zmod (minimal_period ((+ᵥ) a) b))

-- PRed
lemma zmultiples_quotient_stabilizer_equiv_symm_apply (n : zmod (minimal_period ((+ᵥ) a) b)) :
  (zmultiples_quotient_stabilizer_equiv a b).symm n =
    (n : ℤ) • (⟨a, mem_zmultiples a⟩ : zmultiples a) :=
rfl

end equiv_stuff

section equiv_stuff

instance nice_instance {α β : Type*} [monoid α] [mul_action α β] : add_action (additive α) β :=
{ vadd := (•) ∘ additive.to_mul,
  zero_vadd := one_smul α,
  add_vadd := mul_smul }

noncomputable def zpowers_quotient_stabilizer_equiv
  {α β : Type*} [group α] (a : α) [mul_action α β] (b : β) :
  subgroup.zpowers a ⧸ mul_action.stabilizer (subgroup.zpowers a) b ≃*
  multiplicative (zmod (function.minimal_period ((•) a) b)) :=
let f := zmultiples_quotient_stabilizer_equiv (additive.of_mul a) b in
⟨f.to_fun, f.inv_fun, f.left_inv, f.right_inv, f.map_add'⟩

noncomputable def orbit_zpowers_equiv
  {α β : Type*} [group α] (a : α) [mul_action α β] (b : β) :
  mul_action.orbit (subgroup.zpowers a) b ≃ zmod (function.minimal_period ((•) a) b) :=
begin
  refine (mul_action.orbit_equiv_quotient_stabilizer (subgroup.zpowers a) b).trans _,
  exact (zpowers_quotient_stabilizer_equiv a b).to_equiv,
end

noncomputable def orbit_zmultiples_equiv
  {α β : Type*} [add_group α] (a : α) [add_action α β] (b : β) :
  add_action.orbit (add_subgroup.zmultiples a) b ≃ zmod (function.minimal_period ((+ᵥ) a) b) :=
begin
  refine (add_action.orbit_equiv_quotient_stabilizer (add_subgroup.zmultiples a) b).trans _,
  exact (zmultiples_quotient_stabilizer_equiv a b).to_equiv,
end

attribute [to_additive orbit_zmultiples_equiv] orbit_zpowers_equiv

@[to_additive orbit_zmultiples_equiv_symm_apply]
lemma orbit_zpowers_equiv_symm_apply {α β : Type*} [group α] (a : α) [mul_action α β] (b : β)
  (k : zmod (function.minimal_period ((•) a) b)) :
  (orbit_zpowers_equiv a b).symm k =
  (⟨a, subgroup.mem_zpowers a⟩ : subgroup.zpowers a) ^ (k : ℤ) • ⟨b, mul_action.mem_orbit_self b⟩ :=
rfl

lemma zmod.coe_eq_mod {n : ℕ} (k : ℤ) : ((k : zmod n) : ℤ) = k % n :=
begin
  cases n,
  { rw [int.coe_nat_zero, int.mod_zero, int.cast_id, int.cast_id] },
  { rw [←zmod.val_int_cast, ←int.nat_cast_eq_coe_nat],
    refl },
end

lemma orbit_zpowers_equiv_symm_apply' {α β : Type*} [group α] (a : α) [mul_action α β] (b : β)
  (k : ℤ) :
  (orbit_zpowers_equiv a b).symm k =
  (⟨a, subgroup.mem_zpowers a⟩ : subgroup.zpowers a) ^ k • ⟨b, mul_action.mem_orbit_self b⟩ :=
begin
  conv_rhs { rw ← int.mod_add_div k (function.minimal_period ((•) a) b) },
  rw [zpow_add, mul_smul, orbit_zpowers_equiv_symm_apply, zmod.coe_eq_mod, smul_left_cancel_iff,
      eq_comm, subtype.ext_iff, mul_action.orbit.coe_smul, subtype.coe_mk,
      mul_action.zpow_smul_eq_iff_minimal_period_dvd],
  apply dvd_mul_right,
end

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

lemma key_equiv_apply {G : Type u} [group G] (H : subgroup G) (g : G)
  (q : quotient (mul_action.orbit_rel (subgroup.zpowers g) (G ⧸ H)))
  (k : ℤ) :
  key_equiv H g (g ^ k • q.out') = ⟨q, k⟩ :=
begin
  rw [equiv.apply_eq_iff_eq_symm_apply, key_equiv_symm_apply],
  rw [←inv_smul_eq_iff, ←zpow_neg_one, ←zpow_mul, mul_neg_one, ←mul_smul, ←zpow_add, add_comm,
    ←sub_eq_add_neg, mul_action.zpow_smul_eq_iff_minimal_period_dvd, ←zmod.int_coe_eq_int_coe_iff_dvd_sub],
  rw [zmod.int_cast_cast, zmod.cast_int_cast'],
end

end equiv_stuff

section transversal_stuff

def key_transversal_set {G : Type*} [group G] (H : subgroup G) (g : G) :
  set G :=
set.range (λ q, g ^ ((key_equiv H g q).2 : ℤ)  * (key_equiv H g q).1.out'.out')

def key_transversal {G : Type*} [group G] (H : subgroup G) (g : G) : subgroup.left_transversals (H : set G) :=
⟨key_transversal_set H g, subgroup.range_mem_left_transversals (λ q, by rw [←smul_eq_mul,
  mul_action.quotient.coe_smul_out', ←key_equiv_symm_apply, sigma.eta, equiv.symm_apply_apply])⟩

lemma key_transversal_apply {G : Type*} [group G] (H : subgroup G) (g : G) (q : G ⧸ H) :
  ↑(subgroup.mem_left_transversals.to_equiv (key_transversal H g).2 q) =
    g ^ ((key_equiv H g q).2 : ℤ) * (key_equiv H g q).1.out'.out' :=
subgroup.mem_left_transversals.range_to_equiv_apply (λ q, by rw [←smul_eq_mul,  mul_action.quotient.coe_smul_out',
  ←key_equiv_symm_apply, sigma.eta, equiv.symm_apply_apply]) q

lemma key_transversal_apply' {G : Type*} [group G] (H : subgroup G)
  (g : G) (q : quotient (mul_action.orbit_rel (subgroup.zpowers g) (G ⧸ H)))
  (k : zmod (function.minimal_period ((•) g) q.out')) :
  ↑(subgroup.mem_left_transversals.to_equiv (key_transversal H g).2 (g ^ (k : ℤ) • q.out')) =
    g ^ (k : ℤ) * q.out'.out' :=
by rw [key_transversal_apply, ←key_equiv_symm_apply, equiv.apply_symm_apply]

lemma zmod.cast_sub_one {R : Type*} [ring R] {n : ℕ} (k : zmod n) :
  ((k - 1 : zmod n) : R) = (if k = 0 then n else k) - 1 :=
begin
  by_cases hk : k = 0,
  { rw [if_pos hk, hk, zero_sub, zmod.cast_neg_one] },
  { rw [if_neg hk],
    cases n,
    { rw [int.cast_sub, int.cast_one] },
    { rw [←zmod.nat_cast_val, zmod.val, fin.coe_sub_one, if_neg],
      { rw [nat.cast_sub, nat.cast_one, coe_coe],
        exact nat.one_le_iff_ne_zero.mpr (mt k.val_eq_zero.mp hk) },
      { exact hk } } },
end

lemma key_transversal_apply'' {G : Type*} [group G] (H : subgroup G)
  (g : G) (q : quotient (mul_action.orbit_rel (subgroup.zpowers g) (G ⧸ H)))
  (k : zmod (function.minimal_period ((•) g) q.out')) :
  ↑(subgroup.mem_left_transversals.to_equiv (g • key_transversal H g).2 (g ^ (k : ℤ) • q.out')) =
    if k = 0 then g ^ function.minimal_period ((•) g) q.out' * q.out'.out'
      else g ^ (k : ℤ) * q.out'.out' :=
begin
  rw [subgroup.smul_apply_eq_smul_apply_inv_smul, key_transversal_apply, ←mul_smul, ←zpow_neg_one,
      ←zpow_add, key_equiv_apply, smul_eq_mul, ←mul_assoc, ←zpow_one_add,
      int.cast_add, int.cast_neg, int.cast_one, zmod.int_cast_cast, zmod.cast_id', id.def],

  rw [←sub_eq_neg_add, zmod.cast_sub_one, add_sub_cancel'_right],
  by_cases hk : k = 0,
  { rw [if_pos hk, if_pos hk, int.nat_cast_eq_coe_nat, zpow_coe_nat] },
  { rw [if_neg hk, if_neg hk] },
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

instance : infinite (zmod 0) :=
int.infinite

lemma _root_.zmod.card' {n : ℕ} [fintype (zmod n)] : fintype.card (zmod n) = n :=
begin
  casesI n,
  { exact (not_fintype (zmod 0)).elim },
  { convert fintype.card_fin n.succ },
end

@[to_additive] lemma lem0 {α β : Type*} [group α] [mul_action α β] (a : α) (b : β)
  [fintype (mul_action.orbit (zpowers a) b)] :
  function.minimal_period ((•) a) b = fintype.card (mul_action.orbit (zpowers a) b) :=
begin
  rw [←fintype.of_equiv_card (orbit_zpowers_equiv a b), zmod.card'],
end

@[to_additive] instance {α β : Type*} [group α] [mul_action α β] (a : α) (b : β)
  [fintype (mul_action.orbit (zpowers a) b)] :
  fact (0 < function.minimal_period ((•) a) b) :=
⟨begin
  rw lem0,
  exact fintype.card_pos_iff.mpr ⟨⟨b, mul_action.mem_orbit_self b⟩⟩,
end⟩

open_locale classical

lemma transfer_computation (g : G) : transfer ϕ g =
  ∏ (q : quotient (mul_action.orbit_rel (zpowers g) (G ⧸ H))),
    ϕ ⟨q.out'.out'⁻¹ * g ^ (function.minimal_period ((•) g) q.out') * q.out'.out', sorry⟩ :=
begin
  calc transfer ϕ g = ∏ (q : G ⧸ H), _ : transfer_def ϕ (key_transversal H g) g
  ... = _ : ((key_equiv H g).symm.prod_comp _).symm
  ... = _ : finset.prod_sigma _ _ _
  ... = _ : fintype.prod_congr _ _ (λ q, _),
  simp only,
  simp only [key_equiv_symm_apply, key_transversal_apply', key_transversal_apply''],
  rw fintype.prod_eq_single (0 : zmod (function.minimal_period ((•) g) q.out')),
  { simp only [if_pos, zmod.cast_zero, zpow_zero, one_mul, mul_assoc] },
  { intros k hk,
    simp only [if_neg hk, inv_mul_self],
    exact ϕ.map_one },
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
  haveI : normal H := ⟨λ h hh g, by rwa [hH hh, mul_inv_cancel_right]⟩,
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
