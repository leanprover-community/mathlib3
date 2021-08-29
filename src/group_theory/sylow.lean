/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import group_theory.group_action
import group_theory.quotient_group
import group_theory.order_of_element
import data.zmod.basic
import data.fintype.card
import data.list.rotate
import group_theory.p_group

/-!
# Sylow theorems

The Sylow theorems are the following results for every finite group `G` and every prime number `p`.

* There exists a Sylow `p`-subgroup of `G`.
* All Sylow `p`-subgroups of `G` are conjugate to each other.
* Let `nₚ` be the number of Sylow `p`-subgroups of `G`, then `nₚ` divides the index of the Sylow
  `p`-subgroup, `nₚ ≡ 1 [MOD p]`, and `nₚ` is equal to the index of the normalizer of the Sylow
  `p`-subgroup in `G`.

In this file, currently only the first of these results is proven.

## Main statements

* `exists_prime_order_of_dvd_card`: For every prime `p` dividing the order of `G` there exists an
  element of order `p` in `G`. This is known as Cauchy`s theorem.
* `exists_subgroup_card_pow_prime`: A generalisation of the first of the Sylow theorems: For every
  prime power `pⁿ` dividing `G`, there exists a subgroup of `G` of order `pⁿ`.

## TODO

* Prove the second and third of the Sylow theorems.
* Sylow theorems for infinite groups
-/

open equiv fintype finset mul_action function
open equiv.perm subgroup list quotient_group
open_locale big_operators
universes u v w
variables {G : Type u} {α : Type v} {β : Type w} [group G]

local attribute [instance, priority 10] subtype.fintype set_fintype classical.prop_decidable

lemma quotient_group.card_preimage_mk [fintype G] (s : subgroup G)
  (t : set (quotient s)) : fintype.card (quotient_group.mk ⁻¹' t) =
  fintype.card s * fintype.card t :=
by rw [← fintype.card_prod, fintype.card_congr
  (preimage_mk_equiv_subgroup_times_set _ _)]

namespace sylow

/-- Given a vector `v` of length `n`, make a vector of length `n+1` whose product is `1`,
by consing the the inverse of the product of `v`. -/
def mk_vector_prod_eq_one (n : ℕ) (v : vector G n) : vector G (n+1) :=
v.to_list.prod⁻¹ ::ᵥ v

lemma mk_vector_prod_eq_one_injective (n : ℕ) : injective (@mk_vector_prod_eq_one G _ n) :=
λ ⟨v, _⟩ ⟨w, _⟩ h, subtype.eq (show v = w, by injection h with h; injection h)

/-- The type of vectors with terms from `G`, length `n`, and product equal to `1:G`. -/
def vectors_prod_eq_one (G : Type*) [group G] (n : ℕ) : set (vector G n) :=
{v | v.to_list.prod = 1}

lemma mem_vectors_prod_eq_one {n : ℕ} (v : vector G n) :
  v ∈ vectors_prod_eq_one G n ↔ v.to_list.prod = 1 := iff.rfl

lemma mem_vectors_prod_eq_one_iff {n : ℕ} (v : vector G (n + 1)) :
  v ∈ vectors_prod_eq_one G (n + 1) ↔ v ∈ set.range (@mk_vector_prod_eq_one G _ n) :=
⟨λ (h : v.to_list.prod = 1), ⟨v.tail,
  begin
    unfold mk_vector_prod_eq_one,
    conv {to_rhs, rw ← vector.cons_head_tail v},
    suffices : (v.tail.to_list.prod)⁻¹ = v.head,
    { rw this },
    rw [← mul_left_inj v.tail.to_list.prod, inv_mul_self, ← list.prod_cons,
      ← vector.to_list_cons, vector.cons_head_tail, h]
  end⟩,
  λ ⟨w, hw⟩, by rw [mem_vectors_prod_eq_one, ← hw, mk_vector_prod_eq_one,
    vector.to_list_cons, list.prod_cons, inv_mul_self]⟩

/-- The rotation action of `zmod n` (viewed as multiplicative group) on
`vectors_prod_eq_one G n`, where `G` is a multiplicative group. -/
def rotate_vectors_prod_eq_one (G : Type*) [group G] (n : ℕ)
  (m : multiplicative (zmod n)) (v : vectors_prod_eq_one G n) : vectors_prod_eq_one G n :=
⟨⟨v.1.to_list.rotate m.val, by simp⟩, prod_rotate_eq_one_of_prod_eq_one v.2 _⟩

instance rotate_vectors_prod_eq_one.mul_action (n : ℕ) [fact (0 < n)] :
  mul_action (multiplicative (zmod n)) (vectors_prod_eq_one G n) :=
{ smul := (rotate_vectors_prod_eq_one G n),
  one_smul :=
  begin
    intro v, apply subtype.eq, apply vector.eq _ _,
    show rotate _ (0 : zmod n).val = _, rw zmod.val_zero,
    exact rotate_zero v.1.to_list
  end,
  mul_smul := λ a b ⟨⟨v, hv₁⟩, hv₂⟩, subtype.eq $ vector.eq _ _ $
    show v.rotate ((a + b : zmod n).val) = list.rotate (list.rotate v (b.val)) (a.val),
    by rw [zmod.val_add, rotate_rotate, ← rotate_mod _ (b.val + a.val), add_comm, hv₁] }

lemma one_mem_vectors_prod_eq_one (n : ℕ) : vector.repeat (1 : G) n ∈ vectors_prod_eq_one G n :=
by simp [vector.repeat, vectors_prod_eq_one]

lemma one_mem_fixed_points_rotate (n : ℕ) [fact (0 < n)] :
  (⟨vector.repeat (1 : G) n, one_mem_vectors_prod_eq_one n⟩ : vectors_prod_eq_one G n) ∈
  fixed_points (multiplicative (zmod n)) (vectors_prod_eq_one G n) :=
λ m, subtype.eq $ vector.eq _ _ $
rotate_eq_self_iff_eq_repeat.2 ⟨(1 : G),
  show list.repeat (1 : G) n = list.repeat 1 (list.repeat (1 : G) n).length, by simp⟩ _

/-- **Cauchy's theorem** -/
lemma exists_prime_order_of_dvd_card [fintype G] (p : ℕ) [hp : fact p.prime]
  (hdvd : p ∣ card G) : ∃ x : G, order_of x = p :=
have hcard : card (vectors_prod_eq_one G p) = card G ^ (p - 1),
  by conv_lhs { rw [← nat.sub_add_cancel hp.out.pos, set.ext mem_vectors_prod_eq_one_iff,
    set.card_range_of_injective (mk_vector_prod_eq_one_injective _), card_vector] },
have hzmod : fintype.card (multiplicative (zmod p)) = p ^ 1,
  by { rw pow_one p, exact zmod.card p },
have hdvdcard : p ∣ fintype.card (vectors_prod_eq_one G p) :=
  calc p ∣ card G ^ 1 : by rwa pow_one
  ... ∣ card G ^ (p - 1) : pow_dvd_pow _ (nat.le_sub_left_of_add_le hp.out.two_le)
  ... = card (vectors_prod_eq_one G p) : hcard.symm,
let ⟨⟨⟨x, hxl⟩, hx1⟩, hx, h1x⟩ := mul_action.exists_fixed_point_of_prime_dvd_card_of_fixed_point
  (vectors_prod_eq_one G p) hzmod hdvdcard
  (one_mem_fixed_points_rotate _) in
have ∃ a, x = list.repeat a x.length := by exactI rotate_eq_self_iff_eq_repeat.1 (λ n,
  have list.rotate x (n : zmod p).val = x :=
    subtype.mk.inj (subtype.mk.inj (hx (n : zmod p))),
  by rwa [zmod.val_nat_cast, ← hxl, rotate_mod] at this),
let ⟨a, ha⟩ := this in
⟨a, have hxp1 : x.prod = 1 := hx1,
  have ha1: a ≠ 1,
    from λ h, h1x (subtype.ext $ subtype.ext $
      by rw [subtype.coe_mk, subtype.coe_mk, subtype.coe_mk, ha, hxl, h,
        vector.repeat, subtype.coe_mk]),
  have a ^ p = 1, by rwa [ha, list.prod_repeat, hxl] at hxp1,
  (hp.1.2 _ (order_of_dvd_of_pow_eq_one this)).resolve_left
    (λ h, ha1 (order_of_eq_one_iff.1 h))⟩

open subgroup submonoid mul_action

lemma mem_fixed_points_mul_left_cosets_iff_mem_normalizer {H : subgroup G}
  [fintype ((H : set G) : Type u)] {x : G} :
  (x : quotient H) ∈ fixed_points H (quotient H) ↔ x ∈ normalizer H :=
⟨λ hx, have ha : ∀ {y : quotient H}, y ∈ orbit H (x : quotient H) → y = x,
  from λ _, ((mem_fixed_points' _).1 hx _),
  (inv_mem_iff _).1 (@mem_normalizer_fintype _ _ _ _inst_2 _ (λ n (hn : n ∈ H),
    have (n⁻¹ * x)⁻¹ * x ∈ H := quotient_group.eq.1 (ha (mem_orbit _ ⟨n⁻¹, H.inv_mem hn⟩)),
    show _ ∈ H, by {rw [mul_inv_rev, inv_inv] at this, convert this, rw inv_inv}
    )),
λ (hx : ∀ (n : G), n ∈ H ↔ x * n * x⁻¹ ∈ H),
(mem_fixed_points' _).2 $ λ y, quotient.induction_on' y $ λ y hy, quotient_group.eq.2
  (let ⟨⟨b, hb₁⟩, hb₂⟩ := hy in
  have hb₂ : (b * x)⁻¹ * y ∈ H := quotient_group.eq.1 hb₂,
  (inv_mem_iff H).1 $ (hx _).2 $ (mul_mem_cancel_left H (H.inv_mem hb₁)).1
  $ by rw hx at hb₂;
    simpa [mul_inv_rev, mul_assoc] using hb₂)⟩

def fixed_points_mul_left_cosets_equiv_quotient (H : subgroup G) [fintype (H : set G)] :
  mul_action.fixed_points H (quotient H) ≃
  quotient (subgroup.comap ((normalizer H).subtype : normalizer H →* G) H) :=
@subtype_quotient_equiv_quotient_subtype G (normalizer H : set G) (id _) (id _) (fixed_points _ _)
  (λ a, (@mem_fixed_points_mul_left_cosets_iff_mem_normalizer _ _ _ _inst_2 _).symm)
  (by intros; refl)

/-- If `H` is a `p`-subgroup of `G`, then the index of `H` inside its normalizer is congruent
  mod `p` to the index of `H`.  -/
lemma card_quotient_normalizer_modeq_card_quotient [fintype G] {p : ℕ} {n : ℕ} [hp : fact p.prime]
  {H : subgroup G} (hH : fintype.card H = p ^ n) :
  card (quotient (subgroup.comap ((normalizer H).subtype : normalizer H →* G) H))
  ≡ card (quotient H) [MOD p] :=
begin
  rw [← fintype.card_congr (fixed_points_mul_left_cosets_equiv_quotient H)],
  exact (card_modeq_card_fixed_points _ hH).symm
end

/-- If `H` is a subgroup of `G` of cardinality `p ^ n`, then the cardinality of the
  normalizer of `H` is congruent mod `p ^ (n + 1)` to the cardinality of `G`.  -/
lemma card_normalizer_modeq_card [fintype G] {p : ℕ} {n : ℕ} [hp : fact p.prime]
  {H : subgroup G} (hH : fintype.card H = p ^ n) :
  card (normalizer H) ≡ card G [MOD p ^ (n + 1)] :=
have subgroup.comap ((normalizer H).subtype : normalizer H →* G) H ≃ H,
  from set.bij_on.equiv (normalizer H).subtype
    ⟨λ _, id, λ _ _ _ _ h, subtype.val_injective h,
      λ x hx, ⟨⟨x, le_normalizer hx⟩, hx, rfl⟩⟩,
begin
  rw [card_eq_card_quotient_mul_card_subgroup H,
      card_eq_card_quotient_mul_card_subgroup
        (subgroup.comap ((normalizer H).subtype : normalizer H →* G) H),
      fintype.card_congr this, hH, pow_succ],
  exact (card_quotient_normalizer_modeq_card_quotient hH).mul_right' _
end

/-- If `H` is a `p`-subgroup but not a Sylow `p`-subgroup, then `p` divides the
  index of `H` inside its normalizer. -/
lemma prime_dvd_card_quotient_normalizer [fintype G] {p : ℕ} {n : ℕ} [hp : fact p.prime]
  (hdvd : p ^ (n + 1) ∣ card G) {H : subgroup G} (hH : fintype.card H = p ^ n) :
  p ∣ card (quotient (subgroup.comap ((normalizer H).subtype : normalizer H →* G) H)) :=
let ⟨s, hs⟩ := exists_eq_mul_left_of_dvd hdvd in
have hcard : card (quotient H) = s * p :=
  (nat.mul_left_inj (show card H > 0, from fintype.card_pos_iff.2
      ⟨⟨1, H.one_mem⟩⟩)).1
    (by rwa [← card_eq_card_quotient_mul_card_subgroup H, hH, hs,
      pow_succ', mul_assoc, mul_comm p]),
have hm : s * p % p =
  card (quotient (subgroup.comap ((normalizer H).subtype : normalizer H →* G) H)) % p :=
  hcard ▸ (card_quotient_normalizer_modeq_card_quotient hH).symm,
nat.dvd_of_mod_eq_zero
  (by rwa [nat.mod_eq_zero_of_dvd (dvd_mul_left _ _), eq_comm] at hm)

/-- If `H` is a `p`-subgroup but not a Sylow `p`-subgroup of cardinality `p ^ n`,
  then `p ^ (n + 1)` divides the cardinality of the normalizer of `H`. -/
lemma prime_pow_dvd_card_normalizer [fintype G] {p : ℕ} {n : ℕ} [hp : fact p.prime]
  (hdvd : p ^ (n + 1) ∣ card G) {H : subgroup G} (hH : fintype.card H = p ^ n) :
  p ^ (n + 1) ∣ card (normalizer H) :=
nat.modeq_zero_iff_dvd.1 ((card_normalizer_modeq_card hH).trans
  hdvd.modeq_zero_nat)

/-- If `H` is a subgroup of `G` of cardinality `p ^ n`,
  then `H` is contained in a subgroup of cardinality `p ^ (n + 1)`
  if `p ^ (n + 1)` divides the cardinality of `G` -/
theorem exists_subgroup_card_pow_succ [fintype G] {p : ℕ} {n : ℕ} [hp : fact p.prime]
  (hdvd : p ^ (n + 1) ∣ card G) {H : subgroup G} (hH : fintype.card H = p ^ n) :
  ∃ K : subgroup G, fintype.card K = p ^ (n + 1) ∧ H ≤ K :=
let ⟨s, hs⟩ := exists_eq_mul_left_of_dvd hdvd in
have hcard : card (quotient H) = s * p :=
  (nat.mul_left_inj (show card H > 0, from fintype.card_pos_iff.2
      ⟨⟨1, H.one_mem⟩⟩)).1
    (by rwa [← card_eq_card_quotient_mul_card_subgroup H, hH, hs,
      pow_succ', mul_assoc, mul_comm p]),
have hm : s * p % p =
  card (quotient (subgroup.comap ((normalizer H).subtype : normalizer H →* G) H)) % p :=
  card_congr (fixed_points_mul_left_cosets_equiv_quotient H) ▸ hcard ▸
    @card_modeq_card_fixed_points _ _ _ _ _ _ _ p _ hp hH,
have hm' : p ∣ card (quotient (subgroup.comap ((normalizer H).subtype : normalizer H →* G) H)) :=
  nat.dvd_of_mod_eq_zero
    (by rwa [nat.mod_eq_zero_of_dvd (dvd_mul_left _ _), eq_comm] at hm),
let ⟨x, hx⟩ := @exists_prime_order_of_dvd_card _ (quotient_group.quotient.group _) _ _ hp hm' in
have hequiv : H ≃ (subgroup.comap ((normalizer H).subtype : normalizer H →* G) H) :=
  ⟨λ a, ⟨⟨a.1, le_normalizer a.2⟩, a.2⟩, λ a, ⟨a.1.1, a.2⟩,
    λ ⟨_, _⟩, rfl, λ ⟨⟨_, _⟩, _⟩, rfl⟩,
⟨subgroup.map ((normalizer H).subtype) (subgroup.comap
  (quotient_group.mk' (comap H.normalizer.subtype H)) (gpowers x)),
begin
  show card ↥(map H.normalizer.subtype
    (comap (mk' (comap H.normalizer.subtype H)) (subgroup.gpowers x))) = p ^ (n + 1),
  suffices : card ↥(subtype.val '' ((subgroup.comap (mk' (comap H.normalizer.subtype H))
    (gpowers x)) : set (↥(H.normalizer)))) = p^(n+1),
  { convert this using 2 },
  rw [set.card_image_of_injective
        (subgroup.comap (mk' (comap H.normalizer.subtype H)) (gpowers x) : set (H.normalizer))
        subtype.val_injective,
      pow_succ', ← hH, fintype.card_congr hequiv, ← hx, order_eq_card_gpowers,
      ← fintype.card_prod],
  exact @fintype.card_congr _ _ (id _) (id _) (preimage_mk_equiv_subgroup_times_set _ _)
end,
begin
  assume y hy,
  simp only [exists_prop, subgroup.coe_subtype, mk'_apply, subgroup.mem_map, subgroup.mem_comap],
  refine ⟨⟨y, le_normalizer hy⟩, ⟨0, _⟩, rfl⟩,
  rw [gpow_zero, eq_comm, quotient_group.eq_one_iff],
  simpa using hy
end⟩

/-- If `H` is a subgroup of `G` of cardinality `p ^ n`,
  then `H` is contained in a subgroup of cardinality `p ^ m`
  if `n ≤ m` and `p ^ m` divides the cardinality of `G` -/
theorem exists_subgroup_card_pow_prime_le [fintype G] (p : ℕ) : ∀ {n m : ℕ} [hp : fact p.prime]
  (hdvd : p ^ m ∣ card G) (H : subgroup G) (hH : card H = p ^ n) (hnm : n ≤ m),
  ∃ K : subgroup G, card K = p ^ m ∧ H ≤ K
| n m := λ hp hdvd H hH hnm,
  (lt_or_eq_of_le hnm).elim
    (λ hnm : n < m,
      have h0m : 0 < m, from (lt_of_le_of_lt n.zero_le hnm),
      have wf : m - 1 < m,  from nat.sub_lt h0m zero_lt_one,
      have hnm1 : n ≤ m - 1, from nat.le_sub_right_of_add_le hnm,
      let ⟨K, hK⟩ := @exists_subgroup_card_pow_prime_le n (m - 1) hp
        (nat.pow_dvd_of_le_of_pow_dvd (nat.sub_le_self _ _) hdvd) H hH hnm1 in
      have hdvd' : p ^ ((m - 1) + 1) ∣ card G, by rwa [nat.sub_add_cancel h0m],
      let ⟨K', hK'⟩ := @exists_subgroup_card_pow_succ _ _ _ _ _ hp hdvd' K hK.1 in
      ⟨K', by rw [hK'.1, nat.sub_add_cancel h0m], le_trans hK.2 hK'.2⟩)
    (λ hnm : n = m, ⟨H, by simp [hH, hnm]⟩)

/-- A generalisation of **Sylow's first theorem**. If `p ^ n` divides
  the cardinality of `G`, then there is a subgroup of cardinality `p ^ n` -/
theorem exists_subgroup_card_pow_prime [fintype G] (p : ℕ) {n : ℕ} [fact p.prime]
  (hdvd : p ^ n ∣ card G) : ∃ K : subgroup G, fintype.card K = p ^ n :=
let ⟨K, hK⟩ := exists_subgroup_card_pow_prime_le p hdvd ⊥ (by simp) n.zero_le in
⟨K, hK.1⟩

end sylow
