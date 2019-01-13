/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import group_theory.order_of_element data.zmod.basic algebra.pi_instances group_theory.group_action

open equiv fintype finset is_group_action is_monoid_action function equiv.perm is_subgroup list quotient_group
universes u v w
variables {G : Type u} {α : Type v} {β : Type w} [group G]

local attribute [instance, priority 0] subtype.fintype set_fintype classical.prop_decidable

namespace is_group_action
variables (f : G → α → α) [is_group_action f]

lemma mem_fixed_points_iff_card_orbit_eq_one {f : G → α → α} [is_group_action f] {a : α}
  [fintype (orbit f a)] : a ∈ fixed_points f ↔ card (orbit f a) = 1 :=
begin
  rw [fintype.card_eq_one_iff, mem_fixed_points],
  split,
  { exact λ h, ⟨⟨a, mem_orbit_self _ _⟩, λ ⟨b, ⟨x, hx⟩⟩, subtype.eq $ by simp [h x, hx.symm]⟩ },
  { assume h x,
    rcases h with ⟨⟨z, hz⟩, hz₁⟩,
    exact calc f x a = z : subtype.mk.inj (hz₁ ⟨f x a, mem_orbit _ _ _⟩)
      ... = a : (subtype.mk.inj (hz₁ ⟨a, mem_orbit_self _ _⟩)).symm }
end

lemma card_modeq_card_fixed_points [fintype α] [fintype G] [fintype (fixed_points f)]
  {p n : ℕ} (hp : nat.prime p) (h : card G = p ^ n) : card α ≡ card (fixed_points f) [MOD p] :=
calc card α = card (Σ y : quotient (orbit_rel f), {x // quotient.mk' x = y}) :
  card_congr (equiv_fib (@quotient.mk' _ (orbit_rel f)))
... = univ.sum (λ a : quotient (orbit_rel f), card {x // quotient.mk' x = a}) : card_sigma _
... ≡ (@univ (fixed_points f) _).sum (λ _, 1) [MOD p] :
begin
  rw [← zmodp.eq_iff_modeq_nat hp, sum_nat_cast, sum_nat_cast],
  refine eq.symm (sum_bij_ne_zero (λ a _ _, quotient.mk' a.1)
    (λ _ _ _, mem_univ _)
    (λ a₁ a₂ _ _ _ _ h,
      subtype.eq (mem_fixed_points'.1 a₂.2 a₁.1 (quotient.exact' h)))
      (λ b, _)
      (λ a ha _, by rw [← mem_fixed_points_iff_card_orbit_eq_one.1 a.2];
        simp only [quotient.eq']; congr)),
  { refine quotient.induction_on' b (λ b _ hb, _),
    have : card (orbit f b) ∣ p ^ n,
    { rw [← h, fintype.card_congr (orbit_equiv_quotient_stabilizer f b)];
      exact card_quotient_dvd_card _ },
    rcases (nat.dvd_prime_pow hp).1 this with ⟨k, _, hk⟩,
    have hb' :¬ p ^ 1 ∣ p ^ k,
    { rw [nat.pow_one, ← hk, ← nat.modeq.modeq_zero_iff, ← zmodp.eq_iff_modeq_nat hp,
        nat.cast_zero, ← ne.def],
      exact eq.mpr (by simp only [quotient.eq']; congr) hb },
    have : k = 0 := nat.le_zero_iff.1 (nat.le_of_lt_succ (lt_of_not_ge (mt (nat.pow_dvd_pow p) hb'))),
    refine ⟨⟨b, mem_fixed_points_iff_card_orbit_eq_one.2 $ by rw [hk, this, nat.pow_zero]⟩, mem_univ _,
      by simp [zero_ne_one], rfl⟩ }
end
... = _ : by simp; refl

end is_group_action

lemma quotient_group.card_preimage_mk [fintype G] (s : set G) [is_subgroup s]
  (t : set (quotient s)) : fintype.card (quotient_group.mk ⁻¹' t) =
  fintype.card s * fintype.card t :=
by rw [← fintype.card_prod, fintype.card_congr
  (preimage_mk_equiv_subgroup_times_set _ _)]

namespace sylow

def mk_vector_prod_eq_one (n : ℕ) (v : vector G n) : vector G (n+1) :=
v.to_list.prod⁻¹ :: v

lemma mk_vector_prod_eq_one_inj (n : ℕ) : injective (@mk_vector_prod_eq_one G _ n) :=
λ ⟨v, _⟩ ⟨w, _⟩ h, subtype.eq (show v = w, by injection h with h; injection h)

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
    rw [← mul_right_inj v.tail.to_list.prod, inv_mul_self, ← list.prod_cons,
      ← vector.to_list_cons, vector.cons_head_tail, h]
  end⟩,
  λ ⟨w, hw⟩, by rw [mem_vectors_prod_eq_one, ← hw, mk_vector_prod_eq_one,
    vector.to_list_cons, list.prod_cons, inv_mul_self]⟩

def rotate_vectors_prod_eq_one (G : Type*) [group G] (n : ℕ+) (m : multiplicative (zmod n))
  (v : vectors_prod_eq_one G n) : vectors_prod_eq_one G n :=
⟨⟨v.1.to_list.rotate m.1, by simp⟩, prod_rotate_eq_one_of_prod_eq_one v.2 _⟩

instance rotate_vectors_prod_eq_one.is_group_action (n : ℕ+) :
  is_group_action (rotate_vectors_prod_eq_one G n) :=
{to_is_monoid_action := ⟨λ v, subtype.eq $ vector.eq _ _ $ rotate_zero v.1.to_list,
  λ a b ⟨⟨v, hv₁⟩, hv₂⟩, subtype.eq $ vector.eq _ _ $
    show v.rotate ((a + b : zmod n).val) = list.rotate (list.rotate v (b.val)) (a.val),
    by rw [zmod.add_val, rotate_rotate, ← rotate_mod _ (b.1 + a.1), add_comm, hv₁]⟩}

lemma one_mem_vectors_prod_eq_one (n : ℕ) : vector.repeat (1 : G) n ∈ vectors_prod_eq_one G n :=
by simp [vector.repeat, vectors_prod_eq_one]

lemma one_mem_fixed_points_rotate (n : ℕ+) :
  (⟨vector.repeat (1 : G) n, one_mem_vectors_prod_eq_one n⟩ : vectors_prod_eq_one G n) ∈
  fixed_points (rotate_vectors_prod_eq_one G n) :=
λ m, subtype.eq $ vector.eq _ _ $
by haveI : nonempty G := ⟨1⟩; exact
rotate_eq_self_iff_eq_repeat.2 ⟨(1 : G),
  show list.repeat (1 : G) n = list.repeat 1 (list.repeat (1 : G) n).length, by simp⟩ _

/-- Cauchy's theorem -/
lemma exists_prime_order_of_dvd_card [fintype G] {p : ℕ} (hp : nat.prime p)
  (hdvd : p ∣ card G) : ∃ x : G, order_of x = p :=
let n : ℕ+ := ⟨p - 1, nat.sub_pos_of_lt hp.gt_one⟩ in
let p' : ℕ+ := ⟨p, hp.pos⟩ in
have hn : p' = n + 1 := subtype.eq (nat.succ_sub hp.pos),
have hcard : card (vectors_prod_eq_one G (n + 1)) = card G ^ (n : ℕ),
  by rw [set.ext mem_vectors_prod_eq_one_iff,
    set.card_range_of_injective (mk_vector_prod_eq_one_inj _), card_vector],
have hzmod : fintype.card (multiplicative (zmod p')) =
  (p' : ℕ) ^ 1 := (nat.pow_one p').symm ▸ card_fin _,
have hmodeq : _ = _ := @is_group_action.card_modeq_card_fixed_points _ _ _
  (rotate_vectors_prod_eq_one G p') _ _ _ _ _ 1 hp hzmod,
have hdvdcard : p ∣ fintype.card (vectors_prod_eq_one G (n + 1)) :=
  calc p ∣ card G ^ 1 : by rwa nat.pow_one
  ... ∣ card G ^ (n : ℕ) : nat.pow_dvd_pow _ n.2
  ... = card (vectors_prod_eq_one G (n + 1)) : hcard.symm,
have hdvdcard₂ : p ∣ card (fixed_points (rotate_vectors_prod_eq_one G p')) :=
  nat.dvd_of_mod_eq_zero (hmodeq ▸ hn.symm ▸ nat.mod_eq_zero_of_dvd hdvdcard),
have hcard_pos : 0 < card (fixed_points (rotate_vectors_prod_eq_one G p')) :=
  fintype.card_pos_iff.2 ⟨⟨⟨vector.repeat 1 p', one_mem_vectors_prod_eq_one _⟩,
    one_mem_fixed_points_rotate _⟩⟩,
have hlt : 1 < card (fixed_points (rotate_vectors_prod_eq_one G p')) :=
  calc (1 : ℕ) < p' : hp.gt_one
  ... ≤ _ : nat.le_of_dvd hcard_pos hdvdcard₂,
let ⟨⟨⟨⟨x, hx₁⟩, hx₂⟩, hx₃⟩, hx₄⟩ := fintype.exists_ne_of_card_gt_one hlt
  ⟨_, one_mem_fixed_points_rotate p'⟩ in
have hx : x ≠ list.repeat (1 : G) p', from λ h, by simpa [h, vector.repeat] using hx₄,
have nG : nonempty G, from ⟨1⟩,
have ∃ a, x = list.repeat a x.length := by exactI rotate_eq_self_iff_eq_repeat.1 (λ n,
  have list.rotate x (n : zmod p').val = x :=
    subtype.mk.inj (subtype.mk.inj (hx₃ (n : zmod p'))),
  by rwa [zmod.val_cast_nat, ← hx₁, rotate_mod] at this),
let ⟨a, ha⟩ := this in
⟨a, have hx1 : x.prod = 1 := hx₂,
  have ha1: a ≠ 1, from λ h, hx (ha.symm ▸ h ▸ hx₁ ▸ rfl),
  have a ^ p = 1, by rwa [ha, list.prod_repeat, hx₁] at hx1,
  (hp.2 _ (order_of_dvd_of_pow_eq_one this)).resolve_left
    (λ h, ha1 (order_of_eq_one_iff.1 h))⟩

end sylow
