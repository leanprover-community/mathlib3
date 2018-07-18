/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

Theory of univariate polynomials, represented as finsupps, ℕ →₀ α, with α a comm_semiring
-/

import data.finsupp algebra.euclidean_domain

open finsupp finset lattice

instance with_bot.nat.has_one : has_one (with_bot ℕ) := ⟨(1 : ℕ)⟩

def polynomial (α : Type*) [comm_semiring α] := ℕ →₀ α

namespace polynomial
universe u
variables {α : Type u} {a b : α} {m n : ℕ} 
variables [decidable_eq α]

section comm_semiring
variables [comm_semiring α] {p q : polynomial α}

instance : has_coe_to_fun (polynomial α) := finsupp.has_coe_to_fun
instance : has_zero (polynomial α) := finsupp.has_zero
instance : has_one (polynomial α) := finsupp.has_one
instance : has_add (polynomial α) := finsupp.has_add
instance : has_mul (polynomial α) := finsupp.has_mul
instance : comm_semiring (polynomial α) := finsupp.to_comm_semiring
instance : decidable_eq (polynomial α) := finsupp.decidable_eq

local attribute [instance] finsupp.to_comm_semiring

/-- `monomial n a` is the polynomial `a * X^n` -/
def monomial (n : ℕ) (a : α) : polynomial α := single n a

/-- `C a` is the constant polynomial a -/
def C (a : α) : polynomial α := monomial 0 a

/-- `X` is the polynomial whose evaluation is the identity funtion -/
def X : polynomial α := monomial 1 1

@[simp] lemma C_0 : C (0 : α) = 0 := by simp [C, monomial]; refl

@[simp] lemma C_1 : C (1 : α) = 1 := rfl

@[simp] lemma C_mul_monomial : C a * monomial n b = monomial n (a * b) :=
by simp [C, monomial, single_mul_single]

@[simp] lemma C_mul_C : C a * C b = C (a * b) :=
by simp [C, monomial, single_mul_single]

@[simp] lemma monomial_mul_monomial : monomial n a * monomial m b = monomial (n + m) (a * b) :=
single_mul_single

@[simp] lemma monomial_zero_right (n : ℕ) : monomial n (0 : α) = 0 := 
finsupp.ext $ λ a, show ite _ _ _ = (0 : α), by split_ifs; simp

lemma X_pow_eq_monomial : (X : polynomial α) ^ n = monomial n (1 : α) :=
by induction n; simp [X, C_1.symm, -C_1, C, pow_succ, *] at *

lemma monomial_add_right : monomial (n + m) a = (monomial n a * X ^ m) :=
by rw [X_pow_eq_monomial, monomial, monomial, monomial, single_mul_single]; simp

lemma monomial_add_left : monomial (m + n) a = (X ^ m * monomial n a) :=
by rw [X_pow_eq_monomial, monomial, monomial, monomial, single_mul_single]; simp

lemma monomial_eq : monomial n a = C a * X ^ n :=
by rw [X_pow_eq_monomial, C_mul_monomial, mul_one]

@[simp] lemma support_zero : (0 : polynomial α).support = ∅ := rfl

@[elab_as_eliminator] lemma induction_on {M : polynomial α → Prop} (p : polynomial α)
  (h_C : ∀a, M (C a)) (h_add : ∀p q, M p → M q → M (p + q)) 
  (h_X : ∀(n : ℕ) (a : α), M (monomial n a) → M (monomial n a * X)) :
  M p :=
have ∀n a, M (monomial n a),
begin
  assume n a,
  induction n with n ih,
  { exact h_C _ },
  { rw [← nat.add_one, monomial_add_right, pow_one],
    exact h_X _ _ ih }
end,
finsupp.induction p (show M (0 : polynomial α), by rw ← C_0; exact h_C 0) $ 
λ n a f hfn ha ih, (show M (monomial n a + f), from h_add _ _ (this _ _) ih)

lemma monomial_apply : (monomial n a : ℕ → α) m = ite (n = m) a 0 :=
finsupp.single_apply

@[simp] lemma monomial_apply_self : (monomial n a : ℕ → α) n = a :=
by simp [monomial_apply]

lemma C_apply : (C a : ℕ → α) n = ite (0 = n) a 0 := rfl

@[simp] lemma C_apply_zero : (C a : ℕ → α) 0 = a := rfl

@[simp] lemma zero_apply (n : ℕ) : (0 : polynomial α) n = 0 := rfl

@[simp] lemma one_apply_zero (n : ℕ) : (1 : polynomial α) 0 = 1 := rfl

@[simp] lemma  X_apply_one : (X : polynomial α) 1 = 1 := rfl

@[simp] lemma add_apply (p q : polynomial α) (n : ℕ) : (p + q) n = p n + q n := add_apply

@[simp] lemma C_mul_apply (p : polynomial α) : (C a * p) n = a * p n :=
induction_on p (λ b, show (monomial 0 a * monomial 0 b) n = a * 
  (monomial 0 b : ℕ → α) n,
  begin 
    rw [monomial_mul_monomial, monomial_apply, monomial_apply],
    split_ifs; simp
  end) 
  begin 
    intros, 
    rw [mul_add, add_apply, add_apply, mul_add], 
    simp *,
  end
  begin
    intros,
    rw [X, monomial_mul_monomial, C, monomial_mul_monomial, monomial_apply, monomial_apply],
    split_ifs;
    simp * at *,
  end

@[elab_as_eliminator] lemma monomial_induction_on {M : polynomial α → Prop} (p : polynomial α)
  (h0 : M 0) 
  (h : ∀ (n : ℕ) (a : α) (p : polynomial α), p n = 0 → a ≠ 0 → M p → 
  M (monomial n a + p)) : M p :=
finsupp.induction p h0 (λ n a p hpn, h n a p (by rwa [mem_support_iff, ne.def, not_not] at hpn))

section eval
variable {x : α}

/-- `eval x p` is the evaluation of the polynomial x at p -/
def eval (x : α) (p : polynomial α) : α :=
p.sum (λ e a, a * x ^ e)

@[simp] lemma eval_zero : (0 : polynomial α).eval x = 0 :=
finsupp.sum_zero_index

@[simp] lemma eval_add : (p + q).eval x = p.eval x + q.eval x :=
finsupp.sum_add_index (by simp) (by simp [add_mul])

@[simp] lemma eval_monomial : (monomial n a).eval x = a * x ^ n :=
finsupp.sum_single_index (zero_mul _)

@[simp] lemma eval_C : (C a).eval x = a :=
by simp [eval_monomial, C, prod_zero_index]

@[simp] lemma eval_X : X.eval x = x :=
by simp [eval_monomial, X, prod_single_index, pow_one]

@[simp] lemma eval_mul_monomial :
  ∀{n a}, (p * monomial n a).eval x = p.eval x * a * x ^ n :=
begin
  apply polynomial.induction_on p,
  { assume a' s a, by simp [C_mul_monomial, eval_monomial] },
  { assume p q ih_p ih_q, simp [add_mul, eval_add, ih_p, ih_q] },
  { assume m b ih n a,
    unfold X,
    rw [mul_assoc, ih, monomial_mul_monomial, ih, pow_add],
    simp [mul_assoc, mul_comm, mul_left_comm] }
end

@[simp] lemma eval_mul : (p * q).eval x = p.eval x * q.eval x :=
begin
  apply polynomial.induction_on q,
  { simp [C, eval_monomial, eval_mul_monomial, prod_zero_index] },
  { simp [mul_add, eval_add] {contextual := tt} },
  { simp [X, eval_monomial, eval_mul_monomial, (mul_assoc _ _ _).symm] { contextual := tt} }
end

/-- `is_root p x` implies `x` is a root of `p`. The evaluation of `p` at `x` is zero -/
def is_root (p : polynomial α) (a : α) : Prop := p.eval a = 0

instance : decidable (is_root p a) := by unfold is_root; apply_instance

@[simp] lemma is_root.def : is_root p a ↔ p.eval a = 0 := iff.rfl

lemma root_mul_left_of_is_root (p : polynomial α) {q : polynomial α} :
  is_root q a → is_root (p * q) a :=
by simp [is_root.def, eval_mul] {contextual := tt}

lemma root_mul_right_of_is_root {p : polynomial α} (q : polynomial α) :
  is_root p a → is_root (p * q) a :=
by simp [is_root.def, eval_mul] {contextual := tt}

end eval

/-- `degree` gives values in `with_bot ℕ`. `degree 0 = ⊥` and for p ≠ 0 `degree p = some n`
where `n` is the highest power of `X` that appears in `p` -/
def degree (p : polynomial α) : with_bot ℕ := p.support.sup some

def nat_degree (p : polynomial α) : ℕ := @option.iget _ ⟨0⟩ (degree p)

/-- `leading_coeff p` gives the coefficient of the highest power of `X` in `p`-/
def leading_coeff (p : polynomial α) : α := p (nat_degree p)

/-- a polynomial is `monic` if its leading coefficient is 1 -/
def monic (p : polynomial α) := leading_coeff p = (1 : α)

lemma monic.def : monic p ↔ leading_coeff p = 1 := iff.rfl

instance monic.decidable : decidable (monic p) :=
by unfold monic; apply_instance

@[simp] lemma degree_zero : degree (0 : polynomial α) = ⊥ := rfl

lemma degree_C (ha : a ≠ 0) : degree (C a) = (0 : with_bot ℕ) :=
show sup (ite (a = 0) ∅ {0}) some = 0,
by rw [if_neg ha]; refl
 
lemma degree_eq_bot : degree p = ⊥ ↔ p = 0 :=
⟨λ h, by rw [degree, ← max_eq_sup_with_bot] at h;
  exact support_eq_empty.1 (finset.max_eq_none.1 h),
λ h, h.symm ▸ rfl⟩

lemma degree_eq_nat_degree (hp : p ≠ 0) : degree p = (nat_degree p : with_bot ℕ) :=
let ⟨n, hn⟩ := classical.not_forall.1 (mt option.eq_none_iff_forall_not_mem.2 (mt degree_eq_bot.1 hp)) in
have hn : degree p = some n := not_not.1 hn,
by rw [nat_degree, hn, option.iget_some]; refl

lemma nat_degree_eq_of_degree_eq (h : degree p = degree q) : nat_degree p = nat_degree q :=
by unfold nat_degree; rw h

@[simp] lemma nat_degree_C (a : α) : nat_degree (C a) = 0 :=
if ha : a = 0 
then have C a = 0 := by simp [ha],
  by rw [nat_degree, degree_eq_bot.2 this]; refl
else by rw [nat_degree, degree_C ha]; refl

lemma degree_monomial_le (n : ℕ) (a : α) : degree (monomial n a) ≤ n :=
begin
  unfold single monomial degree finsupp.support,
  by_cases a = 0;
  simp [h];
  exact le_refl _
end

@[simp] lemma degree_monomial (n : ℕ) (ha : a ≠ 0) : degree (monomial n a) = n :=
begin
  unfold X single monomial degree finsupp.support,
  rw if_neg ha,
  refl
end

lemma le_degree_of_ne_zero (h : p n ≠ 0) : (n : with_bot ℕ) ≤ degree p :=
show @has_le.le (with_bot ℕ) _ (some n : with_bot ℕ) (p.support.sup some : with_bot ℕ),
from finset.le_sup ((finsupp.mem_support_iff _ _).2 h)

lemma eq_zero_of_degree_lt (h : degree p < n) : p n = 0 :=
not_not.1 (mt le_degree_of_ne_zero (not_le_of_gt h))

lemma ne_zero_of_degree_gt {n : with_bot ℕ} (h : n < degree p) : p ≠ 0 :=
mt degree_eq_bot.2 (ne.symm (ne_of_lt (lt_of_le_of_lt bot_le h)))

lemma eq_C_of_degree_le_zero (h : degree p ≤ 0) : p = C (p 0) :=
ext begin
  assume n,
  cases n,
  { refl },
  { have : degree p < ↑(nat.succ n) := lt_of_le_of_lt h (with_bot.some_lt_some.2 (nat.succ_pos _)),
    rw [C_apply, if_neg (nat.succ_ne_zero _).symm, eq_zero_of_degree_lt this] }
end

lemma degree_add_le (p q : polynomial α) : degree (p + q) ≤ max (degree p) (degree q) :=
calc degree (p + q) = ((p + q).support).sup some : rfl
  ... ≤ (p.support ∪ q.support).sup some : sup_mono support_add
  ... = p.support.sup some ⊔ q.support.sup some : sup_union
  ... = _ : with_bot.sup_eq_max _ _

@[simp] lemma leading_coeff_zero : leading_coeff (0 : polynomial α) = 0 := rfl

@[simp] lemma leading_coeff_eq_zero : leading_coeff p = 0 ↔ p = 0 :=
⟨λ h, by_contradiction $ λ hp, mt (mem_support_iff _ _).1
  (not_not.2 h) (mem_of_max (degree_eq_nat_degree hp)),
by simp {contextual := tt}⟩

lemma degree_add_eq_of_degree_lt (h : degree p < degree q) : degree (p + q) = degree q :=
le_antisymm (max_eq_right_of_lt h ▸ degree_add_le _ _)
  (have hq0 : q ≠ 0 := mt degree_eq_bot.2 (ne.symm (ne_of_lt (lt_of_le_of_lt bot_le h))),
  begin
    rw degree_eq_nat_degree hq0 at *,
    refine le_degree_of_ne_zero _,
    rw [add_apply, eq_zero_of_degree_lt h, zero_add],
    exact mt leading_coeff_eq_zero.1 hq0
  end)

lemma degree_add_eq_of_leading_coeff_add_ne_zero (h : leading_coeff p + leading_coeff q ≠ 0) :
  degree (p + q) = max p.degree q.degree :=
le_antisymm (degree_add_le _ _) 
((lt_trichotomy (degree p) (degree q)).elim 
(λ hlt, by rw [degree_add_eq_of_degree_lt hlt, max_eq_right_of_lt hlt];
  exact le_refl _)
(λ hlt, hlt.elim (λ heq, le_of_not_gt (λ hlt, 
  have hq : q ≠ 0 := λ hq, 
    have hp : p = 0, by simpa [hq, degree_eq_bot] using heq,
    by simpa [hp, hq] using h,
  begin 
    rw [heq, max_self, degree_eq_nat_degree hq] at hlt,
    have := eq_zero_of_degree_lt hlt,
    rw add_apply at this,
    conv at this in (p (nat_degree q)) { rw ← nat_degree_eq_of_degree_eq heq },
    exact h this,
  end)) 
(λ hlt, by rw [add_comm, degree_add_eq_of_degree_lt hlt, max_eq_left_of_lt hlt];
  exact le_refl _)))

lemma degree_erase_le (p : polynomial α) (n : ℕ) : degree (p.erase n) ≤ degree p :=
sup_mono (erase_subset _ _)

lemma degree_erase_lt (hp : p ≠ 0) : degree (p.erase (nat_degree p)) < degree p :=
lt_of_le_of_ne (degree_erase_le _ _) $ (degree_eq_nat_degree hp).symm ▸ λ h, not_mem_erase _ _ (mem_of_max h)

lemma degree_sum_le {β : Type*} [decidable_eq β] (s : finset β) (f : β → polynomial α) :
  degree (s.sum f) ≤ s.sup (degree ∘ f) :=
finset.induction_on s (by simp [finsupp.support_zero]) $ 
  assume a s has ih,
  calc degree (sum (insert a s) f) ≤ max (degree (f a)) (degree (s.sum f)) :
    by rw sum_insert has; exact degree_add_le _ _
  ... ≤ _ : by rw [sup_insert, with_bot.sup_eq_max];
    exact max_le_max (le_refl _) ih

lemma degree_mul_le (p q : polynomial α) : degree (p * q) ≤ degree p + degree q :=
calc _ ≤ sup (p.support)
      (degree ∘ λ (a : ℕ), sum q (λ (a₂ : ℕ) (b₂ : α), single (a + a₂) (p a * b₂))) : degree_sum_le _ _
  ... ≤ (sup (p.support) some : with_bot ℕ) + sup (q.support) some : 
  finset.sup_le (λ a ha, 
    calc degree (sum q (λ (a₂ : ℕ) (b₂ : α), single (a + a₂) (p a * b₂))) ≤ 
       sup (q.support) (λ b, degree (monomial (a + b) (p a * q b))) : degree_sum_le _ _
    ... ≤ sup (p.support) some + sup (q.support) some :
      finset.sup_le (λ b hb, if hpq : p a * q b = 0 then by simp [hpq]
        else by rw [degree_monomial _ hpq, with_bot.coe_add];
          exact add_le_add' (le_degree_of_ne_zero ((mem_support_iff _ _).1 ha)) 
            (le_degree_of_ne_zero ((mem_support_iff _ _).1 hb))))

lemma degree_pow_le (p : polynomial α) : ∀ n, degree (p ^ n) ≤ add_monoid.smul n (degree p)
| 0     := by rw [pow_zero, add_monoid.zero_smul]; exact degree_monomial_le _ _
| (n+1) := calc degree (p ^ (n + 1)) ≤ degree p + degree (p ^ n) : 
    by rw pow_succ; exact degree_mul_le _ _
  ... ≤ _ : by rw succ_smul; exact add_le_add' (le_refl _) (degree_pow_le _)

@[simp] lemma leading_coeff_monomial (a : α) (n : ℕ) : leading_coeff (monomial n a) = a :=
begin 
  by_cases ha : a = 0,
  { simp [ha] },
  { rw [leading_coeff, nat_degree, monomial_apply, degree_monomial _ ha, if_pos], refl }
end

@[simp] lemma leading_coeff_C (a : α) : leading_coeff (C a) = a :=
leading_coeff_monomial _ _

@[simp] lemma leading_coeff_X : leading_coeff (X : polynomial α) = 1 := leading_coeff_monomial _ _

@[simp] lemma leading_coeff_one : leading_coeff (1 : polynomial α) = 1 := leading_coeff_monomial _ _

@[simp] lemma monic_one : monic (1 : polynomial α) := leading_coeff_C _

lemma leading_coeff_add_of_degree_lt (h : degree p < degree q) :
  leading_coeff (p + q) = leading_coeff q :=
have hq0 : q ≠ 0 := ne_zero_of_degree_gt h,
have hpq0 : p + q ≠ 0 := ne_zero_of_degree_gt 
  (show degree p < degree (p + q), by rwa degree_add_eq_of_degree_lt h),
have h : nat_degree (p + q) = nat_degree q := option.some_inj.1 $ 
  show (nat_degree (p + q) : with_bot ℕ) = nat_degree q,
  by rw [← degree_eq_nat_degree hq0, ← degree_eq_nat_degree hpq0];
  exact degree_add_eq_of_degree_lt h,
begin
  unfold leading_coeff,
  rw [h, add_apply, eq_zero_of_degree_lt, zero_add],
  rwa ← degree_eq_nat_degree hq0
end

lemma leading_coeff_add_of_degree_eq (h : degree p = degree q)
  (hlc : leading_coeff p + leading_coeff q ≠ 0) :
  leading_coeff (p + q) = leading_coeff p + leading_coeff q :=
if hp0 : p = 0 then by simp [hp0]
else
have hpq0 : p + q ≠ 0 := λ hpq0,
  by rw [leading_coeff, leading_coeff, nat_degree, nat_degree, h,
    ← add_apply, hpq0, zero_apply] at hlc;
  exact hlc rfl,
have hpq : nat_degree (p + q) = nat_degree p := option.some_inj.1
  $ show (nat_degree (p + q) : with_bot ℕ) = nat_degree p,
  by rw [← degree_eq_nat_degree hp0, ← degree_eq_nat_degree hpq0,
    degree_add_eq_of_leading_coeff_add_ne_zero hlc, h, max_self],
by rw [leading_coeff, add_apply, hpq, leading_coeff, nat_degree_eq_of_degree_eq h];
  refl

@[simp] lemma mul_apply_degree_add_degree (p q : polynomial α) :
  (p * q) (nat_degree p + nat_degree q) = leading_coeff p * leading_coeff q :=
if hpl : leading_coeff p = 0 then
  by rw [hpl, zero_mul, leading_coeff_eq_zero.1 hpl, zero_mul, zero_apply]
else if hql : leading_coeff q = 0 then
  by rw [hql, mul_zero, leading_coeff_eq_zero.1 hql, mul_zero, zero_apply]
else calc p.sum  (λ a b, sum q (λ a₂ b₂, monomial (a + a₂)
    (p a * b₂))) (nat_degree p + nat_degree q) =
    sum (finset.singleton (nat_degree p)) (λ a, (sum q (λ a₂ b₂, monomial (a + a₂) (p a * b₂)))
    (nat_degree p + nat_degree q)) :
  begin rw [sum_apply, finsupp.sum],
    refine eq.symm (sum_subset (λ n hn, (mem_support_iff _ _).2
      ((mem_singleton.1 hn).symm ▸ hpl)) (λ n hnp hn, _)),
    rw [← @sum_const_zero _ _ q.support, finsupp.sum_apply, finsupp.sum],
    refine finset.sum_congr rfl (λ m hm, _),
    have : n + m ≠ nat_degree p + nat_degree q := ne_of_lt
      (add_lt_add_of_lt_of_le (lt_of_le_of_ne 
       (le_of_not_gt 
        (λ h, have degree p < n := 
          by rw degree_eq_nat_degree (mt leading_coeff_eq_zero.2 hpl); 
          exact with_bot.some_lt_some.2 h,
        mt (mem_support_iff _ _).1 (not_not.2 (eq_zero_of_degree_lt this)) hnp)) 
        (mt mem_singleton.2 hn)) 
      (le_of_not_gt 
        (λ h, have degree q < m := 
          by rw degree_eq_nat_degree (mt leading_coeff_eq_zero.2 hql); 
          exact with_bot.some_lt_some.2 h, 
            mt eq_zero_of_degree_lt ((mem_support_iff _ _).1 hm) this))),
    rw [monomial_apply, if_neg this], 
  end
... = (finset.singleton (nat_degree q)).sum (λ a, (monomial (nat_degree p + a) 
    (p (nat_degree p) * q a) : ℕ → α) (nat_degree p + nat_degree q)) : 
  begin 
    rw [sum_singleton, sum_apply, finsupp.sum],
    refine eq.symm (sum_subset (λ n hn, (mem_support_iff _ _).2
      ((mem_singleton.1 hn).symm ▸ hql)) (λ n hnq hn, _)),
    have : nat_degree p + n ≠ nat_degree p + nat_degree q :=
      mt add_left_cancel (mt mem_singleton.2 hn),
    exact if_neg this,
  end
... = leading_coeff p * leading_coeff q : 
  by simp [monomial_apply_self, leading_coeff]

lemma degree_mul_eq' (h : leading_coeff p * leading_coeff q ≠ 0) :
  degree (p * q) = degree p + degree q :=
have hp : p ≠ 0 := mt leading_coeff_eq_zero.2 (λ h₁, by simpa [h₁] using h),
have hq : q ≠ 0 := mt leading_coeff_eq_zero.2 (λ h₁, by simpa [h₁] using h),
le_antisymm (degree_mul_le _ _) 
begin 
  rw [degree_eq_nat_degree hp, degree_eq_nat_degree hq],
  refine le_degree_of_ne_zero _,
  rwa mul_apply_degree_add_degree
end

lemma nat_degree_mul_eq' (h : leading_coeff p * leading_coeff q ≠ 0) :
  nat_degree (p * q) = nat_degree p + nat_degree q :=
have hp : p ≠ 0 := mt leading_coeff_eq_zero.2 (λ h₁, by simpa [h₁] using h),
have hq : q ≠ 0 := mt leading_coeff_eq_zero.2 (λ h₁, by simpa [h₁] using h),
have hpq : p * q ≠ 0 := λ hpq, by rw [← mul_apply_degree_add_degree, hpq, zero_apply] at h;
  exact h rfl,
option.some_inj.1 (show (nat_degree (p * q) : with_bot ℕ) = nat_degree p + nat_degree q,
  by rw [← degree_eq_nat_degree hpq, degree_mul_eq' h, degree_eq_nat_degree hp, degree_eq_nat_degree hq])

lemma leading_coeff_mul' (h : leading_coeff p * leading_coeff q ≠ 0) :
  leading_coeff (p * q) = leading_coeff p * leading_coeff q :=
begin
  unfold leading_coeff,
  rw [nat_degree_mul_eq' h, mul_apply_degree_add_degree],
  refl
end

lemma leading_coeff_pow' : leading_coeff p ^ n ≠ 0 →
  leading_coeff (p ^ n) = leading_coeff p ^ n :=
nat.rec_on n (by simp) $
λ n ih h,
have h₁ : leading_coeff p ^ n ≠ 0 := 
  λ h₁, by simpa [h₁, pow_succ] using h,
have h₂ : leading_coeff p * leading_coeff (p ^ n) ≠ 0 :=
  by rwa [pow_succ, ← ih h₁] at h,
by rw [pow_succ, pow_succ, leading_coeff_mul' h₂, ih h₁]

lemma degree_pow_eq' : ∀ {n}, leading_coeff p ^ n ≠ 0 →
  degree (p ^ n) = add_monoid.smul n (degree p)
| 0     := λ h, by rw [pow_zero, ← C_1] at *;
  rw [degree_C h, add_monoid.zero_smul]
| (n+1) := λ h,
have h₁ : leading_coeff p ^ n ≠ 0 := λ h₁,
  by simpa [h₁, pow_succ] using h,
have h₂ : leading_coeff p * leading_coeff (p ^ n) ≠ 0 :=
  by rwa [pow_succ, ← leading_coeff_pow' h₁] at h,
by rw [pow_succ, degree_mul_eq' h₂, succ_smul, degree_pow_eq' h₁]

end comm_semiring

section comm_ring
variables [comm_ring α] {p q : polynomial α}
instance : comm_ring (polynomial α) := finsupp.to_comm_ring
instance : has_scalar α (polynomial α) := finsupp.to_has_scalar
instance : module α (polynomial α) := finsupp.to_module
instance {x : α} : is_ring_hom (eval x) := ⟨λ x y, eval_add, λ x y, eval_mul, eval_C⟩

@[simp] lemma degree_neg (p : polynomial α) : degree (-p) = degree p :=
by unfold degree; rw support_neg

@[simp] lemma neg_apply (p : polynomial α) (n : ℕ) : (-p) n = -p n := neg_apply

@[simp] lemma eval_neg (p : polynomial α) (x : α) : (-p).eval x = -p.eval x :=
is_ring_hom.map_neg _

@[simp] lemma eval_sub (p q : polynomial α) (x : α) : (p - q).eval x = p.eval x - q.eval x :=
is_ring_hom.map_sub _

lemma degree_sub_lt (hd : degree p = degree q)
  (hp0 : p ≠ 0) (hlc : leading_coeff p = leading_coeff q) :
  degree (p - q) < degree p :=
have hp : single (nat_degree p) (leading_coeff p) + p.erase (nat_degree p) = p :=
  finsupp.single_add_erase,
have hq : single (nat_degree q) (leading_coeff q) + q.erase (nat_degree q) = q :=
  finsupp.single_add_erase,
have hd' : nat_degree p = nat_degree q := by unfold nat_degree; rw hd,
have hq0 : q ≠ 0 := mt degree_eq_bot.2 (hd ▸ mt degree_eq_bot.1 hp0),
calc degree (p - q) = degree (erase (nat_degree q) p + -erase (nat_degree q) q) :
  by conv {to_lhs, rw [← hp, ← hq, hlc, hd', add_sub_add_left_eq_sub, sub_eq_add_neg]}
... ≤ max (degree (erase (nat_degree q) p)) (degree (erase (nat_degree q) q))
  : degree_neg (erase (nat_degree q) q) ▸ degree_add_le _ _
... < degree p : max_lt_iff.2 ⟨hd' ▸ degree_erase_lt hp0, hd.symm ▸ degree_erase_lt hq0⟩

lemma degree_lt_wf : well_founded (λ p q : polynomial α, degree p < degree q) :=
inv_image.wf degree (with_bot.well_founded_lt nat.lt_wf)

instance : has_well_founded (polynomial α) := ⟨_, degree_lt_wf⟩

lemma ne_zero_of_ne_zero_of_monic (hp : p ≠ 0) (hq : monic q) : q ≠ 0 
| h := begin 
  rw [h, monic.def, leading_coeff_zero] at hq,
  rw [← mul_one p, ← C_1, ← hq, C_0, mul_zero] at hp,
  exact hp rfl
end

lemma div_wf_lemma (h : degree q ≤ degree p ∧ p ≠ 0) (hq : monic q) :
  degree (p - monomial (nat_degree p - nat_degree q) (leading_coeff p) * q) < degree p :=
have hp : leading_coeff p ≠ 0 := mt leading_coeff_eq_zero.1 h.2, 
have hpq : leading_coeff (monomial (nat_degree p - nat_degree q) 
    (leading_coeff p)) * leading_coeff q ≠ 0,
  by rwa [leading_coeff_monomial, monic.def.1 hq, mul_one],
if h0 : p - monomial (nat_degree p - nat_degree q) (leading_coeff p) * q = 0
then h0.symm ▸ (lt_of_not_ge $ mt le_bot_iff.1 (mt degree_eq_bot.1 h.2))
else
  have hq0 : q ≠ 0 := ne_zero_of_ne_zero_of_monic h.2 hq,
  have hlt : nat_degree q ≤ nat_degree p := with_bot.coe_le_coe.1 
    (by rw [← degree_eq_nat_degree h.2, ← degree_eq_nat_degree hq0];
    exact h.1),
  degree_sub_lt 
  (by rw [degree_mul_eq' hpq, degree_monomial _ hp, degree_eq_nat_degree h.2,
      degree_eq_nat_degree hq0, ← with_bot.coe_add, nat.sub_add_cancel hlt])
  h.2
  (by rw [leading_coeff_mul' hpq, leading_coeff_monomial, monic.def.1 hq, mul_one])

def div_mod_by_monic_aux : Π (p : polynomial α) {q : polynomial α}, 
  monic q → polynomial α × polynomial α
| p := λ q hq, if h : degree q ≤ degree p ∧ p ≠ 0 then
let z := monomial (nat_degree p - nat_degree q) (leading_coeff p) in
have wf : _ := div_wf_lemma h hq,
let dm := div_mod_by_monic_aux (p - z * q) hq in
⟨z + dm.1, dm.2⟩
else ⟨0, p⟩
using_well_founded {dec_tac := tactic.assumption}

/-- `div_by_monic` gives the quotient of `p` by a monic polynomial `q`. -/
def div_by_monic (p q : polynomial α) : polynomial α :=
if hq : monic q then (div_mod_by_monic_aux p hq).1 else 0

/-- `mod_by_monic` gives the remainder of `p` by a monic polynomial `q`. -/
def mod_by_monic (p q : polynomial α) : polynomial α :=
if hq : monic q then (div_mod_by_monic_aux p hq).2 else p

infixl  ` /ₘ ` : 70 := div_by_monic

infixl ` %ₘ ` : 70 := mod_by_monic

lemma degree_mod_by_monic_lt : ∀ (p : polynomial α) {q : polynomial α} (hq : monic q) 
  (hq0 : q ≠ 0), degree (p %ₘ q) < degree q
| p := λ q hq hq0, 
if h : degree q ≤ degree p ∧ p ≠ 0 then 
  have wf : _ := div_wf_lemma ⟨h.1, h.2⟩ hq,
  have degree ((p - monomial (nat_degree p - nat_degree q) 
    (leading_coeff p) * q) %ₘ q) < degree q := 
      degree_mod_by_monic_lt (p - monomial (nat_degree p - nat_degree q) (leading_coeff p) * q) 
      hq hq0,
  begin
    unfold mod_by_monic at this ⊢,
    unfold div_mod_by_monic_aux,
    rw dif_pos hq at this ⊢,
    rw if_pos h,
    exact this
  end
else
  or.cases_on (not_and_distrib.1 h) begin 
    unfold mod_by_monic div_mod_by_monic_aux,
    rw [dif_pos hq, if_neg h],
    exact lt_of_not_ge,
  end
  begin
    assume hp,
    unfold mod_by_monic div_mod_by_monic_aux,
    rw [dif_pos hq, if_neg h, not_not.1 hp],
    exact lt_of_le_of_ne bot_le
      (ne.symm (mt degree_eq_bot.1 hq0)),
  end
using_well_founded {dec_tac := tactic.assumption}

lemma mod_by_monic_eq_sub_mul_div : ∀ (p : polynomial α) {q : polynomial α} (hq : monic q),
  p %ₘ q = p - q * (p /ₘ q)
| p := λ q hq, if h : degree q ≤ degree p ∧ p ≠ 0 then
  have wf : _ := div_wf_lemma h hq,
  have ih : _ := mod_by_monic_eq_sub_mul_div 
    (p - monomial (nat_degree p - nat_degree q) (leading_coeff p) * q) hq,
  begin
  unfold mod_by_monic div_by_monic div_mod_by_monic_aux,
  rw [dif_pos hq, if_pos h],
  rw [mod_by_monic, dif_pos hq] at ih,
  refine ih.trans _,
  simp [mul_add, add_mul, mul_comm, hq, h, div_by_monic]
end
else begin
  unfold mod_by_monic div_by_monic div_mod_by_monic_aux,
  rw [dif_pos hq, if_neg h, dif_pos hq, if_neg h],
  simp
end
using_well_founded {dec_tac := tactic.assumption}

lemma subsingleton_of_monic_zero (h : monic (0 : polynomial α)) : 
  (∀ p q : polynomial α, p = q) ∧ (∀ a b : α, a = b) :=
by rw [monic.def, leading_coeff_zero] at h;
  exact ⟨λ p q, by rw [← mul_one p, ← mul_one q, ← C_1, ← h, C_0, mul_zero, mul_zero],
    λ a b, by rw [← mul_one a, ← mul_one b, ← h, mul_zero, mul_zero]⟩

lemma mod_by_monic_add_div (p : polynomial α) {q : polynomial α} (hq : monic q) : 
  p %ₘ q + q * (p /ₘ q) = p := eq_sub_iff_add_eq.1 (mod_by_monic_eq_sub_mul_div p hq)

@[simp] lemma zero_mod_by_monic (p : polynomial α) : 0 %ₘ p = 0 :=
begin
  unfold mod_by_monic div_mod_by_monic_aux,
  split_ifs;
  simp * at *
end

@[simp] lemma zero_div_by_monic (p : polynomial α) : 0 /ₘ p = 0 :=
begin
  unfold div_by_monic div_mod_by_monic_aux,
  split_ifs;
  simp * at *
end

@[simp] lemma mod_by_monic_zero (p : polynomial α) : p %ₘ 0 = p :=
if h : monic (0 : polynomial α) then (subsingleton_of_monic_zero h).1 _ _ else
begin
  unfold mod_by_monic div_mod_by_monic_aux,
  split_ifs;
  simp * at *
end

@[simp] lemma div_by_monic_zero (p : polynomial α) : p /ₘ 0 = 0 :=
if h : monic (0 : polynomial α) then (subsingleton_of_monic_zero h).1 _ _ else
begin
  unfold div_by_monic div_mod_by_monic_aux,
  split_ifs;
  simp * at *
end

lemma div_by_monic_eq_of_not_monic (p : polynomial α) (hq : ¬monic q) : p /ₘ q = 0 := dif_neg hq

lemma mod_by_monic_eq_of_not_monic (p : polynomial α) (hq : ¬monic q) : p %ₘ q = p := dif_neg hq

lemma mod_by_monic_eq_self_iff (hq : monic q) (hq0 : q ≠ 0) : p %ₘ q = p ↔ degree p < degree q :=
⟨λ h, h ▸ degree_mod_by_monic_lt _ hq hq0, 
λ h, have ¬ degree q ≤ degree p := not_le_of_gt h,
  by unfold mod_by_monic div_mod_by_monic_aux; simp *⟩

lemma div_by_monic_eq_zero_iff (hq : monic q) (hq0 : q ≠ 0) : p /ₘ q = 0 ↔ degree p < degree q :=
⟨λ h, by have := mod_by_monic_add_div p hq;
  rwa [h, mul_zero, add_zero, mod_by_monic_eq_self_iff hq hq0] at this,
λ h, have ¬ degree q ≤ degree p := not_le_of_gt h,
  by unfold div_by_monic div_mod_by_monic_aux; simp *⟩

lemma degree_add_div_by_monic (hq : monic q) (h : degree q ≤ degree p) : 
  degree q + degree (p /ₘ q) = degree p :=
if hq0 : q = 0 then
  have ∀ (p : polynomial α), p = 0, 
    from λ p, (@subsingleton_of_monic_zero α _ _ (hq0 ▸ hq)).1 _ _,
  by rw [this (p /ₘ q), this p, this q]; refl
else
have hdiv0 : p /ₘ q ≠ 0 := by rwa [ne.def,
  div_by_monic_eq_zero_iff hq hq0, not_lt],
have hlc : leading_coeff q * leading_coeff (p /ₘ q) ≠ 0 :=
  by rwa [monic.def.1 hq, one_mul, ne.def, leading_coeff_eq_zero],
have hmod : degree (p %ₘ q) < degree (q * (p /ₘ q)) :=
  calc degree (p %ₘ q) < degree q : degree_mod_by_monic_lt _ hq hq0
  ... ≤ _ : by rw [degree_mul_eq' hlc, degree_eq_nat_degree hq0,
      degree_eq_nat_degree hdiv0, ← with_bot.coe_add, with_bot.coe_le_coe];
    exact nat.le_add_right _ _,
calc degree q + degree (p /ₘ q) = degree (q * (p /ₘ q)) : eq.symm (degree_mul_eq' hlc)
... = degree (p %ₘ q + q * (p /ₘ q)) : (degree_add_eq_of_degree_lt hmod).symm
... = _ : congr_arg _ (mod_by_monic_add_div _ hq)

lemma degree_div_by_monic_le (p q : polynomial α) : degree (p /ₘ q) ≤ degree p :=
if hp0 : p = 0 then by simp [hp0]
else if hq : monic q then
  have hq0 : q ≠ 0 := ne_zero_of_ne_zero_of_monic hp0 hq,
  if h : degree q ≤ degree p
  then by rw [← degree_add_div_by_monic hq h, degree_eq_nat_degree hq0,
      degree_eq_nat_degree (mt (div_by_monic_eq_zero_iff hq hq0).1 (not_lt.2 h))];
    exact with_bot.coe_le_coe.2 (nat.le_add_left _ _)
  else
    by unfold div_by_monic div_mod_by_monic_aux;
      simp [dif_pos hq, h]
else (div_by_monic_eq_of_not_monic p hq).symm ▸ bot_le

lemma degree_div_by_monic_lt (p : polynomial α) {q : polynomial α} (hq : monic q) 
  (hp0 : p ≠ 0) (h0q : 0 < degree q) : degree (p /ₘ q) < degree p :=
have hq0 : q ≠ 0 := ne_zero_of_ne_zero_of_monic hp0 hq,
if hpq : degree p < degree q 
then begin
  rw [(div_by_monic_eq_zero_iff hq hq0).2 hpq, degree_eq_nat_degree hp0],
  exact with_bot.bot_lt
end
else begin
  rw [← degree_add_div_by_monic hq (not_lt.1 hpq), degree_eq_nat_degree hq0,
        degree_eq_nat_degree (mt (div_by_monic_eq_zero_iff hq hq0).1 hpq)],
  exact with_bot.coe_lt_coe.2 (nat.lt_add_of_pos_left 
    (with_bot.coe_lt_coe.1 $ (degree_eq_nat_degree hq0) ▸ h0q))
end

lemma dvd_iff_mod_by_monic_eq_zero (hq : monic q) : p %ₘ q = 0 ↔ q ∣ p :=
⟨λ h, by rw [← mod_by_monic_add_div p hq, h, zero_add];
  exact dvd_mul_right _ _,
λ h, if hq0 : q = 0 then by rw hq0 at hq; 
  exact (subsingleton_of_monic_zero hq).1 _ _ 
  else 
  let ⟨r, hr⟩ := exists_eq_mul_right_of_dvd h in
  by_contradiction (λ hpq0,
  have hmod : p %ₘ q = q * (r - p /ₘ q) :=
    by rw [mod_by_monic_eq_sub_mul_div _ hq, mul_sub, ← hr],
  have degree (q * (r - p /ₘ q)) < degree q :=
    hmod ▸ degree_mod_by_monic_lt _ hq hq0,
  have hrpq0 : leading_coeff (r - p /ₘ q) ≠ 0 := 
    λ h, hpq0 $ leading_coeff_eq_zero.1
      (by rw [hmod, leading_coeff_eq_zero.1 h, mul_zero, leading_coeff_zero]),
  have hlc : leading_coeff q * leading_coeff (r - p /ₘ q) ≠ 0 :=
    by rwa [monic.def.1 hq, one_mul],
  by rw [degree_mul_eq' hlc, degree_eq_nat_degree hq0,
      degree_eq_nat_degree (mt leading_coeff_eq_zero.2 hrpq0)] at this;
    exact not_lt_of_ge (nat.le_add_right _ _) (with_bot.some_lt_some.1 this))⟩

end comm_ring

section nonzero_comm_ring
variables [nonzero_comm_ring α] {p q : polynomial α}

instance : nonzero_comm_ring (polynomial α) :=
{ zero_ne_one := λ (h : (0 : polynomial α) = 1),
    @zero_ne_one α _ $ 
    calc (0 : α) = eval 0 0 : eval_zero.symm
      ... = eval 0 1 : congr_arg _ h
      ... = 1 : eval_C,
  ..polynomial.comm_ring }

@[simp] lemma degree_one : degree (1 : polynomial α) = (0 : with_bot ℕ) :=
degree_C (show (1 : α) ≠ 0, from zero_ne_one.symm)

@[simp] lemma not_monic_zero : ¬monic (0 : polynomial α) :=
by simp [monic, zero_ne_one]

lemma ne_zero_of_monic (h : monic p) : p ≠ 0 := 
λ h₁, @not_monic_zero α _ _ (h₁ ▸ h)

@[simp] lemma degree_X : degree (X : polynomial α) = 1 := 
begin
  unfold X monomial degree single finsupp.support,
  rw if_neg (zero_ne_one).symm,
  refl
end

@[simp] lemma degree_X_sub_C (a : α) : degree (X - C a) = 1 :=
begin 
  rw [sub_eq_add_neg, add_comm, ← @degree_X α],
  by_cases ha : a = 0,
  { simp [ha] },
  exact degree_add_eq_of_degree_lt (by rw [degree_X, degree_neg, degree_C ha]; exact dec_trivial) 
end

lemma monic_X_sub_C (a : α) : monic (X - C a) :=
have degree (-C a) < degree (X : polynomial α) :=
if ha : a = 0 then by simp [ha]; exact dec_trivial else by simp [degree_C ha]; exact dec_trivial,
by unfold monic;
  rw [sub_eq_add_neg, add_comm, leading_coeff_add_of_degree_lt this, leading_coeff_X]

lemma root_X_sub_C : is_root (X - C a) b ↔ a = b := 
by rw [is_root.def, eval_sub, eval_X, eval_C, sub_eq_zero_iff_eq, eq_comm]

@[simp] lemma mod_by_monic_X_sub_C_eq_C_eval (p : polynomial α) (a : α) : p %ₘ (X - C a) = C (p.eval a) :=
have h : (p %ₘ (X - C a)).eval a = p.eval a :=
  by rw [mod_by_monic_eq_sub_mul_div _ (monic_X_sub_C a), eval_sub, eval_mul, 
    eval_sub, eval_X, eval_C, sub_self, zero_mul, sub_zero],
have degree (p %ₘ (X - C a)) < 1 := 
  degree_X_sub_C a ▸ degree_mod_by_monic_lt p (monic_X_sub_C a) ((degree_X_sub_C a).symm ▸ 
    ne_zero_of_monic (monic_X_sub_C _)),
have degree (p %ₘ (X - C a)) ≤ 0 :=
  begin
    cases (degree (p %ₘ (X - C a))),
    { exact bot_le }, 
    { exact with_bot.some_le_some.2 (nat.le_of_lt_succ (with_bot.some_lt_some.1 this)) }
  end,
begin
  rw [eq_C_of_degree_le_zero this, eval_C] at h,
  rw [eq_C_of_degree_le_zero this, h]
end

lemma mul_div_by_monic_eq_iff_is_root : (X - C a) * (p /ₘ (X - C a)) = p ↔ is_root p a := 
⟨λ h, by rw [← h, is_root.def, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul],
λ h : p.eval a = 0, 
  by conv {to_rhs, rw ← mod_by_monic_add_div p (monic_X_sub_C a)};
    rw [mod_by_monic_X_sub_C_eq_C_eval, h, C_0, zero_add]⟩

end nonzero_comm_ring

section integral_domain
variables [integral_domain α] {p q : polynomial α}

@[simp] lemma degree_mul_eq : degree (p * q) = degree p + degree q :=
if hp0 : p = 0 then by simp [hp0]
else if hq0 : q = 0 then  by simp [hq0]
else degree_mul_eq' $ mul_ne_zero (mt leading_coeff_eq_zero.1 hp0) 
    (mt leading_coeff_eq_zero.1 hq0)

@[simp] lemma degree_pow_eq (p : polynomial α) (n : ℕ) : 
  degree (p ^ n) = add_monoid.smul n (degree p) :=
by induction n; simp [*, pow_succ, succ_smul]

@[simp] lemma leading_coeff_mul (p q : polynomial α) : leading_coeff (p * q) = 
  leading_coeff p * leading_coeff q :=
begin
  by_cases hp : p = 0,
  { simp [hp] },
  { by_cases hq : q = 0,
    { simp [hq] },
    { rw [leading_coeff_mul'],
      exact mul_ne_zero (mt leading_coeff_eq_zero.1 hp) (mt leading_coeff_eq_zero.1 hq) } }
end

@[simp] lemma leading_coeff_pow (p : polynomial α) (n : ℕ) :
  leading_coeff (p ^ n) = leading_coeff p ^ n :=
by induction n; simp [*, pow_succ]

instance : integral_domain (polynomial α) := 
{ eq_zero_or_eq_zero_of_mul_eq_zero := λ a b h, begin
    have : leading_coeff 0 = leading_coeff a * leading_coeff b := h ▸ leading_coeff_mul a b,
    rw [leading_coeff_zero, eq_comm] at this,
    rw [← leading_coeff_eq_zero, ← leading_coeff_eq_zero],
    exact eq_zero_or_eq_zero_of_mul_eq_zero this
  end,
  ..polynomial.nonzero_comm_ring }

lemma root_or_root_of_root_mul (h : is_root (p * q) a) : is_root p a ∨ is_root q a :=
by rw [is_root, eval_mul] at h;
  exact eq_zero_or_eq_zero_of_mul_eq_zero h

lemma degree_pos_of_root (hp : p ≠ 0) (h : is_root p a) : 0 < degree p :=
lt_of_not_ge $ λ hlt, begin
  have := eq_C_of_degree_le_zero hlt,
  rw [is_root, this, eval_C] at h,
  exact hp (ext (λ n, show p n = 0, from
    nat.cases_on n h (λ _, eq_zero_of_degree_lt (lt_of_le_of_lt hlt
      (with_bot.coe_lt_coe.2 (nat.succ_pos _)))))),
end

lemma exists_finset_roots : ∀ {p : polynomial α} (hp : p ≠ 0),
  ∃ s : finset α, (s.card : with_bot ℕ) ≤ degree p ∧ ∀ x, x ∈ s ↔ is_root p x
| p := λ hp, by haveI := classical.prop_decidable (∃ x, is_root p x); exact
if h : ∃ x, is_root p x
then
  let ⟨x, hx⟩ := h in
  have hpd : 0 < degree p := degree_pos_of_root hp hx,
  have hd0 : p /ₘ (X - C x) ≠ 0 :=
    λ h, by have := mul_div_by_monic_eq_iff_is_root.2 hx;
      simp * at *,
  have wf : degree (p /ₘ _) < degree p :=
    degree_div_by_monic_lt _ (monic_X_sub_C x) hp
    ((degree_X_sub_C x).symm ▸ dec_trivial),
  let ⟨t, htd, htr⟩ := @exists_finset_roots (p /ₘ (X - C x)) hd0 in
  have hdeg : degree (X - C x) ≤ degree p := begin 
    rw [degree_X_sub_C, degree_eq_nat_degree hp],
    rw degree_eq_nat_degree hp at hpd,
    exact with_bot.coe_le_coe.2 (with_bot.coe_lt_coe.1 hpd)
  end,
  have hdiv0 : p /ₘ (X - C x) ≠ 0 := mt (div_by_monic_eq_zero_iff (monic_X_sub_C x) 
    (ne_zero_of_monic (monic_X_sub_C x))).1 $ not_lt.2 hdeg,
  ⟨insert x t, calc (card (insert x t) : with_bot ℕ) ≤ card t + 1 : 
    with_bot.coe_le_coe.2 $ finset.card_insert_le _ _
    ... ≤ degree p :
      by rw [← degree_add_div_by_monic (monic_X_sub_C x) hdeg,
          degree_X_sub_C, add_comm];
        exact add_le_add' (le_refl (1 : with_bot ℕ)) htd,
  begin
    assume y,
    rw [mem_insert, htr, eq_comm, ← root_X_sub_C],
    conv {to_rhs, rw ← mul_div_by_monic_eq_iff_is_root.2 hx},
    exact ⟨λ h, or.cases_on h (root_mul_right_of_is_root _) (root_mul_left_of_is_root _),
      root_or_root_of_root_mul⟩
  end⟩
else
  ⟨∅, (degree_eq_nat_degree hp).symm ▸ with_bot.coe_le_coe.2 (nat.zero_le _), 
    by clear exists_finset_roots; finish⟩
using_well_founded {dec_tac := tactic.assumption}

/-- `roots p` noncomputably gives a finset containing all the roots of `p` -/
noncomputable def roots (p : polynomial α) : finset α := 
if h : p = 0 then ∅ else classical.some (exists_finset_roots h)

lemma card_roots (hp0 : p ≠ 0) : ((roots p).card : with_bot ℕ) ≤ degree p :=
begin
  unfold roots,
  rw dif_neg hp0,
  exact (classical.some_spec (exists_finset_roots hp0)).1
end

@[simp] lemma mem_roots (hp : p ≠ 0) : a ∈ p.roots ↔ is_root p a :=
by unfold roots; rw dif_neg hp; exact (classical.some_spec (exists_finset_roots hp)).2 _

end integral_domain

section field
variables [field α] {p q : polynomial α} 
instance : vector_space α (polynomial α) :=
{ ..finsupp.to_module }

lemma monic_mul_leading_coeff_inv (h : p ≠ 0) : 
  monic (p * C (leading_coeff p)⁻¹) :=
by rw [monic, leading_coeff_mul, leading_coeff_C, 
  mul_inv_cancel (show leading_coeff p ≠ 0, from mt leading_coeff_eq_zero.1 h)]

lemma degree_mul_leading_coeff_inv (h : p ≠ 0) :
  degree (p * C (leading_coeff p)⁻¹) = degree p :=
have h₁ : (leading_coeff p)⁻¹ ≠ 0 :=
  inv_ne_zero (mt leading_coeff_eq_zero.1 h),
by rw [degree_mul_eq, degree_C h₁, add_zero]

def div (p q : polynomial α) := 
C (leading_coeff q)⁻¹ * (p /ₘ (q * C (leading_coeff q)⁻¹))

def mod (p q : polynomial α) :=
p %ₘ (q * C (leading_coeff q)⁻¹)

private lemma quotient_mul_add_remainder_eq_aux (p q : polynomial α) :
  q * div p q + mod p q = p :=
if h : q = 0 then by simp [h, mod_by_monic, div, mod]
else begin
  conv {to_rhs, rw ← mod_by_monic_add_div p (monic_mul_leading_coeff_inv h)},
  rw [div, mod, add_comm, mul_assoc]  
end

private lemma val_remainder_lt_aux (p : polynomial α) (hq : q ≠ 0) :
  degree (mod p q) < degree q :=
degree_mul_leading_coeff_inv hq ▸
  degree_mod_by_monic_lt p (monic_mul_leading_coeff_inv hq)
    (mul_ne_zero hq (mt leading_coeff_eq_zero.2 (by rw leading_coeff_C;
      exact inv_ne_zero (mt leading_coeff_eq_zero.1 hq))))

instance : has_div (polynomial α) := ⟨div⟩

instance : has_mod (polynomial α) := ⟨mod⟩

lemma mod_by_monic_eq_mod (p : polynomial α) (hq : monic q) : p %ₘ q = p % q :=
show p %ₘ q = p %ₘ (q * C (leading_coeff q)⁻¹), by simp [monic.def.1 hq]

lemma div_by_monic_eq_div (p : polynomial α) (hq : monic q) : p /ₘ q = p / q :=
show p /ₘ q = C (leading_coeff q)⁻¹ * (p /ₘ (q * C (leading_coeff q)⁻¹)),
by simp [monic.def.1 hq]

lemma mod_X_sub_C_eq_C_eval (p : polynomial α) (a : α) : p % (X - C a) = C (p.eval a) :=
mod_by_monic_eq_mod p (monic_X_sub_C a) ▸ mod_by_monic_X_sub_C_eq_C_eval _ _

lemma mul_div_eq_iff_is_root : (X - C a) * (p / (X - C a)) = p ↔ is_root p a :=
div_by_monic_eq_div p (monic_X_sub_C a) ▸ mul_div_by_monic_eq_iff_is_root

/-
instance : euclidean_domain (polynomial α) :=
{ quotient := div_aux, 
  remainder := mod_aux,
  quotient_mul_add_remainder_eq := quotient_mul_add_remainder_eq_aux,
  valuation := euclid_val_poly,
  val_remainder_lt := λ p q hq, val_remainder_lt_aux _ hq,
  val_le_mul_left := λ p q hq, 
    if hp : p = 0 then begin 
        unfold euclid_val_poly,
        rw [if_pos hp],
        exact nat.zero_le _
      end 
    else begin
        unfold euclid_val_poly,
        rw [if_neg hp, if_neg (mul_ne_zero hp hq), degree_mul_eq hp hq],
        exact nat.succ_le_succ (nat.le_add_right _ _),
      end }

lemma degree_add_div (p : polynomial α) {q : polynomial α} (hq0 : q ≠ 0) :
  degree q + degree (p / q) = degree p := sorry
-/

end field

end polynomial
