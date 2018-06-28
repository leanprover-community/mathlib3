/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

Theory of univariate polynomials, represented as finsupps, ℕ →₀ α, with α a comm_semiring
-/

import linear_algebra.multivariate_polynomial algebra.euclidean_domain
open finsupp finset lattice

set_option old_structure_cmd true

class nonzero_comm_ring (α : Type*) extends zero_ne_one_class α, comm_ring α

instance integral_domain.to_nonzero_ring (α : Type*) [hd : integral_domain α] : nonzero_comm_ring α :=
{ ..hd }

namespace finset

lemma sup_lt_nat : ∀ {s t : finset ℕ}, s ⊆ t → t.sup id ∉ s
  → 0 < t.sup id → s.sup id < t.sup id :=
λ s, finset.induction_on s (λ _ _ _, id) begin
  assume a s has ih t hst hsup hpos,
  rw finset.sup_insert,
  exact max_lt_iff.2 ⟨lt_of_le_of_ne (finset.le_sup (hst (finset.mem_insert_self _ _))) 
      (λ h, by simpa [h.symm] using hsup),
    ih (λ a ha, hst (finset.mem_insert_of_mem ha))
      (hsup ∘ finset.mem_insert_of_mem) hpos⟩,
end

lemma sup_mem_nat {s : finset ℕ} : s ≠ ∅ → s.sup id ∈ s :=
finset.induction_on s (by simp * at *) $
begin
  assume a s has ih _,
  by_cases h₁ : s = ∅,
  { simp * },
  { cases (le_total a (s.sup id)) with h₂ h₂,
    { simp [lattice.sup_of_le_right h₂, ih h₁] },
    { simp [lattice.sup_of_le_left h₂] } }
end

end finset

namespace finsupp

@[simp] lemma erase_single {α β : Type*} [decidable_eq α] [decidable_eq β] [has_zero β]
  (a : α) (b : β) : (single a b).erase a = (0 : α →₀ β) := 
ext (λ x, begin 
  by_cases hxa : x = a,
  { simp [hxa, erase_same] },
  { simp [erase_ne hxa, single_apply, if_neg (ne.symm hxa)] },
end)

end finsupp

def polynomial (α : Type*) [comm_semiring α] := ℕ →₀ α

namespace polynomial
variables {α : Type*} {a b : α} {m n : ℕ} 
variables [decidable_eq α]

section comm_semiring
variables [comm_semiring α] {p q : polynomial α}

instance : has_coe_to_fun (polynomial α) := finsupp.has_coe_to_fun
instance : has_zero (polynomial α) := finsupp.has_zero
instance : has_one (polynomial α) := finsupp.has_one
instance : has_add (polynomial α) := finsupp.has_add
instance : has_mul (polynomial α) := finsupp.has_mul
instance : comm_semiring (polynomial α) := finsupp.to_comm_semiring

local attribute [instance] finsupp.to_comm_semiring

/-- `monomial n a` is the polynomial `a * X^n` -/
def monomial (n : ℕ) (a : α) : polynomial α := single n a

/-- `C a` is the constant polynomial a -/
def C (a : α) : polynomial α := monomial 0 a

/-- `X` is the polynomial whose evaluation is the identity funtion -/
def X : polynomial α := monomial 1 1

@[simp] lemma C_0 : C 0 = (0 : polynomial α) := by simp [C, monomial]; refl

@[simp] lemma C_1 : C 1 = (1 : polynomial α) := rfl

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

lemma monomial_add_right : monomial (n + m) a = (monomial n a * X ^ m):=
by rw [X_pow_eq_monomial, monomial, monomial, monomial, single_mul_single]; simp

lemma monomial_add_left : monomial (m + n) a = (X ^ m * monomial n a):=
by rw [X_pow_eq_monomial, monomial, monomial, monomial, single_mul_single]; simp

lemma monomial_eq : monomial n a = C a * X ^ n :=
by rw [X_pow_eq_monomial, C_mul_monomial, mul_one]

lemma erase_monomial : (monomial n a).erase n = 0 := finsupp.erase_single _ _

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

lemma monomial_apply : @coe_fn (polynomial α) polynomial.has_coe_to_fun (monomial n a) m = ite (n = m) a 0 :=
finsupp.single_apply

lemma monomial_apply_self : @coe_fn (polynomial α) polynomial.has_coe_to_fun (monomial n a) n = a :=
by simp [monomial_apply]

lemma C_apply : @coe_fn (polynomial α) polynomial.has_coe_to_fun (C a) n = ite (0 = n) a 0 := finsupp.single_apply

lemma add_apply (p q : polynomial α) (n : ℕ) : (p + q) n = p n + q n := add_apply

@[simp] lemma C_mul_apply (p : polynomial α) : (C a * p) n = a * p n :=
induction_on p (λ b, show (monomial 0 a * monomial 0 b) n = a * 
  @coe_fn (polynomial α) polynomial.has_coe_to_fun (monomial 0 b) n,
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

lemma eval_add : (p + q).eval x = p.eval x + q.eval x :=
finsupp.sum_add_index (by simp) (by simp [add_mul])

lemma eval_monomial : (monomial n a).eval x = a * x ^ n :=
finsupp.sum_single_index (zero_mul _)

@[simp] lemma eval_C : (C a).eval x = a :=
by simp [eval_monomial, C, prod_zero_index]

@[simp] lemma eval_X : X.eval x = x :=
by simp [eval_monomial, X, prod_single_index, pow_one]

lemma eval_mul_monomial :
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

lemma eval_mul : ∀{p}, (p * q).eval x = p.eval x * q.eval x :=
begin
  apply polynomial.induction_on q,
  { simp [C, eval_monomial, eval_mul_monomial, prod_zero_index] },
  { simp [mul_add, eval_add] {contextual := tt} },
  { simp [X, eval_monomial, eval_mul_monomial, (mul_assoc _ _ _).symm] { contextual := tt} }
end

/-- `is_root p x` implies `x` is a root of `p`. The evaluation of `p` at `x` is zero -/
def is_root (p : polynomial α) (a : α) : Prop := p.eval a = 0

instance : decidable (is_root p a) := by unfold is_root; apply_instance

lemma is_root.def : is_root p a ↔ p.eval a = 0 := iff.rfl

lemma root_mul_left_of_is_root (q : polynomial α) : is_root p a → is_root (q * p) a :=
by simp [is_root.def, eval_mul] {contextual := tt}

lemma root_mul_right_of_is_root (q : polynomial α) : is_root p a → is_root (p * q) a :=
by simp [is_root.def, eval_mul] {contextual := tt}

end eval

/-- `degree p` gives the highest power of `X` that appears in `p` -/
def degree (p : polynomial α) : ℕ := p.support.sup id

/-- `leading_coeff p` gives the coefficient of the highest power of `X` in `p`-/
def leading_coeff (p : polynomial α) : α := p (degree p)

/-- a polynomial is `monic` if its leading coefficient is 1 -/
def monic (p : polynomial α) := leading_coeff p = (1 : α)

lemma monic.def : monic p ↔ leading_coeff p = 1 := iff.rfl

instance monic.decidable : decidable (monic p) :=
by unfold monic; apply_instance

@[simp] lemma degree_zero : degree (0 : polynomial α) = 0 := rfl

@[simp] lemma degree_C (a : α) : degree (C a) = 0 := 
begin
  unfold C single monomial degree finsupp.support,
  by_cases a = 0;
  simp *;
  refl
end

@[simp] lemma degree_one : degree (1 : polynomial α) = 0 := degree_C _

lemma degree_monomial_le (n : ℕ) (a : α) : degree (monomial n a) ≤ n :=
begin
  unfold single monomial degree finsupp.support,
  by_cases a = 0;
  simp [*, sup];
  refl
end

@[simp] lemma degree_monomial (n : ℕ) (ha : a ≠ 0) : degree (monomial n a) = n :=
begin
  unfold X single monomial degree finsupp.support,
  rw if_neg ha,
  simp [sup]
end

lemma le_degree_of_ne_zero (h : p n ≠ 0) : n ≤ degree p :=
show id n ≤ p.support.sup id,
from finset.le_sup ((finsupp.mem_support_iff _ _).2 h)

lemma eq_zero_of_degree_lt (h : degree p < n) : p n = 0 :=
not_not.1 (mt le_degree_of_ne_zero (not_le_of_gt h))

lemma eq_C_of_degree_eq_zero (h : degree p = 0) : p = C (p 0) := 
ext begin
  assume n,
  cases n,
  { refl },
  { have h : degree p < nat.succ n := h.symm ▸ nat.succ_pos _,
    rw [eq_zero_of_degree_lt h, C_apply, if_neg],
    exact λ h, nat.no_confusion h }
end

lemma degree_add_le (p q : polynomial α) : 
  degree (p + q) ≤ max (degree p) (degree q) :=
show _ ≤ (finset.sup (p.support) id) ⊔ (finset.sup (q.support) id),
by rw ← finset.sup_union;
  exact finset.sup_mono support_add

@[simp] lemma leading_coeff_zero : leading_coeff (0 : polynomial α) = 0 := rfl

@[simp] lemma leading_coeff_eq_zero : leading_coeff p = 0 ↔ p = 0 :=
⟨λ h, by_contradiction (λ h₁, (mem_support_iff _ _).1 (finset.sup_mem_nat (mt support_eq_empty.1 h₁)) h),
by simp { contextual := tt }⟩

lemma degree_add_eq_of_degree_lt (h : degree p < degree q) : degree (p + q) = degree q :=
le_antisymm (max_eq_right_of_lt h ▸ degree_add_le _ _)
  (le_degree_of_ne_zero begin 
    rw [add_apply, eq_zero_of_degree_lt h, zero_add],
    exact mt leading_coeff_eq_zero.1 (λ h₁, by simpa [h₁, nat.not_lt_zero] using h)
  end)

lemma degree_add_eq_of_apply_ne_zero (h : leading_coeff p + q (degree p) ≠ 0) :
  degree (p + q) = max p.degree q.degree :=
le_antisymm (degree_add_le _ _) (le_degree_of_ne_zero begin 
  rw add_apply,
  unfold max,
  split_ifs,
  { cases lt_or_eq_of_le h_1 with h₁ h₁,
    { rw [not_not.1 (mt le_degree_of_ne_zero (not_le_of_gt h₁)), zero_add],
      exact mt leading_coeff_eq_zero.1 (λ h, by simpa [h, nat.not_lt_zero] using h₁) },
    { rwa ← h₁ } },
  assumption
end)

lemma degree_erase_lt (h : 0 < degree p) : 
  degree (p.erase (degree p)) < degree p :=
finset.sup_lt_nat (erase_subset _ _) (not_mem_erase _ _) h

lemma degree_mul_le : ∀ (p q : polynomial α), degree (p * q) ≤ degree p + degree q :=
have hsup : ∀ {n : ℕ} {q : polynomial α} {a : α}, 
    sup ((sum q (λ (m : ℕ) (x : α), single (n + m) (a * x))).support) id
  ≤ n + degree q := λ n q a, sup_le (λ b hb, begin 
    rcases mem_bind.1 (finsupp.support_sum hb) with ⟨x, hx₁, hx₂⟩,
    rw mem_support_iff at hx₁ hx₂,
    rw single_apply at hx₂,
    by_cases hnx : n + x = b,
    { rw [← hnx, id.def],
      exact add_le_add_left (le_degree_of_ne_zero hx₁) _ },
    { simpa [hnx] using hx₂ }
  end),
λ p, monomial_induction_on p
(by simp [nat.zero_le]) 
(assume n a p hpn ha ih q,
calc degree ((single n a + p) * q) ≤ max (degree (single n a * q)) (degree (p * q)) :
  by rw add_mul; exact degree_add_le _ _
  ... = max ((q.sum (λ m x, single (n + m) (a * x))).support.sup id) (degree (p * q)) :
    by rw [mul_def, sum_single_index, degree]; simp
  ... ≤ max (n + degree q) (degree p + degree q) : by exact max_le_max hsup (ih _)
  ... ≤ max n (degree p) + degree q : max_le (add_le_add_right 
    (le_max_left _ _) _) (add_le_add_right (le_max_right _ _) _)
  ... = degree (monomial n a + p) + degree q : 
    begin
      rw [degree_add_eq_of_apply_ne_zero, degree_monomial _ ha],
      rwa [leading_coeff, degree_monomial _ ha, monomial_apply_self, hpn, add_zero]
    end)
  
lemma degree_erase_le (p : polynomial α) (n : ℕ) : degree (p.erase n) ≤ degree p :=
sup_mono (erase_subset _ _)

@[simp] lemma leading_coeff_monomial (a : α) (n : ℕ) : leading_coeff (monomial n a) = a :=
begin 
  by_cases ha : a = 0,
  { simp [ha] },
  { simp [leading_coeff, degree_monomial _ ha, monomial_apply] },
end

@[simp] lemma leading_coeff_C (a : α) : leading_coeff (C a) = a :=
leading_coeff_monomial _ _

@[simp] lemma monic_one : monic (1 : polynomial α) := leading_coeff_C _

lemma leading_coeff_add_of_lt (h : degree p < degree q) :
  leading_coeff (p + q) = leading_coeff q :=
by unfold leading_coeff;
  rw [degree_add_eq_of_degree_lt h, add_apply, eq_zero_of_degree_lt h, zero_add]

@[simp] lemma mul_apply_degree_add_degree (p q : polynomial α) :
  (p * q) (degree p + degree q) = leading_coeff p * leading_coeff q :=
if hp : degree p = 0 then begin 
  rw [eq_C_of_degree_eq_zero hp],
  simp [leading_coeff, C_apply]
end
else
have h₁ : p * q = monomial (degree p + degree q) (p (degree p) * q (degree q)) +
  erase (degree p) p * monomial (degree q) (q (degree q)) +
  (erase (degree q) q * monomial (degree p) (p (degree p)) +
  erase (degree p) p * erase (degree q) q),
begin
  unfold monomial,
  conv {to_lhs, rw [← @single_add_erase _ _ _ _ _ (degree p) p, 
      ← @single_add_erase _ _ _ _ _ (degree q) q,
      mul_add, add_mul, add_mul, single_mul_single] },
  simp [mul_comm],
end,
have h₂ : ∀ {p q r : polynomial α}, degree r ≤ degree q →
  (erase (degree p) p * r) (degree p + degree q) = 0,
from λ p q r hr, if hp : degree p = 0 then
  by rw [hp, eq_C_of_degree_eq_zero hp, C, erase_monomial, zero_add, zero_mul, zero_apply]
else
eq_zero_of_degree_lt 
  (calc degree (erase (degree p) p * r)
      ≤ _ : degree_mul_le _ _
  ... < _ : add_lt_add_of_lt_of_le (degree_erase_lt (nat.pos_of_ne_zero hp)) hr),
begin
  rw [h₁, add_apply, add_apply, add_apply, monomial_apply, if_pos rfl],
  rw [h₂ (degree_monomial_le _ _), h₂ (degree_erase_le _ _),
    add_comm (degree p), h₂ (degree_monomial_le _ _), add_zero, add_zero, add_zero],
  refl,  
end

lemma degree_mul_eq' {p q : polynomial α} (h : leading_coeff p * leading_coeff q ≠ 0) :
  degree (p * q) = degree p + degree q := 
le_antisymm (degree_mul_le _ _) (le_degree_of_ne_zero (by rwa mul_apply_degree_add_degree))

end comm_semiring

section comm_ring
variables [comm_ring α] {p q : polynomial α}
instance : comm_ring (polynomial α) := finsupp.to_comm_ring
instance : has_scalar α (polynomial α) := finsupp.to_has_scalar
instance : module α (polynomial α) := finsupp.to_module
instance {x : α} : is_ring_hom (eval x) := ⟨λ x y, eval_add, λ x y, eval_mul, eval_C⟩

@[simp] lemma degree_neg (p : polynomial α) : degree (-p) = degree p :=
by unfold degree; rw support_neg

@[simp] lemma neg_apply (p : polynomial α) (n : ℕ) : (-p) n = - p n := neg_apply

lemma eval_neg (p : polynomial α) (x : α) : (-p).eval x = -p.eval x :=
is_ring_hom.map_neg _

lemma eval_sub (p q : polynomial α) (x : α) : (p - q).eval x = p.eval x - q.eval x :=
is_ring_hom.map_sub _

lemma degree_sub_lt (hd : degree p = degree q)
  (hpos : 0 < degree p) (hlc : leading_coeff p = leading_coeff q) :
  degree (p - q) < degree p :=
have hlc' : p (degree p) = q (degree q) := hlc,
have hp : single (degree p) (p (degree p)) + p.erase (degree p) = p :=
  finsupp.single_add_erase,
have hq : single (degree q) (q (degree q)) + q.erase (degree q) = q :=
  finsupp.single_add_erase,
begin
  conv { to_lhs, rw [← hp, ← hq, hlc', hd, add_sub_add_left_eq_sub] },
  exact calc degree (erase (degree q) p + -erase (degree q) q)
    ≤ max (degree (erase (degree q) p)) (degree (erase (degree q) q))
    : by rw ← degree_neg (erase (degree q) q);
      exact degree_add_le _ _
  ... < degree p : max_lt_iff.2
    ⟨hd ▸ degree_erase_lt hpos,
    hd.symm ▸ degree_erase_lt (hd ▸ hpos)⟩
end

lemma div_wf_lemma (h : degree q ≤ degree p ∧ 0 < degree p) (hq : monic q) :
  degree (p - monomial (degree p - degree q) (leading_coeff p) * q) < degree p := 
have hp : leading_coeff p ≠ 0, from mt leading_coeff_eq_zero.1 (λ h₁, by simpa [h₁, lt_irrefl] using h),
have hpq : leading_coeff (monomial (degree p - degree q) (leading_coeff p)) * leading_coeff q ≠ 0,
  by rwa [leading_coeff, degree_monomial _ hp, monomial_apply, if_pos rfl, monic.def.1 hq, mul_one],
have hzq : leading_coeff (monomial (degree p - degree q) (p (degree p))) * leading_coeff q ≠ 0 :=
  by rwa [monic.def.1 hq, leading_coeff_monomial, mul_one],
degree_sub_lt (by rw [degree_mul_eq' hpq, degree_monomial _ hp, nat.sub_add_cancel h.1]) 
h.2
(by rw [leading_coeff, leading_coeff, degree_mul_eq' hzq, mul_apply_degree_add_degree, 
      leading_coeff_monomial, monic.def.1 hq, mul_one])
      
def div_mod_by_monic_aux : Π (p : polynomial α) {q : polynomial α}, 
  monic q → polynomial α × polynomial α
| p := λ q hq, if h : degree q ≤ degree p ∧ 0 < degree p then
have h : _ := div_wf_lemma h hq,
let z := monomial (degree p - degree q) (leading_coeff p) in
let dm := div_mod_by_monic_aux (p - z * q) hq in
⟨z + dm.1, dm.2⟩
else if degree p = 0 ∧ degree q = 0
  then ⟨C (leading_coeff p), 0⟩
else ⟨0, p⟩
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf degree⟩]}

/-- `div_by_monic` gives the quotient of `p` by a monic polynomial `q`. -/
def div_by_monic (p q : polynomial α) : polynomial α :=
if hq : monic q then (div_mod_by_monic_aux p hq).1 else 0

/-- `mod_by_monic` gives the remainder of `p` by a monic polynomial `q` -/
def mod_by_monic (p q : polynomial α) : polynomial α :=
if hq : monic q then (div_mod_by_monic_aux p hq).2 else p

lemma degree_mod_by_monic_lt : ∀ (p : polynomial α) {q : polynomial α} (hq : monic q) 
  (hq0 : 0 < degree q), degree (mod_by_monic p q) < degree q
| p := λ q hq hq0, if h : degree q ≤ degree p ∧ 0 < degree p then 
have wf : _ := div_wf_lemma h hq,
have degree (mod_by_monic (p - monomial (degree p - degree q) 
  (leading_coeff p) * q) q) < degree q := 
    degree_mod_by_monic_lt (p - monomial (degree p - degree q) (leading_coeff p) * q) 
    hq hq0,
begin
  unfold mod_by_monic at this ⊢,
  unfold div_mod_by_monic_aux,
  rw dif_pos hq at this ⊢,
  rw if_pos h,
  exact this
end
else 
have h₁ : ¬ (degree p = 0 ∧ degree q = 0) := λ h₁, by simpa [h₁.2, lt_irrefl] using hq0,
begin
  unfold mod_by_monic div_mod_by_monic_aux,
  rw [dif_pos hq, if_neg h, if_neg h₁],
  cases not_and_distrib.1 h with h₂ h₂,
  { exact lt_of_not_ge h₂ },
  { simpa [nat.le_zero_iff.1 (le_of_not_gt h₂)] }
end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf degree⟩]}

@[simp] lemma mod_by_monic_one : ∀ p : polynomial α, mod_by_monic p 1 = 0
| p := if hp0 : 0 < degree p then 
have hd : degree 1 ≤ degree p ∧ 0 < degree p := ⟨by rw @degree_one α _ _; exact nat.zero_le _, hp0⟩,
have wf : degree (p + -monomial (degree p) (leading_coeff p)) < degree p :=
  by have := div_wf_lemma hd monic_one; simpa using this,
have h : _ := mod_by_monic_one (p - monomial (degree p - degree (1 : polynomial α)) (leading_coeff p) * 1),
begin
  unfold mod_by_monic div_mod_by_monic_aux,
  rw [dif_pos monic_one, if_pos hd],
  rwa [mod_by_monic, dif_pos monic_one] at h
end else 
have hp0' : degree p = 0 := not_not.1 $ mt nat.pos_of_ne_zero hp0,
begin
  unfold mod_by_monic div_mod_by_monic_aux,
  simp [hp0, hp0']
end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf degree⟩]}

lemma degree_mod_by_monic_lt_or_eq_zero (p : polynomial α) {q : polynomial α} (hq : monic q) 
  : degree (mod_by_monic p q) < degree q ∨ mod_by_monic p q = 0 :=
if hq0 : 0 < degree q then or.inl $ degree_mod_by_monic_lt p hq hq0
else have hq0 : degree q = 0 := not_not.1 $ mt nat.pos_of_ne_zero hq0,
have hq : q = 1 :=
  by rw [eq_C_of_degree_eq_zero hq0, ← hq0, (show q (degree q) = 1, from hq)]; refl,
by subst hq;
  simp [mod_by_monic_one]

lemma mod_by_monic_eq_sub_mul_div : ∀ (p : polynomial α) {q : polynomial α} (hq : monic q),
  mod_by_monic p q = p - q * div_by_monic p q
| p := λ q hq, if h : degree q ≤ degree p ∧ 0 < degree p then
  have wf : _ := div_wf_lemma h hq,
  have ih : _ := mod_by_monic_eq_sub_mul_div (p - monomial (degree p - degree q) (leading_coeff p) * q) hq,
  begin
  unfold mod_by_monic div_by_monic div_mod_by_monic_aux,
  rw [dif_pos hq, if_pos h],
  rw [mod_by_monic, dif_pos hq] at ih,
  refine ih.trans _,
  simp [mul_add, add_mul, mul_comm, hq, h, div_by_monic]
end
else if h₁ : degree p = 0 ∧ degree q = 0 then 
have hq0 : q 0 = 1 := h₁.2 ▸ hq,
begin
  unfold mod_by_monic div_by_monic div_mod_by_monic_aux,
  rw [dif_pos hq, if_neg h, if_pos h₁],
  rw [eq_C_of_degree_eq_zero h₁.1, eq_C_of_degree_eq_zero h₁.2] at *,
  conv {to_rhs, congr, rw eq_C_of_degree_eq_zero h₁.1},
  simp [hq0, leading_coeff, h₁.1, h₁.2, h, hq, lt_irrefl, C_apply],
end
else begin 
  unfold mod_by_monic div_by_monic div_mod_by_monic_aux,
  simp [hq, h, h₁]
end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf degree⟩]}

lemma mod_by_monic_add_div (p : polynomial α) {q : polynomial α} (hq : monic q) : 
  mod_by_monic p q + q * div_by_monic p q = p := eq_sub_iff_add_eq.1 (mod_by_monic_eq_sub_mul_div p hq)

lemma degree_div_by_monic_lt (p : polynomial α) {q : polynomial α} (hq : monic q) 
  (hq0 : 0 < degree q) (hp0 : 0 < degree p) : degree (div_by_monic p q) < degree p :=
if hdp : div_by_monic p q = 0 then by simpa [hdp] else
have h₁ : leading_coeff q * leading_coeff (div_by_monic p q) ≠ 0 :=
by rw [monic.def.1 hq, one_mul];
  exact mt leading_coeff_eq_zero.1 hdp,
have h₂ : degree (mod_by_monic p q) < degree (q * div_by_monic p q) :=
by rw degree_mul_eq' h₁;
  exact calc degree (mod_by_monic p q) < degree q : degree_mod_by_monic_lt p hq hq0 
    ... ≤ degree q + _ : nat.le_add_right _ _,
begin
  conv {to_rhs, rw ← mod_by_monic_add_div p hq},
  rw [degree_add_eq_of_degree_lt h₂, degree_mul_eq' h₁],
  exact (lt_add_iff_pos_left _).2 hq0,
end

lemma dvd_iff_mod_by_monic_eq_zero (hq : monic q) : mod_by_monic p q = 0 ↔ q ∣ p :=
⟨λ h, by rw [← mod_by_monic_add_div p hq, h, zero_add];
  exact dvd_mul_right _ _,
λ h, or.cases_on (degree_mod_by_monic_lt_or_eq_zero p hq) 
(λ hlt, let ⟨r, hr⟩ := exists_eq_mul_right_of_dvd h in
have hr : mod_by_monic p q = q * (r - div_by_monic p q) :=
  by rwa [← mod_by_monic_add_div p hq, ← eq_sub_iff_add_eq, ← mul_sub] at hr,
have r - div_by_monic p q = 0 := classical.by_contradiction
  (λ h,
  have hlc : leading_coeff q * leading_coeff (r - div_by_monic p q) ≠ 0 :=
    by rwa [monic.def.1 hq, one_mul, ne.def, leading_coeff_eq_zero],
  have hq : degree (q * (r - div_by_monic p q)) = 
    degree q + degree (r - div_by_monic p q) :=
      by rw degree_mul_eq' hlc,
  by rw [hr, hq] at hlt;
    exact not_lt_of_ge (nat.le_add_right _ _) hlt),
by rwa [this, mul_zero] at hr) id⟩

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

@[simp] lemma not_monic_zero : ¬monic (0 : polynomial α) :=
by simp [monic, zero_ne_one]

lemma degree_X : degree (X : polynomial α) = 1 := 
begin
  unfold X monomial degree single finsupp.support,
  rw if_neg (zero_ne_one).symm,
  simp [sup],
end

lemma degree_X_sub_C (a : α) : degree (X - C a) = 1 :=
begin 
  rw [sub_eq_add_neg, add_comm, ← @degree_X α],
  exact degree_add_eq_of_degree_lt (by simp [degree_X, degree_neg, degree_C, nat.succ_pos]) 
end

lemma monic_X_sub_C (a : α) : monic (X - C a) :=
begin
  unfold monic leading_coeff,
  rw [degree_X_sub_C, sub_eq_add_neg, add_apply, X, C, monomial_apply, neg_apply, monomial_apply],
  split_ifs; simp * at *
end

lemma root_X_sub_C : is_root (X - C a) b ↔ a = b := 
by rw [is_root.def, eval_sub, eval_X, eval_C, sub_eq_zero_iff_eq, eq_comm]

lemma mod_by_monic_X_sub_C_eq_C_eval (p : polynomial α) (a : α) : mod_by_monic p (X - C a) = C (p.eval a) :=
have h : (mod_by_monic p (X - C a)).eval a = p.eval a :=
  by rw [mod_by_monic_eq_sub_mul_div _ (monic_X_sub_C a), eval_sub, eval_mul, 
    eval_sub, eval_X, eval_C, sub_self, zero_mul, sub_zero],
have degree (mod_by_monic p (X - C a)) < 1 := 
  degree_X_sub_C a ▸ degree_mod_by_monic_lt p (monic_X_sub_C a) ((degree_X_sub_C a).symm ▸ nat.succ_pos _),
have degree (mod_by_monic p (X - C a)) = 0 := nat.eq_zero_of_le_zero (nat.le_of_lt_succ this),
begin
  rw [eq_C_of_degree_eq_zero this, eval_C] at h,
  rw [eq_C_of_degree_eq_zero this, h]
end

lemma mul_div_eq_iff_is_root : (X - C a) * div_by_monic p (X - C a) = p ↔ is_root p a := 
⟨λ h, by rw [← h, is_root.def, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul],
λ h : p.eval a = 0, 
  by conv{to_rhs, rw ← mod_by_monic_add_div p (monic_X_sub_C a)};
    rw [mod_by_monic_X_sub_C_eq_C_eval, h, C_0, zero_add]⟩

end nonzero_comm_ring

section integral_domain
variables [integral_domain α] {p q : polynomial α}

lemma degree_mul_eq (hp : p ≠ 0) (hq : q ≠ 0) : degree (p * q) = degree p + degree q :=
by rw degree_mul_eq';
  exact mul_ne_zero (mt leading_coeff_eq_zero.1 hp) 
    (mt leading_coeff_eq_zero.1 hq)

lemma leading_coeff_mul (p q : polynomial α) : leading_coeff (p * q) = 
  leading_coeff p * leading_coeff q :=
begin
  by_cases hp : p = 0,
  { simp [hp] },
  by_cases hq : q = 0,
  { simp [hq] },
  rw [leading_coeff, degree_mul_eq hp hq, mul_apply_degree_add_degree],
end

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

lemma exists_finset_roots : Π {p : polynomial α} (hp : p ≠ 0),
  ∃ s : finset α, s.card ≤ degree p ∧ ∀ x, x ∈ s ↔ is_root p x
| p := λ hp, by haveI := classical.prop_decidable (∃ x, is_root p x); exact
if h : ∃ x, is_root p x
then
  let ⟨x, hx⟩ := h in
  have hpd : 0 < degree p := nat.pos_of_ne_zero
    (λ h, begin
      rw [eq_C_of_degree_eq_zero h, is_root, eval_C] at hx,
      have h1 : p (degree p) ≠ 0 := mt leading_coeff_eq_zero.1 hp,
      rw h at h1,
      contradiction,
    end),
  have hd0 : div_by_monic p (X - C x) ≠ 0 :=
    λ h, by have := mul_div_eq_iff_is_root.2 hx;
      simp * at *,
  have wf : degree (div_by_monic p _) < degree p :=
    degree_div_by_monic_lt _ (monic_X_sub_C x)
    ((degree_X_sub_C x).symm ▸ nat.succ_pos _) hpd,
  let ⟨t, htd, htr⟩ := @exists_finset_roots (div_by_monic p (X - C x)) hd0 in
  ⟨insert x t, calc (insert x t).card ≤ t.card + 1 : finset.card_insert_le _ _
    ... ≤ degree (div_by_monic p (X - C x)) + 1 : nat.succ_le_succ htd
    ... ≤ _ : nat.succ_le_of_lt wf,
  begin
    assume y,
    rw [mem_insert, htr, eq_comm, ← root_X_sub_C],
    conv {to_rhs, rw ← mul_div_eq_iff_is_root.2 hx},
    exact ⟨λ h, or.cases_on h (root_mul_right_of_is_root _) (root_mul_left_of_is_root _),
      root_or_root_of_root_mul⟩
  end⟩
else
  ⟨∅, nat.zero_le _, by clear exists_finset_roots; finish⟩
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf degree⟩]}

/-- `roots p` noncomputably gives a finset containing all the roots of `p` -/
noncomputable def roots (p : polynomial α) : finset α := 
if h : p = 0 then ∅ else classical.some (exists_finset_roots h)

lemma card_roots (p : polynomial α) : (roots p).card ≤ degree p :=
begin
  unfold roots,
  split_ifs,
  { exact nat.zero_le _ },
  { exact (classical.some_spec (exists_finset_roots h)).1 }
end

lemma mem_roots (hp : p ≠ 0) : a ∈ p.roots ↔ is_root p a :=
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
have C (leading_coeff p)⁻¹ ≠ 0 := mt leading_coeff_eq_zero.2
  $ by rw [leading_coeff_C];
  exact inv_ne_zero (mt leading_coeff_eq_zero.1 h),
by rw [degree_mul_eq h this, degree_C, add_zero]

def div_aux (p q : polynomial α) := 
C (leading_coeff q)⁻¹ * div_by_monic p (q * C (leading_coeff q)⁻¹)

def mod_aux (p q : polynomial α) :=
mod_by_monic p (q * C (leading_coeff q)⁻¹)

private lemma quotient_mul_add_remainder_eq_aux (p q : polynomial α) :
  q * div_aux p q + mod_aux p q = p :=
if h : q = 0 then by simp [h, mod_by_monic, div_aux, mod_aux]
else begin
  conv {to_rhs, rw ← mod_by_monic_add_div p (monic_mul_leading_coeff_inv h)},
  rw [mod_aux, div_aux, add_comm, mul_assoc]
end

/-- `euclid_val_poly` is the Euclidean size function, used in the proof that polynomials over a 
field are a Euclidean domain. `euclid_val_poly 0 = 0` and `euclid_val_poly p = degree p + 1` 
for `p ≠ 0`. -/
def euclid_val_poly (p : polynomial α) := 
if p = 0 then 0 else degree p + 1

@[simp] lemma euclid_val_poly_zero : euclid_val_poly (0 : polynomial α) = 0 := rfl

lemma euclid_val_poly_lt_of_degree_lt (h : degree p < degree q) :
  euclid_val_poly p < euclid_val_poly q :=
begin
  unfold euclid_val_poly,
  split_ifs; 
  simp [*, nat.succ_pos, -add_comm, nat.not_lt_zero, 
    iff.intro nat.lt_of_succ_lt_succ nat.succ_lt_succ] at *
end

private lemma val_remainder_lt_aux (p : polynomial α) (hq : q ≠ 0) :
  euclid_val_poly (mod_aux p q) < euclid_val_poly q :=
or.cases_on (degree_mod_by_monic_lt_or_eq_zero p (monic_mul_leading_coeff_inv hq)) 
begin 
  unfold mod_aux,
  rw [degree_mul_leading_coeff_inv hq],
  exact euclid_val_poly_lt_of_degree_lt
end
(λ h, begin
  rw [mod_aux, h, euclid_val_poly, if_pos rfl, euclid_val_poly, if_neg hq],
  exact nat.succ_pos _
end)

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

end field

end polynomial