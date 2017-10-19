/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Introduces the rational numbers as discrete, linear ordered field.
-/

import data.nat.gcd data.pnat data.int.basic order.basic pending

/- linorder -/

section linear_order_cases_on
universes u v
variables {α : Type u} [decidable_linear_order α] {β : Sort v}

def linear_order_cases_on (a b : α) (h_eq : a = b → β) (h_lt : a < b → β) (h_gt : a > b → β) : β :=
if h₁ : a = b then h_eq h₁ else
  if h₂ : a < b then h_lt h₂ else h_gt ((lt_or_gt_of_ne h₁).resolve_left h₂)

variables {a b : α} {h_eq : a = b → β} {h_lt : a < b → β} {h_gt : a > b → β}

@[simp] theorem linear_order_cases_on_eq (h : a = b) : linear_order_cases_on a b h_eq h_lt h_gt = h_eq h :=
dif_pos h

@[simp] theorem linear_order_cases_on_lt (h : a < b) : linear_order_cases_on a b h_eq h_lt h_gt = h_lt h :=
eq.trans (dif_neg $ ne_of_lt h) $ dif_pos h

@[simp] theorem linear_order_cases_on_gt (h : a > b) : linear_order_cases_on a b h_eq h_lt h_gt = h_gt h :=
eq.trans (dif_neg $ (ne_of_lt h).symm) (dif_neg $ not_lt_of_ge $ le_of_lt h)

end linear_order_cases_on

/- linorder ring -/

section ordered_ring
universes u
variables {α : Type u} [linear_ordered_ring α] {a b : α}

theorem mul_nonneg_iff_right_nonneg_of_pos (h : 0 < a) : 0 ≤ b * a ↔ 0 ≤ b :=
⟨assume : 0 ≤ b * a, nonneg_of_mul_nonneg_right this h, assume : 0 ≤ b, mul_nonneg this $ le_of_lt h⟩

end ordered_ring

/- rational numbers -/

structure rat := mk' ::
(num : ℤ)
(denom : ℕ)
(pos : denom > 0)
(cop : num.nat_abs.coprime denom)
notation `ℚ` := rat

namespace rat

def of_int (n : ℤ) : ℚ :=
⟨n, 1, nat.one_pos, nat.coprime_one_right _⟩

instance coe_int_rat : has_coe ℤ ℚ := ⟨of_int⟩

instance coe_nat_rat : has_coe ℕ ℚ := ⟨of_int ∘ int.of_nat⟩

instance : has_zero ℚ := ⟨(0 : ℤ)⟩

instance : has_one ℚ := ⟨(1 : ℤ)⟩

def mk_pnat (n : ℤ) : ℕ+ → ℚ | ⟨d, dpos⟩ :=
let n' := n.nat_abs, g := n'.gcd d in
⟨n / g, d / g, begin
  apply (nat.le_div_iff_mul_le _ _ (nat.gcd_pos_of_pos_right _ dpos)).2,
  simp, exact nat.le_of_dvd dpos (nat.gcd_dvd_right _ _)
end, begin
  have : int.nat_abs (n / ↑g) = n' / g,
  { cases int.nat_abs_eq n with e e; rw e, { refl },
    rw [int.neg_div_of_dvd, int.nat_abs_neg], { refl },
    exact int.coe_nat_dvd_coe_nat_of_dvd (nat.gcd_dvd_left _ _) },
  rw this,
  exact nat.coprime_div_gcd_div_gcd (nat.gcd_pos_of_pos_right _ dpos)
end⟩

def mk_nat (n : ℤ) (d : ℕ) : ℚ :=
if d0 : d = 0 then 0 else mk_pnat n ⟨d, nat.pos_of_ne_zero d0⟩

def mk : ℤ → ℤ → ℚ
| n (int.of_nat d) := mk_nat n d
| n -[1+ d]        := mk_pnat (-n) d.succ_pnat

local infix ` /. `:70 := mk

theorem mk_pnat_eq (n d h) : mk_pnat n ⟨d, h⟩ = n /. d :=
by change n /. d with dite _ _ _; simp [ne_of_gt h]

theorem mk_nat_eq (n d) : mk_nat n d = n /. d := rfl

@[simp] theorem mk_zero (n) : n /. 0 = 0 := rfl

@[simp] theorem zero_mk_pnat (n) : mk_pnat 0 n = 0 :=
by cases n; simp [mk_pnat]; change int.nat_abs 0 with 0; simp *; refl

@[simp] theorem zero_mk_nat (n) : mk_nat 0 n = 0 :=
by by_cases n = 0; simp [*, mk_nat]

@[simp] theorem zero_mk (n) : 0 /. n = 0 :=
by cases n; simp [mk]

private lemma gcd_abs_eq_left {a b} : (nat.gcd (int.nat_abs a) b : ℤ) ∣ a :=
int.coe_nat_dvd_right.1
  (int.coe_nat_dvd_coe_nat_of_dvd $ nat.gcd_dvd_left (int.nat_abs a) b)

@[simp] theorem mk_eq_zero {a b : ℤ} (b0 : b ≠ 0) : a /. b = 0 ↔ a = 0 :=
begin
  constructor; intro h; [skip, {subst a, simp}],
  have : ∀ {a b}, mk_pnat a b = 0 → a = 0,
  { intros a b e, cases b with b h,
    injection e with e,
    apply int.eq_mul_of_div_eq_right gcd_abs_eq_left e },
  cases b with b; simp [mk, mk_nat] at h,
  { simp [mt (congr_arg int.of_nat) b0] at h,
    exact this h },
  { apply neg_inj, simp [this h] }
end

theorem mk_eq : ∀ {a b c d : ℤ} (hb : b ≠ 0) (hd : d ≠ 0),
  a /. b = c /. d ↔ a * d = c * b :=
suffices ∀ a b c d hb hd, mk_pnat a ⟨b, hb⟩ = mk_pnat c ⟨d, hd⟩ ↔ a * d = c * b,
begin
  intros, cases b with b b; simp [mk, mk_nat, nat.succ_pnat],
  simp [mt (congr_arg int.of_nat) hb],
  all_goals {
    cases d with d d; simp [mk, mk_nat, nat.succ_pnat],
    simp [mt (congr_arg int.of_nat) hd],
    all_goals { rw this, try {refl} } },
  { change a * ↑(d.succ) = -c * ↑b ↔ a * -(d.succ) = c * b,
    constructor; intro h; apply neg_inj; simp at h; simp [h] },
  { change -a * ↑d = c * b.succ ↔ a * d = c * -b.succ,
    constructor; intro h; apply neg_inj; simp at h; simp [h] },
  { change -a * d.succ = -c * b.succ ↔ a * -d.succ = c * -b.succ,
    simp }
end,
begin
  intros, simp [mk_pnat], constructor; intro h,
  { injection h with ha hb,
    have ha, {
      have dv := @gcd_abs_eq_left,
      have := int.eq_mul_of_div_eq_right dv ha,
      rw ← int.mul_div_assoc _ dv at this,
      exact int.eq_mul_of_div_eq_left (dvd_mul_of_dvd_right dv _) this.symm },
    have hb, {
      have dv := λ {a b}, nat.gcd_dvd_right (int.nat_abs a) b,
      have := nat.eq_mul_of_div_eq_right dv hb,
      rw ← nat.mul_div_assoc _ dv at this,
      exact nat.eq_mul_of_div_eq_left (dvd_mul_of_dvd_right dv _) this.symm },
    apply eq_of_mul_eq_mul_right _,
    { rw [mul_assoc, mul_assoc],
      have := congr (congr_arg (*) ha.symm) (congr_arg coe hb),
      simp [int.coe_nat_mul] at this, assumption },
    { apply mt int.coe_nat_inj, apply ne_of_gt,
      apply mul_pos; apply nat.gcd_pos_of_pos_right; assumption } },
  { have : ∀ a c, a * d = c * b →
      a / nat.gcd a b = c / nat.gcd c d ∧ b / nat.gcd a b = d / nat.gcd c d,
    { intros a c h,
      have bd : b / nat.gcd a b = d / nat.gcd c d,
      { have : ∀ {a c} (b>0) (d>0),
          a * d = c * b → b / nat.gcd a b ≤ d / nat.gcd c d,
        tactic.swap, { exact le_antisymm (this _ hb _ hd h) (this _ hd _ hb h.symm) },
        intros a c b hb d hd h,
        have gb0 := nat.gcd_pos_of_pos_right a hb,
        have gd0 := nat.gcd_pos_of_pos_right c hd,
        apply nat.le_of_dvd,
        apply (nat.le_div_iff_mul_le _ _ gd0).2,
        simp, apply nat.le_of_dvd hd (nat.gcd_dvd_right _ _),
        apply nat.dvd_of_coprime_of_dvd_mul_left,
        exact nat.coprime_swap (nat.coprime_div_gcd_div_gcd gb0),
        refine ⟨c / c.gcd d, _⟩,
        rw [← nat.mul_div_assoc _ (nat.gcd_dvd_left _ _),
            ← nat.mul_div_assoc _ (nat.gcd_dvd_right _ _)],
        apply congr_arg (/ c.gcd d),
        rw [mul_comm, ← nat.mul_div_assoc _ (nat.gcd_dvd_left _ _),
            mul_comm, h, nat.mul_div_assoc _ (nat.gcd_dvd_right _ _), mul_comm] },
      refine ⟨_, bd⟩,
      apply nat.eq_of_mul_eq_mul_left hb,
      rw [← nat.mul_div_assoc _ (nat.gcd_dvd_left _ _), mul_comm,
          nat.mul_div_assoc _ (nat.gcd_dvd_right _ _), bd,
          ← nat.mul_div_assoc _ (nat.gcd_dvd_right _ _), h, mul_comm,
          nat.mul_div_assoc _ (nat.gcd_dvd_left _ _)] },
    have ha := this a.nat_abs c.nat_abs begin
      have := congr_arg int.nat_abs h,
      simp [int.nat_abs_mul] at this, exact this
    end,
    tactic.congr_core,
    { have hs := congr_arg int.sign h,
      simp [int.sign_eq_one_of_pos (int.coe_nat_lt_coe_nat_of_lt hb),
            int.sign_eq_one_of_pos (int.coe_nat_lt_coe_nat_of_lt hd)] at hs,
      conv in a { rw ← int.sign_mul_nat_abs a },
      conv in c { rw ← int.sign_mul_nat_abs c },
      rw [int.mul_div_assoc, int.mul_div_assoc],
      exact congr (congr_arg (*) hs) (congr_arg coe ha.left),
      all_goals { exact int.coe_nat_dvd_coe_nat_of_dvd (nat.gcd_dvd_left _ _) } },
    { exact ha.right } }
end

@[simp] theorem div_mk_div_cancel_left {a b c : ℤ} (c0 : c ≠ 0) :
  (a * c) /. (b * c) = a /. b :=
begin
  by_cases b = 0 with b0, { subst b0, simp },
  apply (mk_eq (mul_ne_zero b0 c0) b0).2, simp
end

theorem num_denom : ∀ a : ℚ, a = a.num /. a.denom
| ⟨n, d, h, (c:_=1)⟩ := begin
  change _ = mk_nat n d,
  simp [mk_nat, ne_of_gt h, mk_pnat],
  tactic.congr_core; `[rw c, simp [int.coe_nat_one]]
end

theorem num_denom' (n d h c) : (⟨n, d, h, c⟩ : ℚ) = n /. d := num_denom _

@[elab_as_eliminator] theorem {u} num_denom_cases_on {C : ℚ → Sort u}
   : ∀ (a : ℚ) (H : ∀ n d, d > 0 → (int.nat_abs n).coprime d → C (n /. d)), C a
| ⟨n, d, h, c⟩ H := by rw num_denom'; exact H n d h c

@[elab_as_eliminator] theorem {u} num_denom_cases_on' {C : ℚ → Sort u}
   (a : ℚ) (H : ∀ (n:ℤ) (d:ℕ), (d:ℤ) ≠ 0 → C (n /. d)) : C a :=
num_denom_cases_on a $ λ n d h c,
H n d $ ne_of_gt (int.coe_nat_lt_coe_nat_of_lt h)

protected def add : ℚ → ℚ → ℚ
| ⟨n₁, d₁, h₁, c₁⟩ ⟨n₂, d₂, h₂, c₂⟩ := mk_pnat (n₁ * d₂ + n₂ * d₁) ⟨d₁ * d₂, mul_pos h₁ h₂⟩

instance : has_add ℚ := ⟨rat.add⟩

theorem lift_binop_eq (f : ℚ → ℚ → ℚ) (f₁ : ℤ → ℤ → ℤ → ℤ → ℤ) (f₂ : ℤ → ℤ → ℤ → ℤ → ℤ)
  (fv : ∀ {n₁ d₁ h₁ c₁ n₂ d₂ h₂ c₂},
    f ⟨n₁, d₁, h₁, c₁⟩ ⟨n₂, d₂, h₂, c₂⟩ = f₁ n₁ d₁ n₂ d₂ /. f₂ n₁ d₁ n₂ d₂)
  (f0 : ∀ {n₁ d₁ n₂ d₂} (d₁0 : d₁ ≠ 0) (d₂0 : d₂ ≠ 0), f₂ n₁ d₁ n₂ d₂ ≠ 0)
  (a b c d : ℤ) (b0 : b ≠ 0) (d0 : d ≠ 0)
  (H : ∀ {n₁ d₁ n₂ d₂} (h₁ : a * d₁ = n₁ * b) (h₂ : c * d₂ = n₂ * d),
       f₁ n₁ d₁ n₂ d₂ * f₂ a b c d = f₁ a b c d * f₂ n₁ d₁ n₂ d₂) :
  f (a /. b) (c /. d) = f₁ a b c d /. f₂ a b c d :=
begin
  generalize ha : a /. b = x, cases x with n₁ d₁ h₁ c₁, rw num_denom' at ha,
  generalize hc : c /. d = x, cases x with n₂ d₂ h₂ c₂, rw num_denom' at hc,
  rw fv,
  have d₁0 := ne_of_gt (int.coe_nat_lt_coe_nat_of_lt h₁),
  have d₂0 := ne_of_gt (int.coe_nat_lt_coe_nat_of_lt h₂),
  exact (mk_eq (f0 d₁0 d₂0) (f0 b0 d0)).2 (H ((mk_eq b0 d₁0).1 ha) ((mk_eq d0 d₂0).1 hc))
end

@[simp] theorem add_def {a b c d : ℤ} (b0 : b ≠ 0) (d0 : d ≠ 0) :
  a /. b + c /. d = (a * d + c * b) /. (b * d) :=
begin
  apply lift_binop_eq rat.add; intros; try {assumption},
  { apply mk_pnat_eq },
  { apply mul_ne_zero d₁0 d₂0 },
  calc (n₁ * d₂ + n₂ * d₁) * (b * d) =
          (n₁ * b) * d₂ * d + (n₂ * d) * (d₁ * b) : by simp [mul_add, add_mul]
    ... = (a * d₁) * d₂ * d + (c * d₂) * (d₁ * b) : by rw [h₁, h₂]
    ... = (a * d + c * b) * (d₁ * d₂)             : by simp [mul_add, add_mul]
end

protected def neg : ℚ → ℚ
| ⟨n, d, h, c⟩ := ⟨-n, d, h, by simp [c]⟩

instance : has_neg ℚ := ⟨rat.neg⟩

@[simp] theorem neg_def {a b : ℤ} : -(a /. b) = -a /. b :=
begin
  by_cases b = 0 with b0, { subst b0, simp, refl },
  generalize ha : a /. b = x, cases x with n₁ d₁ h₁ c₁, rw num_denom' at ha,
  show rat.mk' _ _ _ _ = _, rw num_denom',
  have d0 := ne_of_gt (int.coe_nat_lt_coe_nat_of_lt h₁),
  apply (mk_eq d0 b0).2, have h₁ := (mk_eq b0 d0).1 ha,
  simp only [neg_mul_eq_neg_mul_symm, congr_arg has_neg.neg h₁]
end

protected def mul : ℚ → ℚ → ℚ
| ⟨n₁, d₁, h₁, c₁⟩ ⟨n₂, d₂, h₂, c₂⟩ := mk_pnat (n₁ * n₂) ⟨d₁ * d₂, mul_pos h₁ h₂⟩

instance : has_mul ℚ := ⟨rat.mul⟩

@[simp] theorem mul_def {a b c d : ℤ} (b0 : b ≠ 0) (d0 : d ≠ 0) :
  (a /. b) * (c /. d) = (a * c) /. (b * d) :=
begin
  apply lift_binop_eq rat.mul; intros; try {assumption},
  { apply mk_pnat_eq },
  { apply mul_ne_zero d₁0 d₂0 },
  cc
end

protected def inv : ℚ → ℚ
| ⟨(n+1:ℕ), d, h, c⟩ := ⟨d, n+1, n.succ_pos, nat.coprime_swap c⟩
| ⟨0, d, h, c⟩ := 0
| ⟨-[1+ n], d, h, c⟩ := ⟨-d, n+1, n.succ_pos, nat.coprime_swap $ by simp; exact c⟩

instance : has_inv ℚ := ⟨rat.inv⟩

@[simp] theorem inv_def {a b : ℤ} : (a /. b)⁻¹ = b /. a :=
begin
  by_cases a = 0 with a0, { subst a0, simp, refl },
  by_cases b = 0 with b0, { subst b0, simp, refl },
  generalize ha : a /. b = x, cases x with n d h c, rw num_denom' at ha,
  refine eq.trans (_ : rat.inv ⟨n, d, h, c⟩ = d /. n) _,
  { cases n with n; [cases n with n, skip],
    { refl },
    { change int.of_nat n.succ with (n+1:ℕ),
      simp [rat.inv], rw num_denom' },
    { simp [rat.inv], rw num_denom', refl } },
  have n0 : n ≠ 0,
  { refine mt (λ (n0 : n = 0), _) a0,
    subst n0, simp at ha,
    exact (mk_eq_zero b0).1 ha },
  have d0 := ne_of_gt (int.coe_nat_lt_coe_nat_of_lt h),
  have ha := (mk_eq b0 d0).1 ha,
  apply (mk_eq n0 a0).2,
  cc
end

variables (a b c : ℚ)

protected theorem add_zero : a + 0 = a :=
num_denom_cases_on' a $ λ n d h,
by rw [← zero_mk d]; simp [h, -zero_mk]

protected theorem zero_add : 0 + a = a :=
num_denom_cases_on' a $ λ n d h,
by rw [← zero_mk d]; simp [h, -zero_mk]

protected theorem add_comm : a + b = b + a :=
num_denom_cases_on' a $ λ n₁ d₁ h₁,
num_denom_cases_on' b $ λ n₂ d₂ h₂,
by simp [h₁, h₂]

protected theorem add_assoc : a + b + c = a + (b + c) :=
num_denom_cases_on' a $ λ n₁ d₁ h₁,
num_denom_cases_on' b $ λ n₂ d₂ h₂,
num_denom_cases_on' c $ λ n₃ d₃ h₃,
by simp [h₁, h₂, h₃, mul_ne_zero, mul_add]

protected theorem add_left_neg : -a + a = 0 :=
num_denom_cases_on' a $ λ n d h,
by simp [h]

protected theorem mul_one : a * 1 = a :=
num_denom_cases_on' a $ λ n d h,
by change (1:ℚ) with 1 /. 1; simp [h]

protected theorem one_mul : 1 * a = a :=
num_denom_cases_on' a $ λ n d h,
by change (1:ℚ) with 1 /. 1; simp [h]

protected theorem mul_comm : a * b = b * a :=
num_denom_cases_on' a $ λ n₁ d₁ h₁,
num_denom_cases_on' b $ λ n₂ d₂ h₂,
by simp [h₁, h₂]

protected theorem mul_assoc : a * b * c = a * (b * c) :=
num_denom_cases_on' a $ λ n₁ d₁ h₁,
num_denom_cases_on' b $ λ n₂ d₂ h₂,
num_denom_cases_on' c $ λ n₃ d₃ h₃,
by simp [h₁, h₂, h₃, mul_ne_zero]

protected theorem add_mul : (a + b) * c = a * c + b * c :=
num_denom_cases_on' a $ λ n₁ d₁ h₁,
num_denom_cases_on' b $ λ n₂ d₂ h₂,
num_denom_cases_on' c $ λ n₃ d₃ h₃,
by simp [h₁, h₂, h₃, mul_ne_zero];
   refine (div_mk_div_cancel_left h₃).symm.trans _;
   simp [mul_add]

protected theorem mul_add : a * (b + c) = a * b + a * c :=
by rw [rat.mul_comm, rat.add_mul, rat.mul_comm, rat.mul_comm c a]

protected theorem zero_ne_one : 0 ≠ (1:ℚ) :=
mt (λ (h : 0 = 1 /. 1), (mk_eq_zero one_ne_zero).1 h.symm) one_ne_zero

protected theorem mul_inv_cancel : a ≠ 0 → a * a⁻¹ = 1 :=
num_denom_cases_on' a $ λ n d h a0,
have n0 : n ≠ 0, from mt (by intro e; subst e; simp) a0,
by simp [h, n0]; exact
eq.trans (by simp) (@div_mk_div_cancel_left 1 1 _ n0)

protected theorem inv_mul_cancel (h : a ≠ 0) : a⁻¹ * a = 1 :=
eq.trans (rat.mul_comm _ _) (rat.mul_inv_cancel _ h)

instance : decidable_eq ℚ := by tactic.mk_dec_eq_instance

instance field_rat : discrete_field ℚ :=
{ zero             := 0,
  add              := rat.add,
  neg              := rat.neg,
  one              := 1,
  mul              := rat.mul,
  inv              := rat.inv,
  zero_add         := rat.zero_add,
  add_zero         := rat.add_zero,
  add_comm         := rat.add_comm,
  add_assoc        := rat.add_assoc,
  add_left_neg     := rat.add_left_neg,
  mul_one          := rat.mul_one,
  one_mul          := rat.one_mul,
  mul_comm         := rat.mul_comm,
  mul_assoc        := rat.mul_assoc,
  left_distrib     := rat.mul_add,
  right_distrib    := rat.add_mul,
  zero_ne_one      := rat.zero_ne_one,
  mul_inv_cancel   := rat.mul_inv_cancel,
  inv_mul_cancel   := rat.inv_mul_cancel,
  has_decidable_eq := rat.decidable_eq,
  inv_zero         := rfl }

protected def nonneg : ℚ → Prop
| ⟨n, d, h, c⟩ := n ≥ 0

@[simp] theorem mk_nonneg (a : ℤ) {b : ℤ} (h : b > 0) : (a /. b).nonneg ↔ a ≥ 0 :=
begin
  generalize ha : a /. b = x, cases x with n₁ d₁ h₁ c₁, rw num_denom' at ha,
  simp [rat.nonneg],
  have d0 := int.coe_nat_lt_coe_nat_of_lt h₁,
  have := (mk_eq (ne_of_gt h) (ne_of_gt d0)).1 ha,
  constructor; intro h₂,
  { apply nonneg_of_mul_nonneg_right _ d0,
    rw this, exact mul_nonneg h₂ (le_of_lt h) },
  { apply nonneg_of_mul_nonneg_right _ h,
    rw ← this, exact mul_nonneg h₂ (int.coe_zero_le _) },
end

protected def nonneg_add {a b} : rat.nonneg a → rat.nonneg b → rat.nonneg (a + b) :=
num_denom_cases_on' a $ λ n₁ d₁ h₁,
num_denom_cases_on' b $ λ n₂ d₂ h₂,
begin
  have d₁0 : (d₁:ℤ) > 0 := lt_of_le_of_ne (int.coe_zero_le _) h₁.symm,
  have d₂0 : (d₂:ℤ) > 0 := lt_of_le_of_ne (int.coe_zero_le _) h₂.symm,
  simp [d₁0, d₂0, h₁, h₂, mul_pos d₁0 d₂0],
  intros n₁0 n₂0,
  apply add_nonneg; apply mul_nonneg; {assumption <|> apply int.coe_zero_le}
end

protected def nonneg_mul {a b} : rat.nonneg a → rat.nonneg b → rat.nonneg (a * b) :=
num_denom_cases_on' a $ λ n₁ d₁ h₁,
num_denom_cases_on' b $ λ n₂ d₂ h₂,
begin
  have d₁0 : (d₁:ℤ) > 0 := lt_of_le_of_ne (int.coe_zero_le _) h₁.symm,
  have d₂0 : (d₂:ℤ) > 0 := lt_of_le_of_ne (int.coe_zero_le _) h₂.symm,
  simp [d₁0, d₂0, h₁, h₂, mul_pos d₁0 d₂0],
  exact mul_nonneg
end

protected def nonneg_antisymm {a} : rat.nonneg a → rat.nonneg (-a) → a = 0 :=
num_denom_cases_on' a $ λ n d h,
begin
  have d0 : (d:ℤ) > 0 := lt_of_le_of_ne (int.coe_zero_le _) h.symm,
  simp [d0, h],
  exact λ h₁ h₂, le_antisymm (nonpos_of_neg_nonneg h₂) h₁
end

protected def nonneg_total : rat.nonneg a ∨ rat.nonneg (-a) :=
by cases a with n; exact
or.imp_right neg_nonneg_of_nonpos (le_total 0 n)

instance decidable_nonneg : decidable (rat.nonneg a) :=
by cases a; unfold rat.nonneg; apply_instance

protected def le (a b : ℚ) := rat.nonneg (b - a)

instance : has_le ℚ := ⟨rat.le⟩

instance decidable_le : decidable_rel ((≤) : ℚ → ℚ → Prop) :=
show ∀ a b, decidable (rat.nonneg (b - a)), by intros; apply_instance

protected theorem le_refl : a ≤ a :=
show rat.nonneg (a - a), begin rw [sub_self], exact le_refl (0 : int) end

protected theorem le_total : a ≤ b ∨ b ≤ a :=
by have := rat.nonneg_total (b - a); rwa neg_sub at this

protected theorem le_antisymm {a b : ℚ} (hab : a ≤ b) (hba : b ≤ a) : a = b :=
by have := eq_neg_of_add_eq_zero (rat.nonneg_antisymm hba $ by simp; assumption);
   rwa neg_neg at this

protected theorem le_trans {a b c : ℚ} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
by have := rat.nonneg_add hab hbc; simp at this; exact this

instance : linear_order ℚ :=
{ le              := rat.le,
  lt              := λa b, a ≤ b ∧ a ≠ b,
  lt_iff_le_not_le := assume a b,
    iff.intro 
      (assume ⟨h1, h2⟩, 
       have hnle : ¬ b ≤ a, from
        assume hle,
        have a = b, from rat.le_antisymm h1 hle,
        h2 this,
       ⟨or.resolve_left (rat.le_total _ _) hnle, hnle⟩)
      (assume ⟨h1, h2⟩, 
       ⟨h1, 
        assume heq, 
        suffices ¬b≤b, from this (rat.le_refl _), 
        by rw heq at h2; assumption⟩),
  le_refl         := rat.le_refl,
  le_trans        := @rat.le_trans,
  le_antisymm     := @rat.le_antisymm,
  le_total        := rat.le_total }

theorem nonneg_iff_zero_le {a} : rat.nonneg a ↔ 0 ≤ a :=
show rat.nonneg a ↔ rat.nonneg (a - 0), by simp

protected theorem add_le_add_left {a b c : ℚ} : c + a ≤ c + b ↔ a ≤ b :=
by unfold has_le.le rat.le; rw add_sub_add_left_eq_sub

protected theorem add_lt_add_left {a b c : ℚ} : c + a < c + b ↔ a < b :=
⟨assume ⟨h1, h2⟩, ⟨rat.add_le_add_left.mp h1, λ h, by cc⟩,
 assume ⟨h1, h2⟩, ⟨rat.add_le_add_left.mpr h1, λ h, h2 (eq_of_add_eq_add_left h)⟩⟩

protected theorem mul_nonneg {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b :=
by simp [nonneg_iff_zero_le.symm] at *; exact rat.nonneg_mul ha hb

instance : discrete_linear_ordered_field ℚ :=
{ rat.field_rat with
  le              := (≤),
  lt              := (<),
  le_refl         := le_refl,
  le_trans        := @rat.le_trans,
  le_antisymm     := assume a b, le_antisymm,
  le_total        := le_total,
  lt_iff_le_not_le := @lt_iff_le_not_le _ _,
  zero_lt_one     := show (0:ℚ) ≤ 1 ∧ (0:ℚ) ≠ 1, from dec_trivial,
  add_le_add_left := assume a b ab c, rat.add_le_add_left.2 ab,
  add_lt_add_left := assume a b ab c, rat.add_lt_add_left.2 ab,
  mul_nonneg      := @rat.mul_nonneg,
  mul_pos         := assume a b ha hb, lt_of_le_of_ne
    (rat.mul_nonneg (le_of_lt ha) (le_of_lt hb))
    (mul_ne_zero (ne_of_lt ha).symm (ne_of_lt hb).symm).symm,
  decidable_eq    := by apply_instance,
  decidable_le    := assume a b, rat.decidable_nonneg (b - a),
  decidable_lt    := by apply_instance }

lemma coe_int_eq_mk (z : ℤ) : ↑z = rat.mk z 1 :=
show rat.of_int z = rat.mk_nat z 1,
  by unfold rat.of_int rat.mk_nat; simp [rat.mk_pnat, int.coe_nat_one]

lemma coe_nat_rat_eq_mk (n : ℕ) : ↑n = rat.mk ↑n 1 := coe_int_eq_mk _

lemma coe_int_add (z₁ z₂ : ℤ) : ↑(z₁ + z₂) = (↑z₁ + ↑z₂ : ℚ) := by simp [coe_int_eq_mk]

lemma coe_int_sub (z₁ z₂ : ℤ) : ↑(z₁ - z₂) = (↑z₁ - ↑z₂ : ℚ) := by simp [coe_int_eq_mk]

lemma coe_int_one : ↑(1 : ℤ) = (1 : ℚ) := rfl

lemma le_of_of_int_le_of_int {z₁ z₂ : ℤ} (h : (↑z₁ : ℚ) ≤ ↑z₂) : z₁ ≤ z₂ :=
have rat.nonneg ↑(z₂ - z₁), by rwa [coe_int_sub],
have 0 ≤ z₂ - z₁, by rwa [coe_int_eq_mk, rat.mk_nonneg] at this; exact zero_lt_one,
have z₁ + 0 ≤ z₂, from add_le_of_le_sub_left this,
by simp [*] at *

def floor : ℚ → ℤ
| ⟨n, d, h, c⟩ := n / d

def ceil (r : ℚ) : ℤ :=
-(floor (-r))

/- nat ceiling -/

lemma exists_upper_nat_bound (q:ℚ) : ∃n:ℕ, q ≤ ↑n :=
rat.num_denom_cases_on' q $ λn d h₁,
have h₂ : ↑d > (0:int), from lt_of_le_of_ne (int.coe_zero_le d) h₁.symm,
have h₃ : (1:int) ≤ ↑d, from calc 1 = 0 + 1 : by simp
   ... ≤ (↑d:int) : int.add_one_le_of_lt h₂,
have n ≤ ↑d * ↑(int.to_nat n),
  from calc n ≤ 1 * ↑(int.to_nat n) : begin simp, cases n, apply le_refl, simp [int.to_nat] end
    ... ≤ ↑d * ↑(int.to_nat n): mul_le_mul h₃ (le_refl _) (int.coe_zero_le _) (int.coe_zero_le _),
⟨int.to_nat n, show rat.nonneg (↑(int.to_nat n) - rat.mk n ↑d),
begin
  simp [h₁, h₂, coe_nat_rat_eq_mk, mk_nonneg],
  rw [add_comm, ←sub_eq_add_neg, ge],
  apply le_sub_left_of_add_le,
  simp,
  assumption
end⟩

def nat_ceil (q : ℚ) : ℕ := nat.find (exists_upper_nat_bound q)

lemma nat_ceil_spec {q : ℚ} : q ≤ nat_ceil q :=
nat.find_spec (exists_upper_nat_bound q)

lemma nat_ceil_min {q : ℚ} {n : ℕ} : q ≤ n → nat_ceil q ≤ n :=
nat.find_min' (exists_upper_nat_bound q)

lemma nat_ceil_mono {q₁ q₂ : ℚ} (h : q₁ ≤ q₂) : nat_ceil q₁ ≤ nat_ceil q₂ :=
nat_ceil_min $ le_trans h nat_ceil_spec

@[simp] lemma nat_ceil_zero : nat_ceil 0 = 0 :=
le_antisymm (nat_ceil_min $ le_refl _) (nat.zero_le _)

lemma nat_ceil_add_one_eq {q : ℚ} (hq : 0 ≤ q) : nat_ceil (q + 1) = nat_ceil q + 1 :=
le_antisymm
  (nat_ceil_min $ show q + 1 ≤ ↑(int.of_nat $ nat_ceil q + 1),
    begin
      simp [int.of_nat_add, int.of_nat_one, coe_int_add, coe_int_one, -add_comm],
      exact add_le_add_right nat_ceil_spec 1
    end)
  (have (↑(1:ℤ):ℚ) ≤ nat_ceil (q + 1),
      from le_trans (le_add_of_nonneg_left hq) nat_ceil_spec, 
    have h1le : 1 ≤ nat_ceil (q + 1),
      from (int.coe_nat_le_coe_nat_iff _ _).mp $ le_of_of_int_le_of_int this,
    have nat_ceil q ≤ nat_ceil (q + 1) - 1,
      from nat_ceil_min $ show q ≤ ↑(int.of_nat (nat_ceil (q + 1) - 1)),
      begin
        rw [int.of_nat_sub h1le],
        simp [-sub_eq_add_neg, coe_int_sub, int.of_nat_one, coe_int_one],
        exact le_sub_right_of_add_le nat_ceil_spec
      end,
    show nat_ceil q + 1 ≤ nat_ceil (q + 1),
      from (nat.add_le_to_le_sub _ h1le).mpr this)

lemma nat_ceil_lt_add_one {q : ℚ} (hq : q ≥ 0) : ↑(nat_ceil q) < q + 1 :=
lt_of_not_ge $ assume h : q + 1 ≤ ↑(nat_ceil q),
  have nat_ceil q + 0 = nat_ceil q + 1,
    from calc nat_ceil q + 0 = nat_ceil q : by simp
      ... = nat_ceil (q + 1) :
        le_antisymm (nat_ceil_mono $ le_add_of_le_of_nonneg (le_refl _) zero_le_one) (nat_ceil_min h)
      ... = nat_ceil q + 1 : nat_ceil_add_one_eq hq,
  nat.no_confusion $ eq_of_add_eq_add_left this

end rat
