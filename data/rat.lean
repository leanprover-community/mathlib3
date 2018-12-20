/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Introduces the rational numbers as discrete, linear ordered field.
-/

import
  data.nat.gcd data.pnat data.int.sqrt data.equiv.encodable order.basic
  algebra.ordered_field data.real.cau_seq

/- rational numbers -/

/-- `rat`, or `ℚ`, is the type of rational numbers. It is defined
  as the set of pairs ⟨n, d⟩ of integers such that `d` is positive and `n` and
  `d` are coprime. This representation is preferred to the quotient
  because without periodic reduction, the numerator and denominator can grow
  exponentially (for example, adding 1/2 to itself repeatedly). -/
structure rat := mk' ::
(num : ℤ)
(denom : ℕ)
(pos : denom > 0)
(cop : num.nat_abs.coprime denom)
notation `ℚ` := rat

namespace rat

protected def repr : ℚ → string
| ⟨n, d, _, _⟩ := if d = 1 then _root_.repr n else
  _root_.repr n ++ "/" ++ _root_.repr d

instance : has_repr ℚ := ⟨rat.repr⟩
instance : has_to_string ℚ := ⟨rat.repr⟩
meta instance : has_to_format ℚ := ⟨coe ∘ rat.repr⟩

instance : encodable ℚ := encodable.of_equiv (Σ n : ℤ, {d : ℕ // d > 0 ∧ n.nat_abs.coprime d})
  ⟨λ ⟨a, b, c, d⟩, ⟨a, b, c, d⟩, λ⟨a, b, c, d⟩, ⟨a, b, c, d⟩,
   λ ⟨a, b, c, d⟩, rfl, λ⟨a, b, c, d⟩, rfl⟩

/-- Embed an integer as a rational number -/
def of_int (n : ℤ) : ℚ :=
⟨n, 1, nat.one_pos, nat.coprime_one_right _⟩

instance : has_zero ℚ := ⟨of_int 0⟩
instance : has_one ℚ := ⟨of_int 1⟩
instance : inhabited ℚ := ⟨0⟩

/-- Form the quotient `n / d` where `n:ℤ` and `d:ℕ+` (not necessarily coprime) -/
def mk_pnat (n : ℤ) : ℕ+ → ℚ | ⟨d, dpos⟩ :=
let n' := n.nat_abs, g := n'.gcd d in
⟨n / g, d / g, begin
  apply (nat.le_div_iff_mul_le _ _ (nat.gcd_pos_of_pos_right _ dpos)).2,
  simp, exact nat.le_of_dvd dpos (nat.gcd_dvd_right _ _)
end, begin
  have : int.nat_abs (n / ↑g) = n' / g,
  { cases int.nat_abs_eq n with e e; rw e, { refl },
    rw [int.neg_div_of_dvd, int.nat_abs_neg], { refl },
    exact int.coe_nat_dvd.2 (nat.gcd_dvd_left _ _) },
  rw this,
  exact nat.coprime_div_gcd_div_gcd (nat.gcd_pos_of_pos_right _ dpos)
end⟩

/-- Form the quotient `n / d` where `n:ℤ` and `d:ℕ`. In the case `d = 0`, we
  define `n / 0 = 0` by convention. -/
def mk_nat (n : ℤ) (d : ℕ) : ℚ :=
if d0 : d = 0 then 0 else mk_pnat n ⟨d, nat.pos_of_ne_zero d0⟩

/-- Form the quotient `n / d` where `n d : ℤ`. -/
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

private lemma gcd_abs_dvd_left {a b} : (nat.gcd (int.nat_abs a) b : ℤ) ∣ a :=
int.dvd_nat_abs.1 $ int.coe_nat_dvd.2 $ nat.gcd_dvd_left (int.nat_abs a) b

@[simp] theorem mk_eq_zero {a b : ℤ} (b0 : b ≠ 0) : a /. b = 0 ↔ a = 0 :=
begin
  constructor; intro h; [skip, {subst a, simp}],
  have : ∀ {a b}, mk_pnat a b = 0 → a = 0,
  { intros a b e, cases b with b h,
    injection e with e,
    apply int.eq_mul_of_div_eq_right gcd_abs_dvd_left e },
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
    constructor; intro h; apply neg_inj; simpa [left_distrib, neg_add_eq_iff_eq_add,
      eq_neg_iff_add_eq_zero, neg_eq_iff_add_eq_zero] using h },
  { change -a * ↑d = c * b.succ ↔ a * d = c * -b.succ,
    constructor; intro h; apply neg_inj; simpa [left_distrib, eq_comm] using h },
  { change -a * d.succ = -c * b.succ ↔ a * -d.succ = c * -b.succ,
    simp [left_distrib] }
end,
begin
  intros, simp [mk_pnat], constructor; intro h,
  { cases h with ha hb,
    have ha, {
      have dv := @gcd_abs_dvd_left,
      have := int.eq_mul_of_div_eq_right dv ha,
      rw ← int.mul_div_assoc _ dv at this,
      exact int.eq_mul_of_div_eq_left (dvd_mul_of_dvd_right dv _) this.symm },
    have hb, {
      have dv := λ {a b}, nat.gcd_dvd_right (int.nat_abs a) b,
      have := nat.eq_mul_of_div_eq_right dv hb,
      rw ← nat.mul_div_assoc _ dv at this,
      exact nat.eq_mul_of_div_eq_left (dvd_mul_of_dvd_right dv _) this.symm },
    have m0 : (a.nat_abs.gcd b * c.nat_abs.gcd d : ℤ) ≠ 0, {
      refine int.coe_nat_ne_zero.2 (ne_of_gt _),
      apply mul_pos; apply nat.gcd_pos_of_pos_right; assumption },
    apply eq_of_mul_eq_mul_right m0,
    simpa [mul_comm, mul_left_comm] using
      congr (congr_arg (*) ha.symm) (congr_arg coe hb) },
  { suffices : ∀ a c, a * d = c * b →
      a / a.gcd b = c / c.gcd d ∧ b / a.gcd b = d / c.gcd d,
    { cases this a.nat_abs c.nat_abs
        (by simpa [int.nat_abs_mul] using congr_arg int.nat_abs h) with h₁ h₂,
      have hs := congr_arg int.sign h,
      simp [int.sign_eq_one_of_pos (int.coe_nat_lt.2 hb),
            int.sign_eq_one_of_pos (int.coe_nat_lt.2 hd)] at hs,
      conv in a { rw ← int.sign_mul_nat_abs a },
      conv in c { rw ← int.sign_mul_nat_abs c },
      rw [int.mul_div_assoc, int.mul_div_assoc],
      exact ⟨congr (congr_arg (*) hs) (congr_arg coe h₁), h₂⟩,
      all_goals { exact int.coe_nat_dvd.2 (nat.gcd_dvd_left _ _) } },
    intros a c h,
    suffices bd : b / a.gcd b = d / c.gcd d,
    { refine ⟨_, bd⟩,
      apply nat.eq_of_mul_eq_mul_left hb,
      rw [← nat.mul_div_assoc _ (nat.gcd_dvd_left _ _), mul_comm,
          nat.mul_div_assoc _ (nat.gcd_dvd_right _ _), bd,
          ← nat.mul_div_assoc _ (nat.gcd_dvd_right _ _), h, mul_comm,
          nat.mul_div_assoc _ (nat.gcd_dvd_left _ _)] },
    suffices : ∀ {a c : ℕ} (b>0) (d>0),
      a * d = c * b → b / a.gcd b ≤ d / c.gcd d,
    { exact le_antisymm (this _ hb _ hd h) (this _ hd _ hb h.symm) },
    intros a c b hb d hd h,
    have gb0 := nat.gcd_pos_of_pos_right a hb,
    have gd0 := nat.gcd_pos_of_pos_right c hd,
    apply nat.le_of_dvd,
    apply (nat.le_div_iff_mul_le _ _ gd0).2,
    simp, apply nat.le_of_dvd hd (nat.gcd_dvd_right _ _),
    apply (nat.coprime_div_gcd_div_gcd gb0).symm.dvd_of_dvd_mul_left,
    refine ⟨c / c.gcd d, _⟩,
    rw [← nat.mul_div_assoc _ (nat.gcd_dvd_left _ _),
        ← nat.mul_div_assoc _ (nat.gcd_dvd_right _ _)],
    apply congr_arg (/ c.gcd d),
    rw [mul_comm, ← nat.mul_div_assoc _ (nat.gcd_dvd_left _ _),
        mul_comm, h, nat.mul_div_assoc _ (nat.gcd_dvd_right _ _), mul_comm] }
end

@[simp] theorem div_mk_div_cancel_left {a b c : ℤ} (c0 : c ≠ 0) :
  (a * c) /. (b * c) = a /. b :=
begin
  by_cases b0 : b = 0, { subst b0, simp },
  apply (mk_eq (mul_ne_zero b0 c0) b0).2, simp [mul_comm, mul_assoc]
end

theorem num_denom : ∀ a : ℚ, a = a.num /. a.denom
| ⟨n, d, h, (c:_=1)⟩ := show _ = mk_nat n d,
  by simp [mk_nat, ne_of_gt h, mk_pnat, c]

theorem num_denom' (n d h c) : (⟨n, d, h, c⟩ : ℚ) = n /. d := num_denom _

@[elab_as_eliminator] theorem {u} num_denom_cases_on {C : ℚ → Sort u}
   : ∀ (a : ℚ) (H : ∀ n d, d > 0 → (int.nat_abs n).coprime d → C (n /. d)), C a
| ⟨n, d, h, c⟩ H := by rw num_denom'; exact H n d h c

@[elab_as_eliminator] theorem {u} num_denom_cases_on' {C : ℚ → Sort u}
   (a : ℚ) (H : ∀ (n:ℤ) (d:ℕ), d ≠ 0 → C (n /. d)) : C a :=
num_denom_cases_on a $ λ n d h c,
H n d $ ne_of_gt h

theorem num_dvd (a) {b : ℤ} (b0 : b ≠ 0) : (a /. b).num ∣ a :=
begin
  cases e : a /. b with n d h c,
  rw [rat.num_denom', rat.mk_eq b0
    (ne_of_gt (int.coe_nat_pos.2 h))] at e,
  refine (int.nat_abs_dvd.1 $ int.dvd_nat_abs.1 $ int.coe_nat_dvd.2 $
    c.dvd_of_dvd_mul_right _),
  have := congr_arg int.nat_abs e,
  simp [int.nat_abs_mul, int.nat_abs_of_nat] at this, simp [this]
end

theorem denom_dvd (a b : ℤ) : ((a /. b).denom : ℤ) ∣ b :=
begin
  by_cases b0 : b = 0, {simp [b0]},
  cases e : a /. b with n d h c,
  rw [num_denom', mk_eq b0 (ne_of_gt (int.coe_nat_pos.2 h))] at e,
  refine (int.dvd_nat_abs.1 $ int.coe_nat_dvd.2 $ c.symm.dvd_of_dvd_mul_left _),
  rw [← int.nat_abs_mul, ← int.coe_nat_dvd, int.dvd_nat_abs, ← e], simp
end

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
  have d₁0 := ne_of_gt (int.coe_nat_lt.2 h₁),
  have d₂0 := ne_of_gt (int.coe_nat_lt.2 h₂),
  exact (mk_eq (f0 d₁0 d₂0) (f0 b0 d0)).2 (H ((mk_eq b0 d₁0).1 ha) ((mk_eq d0 d₂0).1 hc))
end

@[simp] theorem add_def {a b c d : ℤ} (b0 : b ≠ 0) (d0 : d ≠ 0) :
  a /. b + c /. d = (a * d + c * b) /. (b * d) :=
begin
  apply lift_binop_eq rat.add; intros; try {assumption},
  { apply mk_pnat_eq },
  { apply mul_ne_zero d₁0 d₂0 },
  calc (n₁ * d₂ + n₂ * d₁) * (b * d) =
          (n₁ * b) * d₂ * d + (n₂ * d) * (d₁ * b) : by simp [mul_add, mul_comm, mul_left_comm]
    ... = (a * d₁) * d₂ * d + (c * d₂) * (d₁ * b) : by rw [h₁, h₂]
    ... = (a * d + c * b) * (d₁ * d₂)             : by simp [mul_add, mul_comm, mul_left_comm]
end

protected def neg : ℚ → ℚ
| ⟨n, d, h, c⟩ := ⟨-n, d, h, by simp [c]⟩

instance : has_neg ℚ := ⟨rat.neg⟩

@[simp] theorem neg_def {a b : ℤ} : -(a /. b) = -a /. b :=
begin
  by_cases b0 :  b = 0, { subst b0, simp, refl },
  generalize ha : a /. b = x, cases x with n₁ d₁ h₁ c₁, rw num_denom' at ha,
  show rat.mk' _ _ _ _ = _, rw num_denom',
  have d0 := ne_of_gt (int.coe_nat_lt.2 h₁),
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
| ⟨(n+1:ℕ), d, h, c⟩ := ⟨d, n+1, n.succ_pos, c.symm⟩
| ⟨0, d, h, c⟩ := 0
| ⟨-[1+ n], d, h, c⟩ := ⟨-d, n+1, n.succ_pos, nat.coprime.symm $ by simp; exact c⟩

instance : has_inv ℚ := ⟨rat.inv⟩

@[simp] theorem inv_def {a b : ℤ} : (a /. b)⁻¹ = b /. a :=
begin
  by_cases a0 : a = 0, { subst a0, simp, refl },
  by_cases b0 : b = 0, { subst b0, simp, refl },
  generalize ha : a /. b = x, cases x with n d h c, rw num_denom' at ha,
  refine eq.trans (_ : rat.inv ⟨n, d, h, c⟩ = d /. n) _,
  { cases n with n; [cases n with n, skip],
    { refl },
    { change int.of_nat n.succ with (n+1:ℕ),
      unfold rat.inv, rw num_denom' },
    { unfold rat.inv, rw num_denom', refl } },
  have n0 : n ≠ 0,
  { refine mt (λ (n0 : n = 0), _) a0,
    subst n0, simp at ha,
    exact (mk_eq_zero b0).1 ha },
  have d0 := ne_of_gt (int.coe_nat_lt.2 h),
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
by simp [h₁, h₂, mul_comm]

protected theorem add_assoc : a + b + c = a + (b + c) :=
num_denom_cases_on' a $ λ n₁ d₁ h₁,
num_denom_cases_on' b $ λ n₂ d₂ h₂,
num_denom_cases_on' c $ λ n₃ d₃ h₃,
by simp [h₁, h₂, h₃, mul_ne_zero, mul_add, mul_comm, mul_left_comm, add_left_comm]

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
by simp [h₁, h₂, mul_comm]

protected theorem mul_assoc : a * b * c = a * (b * c) :=
num_denom_cases_on' a $ λ n₁ d₁ h₁,
num_denom_cases_on' b $ λ n₂ d₂ h₂,
num_denom_cases_on' c $ λ n₃ d₃ h₃,
by simp [h₁, h₂, h₃, mul_ne_zero, mul_comm, mul_left_comm]

protected theorem add_mul : (a + b) * c = a * c + b * c :=
num_denom_cases_on' a $ λ n₁ d₁ h₁,
num_denom_cases_on' b $ λ n₂ d₂ h₂,
num_denom_cases_on' c $ λ n₃ d₃ h₃,
by simp [h₁, h₂, h₃, mul_ne_zero];
   refine (div_mk_div_cancel_left (int.coe_nat_ne_zero.2 h₃)).symm.trans _;
   simp [mul_add, mul_comm, mul_assoc, mul_left_comm]

protected theorem mul_add : a * (b + c) = a * b + a * c :=
by rw [rat.mul_comm, rat.add_mul, rat.mul_comm, rat.mul_comm c a]

protected theorem zero_ne_one : 0 ≠ (1:ℚ) :=
mt (λ (h : 0 = 1 /. 1), (mk_eq_zero one_ne_zero).1 h.symm) one_ne_zero

protected theorem mul_inv_cancel : a ≠ 0 → a * a⁻¹ = 1 :=
num_denom_cases_on' a $ λ n d h a0,
have n0 : n ≠ 0, from mt (by intro e; subst e; simp) a0,
by simp [h, n0, mul_comm]; exact
eq.trans (by simp) (@div_mk_div_cancel_left 1 1 _ n0)

protected theorem inv_mul_cancel (h : a ≠ 0) : a⁻¹ * a = 1 :=
eq.trans (rat.mul_comm _ _) (rat.mul_inv_cancel _ h)

instance : decidable_eq ℚ := by tactic.mk_dec_eq_instance

instance : discrete_field ℚ :=
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

/- Extra instances to short-circuit type class resolution -/
instance : field ℚ              := by apply_instance
instance : division_ring ℚ      := by apply_instance
instance : integral_domain ℚ    := by apply_instance
-- TODO(Mario): this instance slows down data.real.basic
--instance : domain ℚ           := by apply_instance
instance : nonzero_comm_ring ℚ  := by apply_instance
instance : comm_ring ℚ          := by apply_instance
--instance : ring ℚ             := by apply_instance
instance : comm_semiring ℚ      := by apply_instance
instance : semiring ℚ           := by apply_instance
instance : add_comm_group ℚ     := by apply_instance
instance : add_group ℚ          := by apply_instance
instance : add_comm_monoid ℚ    := by apply_instance
instance : add_monoid ℚ         := by apply_instance
instance : add_left_cancel_semigroup ℚ := by apply_instance
instance : add_right_cancel_semigroup ℚ := by apply_instance
instance : add_comm_semigroup ℚ := by apply_instance
instance : add_semigroup ℚ      := by apply_instance
instance : comm_monoid ℚ        := by apply_instance
instance : monoid ℚ             := by apply_instance
instance : comm_semigroup ℚ     := by apply_instance
instance : semigroup ℚ          := by apply_instance

theorem sub_def {a b c d : ℤ} (b0 : b ≠ 0) (d0 : d ≠ 0) :
  a /. b - c /. d = (a * d - c * b) /. (b * d) :=
by simp [b0, d0]

protected def nonneg : ℚ → Prop
| ⟨n, d, h, c⟩ := n ≥ 0

@[simp] theorem mk_nonneg (a : ℤ) {b : ℤ} (h : b > 0) : (a /. b).nonneg ↔ a ≥ 0 :=
begin
  generalize ha : a /. b = x, cases x with n₁ d₁ h₁ c₁, rw num_denom' at ha,
  simp [rat.nonneg],
  have d0 := int.coe_nat_lt.2 h₁,
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
  have d₁0 : (d₁:ℤ) > 0 := int.coe_nat_pos.2 (nat.pos_of_ne_zero h₁),
  have d₂0 : (d₂:ℤ) > 0 := int.coe_nat_pos.2 (nat.pos_of_ne_zero h₂),
  simp [d₁0, d₂0, h₁, h₂, mul_pos d₁0 d₂0],
  intros n₁0 n₂0,
  apply add_nonneg; apply mul_nonneg; {assumption <|> apply int.coe_zero_le}
end

protected def nonneg_mul {a b} : rat.nonneg a → rat.nonneg b → rat.nonneg (a * b) :=
num_denom_cases_on' a $ λ n₁ d₁ h₁,
num_denom_cases_on' b $ λ n₂ d₂ h₂,
begin
  have d₁0 : (d₁:ℤ) > 0 := int.coe_nat_pos.2 (nat.pos_of_ne_zero h₁),
  have d₂0 : (d₂:ℤ) > 0 := int.coe_nat_pos.2 (nat.pos_of_ne_zero h₂),
  simp [d₁0, d₂0, h₁, h₂, mul_pos d₁0 d₂0],
  exact mul_nonneg
end

protected def nonneg_antisymm {a} : rat.nonneg a → rat.nonneg (-a) → a = 0 :=
num_denom_cases_on' a $ λ n d h,
begin
  have d0 : (d:ℤ) > 0 := int.coe_nat_pos.2 (nat.pos_of_ne_zero h),
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

instance decidable_le : decidable_rel ((≤) : ℚ → ℚ → Prop)
| a b := show decidable (rat.nonneg (b - a)), by apply_instance

protected theorem le_def {a b c d : ℤ} (b0 : b > 0) (d0 : d > 0) :
  a /. b ≤ c /. d ↔ a * d ≤ c * b :=
show rat.nonneg _ ↔ _,
by simpa [ne_of_gt b0, ne_of_gt d0, mul_pos b0 d0, mul_comm]
   using @sub_nonneg _ _ (b * c) (a * d)

protected theorem le_refl : a ≤ a :=
show rat.nonneg (a - a), by rw sub_self; exact le_refl (0 : ℤ)

protected theorem le_total : a ≤ b ∨ b ≤ a :=
by have := rat.nonneg_total (b - a); rwa neg_sub at this

protected theorem le_antisymm {a b : ℚ} (hab : a ≤ b) (hba : b ≤ a) : a = b :=
by have := eq_neg_of_add_eq_zero (rat.nonneg_antisymm hba $ by simpa);
   rwa neg_neg at this

protected theorem le_trans {a b c : ℚ} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
have rat.nonneg (b - a + (c - b)), from rat.nonneg_add hab hbc,
by simpa

instance : decidable_linear_order ℚ :=
{ le              := rat.le,
  le_refl         := rat.le_refl,
  le_trans        := @rat.le_trans,
  le_antisymm     := @rat.le_antisymm,
  le_total        := rat.le_total,
  decidable_eq    := by apply_instance,
  decidable_le    := assume a b, rat.decidable_nonneg (b - a) }

/- Extra instances to short-circuit type class resolution -/
instance : has_lt ℚ                  := by apply_instance
instance : lattice.distrib_lattice ℚ := by apply_instance
instance : lattice.lattice ℚ         := by apply_instance
instance : lattice.semilattice_inf ℚ := by apply_instance
instance : lattice.semilattice_sup ℚ := by apply_instance
instance : lattice.has_inf ℚ         := by apply_instance
instance : lattice.has_sup ℚ         := by apply_instance
instance : linear_order ℚ            := by apply_instance
instance : partial_order ℚ           := by apply_instance
instance : preorder ℚ                := by apply_instance

theorem nonneg_iff_zero_le {a} : rat.nonneg a ↔ 0 ≤ a :=
show rat.nonneg a ↔ rat.nonneg (a - 0), by simp

theorem num_nonneg_iff_zero_le : ∀ {a : ℚ}, 0 ≤ a.num ↔ 0 ≤ a
| ⟨n, d, h, c⟩ := @nonneg_iff_zero_le ⟨n, d, h, c⟩

theorem mk_le {a b c d : ℤ} (h₁ : b > 0) (h₂ : d > 0) :
  a /. b ≤ c /. d ↔ a * d ≤ c * b :=
by conv in (_ ≤ _) {
  simp only [(≤), rat.le],
  rw [sub_def (ne_of_gt h₂) (ne_of_gt h₁),
      mk_nonneg _ (mul_pos h₂ h₁), ge, sub_nonneg] }

protected theorem add_le_add_left {a b c : ℚ} : c + a ≤ c + b ↔ a ≤ b :=
by unfold has_le.le rat.le; rw add_sub_add_left_eq_sub

protected theorem mul_nonneg {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b :=
by rw ← nonneg_iff_zero_le at ha hb ⊢; exact rat.nonneg_mul ha hb

instance : discrete_linear_ordered_field ℚ :=
{ zero_lt_one     := dec_trivial,
  add_le_add_left := assume a b ab c, rat.add_le_add_left.2 ab,
  add_lt_add_left := assume a b ab c, lt_of_not_ge $ λ ba,
    not_le_of_lt ab $ rat.add_le_add_left.1 ba,
  mul_nonneg      := @rat.mul_nonneg,
  mul_pos         := assume a b ha hb, lt_of_le_of_ne
    (rat.mul_nonneg (le_of_lt ha) (le_of_lt hb))
    (mul_ne_zero (ne_of_lt ha).symm (ne_of_lt hb).symm).symm,
  ..rat.discrete_field, ..rat.decidable_linear_order }

/- Extra instances to short-circuit type class resolution -/
instance : linear_ordered_field ℚ                := by apply_instance
instance : decidable_linear_ordered_comm_ring ℚ  := by apply_instance
instance : linear_ordered_comm_ring ℚ            := by apply_instance
instance : linear_ordered_ring ℚ                 := by apply_instance
instance : ordered_ring ℚ                        := by apply_instance
instance : decidable_linear_ordered_semiring ℚ   := by apply_instance
instance : linear_ordered_semiring ℚ             := by apply_instance
instance : ordered_semiring ℚ                    := by apply_instance
instance : decidable_linear_ordered_comm_group ℚ := by apply_instance
instance : ordered_comm_group ℚ                  := by apply_instance
instance : ordered_cancel_comm_monoid ℚ          := by apply_instance
instance : ordered_comm_monoid ℚ                 := by apply_instance

attribute [irreducible] rat.le

theorem num_pos_iff_pos {a : ℚ} : 0 < a.num ↔ 0 < a :=
lt_iff_lt_of_le_iff_le $
by simpa [(by cases a; refl : (-a).num = -a.num)]
   using @num_nonneg_iff_zero_le (-a)

theorem of_int_eq_mk (z : ℤ) : of_int z = z /. 1 := num_denom' _ _ _ _

theorem coe_int_eq_mk : ∀ z : ℤ, ↑z = z /. 1
| (n : ℕ) := show (n:ℚ) = n /. 1,
  by induction n with n IH n; simp [*, show (1:ℚ) = 1 /. 1, from rfl]
| -[1+ n] := show (-(n + 1) : ℚ) = -[1+ n] /. 1, begin
  induction n with n IH, {refl},
  show -(n + 1 + 1 : ℚ) = -[1+ n.succ] /. 1,
  rw [neg_add, IH],
  simpa [show -1 = (-1) /. 1, from rfl]
end

theorem coe_int_eq_of_int (z : ℤ) : ↑z = of_int z :=
(coe_int_eq_mk z).trans (of_int_eq_mk z).symm

theorem mk_eq_div (n d : ℤ) : n /. d = (n / d : ℚ) :=
begin
  by_cases d0 : d = 0, {simp [d0, div_zero]},
  rw [division_def, coe_int_eq_mk, coe_int_eq_mk, inv_def,
      mul_def one_ne_zero d0, one_mul, mul_one]
end

/-- `floor q` is the largest integer `z` such that `z ≤ q` -/
def floor : ℚ → ℤ
| ⟨n, d, h, c⟩ := n / d

theorem le_floor {z : ℤ} : ∀ {r : ℚ}, z ≤ floor r ↔ (z : ℚ) ≤ r
| ⟨n, d, h, c⟩ := begin
  simp [floor],
  rw [num_denom'],
  have h' := int.coe_nat_lt.2 h,
  conv { to_rhs,
    rw [coe_int_eq_mk, mk_le zero_lt_one h', mul_one] },
  exact int.le_div_iff_mul_le h'
end

theorem floor_lt {r : ℚ} {z : ℤ} : floor r < z ↔ r < z :=
lt_iff_lt_of_le_iff_le le_floor

theorem floor_le (r : ℚ) : (floor r : ℚ) ≤ r :=
le_floor.1 (le_refl _)

theorem lt_succ_floor (r : ℚ) : r < (floor r).succ :=
floor_lt.1 $ int.lt_succ_self _

@[simp] theorem floor_coe (z : ℤ) : floor z = z :=
eq_of_forall_le_iff $ λ a, by rw [le_floor, int.cast_le]

theorem floor_mono {a b : ℚ} (h : a ≤ b) : floor a ≤ floor b :=
le_floor.2 (le_trans (floor_le _) h)

@[simp] theorem floor_add_int (r : ℚ) (z : ℤ) : floor (r + z) = floor r + z :=
eq_of_forall_le_iff $ λ a, by rw [le_floor,
  ← sub_le_iff_le_add, ← sub_le_iff_le_add, le_floor, int.cast_sub]

theorem floor_sub_int (r : ℚ) (z : ℤ) : floor (r - z) = floor r - z :=
eq.trans (by rw [int.cast_neg]; refl) (floor_add_int _ _)

/-- `ceil q` is the smallest integer `z` such that `q ≤ z` -/
def ceil (r : ℚ) : ℤ :=
-(floor (-r))

theorem ceil_le {z : ℤ} {r : ℚ} : ceil r ≤ z ↔ r ≤ z :=
by rw [ceil, neg_le, le_floor, int.cast_neg, neg_le_neg_iff]

theorem le_ceil (r : ℚ) : r ≤ ceil r :=
ceil_le.1 (le_refl _)

@[simp] theorem ceil_coe (z : ℤ) : ceil z = z :=
by rw [ceil, ← int.cast_neg, floor_coe, neg_neg]

theorem ceil_mono {a b : ℚ} (h : a ≤ b) : ceil a ≤ ceil b :=
ceil_le.2 (le_trans h (le_ceil _))

@[simp] theorem ceil_add_int (r : ℚ) (z : ℤ) : ceil (r + z) = ceil r + z :=
by rw [ceil, neg_add', floor_sub_int, neg_sub, sub_eq_neg_add]; refl

theorem ceil_sub_int (r : ℚ) (z : ℤ) : ceil (r - z) = ceil r - z :=
eq.trans (by rw [int.cast_neg]; refl) (ceil_add_int _ _)

/- cast (injection into fields) -/

section cast
variables {α : Type*}

section
variables [division_ring α]

/-- Construct the canonical injection from `ℚ` into an arbitrary
  division ring. If the field has positive characteristic `p`,
  we define `1 / p = 1 / 0 = 0` for consistency with our
  division by zero convention. -/
protected def cast : ℚ → α
| ⟨n, d, h, c⟩ := n / d

@[priority 0] instance cast_coe : has_coe ℚ α := ⟨rat.cast⟩

@[simp] theorem cast_of_int (n : ℤ) : (of_int n : α) = n :=
show (n / (1:ℕ) : α) = n, by rw [nat.cast_one, div_one]

@[simp] theorem cast_coe_int (n : ℤ) : ((n : ℚ) : α) = n :=
by rw [coe_int_eq_of_int, cast_of_int]

@[simp] theorem coe_int_num (n : ℤ) : (n : ℚ).num = n :=
by rw coe_int_eq_of_int; refl

@[simp] theorem coe_int_denom (n : ℤ) : (n : ℚ).denom = 1 :=
by rw coe_int_eq_of_int; refl

@[simp] theorem coe_nat_num (n : ℕ) : (n : ℚ).num = n :=
by rw [← int.cast_coe_nat, coe_int_num]

@[simp] theorem coe_nat_denom (n : ℕ) : (n : ℚ).denom = 1 :=
by rw [← int.cast_coe_nat, coe_int_denom]

@[simp] theorem cast_coe_nat (n : ℕ) : ((n : ℚ) : α) = n := cast_coe_int n

@[simp] theorem cast_zero : ((0 : ℚ) : α) = 0 :=
(cast_of_int _).trans int.cast_zero

@[simp] theorem cast_one : ((1 : ℚ) : α) = 1 :=
(cast_of_int _).trans int.cast_one

theorem mul_cast_comm (a : α) :
  ∀ (n : ℚ), (n.denom : α) ≠ 0 → a * n = n * a
| ⟨n, d, h, c⟩ h₂ := show a * (n * d⁻¹) = n * d⁻¹ * a,
  by rw [← mul_assoc, int.mul_cast_comm, mul_assoc, mul_assoc,
         ← show (d:α)⁻¹ * a = a * d⁻¹, from
           division_ring.inv_comm_of_comm h₂ (int.mul_cast_comm a d).symm]

theorem cast_mk_of_ne_zero (a b : ℤ)
  (b0 : (b:α) ≠ 0) : (a /. b : α) = a / b :=
begin
  have b0' : b ≠ 0, { refine mt _ b0, simp {contextual := tt} },
  cases e : a /. b with n d h c,
  have d0 : (d:α) ≠ 0,
  { intro d0,
    have dd := denom_dvd a b,
    cases (show (d:ℤ) ∣ b, by rwa e at dd) with k ke,
    have : (b:α) = (d:α) * (k:α), {rw [ke, int.cast_mul], refl},
    rw [d0, zero_mul] at this, contradiction },
  rw [num_denom'] at e,
  have := congr_arg (coe : ℤ → α) ((mk_eq b0' $ ne_of_gt $ int.coe_nat_pos.2 h).1 e),
  rw [int.cast_mul, int.cast_mul, int.cast_coe_nat] at this,
  symmetry, change (a * b⁻¹ : α) = n / d,
  rw [eq_div_iff_mul_eq _ _ d0, mul_assoc, nat.mul_cast_comm,
      ← mul_assoc, this, mul_assoc, mul_inv_cancel b0, mul_one]
end

theorem cast_add_of_ne_zero : ∀ {m n : ℚ},
  (m.denom : α) ≠ 0 → (n.denom : α) ≠ 0 → ((m + n : ℚ) : α) = m + n
| ⟨n₁, d₁, h₁, c₁⟩ ⟨n₂, d₂, h₂, c₂⟩ := λ (d₁0 : (d₁:α) ≠ 0) (d₂0 : (d₂:α) ≠ 0), begin
  have d₁0' : (d₁:ℤ) ≠ 0 := int.coe_nat_ne_zero.2 (λ e, by rw e at d₁0; exact d₁0 rfl),
  have d₂0' : (d₂:ℤ) ≠ 0 := int.coe_nat_ne_zero.2 (λ e, by rw e at d₂0; exact d₂0 rfl),
  rw [num_denom', num_denom', add_def d₁0' d₂0'],
  suffices : (n₁ * (d₂ * (d₂⁻¹ * d₁⁻¹)) +
    n₂ * (d₁ * d₂⁻¹) * d₁⁻¹ : α) = n₁ * d₁⁻¹ + n₂ * d₂⁻¹,
  { rw [cast_mk_of_ne_zero, cast_mk_of_ne_zero, cast_mk_of_ne_zero],
    { simpa [division_def, left_distrib, right_distrib, mul_inv_eq,
             d₁0, d₂0, division_ring.mul_ne_zero d₁0 d₂0, mul_assoc] },
    all_goals {simp [d₁0, d₂0, division_ring.mul_ne_zero d₁0 d₂0]} },
  rw [← mul_assoc (d₂:α), mul_inv_cancel d₂0, one_mul,
      ← nat.mul_cast_comm], simp [d₁0, mul_assoc]
end

@[simp] theorem cast_neg : ∀ n, ((-n : ℚ) : α) = -n
| ⟨n, d, h, c⟩ := show (↑-n * d⁻¹ : α) = -(n * d⁻¹),
  by rw [int.cast_neg, neg_mul_eq_neg_mul]

theorem cast_sub_of_ne_zero {m n : ℚ}
  (m0 : (m.denom : α) ≠ 0) (n0 : (n.denom : α) ≠ 0) : ((m - n : ℚ) : α) = m - n :=
have ((-n).denom : α) ≠ 0, by cases n; exact n0,
by simp [m0, this, cast_add_of_ne_zero]

theorem cast_mul_of_ne_zero : ∀ {m n : ℚ},
  (m.denom : α) ≠ 0 → (n.denom : α) ≠ 0 → ((m * n : ℚ) : α) = m * n
| ⟨n₁, d₁, h₁, c₁⟩ ⟨n₂, d₂, h₂, c₂⟩ := λ (d₁0 : (d₁:α) ≠ 0) (d₂0 : (d₂:α) ≠ 0), begin
  have d₁0' : (d₁:ℤ) ≠ 0 := int.coe_nat_ne_zero.2 (λ e, by rw e at d₁0; exact d₁0 rfl),
  have d₂0' : (d₂:ℤ) ≠ 0 := int.coe_nat_ne_zero.2 (λ e, by rw e at d₂0; exact d₂0 rfl),
  rw [num_denom', num_denom', mul_def d₁0' d₂0'],
  suffices : (n₁ * ((n₂ * d₂⁻¹) * d₁⁻¹) : α) = n₁ * (d₁⁻¹ * (n₂ * d₂⁻¹)),
  { rw [cast_mk_of_ne_zero, cast_mk_of_ne_zero, cast_mk_of_ne_zero],
    { simpa [division_def, mul_inv_eq, d₁0, d₂0, division_ring.mul_ne_zero d₁0 d₂0, mul_assoc] },
    all_goals {simp [d₁0, d₂0, division_ring.mul_ne_zero d₁0 d₂0]} },
  rw [division_ring.inv_comm_of_comm d₁0 (nat.mul_cast_comm _ _).symm]
end

theorem cast_inv_of_ne_zero : ∀ {n : ℚ},
  (n.num : α) ≠ 0 → (n.denom : α) ≠ 0 → ((n⁻¹ : ℚ) : α) = n⁻¹
| ⟨n, d, h, c⟩ := λ (n0 : (n:α) ≠ 0) (d0 : (d:α) ≠ 0), begin
  have n0' : (n:ℤ) ≠ 0 := λ e, by rw e at n0; exact n0 rfl,
  have d0' : (d:ℤ) ≠ 0 := int.coe_nat_ne_zero.2 (λ e, by rw e at d0; exact d0 rfl),
  rw [num_denom', inv_def],
  rw [cast_mk_of_ne_zero, cast_mk_of_ne_zero, inv_div];
  simp [n0, d0]
end

theorem cast_div_of_ne_zero {m n : ℚ} (md : (m.denom : α) ≠ 0)
  (nn : (n.num : α) ≠ 0) (nd : (n.denom : α) ≠ 0) : ((m / n : ℚ) : α) = m / n :=
have (n⁻¹.denom : ℤ) ∣ n.num,
by conv in n⁻¹.denom { rw [num_denom n, inv_def] };
   apply denom_dvd,
have (n⁻¹.denom : α) = 0 → (n.num : α) = 0, from
λ h, let ⟨k, e⟩ := this in
  by have := congr_arg (coe : ℤ → α) e;
     rwa [int.cast_mul, int.cast_coe_nat, h, zero_mul] at this,
by rw [division_def, cast_mul_of_ne_zero md (mt this nn), cast_inv_of_ne_zero nn nd, division_def]

@[simp] theorem cast_inj [char_zero α] : ∀ {m n : ℚ}, (m : α) = n ↔ m = n
| ⟨n₁, d₁, h₁, c₁⟩ ⟨n₂, d₂, h₂, c₂⟩ := begin
  refine ⟨λ h, _, congr_arg _⟩,
  have d₁0 : d₁ ≠ 0 := ne_of_gt h₁,
  have d₂0 : d₂ ≠ 0 := ne_of_gt h₂,
  have d₁a : (d₁:α) ≠ 0 := nat.cast_ne_zero.2 d₁0,
  have d₂a : (d₂:α) ≠ 0 := nat.cast_ne_zero.2 d₂0,
  rw [num_denom', num_denom'] at h ⊢,
  rw [cast_mk_of_ne_zero, cast_mk_of_ne_zero] at h; simp [d₁0, d₂0] at h ⊢,
  rwa [eq_div_iff_mul_eq _ _ d₂a, division_def, mul_assoc,
    division_ring.inv_comm_of_comm d₁a (nat.mul_cast_comm _ _),
    ← mul_assoc, ← division_def, eq_comm, eq_div_iff_mul_eq _ _ d₁a, eq_comm,
    ← int.cast_coe_nat, ← int.cast_mul, ← int.cast_coe_nat, ← int.cast_mul,
    int.cast_inj, ← mk_eq (int.coe_nat_ne_zero.2 d₁0) (int.coe_nat_ne_zero.2 d₂0)] at h
end

theorem cast_injective [char_zero α] : function.injective (coe : ℚ → α)
| m n := cast_inj.1

@[simp] theorem cast_eq_zero [char_zero α] {n : ℚ} : (n : α) = 0 ↔ n = 0 :=
by rw [← cast_zero, cast_inj]

@[simp] theorem cast_ne_zero [char_zero α] {n : ℚ} : (n : α) ≠ 0 ↔ n ≠ 0 :=
not_congr cast_eq_zero

theorem eq_cast_of_ne_zero (f : ℚ → α) (H1 : f 1 = 1)
  (Hadd : ∀ x y, f (x + y) = f x + f y)
  (Hmul : ∀ x y, f (x * y) = f x * f y) :
  ∀ n : ℚ, (n.denom : α) ≠ 0 → f n = n
| ⟨n, d, h, c⟩ := λ (h₂ : ((d:ℤ):α) ≠ 0), show _ = (n / (d:ℤ) : α), begin
  rw [num_denom', mk_eq_div, eq_div_iff_mul_eq _ _ h₂],
  have : ∀ n : ℤ, f n = n, { apply int.eq_cast; simp [H1, Hadd] },
  rw [← this, ← this, ← Hmul, div_mul_cancel],
  exact int.cast_ne_zero.2 (int.coe_nat_ne_zero.2 $ ne_of_gt h),
end

theorem eq_cast [char_zero α] (f : ℚ → α) (H1 : f 1 = 1)
  (Hadd : ∀ x y, f (x + y) = f x + f y)
  (Hmul : ∀ x y, f (x * y) = f x * f y) (n : ℚ) : f n = n :=
eq_cast_of_ne_zero _ H1 Hadd Hmul _ $
  nat.cast_ne_zero.2 $ ne_of_gt n.pos

end

theorem cast_mk [discrete_field α] [char_zero α] (a b : ℤ) : ((a /. b) : α) = a / b :=
if b0 : b = 0 then by simp [b0, div_zero]
else cast_mk_of_ne_zero a b (int.cast_ne_zero.2 b0)

@[simp] theorem cast_add [division_ring α] [char_zero α] (m n) : ((m + n : ℚ) : α) = m + n :=
cast_add_of_ne_zero (nat.cast_ne_zero.2 $ ne_of_gt m.pos) (nat.cast_ne_zero.2 $ ne_of_gt n.pos)

@[simp] theorem cast_sub [division_ring α] [char_zero α] (m n) : ((m - n : ℚ) : α) = m - n :=
cast_sub_of_ne_zero (nat.cast_ne_zero.2 $ ne_of_gt m.pos) (nat.cast_ne_zero.2 $ ne_of_gt n.pos)

@[simp] theorem cast_mul [division_ring α] [char_zero α] (m n) : ((m * n : ℚ) : α) = m * n :=
cast_mul_of_ne_zero (nat.cast_ne_zero.2 $ ne_of_gt m.pos) (nat.cast_ne_zero.2 $ ne_of_gt n.pos)

@[simp] theorem cast_inv [discrete_field α] [char_zero α] (n) : ((n⁻¹ : ℚ) : α) = n⁻¹ :=
if n0 : n.num = 0 then
  by simp [show n = 0, by rw [num_denom n, n0]; simp, inv_zero] else
cast_inv_of_ne_zero (int.cast_ne_zero.2 n0) (nat.cast_ne_zero.2 $ ne_of_gt n.pos)

@[simp] theorem cast_div [discrete_field α] [char_zero α] (m n) : ((m / n : ℚ) : α) = m / n :=
by rw [division_def, cast_mul, cast_inv, division_def]

@[simp] theorem cast_pow [discrete_field α] [char_zero α] (q) (k : ℕ) : ((q ^ k : ℚ) : α) = q ^ k :=
by induction k; simp only [*, cast_one, cast_mul, pow_zero, pow_succ]

@[simp] theorem cast_bit0 [division_ring α] [char_zero α] (n : ℚ) : ((bit0 n : ℚ) : α) = bit0 n := cast_add _ _

@[simp] theorem cast_bit1 [division_ring α] [char_zero α] (n : ℚ) : ((bit1 n : ℚ) : α) = bit1 n :=
by rw [bit1, cast_add, cast_one, cast_bit0]; refl

@[simp] theorem cast_nonneg [linear_ordered_field α] : ∀ {n : ℚ}, 0 ≤ (n : α) ↔ 0 ≤ n
| ⟨n, d, h, c⟩ := show 0 ≤ (n * d⁻¹ : α) ↔ 0 ≤ (⟨n, d, h, c⟩ : ℚ),
  by rw [num_denom', ← nonneg_iff_zero_le, mk_nonneg _ (int.coe_nat_pos.2 h),
    mul_nonneg_iff_right_nonneg_of_pos (@inv_pos α _ _ (nat.cast_pos.2 h)),
    int.cast_nonneg]

@[simp] theorem cast_le [linear_ordered_field α] {m n : ℚ} : (m : α) ≤ n ↔ m ≤ n :=
by rw [← sub_nonneg, ← cast_sub, cast_nonneg, sub_nonneg]

@[simp] theorem cast_lt [linear_ordered_field α] {m n : ℚ} : (m : α) < n ↔ m < n :=
by simpa [-cast_le] using not_congr (@cast_le α _ n m)

@[simp] theorem cast_nonpos [linear_ordered_field α] {n : ℚ} : (n : α) ≤ 0 ↔ n ≤ 0 :=
by rw [← cast_zero, cast_le]

@[simp] theorem cast_pos [linear_ordered_field α] {n : ℚ} : (0 : α) < n ↔ 0 < n :=
by rw [← cast_zero, cast_lt]

@[simp] theorem cast_lt_zero [linear_ordered_field α] {n : ℚ} : (n : α) < 0 ↔ n < 0 :=
by rw [← cast_zero, cast_lt]

@[simp] theorem cast_id : ∀ n : ℚ, ↑n = n
| ⟨n, d, h, c⟩ := show (n / (d : ℤ) : ℚ) = _, by rw [num_denom', mk_eq_div]

@[simp] theorem cast_min [discrete_linear_ordered_field α] {a b : ℚ} : (↑(min a b) : α) = min a b :=
by by_cases a ≤ b; simp [h, min]

@[simp] theorem cast_max [discrete_linear_ordered_field α] {a b : ℚ} : (↑(max a b) : α) = max a b :=
by by_cases a ≤ b; simp [h, max]

@[simp] theorem cast_abs [discrete_linear_ordered_field α] {q : ℚ} : ((abs q : ℚ) : α) = abs q :=
by simp [abs]

end cast

/- nat ceiling -/

/-- `nat_ceil q` is the smallest nonnegative integer `n` with `q ≤ n`.
  It is the same as `ceil q` when `q ≥ 0`, otherwise it is `0`. -/
def nat_ceil (q : ℚ) : ℕ := int.to_nat (ceil q)

theorem nat_ceil_le {q : ℚ} {n : ℕ} : nat_ceil q ≤ n ↔ q ≤ n :=
by rw [nat_ceil, int.to_nat_le, ceil_le]; refl

theorem lt_nat_ceil {q : ℚ} {n : ℕ} : n < nat_ceil q ↔ (n : ℚ) < q :=
not_iff_not.1 $ by rw [not_lt, not_lt, nat_ceil_le]

theorem le_nat_ceil (q : ℚ) : q ≤ nat_ceil q :=
nat_ceil_le.1 (le_refl _)

theorem nat_ceil_mono {q₁ q₂ : ℚ} (h : q₁ ≤ q₂) : nat_ceil q₁ ≤ nat_ceil q₂ :=
nat_ceil_le.2 (le_trans h (le_nat_ceil _))

@[simp] theorem nat_ceil_coe (n : ℕ) : nat_ceil n = n :=
show (ceil (n:ℤ)).to_nat = n, by rw [ceil_coe]; refl

@[simp] theorem nat_ceil_zero : nat_ceil 0 = 0 := nat_ceil_coe 0

theorem nat_ceil_add_nat {q : ℚ} (hq : 0 ≤ q) (n : ℕ) : nat_ceil (q + n) = nat_ceil q + n :=
show int.to_nat (ceil (q + (n:ℤ))) = int.to_nat (ceil q) + n,
by rw [ceil_add_int]; exact
match ceil q, int.eq_coe_of_zero_le (ceil_mono hq) with
| _, ⟨m, rfl⟩ := rfl
end

theorem nat_ceil_lt_add_one {q : ℚ} (hq : q ≥ 0) : ↑(nat_ceil q) < q + 1 :=
lt_nat_ceil.1 $ by rw [
  show nat_ceil (q+1) = nat_ceil q+1, from nat_ceil_add_nat hq 1]; apply nat.lt_succ_self

@[simp] lemma denom_neg_eq_denom : ∀ q : ℚ, (-q).denom = q.denom
| ⟨_, d, _, _⟩ := rfl

@[simp] lemma num_neg_eq_neg_num : ∀ q : ℚ, (-q).num = -(q.num)
| ⟨n, _, _, _⟩ := rfl

@[simp] lemma num_zero : rat.num 0 = 0 := rfl

lemma zero_of_num_zero {q : ℚ} (hq : q.num = 0) : q = 0 :=
have q = q.num /. q.denom, from num_denom _,
by simpa [hq]

lemma zero_iff_num_zero {q : ℚ} : q = 0 ↔ q.num = 0 :=
⟨λ _, by simp *, zero_of_num_zero⟩

lemma num_ne_zero_of_ne_zero {q : ℚ} (h : q ≠ 0) : q.num ≠ 0 :=
assume : q.num = 0,
h $ zero_of_num_zero this

lemma denom_ne_zero (q : ℚ) : q.denom ≠ 0 :=
ne_of_gt q.pos

lemma mk_num_ne_zero_of_ne_zero {q : ℚ} {n d : ℤ} (hq : q ≠ 0) (hqnd : q = n /. d) : n ≠ 0 :=
assume : n = 0,
hq $ by simpa [this] using hqnd

lemma mk_denom_ne_zero_of_ne_zero {q : ℚ} {n d : ℤ} (hq : q ≠ 0) (hqnd : q = n /. d) : d ≠ 0 :=
assume : d = 0,
hq $ by simpa [this] using hqnd

lemma mk_ne_zero_of_ne_zero {n d : ℤ} (h : n ≠ 0) (hd : d ≠ 0) : n /. d ≠ 0 :=
assume : n /. d = 0,
h $ (mk_eq_zero hd).1 this

lemma mul_num_denom (q r : ℚ) : q * r = (q.num * r.num) /. ↑(q.denom * r.denom) :=
have hq' : (↑q.denom : ℤ) ≠ 0, by have := denom_ne_zero q; simpa,
have hr' : (↑r.denom : ℤ) ≠ 0, by have := denom_ne_zero r; simpa,
suffices (q.num /. ↑q.denom) * (r.num /. ↑r.denom) = (q.num * r.num) /. ↑(q.denom * r.denom),
  by rwa [←num_denom q, ←num_denom r] at this,
by simp [mul_def hq' hr']

lemma div_num_denom (q r : ℚ) : q / r = (q.num * r.denom) /. (q.denom * r.num) :=
if hr : r.num = 0 then
  have hr' : r = 0, from zero_of_num_zero hr,
  by simp *
else calc q / r = q * r⁻¹ : div_eq_mul_inv
            ... = (q.num /. q.denom) * (r.num /. r.denom)⁻¹ : by rw [←num_denom q, ←num_denom r]
            ... = (q.num /. q.denom) * (r.denom /. r.num) : by rw inv_def
            ... = (q.num * r.denom) /. (q.denom * r.num) : mul_def (by simpa using denom_ne_zero q) hr

lemma num_denom_mk {q : ℚ} {n d : ℤ} (hn : n ≠ 0) (hd : d ≠ 0) (qdf : q = n /. d) :
      ∃ c : ℤ, n = c * q.num ∧ d = c * q.denom :=
have hq : q ≠ 0, from
  assume : q = 0,
  hn $ (rat.mk_eq_zero hd).1 (by cc),
have q.num /. q.denom = n /. d, by rwa [←rat.num_denom q],
have q.num * d = n * ↑(q.denom), from (rat.mk_eq (by simp [rat.denom_ne_zero]) hd).1 this,
begin
  existsi n / q.num,
  have hqdn : q.num ∣ n, begin rw qdf, apply rat.num_dvd, assumption end,
  split,
    { rw int.div_mul_cancel hqdn },
    { apply int.eq_mul_div_of_mul_eq_mul_of_dvd_left,
      {apply rat.num_ne_zero_of_ne_zero hq},
      {simp [rat.denom_ne_zero]},
      repeat {assumption} }
end

theorem mk_pnat_num (n : ℤ) (d : ℕ+) :
  (mk_pnat n d).num = n / nat.gcd n.nat_abs d :=
by cases d; refl

theorem mk_pnat_denom (n : ℤ) (d : ℕ+) :
  (mk_pnat n d).denom = d / nat.gcd n.nat_abs d :=
by cases d; refl

theorem mul_num (q₁ q₂ : ℚ) : (q₁ * q₂).num =
  (q₁.num * q₂.num) / nat.gcd (q₁.num * q₂.num).nat_abs (q₁.denom * q₂.denom) :=
by cases q₁; cases q₂; refl

theorem mul_denom (q₁ q₂ : ℚ) : (q₁ * q₂).denom =
  (q₁.denom * q₂.denom) / nat.gcd (q₁.num * q₂.num).nat_abs (q₁.denom * q₂.denom) :=
by cases q₁; cases q₂; refl

theorem mul_self_num (q : ℚ) : (q * q).num = q.num * q.num :=
by rw [mul_num, int.nat_abs_mul, nat.coprime.gcd_eq_one, int.coe_nat_one, int.div_one];
exact (q.cop.mul_right q.cop).mul (q.cop.mul_right q.cop)

theorem mul_self_denom (q : ℚ) : (q * q).denom = q.denom * q.denom :=
by rw [rat.mul_denom, int.nat_abs_mul, nat.coprime.gcd_eq_one, nat.div_one];
exact (q.cop.mul_right q.cop).mul (q.cop.mul_right q.cop)

theorem abs_def (q : ℚ) : abs q = q.num.nat_abs /. q.denom :=
begin
  have hz : (0:ℚ) = 0 /. 1 := rfl,
  cases le_total q 0 with hq hq,
  { rw [abs_of_nonpos hq],
    rw [num_denom q, hz, rat.le_def (int.coe_nat_pos.2 q.pos) zero_lt_one,
        mul_one, zero_mul] at hq,
    rw [int.of_nat_nat_abs_of_nonpos hq, ← neg_def, ← num_denom q] },
  { rw [abs_of_nonneg hq],
    rw [num_denom q, hz, rat.le_def zero_lt_one (int.coe_nat_pos.2 q.pos),
        mul_one, zero_mul] at hq,
    rw [int.nat_abs_of_nonneg hq, ← num_denom q] }
end

def sqrt (q : ℚ) : ℚ :=
rat.mk (int.sqrt q.num) (nat.sqrt q.denom)

theorem sqrt_eq (q : ℚ) : rat.sqrt (q*q) = abs q :=
by rw [sqrt, mul_self_num, mul_self_denom,
       int.sqrt_eq, nat.sqrt_eq, abs_def]

theorem exists_mul_self (x : ℚ) :
  (∃ q, q * q = x) ↔ rat.sqrt x * rat.sqrt x = x :=
⟨λ ⟨n, hn⟩, by rw [← hn, sqrt_eq, abs_mul_abs_self],
λ h, ⟨rat.sqrt x, h⟩⟩

theorem sqrt_nonneg (q : ℚ) : 0 ≤ rat.sqrt q :=
nonneg_iff_zero_le.1 $ (mk_nonneg _ $ int.coe_nat_pos.2 $
nat.pos_of_ne_zero $ λ H, nat.pos_iff_ne_zero.1 q.pos $ nat.sqrt_eq_zero.1 H).2 trivial

end rat
