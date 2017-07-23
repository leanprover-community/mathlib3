/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro

Basic operations on the natural numbers.
-/
import logic.basic

universe u

open tactic

namespace nat

def iterate {A : Type} (op : A → A) : ℕ → A → A
 | 0 := λ a, a
 | (succ k) := λ a, op (iterate k a)

notation f`^[`n`]` := iterate f n

/- successor and predecessor -/

theorem add_one_ne_zero (n : ℕ) : n + 1 ≠ 0 := succ_ne_zero _

theorem eq_zero_or_eq_succ_pred (n : ℕ) : n = 0 ∨ n = succ (pred n) :=
by cases n; simp

theorem exists_eq_succ_of_ne_zero {n : ℕ} (H : n ≠ 0) : ∃k : ℕ, n = succ k :=
⟨_, (eq_zero_or_eq_succ_pred _).resolve_left H⟩

theorem succ_inj {n m : ℕ} (H : succ n = succ m) : n = m :=
nat.succ.inj_arrow H id

theorem discriminate {B : Sort u} {n : ℕ} (H1: n = 0 → B) (H2 : ∀m, n = succ m → B) : B :=
by ginduction n with h; [exact H1 h, exact H2 _ h]

theorem one_succ_zero : 1 = succ 0 := rfl

theorem two_step_induction {P : ℕ → Sort u} (H1 : P 0) (H2 : P 1)
    (H3 : ∀ (n : ℕ) (IH1 : P n) (IH2 : P (succ n)), P (succ (succ n))) : Π (a : ℕ), P a
| 0               := H1
| 1               := H2
| (succ (succ n)) := H3 _ (two_step_induction _) (two_step_induction _)

theorem sub_induction {P : ℕ → ℕ → Sort u} (H1 : ∀m, P 0 m)
   (H2 : ∀n, P (succ n) 0) (H3 : ∀n m, P n m → P (succ n) (succ m)) : Π (n m : ℕ), P n m
| 0        m        := H1 _
| (succ n) 0        := H2 _
| (succ n) (succ m) := H3 _ _ (sub_induction n m)

/- addition -/

theorem succ_add_eq_succ_add (n m : ℕ) : succ n + m = n + succ m :=
by simp [succ_add, add_succ]

theorem one_add (n : ℕ) : 1 + n = succ n := by simp

protected theorem add_right_comm : ∀ (n m k : ℕ), n + m + k = n + k + m :=
right_comm nat.add nat.add_comm nat.add_assoc

theorem eq_zero_of_add_eq_zero {n m : ℕ} (H : n + m = 0) : n = 0 ∧ m = 0 :=
⟨nat.eq_zero_of_add_eq_zero_right H, nat.eq_zero_of_add_eq_zero_left H⟩

theorem eq_zero_of_mul_eq_zero : ∀ {n m : ℕ}, n * m = 0 → n = 0 ∨ m = 0
| 0        m := λ h, or.inl rfl
| (succ n) m :=
  begin
    rw succ_mul, intro h,
    exact or.inr (eq_zero_of_add_eq_zero_left h)
  end

/- properties of inequality -/

theorem le_succ_of_pred_le {n m : ℕ} : pred n ≤ m → n ≤ succ m :=
nat.cases_on n less_than_or_equal.step (λ a, succ_le_succ)

theorem le_lt_antisymm {n m : ℕ} (h₁ : n ≤ m) (h₂ : m < n) : false :=
nat.lt_irrefl n (nat.lt_of_le_of_lt h₁ h₂)

theorem lt_le_antisymm {n m : ℕ} (h₁ : n < m) (h₂ : m ≤ n) : false :=
le_lt_antisymm h₂ h₁

protected theorem nat.lt_asymm {n m : ℕ} (h₁ : n < m) : ¬ m < n :=
le_lt_antisymm (nat.le_of_lt h₁)

protected def lt_ge_by_cases {a b : ℕ} {C : Sort u} (h₁ : a < b → C) (h₂ : a ≥ b → C) : C :=
decidable.by_cases h₁ (λ h, h₂ (or.elim (nat.lt_or_ge a b) (λ a, absurd a h) (λ a, a)))

protected def lt_by_cases {a b : ℕ} {C : Sort u} (h₁ : a < b → C) (h₂ : a = b → C)
  (h₃ : b < a → C) : C :=
nat.lt_ge_by_cases h₁ (λ h₁,
  nat.lt_ge_by_cases h₃ (λ h, h₂ (nat.le_antisymm h h₁)))

protected theorem lt_trichotomy (a b : ℕ) : a < b ∨ a = b ∨ b < a :=
nat.lt_by_cases (λ h, or.inl h) (λ h, or.inr (or.inl h)) (λ h, or.inr (or.inr h))

protected theorem eq_or_lt_of_not_lt {a b : ℕ} (hnlt : ¬ a < b) : a = b ∨ b < a :=
(nat.lt_trichotomy a b).resolve_left hnlt

theorem lt_succ_of_lt {a b : nat} (h : a < b) : a < succ b := le_succ_of_le h

def one_pos := nat.zero_lt_one

theorem mul_self_le_mul_self {n m : ℕ} (h : n ≤ m) : n * n ≤ m * m :=
mul_le_mul h h (zero_le _) (zero_le _)

theorem mul_self_lt_mul_self : Π {n m : ℕ}, n < m → n * n < m * m
| 0        m h := mul_pos h h
| (succ n) m h := mul_lt_mul h (le_of_lt h) (succ_pos _) (zero_le _)

theorem mul_self_le_mul_self_iff {n m : ℕ} : n ≤ m ↔ n * n ≤ m * m :=
⟨mul_self_le_mul_self, λh, decidable.by_contradiction $
  λhn, not_lt_of_ge h $ mul_self_lt_mul_self $ lt_of_not_ge hn⟩

theorem mul_self_lt_mul_self_iff {n m : ℕ} : n < m ↔ n * n < m * m :=
iff.trans (lt_iff_not_ge _ _) $ iff.trans (not_iff_not_of_iff mul_self_le_mul_self_iff) $
  iff.symm (lt_iff_not_ge _ _)

theorem le_mul_self : Π (n : ℕ), n ≤ n * n
| 0     := le_refl _
| (n+1) := let t := mul_le_mul_left (n+1) (succ_pos n) in by simp at t; exact t

/- subtraction -/

protected theorem sub_le_sub_left {n m : ℕ} (k) (h : n ≤ m) : k - m ≤ k - n :=
by induction h; [refl, exact le_trans (pred_le _) ih_1]

theorem succ_sub_sub_succ (n m k : ℕ) : succ n - m - succ k = n - m - k :=
by rw [nat.sub_sub, nat.sub_sub, add_succ, succ_sub_succ]

protected theorem sub.right_comm (m n k : ℕ) : m - n - k = m - k - n :=
by rw [nat.sub_sub, nat.sub_sub, add_comm]

theorem mul_pred_left : ∀ (n m : ℕ), pred n * m = n * m - m
| 0        m := by simp [nat.zero_sub, pred_zero, zero_mul]
| (succ n) m := by rw [pred_succ, succ_mul, nat.add_sub_cancel]

theorem mul_pred_right (n m : ℕ) : n * pred m = n * m - n :=
by rw [mul_comm, mul_pred_left, mul_comm]

protected theorem mul_sub_right_distrib : ∀ (n m k : ℕ), (n - m) * k = n * k - m * k
| n 0        k := by simp [nat.sub_zero]
| n (succ m) k := by rw [nat.sub_succ, mul_pred_left, mul_sub_right_distrib, succ_mul, nat.sub_sub]

protected theorem mul_sub_left_distrib (n m k : ℕ) : n * (m - k) = n * m - n * k :=
by rw [mul_comm, nat.mul_sub_right_distrib, mul_comm m n, mul_comm n k]

protected theorem mul_self_sub_mul_self_eq (a b : nat) : a * a - b * b = (a + b) * (a - b) :=
by rw [nat.mul_sub_left_distrib, right_distrib, right_distrib, mul_comm b a, add_comm (a*a) (a*b),
       nat.add_sub_add_left]

theorem succ_mul_succ_eq (a b : nat) : succ a * succ b = a*b + a + b + 1 :=
begin rw [← add_one, ← add_one], simp [right_distrib, left_distrib] end

theorem succ_sub {m n : ℕ} (h : m ≥ n) : succ m - n = succ (m - n) :=
exists.elim (nat.le.dest h)
  (assume k, assume hk : n + k = m,
    by rw [← hk, nat.add_sub_cancel_left, ← add_succ, nat.add_sub_cancel_left])

protected theorem sub_pos_of_lt {m n : ℕ} (h : m < n) : n - m > 0 :=
have 0 + m < n - m + m, begin rw [zero_add, nat.sub_add_cancel (le_of_lt h)], exact h end,
lt_of_add_lt_add_right this

protected theorem sub_sub_self {n m : ℕ} (h : m ≤ n) : n - (n - m) = m :=
(nat.sub_eq_iff_eq_add (nat.sub_le _ _)).2 (eq.symm (add_sub_of_le h))

protected theorem sub_add_comm {n m k : ℕ} (h : k ≤ n) : n + m - k = n - k + m :=
(nat.sub_eq_iff_eq_add (nat.le_trans h (nat.le_add_right _ _))).2
  (by rwa [nat.add_right_comm, nat.sub_add_cancel])

theorem sub_one_sub_lt {n i} (h : i < n) : n - 1 - i < n := begin
  rw nat.sub_sub,
  apply nat.sub_lt,
  apply lt_of_lt_of_le (nat.zero_lt_succ _) h,
  rw add_comm,
  apply nat.zero_lt_succ
end

-- Distribute succ over min
theorem min_succ_succ (x y : ℕ) : min (succ x) (succ y) = succ (min x y) :=
have f : x ≤ y → min (succ x) (succ y) = succ (min x y), from λp,
  calc min (succ x) (succ y)
              = succ x         : if_pos (succ_le_succ p)
          ... = succ (min x y) : congr_arg succ (eq.symm (if_pos p)),
have g : ¬ (x ≤ y) → min (succ x) (succ y) = succ (min x y), from λp,
  calc min (succ x) (succ y)
              = succ y         : if_neg (λeq, p (pred_le_pred eq))
          ... = succ (min x y) : congr_arg succ (eq.symm (if_neg p)),
decidable.by_cases f g

theorem sub_eq_sub_min (n m : ℕ) : n - m = n - min n m :=
if h : n ≥ m then by rewrite [min_eq_right h]
else by rewrite [sub_eq_zero_of_le (le_of_not_ge h), min_eq_left (le_of_not_ge h), nat.sub_self]

@[simp] theorem sub_add_min_cancel (n m : ℕ) : n - m + min n m = n :=
by rewrite [sub_eq_sub_min, nat.sub_add_cancel (min_le_left n m)]

theorem pred_inj : ∀ {a b : nat}, a > 0 → b > 0 → nat.pred a = nat.pred b → a = b
| (succ a) (succ b) ha hb h := have a = b, from h, by rw this
| (succ a) 0        ha hb h := absurd hb (lt_irrefl _)
| 0        (succ b) ha hb h := absurd ha (lt_irrefl _)
| 0        0        ha hb h := rfl

/- find -/

section find
parameter {p : ℕ → Prop}

private def lbp (m n : ℕ) : Prop := m = n + 1 ∧ ∀ k ≤ n, ¬p k

parameters [decidable_pred p] (H : ∃n, p n)

private def wf_lbp : well_founded lbp :=
⟨let ⟨n, pn⟩ := H in 
suffices ∀m k, n ≤ k + m → acc lbp k, from λa, this _ _ (nat.le_add_left _ _),
λm, nat.rec_on m
  (λk kn, ⟨_, λy r, match y, r with ._, ⟨rfl, a⟩ := absurd pn (a _ kn) end⟩)
  (λm IH k kn, ⟨_, λy r, match y, r with ._, ⟨rfl, a⟩ := IH _ (by rw nat.add_right_comm; exact kn) end⟩)⟩

protected def find_x : {n // p n ∧ ∀m < n, ¬p m} :=
@well_founded.fix _ (λk, (∀n < k, ¬p n) → {n // p n ∧ ∀m < n, ¬p m}) lbp wf_lbp
(λm IH al, if pm : p m then ⟨m, pm, al⟩ else
    have ∀ n ≤ m, ¬p n, from λn h, or.elim (lt_or_eq_of_le h) (al n) (λe, by rw e; exact pm), 
    IH _ ⟨rfl, this⟩ (λn h, this n $ nat.le_of_succ_le_succ h))
0 (λn h, absurd h (nat.not_lt_zero _))

protected def find : ℕ := nat.find_x.1

protected theorem find_spec : p nat.find := nat.find_x.2.left

protected theorem find_min : ∀ {m : ℕ}, m < nat.find → ¬p m := nat.find_x.2.right

protected theorem find_min' {m : ℕ} (h : p m) : nat.find ≤ m :=
le_of_not_gt (λ l, find_min l h)

end find

/- mod -/

theorem mod_le (x y : ℕ) : x % y ≤ x :=
or.elim (lt_or_ge x y)
  (λxlty, by rw mod_eq_of_lt xlty; refl)
  (λylex, or.elim (eq_zero_or_pos y)
    (λy0, by rw [y0, mod_zero]; refl)
    (λypos, le_trans (le_of_lt (mod_lt _ ypos)) ylex))

@[simp] theorem add_mod_right (x z : ℕ) : (x + z) % z = x % z :=
by rw [mod_eq_sub_mod (nat.le_add_left _ _), nat.add_sub_cancel]

@[simp] theorem add_mod_left (x z : ℕ) : (x + z) % x = z % x :=
by rw [add_comm, add_mod_right]

@[simp] theorem add_mul_mod_self_left (x y z : ℕ) : (x + y * z) % y = x % y :=
by {induction z with z ih, simp, rw[mul_succ, ← add_assoc, add_mod_right, ih]}

@[simp] theorem add_mul_mod_self_right (x y z : ℕ) : (x + y * z) % z = x % z :=
by rw [mul_comm, add_mul_mod_self_left]

@[simp] theorem mul_mod_right (m n : ℕ) : (m * n) % m = 0 :=
by rw [← zero_add (m*n), add_mul_mod_self_left, zero_mod]

@[simp] theorem mul_mod_left (m n : ℕ) : (m * n) % n = 0 :=
by rw [mul_comm, mul_mod_right]

theorem mul_mod_mul_left (z x y : ℕ) : (z * x) % (z * y) = z * (x % y) :=
if y0 : y = 0 then
  by rw [y0, mul_zero, mod_zero, mod_zero]
else if z0 : z = 0 then
  by rw [z0, zero_mul, zero_mul, zero_mul, mod_zero]
else x.strong_induction_on $ λn IH,
  have y0 : y > 0, from nat.pos_of_ne_zero y0,
  have z0 : z > 0, from nat.pos_of_ne_zero z0,
  or.elim (le_or_gt y n)
    (λyn, by rw [
        mod_eq_sub_mod yn,
        mod_eq_sub_mod (mul_le_mul_left z yn),
        ← nat.mul_sub_left_distrib];
      exact IH _ (sub_lt (lt_of_lt_of_le y0 yn) y0))
    (λyn, by rw [mod_eq_of_lt yn, mod_eq_of_lt (mul_lt_mul_of_pos_left yn z0)])

theorem mul_mod_mul_right (z x y : ℕ) : (x * z) % (y * z) = (x % y) * z :=
by rw [mul_comm x z, mul_comm y z, mul_comm (x % y) z]; apply mul_mod_mul_left

theorem cond_to_bool_mod_two (x : ℕ) [d : decidable (x % 2 = 1)]
: cond (@to_bool (x % 2 = 1) d) 1 0 = x % 2 :=
begin
  cases d with h h
  ; unfold decidable.to_bool cond,
  { cases mod_two_eq_zero_or_one x with h' h',
    rw h', cases h h' },
  { rw h },
end

theorem sub_mul_mod (x k n : ℕ) (h₁ : n*k ≤ x) : (x - n*k) % n = x % n :=
begin
  induction k with k,
  { simp },
  { have h₂ : n * k ≤ x,
    { rw [mul_succ] at h₁,
      apply nat.le_trans _ h₁,
      apply le_add_right _ n },
    have h₄ : x - n * k ≥ n,
    { apply @nat.le_of_add_le_add_right (n*k),
      rw [nat.sub_add_cancel h₂],
      simp [mul_succ] at h₁, simp [h₁] },
    rw [mul_succ, ← nat.sub_sub, ← mod_eq_sub_mod h₄, ih_1 h₂] }
end

/- div -/

theorem sub_mul_div (x n p : ℕ) (h₁ : n*p ≤ x) : (x - n*p) / n = x / n - p :=
begin
  cases eq_zero_or_pos n with h₀ h₀,
  { rw [h₀, nat.div_zero, nat.div_zero, nat.zero_sub] },
  { induction p with p,
    { simp },
    { have h₂ : n*p ≤ x,
      { transitivity,
        { apply nat.mul_le_mul_left, apply le_succ },
        { apply h₁ } },
      have h₃ : x - n * p ≥ n,
      { apply le_of_add_le_add_right,
        rw [nat.sub_add_cancel h₂, add_comm],
        rw [mul_succ] at h₁,
        apply h₁ },
      rw [sub_succ, ← ih_1 h₂],
      rw [@div_eq_sub_div (x - n*p) _ h₀ h₃],
      simp [add_one, pred_succ, mul_succ, nat.sub_sub] } }
end

theorem div_mul_le_self : ∀ (m n : ℕ), m / n * n ≤ m
| m 0        := by simp; apply zero_le
| m (succ n) := (le_div_iff_mul_le _ _ (nat.succ_pos _)).1 (le_refl _)

@[simp] theorem add_div_right (x : ℕ) {z : ℕ} (H : z > 0) : (x + z) / z = succ (x / z) :=
by rw [div_eq_sub_div H (nat.le_add_left _ _), nat.add_sub_cancel]

@[simp] theorem add_div_left (x : ℕ) {z : ℕ} (H : z > 0) : (z + x) / z = succ (x / z) :=
by rw [add_comm, add_div_right x H]

@[simp] theorem mul_div_right (n : ℕ) {m : ℕ} (H : m > 0) : m * n / m = n :=
by {induction n; simp [*, mul_succ, -mul_comm]}

@[simp] theorem mul_div_left (m : ℕ) {n : ℕ} (H : n > 0) : m * n / n = m :=
by rw [mul_comm, mul_div_right _ H]

protected theorem div_self {n : ℕ} (H : n > 0) : n / n = 1 :=
let t := add_div_right 0 H in by rwa [zero_add, nat.zero_div] at t

theorem add_mul_div_left (x z : ℕ) {y : ℕ} (H : y > 0) : (x + y * z) / y = x / y + z :=
by {induction z with z ih, simp, rw [mul_succ, ← add_assoc, add_div_right _ H, ih]}

theorem add_mul_div_right (x y : ℕ) {z : ℕ} (H : z > 0) : (x + y * z) / z = x / z + y :=
by rw [mul_comm, add_mul_div_left _ _ H]

protected theorem mul_div_cancel (m : ℕ) {n : ℕ} (H : n > 0) : m * n / n = m :=
let t := add_mul_div_right 0 m H in by rwa [zero_add, nat.zero_div, zero_add] at t

protected theorem mul_div_cancel_left (m : ℕ) {n : ℕ} (H : n > 0) : n * m / n = m :=
by rw [mul_comm, nat.mul_div_cancel _ H]

protected theorem div_eq_of_eq_mul_left {m n k : ℕ} (H1 : n > 0) (H2 : m = k * n) :
  m / n = k :=
by rw [H2, nat.mul_div_cancel _ H1]

protected theorem div_eq_of_eq_mul_right {m n k : ℕ} (H1 : n > 0) (H2 : m = n * k) :
  m / n = k :=
by rw [H2, nat.mul_div_cancel_left _ H1]

protected theorem div_eq_of_lt_le {m n k : ℕ}
  (lo : k * n ≤ m) (hi : m < succ k * n) :
  m / n = k :=
have npos : n > 0, from (eq_zero_or_pos _).resolve_left $ λ hn,
  by rw [hn, mul_zero] at hi lo; exact absurd lo (not_le_of_gt hi),
le_antisymm
  (le_of_lt_succ ((nat.div_lt_iff_lt_mul _ _ npos).2 hi))
  ((nat.le_div_iff_mul_le _ _ npos).2 lo)

theorem mul_sub_div (x n p : ℕ) (h₁ : x < n*p) : (n * p - succ x) / n = p - succ (x / n) :=
begin
  have npos : n > 0 := (eq_zero_or_pos _).resolve_left (λ n0,
    by rw [n0, zero_mul] at h₁; exact not_lt_zero _ h₁),
  apply nat.div_eq_of_lt_le,
  { rw [nat.mul_sub_right_distrib, mul_comm],
    apply nat.sub_le_sub_left,
    exact (div_lt_iff_lt_mul _ _ npos).1 (lt_succ_self _) },
  { change succ (pred (n * p - x)) ≤ (succ (pred (p - x / n))) * n,
    rw [succ_pred_eq_of_pos (nat.sub_pos_of_lt h₁),
        succ_pred_eq_of_pos (nat.sub_pos_of_lt _)],
    { rw [nat.mul_sub_right_distrib, mul_comm],
      apply nat.sub_le_sub_left, apply div_mul_le_self },
    { apply (div_lt_iff_lt_mul _ _ npos).2, rwa mul_comm } }
end

protected theorem div_div_eq_div_mul (m n k : ℕ) : m / n / k = m / (n * k) :=
begin
  cases eq_zero_or_pos k with k0 kpos, {rw [k0, mul_zero, nat.div_zero, nat.div_zero]},
  cases eq_zero_or_pos n with n0 npos, {rw [n0, zero_mul, nat.div_zero, nat.zero_div]},
  apply le_antisymm,
  { apply (le_div_iff_mul_le _ _ (mul_pos npos kpos)).2,
    rw [mul_comm n k, ← mul_assoc],
    apply (le_div_iff_mul_le _ _ npos).1,
    apply (le_div_iff_mul_le _ _ kpos).1,
    refl },
  { apply (le_div_iff_mul_le _ _ kpos).2,
    apply (le_div_iff_mul_le _ _ npos).2,
    rw [mul_assoc, mul_comm n k],
    apply (le_div_iff_mul_le _ _ (mul_pos kpos npos)).1,
    refl }
end

protected theorem mul_div_mul {m : ℕ} (n k : ℕ) (H : m > 0) : m * n / (m * k) = n / k :=
by rw [← nat.div_div_eq_div_mul, nat.mul_div_cancel_left _ H]

/- dvd -/

protected theorem dvd_add_iff_right {k m n : ℕ} (h : k ∣ m) : k ∣ n ↔ k ∣ m + n :=
⟨dvd_add h, dvd.elim h $ λd hd, match m, hd with
| ._, rfl := λh₂, dvd.elim h₂ $ λe he, ⟨e - d,
  by rw [nat.mul_sub_left_distrib, ← he, nat.add_sub_cancel_left]⟩
end⟩

protected theorem dvd_add_iff_left {k m n : ℕ} (h : k ∣ n) : k ∣ m ↔ k ∣ m + n :=
by rw add_comm; exact nat.dvd_add_iff_right h

theorem dvd_sub {k m n : ℕ} (H : n ≤ m) (h₁ : k ∣ m) (h₂ : k ∣ n) : k ∣ m - n :=
(nat.dvd_add_iff_left h₂).2 $ by rw nat.sub_add_cancel H; exact h₁

theorem dvd_mod_iff {k m n : ℕ} (h : k ∣ n) : k ∣ m % n ↔ k ∣ m :=
let t := @nat.dvd_add_iff_left _ (m % n) _ (dvd_trans h (dvd_mul_right n (m / n))) in
by rwa mod_add_div at t

theorem le_of_dvd {m n : ℕ} (h : n > 0) : m ∣ n → m ≤ n :=
λ⟨k, e⟩, by {
  revert h, rw e, refine k.cases_on _ _,
  exact λhn, absurd hn (lt_irrefl _),
  exact λk _, let t := mul_le_mul_left m (succ_pos k) in by rwa mul_one at t }

theorem dvd_antisymm : Π {m n : ℕ}, m ∣ n → n ∣ m → m = n
| m        0        h₁ h₂ := eq_zero_of_zero_dvd h₂
| 0        n        h₁ h₂ := (eq_zero_of_zero_dvd h₁).symm
| (succ m) (succ n) h₁ h₂ := le_antisymm (le_of_dvd (succ_pos _) h₁) (le_of_dvd (succ_pos _) h₂)

theorem pos_of_dvd_of_pos {m n : ℕ} (H1 : m ∣ n) (H2 : n > 0) : m > 0 :=
nat.pos_of_ne_zero $ λm0, by rw m0 at H1; rw eq_zero_of_zero_dvd H1 at H2; exact lt_irrefl _ H2

theorem eq_one_of_dvd_one {n : ℕ} (H : n ∣ 1) : n = 1 :=
le_antisymm (le_of_dvd dec_trivial H) (pos_of_dvd_of_pos H dec_trivial)

theorem dvd_of_mod_eq_zero {m n : ℕ} (H : n % m = 0) : m ∣ n :=
dvd.intro (n / m) $ let t := mod_add_div n m in by simp [H] at t; exact t

theorem mod_eq_zero_of_dvd {m n : ℕ} (H : m ∣ n) : n % m = 0 :=
dvd.elim H (λ z H1, by rw [H1, mul_mod_right])

theorem dvd_iff_mod_eq_zero (m n : ℕ) : m ∣ n ↔ n % m = 0 :=
⟨mod_eq_zero_of_dvd, dvd_of_mod_eq_zero⟩

instance decidable_dvd : @decidable_rel ℕ (∣) :=
λm n, decidable_of_decidable_of_iff (by apply_instance) (dvd_iff_mod_eq_zero _ _).symm

protected theorem mul_div_cancel' {m n : ℕ} (H : n ∣ m) : n * (m / n) = m :=
let t := mod_add_div m n in by rwa [mod_eq_zero_of_dvd H, zero_add] at t

protected theorem div_mul_cancel {m n : ℕ} (H : n ∣ m) : m / n * n = m :=
by rw [mul_comm, nat.mul_div_cancel' H]

protected theorem mul_div_assoc (m : ℕ) {n k : ℕ} (H : k ∣ n) : m * n / k = m * (n / k) :=
or.elim (eq_zero_or_pos k)
  (λh, by rw [h, nat.div_zero, nat.div_zero, mul_zero])
  (λh, have m * n / k = m * (n / k * k) / k, by rw nat.div_mul_cancel H,
       by rw[this, ← mul_assoc, nat.mul_div_cancel _ h])

theorem dvd_of_mul_dvd_mul_left {m n k : ℕ} (kpos : k > 0) (H : k * m ∣ k * n) : m ∣ n :=
dvd.elim H (λl H1, by rw mul_assoc at H1; exact ⟨_, eq_of_mul_eq_mul_left kpos H1⟩)

theorem dvd_of_mul_dvd_mul_right {m n k : ℕ} (kpos : k > 0) (H : m * k ∣ n * k) : m ∣ n :=
by rw [mul_comm m k, mul_comm n k] at H; exact dvd_of_mul_dvd_mul_left kpos H

/- pow -/

@[simp] theorem pow_one (b : ℕ) : b^1 = b := by simp [pow_succ]

theorem pow_le_pow_of_le_left {x y : ℕ} (H : x ≤ y) : ∀ i, x^i ≤ y^i
| 0 := le_refl _
| (succ i) := mul_le_mul (pow_le_pow_of_le_left i) H (zero_le _) (zero_le _)

theorem pow_le_pow_of_le_right {x : ℕ} (H : x > 0) {i} : ∀ {j}, i ≤ j → x^i ≤ x^j
| 0        h := by rw eq_zero_of_le_zero h; apply le_refl
| (succ j) h := (lt_or_eq_of_le h).elim
  (λhl, by rw [pow_succ, ← mul_one (x^i)]; exact
    mul_le_mul (pow_le_pow_of_le_right $ le_of_lt_succ hl) H (zero_le _) (zero_le _))
  (λe, by rw e; refl)

theorem pos_pow_of_pos {b : ℕ} (n : ℕ) (h : 0 < b) : 0 < b^n :=
pow_le_pow_of_le_right h (zero_le _)

theorem zero_pow {n : ℕ} (h : 0 < n) : 0^n = 0 :=
by rw [← succ_pred_eq_of_pos h, pow_succ, mul_zero]

theorem pow_lt_pow_of_lt_left {x y : ℕ} (H : x < y) {i} (h : i > 0) : x^i < y^i :=
begin
  cases i with i, { exact absurd h (not_lt_zero _) },
  rw [pow_succ, pow_succ],
  exact mul_lt_mul' (pow_le_pow_of_le_left (le_of_lt H) _) H (zero_le _)
    (pos_pow_of_pos _ $ lt_of_le_of_lt (zero_le _) H)
end

theorem pow_lt_pow_of_lt_right {x : ℕ} (H : x > 1) {i j} (h : i < j) : x^i < x^j :=
begin
  have xpos := lt_of_succ_lt H,
  refine lt_of_lt_of_le _ (pow_le_pow_of_le_right xpos h),
  rw [← mul_one (x^i), pow_succ],
  exact nat.mul_lt_mul_of_pos_left H (pos_pow_of_pos _ xpos)
end

/- mod / div / pow -/

theorem mod_pow_succ {b : ℕ} (b_pos : b > 0) (w m : ℕ)
: m % (b^succ w) = b * (m/b % b^w) + m % b :=
begin
  apply nat.strong_induction_on m,
  clear m,
  intros p IH,
  cases lt_or_ge p (b^succ w) with h₁ h₁,
  -- base case: p < b^succ w
  { have h₂ : p / b < b^w,
    { rw [div_lt_iff_lt_mul p _ b_pos],
      simp [pow_succ] at h₁,
      simp [h₁] },
    rw [mod_eq_of_lt h₁, mod_eq_of_lt h₂],
    simp [mod_add_div] },
  -- step: p ≥ b^succ w
  { -- Generate condiition for induction principal
    have h₂ : p - b^succ w < p,
    { apply sub_lt_of_pos_le _ _ (pos_pow_of_pos _ b_pos) h₁ },

    -- Apply induction
    rw [mod_eq_sub_mod h₁, IH _ h₂],
    -- Normalize goal and h1
    simp [pow_succ],
    simp [ge, pow_succ] at h₁,
    -- Pull subtraction outside mod and div
    rw [sub_mul_mod _ _ _ h₁, sub_mul_div _ _ _ h₁],
    -- Cancel subtraction inside mod b^w
    have p_b_ge :  b^w ≤ p / b,
    { rw [le_div_iff_mul_le _ _ b_pos],
      simp [h₁] },
    rw [eq.symm (mod_eq_sub_mod p_b_ge)] }
end

/- bitwise ops -/

lemma bodd_bit (b n) : bodd (bit b n) = b :=
by rw bit_val; simp; cases b; cases bodd n; refl

lemma div2_bit (b n) : div2 (bit b n) = n :=
by rw [bit_val, div2_val, add_comm, add_mul_div_left, div_eq_of_lt, zero_add];
   cases b; exact dec_trivial

lemma shiftl'_add (b m n) : ∀ k, shiftl' b m (n + k) = shiftl' b (shiftl' b m n) k
| 0     := rfl
| (k+1) := congr_arg (bit b) (shiftl'_add k)

lemma shiftl_add : ∀ m n k, shiftl m (n + k) = shiftl (shiftl m n) k := shiftl'_add _

lemma shiftr_add (m n) : ∀ k, shiftr m (n + k) = shiftr (shiftr m n) k
| 0     := rfl
| (k+1) := congr_arg div2 (shiftr_add k)

lemma shiftl'_sub (b m) : ∀ {n k}, k ≤ n → shiftl' b m (n - k) = shiftr (shiftl' b m n) k
| n     0     h := rfl
| (n+1) (k+1) h := begin
  simp [shiftl'], rw [add_comm, shiftr_add],
  simp [shiftr, div2_bit],
  apply shiftl'_sub (nat.le_of_succ_le_succ h)
end

lemma shiftl_sub : ∀ m {n k}, k ≤ n → shiftl m (n - k) = shiftr (shiftl m n) k := shiftl'_sub _

lemma shiftl_eq_mul_pow (m) : ∀ n, shiftl m n = m * 2 ^ n
| 0     := (mul_one _).symm
| (k+1) := show bit0 (shiftl m k) = m * (2^k * 2), by rw [bit0_val, shiftl_eq_mul_pow]; simp

lemma shiftl'_tt_eq_mul_pow (m) : ∀ n, shiftl' tt m n + 1 = (m + 1) * 2 ^ n
| 0     := by simp [shiftl, shiftl']
| (k+1) := begin
  change bit1 (shiftl' tt m k) + 1 = (m + 1) * (2^k * 2),
  rw bit1_val,
  change 2 * (shiftl' tt m k + 1) = _,
  rw shiftl'_tt_eq_mul_pow; simp
end

lemma one_shiftl (n) : shiftl 1 n = 2 ^ n :=
(shiftl_eq_mul_pow _ _).trans (one_mul _)

@[simp] lemma zero_shiftl (n) : shiftl 0 n = 0 :=
(shiftl_eq_mul_pow _ _).trans (zero_mul _)

lemma shiftr_eq_div_pow (m) : ∀ n, shiftr m n = m / 2 ^ n
| 0     := (nat.div_one _).symm
| (k+1) := (congr_arg div2 (shiftr_eq_div_pow k)).trans $
           by rw [div2_val, nat.div_div_eq_div_mul]; refl

@[simp] lemma zero_shiftr (n) : shiftr 0 n = 0 :=
(shiftr_eq_div_pow _ _).trans (nat.zero_div _)

@[simp] lemma test_bit_zero (b n) : test_bit (bit b n) 0 = b := bodd_bit _ _

lemma test_bit_succ (m b n) : test_bit (bit b n) (succ m) = test_bit n m :=
have bodd (shiftr (shiftr (bit b n) 1) m) = bodd (shiftr n m),
  by dsimp [shiftr]; rw div2_bit,
by rw [← shiftr_add, add_comm] at this; exact this

lemma binary_rec_eq {C : nat → Sort u} {z : C 0} {f : ∀ b n, C n → C (bit b n)}
  (h : f ff 0 z = z) (b n) :
  binary_rec z f (bit b n) = f b n (binary_rec z f n) :=
begin
  rw [binary_rec],
  by_cases (bit b n = 0) with h',
  {simp [dif_pos h'],
   generalize : binary_rec._main._pack._proof_1 (bit b n) h' = e,
   revert e,
   have bf := bodd_bit b n,
   have n0 := div2_bit b n,
   rw h' at bf n0,
   simp at bf n0,
   rw [← bf, ← n0, binary_rec_zero],
   intros, exact h.symm },
  {simp [dif_neg h'],
   generalize : binary_rec._main._pack._proof_2 (bit b n) = e,
   revert e,
   rw [bodd_bit, div2_bit],
   intros, refl}
end

lemma bitwise_bit_aux {f : bool → bool → bool} (h : f ff ff = ff) :
  @binary_rec (λ_, ℕ)
    (cond (f tt ff) (bit ff 0) 0)
    (λ b n _, bit (f ff b) (cond (f ff tt) n 0)) =
  λ (n : ℕ), cond (f ff tt) n 0 :=
begin
  apply funext, intro n,
  apply bit_cases_on n, intros b n, rw [binary_rec_eq],
  { cases b; try {rw h}; ginduction f ff tt with fft; simp [cond]; refl },
  { rw [h, show cond (f ff tt) 0 0 = 0, by cases f ff tt; refl,
           show cond (f tt ff) (bit ff 0) 0 = 0, by cases f tt ff; refl]; refl }
end

@[simp] lemma bitwise_zero_left (f : bool → bool → bool) (n) :
  bitwise f 0 n = cond (f ff tt) n 0 :=
by unfold bitwise; rw [binary_rec_zero]

@[simp] lemma bitwise_zero_right (f : bool → bool → bool) (h : f ff ff = ff) (m) :
  bitwise f m 0 = cond (f tt ff) m 0 :=
by unfold bitwise; apply bit_cases_on m; intros;
   rw [binary_rec_eq, binary_rec_zero]; exact bitwise_bit_aux h

@[simp] lemma bitwise_zero (f : bool → bool → bool) :
  bitwise f 0 0 = 0 :=
by rw bitwise_zero_left; cases f ff tt; refl

@[simp] lemma bitwise_bit {f : bool → bool → bool} (h : f ff ff = ff) (a m b n) :
  bitwise f (bit a m) (bit b n) = bit (f a b) (bitwise f m n) :=
begin
  unfold bitwise,
  rw [binary_rec_eq, binary_rec_eq],
  { ginduction f tt ff with ftf; dsimp [cond],
    rw [show f a ff = ff, by cases a; assumption],
    apply @congr_arg _ _ _ 0 (bit ff), tactic.swap,
    rw [show f a ff = a, by cases a; assumption],
    apply congr_arg (bit a),
    all_goals {
      apply bit_cases_on m, intros a m,
      rw [binary_rec_eq, binary_rec_zero],
      rw [← bitwise_bit_aux h, ftf], refl } },
  { exact bitwise_bit_aux h }
end

theorem bitwise_swap {f : bool → bool → bool} (h : f ff ff = ff) :
  bitwise (function.swap f) = function.swap (bitwise f) :=
begin
  apply funext, intro m, apply funext,
  dsimp [function.swap],
  apply binary_rec _ (λ a m' IH, _) m; intro n,
  { rw [bitwise_zero_left, bitwise_zero_right], exact h },
  apply bit_cases_on n; intros b n',
  rw [bitwise_bit, bitwise_bit, IH]; exact h
end

@[simp] lemma lor_bit : ∀ (a m b n),
  lor (bit a m) (bit b n) = bit (a || b) (lor m n) := bitwise_bit rfl
@[simp] lemma land_bit : ∀ (a m b n),
  land (bit a m) (bit b n) = bit (a && b) (land m n) := bitwise_bit rfl
@[simp] lemma ldiff_bit : ∀ (a m b n),
  ldiff (bit a m) (bit b n) = bit (a && bnot b) (ldiff m n) := bitwise_bit rfl
@[simp] lemma lxor_bit : ∀ (a m b n),
  lxor (bit a m) (bit b n) = bit (bxor a b) (lxor m n) := bitwise_bit rfl

@[simp] lemma test_bit_bitwise {f : bool → bool → bool} (h : f ff ff = ff) (m n k) :
  test_bit (bitwise f m n) k = f (test_bit m k) (test_bit n k) :=
begin
  revert m n; induction k with k IH; intros m n;
  apply bit_cases_on m; intros a m';
  apply bit_cases_on n; intros b n';
  rw bitwise_bit h,
  { simp [test_bit_zero] },
  { simp [test_bit_succ, IH] }
end

@[simp] lemma test_bit_lor : ∀ (m n k),
  test_bit (lor m n) k = test_bit m k || test_bit n k := test_bit_bitwise rfl
@[simp] lemma test_bit_land : ∀ (m n k),
  test_bit (land m n) k = test_bit m k && test_bit n k := test_bit_bitwise rfl
@[simp] lemma test_bit_ldiff : ∀ (m n k),
  test_bit (ldiff m n) k = test_bit m k && bnot (test_bit n k) := test_bit_bitwise rfl
@[simp] lemma test_bit_lxor : ∀ (m n k),
  test_bit (lxor m n) k = bxor (test_bit m k) (test_bit n k) := test_bit_bitwise rfl

end nat
