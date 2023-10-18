/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import order.basic
import algebra.group_with_zero.basic
import algebra.ring.defs

/-!
# Basic operations on the natural numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains:
- instances on the natural numbers
- some basic lemmas about natural numbers
- extra recursors:
  * `le_rec_on`, `le_induction`: recursion and induction principles starting at non-zero numbers
  * `decreasing_induction`: recursion growing downwards
  * `le_rec_on'`, `decreasing_induction'`: versions with slightly weaker assumptions
  * `strong_rec'`: recursion based on strong inequalities
- decidability instances on predicates about the natural numbers

Many theorems that used to live in this file have been moved to `data.nat.order`,
so that this file requires fewer imports.
For each section here there is a corresponding section in that file with additional results.
It may be possible to move some of these results here, by tweaking their proofs.


-/

universes u v

/-! ### instances -/

instance : nontrivial ℕ :=
⟨⟨0, 1, nat.zero_ne_one⟩⟩

instance : comm_semiring ℕ :=
{ add            := nat.add,
  add_assoc      := nat.add_assoc,
  zero           := nat.zero,
  zero_add       := nat.zero_add,
  add_zero       := nat.add_zero,
  add_comm       := nat.add_comm,
  mul            := nat.mul,
  mul_assoc      := nat.mul_assoc,
  one            := nat.succ nat.zero,
  one_mul        := nat.one_mul,
  mul_one        := nat.mul_one,
  left_distrib   := nat.left_distrib,
  right_distrib  := nat.right_distrib,
  zero_mul       := nat.zero_mul,
  mul_zero       := nat.mul_zero,
  mul_comm       := nat.mul_comm,
  nat_cast       := λ n, n,
  nat_cast_zero  := rfl,
  nat_cast_succ  := λ n, rfl,
  nsmul          := λ m n, m * n,
  nsmul_zero'    := nat.zero_mul,
  nsmul_succ'    := λ n x,
    by rw [nat.succ_eq_add_one, nat.add_comm, nat.right_distrib, nat.one_mul] }

/-! Extra instances to short-circuit type class resolution and ensure computability -/

instance : add_comm_monoid ℕ              := infer_instance
instance : add_monoid ℕ                   := infer_instance
instance : monoid ℕ                       := infer_instance
instance : comm_monoid ℕ                  := infer_instance
instance : comm_semigroup ℕ               := infer_instance
instance : semigroup ℕ                    := infer_instance
instance : add_comm_semigroup ℕ           := infer_instance
instance : add_semigroup ℕ                := infer_instance
instance : distrib ℕ                      := infer_instance
instance : semiring ℕ                     := infer_instance

protected lemma nat.nsmul_eq_mul (m n : ℕ) : m • n = m * n := rfl

instance nat.cancel_comm_monoid_with_zero : cancel_comm_monoid_with_zero ℕ :=
{ mul_left_cancel_of_ne_zero :=
    λ _ _ _ h1 h2, nat.eq_of_mul_eq_mul_left (nat.pos_of_ne_zero h1) h2,
  .. nat.comm_semiring }

attribute [simp] nat.not_lt_zero nat.succ_ne_zero nat.succ_ne_self
  nat.zero_ne_one nat.one_ne_zero
  nat.zero_ne_bit1 nat.bit1_ne_zero
  nat.bit0_ne_one nat.one_ne_bit0
  nat.bit0_ne_bit1 nat.bit1_ne_bit0

variables {m n k : ℕ}
namespace nat

/-!
### Recursion and `forall`/`exists`
-/

@[simp] lemma and_forall_succ {p : ℕ → Prop} : (p 0 ∧ ∀ n, p (n + 1)) ↔ ∀ n, p n :=
⟨λ h n, nat.cases_on n h.1 h.2, λ h, ⟨h _, λ n, h _⟩⟩

@[simp] lemma or_exists_succ {p : ℕ → Prop} : (p 0 ∨ ∃ n, p (n + 1)) ↔ ∃ n, p n :=
⟨λ h, h.elim (λ h0, ⟨0, h0⟩) (λ ⟨n, hn⟩, ⟨n + 1, hn⟩),
  by { rintro ⟨(_|n), hn⟩, exacts [or.inl hn, or.inr ⟨n, hn⟩]}⟩

/-! ### `succ` -/


lemma _root_.has_lt.lt.nat_succ_le {n m : ℕ} (h : n < m) : succ n ≤ m := succ_le_of_lt h

lemma succ_eq_one_add (n : ℕ) : n.succ = 1 + n :=
by rw [nat.succ_eq_add_one, nat.add_comm]

theorem eq_of_lt_succ_of_not_lt {a b : ℕ} (h1 : a < b + 1) (h2 : ¬ a < b) : a = b :=
have h3 : a ≤ b, from le_of_lt_succ h1,
or.elim (eq_or_lt_of_not_lt h2) (λ h, h) (λ h, absurd h (not_lt_of_ge h3))

lemma eq_of_le_of_lt_succ {n m : ℕ} (h₁ : n ≤ m) (h₂ : m < n + 1) : m = n :=
nat.le_antisymm (le_of_succ_le_succ h₂) h₁

theorem one_add (n : ℕ) : 1 + n = succ n := by simp [add_comm]

@[simp] lemma succ_pos' {n : ℕ} : 0 < succ n := succ_pos n

theorem succ_inj' {n m : ℕ} : succ n = succ m ↔ n = m :=
⟨succ.inj, congr_arg _⟩

theorem succ_injective : function.injective nat.succ := λ x y, succ.inj

lemma succ_ne_succ {n m : ℕ} : succ n ≠ succ m ↔ n ≠ m :=
succ_injective.ne_iff

@[simp] lemma succ_succ_ne_one (n : ℕ) : n.succ.succ ≠ 1 :=
succ_ne_succ.mpr n.succ_ne_zero

@[simp] lemma one_lt_succ_succ (n : ℕ) : 1 < n.succ.succ :=
succ_lt_succ $ succ_pos n


theorem succ_le_succ_iff {m n : ℕ} : succ m ≤ succ n ↔ m ≤ n :=
⟨le_of_succ_le_succ, succ_le_succ⟩

theorem max_succ_succ {m n : ℕ} :
  max (succ m) (succ n) = succ (max m n) :=
begin
  by_cases h1 : m ≤ n,
  rw [max_eq_right h1, max_eq_right (succ_le_succ h1)],
  { rw not_le at h1, have h2 := le_of_lt h1,
    rw [max_eq_left h2, max_eq_left (succ_le_succ h2)] }
end

lemma not_succ_lt_self {n : ℕ} : ¬succ n < n :=
not_lt_of_ge (nat.le_succ _)

theorem lt_succ_iff {m n : ℕ} : m < succ n ↔ m ≤ n :=
⟨le_of_lt_succ, lt_succ_of_le⟩

lemma succ_le_iff {m n : ℕ} : succ m ≤ n ↔ m < n :=
⟨lt_of_succ_le, succ_le_of_lt⟩

lemma lt_iff_add_one_le {m n : ℕ} : m < n ↔ m + 1 ≤ n :=
by rw succ_le_iff

-- Just a restatement of `nat.lt_succ_iff` using `+1`.
lemma lt_add_one_iff {a b : ℕ} : a < b + 1 ↔ a ≤ b :=
lt_succ_iff

-- A flipped version of `lt_add_one_iff`.
lemma lt_one_add_iff {a b : ℕ} : a < 1 + b ↔ a ≤ b :=
by simp only [add_comm, lt_succ_iff]

-- This is true reflexively, by the definition of `≤` on ℕ,
-- but it's still useful to have, to convince Lean to change the syntactic type.
lemma add_one_le_iff {a b : ℕ} : a + 1 ≤ b ↔ a < b :=
iff.refl _

lemma one_add_le_iff {a b : ℕ} : 1 + a ≤ b ↔ a < b :=
by simp only [add_comm, add_one_le_iff]

theorem of_le_succ {n m : ℕ} (H : n ≤ m.succ) : n ≤ m ∨ n = m.succ :=
H.lt_or_eq_dec.imp le_of_lt_succ id

lemma succ_lt_succ_iff {m n : ℕ} : succ m < succ n ↔ m < n :=
⟨lt_of_succ_lt_succ, succ_lt_succ⟩

lemma div_le_iff_le_mul_add_pred {m n k : ℕ} (n0 : 0 < n) : m / n ≤ k ↔ m ≤ n * k + (n - 1) :=
begin
  rw [← lt_succ_iff, div_lt_iff_lt_mul n0, succ_mul, mul_comm],
  cases n, {cases n0},
  exact lt_succ_iff,
end

lemma two_lt_of_ne : ∀ {n}, n ≠ 0 → n ≠ 1 → n ≠ 2 → 2 < n
| 0 h _ _ := (h rfl).elim
| 1 _ h _ := (h rfl).elim
| 2 _ _ h := (h rfl).elim
| (n+3) _ _ _ := dec_trivial

theorem forall_lt_succ {P : ℕ → Prop} {n : ℕ} : (∀ m < n + 1, P m) ↔ (∀ m < n, P m) ∧ P n :=
by simp only [lt_succ_iff, decidable.le_iff_eq_or_lt, forall_eq_or_imp, and.comm]

theorem exists_lt_succ {P : ℕ → Prop} {n : ℕ} : (∃ m < n + 1, P m) ↔ (∃ m < n, P m) ∨ P n :=
by { rw ←not_iff_not, push_neg, exact forall_lt_succ }

/-! ### `add` -/

-- Sometimes a bare `nat.add` or similar appears as a consequence of unfolding
-- during pattern matching. These lemmas package them back up as typeclass
-- mediated operations.
@[simp] theorem add_def {a b : ℕ} : nat.add a b = a + b := rfl
@[simp] theorem mul_def {a b : ℕ} : nat.mul a b = a * b := rfl

lemma exists_eq_add_of_le (h : m ≤ n) : ∃ k : ℕ, n = m + k :=
⟨n - m, (nat.add_sub_of_le h).symm⟩

lemma exists_eq_add_of_le' (h : m ≤ n) : ∃ k : ℕ, n = k + m :=
⟨n - m, (nat.sub_add_cancel h).symm⟩

lemma exists_eq_add_of_lt (h : m < n) : ∃ k : ℕ, n = m + k + 1 :=
⟨n - (m + 1), by rw [add_right_comm, nat.add_sub_of_le h]⟩

/-! ### `pred` -/

@[simp]
lemma add_succ_sub_one (n m : ℕ) : (n + succ m) - 1 = n + m :=
by rw [add_succ, succ_sub_one]

@[simp]
lemma succ_add_sub_one (n m : ℕ) : (succ n + m) - 1 = n + m :=
by rw [succ_add, succ_sub_one]

lemma pred_eq_sub_one (n : ℕ) : pred n = n - 1 := rfl

theorem pred_eq_of_eq_succ {m n : ℕ} (H : m = n.succ) : m.pred = n := by simp [H]

@[simp] lemma pred_eq_succ_iff {n m : ℕ} : pred n = succ m ↔ n = m + 2 :=
by cases n; split; rintro ⟨⟩; refl

theorem pred_sub (n m : ℕ) : pred n - m = pred (n - m) :=
by rw [← nat.sub_one, nat.sub_sub, one_add, sub_succ]

lemma le_pred_of_lt {n m : ℕ} (h : m < n) : m ≤ n - 1 :=
nat.sub_le_sub_right h 1

lemma le_of_pred_lt {m n : ℕ} : pred m < n → m ≤ n :=
match m with
| 0 := le_of_lt
| m+1 := id
end

/-- This ensures that `simp` succeeds on `pred (n + 1) = n`. -/
@[simp] lemma pred_one_add (n : ℕ) : pred (1 + n) = n :=
by rw [add_comm, add_one, pred_succ]

/-! ### `mul` -/


theorem two_mul_ne_two_mul_add_one {n m} : 2 * n ≠ 2 * m + 1 :=
mt (congr_arg (%2)) (by { rw [add_comm, add_mul_mod_self_left, mul_mod_right, mod_eq_of_lt]; simp })

lemma mul_ne_mul_left {a b c : ℕ} (ha : 0 < a) : b * a ≠ c * a ↔ b ≠ c :=
(mul_left_injective₀ ha.ne').ne_iff

lemma mul_ne_mul_right {a b c : ℕ} (ha : 0 < a) : a * b ≠ a * c ↔ b ≠ c :=
(mul_right_injective₀ ha.ne').ne_iff

lemma mul_right_eq_self_iff {a b : ℕ} (ha : 0 < a) : a * b = a ↔ b = 1 :=
suffices a * b = a * 1 ↔ b = 1, by rwa mul_one at this,
mul_right_inj' ha.ne'

lemma mul_left_eq_self_iff {a b : ℕ} (hb : 0 < b) : a * b = b ↔ a = 1 :=
by rw [mul_comm, nat.mul_right_eq_self_iff hb]

lemma lt_succ_iff_lt_or_eq {n i : ℕ} : n < i.succ ↔ (n < i ∨ n = i) :=
lt_succ_iff.trans decidable.le_iff_lt_or_eq


/-!
### Recursion and induction principles

This section is here due to dependencies -- the lemmas here require some of the lemmas
proved above, and some of the results in later sections depend on the definitions in this section.
-/

@[simp] lemma rec_zero {C : ℕ → Sort u} (h0 : C 0) (h : ∀ n, C n → C (n + 1)) :
  (nat.rec h0 h : Π n, C n) 0 = h0 :=
rfl

@[simp] lemma rec_add_one {C : ℕ → Sort u} (h0 : C 0) (h : ∀ n, C n → C (n + 1)) (n : ℕ) :
  (nat.rec h0 h : Π n, C n) (n + 1) = h n ((nat.rec h0 h : Π n, C n) n) :=
rfl

/-- Recursion starting at a non-zero number: given a map `C k → C (k+1)` for each `k`,
there is a map from `C n` to each `C m`, `n ≤ m`. For a version where the assumption is only made
when `k ≥ n`, see `le_rec_on'`. -/
@[elab_as_eliminator]
def le_rec_on {C : ℕ → Sort u} {n : ℕ} : Π {m : ℕ}, n ≤ m → (Π {k}, C k → C (k+1)) → C n → C m
| 0     H next x := eq.rec_on (nat.eq_zero_of_le_zero H) x
| (m+1) H next x := or.by_cases (of_le_succ H) (λ h : n ≤ m, next $ le_rec_on h @next x)
  (λ h : n = m + 1, eq.rec_on h x)

theorem le_rec_on_self {C : ℕ → Sort u} {n} {h : n ≤ n} {next} (x : C n) :
  (le_rec_on h next x : C n) = x :=
by cases n; unfold le_rec_on or.by_cases; rw [dif_neg n.not_succ_le_self]

theorem le_rec_on_succ {C : ℕ → Sort u} {n m} (h1 : n ≤ m) {h2 : n ≤ m+1} {next} (x : C n) :
  (le_rec_on h2 @next x : C (m+1)) = next (le_rec_on h1 @next x : C m) :=
by conv { to_lhs, rw [le_rec_on, or.by_cases, dif_pos h1] }

theorem le_rec_on_succ' {C : ℕ → Sort u} {n} {h : n ≤ n+1} {next} (x : C n) :
  (le_rec_on h next x : C (n+1)) = next x :=
by rw [le_rec_on_succ (le_refl n), le_rec_on_self]

theorem le_rec_on_trans {C : ℕ → Sort u} {n m k} (hnm : n ≤ m) (hmk : m ≤ k) {next} (x : C n) :
  (le_rec_on (le_trans hnm hmk) @next x : C k) = le_rec_on hmk @next (le_rec_on hnm @next x) :=
begin
  induction hmk with k hmk ih, { rw le_rec_on_self },
  rw [le_rec_on_succ (le_trans hnm hmk), ih, le_rec_on_succ]
end

theorem le_rec_on_succ_left {C : ℕ → Sort u} {n m} (h1 : n ≤ m) (h2 : n+1 ≤ m)
  {next : Π{{k}}, C k → C (k+1)} (x : C n) :
  (le_rec_on h2 next (next x) : C m) = (le_rec_on h1 next x : C m) :=
begin
  rw [subsingleton.elim h1 (le_trans (le_succ n) h2),
      le_rec_on_trans (le_succ n) h2, le_rec_on_succ']
end

theorem le_rec_on_injective {C : ℕ → Sort u} {n m} (hnm : n ≤ m)
  (next : Π n, C n → C (n+1)) (Hnext : ∀ n, function.injective (next n)) :
  function.injective (le_rec_on hnm next) :=
begin
  induction hnm with m hnm ih, { intros x y H, rwa [le_rec_on_self, le_rec_on_self] at H },
  intros x y H, rw [le_rec_on_succ hnm, le_rec_on_succ hnm] at H, exact ih (Hnext _ H)
end

theorem le_rec_on_surjective {C : ℕ → Sort u} {n m} (hnm : n ≤ m)
  (next : Π n, C n → C (n+1)) (Hnext : ∀ n, function.surjective (next n)) :
  function.surjective (le_rec_on hnm next) :=
begin
  induction hnm with m hnm ih, { intros x, use x, rw le_rec_on_self },
  intros x, rcases Hnext _ x with ⟨w, rfl⟩, rcases ih w with ⟨x, rfl⟩, use x, rw le_rec_on_succ
end

/-- Recursion principle based on `<`. -/
@[elab_as_eliminator]
protected def strong_rec' {p : ℕ → Sort u} (H : ∀ n, (∀ m, m < n → p m) → p n) : ∀ (n : ℕ), p n
| n := H n (λ m hm, strong_rec' m)

/-- Recursion principle based on `<` applied to some natural number. -/
@[elab_as_eliminator]
def strong_rec_on' {P : ℕ → Sort*} (n : ℕ) (h : ∀ n, (∀ m, m < n → P m) → P n) : P n :=
nat.strong_rec' h n

theorem strong_rec_on_beta' {P : ℕ → Sort*} {h} {n : ℕ} :
  (strong_rec_on' n h : P n) = h n (λ m hmn, (strong_rec_on' m h : P m)) :=
by { simp only [strong_rec_on'], rw nat.strong_rec' }

/-- Induction principle starting at a non-zero number. For maps to a `Sort*` see `le_rec_on`. -/
@[elab_as_eliminator] lemma le_induction {P : nat → Prop} {m}
  (h0 : P m) (h1 : ∀ n, m ≤ n → P n → P (n + 1)) :
  ∀ n, m ≤ n → P n :=
by apply nat.less_than_or_equal.rec h0; exact h1

/-- Decreasing induction: if `P (k+1)` implies `P k`, then `P n` implies `P m` for all `m ≤ n`.
Also works for functions to `Sort*`. For a version assuming only the assumption for `k < n`, see
`decreasing_induction'`. -/
@[elab_as_eliminator]
def decreasing_induction {P : ℕ → Sort*} (h : ∀n, P (n+1) → P n) {m n : ℕ} (mn : m ≤ n)
  (hP : P n) : P m :=
le_rec_on mn (λ k ih hsk, ih $ h k hsk) (λ h, h) hP

@[simp] lemma decreasing_induction_self {P : ℕ → Sort*} (h : ∀n, P (n+1) → P n) {n : ℕ}
  (nn : n ≤ n) (hP : P n) : (decreasing_induction h nn hP : P n) = hP :=
by { dunfold decreasing_induction, rw [le_rec_on_self] }

lemma decreasing_induction_succ {P : ℕ → Sort*} (h : ∀n, P (n+1) → P n) {m n : ℕ} (mn : m ≤ n)
  (msn : m ≤ n + 1) (hP : P (n+1)) :
  (decreasing_induction h msn hP : P m) = decreasing_induction h mn (h n hP) :=
by { dunfold decreasing_induction, rw [le_rec_on_succ] }

@[simp] lemma decreasing_induction_succ' {P : ℕ → Sort*} (h : ∀n, P (n+1) → P n) {m : ℕ}
  (msm : m ≤ m + 1) (hP : P (m+1)) : (decreasing_induction h msm hP : P m) = h m hP :=
by { dunfold decreasing_induction, rw [le_rec_on_succ'] }

lemma decreasing_induction_trans {P : ℕ → Sort*} (h : ∀n, P (n+1) → P n) {m n k : ℕ}
  (mn : m ≤ n) (nk : n ≤ k) (hP : P k) :
  (decreasing_induction h (le_trans mn nk) hP : P m) =
  decreasing_induction h mn (decreasing_induction h nk hP) :=
by { induction nk with k nk ih, rw [decreasing_induction_self],
     rw [decreasing_induction_succ h (le_trans mn nk), ih, decreasing_induction_succ] }

lemma decreasing_induction_succ_left {P : ℕ → Sort*} (h : ∀n, P (n+1) → P n) {m n : ℕ}
  (smn : m + 1 ≤ n) (mn : m ≤ n) (hP : P n) :
  (decreasing_induction h mn hP : P m) = h m (decreasing_induction h smn hP) :=
by { rw [subsingleton.elim mn (le_trans (le_succ m) smn), decreasing_induction_trans,
         decreasing_induction_succ'] }

/-- Given `P : ℕ → ℕ → Sort*`, if for all `a b : ℕ` we can extend `P` from the rectangle
strictly below `(a,b)` to `P a b`, then we have `P n m` for all `n m : ℕ`.
Note that for non-`Prop` output it is preferable to use the equation compiler directly if possible,
since this produces equation lemmas. -/
@[elab_as_eliminator]
def strong_sub_recursion {P : ℕ → ℕ → Sort*}
  (H : ∀ a b, (∀ x y, x < a → y < b → P x y) → P a b) : Π (n m : ℕ), P n m
| n m := H n m (λ x y hx hy, strong_sub_recursion x y)

/-- Given `P : ℕ → ℕ → Sort*`, if we have `P i 0` and `P 0 i` for all `i : ℕ`,
and for any `x y : ℕ` we can extend `P` from `(x,y+1)` and `(x+1,y)` to `(x+1,y+1)`
then we have `P n m` for all `n m : ℕ`.
Note that for non-`Prop` output it is preferable to use the equation compiler directly if possible,
since this produces equation lemmas. -/
@[elab_as_eliminator]
def pincer_recursion {P : ℕ → ℕ → Sort*} (Ha0 : ∀ a : ℕ, P a 0) (H0b : ∀ b : ℕ, P 0 b)
  (H : ∀ x y : ℕ, P x y.succ → P x.succ y → P x.succ y.succ) : ∀ (n m : ℕ), P n m
| a 0 := Ha0 a
| 0 b := H0b b
| (nat.succ a) (nat.succ b) := H _ _ (pincer_recursion _ _) (pincer_recursion _ _)

/-- Recursion starting at a non-zero number: given a map `C k → C (k+1)` for each `k ≥ n`,
there is a map from `C n` to each `C m`, `n ≤ m`. -/
@[elab_as_eliminator]
def le_rec_on' {C : ℕ → Sort*} {n : ℕ} :
  Π {m : ℕ}, n ≤ m → (Π ⦃k⦄, n ≤ k → C k → C (k+1)) → C n → C m
| 0     H next x := eq.rec_on (nat.eq_zero_of_le_zero H) x
| (m+1) H next x := or.by_cases (of_le_succ H) (λ h : n ≤ m, next h $ le_rec_on' h next x)
  (λ h : n = m + 1, eq.rec_on h x)

/-- Decreasing induction: if `P (k+1)` implies `P k` for all `m ≤ k < n`, then `P n` implies `P m`.
Also works for functions to `Sort*`. Weakens the assumptions of `decreasing_induction`. -/
@[elab_as_eliminator]
def decreasing_induction' {P : ℕ → Sort*} {m n : ℕ} (h : ∀ k < n, m ≤ k → P (k+1) → P k)
  (mn : m ≤ n) (hP : P n) : P m :=
begin
  -- induction mn using nat.le_rec_on' generalizing h hP -- this doesn't work unfortunately
  refine le_rec_on' mn _ _ h hP; clear h hP mn n,
  { intros n mn ih h hP,
    apply ih,
    { exact λ k hk, h k hk.step },
    { exact h n (lt_succ_self n) mn hP } },
  { intros h hP, exact hP }
end

/-! ### `div` -/

attribute [simp] nat.div_self

/-- A version of `nat.div_lt_self` using successors, rather than additional hypotheses. -/
lemma div_lt_self' (n b : ℕ) : (n+1)/(b+2) < n+1 :=
nat.div_lt_self (nat.succ_pos n) (nat.succ_lt_succ (nat.succ_pos _))

theorem le_div_iff_mul_le' {x y : ℕ} {k : ℕ} (k0 : 0 < k) : x ≤ y / k ↔ x * k ≤ y :=
le_div_iff_mul_le k0

theorem div_lt_iff_lt_mul' {x y : ℕ} {k : ℕ} (k0 : 0 < k) : x / k < y ↔ x < y * k :=
lt_iff_lt_of_le_iff_le $ le_div_iff_mul_le' k0

lemma one_le_div_iff {a b : ℕ} (hb : 0 < b) : 1 ≤ a / b ↔ b ≤ a :=
by rw [le_div_iff_mul_le hb, one_mul]

lemma div_lt_one_iff {a b : ℕ} (hb : 0 < b) : a / b < 1 ↔ a < b :=
lt_iff_lt_of_le_iff_le $ one_le_div_iff hb

protected theorem div_le_div_right {n m : ℕ} (h : n ≤ m) {k : ℕ} : n / k ≤ m / k :=
(nat.eq_zero_or_pos k).elim (λ k0, by simp [k0]) $ λ hk,
(le_div_iff_mul_le' hk).2 $ le_trans (nat.div_mul_le_self _ _) h

lemma lt_of_div_lt_div {m n k : ℕ} : m / k < n / k → m < n :=
lt_imp_lt_of_le_imp_le $ λ h, nat.div_le_div_right h

protected lemma div_pos {a b : ℕ} (hba : b ≤ a) (hb : 0 < b) : 0 < a / b :=
nat.pos_of_ne_zero (λ h, lt_irrefl a
  (calc a = a % b : by simpa [h] using (mod_add_div a b).symm
      ... < b : nat.mod_lt a hb
      ... ≤ a : hba))

lemma lt_mul_of_div_lt {a b c : ℕ} (h : a / c < b) (w : 0 < c) : a < b * c :=
lt_of_not_ge $ not_le_of_gt h ∘ (nat.le_div_iff_mul_le w).2

lemma mul_div_le_mul_div_assoc (a b c : ℕ) : a * (b / c) ≤ (a * b) / c :=
if hc0 : c = 0 then by simp [hc0]
else (nat.le_div_iff_mul_le (nat.pos_of_ne_zero hc0)).2
  (by rw [mul_assoc]; exact nat.mul_le_mul_left _ (nat.div_mul_le_self _ _))


protected theorem eq_mul_of_div_eq_right {a b c : ℕ} (H1 : b ∣ a) (H2 : a / b = c) :
  a = b * c :=
by rw [← H2, nat.mul_div_cancel' H1]

protected theorem div_eq_iff_eq_mul_right {a b c : ℕ} (H : 0 < b) (H' : b ∣ a) :
  a / b = c ↔ a = b * c :=
⟨nat.eq_mul_of_div_eq_right H', nat.div_eq_of_eq_mul_right H⟩

protected theorem div_eq_iff_eq_mul_left {a b c : ℕ} (H : 0 < b) (H' : b ∣ a) :
  a / b = c ↔ a = c * b :=
by rw mul_comm; exact nat.div_eq_iff_eq_mul_right H H'

protected theorem eq_mul_of_div_eq_left {a b c : ℕ} (H1 : b ∣ a) (H2 : a / b = c) :
  a = c * b :=
by rw [mul_comm, nat.eq_mul_of_div_eq_right H1 H2]


protected theorem mul_div_cancel_left' {a b : ℕ} (Hd :  a ∣ b) : a * (b / a) = b :=
by rw [mul_comm,nat.div_mul_cancel Hd]

/-- Alias of `nat.mul_div_mul` -/ --TODO: Update `nat.mul_div_mul` in the core?
protected lemma mul_div_mul_left (a b : ℕ) {c : ℕ} (hc : 0 < c) : c * a / (c * b) = a / b :=
nat.mul_div_mul a b hc
protected lemma mul_div_mul_right (a b : ℕ) {c : ℕ} (hc : 0 < c) : a * c / (b * c) = a / b :=
by rw [mul_comm, mul_comm b, a.mul_div_mul_left b hc]

lemma lt_div_mul_add {a b : ℕ} (hb : 0 < b) : a < a/b*b + b :=
begin
  rw [←nat.succ_mul, ←nat.div_lt_iff_lt_mul hb],
  exact nat.lt_succ_self _,
end

@[simp]
protected lemma div_left_inj {a b d : ℕ} (hda : d ∣ a) (hdb : d ∣ b) : a / d = b / d ↔ a = b :=
begin
  refine ⟨λ h, _, congr_arg _⟩,
  rw [←nat.mul_div_cancel' hda, ←nat.mul_div_cancel' hdb, h],
end

/-! ### `mod`, `dvd` -/


lemma mod_eq_iff_lt {a b : ℕ} (h : b ≠ 0) : a % b = a ↔ a < b :=
begin
  cases b, contradiction,
  exact ⟨λ h, h.ge.trans_lt (mod_lt _ (succ_pos _)), mod_eq_of_lt⟩,
end

@[simp] lemma mod_succ_eq_iff_lt {a b : ℕ} : a % b.succ = a ↔ a < b.succ :=
mod_eq_iff_lt (succ_ne_zero _)

lemma div_add_mod (m k : ℕ) : k * (m / k) + m % k = m :=
(nat.add_comm _ _).trans (mod_add_div _ _)

lemma mod_add_div' (m k : ℕ) : m % k + (m / k) * k = m :=
by { rw mul_comm, exact mod_add_div _ _ }

lemma div_add_mod' (m k : ℕ) : (m / k) * k + m % k = m :=
by { rw mul_comm, exact div_add_mod _ _ }

/-- See also `nat.div_mod_equiv` for a similar statement as an `equiv`. -/
protected theorem div_mod_unique {n k m d : ℕ} (h : 0 < k) :
  n / k = d ∧ n % k = m ↔ m + k * d = n ∧ m < k :=
⟨λ ⟨e₁, e₂⟩, e₁ ▸ e₂ ▸ ⟨mod_add_div _ _, mod_lt _ h⟩,
 λ ⟨h₁, h₂⟩, h₁ ▸ by rw [add_mul_div_left _ _ h, add_mul_mod_self_left];
   simp [div_eq_of_lt, mod_eq_of_lt, h₂]⟩

protected theorem dvd_add_left {k m n : ℕ} (h : k ∣ n) : k ∣ m + n ↔ k ∣ m :=
(nat.dvd_add_iff_left h).symm

protected theorem dvd_add_right {k m n : ℕ} (h : k ∣ m) : k ∣ m + n ↔ k ∣ n :=
(nat.dvd_add_iff_right h).symm

protected theorem mul_dvd_mul_iff_left {a b c : ℕ} (ha : 0 < a) : a * b ∣ a * c ↔ b ∣ c :=
exists_congr $ λ d, by rw [mul_assoc, mul_right_inj' ha.ne']

protected theorem mul_dvd_mul_iff_right {a b c : ℕ} (hc : 0 < c) : a * c ∣ b * c ↔ a ∣ b :=
exists_congr $ λ d, by rw [mul_right_comm, mul_left_inj' hc.ne']

@[simp] theorem mod_mod_of_dvd (n : nat) {m k : nat} (h : m ∣ k) : n % k % m = n % m :=
begin
  conv { to_rhs, rw ←mod_add_div n k },
  rcases h with ⟨t, rfl⟩, rw [mul_assoc, add_mul_mod_self_left]
end

@[simp] theorem mod_mod (a n : ℕ) : (a % n) % n = a % n :=
(nat.eq_zero_or_pos n).elim
  (λ n0, by simp [n0])
  (λ npos, mod_eq_of_lt (mod_lt _ npos))

@[simp] theorem mod_add_mod (m n k : ℕ) : (m % n + k) % n = (m + k) % n :=
by have := (add_mul_mod_self_left (m % n + k) n (m / n)).symm;
   rwa [add_right_comm, mod_add_div] at this

@[simp] theorem add_mod_mod (m n k : ℕ) : (m + n % k) % k = (m + n) % k :=
by rw [add_comm, mod_add_mod, add_comm]

lemma add_mod (a b n : ℕ) : (a + b) % n = ((a % n) + (b % n)) % n :=
by rw [add_mod_mod, mod_add_mod]

theorem add_mod_eq_add_mod_right {m n k : ℕ} (i : ℕ) (H : m % n = k % n) :
  (m + i) % n = (k + i) % n :=
by rw [← mod_add_mod, ← mod_add_mod k, H]

theorem add_mod_eq_add_mod_left {m n k : ℕ} (i : ℕ) (H : m % n = k % n) :
  (i + m) % n = (i + k) % n :=
by rw [add_comm, add_mod_eq_add_mod_right _ H, add_comm]

lemma mul_mod (a b n : ℕ) : (a * b) % n = ((a % n) * (b % n)) % n :=
begin
  conv_lhs
  { rw [←mod_add_div a n, ←mod_add_div' b n, right_distrib, left_distrib, left_distrib,
        mul_assoc, mul_assoc, ←left_distrib n _ _, add_mul_mod_self_left, ← mul_assoc,
        add_mul_mod_self_right] }
end

lemma mul_dvd_of_dvd_div {a b c : ℕ} (hab : c ∣ b) (h : a ∣ b / c) : c * a ∣ b :=
have h1 : ∃ d, b / c = a * d, from h,
have h2 : ∃ e, b = c * e, from hab,
let ⟨d, hd⟩ := h1, ⟨e, he⟩ := h2 in
have h3 : b = a * d * c, from
  nat.eq_mul_of_div_eq_left hab hd,
show ∃ d, b = c * a * d, from ⟨d, by cc⟩

lemma eq_of_dvd_of_div_eq_one {a b : ℕ} (w : a ∣ b) (h : b / a = 1) : a = b :=
by rw [←nat.div_mul_cancel w, h, one_mul]

lemma eq_zero_of_dvd_of_div_eq_zero {a b : ℕ} (w : a ∣ b) (h : b / a = 0) : b = 0 :=
by rw [←nat.div_mul_cancel w, h, zero_mul]

lemma div_le_div_left {a b c : ℕ} (h₁ : c ≤ b) (h₂ : 0 < c) : a / b ≤ a / c :=
(nat.le_div_iff_mul_le h₂).2 $
  le_trans (nat.mul_le_mul_left _ h₁) (div_mul_le_self _ _)

lemma lt_iff_le_pred : ∀ {m n : ℕ}, 0 < n → (m < n ↔ m ≤ n - 1)
| m (n+1) _ := lt_succ_iff

lemma mul_div_le (m n : ℕ) : n * (m / n) ≤ m :=
begin
  cases nat.eq_zero_or_pos n with n0 h,
  { rw [n0, zero_mul], exact m.zero_le },
  { rw [mul_comm, ← nat.le_div_iff_mul_le' h] },
end

lemma lt_mul_div_succ (m : ℕ) {n : ℕ} (n0 : 0 < n) : m < n * ((m / n) + 1) :=
begin
  rw [mul_comm, ← nat.div_lt_iff_lt_mul' n0],
  exact lt_succ_self _
end

lemma mul_add_mod (a b c : ℕ) : (a * b + c) % b = c % b :=
by simp [nat.add_mod]

lemma mul_add_mod_of_lt {a b c : ℕ} (h : c < b) : (a * b + c) % b = c :=
by rw [nat.mul_add_mod, nat.mod_eq_of_lt h]

lemma pred_eq_self_iff {n : ℕ} : n.pred = n ↔ n = 0 :=
by { cases n; simp [(nat.succ_ne_self _).symm] }

/-! ### `find` -/
section find

variables {p q : ℕ → Prop} [decidable_pred p] [decidable_pred q]

lemma find_eq_iff (h : ∃ n : ℕ, p n) : nat.find h = m ↔ p m ∧ ∀ n < m, ¬ p n :=
begin
  split,
  { rintro rfl, exact ⟨nat.find_spec h, λ _, nat.find_min h⟩ },
  { rintro ⟨hm, hlt⟩,
    exact le_antisymm (nat.find_min' h hm) (not_lt.1 $ imp_not_comm.1 (hlt _) $ nat.find_spec h) }
end

@[simp] lemma find_lt_iff (h : ∃ n : ℕ, p n) (n : ℕ) : nat.find h < n ↔ ∃ m < n, p m :=
⟨λ h2, ⟨nat.find h, h2, nat.find_spec h⟩, λ ⟨m, hmn, hm⟩, (nat.find_min' h hm).trans_lt hmn⟩

@[simp] lemma find_le_iff (h : ∃ n : ℕ, p n) (n : ℕ) : nat.find h ≤ n ↔ ∃ m ≤ n, p m :=
by simp only [exists_prop, ← lt_succ_iff, find_lt_iff]

@[simp] lemma le_find_iff (h : ∃ (n : ℕ), p n) (n : ℕ) : n ≤ nat.find h ↔ ∀ m < n, ¬ p m :=
by simp_rw [← not_lt, find_lt_iff, not_exists]

@[simp] lemma lt_find_iff (h : ∃ n : ℕ, p n) (n : ℕ) : n < nat.find h ↔ ∀ m ≤ n, ¬ p m :=
by simp only [← succ_le_iff, le_find_iff, succ_le_succ_iff]

@[simp] lemma find_eq_zero (h : ∃ n : ℕ, p n) : nat.find h = 0 ↔ p 0 :=
by simp [find_eq_iff]

theorem find_mono (h : ∀ n, q n → p n) {hp : ∃ n, p n} {hq : ∃ n, q n} :
  nat.find hp ≤ nat.find hq :=
nat.find_min' _ (h _ (nat.find_spec hq))

lemma find_le {h : ∃ n, p n} (hn : p n) : nat.find h ≤ n :=
(nat.find_le_iff _ _).2 ⟨n, le_rfl, hn⟩

lemma find_comp_succ (h₁ : ∃ n, p n) (h₂ : ∃ n, p (n + 1)) (h0 : ¬ p 0) :
  nat.find h₁ = nat.find h₂ + 1 :=
begin
  refine (find_eq_iff _).2 ⟨nat.find_spec h₂, λ n hn, _⟩,
  cases n with n,
  exacts [h0, @nat.find_min (λ n, p (n + 1)) _ h₂ _ (succ_lt_succ_iff.1 hn)]
end

end find

/-! ### `find_greatest` -/
section find_greatest

/-- `find_greatest P b` is the largest `i ≤ bound` such that `P i` holds, or `0` if no such `i`
exists -/
protected def find_greatest (P : ℕ → Prop) [decidable_pred P] : ℕ → ℕ
| 0       := 0
| (n + 1) := if P (n + 1) then n + 1 else find_greatest n

variables {P Q : ℕ → Prop} [decidable_pred P] {b : ℕ}

@[simp] lemma find_greatest_zero : nat.find_greatest P 0 = 0 := rfl

lemma find_greatest_succ (n : ℕ) :
  nat.find_greatest P (n + 1) = if P (n + 1) then n + 1 else nat.find_greatest P n := rfl

@[simp] lemma find_greatest_eq : ∀ {b}, P b → nat.find_greatest P b = b
| 0       h := rfl
| (n + 1) h := by simp [nat.find_greatest, h]

@[simp] lemma find_greatest_of_not (h : ¬ P (b + 1)) :
  nat.find_greatest P (b + 1) = nat.find_greatest P b :=
by simp [nat.find_greatest, h]

end find_greatest

/-! ### decidability of predicates -/

instance decidable_ball_lt (n : nat) (P : Π k < n, Prop) :
  ∀ [H : ∀ n h, decidable (P n h)], decidable (∀ n h, P n h) :=
begin
  induction n with n IH; intro; resetI,
  { exact is_true (λ n, dec_trivial) },
  cases IH (λ k h, P k (lt_succ_of_lt h)) with h,
  { refine is_false (mt _ h), intros hn k h, apply hn },
  by_cases p : P n (lt_succ_self n),
  { exact is_true (λ k h',
     (le_of_lt_succ h').lt_or_eq_dec.elim (h _)
       (λ e, match k, e, h' with _, rfl, h := p end)) },
  { exact is_false (mt (λ hn, hn _ _) p) }
end

instance decidable_forall_fin {n : ℕ} (P : fin n → Prop)
  [H : decidable_pred P] : decidable (∀ i, P i) :=
decidable_of_iff (∀ k h, P ⟨k, h⟩) ⟨λ a ⟨k, h⟩, a k h, λ a k h, a ⟨k, h⟩⟩

instance decidable_ball_le (n : ℕ) (P : Π k ≤ n, Prop)
  [H : ∀ n h, decidable (P n h)] : decidable (∀ n h, P n h) :=
decidable_of_iff (∀ k (h : k < succ n), P k (le_of_lt_succ h))
⟨λ a k h, a k (lt_succ_of_le h), λ a k h, a k _⟩

instance decidable_exists_lt {P : ℕ → Prop} [h : decidable_pred P] :
  decidable_pred (λ n, ∃ (m : ℕ), m < n ∧ P m)
| 0 := is_false (by simp)
| (n + 1) := decidable_of_decidable_of_iff (@or.decidable _ _ (decidable_exists_lt n) (h n))
  (by simp only [lt_succ_iff_lt_or_eq, or_and_distrib_right, exists_or_distrib, exists_eq_left])

instance decidable_exists_le {P : ℕ → Prop} [h : decidable_pred P] :
  decidable_pred (λ n, ∃ (m : ℕ), m ≤ n ∧ P m) :=
λ n, decidable_of_iff (∃ m, m < n + 1 ∧ P m) (exists_congr (λ x, and_congr_left' lt_succ_iff))

end nat
