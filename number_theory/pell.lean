/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.int.basic data.nat.prime data.nat.modeq

/-- The ring of integers adjoined with a square root of `d`.
  These have the form `a + b √d` where `a b : ℤ`. The components
  are called `re` and `im` by analogy to the negative `d` case,
  but of course both parts are real here since `d` is nonnegative. -/
structure zsqrtd (d : ℕ) := mk {} ::
(re : ℤ)
(im : ℤ)

prefix `ℤ√`:100 := zsqrtd

namespace zsqrtd
section
  parameters {d : ℕ}

  instance : decidable_eq ℤ√d :=
  by tactic.mk_dec_eq_instance

  theorem ext : ∀ {z w : ℤ√d}, z = w ↔ z.re = w.re ∧ z.im = w.im
  | ⟨x, y⟩ ⟨x', y'⟩ := ⟨λ h, by injection h; split; assumption,
                        λ ⟨h₁, h₂⟩, by congr; assumption⟩

  /-- Convert an integer to a `ℤ√d` -/
  def of_int (n : ℤ) : ℤ√d := ⟨n, 0⟩
  @[simp] theorem of_int_re (n : ℤ) : (of_int n).re = n := rfl
  @[simp] theorem of_int_im (n : ℤ) : (of_int n).im = 0 := rfl

  /-- The zero of the ring -/
  def zero : ℤ√d := of_int 0
  instance : has_zero ℤ√d := ⟨zsqrtd.zero⟩
  @[simp] theorem zero_re : (0 : ℤ√d).re = 0 := rfl
  @[simp] theorem zero_im : (0 : ℤ√d).im = 0 := rfl

  /-- The one of the ring -/
  def one : ℤ√d := of_int 1
  instance : has_one ℤ√d := ⟨zsqrtd.one⟩
  @[simp] theorem one_re : (1 : ℤ√d).re = 1 := rfl
  @[simp] theorem one_im : (1 : ℤ√d).im = 0 := rfl

  /-- The representative of `√d` in the ring -/
  def sqrtd : ℤ√d := ⟨0, 1⟩
  @[simp] theorem sqrtd_re : (sqrtd : ℤ√d).re = 0 := rfl
  @[simp] theorem sqrtd_im : (sqrtd : ℤ√d).im = 1 := rfl

  /-- Addition of elements of `ℤ√d` -/
  def add : ℤ√d → ℤ√d → ℤ√d
  | ⟨x, y⟩ ⟨x', y'⟩ := ⟨x + x', y + y'⟩
  instance : has_add ℤ√d := ⟨zsqrtd.add⟩
  @[simp] theorem add_def (x y x' y' : ℤ) :
    (⟨x, y⟩ + ⟨x', y'⟩ : ℤ√d) = ⟨x + x', y + y'⟩ := rfl
  @[simp] theorem add_re : ∀ z w : ℤ√d, (z + w).re = z.re + w.re
  | ⟨x, y⟩ ⟨x', y'⟩ := rfl
  @[simp] theorem add_im : ∀ z w : ℤ√d, (z + w).im = z.im + w.im
  | ⟨x, y⟩ ⟨x', y'⟩ := rfl

  @[simp] theorem bit0_re (z) : (bit0 z : ℤ√d).re = bit0 z.re := add_re _ _
  @[simp] theorem bit0_im (z) : (bit0 z : ℤ√d).im = bit0 z.im := add_im _ _

  @[simp] theorem bit1_re (z) : (bit1 z : ℤ√d).re = bit1 z.re := by simp [bit1]
  @[simp] theorem bit1_im (z) : (bit1 z : ℤ√d).im = bit0 z.im := by simp [bit1]

  /-- Negation in `ℤ√d` -/
  def neg : ℤ√d → ℤ√d
  | ⟨x, y⟩ := ⟨-x, -y⟩
  instance : has_neg ℤ√d := ⟨zsqrtd.neg⟩
  @[simp] theorem neg_re : ∀ z : ℤ√d, (-z).re = -z.re
  | ⟨x, y⟩ := rfl
  @[simp] theorem neg_im : ∀ z : ℤ√d, (-z).im = -z.im
  | ⟨x, y⟩ := rfl

  /-- Conjugation in `ℤ√d`. The conjugate of `a + b √d` is `a - b √d`. -/
  def conj : ℤ√d → ℤ√d
  | ⟨x, y⟩ := ⟨x, -y⟩
  @[simp] theorem conj_re : ∀ z : ℤ√d, (conj z).re = z.re
  | ⟨x, y⟩ := rfl
  @[simp] theorem conj_im : ∀ z : ℤ√d, (conj z).im = -z.im
  | ⟨x, y⟩ := rfl

  /-- Multiplication in `ℤ√d` -/
  def mul : ℤ√d → ℤ√d → ℤ√d
  | ⟨x, y⟩ ⟨x', y'⟩ := ⟨x * x' + d * y * y', x * y' + y * x'⟩
  instance : has_mul ℤ√d := ⟨zsqrtd.mul⟩
  @[simp] theorem mul_re : ∀ z w : ℤ√d, (z * w).re = z.re * w.re + d * z.im * w.im
  | ⟨x, y⟩ ⟨x', y'⟩ := rfl
  @[simp] theorem mul_im : ∀ z w : ℤ√d, (z * w).im = z.re * w.im + z.im * w.re
  | ⟨x, y⟩ ⟨x', y'⟩ := rfl

  instance : comm_ring ℤ√d := by refine
  { add            := (+),
    zero           := 0,
    neg            := has_neg.neg,
    mul            := (*),
    one            := 1, ..};
  { intros, simp [ext, add_mul, mul_add, mul_comm, mul_left_comm] }

  instance : add_comm_monoid ℤ√d    := by apply_instance
  instance : add_monoid ℤ√d         := by apply_instance
  instance : monoid ℤ√d             := by apply_instance
  instance : comm_monoid ℤ√d        := by apply_instance
  instance : comm_semigroup ℤ√d     := by apply_instance
  instance : semigroup ℤ√d          := by apply_instance
  instance : add_comm_semigroup ℤ√d := by apply_instance
  instance : add_semigroup ℤ√d      := by apply_instance
  instance : comm_semiring ℤ√d      := by apply_instance
  instance : semiring ℤ√d           := by apply_instance
  instance : ring ℤ√d               := by apply_instance
  instance : distrib ℤ√d            := by apply_instance

  instance : zero_ne_one_class ℤ√d :=
  { zero := 0, one := 1, zero_ne_one := dec_trivial }

  @[simp] theorem coe_nat_re (n : ℕ) : (n : ℤ√d).re = n :=
  by induction n; simp *
  @[simp] theorem coe_nat_im (n : ℕ) : (n : ℤ√d).im = 0 :=
  by induction n; simp *
  theorem coe_nat_val (n : ℕ) : (n : ℤ√d) = ⟨n, 0⟩ :=
  by simp [ext]

  @[simp] theorem coe_int_re (n : ℤ) : (n : ℤ√d).re = n :=
  by cases n; simp [*, int.of_nat_eq_coe, int.neg_succ_of_nat_eq]
  @[simp] theorem coe_int_im (n : ℤ) : (n : ℤ√d).im = 0 :=
  by cases n; simp *
  theorem coe_int_val (n : ℤ) : (n : ℤ√d) = ⟨n, 0⟩ :=
  by simp [ext]

  @[simp] theorem of_int_eq_coe (n : ℤ) : (of_int n : ℤ√d) = n :=
  by simp [ext]

  @[simp] theorem smul_val (n x y : ℤ) : (n : ℤ√d) * ⟨x, y⟩ = ⟨n * x, n * y⟩ :=
  by simp [ext]

  @[simp] theorem muld_val (x y : ℤ) : sqrtd * ⟨x, y⟩ = ⟨d * y, x⟩ :=
  by simp [ext]

  @[simp] theorem smuld_val (n x y : ℤ) : sqrtd * (n : ℤ√d) * ⟨x, y⟩ = ⟨d * n * y, n * x⟩ :=
  by simp [ext]

  theorem decompose {x y : ℤ} : (⟨x, y⟩ : ℤ√d) = x + sqrtd * y :=
  by simp [ext]

  theorem mul_conj {x y : ℤ} : (⟨x, y⟩ * conj ⟨x, y⟩ : ℤ√d) = x * x - d * y * y :=
  by simp [ext, mul_comm]

  theorem conj_mul : Π {a b : ℤ√d}, conj (a * b) = conj a * conj b :=
  by simp [ext]

  protected lemma coe_int_add (m n : ℤ) : (↑(m + n) : ℤ√d) = ↑m + ↑n := by simp [ext]
  protected lemma coe_int_sub (m n : ℤ) : (↑(m - n) : ℤ√d) = ↑m - ↑n := by simp [ext]
  protected lemma coe_int_mul (m n : ℤ) : (↑(m * n) : ℤ√d) = ↑m * ↑n := by simp [ext]
  protected lemma coe_int_inj {m n : ℤ} (h : (↑m : ℤ√d) = ↑n) : m = n :=
  by simpa using congr_arg re h

  /-- Read `sq_le a c b d` as `a √c ≤ b √d` -/
  def sq_le (a c b d : ℕ) : Prop := c*a*a ≤ d*b*b

  theorem sq_le_of_le {c d x y z w : ℕ} (xz : z ≤ x) (yw : y ≤ w) (xy : sq_le x c y d) : sq_le z c w d :=
  le_trans (mul_le_mul (nat.mul_le_mul_left _ xz) xz (nat.zero_le _) (nat.zero_le _)) $
    le_trans xy (mul_le_mul (nat.mul_le_mul_left _ yw) yw (nat.zero_le _) (nat.zero_le _))

  theorem sq_le_add_mixed {c d x y z w : ℕ} (xy : sq_le x c y d) (zw : sq_le z c w d) :
    c * (x * z) ≤ d * (y * w) :=
  nat.mul_self_le_mul_self_iff.2 $
  by simpa [mul_comm, mul_left_comm] using
     mul_le_mul xy zw (nat.zero_le _) (nat.zero_le _)

  theorem sq_le_add {c d x y z w : ℕ} (xy : sq_le x c y d) (zw : sq_le z c w d) :
    sq_le (x + z) c (y + w) d :=
  begin
    have xz := sq_le_add_mixed xy zw,
    simp [sq_le, mul_assoc] at xy zw,
    simp [sq_le, mul_add, mul_comm, mul_left_comm, add_le_add, *]
  end

  theorem sq_le_cancel {c d x y z w : ℕ} (zw : sq_le y d x c) (h : sq_le (x + z) c (y + w) d) : sq_le z c w d :=
  begin
    apply le_of_not_gt,
    intro l,
    refine not_le_of_gt _ h,
    simp [sq_le, mul_add, mul_comm, mul_left_comm],
    have hm := sq_le_add_mixed zw (le_of_lt l),
    simp [sq_le, mul_assoc] at l zw,
    exact lt_of_le_of_lt (add_le_add_right zw _)
      (add_lt_add_left (add_lt_add_of_le_of_lt hm (add_lt_add_of_le_of_lt hm l)) _)
  end

  theorem sq_le_smul {c d x y : ℕ} (n : ℕ) (xy : sq_le x c y d) : sq_le (n * x) c (n * y) d :=
  by simpa [sq_le, mul_left_comm, mul_assoc] using
     nat.mul_le_mul_left (n * n) xy

  theorem sq_le_mul {d x y z w : ℕ} :
    (sq_le x 1 y d → sq_le z 1 w d → sq_le (x * w + y * z) d (x * z + d * y * w) 1) ∧
    (sq_le x 1 y d → sq_le w d z 1 → sq_le (x * z + d * y * w) 1 (x * w + y * z) d) ∧
    (sq_le y d x 1 → sq_le z 1 w d → sq_le (x * z + d * y * w) 1 (x * w + y * z) d) ∧
    (sq_le y d x 1 → sq_le w d z 1 → sq_le (x * w + y * z) d (x * z + d * y * w) 1) :=
  by refine ⟨_, _, _, _⟩; {
    intros xy zw,
    have := int.mul_nonneg (sub_nonneg_of_le (int.coe_nat_le_coe_nat_of_le xy))
                           (sub_nonneg_of_le (int.coe_nat_le_coe_nat_of_le zw)),
    refine int.le_of_coe_nat_le_coe_nat (le_of_sub_nonneg _),
    simpa [mul_add, mul_left_comm, mul_comm] }

  /-- "Generalized" `nonneg`. `nonnegg c d x y` means `a √c + b √d ≥ 0`;
    we are interested in the case `c = 1` but this is more symmetric -/
  def nonnegg (c d : ℕ) : ℤ → ℤ → Prop
  | (a : ℕ) (b : ℕ) := true
  | (a : ℕ) -[1+ b] := sq_le (b+1) c a d
  | -[1+ a] (b : ℕ) := sq_le (a+1) d b c
  | -[1+ a] -[1+ b] := false

  theorem nonnegg_comm {c d : ℕ} {x y : ℤ} : nonnegg c d x y = nonnegg d c y x :=
  by induction x; induction y; refl

  theorem nonnegg_neg_pos {c d} : Π {a b : ℕ}, nonnegg c d (-a) b ↔ sq_le a d b c
  | 0     b := ⟨by simp [sq_le, nat.zero_le], λa, trivial⟩
  | (a+1) b := by rw ← int.neg_succ_of_nat_coe; refl

  theorem nonnegg_pos_neg {c d} {a b : ℕ} : nonnegg c d a (-b) ↔ sq_le b c a d :=
  by rw nonnegg_comm; exact nonnegg_neg_pos

  theorem nonnegg_cases_right {c d} {a : ℕ} : Π {b : ℤ}, (Π x : ℕ, b = -x → sq_le x c a d) → nonnegg c d a b
  | (b:nat) h := trivial
  | -[1+ b] h := h (b+1) rfl

  theorem nonnegg_cases_left {c d} {b : ℕ} {a : ℤ} (h : Π x : ℕ, a = -x → sq_le x d b c) : nonnegg c d a b :=
  cast nonnegg_comm (nonnegg_cases_right h)

  /-- Nonnegativity of an element of `ℤ√d`. -/
  def nonneg : ℤ√d → Prop | ⟨a, b⟩ := nonnegg d 1 a b

  protected def le (a b : ℤ√d) : Prop := nonneg (b - a)

  instance : has_le ℤ√d := ⟨zsqrtd.le⟩

  protected def lt (a b : ℤ√d) : Prop := ¬(b ≤ a)

  instance : has_lt ℤ√d := ⟨zsqrtd.lt⟩

  instance decidable_nonnegg (c d a b) : decidable (nonnegg c d a b) :=
  by cases a; cases b; repeat {rw int.of_nat_eq_coe}; unfold nonnegg sq_le; apply_instance

  instance decidable_nonneg : Π (a : ℤ√d), decidable (nonneg a)
  | ⟨a, b⟩ := zsqrtd.decidable_nonnegg _ _ _ _

  instance decidable_le (a b : ℤ√d) : decidable (a ≤ b) := decidable_nonneg _

  theorem nonneg_cases : Π {a : ℤ√d}, nonneg a → ∃ x y : ℕ, a = ⟨x, y⟩ ∨ a = ⟨x, -y⟩ ∨ a = ⟨-x, y⟩
  | ⟨(x : ℕ), (y : ℕ)⟩ h := ⟨x, y, or.inl rfl⟩
  | ⟨(x : ℕ), -[1+ y]⟩ h := ⟨x, y+1, or.inr $ or.inl rfl⟩
  | ⟨-[1+ x], (y : ℕ)⟩ h := ⟨x+1, y, or.inr $ or.inr rfl⟩
  | ⟨-[1+ x], -[1+ y]⟩ h := false.elim h

  lemma nonneg_add_lem {x y z w : ℕ} (xy : nonneg ⟨x, -y⟩) (zw : nonneg ⟨-z, w⟩) : nonneg (⟨x, -y⟩ + ⟨-z, w⟩) :=
  have nonneg ⟨int.sub_nat_nat x z, int.sub_nat_nat w y⟩, from int.sub_nat_nat_elim x z
    (λm n i, sq_le y d m 1 → sq_le n 1 w d → nonneg ⟨i, int.sub_nat_nat w y⟩)
    (λj k, int.sub_nat_nat_elim w y
      (λm n i, sq_le n d (k + j) 1 → sq_le k 1 m d → nonneg ⟨int.of_nat j, i⟩)
      (λm n xy zw, trivial)
      (λm n xy zw, sq_le_cancel zw xy))
    (λj k, int.sub_nat_nat_elim w y
      (λm n i, sq_le n d k 1 → sq_le (k + j + 1) 1 m d → nonneg ⟨-[1+ j], i⟩)
      (λm n xy zw, sq_le_cancel xy zw)
      (λm n xy zw, let t := nat.le_trans zw (sq_le_of_le (nat.le_add_right n (m+1)) (le_refl _) xy) in
        have k + j + 1 ≤ k, from nat.mul_self_le_mul_self_iff.2 (by repeat{rw one_mul at t}; exact t),
        absurd this (not_le_of_gt $ nat.succ_le_succ $ nat.le_add_right _ _))) (nonnegg_pos_neg.1 xy) (nonnegg_neg_pos.1 zw),
  show nonneg ⟨_, _⟩, by rw [neg_add_eq_sub]; rwa [int.sub_nat_nat_eq_coe,int.sub_nat_nat_eq_coe] at this

  theorem nonneg_add {a b : ℤ√d} (ha : nonneg a) (hb : nonneg b) : nonneg (a + b) :=
  begin
    rcases nonneg_cases ha with ⟨x, y, rfl|rfl|rfl⟩;
    rcases nonneg_cases hb with ⟨z, w, rfl|rfl|rfl⟩; dsimp [add, nonneg] at ha hb ⊢,
    { trivial },
    { refine nonnegg_cases_right (λi h, sq_le_of_le _ _ (nonnegg_pos_neg.1 hb)),
      { exact int.coe_nat_le.1 (le_of_neg_le_neg (@int.le.intro _ _ y (by simp *))) },
      { apply nat.le_add_left } },
    { refine nonnegg_cases_left (λi h, sq_le_of_le _ _ (nonnegg_neg_pos.1 hb)),
      { exact int.coe_nat_le.1 (le_of_neg_le_neg (@int.le.intro _ _ x (by simp *))) },
      { apply nat.le_add_left } },
    { refine nonnegg_cases_right (λi h, sq_le_of_le _ _ (nonnegg_pos_neg.1 ha)),
      { exact int.coe_nat_le.1 (le_of_neg_le_neg (@int.le.intro _ _ w (by simp *))) },
      { apply nat.le_add_right } },
    { simpa using nonnegg_pos_neg.2 (sq_le_add (nonnegg_pos_neg.1 ha) (nonnegg_pos_neg.1 hb)) },
    { exact nonneg_add_lem ha hb },
    { refine nonnegg_cases_left (λi h, sq_le_of_le _ _ (nonnegg_neg_pos.1 ha)),
      { exact int.coe_nat_le.1 (le_of_neg_le_neg (@int.le.intro _ _ z (by simp *))) },
      { apply nat.le_add_right } },
    { rw [add_comm, add_comm ↑y], exact nonneg_add_lem hb ha },
    { simpa using nonnegg_neg_pos.2 (sq_le_add (nonnegg_neg_pos.1 ha) (nonnegg_neg_pos.1 hb)) },
  end

  theorem le_refl (a : ℤ√d) : a ≤ a := show nonneg (a - a), by simp

  protected theorem le_trans {a b c : ℤ√d} (ab : a ≤ b) (bc : b ≤ c) : a ≤ c :=
  have nonneg (b - a + (c - b)), from nonneg_add ab bc,
  have nonneg (c - a + (b - b)), by simpa [-add_right_neg, add_left_comm],
  by simpa

  theorem nonneg_iff_zero_le {a : ℤ√d} : nonneg a ↔ 0 ≤ a := show _ ↔ nonneg _, by simp

  theorem le_of_le_le {x y z w : ℤ} (xz : x ≤ z) (yw : y ≤ w) : (⟨x, y⟩ : ℤ√d) ≤ ⟨z, w⟩ :=
  show nonneg ⟨z - x, w - y⟩, from
  match z - x, w - y, int.le.dest_sub xz, int.le.dest_sub yw with ._, ._, ⟨a, rfl⟩, ⟨b, rfl⟩ := trivial end

  theorem le_arch (a : ℤ√d) : ∃n : ℕ, a ≤ n :=
  let ⟨x, y, (h : a ≤ ⟨x, y⟩)⟩ := show ∃x y : ℕ, nonneg (⟨x, y⟩ + -a), from match -a with
  | ⟨int.of_nat x, int.of_nat y⟩ := ⟨0, 0, trivial⟩
  | ⟨int.of_nat x, -[1+ y]⟩      := ⟨0, y+1, by simp [int.neg_succ_of_nat_coe]⟩
  | ⟨-[1+ x],      int.of_nat y⟩ := ⟨x+1, 0, by simp [int.neg_succ_of_nat_coe]⟩
  | ⟨-[1+ x],      -[1+ y]⟩      := ⟨x+1, y+1, by simp [int.neg_succ_of_nat_coe]⟩
  end in begin
    refine ⟨x + d*y, zsqrtd.le_trans h _⟩,
    rw [← int.cast_coe_nat, ← of_int_eq_coe],
    change nonneg ⟨(↑x + d*y) - ↑x, 0-↑y⟩,
    cases y with y,
    { simp },
    have h : ∀y, sq_le y d (d * y) 1 := λ y,
      by simpa [sq_le, mul_comm, mul_left_comm] using
         nat.mul_le_mul_right (y * y) (nat.le_mul_self d),
    rw [show (x:ℤ) + d * nat.succ y - x = d * nat.succ y, by simp],
    exact h (y+1)
  end

  protected theorem nonneg_total : Π (a : ℤ√d), nonneg a ∨ nonneg (-a)
  | ⟨(x : ℕ), (y : ℕ)⟩ := or.inl trivial
  | ⟨-[1+ x], -[1+ y]⟩ := or.inr trivial
  | ⟨0,       -[1+ y]⟩ := or.inr trivial
  | ⟨-[1+ x], 0⟩       := or.inr trivial
  | ⟨(x+1:ℕ), -[1+ y]⟩ := nat.le_total
  | ⟨-[1+ x], (y+1:ℕ)⟩ := nat.le_total

  protected theorem le_total (a b : ℤ√d) : a ≤ b ∨ b ≤ a :=
  let t := nonneg_total (b - a) in by rw [show -(b-a) = a-b, from neg_sub b a] at t; exact t

  instance : preorder ℤ√d :=
  { le               := zsqrtd.le,
    le_refl          := zsqrtd.le_refl,
    le_trans         := @zsqrtd.le_trans,
    lt               := zsqrtd.lt,
    lt_iff_le_not_le := λ a b,
      (and_iff_right_of_imp (zsqrtd.le_total _ _).resolve_left).symm }

  protected theorem add_le_add_left (a b : ℤ√d) (ab : a ≤ b) (c : ℤ√d) : c + a ≤ c + b :=
  show nonneg _, by rw add_sub_add_left_eq_sub; exact ab

  protected theorem le_of_add_le_add_left (a b c : ℤ√d) (h : c + a ≤ c + b) : a ≤ b :=
  by simpa using zsqrtd.add_le_add_left _ _ h (-c)

  protected theorem add_lt_add_left (a b : ℤ√d) (h : a < b) (c) : c + a < c + b :=
  λ h', h (zsqrtd.le_of_add_le_add_left _ _ _ h')

  theorem nonneg_smul {a : ℤ√d} {n : ℕ} (ha : nonneg a) : nonneg (n * a) :=
  by rw ← int.cast_coe_nat; exact match a, nonneg_cases ha, ha with
  | ._, ⟨x, y, or.inl rfl⟩,          ha := by rw smul_val; trivial
  | ._, ⟨x, y, or.inr $ or.inl rfl⟩, ha := by rw smul_val; simpa using
    nonnegg_pos_neg.2 (sq_le_smul n $ nonnegg_pos_neg.1 ha)
  | ._, ⟨x, y, or.inr $ or.inr rfl⟩, ha := by rw smul_val; simpa using
    nonnegg_neg_pos.2 (sq_le_smul n $ nonnegg_neg_pos.1 ha)
  end

  theorem nonneg_muld {a : ℤ√d} (ha : nonneg a) : nonneg (sqrtd * a) :=
  by refine match a, nonneg_cases ha, ha with
  | ._, ⟨x, y, or.inl rfl⟩,          ha := trivial
  | ._, ⟨x, y, or.inr $ or.inl rfl⟩, ha := by simp; apply nonnegg_neg_pos.2;
    simpa [sq_le, mul_comm, mul_left_comm] using
      nat.mul_le_mul_left d (nonnegg_pos_neg.1 ha)
  | ._, ⟨x, y, or.inr $ or.inr rfl⟩, ha := by simp; apply nonnegg_pos_neg.2;
    simpa [sq_le, mul_comm, mul_left_comm] using
      nat.mul_le_mul_left d (nonnegg_neg_pos.1 ha)
  end

  theorem nonneg_mul_lem {x y : ℕ} {a : ℤ√d} (ha : nonneg a) : nonneg (⟨x, y⟩ * a) :=
  have (⟨x, y⟩ * a : ℤ√d) = x * a + sqrtd * (y * a), by rw [decompose, right_distrib, mul_assoc]; refl,
  by rw this; exact nonneg_add (nonneg_smul ha) (nonneg_muld $ nonneg_smul ha)

  theorem nonneg_mul {a b : ℤ√d} (ha : nonneg a) (hb : nonneg b) : nonneg (a * b) :=
  match a, b, nonneg_cases ha, nonneg_cases hb, ha, hb with
  | ._, ._, ⟨x, y, or.inl rfl⟩,          ⟨z, w, or.inl rfl⟩,          ha, hb := trivial
  | ._, ._, ⟨x, y, or.inl rfl⟩,          ⟨z, w, or.inr $ or.inr rfl⟩, ha, hb := nonneg_mul_lem hb
  | ._, ._, ⟨x, y, or.inl rfl⟩,          ⟨z, w, or.inr $ or.inl rfl⟩, ha, hb := nonneg_mul_lem hb
  | ._, ._, ⟨x, y, or.inr $ or.inr rfl⟩, ⟨z, w, or.inl rfl⟩,          ha, hb := by rw mul_comm; exact nonneg_mul_lem ha
  | ._, ._, ⟨x, y, or.inr $ or.inl rfl⟩, ⟨z, w, or.inl rfl⟩,          ha, hb := by rw mul_comm; exact nonneg_mul_lem ha
  | ._, ._, ⟨x, y, or.inr $ or.inr rfl⟩, ⟨z, w, or.inr $ or.inr rfl⟩, ha, hb :=
    by rw [calc (⟨-x, y⟩ * ⟨-z, w⟩ : ℤ√d) = ⟨_, _⟩ : rfl
        ... = ⟨x * z + d * y * w, -(x * w + y * z)⟩ : by simp]; exact
    nonnegg_pos_neg.2 (sq_le_mul.left (nonnegg_neg_pos.1 ha) (nonnegg_neg_pos.1 hb))
  | ._, ._, ⟨x, y, or.inr $ or.inr rfl⟩, ⟨z, w, or.inr $ or.inl rfl⟩, ha, hb :=
    by rw [calc (⟨-x, y⟩ * ⟨z, -w⟩ : ℤ√d) = ⟨_, _⟩ : rfl
        ... = ⟨-(x * z + d * y * w), x * w + y * z⟩ : by simp]; exact
    nonnegg_neg_pos.2 (sq_le_mul.right.left (nonnegg_neg_pos.1 ha) (nonnegg_pos_neg.1 hb))
  | ._, ._, ⟨x, y, or.inr $ or.inl rfl⟩, ⟨z, w, or.inr $ or.inr rfl⟩, ha, hb :=
    by rw [calc (⟨x, -y⟩ * ⟨-z, w⟩ : ℤ√d) = ⟨_, _⟩ : rfl
        ... = ⟨-(x * z + d * y * w), x * w + y * z⟩ : by simp]; exact
    nonnegg_neg_pos.2 (sq_le_mul.right.right.left (nonnegg_pos_neg.1 ha) (nonnegg_neg_pos.1 hb))
  | ._, ._, ⟨x, y, or.inr $ or.inl rfl⟩, ⟨z, w, or.inr $ or.inl rfl⟩, ha, hb :=
    by rw [calc (⟨x, -y⟩ * ⟨z, -w⟩ : ℤ√d) = ⟨_, _⟩ : rfl
        ... = ⟨x * z + d * y * w, -(x * w + y * z)⟩ : by simp]; exact
    nonnegg_pos_neg.2 (sq_le_mul.right.right.right (nonnegg_pos_neg.1 ha) (nonnegg_pos_neg.1 hb))
  end

  protected theorem mul_nonneg (a b : ℤ√d) : 0 ≤ a → 0 ≤ b → 0 ≤ a * b :=
  by repeat {rw ← nonneg_iff_zero_le}; exact nonneg_mul

  theorem not_sq_le_succ (c d y) (h : c > 0) : ¬sq_le (y + 1) c 0 d :=
  not_le_of_gt $ mul_pos (mul_pos h $ nat.succ_pos _) $ nat.succ_pos _

  /-- A nonsquare is a natural number that is not equal to the square of an
    integer. This is implemented as a typeclass because it's a necessary condition
    for much of the Pell equation theory. -/
  class nonsquare (x : ℕ) : Prop := (ns : ∀n : ℕ, x ≠ n*n)

  parameter [dnsq : nonsquare d]
  include dnsq

  theorem d_pos : 0 < d := lt_of_le_of_ne (nat.zero_le _) $ ne.symm $ (nonsquare.ns d 0)

  theorem divides_sq_eq_zero {x y} (h : x * x = d * y * y) : x = 0 ∧ y = 0 :=
  let g := x.gcd y in or.elim g.eq_zero_or_pos
    (λH, ⟨nat.eq_zero_of_gcd_eq_zero_left H, nat.eq_zero_of_gcd_eq_zero_right H⟩)
    (λgpos, false.elim $
      let ⟨m, n, co, (hx : x = m * g), (hy : y = n * g)⟩ := nat.exists_coprime gpos in
      begin
        rw [hx, hy] at h,
        have : m * m = d * (n * n) := nat.eq_of_mul_eq_mul_left (mul_pos gpos gpos)
          (by simpa [mul_comm, mul_left_comm] using h),
        have co2 := let co1 := co.mul_right co in co1.mul co1,
        exact nonsquare.ns d m (nat.dvd_antisymm (by rw this; apply dvd_mul_right) $
          co2.dvd_of_dvd_mul_right $ by simp [this])
      end)

  theorem divides_sq_eq_zero_z {x y : ℤ} (h : x * x = d * y * y) : x = 0 ∧ y = 0 :=
  by rw [mul_assoc, ← int.nat_abs_mul_self, ← int.nat_abs_mul_self, ← int.coe_nat_mul, ← mul_assoc] at h;
  exact let ⟨h1, h2⟩ := divides_sq_eq_zero (int.coe_nat_inj h) in
  ⟨int.eq_zero_of_nat_abs_eq_zero h1, int.eq_zero_of_nat_abs_eq_zero h2⟩

  theorem not_divides_square (x y) : (x + 1) * (x + 1) ≠ d * (y + 1) * (y + 1) :=
  λe, by have t := (divides_sq_eq_zero e).left; contradiction

  theorem nonneg_antisymm : Π {a : ℤ√d}, nonneg a → nonneg (-a) → a = 0
  | ⟨0,         0⟩         xy yx := rfl
  | ⟨-[1+ x],   -[1+ y]⟩   xy yx := false.elim xy
  | ⟨(x+1:nat), (y+1:nat)⟩ xy yx := false.elim yx
  | ⟨-[1+ x],   0⟩         xy yx := absurd xy (not_sq_le_succ _ _ _ dec_trivial)
  | ⟨(x+1:nat), 0⟩         xy yx := absurd yx (not_sq_le_succ _ _ _ dec_trivial)
  | ⟨0,         -[1+ y]⟩   xy yx := absurd xy (not_sq_le_succ _ _ _ d_pos)
  | ⟨0,         (y+1:nat)⟩ _  yx := absurd yx (not_sq_le_succ _ _ _ d_pos)
  | ⟨(x+1:nat), -[1+ y]⟩   (xy : sq_le _ _ _ _) (yx : sq_le _ _ _ _) :=
    let t := le_antisymm yx xy in by rw[one_mul] at t; exact absurd t (not_divides_square _ _)
  | ⟨-[1+ x],   (y+1:nat)⟩ (xy : sq_le _ _ _ _) (yx : sq_le _ _ _ _) :=
    let t := le_antisymm xy yx in by rw[one_mul] at t; exact absurd t (not_divides_square _ _)

  theorem le_antisymm {a b : ℤ√d} (ab : a ≤ b) (ba : b ≤ a) : a = b :=
  eq_of_sub_eq_zero $ nonneg_antisymm ba (by rw neg_sub; exact ab)

  instance : decidable_linear_order ℤ√d :=
  { le_antisymm     := @zsqrtd.le_antisymm,
    le_total        := zsqrtd.le_total,
    decidable_le    := zsqrtd.decidable_le,
    ..zsqrtd.preorder }

  protected theorem eq_zero_or_eq_zero_of_mul_eq_zero : Π {a b : ℤ√d}, a * b = 0 → a = 0 ∨ b = 0
  | ⟨x, y⟩ ⟨z, w⟩ h := by injection h with h1 h2; exact
    have h1 : x*z = -(d*y*w), from eq_neg_of_add_eq_zero h1,
    have h2 : x*w = -(y*z), from eq_neg_of_add_eq_zero h2,
    have fin : x*x = d*y*y → (⟨x, y⟩:ℤ√d) = 0, from
    λe, match x, y, divides_sq_eq_zero_z e with ._, ._, ⟨rfl, rfl⟩ := rfl end,
    if z0 : z = 0 then if w0 : w = 0 then
      or.inr (match z, w, z0, w0 with ._, ._, rfl, rfl := rfl end)
    else
       or.inl $ fin $ eq_of_mul_eq_mul_right w0 $ calc
         x * x * w = -y * (x * z) : by simp [h2, mul_assoc, mul_left_comm]
               ... = d * y * y * w : by simp [h1, mul_assoc, mul_left_comm]
    else
       or.inl $ fin $ eq_of_mul_eq_mul_right z0 $ calc
         x * x * z = d * -y * (x * w) : by simp [h1, mul_assoc, mul_left_comm]
               ... = d * y * y * z : by simp [h2, mul_assoc, mul_left_comm]

  instance : integral_domain ℤ√d :=
  { zero_ne_one := zero_ne_one,
    eq_zero_or_eq_zero_of_mul_eq_zero := @zsqrtd.eq_zero_or_eq_zero_of_mul_eq_zero,
    ..zsqrtd.comm_ring }

  protected theorem mul_pos (a b : ℤ√d) (a0 : 0 < a) (b0 : 0 < b) : 0 < a * b := λab,
  or.elim (eq_zero_or_eq_zero_of_mul_eq_zero (le_antisymm ab (mul_nonneg _ _ (le_of_lt a0) (le_of_lt b0))))
    (λe, ne_of_gt a0 e)
    (λe, ne_of_gt b0 e)

  instance : decidable_linear_ordered_comm_ring ℤ√d :=
  { add_le_add_left := @zsqrtd.add_le_add_left,
    add_lt_add_left := @zsqrtd.add_lt_add_left,
    zero_ne_one     := zero_ne_one,
    mul_nonneg      := @zsqrtd.mul_nonneg,
    mul_pos         := @zsqrtd.mul_pos,
    zero_lt_one     := dec_trivial,
    ..zsqrtd.comm_ring, ..zsqrtd.decidable_linear_order }

  instance : decidable_linear_ordered_semiring ℤ√d := by apply_instance
  instance : linear_ordered_semiring ℤ√d           := by apply_instance
  instance : ordered_semiring ℤ√d                  := by apply_instance

end
end zsqrtd

namespace pell
open nat

section
  parameters {a : ℕ} (a1 : a > 1)

  include a1
  private def d := a*a - 1

  @[simp] theorem d_pos : 0 < d := nat.sub_pos_of_lt (mul_lt_mul a1 (le_of_lt a1) dec_trivial dec_trivial : 1*1<a*a)

  /-- The Pell sequences, defined together in mutual recursion. -/
  def pell : ℕ → ℕ × ℕ :=
  λn, nat.rec_on n (1, 0) (λn xy, (xy.1*a + d*xy.2, xy.1 + xy.2*a))

  /-- The Pell `x` sequence. -/
  def xn (n : ℕ) : ℕ := (pell n).1
  /-- The Pell `y` sequence. -/
  def yn (n : ℕ) : ℕ := (pell n).2

  @[simp] theorem pell_val (n : ℕ) : pell n = (xn n, yn n) :=
  show pell n = ((pell n).1, (pell n).2), from match pell n with (a, b) := rfl end

  @[simp] theorem xn_zero : xn 0 = 1 := rfl
  @[simp] theorem yn_zero : yn 0 = 0 := rfl

  @[simp] theorem xn_succ (n : ℕ) : xn (n+1) = xn n * a + d * yn n := rfl
  @[simp] theorem yn_succ (n : ℕ) : yn (n+1) = xn n + yn n * a := rfl

  @[simp] theorem xn_one : xn 1 = a := by simp
  @[simp] theorem yn_one : yn 1 = 1 := by simp

  def xz (n : ℕ) : ℤ := xn n
  def yz (n : ℕ) : ℤ := yn n
  def az : ℤ := a

  theorem asq_pos : 0 < a*a :=
  le_trans (le_of_lt a1) (by have := @nat.mul_le_mul_left 1 a a (le_of_lt a1); rwa mul_one at this)

  theorem dz_val : ↑d = az*az - 1 :=
  have 1 ≤ a*a, from asq_pos,
  show ↑(a*a - 1) = _, by rw int.coe_nat_sub this; refl

  @[simp] theorem xz_succ (n : ℕ) : xz (n+1) = xz n * az + ↑d * yz n := rfl
  @[simp] theorem yz_succ (n : ℕ) : yz (n+1) = xz n + yz n * az := rfl

  /-- The Pell sequence can also be viewed as an element of `ℤ√d` -/
  def pell_zd (n : ℕ) : ℤ√d := ⟨xn n, yn n⟩
  @[simp] theorem pell_zd_re (n : ℕ) : (pell_zd n).re = xn n := rfl
  @[simp] theorem pell_zd_im (n : ℕ) : (pell_zd n).im = yn n := rfl

  /-- The property of being a solution to the Pell equation, expressed
    as a property of elements of `ℤ√d`. -/
  def is_pell : ℤ√d → Prop | ⟨x, y⟩ := x*x - d*y*y = 1

  theorem is_pell_nat {x y : ℕ} : is_pell ⟨x, y⟩ ↔ x*x - d*y*y = 1 :=
  ⟨λh, int.coe_nat_inj (by rw int.coe_nat_sub (int.le_of_coe_nat_le_coe_nat $ int.le.intro_sub h); exact h),
  λh, show ((x*x : ℕ) - (d*y*y:ℕ) : ℤ) = 1, by rw [← int.coe_nat_sub $ le_of_lt $ nat.lt_of_sub_eq_succ h, h]; refl⟩

  theorem is_pell_norm : Π {b : ℤ√d}, is_pell b ↔ b * b.conj = 1
  | ⟨x, y⟩ := by simp [zsqrtd.ext, is_pell, mul_comm]

  theorem is_pell_mul {b c : ℤ√d} (hb : is_pell b) (hc : is_pell c) : is_pell (b * c) :=
  is_pell_norm.2 (by simp [mul_comm, mul_left_comm,
    zsqrtd.conj_mul, pell.is_pell_norm.1 hb, pell.is_pell_norm.1 hc])

  theorem is_pell_conj : ∀ {b : ℤ√d}, is_pell b ↔ is_pell b.conj | ⟨x, y⟩ :=
  by simp [is_pell, zsqrtd.conj]

  @[simp] theorem pell_zd_succ (n : ℕ) : pell_zd (n+1) = pell_zd n * ⟨a, 1⟩ :=
  by simp [zsqrtd.ext]

  theorem is_pell_one : is_pell ⟨a, 1⟩ :=
  show az*az-d*1*1=1, by simp [dz_val]

  theorem is_pell_pell_zd : ∀ (n : ℕ), is_pell (pell_zd n)
  | 0     := rfl
  | (n+1) := let o := is_pell_one in by simp; exact pell.is_pell_mul (is_pell_pell_zd n) o

  @[simp] theorem pell_eqz (n : ℕ) : xz n * xz n - d * yz n * yz n = 1 := is_pell_pell_zd n

  @[simp] theorem pell_eq (n : ℕ) : xn n * xn n - d * yn n * yn n = 1 :=
  let pn := pell_eqz n in
  have h : (↑(xn n * xn n) : ℤ) - ↑(d * yn n * yn n) = 1,
    by repeat {rw int.coe_nat_mul}; exact pn,
  have hl : d * yn n * yn n ≤ xn n * xn n, from
    int.le_of_coe_nat_le_coe_nat $ int.le.intro $ add_eq_of_eq_sub' $ eq.symm h,
  int.coe_nat_inj (by rw int.coe_nat_sub hl; exact h)

  instance dnsq : zsqrtd.nonsquare d := ⟨λn h,
    have n*n + 1 = a*a, by rw ← h; exact nat.succ_pred_eq_of_pos (asq_pos a1),
    have na : n < a, from nat.mul_self_lt_mul_self_iff.2 (by rw ← this; exact nat.lt_succ_self _),
    have (n+1)*(n+1) ≤ n*n + 1, by rw this; exact nat.mul_self_le_mul_self na,
    have n+n ≤ 0, from @nat.le_of_add_le_add_right (n*n + 1) _ _ (by simpa [mul_add, mul_comm, mul_left_comm]),
    ne_of_gt d_pos $ by rw nat.eq_zero_of_le_zero (le_trans (nat.le_add_left _ _) this) at h; exact h⟩

  theorem xn_ge_a_pow : ∀ (n : ℕ), a^n ≤ xn n
  | 0     := le_refl 1
  | (n+1) := by simp [nat.pow_succ]; exact le_trans
    (nat.mul_le_mul_right _ (xn_ge_a_pow n)) (nat.le_add_right _ _)

  theorem n_lt_a_pow : ∀ (n : ℕ), n < a^n
  | 0     := nat.le_refl 1
  | (n+1) := begin have IH := n_lt_a_pow n,
    have : a^n + a^n ≤ a^n * a,
    { rw ← mul_two, exact nat.mul_le_mul_left _ a1 },
    simp [nat.pow_succ], refine lt_of_lt_of_le _ this,
    exact add_lt_add_of_lt_of_le IH (lt_of_le_of_lt (nat.zero_le _) IH)
  end

  theorem n_lt_xn (n) : n < xn n :=
  lt_of_lt_of_le (n_lt_a_pow n) (xn_ge_a_pow n)

  theorem x_pos (n) : xn n > 0 :=
  lt_of_le_of_lt (nat.zero_le n) (n_lt_xn n)

  lemma eq_pell_lem : ∀n (b:ℤ√d), 1 ≤ b → is_pell b → pell_zd n ≥ b → ∃n, b = pell_zd n
  | 0     b := λh1 hp hl, ⟨0, @zsqrtd.le_antisymm _ dnsq _ _ hl h1⟩
  | (n+1) b := λh1 hp h,
    have a1p : (0:ℤ√d) ≤ ⟨a, 1⟩, from trivial,
    have am1p : (0:ℤ√d) ≤ ⟨a, -1⟩, from show (_:nat) ≤ _, by simp; exact nat.pred_le _,
    have a1m : (⟨a, 1⟩ * ⟨a, -1⟩ : ℤ√d) = 1, from is_pell_norm.1 is_pell_one,
    if ha : b ≥ ⟨↑a, 1⟩ then
      let ⟨m, e⟩ := eq_pell_lem n (b * ⟨a, -1⟩)
        (by rw ← a1m; exact mul_le_mul_of_nonneg_right ha am1p)
        (is_pell_mul hp (is_pell_conj.1 is_pell_one))
        (by have t := mul_le_mul_of_nonneg_right h am1p; rwa [pell_zd_succ, mul_assoc, a1m, mul_one] at t) in
      ⟨m+1, by rw [show b = b * ⟨a, -1⟩ * ⟨a, 1⟩, by rw [mul_assoc, eq.trans (mul_comm _ _) a1m]; simp, pell_zd_succ, e]⟩
    else
      suffices ¬1 < b, from ⟨0, show b = 1, from (or.resolve_left (lt_or_eq_of_le h1) this).symm⟩, λh1l,
      by cases b with x y; exact
      have bm : (_*⟨_,_⟩ :ℤ√(d a1)) = 1, from pell.is_pell_norm.1 hp,
      have y0l : (0:ℤ√(d a1)) < ⟨x - x, y - -y⟩, from sub_lt_sub h1l $ λ(hn : (1:ℤ√(d a1)) ≤ ⟨x, -y⟩),
        by have t := mul_le_mul_of_nonneg_left hn (le_trans zero_le_one h1); rw [bm, mul_one] at t; exact h1l t,
      have yl2 : (⟨_, _⟩ : ℤ√_) < ⟨_, _⟩, from
        show (⟨x, y⟩ - ⟨x, -y⟩ : ℤ√(d a1)) < ⟨a, 1⟩ - ⟨a, -1⟩, from
        sub_lt_sub (by exact ha) $ λ(hn : (⟨x, -y⟩ : ℤ√(d a1)) ≤ ⟨a, -1⟩),
        by have t := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn (le_trans zero_le_one h1)) a1p;
           rw [bm, one_mul, mul_assoc, eq.trans (mul_comm _ _) a1m, mul_one] at t; exact ha t,
      by simp at y0l; simp at yl2; exact
      match y, y0l, (yl2 : (⟨_, _⟩ : ℤ√_) < ⟨_, _⟩) with
      | 0, y0l, yl2 := y0l (le_refl 0)
      | (y+1 : ℕ), y0l, yl2 := yl2 (zsqrtd.le_of_le_le (le_refl 0)
          (let t := int.coe_nat_le_coe_nat_of_le (nat.succ_pos y) in add_le_add t t))
      | -[1+y], y0l, yl2 := y0l trivial
      end

  theorem eq_pell_zd (b : ℤ√d) (b1 : 1 ≤ b) (hp : is_pell b) : ∃n, b = pell_zd n :=
  let ⟨n, h⟩ := @zsqrtd.le_arch d b in
  eq_pell_lem n b b1 hp $ zsqrtd.le_trans h $ by rw zsqrtd.coe_nat_val; exact
  zsqrtd.le_of_le_le
    (int.coe_nat_le_coe_nat_of_le $ le_of_lt $ n_lt_xn _ _) (int.coe_zero_le _)

  theorem eq_pell {x y : ℕ} (hp : x*x - d*y*y = 1) : ∃n, x = xn n ∧ y = yn n :=
  have (1:ℤ√d) ≤ ⟨x, y⟩, from match x, hp with
  | 0,    (hp : 0 - _ = 1) := by rw nat.zero_sub at hp; contradiction
  | (x+1), hp := zsqrtd.le_of_le_le (int.coe_nat_le_coe_nat_of_le $ nat.succ_pos x) (int.coe_zero_le _)
  end,
  let ⟨m, e⟩ := eq_pell_zd ⟨x, y⟩ this (is_pell_nat.2 hp) in
  ⟨m, match x, y, e with ._, ._, rfl := ⟨rfl, rfl⟩ end⟩

  theorem pell_zd_add (m) : ∀ n, pell_zd (m + n) = pell_zd m * pell_zd n
  | 0     := (mul_one _).symm
  | (n+1) := by rw[← add_assoc, pell_zd_succ, pell_zd_succ, pell_zd_add n, ← mul_assoc]

  theorem xn_add (m n) : xn (m + n) = xn m * xn n + d * yn m * yn n :=
  by injection (pell_zd_add _ m n) with h _;
     repeat {rw ← int.coe_nat_add at h <|> rw ← int.coe_nat_mul at h};
     exact int.coe_nat_inj h

  theorem yn_add (m n) : yn (m + n) = xn m * yn n + yn m * xn n :=
  by injection (pell_zd_add _ m n) with _ h;
     repeat {rw ← int.coe_nat_add at h <|> rw ← int.coe_nat_mul at h};
     exact int.coe_nat_inj h

  theorem pell_zd_sub {m n} (h : n ≤ m) : pell_zd (m - n) = pell_zd m * (pell_zd n).conj :=
  let t := pell_zd_add n (m - n) in
  by rw [nat.add_sub_of_le h] at t;
     rw [t, mul_comm (pell_zd _ n) _, mul_assoc, (is_pell_norm _).1 (is_pell_pell_zd _ _), mul_one]

  theorem xz_sub {m n} (h : n ≤ m) : xz (m - n) = xz m * xz n - d * yz m * yz n :=
  by injection (pell_zd_sub _ h) with h _; repeat {rw ← neg_mul_eq_mul_neg at h}; exact h

  theorem yz_sub {m n} (h : n ≤ m) : yz (m - n) = xz n * yz m - xz m * yz n :=
  by injection (pell_zd_sub a1 h) with _ h; repeat {rw ← neg_mul_eq_mul_neg at h}; rw [add_comm, mul_comm] at h; exact h

  theorem xy_coprime (n) : (xn n).coprime (yn n) :=
  nat.coprime_of_dvd' $ λk kx ky,
  let p := pell_eq n in by rw ← p; exact
  nat.dvd_sub (le_of_lt $ nat.lt_of_sub_eq_succ p)
    (dvd_mul_of_dvd_right kx _) (dvd_mul_of_dvd_right ky _)

  theorem y_increasing {m} : Π {n}, m < n → yn m < yn n
  | 0     h := absurd h $ nat.not_lt_zero _
  | (n+1) h :=
    have yn m ≤ yn n, from or.elim (lt_or_eq_of_le $ nat.le_of_succ_le_succ h)
      (λhl, le_of_lt $ y_increasing hl) (λe, by rw e),
    by simp; refine lt_of_le_of_lt _ (nat.lt_add_of_pos_left $ x_pos a1 n);
       rw ← mul_one (yn a1 m);
       exact mul_le_mul this (le_of_lt a1) (nat.zero_le _) (nat.zero_le _)

  theorem x_increasing {m} : Π {n}, m < n → xn m < xn n
  | 0     h := absurd h $ nat.not_lt_zero _
  | (n+1) h :=
    have xn m ≤ xn n, from or.elim (lt_or_eq_of_le $ nat.le_of_succ_le_succ h)
      (λhl, le_of_lt $ x_increasing hl) (λe, by rw e),
    by simp; refine lt_of_lt_of_le (lt_of_le_of_lt this _) (nat.le_add_right _ _);
       have t := nat.mul_lt_mul_of_pos_left a1 (x_pos a1 n); rwa mul_one at t

  theorem yn_ge_n : Π n, n ≤ yn n
  | 0 := nat.zero_le _
  | (n+1) := show n < yn (n+1), from lt_of_le_of_lt (yn_ge_n n) (y_increasing $ nat.lt_succ_self n)

  theorem y_mul_dvd (n) : ∀k, yn n ∣ yn (n * k)
  | 0     := dvd_zero _
  | (k+1) := by rw [nat.mul_succ, yn_add]; exact
    dvd_add (dvd_mul_left _ _) (dvd_mul_of_dvd_left (y_mul_dvd k) _)

  theorem y_dvd_iff (m n) : yn m ∣ yn n ↔ m ∣ n :=
  ⟨λh, nat.dvd_of_mod_eq_zero $ (nat.eq_zero_or_pos _).resolve_right $ λhp,
    have co : nat.coprime (yn m) (xn (m * (n / m))), from nat.coprime.symm $
      (xy_coprime _).coprime_dvd_right (y_mul_dvd m (n / m)),
    have m0 : m > 0, from m.eq_zero_or_pos.resolve_left $
      λe, by rw [e, nat.mod_zero] at hp; rw [e] at h; exact
      have 0 < yn a1 n, from y_increasing _ hp,
      ne_of_lt (y_increasing a1 hp) (eq_zero_of_zero_dvd h).symm,
    by rw [← nat.mod_add_div n m, yn_add] at h; exact
    not_le_of_gt (y_increasing _ $ nat.mod_lt n m0)
     (nat.le_of_dvd (y_increasing _ hp) $ co.dvd_of_dvd_mul_right $
      (nat.dvd_add_iff_right $ dvd_mul_of_dvd_right (y_mul_dvd _ _ _) _).2 h),
  λ⟨k, e⟩, by rw e; apply y_mul_dvd⟩

  theorem xy_modeq_yn (n) :
    ∀k, xn (n * k) ≡ (xn n)^k [MOD (yn n)^2]
      ∧ yn (n * k) ≡ k * (xn n)^(k-1) * yn n [MOD (yn n)^3]
  | 0     := by constructor; simp
  | (k+1) :=
    let ⟨hx, hy⟩ := xy_modeq_yn k in
    have L : xn (n * k) * xn n + d * yn (n * k) * yn n ≡ xn n^k * xn n + 0 [MOD yn n^2], from
    modeq.modeq_add (modeq.modeq_mul_right _ hx) $ modeq.modeq_zero_iff.2 $
      by rw nat.pow_succ; exact
      mul_dvd_mul_right (dvd_mul_of_dvd_right (modeq.modeq_zero_iff.1 $
        (hy.modeq_of_dvd_of_modeq $ by simp [nat.pow_succ]).trans $ modeq.modeq_zero_iff.2 $
        by simp [-mul_comm, -mul_assoc]) _) _,
    have R : xn (n * k) * yn n + yn (n * k) * xn n ≡
             xn n^k * yn n + k * xn n^k * yn n [MOD yn n^3], from
    modeq.modeq_add (by rw nat.pow_succ; exact modeq.modeq_mul_right' _ hx) $
      have k * xn n^(k - 1) * yn n * xn n = k * xn n^k * yn n,
        by clear _let_match; cases k with k; simp [nat.pow_succ, mul_comm, mul_left_comm],
      by rw ← this; exact modeq.modeq_mul_right _ hy,
    by rw [nat.add_sub_cancel, nat.mul_succ, xn_add, yn_add, nat.pow_succ (xn _ n),
           nat.succ_mul, add_comm (k * xn _ n^k) (xn _ n^k), right_distrib];
       exact ⟨L, R⟩

  theorem ysq_dvd_yy (n) : yn n * yn n ∣ yn (n * yn n) :=
  modeq.modeq_zero_iff.1 $
    ((xy_modeq_yn n (yn n)).right.modeq_of_dvd_of_modeq $ by simp [nat.pow_succ]).trans
    (modeq.modeq_zero_iff.2 $ by simp [mul_dvd_mul_left, mul_assoc])

  theorem dvd_of_ysq_dvd {n t} (h : yn n * yn n ∣ yn t) : yn n ∣ t :=
  have nt : n ∣ t, from (y_dvd_iff n t).1 $ dvd_of_mul_left_dvd h,
  n.eq_zero_or_pos.elim (λn0, by rw n0; rw n0 at nt; exact nt) $ λ(n0l : n > 0),
  let ⟨k, ke⟩ := nt in
  have yn n ∣ k * (xn n)^(k-1), from
  nat.dvd_of_mul_dvd_mul_right (y_increasing n0l) $ modeq.modeq_zero_iff.1 $
    by have xm := (xy_modeq_yn a1 n k).right; rw ← ke at xm; exact
    (xm.modeq_of_dvd_of_modeq $ by simp [nat.pow_succ]).symm.trans
      (modeq.modeq_zero_iff.2 h),
  by rw ke; exact dvd_mul_of_dvd_right
    (((xy_coprime _ _).pow_left _).symm.dvd_of_dvd_mul_right this) _

  theorem pell_zd_succ_succ (n) : pell_zd (n + 2) + pell_zd n = (2 * a : ℕ) * pell_zd (n + 1) :=
  have (1:ℤ√d) + ⟨a, 1⟩ * ⟨a, 1⟩ = ⟨a, 1⟩ * (2 * a),
  by rw zsqrtd.coe_nat_val; change (⟨_,_⟩:ℤ√(d a1))=⟨_,_⟩;
     rw dz_val; change az a1 with a; simp [mul_add, add_mul],
  by simpa [mul_add, mul_comm, mul_left_comm] using congr_arg (* pell_zd a1 n) this

  theorem xy_succ_succ (n) : xn (n + 2) + xn n = (2 * a) * xn (n + 1) ∧
                             yn (n + 2) + yn n = (2 * a) * yn (n + 1) := begin
    have := pell_zd_succ_succ a1 n, unfold pell_zd at this,
    rw [← int.cast_coe_nat, zsqrtd.smul_val] at this,
    injection this with h₁ h₂,
    split; apply int.coe_nat_inj; [simpa using h₁, simpa using h₂]
  end

  theorem xn_succ_succ (n) : xn (n + 2) + xn n = (2 * a) * xn (n + 1) := (xy_succ_succ n).1
  theorem yn_succ_succ (n) : yn (n + 2) + yn n = (2 * a) * yn (n + 1) := (xy_succ_succ n).2

  theorem xz_succ_succ (n) : xz (n + 2) = (2 * a : ℕ) * xz (n + 1) - xz n :=
  eq_sub_of_add_eq $ by delta xz; rw [← int.coe_nat_add, ← int.coe_nat_mul, xn_succ_succ]

  theorem yz_succ_succ (n) : yz (n + 2) = (2 * a : ℕ) * yz (n + 1) - yz n :=
  eq_sub_of_add_eq $ by delta yz; rw [← int.coe_nat_add, ← int.coe_nat_mul, yn_succ_succ]

  theorem yn_modeq_a_sub_one : ∀ n, yn n ≡ n [MOD a-1]
  | 0 := by simp
  | 1 := by simp
  | (n+2) := modeq.modeq_add_cancel_right (yn_modeq_a_sub_one n) $
    have 2*(n+1) = n+2+n, by simp [two_mul],
    by rw [yn_succ_succ, ← this];
    refine modeq.modeq_mul (modeq.modeq_mul_left 2 (_ : a ≡ 1 [MOD a-1])) (yn_modeq_a_sub_one (n+1));
    exact (modeq.modeq_of_dvd $ by rw [int.coe_nat_sub $ le_of_lt a1]; apply dvd_refl).symm

  theorem yn_modeq_two : ∀ n, yn n ≡ n [MOD 2]
  | 0 := by simp
  | 1 := by simp
  | (n+2) := modeq.modeq_add_cancel_right (yn_modeq_two n) $
    have 2*(n+1) = n+2+n, by simp [two_mul],
    by rw [yn_succ_succ, ← this];
    refine modeq.modeq_mul _ (yn_modeq_two (n+1));
    exact modeq.trans
      (modeq.modeq_zero_iff.2 $ by simp)
      (modeq.modeq_zero_iff.2 $ by simp).symm

  -- TODO(Mario): Hopefully a tactic will be able to dispense this lemma
  lemma x_sub_y_dvd_pow_lem (y2 y1 y0 yn1 yn0 xn1 xn0 ay a2 : ℤ) :
    (a2 * yn1 - yn0) * ay + y2 - (a2 * xn1 - xn0) =
      y2 - a2 * y1 + y0 + a2 * (yn1 * ay + y1 - xn1) - (yn0 * ay + y0 - xn0) :=
  calc  (a2 * yn1 - yn0) * ay + y2 - (a2 * xn1 - xn0)
      = a2 * yn1 * ay - yn0 * ay + y2 - (a2 * xn1 - xn0) : by rw [mul_sub_right_distrib]
  ... = y2 + a2 * (yn1 * ay) - a2 * xn1 - yn0 * ay + xn0 : by simp [mul_comm, mul_left_comm]
  ... = y2 + a2 * (yn1 * ay) - a2 * y1 + a2 * y1 - a2 * xn1 - yn0 * ay + y0 - y0 + xn0 : by rw [add_sub_cancel, sub_add_cancel]
  ... = y2 - a2 * y1 + y0 + a2 * (yn1 * ay + y1 - xn1) - (yn0 * ay + y0 - xn0) : by simp [mul_add]

  theorem x_sub_y_dvd_pow (y : ℕ) :
    ∀ n, (2*a*y - y*y - 1 : ℤ) ∣ yz n * (a - y) + ↑(y^n) - xz n
  | 0 := by simp [xz, yz, int.coe_nat_zero, int.coe_nat_one]
  | 1 := by simp [xz, yz, int.coe_nat_zero, int.coe_nat_one]
  | (n+2) :=
    have (2*a*y - y*y - 1 : ℤ) ∣ ↑(y^(n + 2)) - ↑(2 * a) * ↑(y^(n + 1)) + ↑(y^n), from
    ⟨-↑(y^n), by simp [nat.pow_succ, mul_add, int.coe_nat_mul,
        show ((2:ℕ):ℤ) = 2, from rfl, mul_comm, mul_left_comm]⟩,
    by rw [xz_succ_succ, yz_succ_succ, x_sub_y_dvd_pow_lem a1 ↑(y^(n+2)) ↑(y^(n+1)) ↑(y^n)]; exact
    dvd_sub (dvd_add this $ dvd_mul_of_dvd_right (x_sub_y_dvd_pow (n+1)) _) (x_sub_y_dvd_pow n)

  theorem xn_modeq_x2n_add_lem (n j) : xn n ∣ d * yn n * (yn n * xn j) + xn j :=
  have h1 : d * yn n * (yn n * xn j) + xn j = (d * yn n * yn n + 1) * xn j,
    by simp [add_mul, mul_assoc],
  have h2 : d * yn n * yn n + 1 = xn n * xn n, by apply int.coe_nat_inj;
    repeat {rw int.coe_nat_add <|> rw int.coe_nat_mul}; exact
    add_eq_of_eq_sub' (eq.symm $ pell_eqz _ _),
  by rw h2 at h1; rw [h1, mul_assoc]; exact dvd_mul_right _ _

  theorem xn_modeq_x2n_add (n j) : xn (2 * n + j) + xn j ≡ 0 [MOD xn n] :=
  by rw [two_mul, add_assoc, xn_add, add_assoc]; exact
  show _ ≡ 0+0 [MOD xn a1 n], from modeq.modeq_add (modeq.modeq_zero_iff.2 $ dvd_mul_right (xn a1 n) (xn a1 (n + j))) $
  by rw [yn_add, left_distrib, add_assoc]; exact
  show _ ≡ 0+0 [MOD xn a1 n], from modeq.modeq_add (modeq.modeq_zero_iff.2 $ dvd_mul_of_dvd_right (dvd_mul_right _ _) _) $
  modeq.modeq_zero_iff.2 $ xn_modeq_x2n_add_lem _ _ _

  lemma xn_modeq_x2n_sub_lem {n j} (h : j ≤ n) : xn (2 * n - j) + xn j ≡ 0 [MOD xn n] :=
  have h1 : xz n ∣ ↑d * yz n * yz (n - j) + xz j, by rw [yz_sub _ h, mul_sub_left_distrib, sub_add_eq_add_sub]; exact
  dvd_sub
    (by delta xz; delta yz;
        repeat {rw ← int.coe_nat_add <|> rw ← int.coe_nat_mul}; rw mul_comm (xn a1 j) (yn a1 n);
        exact int.coe_nat_dvd.2 (xn_modeq_x2n_add_lem _ _ _))
    (dvd_mul_of_dvd_right (dvd_mul_right _ _) _),
  by rw [two_mul, nat.add_sub_assoc h, xn_add, add_assoc]; exact
  show _ ≡ 0+0 [MOD xn a1 n], from modeq.modeq_add (modeq.modeq_zero_iff.2 $ dvd_mul_right _ _) $
  modeq.modeq_zero_iff.2 $ int.coe_nat_dvd.1 $ by simpa [xz, yz] using h1

  theorem xn_modeq_x2n_sub {n j} (h : j ≤ 2 * n) : xn (2 * n - j) + xn j ≡ 0 [MOD xn n] :=
  (le_total j n).elim xn_modeq_x2n_sub_lem
    (λjn, have 2 * n - j + j ≤ n + j, by rw [nat.sub_add_cancel h, two_mul]; exact nat.add_le_add_left jn _,
      let t := xn_modeq_x2n_sub_lem (nat.le_of_add_le_add_right this) in by rwa [nat.sub_sub_self h, add_comm] at t)

  theorem xn_modeq_x4n_add (n j) : xn (4 * n + j) ≡ xn j [MOD xn n] :=
  modeq.modeq_add_cancel_right (modeq.refl $ xn (2 * n + j)) $
  by refine @modeq.trans _ _ 0 _ _ (by rw add_comm; exact (xn_modeq_x2n_add _ _ _).symm);
     rw [show 4*n = 2*n + 2*n, from right_distrib 2 2 n, add_assoc]; apply xn_modeq_x2n_add

  theorem xn_modeq_x4n_sub {n j} (h : j ≤ 2 * n) : xn (4 * n - j) ≡ xn j [MOD xn n] :=
  have h' : j ≤ 2*n, from le_trans h (by rw nat.succ_mul; apply nat.le_add_left),
  modeq.modeq_add_cancel_right (modeq.refl $ xn (2 * n - j)) $
  by refine @modeq.trans _ _ 0 _ _ (by rw add_comm; exact (xn_modeq_x2n_sub _ h).symm);
     rw [show 4*n = 2*n + 2*n, from right_distrib 2 2 n, nat.add_sub_assoc h']; apply xn_modeq_x2n_add

  theorem eq_of_xn_modeq_lem1 {i n} (npos : n > 0) : Π {j}, i < j → j < n → xn i % xn n < xn j % xn n
  | 0     ij _  := absurd ij (nat.not_lt_zero _)
  | (j+1) ij jn :=
     suffices xn j % xn n < xn (j + 1) % xn n, from
     (lt_or_eq_of_le (nat.le_of_succ_le_succ ij)).elim
        (λh, lt_trans (eq_of_xn_modeq_lem1 h (le_of_lt jn)) this)
        (λh, by rw h; exact this),
    by rw [nat.mod_eq_of_lt (x_increasing _ (nat.lt_of_succ_lt jn)), nat.mod_eq_of_lt (x_increasing _ jn)];
       exact x_increasing _ (nat.lt_succ_self _)

  theorem eq_of_xn_modeq_lem2 {n} (h : 2 * xn n = xn (n + 1)) : a = 2 ∧ n = 0 :=
  by rw [xn_succ, mul_comm] at h; exact
  have n = 0, from n.eq_zero_or_pos.resolve_right $ λnp,
    ne_of_lt (lt_of_le_of_lt (nat.mul_le_mul_left _ a1)
      (nat.lt_add_of_pos_right $ mul_pos (d_pos a1) (y_increasing a1 np))) h,
  by cases this; simp at h; exact ⟨h.symm, rfl⟩

  theorem eq_of_xn_modeq_lem3 {i n} (npos : n > 0) :
    Π {j}, i < j → j ≤ 2 * n → j ≠ n → ¬(a = 2 ∧ n = 1 ∧ i = 0 ∧ j = 2) → xn i % xn n < xn j % xn n
  | 0     ij _   _   _     := absurd ij (nat.not_lt_zero _)
  | (j+1) ij j2n jnn ntriv :=
    have lem2 : ∀k > n, k ≤ 2*n → (↑(xn k % xn n) : ℤ) = xn n - xn (2 * n - k), from λk kn k2n,
      let k2nl := lt_of_add_lt_add_right $ show 2*n-k+k < n+k, by
        {rw nat.sub_add_cancel, rw two_mul; exact (add_lt_add_left kn n), exact k2n } in
      have xle : xn (2 * n - k) ≤ xn n, from le_of_lt $ x_increasing k2nl,
      suffices xn k % xn n = xn n - xn (2 * n - k), by rw [this, int.coe_nat_sub xle],
      by {
        rw ← nat.mod_eq_of_lt (nat.sub_lt (x_pos a1 n) (x_pos a1 (2 * n - k))),
        apply modeq.modeq_add_cancel_right (modeq.refl (xn a1 (2 * n - k))),
        rw [nat.sub_add_cancel xle],
        have t := xn_modeq_x2n_sub_lem a1 (le_of_lt k2nl),
        rw nat.sub_sub_self k2n at t,
        exact t.trans (modeq.modeq_zero_iff.2 $ dvd_refl _).symm },
    (lt_trichotomy j n).elim
    (λ (jn : j < n), eq_of_xn_modeq_lem1 npos ij (lt_of_le_of_ne jn jnn)) $ λo, o.elim
    (λ (jn : j = n), by {
      cases jn,
      apply int.lt_of_coe_nat_lt_coe_nat,
      rw [lem2 (n+1) (nat.lt_succ_self _) j2n,
          show 2 * n - (n + 1) = n - 1, by rw[two_mul, ← nat.sub_sub, nat.add_sub_cancel]],
      refine lt_sub_left_of_add_lt (int.coe_nat_lt_coe_nat_of_lt _),
      cases (lt_or_eq_of_le $ nat.le_of_succ_le_succ ij) with lin ein,
      { rw nat.mod_eq_of_lt (x_increasing _ lin),
        have ll : xn a1 (n-1) + xn a1 (n-1) ≤ xn a1 n,
        { rw [← two_mul, mul_comm, show xn a1 n = xn a1 (n-1+1), by rw [nat.sub_add_cancel npos], xn_succ],
          exact le_trans (nat.mul_le_mul_left _ a1) (nat.le_add_right _ _) },
        have npm : (n-1).succ = n := nat.succ_pred_eq_of_pos npos,
        have il : i ≤ n - 1 := by apply nat.le_of_succ_le_succ; rw npm; exact lin,
        cases lt_or_eq_of_le il with ill ile,
        { exact lt_of_lt_of_le (nat.add_lt_add_left (x_increasing a1 ill) _) ll },
        { rw ile,
          apply lt_of_le_of_ne ll,
          rw ← two_mul,
          exact λe, ntriv $
            let ⟨a2, s1⟩ := @eq_of_xn_modeq_lem2 _ a1 (n-1) (by rw[nat.sub_add_cancel npos]; exact e) in
            have n1 : n = 1, from le_antisymm (nat.le_of_sub_eq_zero s1) npos,
            by rw [ile, a2, n1]; exact ⟨rfl, rfl, rfl, rfl⟩ } },
      { rw [ein, nat.mod_self, add_zero],
        exact x_increasing _ (nat.pred_lt $ ne_of_gt npos) } })
    (λ (jn : j > n),
      have lem1 : j ≠ n → xn j % xn n < xn (j + 1) % xn n → xn i % xn n < xn (j + 1) % xn n, from λjn s,
      (lt_or_eq_of_le (nat.le_of_succ_le_succ ij)).elim
        (λh, lt_trans (eq_of_xn_modeq_lem3 h (le_of_lt j2n) jn $ λ⟨a1, n1, i0, j2⟩,
          by rw [n1, j2] at j2n; exact absurd j2n dec_trivial) s)
        (λh, by rw h; exact s),
      lem1 (ne_of_gt jn) $ int.lt_of_coe_nat_lt_coe_nat $ by {
        rw [lem2 j jn (le_of_lt j2n), lem2 (j+1) (nat.le_succ_of_le jn) j2n],
        refine sub_lt_sub_left (int.coe_nat_lt_coe_nat_of_lt $ x_increasing _ _) _,
        rw [nat.sub_succ],
        exact nat.pred_lt (ne_of_gt $ nat.sub_pos_of_lt j2n) })

  theorem eq_of_xn_modeq_le {i j n} (npos : n > 0) (ij : i ≤ j) (j2n : j ≤ 2 * n) (h : xn i ≡ xn j [MOD xn n])
    (ntriv : ¬(a = 2 ∧ n = 1 ∧ i = 0 ∧ j = 2)) : i = j :=
  (lt_or_eq_of_le ij).resolve_left $ λij',
  if jn : j = n then by {
    refine ne_of_gt _ h,
    rw [jn, nat.mod_self],
    have x0 : xn a1 0 % xn a1 n > 0 := by rw [nat.mod_eq_of_lt (x_increasing a1 npos)]; exact dec_trivial,
    cases i with i, exact x0,
    rw jn at ij',
    exact lt_trans x0 (eq_of_xn_modeq_lem3 _ npos (nat.succ_pos _) (le_trans ij j2n) (ne_of_lt ij') $
      λ⟨a1, n1, _, i2⟩, by rw [n1, i2] at ij'; exact absurd ij' dec_trivial)
  } else ne_of_lt (eq_of_xn_modeq_lem3 npos ij' j2n jn ntriv) h

  theorem eq_of_xn_modeq {i j n} (npos : n > 0) (i2n : i ≤ 2 * n) (j2n : j ≤ 2 * n) (h : xn i ≡ xn j [MOD xn n])
    (ntriv : a = 2 → n = 1 → (i = 0 → j ≠ 2) ∧ (i = 2 → j ≠ 0)) : i = j :=
  (le_total i j).elim
    (λij, eq_of_xn_modeq_le npos ij j2n h $ λ⟨a2, n1, i0, j2⟩, (ntriv a2 n1).left i0 j2)
    (λij, (eq_of_xn_modeq_le npos ij i2n h.symm $ λ⟨a2, n1, j0, i2⟩, (ntriv a2 n1).right i2 j0).symm)

  theorem eq_of_xn_modeq' {i j n} (ipos : i > 0) (hin : i ≤ n) (j4n : j ≤ 4 * n) (h : xn j ≡ xn i [MOD xn n]) :
    j = i ∨ j + i = 4 * n :=
  have i2n : i ≤ 2*n, by apply le_trans hin; rw two_mul; apply nat.le_add_left,
  have npos : n > 0, from lt_of_lt_of_le ipos hin,
  (le_or_gt j (2 * n)).imp
    (λj2n : j ≤ 2*n, eq_of_xn_modeq npos j2n i2n h $
      λa2 n1, ⟨λj0 i2, by rw [n1, i2] at hin; exact absurd hin dec_trivial,
               λj2 i0, ne_of_gt ipos i0⟩)
    (λj2n : j > 2*n, suffices i = 4*n - j, by rw [this, nat.add_sub_of_le j4n],
     have j42n : 4*n - j ≤ 2*n, from @nat.le_of_add_le_add_right j _ _ $
     by rw [nat.sub_add_cancel j4n, show 4*n = 2*n + 2*n, from right_distrib 2 2 n];
        exact nat.add_le_add_left (le_of_lt j2n) _,
     eq_of_xn_modeq npos i2n j42n
       (h.symm.trans $ let t := xn_modeq_x4n_sub j42n in by rwa [nat.sub_sub_self j4n] at t)
       (λa2 n1, ⟨λi0, absurd i0 (ne_of_gt ipos), λi2, by rw[n1, i2] at hin; exact absurd hin dec_trivial⟩))

  theorem modeq_of_xn_modeq {i j n} (ipos : i > 0) (hin : i ≤ n) (h : xn j ≡ xn i [MOD xn n]) :
    j ≡ i [MOD 4 * n] ∨ j + i ≡ 0 [MOD 4 * n] :=
  let j' := j % (4 * n) in
  have n4 : 4 * n > 0, from mul_pos dec_trivial (lt_of_lt_of_le ipos hin),
  have jl : j' < 4 * n, from nat.mod_lt _ n4,
  have jj : j ≡ j' [MOD 4 * n], by delta modeq; rw nat.mod_eq_of_lt jl,
  have ∀j q, xn (j + 4 * n * q) ≡ xn j [MOD xn n], begin
    intros j q, induction q with q IH, { simp },
    rw[nat.mul_succ, ← add_assoc, add_comm],
    exact modeq.trans (xn_modeq_x4n_add _ _ _) IH
  end,
  or.imp
    (λ(ji : j' = i), by rwa ← ji)
    (λ(ji : j' + i = 4 * n), (modeq.modeq_add jj (modeq.refl _)).trans $
      by rw ji; exact modeq.modeq_zero_iff.2 (dvd_refl _))
    (eq_of_xn_modeq' ipos hin (le_of_lt jl) $
      (modeq.symm (by rw ← nat.mod_add_div j (4*n); exact this j' _)).trans h)
end

theorem xy_modeq_of_modeq {a b c} (a1 : a > 1) (b1 : b > 1) (h : a ≡ b [MOD c]) :
  ∀ n, xn a1 n ≡ xn b1 n [MOD c] ∧ yn a1 n ≡ yn b1 n [MOD c]
| 0 := by constructor; refl
| 1 := by simp; exact ⟨h, modeq.refl 1⟩
| (n+2) := ⟨
  modeq.modeq_add_cancel_right (xy_modeq_of_modeq n).left $
    by rw [xn_succ_succ a1, xn_succ_succ b1]; exact
    modeq.modeq_mul (modeq.modeq_mul_left _ h) (xy_modeq_of_modeq (n+1)).left,
  modeq.modeq_add_cancel_right (xy_modeq_of_modeq n).right $
    by rw [yn_succ_succ a1, yn_succ_succ b1]; exact
    modeq.modeq_mul (modeq.modeq_mul_left _ h) (xy_modeq_of_modeq (n+1)).right⟩

theorem matiyasevic {a k x y} : (∃ a1 : a > 1, xn a1 k = x ∧ yn a1 k = y) ↔
a > 1 ∧ k ≤ y ∧
(x = 1 ∧ y = 0 ∨
∃ (u v s t b : ℕ),
  x * x - (a * a - 1) * y * y = 1 ∧
  u * u - (a * a - 1) * v * v = 1 ∧
  s * s - (b * b - 1) * t * t = 1 ∧
  b > 1 ∧ b ≡ 1 [MOD 4 * y] ∧ b ≡ a [MOD u] ∧
  v > 0 ∧ y * y ∣ v ∧
  s ≡ x [MOD u] ∧
  t ≡ k [MOD 4 * y]) :=
⟨λ⟨a1, hx, hy⟩, by rw [← hx, ← hy];
  refine ⟨a1, (nat.eq_zero_or_pos k).elim
    (λk0, by rw k0; exact ⟨le_refl _, or.inl ⟨rfl, rfl⟩⟩) (λkpos, _)⟩; exact
  let x := xn a1 k, y := yn a1 k,
      m := 2 * (k * y),
      u := xn a1 m, v := yn a1 m in
  have ky : k ≤ y, from yn_ge_n a1 k,
  have yv : y * y ∣ v, from dvd_trans (ysq_dvd_yy a1 k) $
      (y_dvd_iff _ _ _).2 $ dvd_mul_left _ _,
  have uco : nat.coprime u (4 * y), from
    have 2 ∣ v, from modeq.modeq_zero_iff.1 $ (yn_modeq_two _ _).trans $
      modeq.modeq_zero_iff.2 (dvd_mul_right _ _),
    have nat.coprime u 2, from
      (xy_coprime a1 m).coprime_dvd_right this,
    (this.mul_right this).mul_right $
      (xy_coprime _ _).coprime_dvd_right (dvd_of_mul_left_dvd yv),
  let ⟨b, ba, bm1⟩ := modeq.chinese_remainder uco a 1 in
  have m1 : 1 < m, from
    have 0 < k * y, from mul_pos kpos (y_increasing a1 kpos),
    nat.mul_le_mul_left 2 this,
  have vp : v > 0, from y_increasing a1 (lt_trans zero_lt_one m1),
  have b1 : b > 1, from
    have u > xn a1 1, from x_increasing a1 m1,
    have u > a, by simp at this; exact this,
    lt_of_lt_of_le a1 $ by delta modeq at ba;
      rw nat.mod_eq_of_lt this at ba; rw ← ba; apply nat.mod_le,
  let s := xn b1 k, t := yn b1 k in
  have sx : s ≡ x [MOD u], from (xy_modeq_of_modeq b1 a1 ba k).left,
  have tk : t ≡ k [MOD 4 * y], from
      have 4 * y ∣ b - 1, from int.coe_nat_dvd.1 $
        by rw int.coe_nat_sub (le_of_lt b1);
           exact modeq.dvd_of_modeq bm1.symm,
      modeq.modeq_of_dvd_of_modeq this $ yn_modeq_a_sub_one _ _,
  ⟨ky, or.inr ⟨u, v, s, t, b,
    pell_eq _ _, pell_eq _ _, pell_eq _ _, b1, bm1, ba, vp, yv, sx, tk⟩⟩,
λ⟨a1, ky, o⟩, ⟨a1, match o with
| or.inl ⟨x1, y0⟩ := by rw y0 at ky; rw [nat.eq_zero_of_le_zero ky, x1, y0]; exact ⟨rfl, rfl⟩
| or.inr ⟨u, v, s, t, b, xy, uv, st, b1, rem⟩ :=
  match x, y, eq_pell a1 xy, u, v, eq_pell a1 uv, s, t, eq_pell b1 st, rem, ky with
  | ._, ._, ⟨i, rfl, rfl⟩, ._, ._, ⟨n, rfl, rfl⟩, ._, ._, ⟨j, rfl, rfl⟩,
    ⟨(bm1 : b ≡ 1 [MOD 4 * yn a1 i]),
     (ba : b ≡ a [MOD xn a1 n]),
     (vp : yn a1 n > 0),
     (yv : yn a1 i * yn a1 i ∣ yn a1 n),
     (sx : xn b1 j ≡ xn a1 i [MOD xn a1 n]),
     (tk : yn b1 j ≡ k [MOD 4 * yn a1 i])⟩,
     (ky : k ≤ yn a1 i) :=
    (nat.eq_zero_or_pos i).elim
      (λi0, by simp [i0] at ky; rw [i0, ky]; exact ⟨rfl, rfl⟩) $ λipos,
    suffices i = k, by rw this; exact ⟨rfl, rfl⟩,
    by clear _x o rem xy uv st _match _match _fun_match; exact
    have iln : i ≤ n, from le_of_not_gt $ λhin,
    not_lt_of_ge (nat.le_of_dvd vp (dvd_of_mul_left_dvd yv)) (y_increasing a1 hin),
    have yd : 4 * yn a1 i ∣ 4 * n, from mul_dvd_mul_left _ $ dvd_of_ysq_dvd a1 yv,
    have jk : j ≡ k [MOD 4 * yn a1 i], from
      have 4 * yn a1 i ∣ b - 1, from int.coe_nat_dvd.1 $
        by rw int.coe_nat_sub (le_of_lt b1); exact modeq.dvd_of_modeq bm1.symm,
      (modeq.modeq_of_dvd_of_modeq this (yn_modeq_a_sub_one b1 _)).symm.trans tk,
    have ki : k + i < 4 * yn a1 i, from
      lt_of_le_of_lt (add_le_add ky (yn_ge_n a1 i)) $
      by rw ← two_mul; exact nat.mul_lt_mul_of_pos_right dec_trivial (y_increasing a1 ipos),
    have ji : j ≡ i [MOD 4 * n], from
      have xn a1 j ≡ xn a1 i [MOD xn a1 n], from (xy_modeq_of_modeq b1 a1 ba j).left.symm.trans sx,
      (modeq_of_xn_modeq a1 ipos iln this).resolve_right $ λ (ji : j + i ≡ 0 [MOD 4 * n]),
      not_le_of_gt ki $ nat.le_of_dvd (lt_of_lt_of_le ipos $ nat.le_add_left _ _) $
      modeq.modeq_zero_iff.1 $ (modeq.modeq_add jk.symm (modeq.refl i)).trans $
      modeq.modeq_of_dvd_of_modeq yd ji,
    by have : i % (4 * yn a1 i) = k % (4 * yn a1 i) :=
         (modeq.modeq_of_dvd_of_modeq yd ji).symm.trans jk;
       rwa [nat.mod_eq_of_lt (lt_of_le_of_lt (nat.le_add_left _ _) ki),
            nat.mod_eq_of_lt (lt_of_le_of_lt (nat.le_add_right _ _) ki)] at this
  end
end⟩⟩

lemma eq_pow_of_pell_lem {a y k} (a1 : 1 < a) (ypos : y > 0) : k > 0 → a > y^k →
  (↑(y^k) : ℤ) < 2*a*y - y*y - 1 :=
have y < a → 2*a*y ≥ a + (y*y + 1), begin
  intro ya, induction y with y IH, exact absurd ypos (lt_irrefl _),
  cases nat.eq_zero_or_pos y with y0 ypos,
  { rw y0, simp [two_mul], apply add_le_add_left, exact a1 },
  { rw [nat.mul_succ, nat.mul_succ, nat.succ_mul y],
    have : 2 * a ≥ y + nat.succ y,
    { change y + y < 2 * a, rw ← two_mul,
      exact mul_lt_mul_of_pos_left (nat.lt_of_succ_lt ya) dec_trivial },
    have := add_le_add (IH ypos (nat.lt_of_succ_lt ya)) this,
    simp at this, simp, exact this }
end, λk0 yak,
lt_of_lt_of_le (int.coe_nat_lt_coe_nat_of_lt yak) $
by rw sub_sub; apply le_sub_right_of_add_le;
   apply int.coe_nat_le_coe_nat_of_le;
   have y1 := nat.pow_le_pow_of_le_right ypos k0; simp at y1;
   exact this (lt_of_le_of_lt y1 yak)

theorem eq_pow_of_pell {m n k} : (n^k = m ↔
k = 0 ∧ m = 1 ∨ k > 0 ∧
(n = 0 ∧ m = 0 ∨ n > 0 ∧
∃ (w a t z : ℕ) (a1 : a > 1),
  xn a1 k ≡ yn a1 k * (a - n) + m [MOD t] ∧
  2 * a * n = t + (n * n + 1) ∧
  m < t ∧ n ≤ w ∧ k ≤ w ∧
  a * a - ((w + 1) * (w + 1) - 1) * (w * z) * (w * z) = 1)) :=
⟨λe, by rw ← e;
  refine (nat.eq_zero_or_pos k).elim
    (λk0, by rw k0; exact or.inl ⟨rfl, rfl⟩)
    (λkpos, or.inr ⟨kpos, _⟩);
  refine (nat.eq_zero_or_pos n).elim
    (λn0, by rw [n0, nat.zero_pow kpos]; exact or.inl ⟨rfl, rfl⟩)
    (λnpos, or.inr ⟨npos, _⟩); exact
  let w := _root_.max n k in
  have nw : n ≤ w, from le_max_left _ _,
  have kw : k ≤ w, from le_max_right _ _,
  have wpos : w > 0, from lt_of_lt_of_le npos nw,
  have w1 : w + 1 > 1, from nat.succ_lt_succ wpos,
  let a := xn w1 w in
  have a1 : a > 1, from x_increasing w1 wpos,
  let x := xn a1 k, y := yn a1 k in
  let ⟨z, ze⟩ := show w ∣ yn w1 w, from modeq.modeq_zero_iff.1 $
    modeq.trans (yn_modeq_a_sub_one w1 w) (modeq.modeq_zero_iff.2 $ dvd_refl _) in
  have nt : (↑(n^k) : ℤ) < 2 * a * n - n * n - 1, from
    eq_pow_of_pell_lem a1 npos kpos $ calc
      n^k ≤ n^w       : nat.pow_le_pow_of_le_right npos kw
      ... < (w + 1)^w : nat.pow_lt_pow_of_lt_left (nat.lt_succ_of_le nw) wpos
      ... ≤ a         : xn_ge_a_pow w1 w,
  let ⟨t, te⟩ := int.eq_coe_of_zero_le $
    le_trans (int.coe_zero_le _) $ le_of_lt nt in
  have na : n ≤ a, from le_trans nw $ le_of_lt $ n_lt_xn w1 w,
  have tm : x ≡ y * (a - n) + n^k [MOD t], begin
    apply modeq.modeq_of_dvd,
    rw [int.coe_nat_add, int.coe_nat_mul, int.coe_nat_sub na, ← te],
    exact x_sub_y_dvd_pow a1 n k
  end,
  have ta : 2 * a * n = t + (n * n + 1), from int.coe_nat_inj $
    by rw [int.coe_nat_add, ← te, sub_sub];
       repeat {rw int.coe_nat_add <|> rw int.coe_nat_mul};
       rw [int.coe_nat_one, sub_add_cancel]; refl,
  have mt : n^k < t, from int.lt_of_coe_nat_lt_coe_nat $
    by rw ← te; exact nt,
  have zp : a * a - ((w + 1) * (w + 1) - 1) * (w * z) * (w * z) = 1,
    by rw ← ze; exact pell_eq w1 w,
  ⟨w, a, t, z, a1, tm, ta, mt, nw, kw, zp⟩,
λo, match o with
| or.inl ⟨k0, m1⟩ := by rw [k0, m1]; refl
| or.inr ⟨kpos, or.inl ⟨n0, m0⟩⟩ := by rw [n0, m0, nat.zero_pow kpos]
| or.inr ⟨kpos, or.inr ⟨npos, w, a, t, z,
   (a1 : a > 1),
   (tm : xn a1 k ≡ yn a1 k * (a - n) + m [MOD t]),
   (ta : 2 * a * n = t + (n * n + 1)),
   (mt : m < t),
   (nw : n ≤ w),
   (kw : k ≤ w),
   (zp : a * a - ((w + 1) * (w + 1) - 1) * (w * z) * (w * z) = 1)⟩⟩ :=
  have wpos : w > 0, from lt_of_lt_of_le npos nw,
  have w1 : w + 1 > 1, from nat.succ_lt_succ wpos,
  let ⟨j, xj, yj⟩ := eq_pell w1 zp in
  by clear _match o _let_match; exact
  have jpos : j > 0, from (nat.eq_zero_or_pos j).resolve_left $ λj0,
    have a1 : a = 1, by rw j0 at xj; exact xj,
    have 2 * n = t + (n * n + 1), by rw a1 at ta; exact ta,
    have n1 : n = 1, from
      have n * n < n * 2, by rw [mul_comm n 2, this]; apply nat.le_add_left,
      have n ≤ 1, from nat.le_of_lt_succ $ lt_of_mul_lt_mul_left this (nat.zero_le _),
      le_antisymm this npos,
    by rw n1 at this;
      rw ← @nat.add_right_cancel 0 2 t this at mt;
      exact nat.not_lt_zero _ mt,
  have wj : w ≤ j, from nat.le_of_dvd jpos $ modeq.modeq_zero_iff.1 $
    (yn_modeq_a_sub_one w1 j).symm.trans $
    modeq.modeq_zero_iff.2 ⟨z, yj.symm⟩,
  have nt : (↑(n^k) : ℤ) < 2 * a * n - n * n - 1, from
    eq_pow_of_pell_lem a1 npos kpos $ calc
      n^k ≤ n^j       : nat.pow_le_pow_of_le_right npos (le_trans kw wj)
      ... < (w + 1)^j : nat.pow_lt_pow_of_lt_left (nat.lt_succ_of_le nw) jpos
      ... ≤ xn w1 j   : xn_ge_a_pow w1 j
      ... = a         : xj.symm,
  have na : n ≤ a, by rw xj; exact
    le_trans (le_trans nw wj) (le_of_lt $ n_lt_xn _ _),
  have te : (t : ℤ) = 2 * ↑a * ↑n - ↑n * ↑n - 1, by
    rw sub_sub; apply eq_sub_of_add_eq; apply (int.coe_nat_eq_coe_nat_iff _ _).2;
    exact ta.symm,
  have xn a1 k ≡ yn a1 k * (a - n) + n^k [MOD t],
    by have := x_sub_y_dvd_pow a1 n k;
       rw [← te, ← int.coe_nat_sub na] at this; exact modeq.modeq_of_dvd this,
  have n^k % t = m % t, from
    modeq.modeq_add_cancel_left (modeq.refl _) (this.symm.trans tm),
  by rw ← te at nt;
     rwa [nat.mod_eq_of_lt (int.lt_of_coe_nat_lt_coe_nat nt), nat.mod_eq_of_lt mt] at this
end⟩

end pell
