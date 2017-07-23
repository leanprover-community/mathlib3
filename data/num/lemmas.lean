/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

Properties of the binary representation of integers.
-/
import data.num.basic data.num.bitwise pending

meta def unfold_coe : tactic unit :=
`[unfold coe lift_t has_lift_t.lift coe_t has_coe_t.coe coe_b has_coe.coe]

namespace pos_num

  theorem one_to_nat : ((1 : pos_num) : ℕ) = 1 := rfl

  theorem bit_to_nat (b n) : (bit b n : ℕ) = nat.bit b n :=
  by cases b; refl

  theorem succ_to_nat : ∀ n, (succ n : ℕ) = n + 1
  | 1        := rfl
  | (bit0 p) := rfl
  | (bit1 p) := (congr_arg _root_.bit0 (succ_to_nat p)).trans $
    show ↑p + 1 + ↑p + 1 = ↑p + ↑p + 1 + 1, by simp

  theorem add_one (n : pos_num) : n + 1 = succ n := by cases n; refl
  theorem one_add (n : pos_num) : 1 + n = succ n := by cases n; refl

  theorem add_to_nat : ∀ m n, ((m + n : pos_num) : ℕ) = m + n
  | 1        b        := by rw [one_add b, succ_to_nat, add_comm]; refl
  | a        1        := by rw [add_one a, succ_to_nat]; refl
  | (bit0 a) (bit0 b) := (congr_arg _root_.bit0 (add_to_nat a b)).trans $
    show ((a + b) + (a + b) : ℕ) = (a + a) + (b + b), by simp
  | (bit0 a) (bit1 b) := (congr_arg _root_.bit1 (add_to_nat a b)).trans $
    show ((a + b) + (a + b) + 1 : ℕ) = (a + a) + (b + b + 1), by simp
  | (bit1 a) (bit0 b) := (congr_arg _root_.bit1 (add_to_nat a b)).trans $
    show ((a + b) + (a + b) + 1 : ℕ) = (a + a + 1) + (b + b), by simp
  | (bit1 a) (bit1 b) :=
    show (succ (a + b) + succ (a + b) : ℕ) = (a + a + 1) + (b + b + 1),
    by rw [succ_to_nat, add_to_nat]; simp

  theorem add_succ : ∀ (m n : pos_num), m + succ n = succ (m + n)
  | 1        b        := by simp [one_add]
  | (bit0 a) 1        := congr_arg bit0 (add_one a)
  | (bit1 a) 1        := congr_arg bit1 (add_one a)
  | (bit0 a) (bit0 b) := rfl
  | (bit0 a) (bit1 b) := congr_arg bit0 (add_succ a b)
  | (bit1 a) (bit0 b) := rfl
  | (bit1 a) (bit1 b) := congr_arg bit1 (add_succ a b)

  theorem bit0_of_bit0 : Π n, _root_.bit0 n = bit0 n
  | 1        := rfl
  | (bit0 p) := congr_arg bit0 (bit0_of_bit0 p)
  | (bit1 p) := show bit0 (succ (_root_.bit0 p)) = _, by rw bit0_of_bit0; refl

  theorem bit1_of_bit1 (n : pos_num) : _root_.bit1 n = bit1 n :=
  show _root_.bit0 n + 1 = bit1 n, by rw [add_one, bit0_of_bit0]; refl

  theorem to_nat_pos : ∀ n : pos_num, (n : ℕ) > 0
  | 1        := dec_trivial
  | (bit0 p) := let h := to_nat_pos p in add_pos h h
  | (bit1 p) := nat.succ_pos _

  theorem pred'_to_nat : ∀ n, (option.cases_on (pred' n) ((n : ℕ) = 1) (λm, (m : ℕ) = nat.pred n) : Prop)
  | 1                := rfl
  | (pos_num.bit1 q) := rfl
  | (pos_num.bit0 q) :=
    suffices _ → ((option.cases_on (pred' q) 1 bit1 : pos_num) : ℕ) = nat.pred (bit0 q),
    from this (pred'_to_nat q),
    match pred' q with
    | none, (IH : (q : ℕ) = 1) := show 1 = nat.pred (q + q), by rw IH; refl
    | some p, (IH : ↑p = nat.pred q) :=
      show _root_.bit1 ↑p = nat.pred (q + q), begin
        rw [←nat.succ_pred_eq_of_pos (to_nat_pos q), IH],
        generalize : nat.pred q = n,
        simp [_root_.bit1, _root_.bit0]
      end
    end

  theorem mul_to_nat (m) : ∀ n, ((m * n : pos_num) : ℕ) = m * n
  | 1        := (mul_one _).symm
  | (bit0 p) := show (↑(m * p) + ↑(m * p) : ℕ) = ↑m * (p + p), by rw [mul_to_nat, left_distrib]
  | (bit1 p) := (add_to_nat (bit0 (m * p)) m).trans $
    show (↑(m * p) + ↑(m * p) + ↑m : ℕ) = ↑m * (p + p) + m, by rw [mul_to_nat, left_distrib]

end pos_num

namespace num
  open pos_num

  theorem zero_to_nat : ((0 : num) : ℕ) = 0 := rfl

  theorem one_to_nat : ((1 : num) : ℕ) = 1 := rfl

  theorem bit_to_nat (b n) : (bit b n : ℕ) = nat.bit b n :=
  by cases b; cases n; refl

  theorem add_to_nat : ∀ m n, ((m + n : num) : ℕ) = m + n
  | 0       0       := rfl
  | 0       (pos q) := (zero_add _).symm
  | (pos p) 0       := rfl
  | (pos p) (pos q) := pos_num.add_to_nat _ _

  theorem add_zero (n : num) : n + 0 = n := by cases n; refl
  theorem zero_add (n : num) : 0 + n = n := by cases n; refl

  theorem add_succ : ∀ (m n : num), m + succ n = succ (m + n)
  | 0       n       := by simp [zero_add]
  | (pos p) 0       := show pos (p + 1) = succ (pos p + 0), by rw [add_one, add_zero]; refl
  | (pos p) (pos q) := congr_arg pos (pos_num.add_succ _ _)

  theorem succ'_to_nat : ∀ n, (succ' n : ℕ) = n + 1
  | 0       := rfl
  | (pos p) := pos_num.succ_to_nat _

  theorem succ_to_nat (n) : (succ n : ℕ) = n + 1 := succ'_to_nat n

  @[simp] theorem to_of_nat : Π (n : ℕ), ((n : num) : ℕ) = n
  | 0     := rfl
  | (n+1) := (succ_to_nat (num.of_nat n)).trans (congr_arg nat.succ (to_of_nat n))

  theorem of_nat_inj : ∀ {m n : ℕ}, (m : num) = n → m = n :=
  function.injective_of_left_inverse to_of_nat

  theorem add_of_nat (m) : ∀ n, ((m + n : ℕ) : num) = m + n
  | 0     := (add_zero _).symm
  | (n+1) := show succ (m + n : ℕ) = m + succ n,
             by rw [add_succ, add_of_nat]

  theorem mul_to_nat : ∀ m n, ((m * n : num) : ℕ) = m * n
  | 0       0       := rfl
  | 0       (pos q) := (zero_mul _).symm
  | (pos p) 0       := rfl
  | (pos p) (pos q) := pos_num.mul_to_nat _ _

end num

namespace pos_num
  open num

  @[simp] theorem of_to_nat : Π (n : pos_num), ((n : ℕ) : num) = pos n
  | 1        := rfl
  | (bit0 p) :=
    show ↑(p + p : ℕ) = pos (bit0 p),
    by rw [add_of_nat, of_to_nat]; exact congr_arg pos p.bit0_of_bit0
  | (bit1 p) :=
    show num.succ (p + p : ℕ) = pos (bit1 p),
    by rw [add_of_nat, of_to_nat]; exact congr_arg (num.pos ∘ succ) p.bit0_of_bit0

  theorem to_nat_inj {m n : pos_num} (h : (m : ℕ) = n) : m = n :=
  by have := congr_arg (coe : ℕ → num) h; simp at this; injection this

  theorem pred_to_nat {n : pos_num} (h : n > 1) : (pred n : ℕ) = nat.pred n :=
  begin
    unfold pred,
    have := pred'_to_nat n, revert this,
    cases pred' n; dsimp [option.get_or_else],
    { intro this, rw @to_nat_inj n 1 this at h,
      exact absurd h dec_trivial },
    { exact id }
  end

  theorem cmp_swap (m) : ∀n, (cmp m n).swap = cmp n m :=
  by induction m with m IH m IH; intro n;
     cases n with n n; try {unfold cmp}; try {refl}; rw ←IH; cases cmp m n; refl

  lemma cmp_dec_lemma {m n} : m < n → bit1 m < bit0 n :=
  show (m:ℕ) < n → (m + m + 1 + 1 : ℕ) ≤ n + n,
  by intro h; rw [nat.add_right_comm m m 1, add_assoc]; exact add_le_add h h

  theorem cmp_dec : ∀ (m n), (ordering.cases_on (cmp m n) (m < n) (m = n) (m > n) : Prop)
  | 1        1        := rfl
  | (bit0 a) 1        := let h : (1:ℕ) ≤ a := to_nat_pos a in add_le_add h h
  | (bit1 a) 1        := nat.succ_lt_succ $ to_nat_pos $ bit0 a
  | 1        (bit0 b) := let h : (1:ℕ) ≤ b := to_nat_pos b in add_le_add h h
  | 1        (bit1 b) := nat.succ_lt_succ $ to_nat_pos $ bit0 b
  | (bit0 a) (bit0 b) := begin
      have := cmp_dec a b, revert this, cases cmp a b; dsimp; intro,
      { exact @add_lt_add nat _ _ _ _ _ this this },
      { rw this },
      { exact @add_lt_add nat _ _ _ _ _ this this }
    end
  | (bit0 a) (bit1 b) := begin dsimp [cmp],
      have := cmp_dec a b, revert this, cases cmp a b; dsimp; intro,
      { exact nat.le_succ_of_le (@add_lt_add nat _ _ _ _ _ this this) },
      { rw this, apply nat.lt_succ_self },
      { exact cmp_dec_lemma this }
    end
  | (bit1 a) (bit0 b) := begin dsimp [cmp],
      have := cmp_dec a b, revert this, cases cmp a b; dsimp; intro,
      { exact cmp_dec_lemma this },
      { rw this, apply nat.lt_succ_self },
      { exact nat.le_succ_of_le (@add_lt_add nat _ _ _ _ _ this this) },
    end
  | (bit1 a) (bit1 b) := begin
      have := cmp_dec a b, revert this, cases cmp a b; dsimp; intro,
      { exact nat.succ_lt_succ (add_lt_add this this) },
      { rw this },
      { exact nat.succ_lt_succ (add_lt_add this this) }
    end

  theorem lt_iff_cmp {m n} : m < n ↔ cmp m n = ordering.lt :=
  match cmp m n, cmp_dec m n with
  | ordering.lt, (h : m < n) := ⟨λ_, rfl, λ_, h⟩
  | ordering.eq, (h : m = n) :=
    ⟨λh', absurd h' $ by rw h; apply @lt_irrefl nat, dec_trivial⟩
  | ordering.gt, (h : m > n) :=
    ⟨λh', absurd h' $ @not_lt_of_gt nat _ _ _ h, dec_trivial⟩
  end

  theorem le_iff_cmp {m n} : m ≤ n ↔ cmp m n ≠ ordering.gt :=
  iff.trans ⟨@not_lt_of_ge nat _ _ _, le_of_not_gt⟩ $ not_congr $
  lt_iff_cmp.trans $ by rw ←cmp_swap; cases cmp m n; exact dec_trivial

  instance decidable_lt : @decidable_rel pos_num (<) := λ m n,
  decidable_of_decidable_of_iff (by apply_instance) lt_iff_cmp.symm

  instance decidable_le : @decidable_rel pos_num (≤) := λ m n,
  decidable_of_decidable_of_iff (by apply_instance) le_iff_cmp.symm

  meta def transfer_rw : tactic unit :=
  `[repeat {rw add_to_nat <|> rw mul_to_nat <|> rw one_to_nat <|> rw zero_to_nat}]

  meta def transfer : tactic unit := `[intros, apply to_nat_inj, transfer_rw, try {simp}]

  instance : add_comm_semigroup pos_num :=
  { add            := (+),
    add_assoc      := by transfer,
    add_comm       := by transfer }

  instance : comm_monoid pos_num :=
  { mul            := (*),
    mul_assoc      := by transfer,
    one            := 1,
    one_mul        := by transfer,
    mul_one        := by transfer,
    mul_comm       := by transfer }

  instance : distrib pos_num :=
  { add            := (+),
    mul            := (*),
    left_distrib   := by {transfer, simp [left_distrib]},
    right_distrib  := by {transfer, simp [left_distrib]} }

  -- TODO(Mario): Prove these using transfer tactic
  instance : decidable_linear_order pos_num :=
  { lt              := (<),
    le              := (≤),
    le_refl         := λa, @le_refl nat _ _,
    le_trans        := λa b c, @le_trans nat _ _ _ _,
    le_antisymm     := λa b h1 h2, to_nat_inj $ @le_antisymm nat _ _ _ h1 h2,
    le_total        := λa b, @le_total nat _ _ _,
    le_iff_lt_or_eq := λa b, le_iff_lt_or_eq.trans $ or_congr iff.rfl ⟨to_nat_inj, congr_arg _⟩,
    lt_irrefl       := λ a, @lt_irrefl nat _ _,
    decidable_lt    := by apply_instance,
    decidable_le    := by apply_instance,
    decidable_eq    := by apply_instance }

end pos_num

namespace num
  open pos_num

  @[simp] theorem of_to_nat : Π (n : num), ((n : ℕ) : num) = n
  | 0       := rfl
  | (pos p) := p.of_to_nat

  theorem to_nat_inj : ∀ {m n : num}, (m : ℕ) = n → m = n :=
  function.injective_of_left_inverse of_to_nat

  theorem pred_to_nat : ∀ (n : num), (pred n : ℕ) = nat.pred n
  | 0       := rfl
  | (pos p) :=
    suffices _ → ↑(option.cases_on (pred' p) 0 pos : num) = nat.pred p,
    from this (pred'_to_nat p),
    by { cases pred' p; dsimp [option.get_or_else]; intro h, rw h; refl, exact h }

  theorem cmp_swap (m n) : (cmp m n).swap = cmp n m :=
  by cases m; cases n; try {unfold cmp}; try {refl}; apply pos_num.cmp_swap

  theorem cmp_dec : ∀ (m n), (ordering.cases_on (cmp m n) (m < n) (m = n) (m > n) : Prop)
  | 0       0       := rfl
  | 0       (pos b) := to_nat_pos _
  | (pos a) 0       := to_nat_pos _
  | (pos a) (pos b) :=
    by { have := pos_num.cmp_dec a b; revert this; dsimp [cmp];
         cases pos_num.cmp a b, exacts [id, congr_arg pos, id] }

  theorem lt_iff_cmp {m n} : m < n ↔ cmp m n = ordering.lt :=
  match cmp m n, cmp_dec m n with
  | ordering.lt, (h : m < n) := ⟨λ_, rfl, λ_, h⟩
  | ordering.eq, (h : m = n) :=
    ⟨λh', absurd h' $ by rw h; apply @lt_irrefl nat, dec_trivial⟩
  | ordering.gt, (h : m > n) :=
    ⟨λh', absurd h' $ @not_lt_of_gt nat _ _ _ h, dec_trivial⟩
  end

  theorem le_iff_cmp {m n} : m ≤ n ↔ cmp m n ≠ ordering.gt :=
  iff.trans ⟨@not_lt_of_ge nat _ _ _, le_of_not_gt⟩ $ not_congr $
  lt_iff_cmp.trans $ by rw ←cmp_swap; cases cmp m n; exact dec_trivial

  instance decidable_lt : @decidable_rel num (<) := λ m n,
  decidable_of_decidable_of_iff (by apply_instance) lt_iff_cmp.symm

  instance decidable_le : @decidable_rel num (≤) := λ m n,
  decidable_of_decidable_of_iff (by apply_instance) le_iff_cmp.symm

  meta def transfer_rw : tactic unit :=
  `[repeat {rw add_to_nat <|> rw mul_to_nat <|> rw one_to_nat <|> rw zero_to_nat}]

  meta def transfer : tactic unit := `[intros, apply to_nat_inj, transfer_rw, try {simp}]

  instance : comm_semiring num :=
  { add            := (+),
    add_assoc      := by transfer,
    zero           := 0,
    zero_add       := zero_add,
    add_zero       := add_zero,
    add_comm       := by transfer,
    mul            := (*),
    mul_assoc      := by transfer,
    one            := 1,
    one_mul        := by transfer,
    mul_one        := by transfer,
    left_distrib   := by {transfer, simp [left_distrib]},
    right_distrib  := by {transfer, simp [left_distrib]},
    zero_mul       := by transfer,
    mul_zero       := by transfer,
    mul_comm       := by transfer }

  instance : decidable_linear_ordered_semiring num :=
  { num.comm_semiring with
    add_left_cancel            := λ a b c h, by { apply to_nat_inj,
      have := congr_arg (coe : num → nat) h, revert this,
      transfer_rw, apply add_left_cancel },
    add_right_cancel           := λ a b c h, by { apply to_nat_inj,
      have := congr_arg (coe : num → nat) h, revert this,
      transfer_rw, apply add_right_cancel },
    lt                         := (<),
    le                         := (≤),
    le_refl                    := λa, @le_refl nat _ _,
    le_trans                   := λa b c, @le_trans nat _ _ _ _,
    le_antisymm                := λa b h1 h2, to_nat_inj $ @le_antisymm nat _ _ _ h1 h2,
    le_total                   := λa b, @le_total nat _ _ _,
    le_iff_lt_or_eq            := λa b, le_iff_lt_or_eq.trans $ or_congr iff.rfl ⟨to_nat_inj, congr_arg _⟩,
    le_of_lt                   := λa b, @le_of_lt nat _ _ _,
    lt_irrefl                  := λa, @lt_irrefl nat _ _,
    lt_of_lt_of_le             := λa b c, @lt_of_lt_of_le nat _ _ _ _,
    lt_of_le_of_lt             := λa b c, @lt_of_le_of_lt nat _ _ _ _,
    lt_of_add_lt_add_left      := λa b c, show (_:ℕ)<_→(_:ℕ)<_, by {transfer_rw, apply lt_of_add_lt_add_left},
    add_lt_add_left            := λa b h c, show (_:ℕ)<_, by {transfer_rw, apply @add_lt_add_left nat _ _ _ h},
    add_le_add_left            := λa b h c, show (_:ℕ)≤_, by {transfer_rw, apply @add_le_add_left nat _ _ _ h},
    le_of_add_le_add_left      := λa b c, show (_:ℕ)≤_→(_:ℕ)≤_, by {transfer_rw, apply le_of_add_le_add_left},
    zero_lt_one                := dec_trivial,
    mul_le_mul_of_nonneg_left  := λa b c h _, show (_:ℕ)≤_, by {transfer_rw, apply nat.mul_le_mul_left _ h},
    mul_le_mul_of_nonneg_right := λa b c h _, show (_:ℕ)≤_, by {transfer_rw, apply nat.mul_le_mul_right _ h},
    mul_lt_mul_of_pos_left     := λa b c h₁ h₂, show (_:ℕ)<_, by {transfer_rw, apply nat.mul_lt_mul_of_pos_left h₁ h₂},
    mul_lt_mul_of_pos_right    := λa b c h₁ h₂, show (_:ℕ)<_, by {transfer_rw, apply nat.mul_lt_mul_of_pos_right h₁ h₂},
    decidable_lt               := num.decidable_lt,
    decidable_le               := num.decidable_le,
    decidable_eq               := num.decidable_eq }

  lemma bitwise_to_nat {f : num → num → num} {g : bool → bool → bool}
    (p : pos_num → pos_num → num)
    (gff : g ff ff = ff)
    (f00 : f 0 0 = 0)
    (f0n : ∀ n, f 0 (pos n) = cond (g ff tt) (pos n) 0)
    (fn0 : ∀ n, f (pos n) 0 = cond (g tt ff) (pos n) 0)
    (fnn : ∀ m n, f (pos m) (pos n) = p m n)
    (p11 : p 1 1 = cond (g tt tt) 1 0)
    (p1b : ∀ b n, p 1 (pos_num.bit b n) = bit (g tt b) (cond (g ff tt) ↑n 0))
    (pb1 : ∀ a m, p (pos_num.bit a m) 1 = bit (g a tt) (cond (g tt ff) ↑m 0))
    (pbb : ∀ a b m n, p (pos_num.bit a m) (pos_num.bit b n) = bit (g a b) (p m n))
    : ∀ m n : num, (f m n : ℕ) = nat.bitwise g m n :=
  begin
    intros, cases m with m; cases n with n;
    try { change zero with 0 };
    try { change ((0:num):ℕ) with 0 },
    { rw [f00, nat.bitwise_zero]; refl },
    { unfold nat.bitwise, rw [f0n, nat.binary_rec_zero],
      cases g ff tt; refl },
    { unfold nat.bitwise,
      generalize h : (pos m : ℕ) = m', revert h,
      apply nat.bit_cases_on m' _, intros b m' h,
      rw [fn0, nat.binary_rec_eq, nat.binary_rec_zero, ←h],
      cases g tt ff; refl,
      apply nat.bitwise_bit_aux gff },
    { rw fnn, revert n,
      have : ∀b (n : pos_num), cond b ↑n 0 = ↑(cond b n 0 : num) :=
        by intros; cases b; refl,
      induction m with m IH m IH; intro n; cases n with n n,
      any_goals { change one with 1 },
      any_goals { change pos 1 with 1 },
      any_goals { change pos_num.bit0 with pos_num.bit ff },
      any_goals { change pos_num.bit1 with pos_num.bit tt },
      any_goals { change ((1:num):ℕ) with nat.bit tt 0 },
      all_goals {
        repeat {
          rw show ∀ b n, (pos (pos_num.bit b n) : ℕ) = nat.bit b ↑n,
             by intros; cases b; refl },
        rw nat.bitwise_bit },
      any_goals { assumption },
      any_goals { rw [nat.bitwise_zero, p11], cases g tt tt; refl },
      any_goals { rw [nat.bitwise_zero_left, this, ←bit_to_nat, p1b] },
      any_goals { rw [nat.bitwise_zero_right _ gff, this, ←bit_to_nat, pb1] },
      all_goals { rw [←show ∀ n, ↑(p m n) = nat.bitwise g ↑m ↑n, from IH],
        rw [←bit_to_nat, pbb] } }
  end

  @[simp] lemma lor_to_nat   : ∀ m n, (lor    m n : ℕ) = nat.lor    m n :=
  by apply bitwise_to_nat (λx y, ↑(pos_num.lor x y)); intros; try {cases a}; try {cases b}; refl
  @[simp] lemma land_to_nat  : ∀ m n, (land   m n : ℕ) = nat.land   m n :=
  by apply bitwise_to_nat pos_num.land; intros; try {cases a}; try {cases b}; refl
  @[simp] lemma ldiff_to_nat : ∀ m n, (ldiff  m n : ℕ) = nat.ldiff  m n :=
  by apply bitwise_to_nat pos_num.ldiff; intros; try {cases a}; try {cases b}; refl
  @[simp] lemma lxor_to_nat  : ∀ m n, (lxor   m n : ℕ) = nat.lxor   m n :=
  by apply bitwise_to_nat pos_num.lxor; intros; try {cases a}; try {cases b}; refl

  @[simp] lemma shiftl_to_nat (m n) : (shiftl m n : ℕ) = nat.shiftl m n :=
  begin
    cases m; dunfold shiftl, {symmetry, apply nat.zero_shiftl},
    induction n with n IH, {refl},
    simp [pos_num.shiftl, nat.shiftl_succ], rw ←IH, refl
  end

  @[simp] lemma shiftr_to_nat (m n) : (shiftr m n : ℕ) = nat.shiftr m n :=
  begin
    cases m with m; dunfold shiftr, {symmetry, apply nat.zero_shiftr},
    revert m; induction n with n IH; intro m, {cases m; refl},
    cases m with m m; dunfold pos_num.shiftr,
    { rw [nat.shiftr_eq_div_pow], symmetry, apply nat.div_eq_of_lt,
      exact @nat.pow_lt_pow_of_lt_right 2 dec_trivial 0 (n+1) (nat.succ_pos _) },
    { transitivity, apply IH,
      change nat.shiftr m n = nat.shiftr (bit1 m) (n+1),
      rw [add_comm n 1, nat.shiftr_add],
      apply congr_arg (λx, nat.shiftr x n), unfold nat.shiftr,
      change (bit1 ↑m : ℕ) with nat.bit tt m,
      rw nat.div2_bit },
    { transitivity, apply IH,
      change nat.shiftr m n = nat.shiftr (bit0 m) (n + 1),
      rw [add_comm n 1, nat.shiftr_add],
      apply congr_arg (λx, nat.shiftr x n), unfold nat.shiftr,
      change (bit0 ↑m : ℕ) with nat.bit ff m,
      rw nat.div2_bit }
  end

  @[simp] lemma test_bit_to_nat (m n) : test_bit m n = nat.test_bit m n :=
  begin
    cases m with m; unfold test_bit nat.test_bit,
    { change (zero : nat) with 0, rw nat.zero_shiftr, refl },
    revert m; induction n with n IH; intro m;
    cases m; dunfold pos_num.test_bit, {refl},
    { exact (nat.bodd_bit _ _).symm },
    { exact (nat.bodd_bit _ _).symm },
    { change ff = nat.bodd (nat.shiftr 1 (n + 1)),
      rw [add_comm, nat.shiftr_add], change nat.shiftr 1 1 with 0,
      rw nat.zero_shiftr; refl },
    { change pos_num.test_bit a n = nat.bodd (nat.shiftr (nat.bit tt a) (n + 1)),
      rw [add_comm, nat.shiftr_add], unfold nat.shiftr,
      rw nat.div2_bit, apply IH },
    { change pos_num.test_bit a n = nat.bodd (nat.shiftr (nat.bit ff a) (n + 1)),
      rw [add_comm, nat.shiftr_add], unfold nat.shiftr,
      rw nat.div2_bit, apply IH },
  end

end num
