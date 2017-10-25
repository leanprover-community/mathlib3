/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

Properties of the binary representation of integers.
-/
import data.num.basic data.num.bitwise algebra.order tactic.interactive logic.basic data.option

meta def unfold_coe : tactic unit :=
`[unfold coe lift_t has_lift_t.lift coe_t has_coe_t.coe coe_b has_coe.coe]

namespace pos_num
  variables {α : Type*}

  theorem bit_to_nat (b n) : (bit b n : ℕ) = nat.bit b n :=
  by cases b; refl

  theorem add_one (n : pos_num) : n + 1 = succ n := by cases n; refl
  theorem one_add (n : pos_num) : 1 + n = succ n := by cases n; refl

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

  theorem cast_one [has_zero α] [has_one α] [has_add α] : ((1 : pos_num) : α) = 1 := rfl

  theorem cast_add_one_comm [add_monoid α] [has_one α] (n : pos_num) :
    (n + 1 : α) = 1 + n :=
  begin
    have : ∀ {p : pos_num}, (p + 1 : α) = 1 + p → (↑p + ↑p + 1 : α) = 1 + (↑p + ↑p),
    { intros p IH, rw [add_assoc, IH, ← add_assoc, IH, add_assoc] },
    induction n with p IH p IH, {refl},
    { show (↑p + ↑p + 1 + 1 : α) = 1 + (↑p + ↑p + 1),
      rw [← add_assoc (1:α), this IH] },
    { apply this IH }
  end

  theorem cast_add_comm_lemma_1 [add_monoid α] [has_one α] {a b : α} (h : a + b = b + a) :
    (a + a) + (b + b) = (b + b) + (a + a) :=
  by rw [add_assoc, ← add_assoc a b, h, add_assoc, ← add_assoc, h,
          add_assoc, ← add_assoc a, h, add_assoc, ← add_assoc]

  theorem cast_add_comm_lemma_2 [add_monoid α] [has_one α] {a b : α} (h : a + b = b + a)
    (h₂ : a + a + 1 = 1 + (a + a)) : (a + a) + (b + b + 1) = (b + b + 1) + (a + a) :=
  by rw [← add_assoc, cast_add_comm_lemma_1 h, add_assoc, h₂, ← add_assoc]

  theorem cast_add_comm [add_monoid α] [has_one α] : ∀ m n : pos_num, (m + n : α) = n + m 
  | 1        b        := (cast_add_one_comm b).symm
  | a        1        := cast_add_one_comm a
  | (bit0 a) (bit0 b) := cast_add_comm_lemma_1 (cast_add_comm a b)
  | (bit0 a) (bit1 b) := cast_add_comm_lemma_2 (cast_add_comm a b) (cast_add_one_comm (bit0 a))
  | (bit1 a) (bit0 b) := (cast_add_comm_lemma_2 (cast_add_comm a b).symm (cast_add_one_comm (bit0 b))).symm
  | (bit1 a) (bit1 b) := show ((a + a + 1) + (b + b + 1) : α) = (b + b + 1) + (a + a + 1),
    by rw [add_assoc, ← show (b + b + 1 + 1 : α) = 1 + (b + b + 1), from cast_add_one_comm (bit1 b),
            ← add_assoc, cast_add_comm_lemma_2 (cast_add_comm a b) (cast_add_one_comm (bit0 a)), add_assoc]

  theorem cast_succ [add_monoid α] [has_one α] : ∀ n, (succ n : α) = n + 1
  | 1        := rfl
  | (bit0 p) := rfl
  | (bit1 p) := (congr_arg _root_.bit0 (cast_succ p)).trans $
    show (↑p + 1 + (↑p + 1) : α) = ↑p + ↑p + 1 + 1,
    by rw [add_assoc, ← add_assoc (1:α), ← cast_add_one_comm]; simp 

  theorem cast_add [add_monoid α] [has_one α] : ∀ m n, ((m + n : pos_num) : α) = m + n
  | 1        b        := by rw [one_add b, cast_succ, cast_add_one_comm]; refl
  | a        1        := by rw [add_one a, cast_succ]; refl
  | (bit0 a) (bit0 b) := (congr_arg _root_.bit0 (cast_add a b)).trans $
    show ((a + b) + (a + b) : α) = (a + a) + (b + b),
    by rw [add_assoc, ← add_assoc ↑b, ← cast_add_comm a b]; simp
  | (bit0 a) (bit1 b) := (congr_arg _root_.bit1 (cast_add a b)).trans $
    show ((a + b) + (a + b) + 1 : α) = (a + a) + (b + b + 1),
    by rw [add_assoc ↑a, ← add_assoc ↑b, ← cast_add_comm a b]; simp
  | (bit1 a) (bit0 b) := (congr_arg _root_.bit1 (cast_add a b)).trans $
    calc ((a + b) + (a + b) + 1 : α)
          = a + (b + a) + (b + 1) : by simp
      ... = a + (a + b + 1) + b   : by rw [cast_add_comm, cast_add_one_comm]; simp
      ... = (a + a + 1) + (b + b) : by rw [add_assoc ↑a ↑b, cast_add_one_comm]; simp
  | (bit1 a) (bit1 b) :=
    calc (succ (a + b) + succ (a + b) : α)
          = a + (b + 1 + a) + b + 1  : by rw [cast_succ, cast_add]; simp
      ... = a + (a + 1 + b) + b + 1  : by rw [cast_add_one_comm, add_assoc (1:α),
            cast_add_comm, ← add_assoc (1:α), cast_add_one_comm]
      ... = (a + a + 1) + (b + b + 1) : by simp

  theorem one_le_cast [linear_ordered_semiring α] : ∀ n : pos_num, (1 : α) ≤ n
  | 1        := le_refl _
  | (bit0 p) := let h := one_le_cast p in
    le_trans (le_add_of_nonneg_left zero_le_one) (add_le_add h h)
  | (bit1 p) := let h := le_trans zero_le_one $ one_le_cast p in
    le_add_of_nonneg_left (add_nonneg h h)

  theorem cast_pos [linear_ordered_semiring α] (n : pos_num) : (n : α) > 0 :=
  lt_of_lt_of_le zero_lt_one (one_le_cast n)

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
        rw [←nat.succ_pred_eq_of_pos (cast_pos q), IH],
        generalize : nat.pred q = n,
        simp [_root_.bit1, _root_.bit0]
      end
    end

  theorem cast_mul [semiring α] (m) : ∀ n, ((m * n : pos_num) : α) = m * n
  | 1        := (mul_one _).symm
  | (bit0 p) := show (↑(m * p) + ↑(m * p) : α) = ↑m * (p + p), by rw [cast_mul, left_distrib]
  | (bit1 p) := (cast_add (bit0 (m * p)) m).trans $
    show (↑(m * p) + ↑(m * p) + m : α) = ↑m * (p + p + 1),
    by rw [cast_mul, left_distrib _ _ (1:α), mul_one, left_distrib]

  theorem cmp_swap (m) : ∀n, (cmp m n).swap = cmp n m :=
  by induction m with m IH m IH; intro n;
     cases n with n n; try {unfold cmp}; try {refl}; rw ←IH; cases cmp m n; refl

  theorem cast_cmp' [linear_ordered_semiring α] : ∀ (m n),
    (ordering.cases_on (cmp m n) ((m + 1 : α) ≤ n) (m = n) ((n + 1 : α) ≤ m) : Prop)
  | 1        1        := rfl
  | (bit0 a) 1        := add_le_add (one_le_cast _) (one_le_cast _)
  | (bit1 a) 1        := le_add_of_le_of_nonneg (add_le_add (one_le_cast _) (one_le_cast _)) zero_le_one
  | 1        (bit0 b) := add_le_add (one_le_cast _) (one_le_cast _)
  | 1        (bit1 b) := le_add_of_le_of_nonneg (add_le_add (one_le_cast _) (one_le_cast _)) zero_le_one
  | (bit0 a) (bit0 b) := begin
      have := cast_cmp' a b, revert this, cases cmp a b; dsimp; intro,
      { have := add_le_add (le_trans (le_add_of_nonneg_right zero_le_one) this) this,
        by rwa ← add_assoc at this },
      { rw this },
      { have := add_le_add (le_trans (le_add_of_nonneg_right zero_le_one) this) this,
        by rwa ← add_assoc at this }
    end
  | (bit0 a) (bit1 b) := begin dsimp [cmp],
      have := cast_cmp' a b, revert this, cases cmp a b; dsimp; intro,
      { have := le_trans (le_add_of_nonneg_right zero_le_one) this,
        exact add_le_add_right (add_le_add this this) _ },
      { rw this, refl },
      { have := add_le_add this this,
        by rwa [← add_assoc, add_right_comm ↑b] at this }
    end
  | (bit1 a) (bit0 b) := begin dsimp [cmp],
      have := cast_cmp' a b, revert this, cases cmp a b; dsimp; intro,
      { have := add_le_add this this,
        by rwa [← add_assoc, add_right_comm ↑a] at this },
      { rw this, refl },
      { have := le_trans (le_add_of_nonneg_right zero_le_one) this,
        exact add_le_add_right (add_le_add this this) _ },
    end
  | (bit1 a) (bit1 b) := begin
      have := cast_cmp' a b, revert this, cases cmp a b; dsimp; intro,
      { apply add_le_add_right,
        have := add_le_add (le_trans (le_add_of_nonneg_right zero_le_one) this) this,
        by rwa ← add_assoc at this },
      { rw this },
      { apply add_le_add_right,
        have := add_le_add (le_trans (le_add_of_nonneg_right zero_le_one) this) this,
        by rwa ← add_assoc at this }
    end

  theorem cast_cmp [linear_ordered_semiring α] (m n) : (ordering.cases_on (cmp m n) ((m:α) < n) (m = n) ((m:α) > n) : Prop) :=
  match cmp m n, cast_cmp' m n with
  | ordering.lt := lt_of_lt_of_le (lt_add_of_pos_right _ zero_lt_one)
  | ordering.eq := id
  | ordering.gt := lt_of_lt_of_le (lt_add_of_pos_right _ zero_lt_one)
  end

  theorem cmp_eq (m n) : cmp m n = ordering.eq ↔ m = n :=
  begin
    have := @cast_cmp ℕ _ m n,
    cases cmp m n; simp at this ⊢; try {exact this};
    { simp [show m ≠ n, from λ e, by rw e at this; exact lt_irrefl _ this],
      exact dec_trivial }
  end

  theorem cast_lt [linear_ordered_semiring α] {m n : pos_num} : (m:α) < n ↔ m < n :=
  show (m:α) < n ↔ cmp m n = ordering.lt, begin
    have := @cast_cmp α _ m n,
    cases cmp m n; dsimp [(>)] at this,
    { simp [this] },
    { simp [this, lt_irrefl], exact dec_trivial },
    { simp [not_lt_of_gt this], exact dec_trivial }
  end

  theorem cast_le [linear_ordered_semiring α] {m n : pos_num} : (m:α) ≤ n ↔ m ≤ n :=
  by rw ← not_lt; exact not_congr cast_lt

  theorem cast_inj [linear_ordered_semiring α] {m n : pos_num} : (m:α) = n ↔ m = n :=
  by rw [le_antisymm_iff, cast_le, cast_le, ← cmp_eq]; dsimp [(≤), (<)];
     rw ← cmp_swap m n; cases cmp m n; exact dec_trivial

end pos_num

namespace num
  variables {α : Type*}
  open pos_num

  theorem cast_zero [has_zero α] [has_one α] [has_add α] :
    ((0 : num) : α) = 0 := rfl

  theorem cast_one [has_zero α] [has_one α] [has_add α] :
    ((1 : num) : α) = 1 := rfl

  theorem bit_to_nat (b n) : (bit b n : ℕ) = nat.bit b n :=
  by cases b; cases n; refl

  theorem cast_add [add_monoid α] [has_one α] : ∀ m n, ((m + n : num) : α) = m + n
  | 0       0       := (zero_add _).symm
  | 0       (pos q) := (zero_add _).symm
  | (pos p) 0       := (add_zero _).symm
  | (pos p) (pos q) := pos_num.cast_add _ _

  theorem add_zero (n : num) : n + 0 = n := by cases n; refl
  theorem zero_add (n : num) : 0 + n = n := by cases n; refl

  theorem add_succ : ∀ (m n : num), m + succ n = succ (m + n)
  | 0       n       := by simp [zero_add]
  | (pos p) 0       := show pos (p + 1) = succ (pos p + 0), by rw [add_one, add_zero]; refl
  | (pos p) (pos q) := congr_arg pos (pos_num.add_succ _ _)

  theorem cast_succ' [add_monoid α] [has_one α] : ∀ n, (succ' n : α) = n + 1
  | 0       := (_root_.zero_add _).symm
  | (pos p) := pos_num.cast_succ _

  theorem cast_succ [add_monoid α] [has_one α] (n) : (succ n : α) = n + 1 := cast_succ' n

  @[simp] theorem to_of_nat : Π (n : ℕ), ((n : num) : ℕ) = n
  | 0     := rfl
  | (n+1) := (cast_succ (num.of_nat n)).trans (congr_arg nat.succ (to_of_nat n))

  theorem of_nat_inj : ∀ {m n : ℕ}, (m : num) = n → m = n :=
  function.injective_of_left_inverse to_of_nat

  theorem add_of_nat (m) : ∀ n, ((m + n : ℕ) : num) = m + n
  | 0     := (add_zero _).symm
  | (n+1) := show succ (m + n : ℕ) = m + succ n,
             by rw [add_succ, add_of_nat]

  theorem cast_mul [semiring α] : ∀ m n, ((m * n : num) : α) = m * n
  | 0       0       := (zero_mul _).symm
  | 0       (pos q) := (zero_mul _).symm
  | (pos p) 0       := (mul_zero _).symm
  | (pos p) (pos q) := pos_num.cast_mul _ _

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

  theorem to_nat_inj {m n : pos_num} : (m : ℕ) = n → m = n := cast_inj.1

  theorem pred_to_nat {n : pos_num} (h : n > 1) : (pred n : ℕ) = nat.pred n :=
  begin
    unfold pred,
    have := pred'_to_nat n, revert this,
    cases pred' n; dsimp [option.get_or_else],
    { intro this, rw @to_nat_inj n 1 this at h,
      exact absurd h dec_trivial },
    { exact id }
  end

  theorem lt_iff_cmp {m n} : m < n ↔ cmp m n = ordering.lt := iff.rfl

  theorem le_iff_cmp {m n} : m ≤ n ↔ cmp m n ≠ ordering.gt :=
  not_congr $ lt_iff_cmp.trans $
  by rw ← cmp_swap; cases cmp m n; exact dec_trivial

  meta def transfer_rw : tactic unit :=
  `[repeat {rw ← @cast_inj ℕ <|> rw ← @cast_lt ℕ <|> rw ← @cast_le ℕ},
    repeat {rw cast_add <|> rw cast_mul <|> rw cast_one <|> rw cast_zero}]

  meta def transfer : tactic unit := `[intros, transfer_rw, try {simp}]

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

  instance : decidable_linear_order pos_num :=
  { lt              := (<),
    lt_iff_le_not_le := by {intros a b, transfer_rw, apply lt_iff_le_not_le},
    le              := (≤),
    le_refl         := by transfer,
    le_trans        := by {intros a b c, transfer_rw, apply le_trans},
    le_antisymm     := by {intros a b, transfer_rw, apply le_antisymm},
    le_total        := by {intros a b, transfer_rw, apply le_total},
    decidable_lt    := by apply_instance,
    decidable_le    := by apply_instance,
    decidable_eq    := by apply_instance }

end pos_num

namespace num
  variables {α : Type*}
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

  theorem cast_cmp' [linear_ordered_semiring α] : ∀ (m n),
    (ordering.cases_on (cmp m n) ((m + 1 : α) ≤ n) (m = n) ((n + 1 : α) ≤ m) : Prop)
  | 0       0       := rfl
  | 0       (pos b) := by have := one_le_cast b; rwa ← _root_.zero_add (1:α) at this
  | (pos a) 0       := by have := one_le_cast a; rwa ← _root_.zero_add (1:α) at this
  | (pos a) (pos b) :=
    by { have := pos_num.cast_cmp' a b, revert this; dsimp [cmp];
         cases pos_num.cmp a b, exacts [id, congr_arg pos, id] }

  theorem cast_cmp [linear_ordered_semiring α] (m n) : (ordering.cases_on (cmp m n) ((m:α) < n) (m = n) ((m:α) > n) : Prop) :=
  match cmp m n, cast_cmp' m n with
  | ordering.lt := lt_of_lt_of_le (lt_add_of_pos_right _ zero_lt_one)
  | ordering.eq := id
  | ordering.gt := lt_of_lt_of_le (lt_add_of_pos_right _ zero_lt_one)
  end

  theorem cmp_eq (m n) : cmp m n = ordering.eq ↔ m = n :=
  begin
    have := @cast_cmp ℕ _ m n,
    cases cmp m n; simp at this ⊢; try {exact this};
    { simp [show m ≠ n, from λ e, by rw e at this; exact lt_irrefl _ this],
      exact dec_trivial }
  end

  theorem cast_lt [linear_ordered_semiring α] {m n : num} : (m:α) < n ↔ m < n :=
  show (m:α) < n ↔ cmp m n = ordering.lt, begin
    have := @cast_cmp α _ m n,
    cases cmp m n; dsimp [(>)] at this,
    { simp [this] },
    { simp [this, lt_irrefl], exact dec_trivial },
    { simp [not_lt_of_gt this], exact dec_trivial }
  end

  theorem cast_le [linear_ordered_semiring α] {m n : num} : (m:α) ≤ n ↔ m ≤ n :=
  by rw ← not_lt; exact not_congr cast_lt

  theorem cast_inj [linear_ordered_semiring α] {m n : num} : (m:α) = n ↔ m = n :=
  by rw [le_antisymm_iff, cast_le, cast_le, ← cmp_eq]; dsimp [(≤), (<)];
     rw ← cmp_swap m n; cases cmp m n; exact dec_trivial

  theorem lt_iff_cmp {m n} : m < n ↔ cmp m n = ordering.lt := iff.rfl

  theorem le_iff_cmp {m n} : m ≤ n ↔ cmp m n ≠ ordering.gt :=
  not_congr $ lt_iff_cmp.trans $
  by rw ← cmp_swap; cases cmp m n; exact dec_trivial

  meta def transfer_rw : tactic unit :=
  `[repeat {rw ← @cast_inj ℕ <|> rw ← @cast_lt ℕ <|> rw ← @cast_le ℕ},
    repeat {rw cast_add <|> rw cast_mul <|> rw cast_one <|> rw cast_zero}]

  meta def transfer : tactic unit := `[intros, transfer_rw, try {simp}]

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
    add_left_cancel            := by {intros a b c, transfer_rw, apply add_left_cancel},
    add_right_cancel           := by {intros a b c, transfer_rw, apply add_right_cancel},
    lt                         := (<),
    lt_iff_le_not_le           := by {intros a b, transfer_rw, apply lt_iff_le_not_le},
    le                         := (≤),
    le_refl                    := by transfer,
    le_trans                   := by {intros a b c, transfer_rw, apply le_trans},
    le_antisymm                := by {intros a b, transfer_rw, apply le_antisymm},
    le_total                   := by {intros a b, transfer_rw, apply le_total},
    add_le_add_left            := by {intros a b h c, revert h, transfer_rw, exact λ h, add_le_add_left h c},
    le_of_add_le_add_left      := by {intros a b c, transfer_rw, apply le_of_add_le_add_left},
    zero_lt_one                := dec_trivial,
    mul_le_mul_of_nonneg_left  := by {intros a b c, transfer_rw, apply mul_le_mul_of_nonneg_left},
    mul_le_mul_of_nonneg_right := by {intros a b c, transfer_rw, apply mul_le_mul_of_nonneg_right},
    mul_lt_mul_of_pos_left     := by {intros a b c, transfer_rw, apply mul_lt_mul_of_pos_left},
    mul_lt_mul_of_pos_right    := by {intros a b c, transfer_rw, apply mul_lt_mul_of_pos_right},
    decidable_lt               := num.decidable_lt,
    decidable_le               := num.decidable_le,
    decidable_eq               := num.decidable_eq }

  theorem bitwise_to_nat {f : num → num → num} {g : bool → bool → bool}
    (p : pos_num → pos_num → num)
    (gff : g ff ff = ff)
    (f00 : f 0 0 = 0)
    (f0n : ∀ n, f 0 (pos n) = cond (g ff tt) (pos n) 0)
    (fn0 : ∀ n, f (pos n) 0 = cond (g tt ff) (pos n) 0)
    (fnn : ∀ m n, f (pos m) (pos n) = p m n)
    (p11 : p 1 1 = cond (g tt tt) 1 0)
    (p1b : ∀ b n, p 1 (pos_num.bit b n) = bit (g tt b) (cond (g ff tt) (pos n) 0))
    (pb1 : ∀ a m, p (pos_num.bit a m) 1 = bit (g a tt) (cond (g tt ff) (pos m) 0))
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
    { rw fnn,
      have : ∀b (n : pos_num), (cond b ↑n 0 : ℕ) = ↑(cond b (pos n) 0 : num) :=
        by intros; cases b; refl,
      induction m with m IH m IH generalizing n; cases n with n n,
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
      any_goals { rw [nat.bitwise_zero_left, this, ← bit_to_nat, p1b] },
      any_goals { rw [nat.bitwise_zero_right _ gff, this, ← bit_to_nat, pb1] },
      all_goals { rw [← show ∀ n, ↑(p m n) = nat.bitwise g ↑m ↑n, from IH],
        rw [← bit_to_nat, pbb] } }
  end

  @[simp] theorem lor_to_nat   : ∀ m n, (lor    m n : ℕ) = nat.lor    m n :=
  by apply bitwise_to_nat (λx y, pos (pos_num.lor x y)); intros; try {cases a}; try {cases b}; refl
  @[simp] theorem land_to_nat  : ∀ m n, (land   m n : ℕ) = nat.land   m n :=
  by apply bitwise_to_nat pos_num.land; intros; try {cases a}; try {cases b}; refl
  @[simp] theorem ldiff_to_nat : ∀ m n, (ldiff  m n : ℕ) = nat.ldiff  m n :=
  by apply bitwise_to_nat pos_num.ldiff; intros; try {cases a}; try {cases b}; refl
  @[simp] theorem lxor_to_nat  : ∀ m n, (lxor   m n : ℕ) = nat.lxor   m n :=
  by apply bitwise_to_nat pos_num.lxor; intros; try {cases a}; try {cases b}; refl

  @[simp] theorem shiftl_to_nat (m n) : (shiftl m n : ℕ) = nat.shiftl m n :=
  begin
    cases m; dunfold shiftl, {symmetry, apply nat.zero_shiftl},
    induction n with n IH, {refl},
    simp [pos_num.shiftl, nat.shiftl_succ], rw ←IH, refl
  end

  @[simp] theorem shiftr_to_nat (m n) : (shiftr m n : ℕ) = nat.shiftr m n :=
  begin
    cases m with m; dunfold shiftr, {symmetry, apply nat.zero_shiftr},
    induction n with n IH generalizing m, {cases m; refl},
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

  @[simp] theorem test_bit_to_nat (m n) : test_bit m n = nat.test_bit m n :=
  begin
    cases m with m; unfold test_bit nat.test_bit,
    { change (zero : nat) with 0, rw nat.zero_shiftr, refl },
    induction n with n IH generalizing m;
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

namespace znum
  variables {α : Type*}
  open pos_num

  theorem cast_zero [has_zero α] [has_one α] [has_add α] [has_neg α] :
    ((0 : znum) : α) = 0 := rfl

  theorem cast_one [has_zero α] [has_one α] [has_add α] [has_neg α] :
    ((1 : znum) : α) = 1 := rfl

end znum