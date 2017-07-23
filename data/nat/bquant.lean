import data.nat.sub

open nat

def ball (n : nat) (P : nat → Prop) := ∀ k : ℕ, k < n → P k

  def ball' (n : nat) (P : Π (k : ℕ) (p : k < n), Prop) := Π (k : ℕ) (p : k < n), P k p

  theorem ball_zero (P : nat → Prop) : ball 0 P :=
  λ x Hlt, absurd Hlt (not_lt_zero _)

  theorem ball_zero' (P : Π (k : ℕ) (p : k < 0), Prop) : ball' 0 P :=
  λ k p, absurd p (not_lt_zero _)

  theorem ball_of_ball_succ {n : nat} {P : nat → Prop} (H : ball (succ n) P) : ball n P  :=
  λ x Hlt, H x (lt.step Hlt)

  def step_p {n : ℕ} (P : Π (k : ℕ) (p : k < succ n), Prop) : Π (k : ℕ) (p : k < n), Prop :=
    λ k p, P k (lt.step p)

  theorem ball_of_ball_succ' {n : nat} {P : Π (k : ℕ) (p : k < succ n), Prop} (H : ball' (succ n)  P) : ball' n (step_p P) :=
   λ x Hlt, H _ _

  theorem ball_succ_of_ball {n : nat} {P : nat → Prop} (H₁ : ball n P) (H₂ : P n) : ball (succ n) P :=
  λ (x : nat) (Hlt : x < succ n), or.elim (nat.eq_or_lt_of_le (le_of_succ_le_succ Hlt))
    (λ heq : x = n, (eq.symm heq) ▸ H₂)
    (λ hlt : x < n, H₁ x hlt)

  theorem not_ball_of_not {n : nat} {P : nat → Prop} (H₁ : ¬ P n) : ¬ ball (succ n) P :=
  λ (H : ball (succ n) P), absurd (H n (lt.base n)) H₁

  theorem not_ball_succ_of_not_ball {n : nat} {P : nat → Prop} (H₁ : ¬ ball n P) : ¬ ball (succ n) P :=
  λ (H : ball (succ n) P), absurd (ball_of_ball_succ H) H₁

  instance decidable_ball (n : nat) (P : nat → Prop) [H : decidable_pred P] : decidable (ball n P) :=
  nat.rec_on n
    (decidable.is_true (ball_zero P))
    (λ n₁ ih, decidable.rec_on ih
      (λ ih_neg, decidable.is_false (not_ball_succ_of_not_ball ih_neg))
      (λ ih_pos, decidable.rec_on (H n₁)
        (λ p_neg, decidable.is_false (not_ball_of_not p_neg))
        (λ p_pos, decidable.is_true (ball_succ_of_ball ih_pos p_pos))))

instance decidable_lo_hi (lo hi : nat) (P : nat → Prop) [H : decidable_pred P] : decidable (∀x, lo ≤ x → x < hi → P x) :=
suffices ball (hi - lo) (λx, P (lo + x)) ↔ (∀x, lo ≤ x → x < hi → P x), from
decidable_of_decidable_of_iff (by apply_instance) this,
⟨λal x hl hh, by have := al (x - lo) (lt_of_not_ge $
  (not_congr (nat.sub_le_sub_right_iff _ _ _ hl)).2 $ not_le_of_gt hh);
  rwa [nat.add_sub_of_le hl] at this,
λal x h, al _ (nat.le_add_right _ _) (by rw add_comm; exact nat.add_lt_of_lt_sub h)⟩
