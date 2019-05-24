/-
  Copyright (c) 2019 Seul Baek. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Seul Baek

  First-order constraint for variables.
  `fov k x` asserts that variable k is only used
  as a first-order variable in x. I.e., variable k
  never occurs at the head of a complex term.
-/

import tactic.vampire.form2

open nat

namespace vampire

local notation `#` := term₂.var
local notation a `&` b := term₂.app a b

local notation `⟪` b `,` a `⟫` := form₂.lit b a
local notation p `∨*` q        := form₂.bin tt p q
local notation p `∧*` q        := form₂.bin ff p q
local notation `∃*`            := form₂.qua tt
local notation `∀*`            := form₂.qua ff

namespace term₂

def fov_on (k : nat) : bool → term₂ → Prop
| ff (# m)   := k ≠ m
| tt (# _)   := true
| _  (a & b) := fov_on ff a ∧ fov_on tt b

instance fov_on.decidable {k : nat} :
  ∀ {b : bool} {t : term₂}, decidable (t.fov_on k b)
| ff (# m)   := by {unfold fov_on, apply_instance}
| tt (# m)   := decidable.true
| tt (a & b) := @and.decidable _ _ fov_on.decidable fov_on.decidable
| ff (a & b) := @and.decidable _ _ fov_on.decidable fov_on.decidable

def fov (k : nat) : term₂ → Prop := fov_on k ff

instance fov.decidable {k : nat} {p : term₂} : decidable (p.fov k) :=
by {unfold fov, apply_instance}

lemma fov_of_not_occ (k : nat) :
  ∀ a : term₂, ¬ a.occ k → fov k a
| (# m)   h0 := h0
| (a & (# m)) h0 :=
  ⟨fov_of_not_occ _ (λ h1, absurd (or.inl h1) h0), trivial⟩
| (a & (b & c)) h0 :=
  by { cases not_or_distrib.elim_left h0 with h1 h2,
       refine ⟨fov_of_not_occ _ h1, fov_of_not_occ _ h2⟩ }

lemma fov_app_var (k m : nat) (a : term₂) :
  fov k (a & (# m)) ↔ fov k a :=
by simp only [fov, fov_on, and_true]

lemma fov_incr_ge :
  ∀ {k m : nat} (a : term₂),
  m ≤ k → (fov (k + 1) (a.incr_ge m) ↔ fov k a)
| k m (# n) h0 :=
  begin
    unfold term₂.incr_ge,
    by_cases h2 : m ≤ n,
    { rw if_pos h2,
      apply not_iff_not_of_iff (nat.succ_eq_succ_iff _ _) },
    rw if_neg h2,
    have h3 : n < k,
    { rw not_le at h2,
      exact lt_of_lt_of_le h2 h0 },
    refine ⟨ λ _, ne_of_gt h3,
             λ _, ne_of_gt (lt_trans h3 $ lt_succ_self _) ⟩
  end
| k m (a & (# n)) h0 :=
  begin
    unfold term₂.incr_ge,
    by_cases h2 : m ≤ n;
    (`[rw if_pos h2] <|> `[rw if_neg h2]);
    `[ rw [fov_app_var, fov_app_var],
       apply fov_incr_ge a h0 ]
  end
| k m (a & (b & c)) h0 :=
  begin
    apply pred_mono_2,
    { apply fov_incr_ge a h0 },
    apply fov_incr_ge (b & c) h0
  end

lemma fov_incr_ge_of_lt {k m : nat} (h0 : k < m) :
  ∀ a : term₂, fov k a → fov k (a.incr_ge m)
| (# n) h1 :=
  begin
    unfold incr_ge,
    by_cases h2 : m ≤ n,
    { rw if_pos h2,
      apply ne_of_lt (lt_trans
        (lt_of_lt_of_le h0 h2) $ lt_succ_self _) },
    rw if_neg h2, exact h1
  end
| (a & (# n)) h1 :=
  begin
    unfold incr_ge,
    by_cases h2 : m ≤ n;
    (`[rw if_pos h2] <|> `[rw if_neg h2]);
    `[refine ⟨fov_incr_ge_of_lt _ h1.left, trivial⟩]
  end
| (a & (b & c)) h1 :=
  ⟨ fov_incr_ge_of_lt a h1.left,
    fov_incr_ge_of_lt (b & c) h1.right ⟩

end term₂

namespace form₂

def fov : nat → form₂ → Prop
| k ⟪b, a⟫           := a.fov k
| k (form₂.bin _ p q) := fov k p ∧ fov k q
| k (form₂.qua b p)   := fov (k + 1) p

lemma fov_of_not_occ :
  ∀ k : nat, ∀ p : form₂, ¬ p.occ k → p.fov k
| k (form₂.lit b a)   := term₂.fov_of_not_occ _ _
| k (form₂.bin b p q) :=
  by { intro h0,
       cases not_or_distrib.elim_left h0 with h1 h2,
       refine ⟨fov_of_not_occ _ _ h1, fov_of_not_occ _ _ h2⟩ }
| k (form₂.qua b p) := fov_of_not_occ (k + 1) _

lemma fov_incr_ge :
  ∀ {k m : nat} {p : form₂},
  m ≤ k → fov k p → fov (k + 1) (p.incr_ge m)
| k m ⟪b, a⟫ h0 h1 :=
  by { unfold fov at h1,
       rwa ← term₂.fov_incr_ge a h0 at h1 }
| k m (form₂.bin b p q) h0 h1 :=
  by { cases h1, constructor;
       apply fov_incr_ge h0;
       assumption }
| k m (form₂.qua b p) h0 h1 :=
  by { apply @fov_incr_ge (k + 1),
       exact succ_le_succ h0, exact h1 }

lemma fov_incr_ge_of_lt :
  ∀ {k m : nat} (h0 : k < m),
  ∀ p : form₂, fov k p → fov k (p.incr_ge m)
| k m h0 ⟪b, a⟫           := term₂.fov_incr_ge_of_lt h0 _
| k m h0 (form₂.bin _ p q) :=
  λ h1, ⟨ fov_incr_ge_of_lt h0 _ h1.left,
          fov_incr_ge_of_lt h0 _ h1.right ⟩
| k m h0 (form₂.qua b p)   :=
  fov_incr_ge_of_lt (succ_lt_succ h0) _

instance fov.decidable : ∀ {k : nat} {p : form₂}, decidable (p.fov k)
| k ⟪b, a⟫ := by {unfold fov, apply_instance}
| k (form₂.bin b p q):=
  @and.decidable _ _ fov.decidable fov.decidable
| k (form₂.qua b p) := @fov.decidable _ p

end form₂

def foq (ae : bool) : form₂ → Prop
| ⟪b, a⟫            := true
| (form₂.bin _ p q) := foq p ∧ foq q
| (form₂.qua b p)   := (ae = b → p.fov 0) ∧ foq p

instance foq.decidable (b : bool) : ∀ {p : form₂}, decidable (foq b p)
| ⟪b, a⟫            := decidable.true
| (form₂.bin _ p q) := @and.decidable _ _ foq.decidable foq.decidable
| (form₂.qua c p)   :=
  @and.decidable _ _
    (@implies.decidable _ _ (by apply_instance)
    form₂.fov.decidable) foq.decidable

lemma foq_incr_ge {b : bool} :
  ∀ {m : nat} {p : form₂},
  foq b p → foq b (p.incr_ge m)
| m ⟪b, a⟫           h0 := trivial
| m (form₂.bin b p q) h0 :=
  by { cases h0, constructor;
       apply foq_incr_ge; assumption }
| m (form₂.qua c p)   h0 :=
  begin
    constructor,
    { intro h1,
      apply form₂.fov_incr_ge_of_lt,
      { apply zero_lt_succ },
      apply h0.left h1 },
    exact foq_incr_ge h0.right
  end

lemma fov_incr {k : nat} {p : form₂} :
  p.fov k → p.incr.fov (k + 1):=
form₂.fov_incr_ge (nat.zero_le _)

lemma fov_neg : ∀ k : nat, ∀ p : form₂, p.neg.fov k ↔ p.fov k
| k ⟪b, a⟫           := by refl
| k (form₂.bin b p q) :=
  by simp only [form₂.fov, form₂.neg, fov_neg]
| k (form₂.qua b p)   :=
  by simp only [form₂.fov, form₂.neg, fov_neg]

end vampire
