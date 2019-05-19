/-
  Copyright (c) 2019 Seul Baek. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Seul Baek

  Second-order terms.
-/

import algebra.ordered_group
import tactic.spass.model
import tactic.spass.misc

universe u

variable {α : Type u}

open nat

local notation f `₀↦` a := assign a f

@[derive has_reflect, derive decidable_eq]
inductive term₂ : Type
| var : nat → term₂
| app : term₂ → term₂ → term₂

local notation `#`     := term₂.var
local notation a `&` b := term₂.app a b

namespace term₂

meta def to_expr : term₂ → expr
| (# k)   := `(# %%`(k))
| (t & s) := `(%%(t.to_expr) & %%(s.to_expr))

local notation `#`     := term₂.var
local notation a `&` b := term₂.app a b
def repr : term₂ → string
| (# k)   := "X" ++ k.to_subs
| (t & s) := "(" ++ t.repr ++ " " ++ s.repr ++ ")"

instance has_repr : has_repr term₂ := ⟨repr⟩

def incr_ge (k : nat) : term₂ → term₂
| (# m)   := if k ≤ m then # (m + 1) else # m
| (a & b) := a.incr_ge & b.incr_ge

def incr : term₂ → term₂ := incr_ge 0

def val (M : model α) : term₂ → value α
| (# k)   := M k
| (a & b) := a.val ∘ list.cons (b.val []).fst

end term₂

lemma incr_app (a b : term₂) :
  term₂.incr (a & b) = (a.incr & b.incr) :=
by simp only [ term₂.incr, and_self,
     term₂.incr_ge, eq_self_iff_true ]

namespace term₂

lemma val_assign_incr (M : model α) (v : value α) :
  ∀ a : term₂, val (M ₀↦ v) a.incr = val M a
| (# k)   := rfl
| (a & b) :=
  by simp only [val, val_assign_incr a,
     val_assign_incr b, incr_app]

def occ (k : nat) : term₂ → Prop
| (# m)   := k = m
| (a & b) := a.occ ∨ b.occ

lemma not_occ_incr_ge (k : nat) :
  ∀ a : term₂, ¬ (a.incr_ge k).occ k
| (# m)  :=
  begin
    unfold term₂.incr_ge,
    by_cases h1 : k ≤ m,
    { rw if_pos h1,
      unfold occ, intro h2,
      rw [h2, ← not_lt] at h1,
      exact (h1 $ lt_succ_self _) },
    rw if_neg h1,
    unfold occ, intro h2,
    rw h2 at h1,
    exact h1 (le_refl _)
  end
| (a & b) :=
  begin
    unfold term₂.incr_ge,
    intro h0, cases h0;
    apply not_occ_incr_ge _ h0
  end

end term₂

lemma eq_of_var_eq_var {k m : nat} : (# k) = (# m) → k = m :=
by {intro h0, cases h0, refl}

lemma val_incr_ge {M N : model α} {k : nat}
  (h0 : ∀ m < k, M m = N m) (h1 : ∀ m ≥ k, M (m + 1) = N m) :
    ∀ a : term₂, (a.incr_ge k).val M = a.val N
| (# m) :=
  begin
    unfold term₂.incr_ge,
    by_cases h2 : k ≤ m,
    { rw if_pos h2,
      apply h1 _ h2 },
    rw if_neg h2,
    rw not_le at h2,
    apply h0 _ h2
  end
| (a & b) :=
  by simp only [term₂.incr_ge, term₂.val, val_incr_ge]
