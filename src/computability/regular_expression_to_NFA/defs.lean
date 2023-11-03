/-
Copyright (c) 2022 Russell Emerine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Russell Emerine
-/
import computability.regular_expressions
import computability.NFA
import data.fintype.sum
import data.fintype.option

/-!
# Definitions for Converting Regular Expressions to NFA's

Definitions of the state types of NFA's corresponding to regular expressions, and some required
instances for those state types. Then, definitions of NFA's corresponding to regular expressions,
and some required instances for those NFA's.

This is based on the referenced link. The link uses ε-NFA's, but it was hard to deal with
ε-closures when proving things, so I used equivalent one-character transition NFA's instead.

## References

* <https://courses.engr.illinois.edu/cs373/sp2013/Lectures/lec07.pdf>
-/

universe u

variables {α : Type u} [dec : decidable_eq α]

namespace regular_expression

/--
The NFA state type for a particular regular expression.
-/
def state : regular_expression α → Type _
| zero := unit
| epsilon := unit
| (char _) := bool
| (plus r₁ r₂) := state r₁ ⊕ state r₂
| (comp r₁ r₂) := state r₁ ⊕ state r₂
| (star r) := option (state r)

instance {r : regular_expression α} : inhabited r.state :=
begin
  induction r,
  case zero { exact punit.inhabited, },
  case epsilon { exact punit.inhabited, },
  case char : a { exact bool.inhabited, },
  case plus : r₁ r₂ hr₁ hr₂ { exactI sum.inhabited_left, },
  case comp : r₁ r₂ hr₁ hr₂ { exactI sum.inhabited_left, },
  case star : r hr { exact option.inhabited _, },
end

-- NFAs are only real NFAs when the states are fintypes, and the instance is needed for the proofs
instance {r : regular_expression α} : fintype r.state :=
begin
  induction r,
  case zero { exact unit.fintype },
  case epsilon { exact unit.fintype, },
  case char : a { exact bool.fintype, },
  case plus : r₁ r₂ hr₁ hr₂ { exactI sum.fintype r₁.state r₂.state, },
  case comp : r₁ r₂ hr₁ hr₂ { exactI sum.fintype r₁.state r₂.state, },
  case star : r hr { exactI option.fintype, },
end

instance {r : regular_expression α} : decidable_eq r.state :=
begin
  induction r,
  case zero { exact punit.decidable_eq, },
  case epsilon { exact punit.decidable_eq, },
  case char { exact bool.decidable_eq, },
  case plus : r₁ r₂ hr₂ hr₂ { exactI sum.decidable_eq r₁.state r₂.state, },
  case comp : r₁ r₂ hr₂ hr₂ { exactI sum.decidable_eq r₁.state r₂.state, },
  case star : r hr { exactI option.decidable_eq, },
end

/--
Recursively converts a regular expression to its corresponding NFA.
-/
def to_NFA : Π (r : regular_expression α), NFA α r.state
| zero := ⟨(λ _ _ _, false), (λ _, false), (λ _, false)⟩
| epsilon := ⟨(λ _ _ _, false), (λ _, true), (λ _, true)⟩
| (char a) :=
  ⟨
    (λ p c q, p = ff ∧ a = c ∧ q = tt),
    (λ q, q = ff),
    (λ q, q = tt)
  ⟩
| (plus r₁ r₂) :=
  let P₁ := r₁.to_NFA in
  let P₂ := r₂.to_NFA in
  ⟨
    (λ p c q,
      match (p, q) with
      | (sum.inl p, sum.inl q) := P₁.step p c q
      | (sum.inl _, sum.inr _) := false
      | (sum.inr _, sum.inl _) := false
      | (sum.inr p, sum.inr q) := P₂.step p c q
      end),
    (λ q,
      match q with
      | sum.inl q := P₁.start q
      | sum.inr q := P₂.start q
      end),
    (λ q,
      match q with
      | sum.inl q := P₁.accept q
      | sum.inr q := P₂.accept q
      end)
  ⟩
| (comp r₁ r₂) :=
  let P₁ := r₁.to_NFA in
  let P₂ := r₂.to_NFA in
  ⟨
    (λ p c q,
      match (p, q) with
      | (sum.inl p, sum.inl q) := P₁.step p c q
      | (sum.inl p, sum.inr q) := P₂.start q ∧ (∃ r, P₁.accept r ∧ P₁.step p c r)
      | (sum.inr p, sum.inl q) := false
      | (sum.inr p, sum.inr q) := P₂.step p c q
      end),
    (λ q,
      match q with
      | sum.inl q := P₁.start q
      | sum.inr q := P₂.start q ∧ (∃ p, P₁.accept p ∧ P₁.start p)
      end),
    (λ q,
      match q with
      | sum.inl q := P₁.accept q ∧ (∃ p, P₂.accept p ∧ P₂.start p)
      | sum.inr q := P₂.accept q
      end)
  ⟩
| (star r) :=
  let P := r.to_NFA in
  ⟨
    (λ p c q,
      match (p, q) with
      | (some p, some q) := P.step p c q ∨ (∃ r, P.accept r ∧ P.step p c r ∧ P.start q)
      | (some p, none) := false
      | (none, some q) := false
      | (none, none) := false
      end),
    (λ q,
      match q with
      | some q := P.start q
      | none := true
      end),
    (λ q,
      match q with
      | some q := P.accept q
      | none := true
      end)
  ⟩

include dec

/--
All three functions in an NFA constructed from `to_NFA` are decidable. Since the functions rely on
each other, the class is proven here, and the instance declarations use this.
-/
def regular_expression_to_NFA_decidable {r : regular_expression α} :
  (∀ p a q, decidable (q ∈ r.to_NFA.step p a))
  × decidable_pred (r.to_NFA.start)
  × decidable_pred (r.to_NFA.accept) :=
begin
  induction r,
  case zero
  { refine ⟨_, _, _⟩,
    { assume _ _ _, exact decidable.false, },
    { assume q, exact decidable.false, },
    { assume q, exact decidable.false, }, },
  case epsilon
  { refine ⟨_, _, _⟩,
    { assume p a q, exact decidable.false, },
    { assume q, exact decidable.true, },
    { assume q, exact decidable.true, }, },
  case char : a
  { refine ⟨_, _, _⟩,
    { assume p c q, exact and.decidable, },
    { assume q, exact set.decidable_set_of ff (eq q), },
    { assume q, exact set.decidable_set_of tt (eq q), }, },
  case plus : r₁ r₂ hr₁ hr₂
  { rcases hr₁ with ⟨hr₁_step, hr₁_start, hr₁_accept⟩,
    rcases hr₂ with ⟨hr₂_step, hr₂_start, hr₂_accept⟩,
    refine ⟨_, _, _⟩,
    { assume p a q,
      cases p; cases q,
      case inl inl { exact hr₁_step p a q, },
      case inl inr { exact decidable.false, },
      case inr inl { exact decidable.false, },
      case inr inr { exact hr₂_step p a q, }, },
    { assume q,
      cases q,
      case inl { exact hr₁_start q, },
      case inr { exact hr₂_start q, }, },
    { assume q,
      cases q,
      case inl { exact hr₁_accept q, },
      case inr { exact hr₂_accept q, }, }, },
  case comp : r₁ r₂ hr₁ hr₂
  { rcases hr₁ with ⟨hr₁_step, hr₁_start, hr₁_accept⟩,
    rcases hr₂ with ⟨hr₂_step, hr₂_start, hr₂_accept⟩,
    refine ⟨_, _, _⟩,
    { assume p a q,
      cases p; cases q,
      case inl inl { exact hr₁_step p a q, },
      case inl inr
      { have : decidable (∃ (r : r₁.state), r₁.to_NFA.accept r ∧ r₁.to_NFA.step p a r),
        { have : decidable_pred (λ (r : r₁.state), r₁.to_NFA.accept r ∧ r₁.to_NFA.step p a r),
          { assume r,
            have : decidable (r₁.to_NFA.step p a r),
            { exact hr₁_step p a r, },
            exactI and.decidable, },
          exactI fintype.decidable_exists_fintype, },
        exactI and.decidable, },
      case inr inl { exact decidable.false, },
      case inr inr { exact hr₂_step p a q, }, },
    { assume q,
      cases q,
      case inl { exact hr₁_start q, },
      case inr { exactI and.decidable, }, },
    { assume q,
      cases q,
      case inl { exactI and.decidable, },
      case inr { exact hr₂_accept q, }, }, },
  case star : r hr
  { rcases hr with ⟨hr_step, hr_start, hr_accept⟩,
    refine ⟨_, _, _⟩,
    { assume p a q,
      cases p; cases q,
      case some some
      { have : decidable (r.to_NFA.step p a q),
        { exact hr_step p a q, },
        have :
          decidable
            (∃ (r_1 : r.state), r.to_NFA.accept r_1 ∧ r.to_NFA.step p a r_1 ∧ r.to_NFA.start q),
        { have :
            decidable_pred
              (λ (r_1 : r.state), r.to_NFA.accept r_1 ∧ r.to_NFA.step p a r_1 ∧ r.to_NFA.start q),
          { assume s,
            have : decidable (r.to_NFA.step p a s ∧ r.to_NFA.start q),
            { have : decidable (r.to_NFA.step p a s),
              { exact hr_step p a s, },
              exactI and.decidable, },
            exactI and.decidable, },
          exactI fintype.decidable_exists_fintype, },
        exactI or.decidable, },
      all_goals { exact decidable.false, }, },
    { assume q,
      cases q,
      case none { exact decidable.true, },
      case some { exact hr_start q, }, },
    { assume q,
      cases q,
      case none { exact decidable.true, },
      case some { exact hr_accept q, }, }, },
end

instance decidable_step {r : regular_expression α} {p a q} : decidable (r.to_NFA.step p a q) :=
  regular_expression_to_NFA_decidable.1 p a q

instance decidable_start {r : regular_expression α} : decidable_pred (r.to_NFA.start) :=
  regular_expression_to_NFA_decidable.2.1

instance decidable_accept {r : regular_expression α} : decidable_pred (r.to_NFA.accept) :=
  regular_expression_to_NFA_decidable.2.2

end regular_expression
