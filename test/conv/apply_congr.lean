/-
Copyright (c) 2019 Lucas Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucas Allen, Scott Morrison
-/

import algebra.big_operators.basic
import data.finsupp.basic
import tactic.converter.apply_congr
import tactic.interactive

example (f g : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = g m) :
  finset.sum S f = finset.sum S g :=
begin
  conv_lhs {
    -- If we just call `congr` here, in the second goal we're helpless,
    -- because we are only given the opportunity to rewrite `f`.

    -- However `apply_congr` uses the appropriate `@[congr]` lemma,
    -- so we get to rewrite `f x`, in the presence of the crucial `H : x ∈ S` hypothesis.
    apply_congr,
    skip,
    simp [h, H], }
end

-- Again, with some `guard` statements.
example (f g : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = g m) :
  finset.sum S f = finset.sum S g :=
begin
  conv_lhs {
    apply_congr finset.sum_congr,
    -- (See the note about get_goals/set_goals inside apply_congr)
    (do ng ← tactic.num_goals, guard $ ng = 2),
    guard_target S,
    skip,
    guard_target f x,
    simp [h, H] }
end

-- Verify we can `rw` as well as `simp`.
example (f g : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = g m) :
  finset.sum S f = finset.sum S g :=
by conv_lhs { apply_congr, skip, rw h x H, }

-- Check that the appropriate `@[congr]` lemma is automatically selected.
example (f g : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = g m) :
  finset.prod S f = finset.prod S g :=
by conv_lhs { apply_congr, skip, simp [h, H], }

example (f g : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = g m) :
  finset.fold (+) 0 f S = finset.fold (+) 0 g S :=
begin
  -- This time, the automatically selected congruence lemma is "too good"!
  -- `finset.sum_congr` matches, and so the `conv` block actually
  -- rewrites the left hand side into a `finset.sum`.
  conv_lhs { apply_congr, skip, simp [h, H], },
  -- So we need a `refl` to identify that we're done.
  refl,
end

-- This can be avoided by selecting the congruence lemma by hand.
example (f g : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = g m) :
  finset.fold (+) 0 f S = finset.fold (+) 0 g S :=
begin
  conv_lhs { apply_congr finset.fold_congr, simp [h, H], },
end

example (f : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = 0) :
  finset.sum S f = 0 :=
begin
  conv_lhs { apply_congr, skip, simp [h, H], },
  simp,
end

-- An example using `finsupp.sum`
open_locale classical

example {k G : Type} [semiring k] [group G]
  (g : G →₀ k) (a₁ x : G) (b₁ : k)
  (t : ∀ (a₂ : G), a₁ * a₂ = x ↔ a₁⁻¹ * x = a₂) :
  g.sum (λ (a₂ : G) (b₂ : k), ite (a₁ * a₂ = x) (b₁ * b₂) 0) = b₁ * g (a₁⁻¹ * x) :=
begin
  -- In fact, `congr` works fine here, because our rewrite works globally.
  conv_lhs { apply_congr, skip, dsimp, rw t, },
  rw finset.sum_ite_eq g.support, -- it's a pity we can't just use `simp` here.
  split_ifs,
  { refl, },
  { simp [finsupp.not_mem_support_iff.1 h], },
end

example : true :=
begin
  success_if_fail { conv { apply_congr, }, },
  trivial
end
