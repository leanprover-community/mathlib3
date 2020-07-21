/-
Lean for the Curious Mathematician
Tuesday, July 14, 2020
13:00 session
Happy Bastille Day!
-/

import data.real.basic

/-! ## Logic -/

/-!
### Agenda

- a quick overview of Lean's tactics for dealing with logical connectives
- continue with Patrick Massot's tutorial

After the overview, I will ask you to tell us how far you have gotten in the
tutorial (by file number), so we can group you in rooms accordingly. (Tutors,
please self identify as well!)

An apology:

In this presentation, I won't tell you anything you don't already know.

For example, I will say:

"To prove 'A and B', is suffices to prove A and then to prove B."

"If you know 'A and B', you can use A and you can use B."

The point is, to communicate these intentions to Lean, we have to give names
to these actions.

Analogies:

- Learning grammar.
- Learning Latex.

Other resources:

- Everything I go over here is in the tutorial.
- It is also in *Mathematics in Lean*.
- *Theorem Proving in Lean* has a more foundational, logician's perspective.
- See also the cheat sheet:

    https://leanprover-community.github.io//img/lean-tactics.pdf

You can find links to all of these (including the cheat sheet) on the mathlib
web pages, under "Learning resources."

This file is in the LFTCM repository.

Most of the examples here are from *Mathematics in Lean*.
-/

/-!
### Overview

The list:

→       \to, \r       if ... then         implication
∀       \all          for all             universal quantifier
∃       \ex           there exists        existential quantifier
¬       \not, \n      not                 negation
∧       \and          and                 conjunction
↔       \iff, \lr     if and only if      bi-implication
∨       \or           or                  disjunction
false                 contradiction       falsity
true                  this is trivial!    truth

Remember that a goal in Lean is of the form

  1 goal
  x y : ℕ,
  h₁ : prime x,
  h₂ : ¬even x,
  h₃ : y > x
  ⊢ y ≥ 4

The stuff before the `⊢` is called the *context*, or *local context*. The facts
there are called *hypotheses* or *local hypotheses*.

The stuff after the `⊢` is also called the *goal*, or the *target*.

A common theme:

- Some tactics tell us how to *prove* a goal involving the connective.
  (Logician's terminology: "introduce" the connective.)

- Some tactics tell us how to *use* a hypothesis involving the connective.
  (Logician's terminology: "eliminate" the connective.)

Summary:

→       if ... then       `intro`, `intros`     `apply`, `have h₃ := h₁ h₂`
∀       for all           `intro`, `intros`     `apply`, `specialize`,
                                                  `have h₂ := h₁ t`
∃       there exists      `use`                 `cases`
¬       not               `intro`, `intros`     `apply`, `contradiction`
∧       and               `split`               `cases`, `h.1` / `h.2`,
                                                  `h.left` / `h.right`
↔       if and only if    `split`               `cases`, `h.1` / `h.2`,
                                                  `h.mp` / `h.mpr`, `rw`
∨       or                `left` / `right`      `cases`
false   contradiction                           `contradiction`, `ex_falso`
true    this is trivial!  `trivial`

Also, for proof by contradiction:

  Use `open_locale classical` (but not right after the `import`s.)
  Use the `by_contradiction` tactic.

There are lots of other tactics and methods. But these are all you need to deal
with the logical connectives.

Another theme: sometimes the logical structure is hidden under a definition.
For example:

  `x ∣ y`   is existential
  `s ⊆ t`   is universal

Lean will unfold definitions as needed.
-/

/-!
### Implication and the universal quantifier
-/

section

variables   a b c d : ℝ
variable    h₁ : a ≤ b
variables   h₂ : c ≤ d

#check @add_le_add
#check @add_le_add _ _ a b
#check @add_le_add _ _ a b c d h₁
#check add_le_add h₁

include h₁ h₂

-- demonstrate variations on `apply` and `have`

example : a + c ≤ b + d :=
sorry

end

section

def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a

variables {f g : ℝ → ℝ} {a b : ℝ}

-- demonstrate variations on `apply`, `have`, and `specialize`
-- `dsimp` helps clarify the goal

theorem fn_ub_add (hfa : fn_ub f a) (hgb : fn_ub g b) :
  fn_ub (λ x, f x + g x) (a + b) :=
sorry

end

/-!
### The existential quantifier
-/

-- demonstrate `use` and `norm_num`

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
sorry

-- demonstrate `cases` and `use`, and use `fn_ub_add`

section

def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a

variables {f g : ℝ → ℝ}

example (ubf : fn_has_ub f) (ubg : fn_has_ub g) :
  fn_has_ub (λ x, f x + g x) :=
sorry

end

/-!
### Negation
-/

section

variable {f : ℝ → ℝ}

example (h : ∀ a, ∃ x, f x > a) : ¬ fn_has_ub f :=
sorry

end

/-!
### Conjunction
-/

section

variables {x y : ℝ}

-- demonstrate `split`

example (h₀ : x ≤ y) (h₁ : ¬ y ≤ x) : x ≤ y ∧ x ≠ y :=
sorry

-- demonstrate `cases`, `h.1`, `h.2`

example (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x :=
sorry

end

/-!
### Disjunction
-/

section

variables x y : ℝ

#check le_or_gt 0 y
#check @abs_of_nonneg
#check @abs_of_neg

example : x < abs y → x < y ∨ x < -y :=
sorry

end

/-!
### Final note

I haven't done everything! In particular, I skipped bi-implication, `true`, `false`,
proof by contradiction, and more.

But this should get you started, and you can consult the resources for more.
-/

