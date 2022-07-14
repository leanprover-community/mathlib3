import data.real.basic
import data.nat.prime

/-
Our goal now is to talk about how to handle logical connectives.

I will say things like:

"To prove 'A and B', is suffices to prove A and then to prove B."

"If you know 'A and B', you can use A and you can use B."

The point is, to communicate these intentions to Lean, we have to give names to these actions.

Analogies:

- Learning grammar.
- Learning Latex.

Everything I go over here is in *Mathematics in Lean*. See also the cheat sheet:

  https://leanprover-community.github.io//img/lean-tactics.pdf

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

  Use `open_locale classical`.
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

theorem my_add_le_add (x y z w : ℝ) (h₁ : x ≤ y) (h₂ : z ≤ w) :
  x + z ≤ y + w := add_le_add h₁ h₂

section
variables   a b c d : ℝ
variable    h₁ : a ≤ b
variables   h₂ : c ≤ d

#check my_add_le_add
#check my_add_le_add a b
#check my_add_le_add a b c d h₁
#check my_add_le_add _ _ _ _ h₁
#check my_add_le_add _ _ _ _ h₁ h₂
end

theorem my_add_le_add' {x y z w : ℝ} (h₁ : x ≤ y) (h₂ : z ≤ w) :
  x + z ≤ y + w := add_le_add h₁ h₂

section
variables   a b c d : ℝ
variable    h₁ : a ≤ b
variables   h₂ : c ≤ d

#check my_add_le_add'
#check my_add_le_add' h₁
#check my_add_le_add' h₁ h₂
end

def fn_ub (f : ℝ → ℝ) (a : ℝ) := ∀ x, f x ≤ a

section

variables {f g : ℝ → ℝ} {a b : ℝ}

-- demonstrate variations on `apply`, `have`, and `specialize`
-- `dsimp` helps clarify the goal

theorem fn_ub_add (hfa : fn_ub f a) (hgb : fn_ub g b) :
  fn_ub (f + g) (a + b) :=
begin
  intro x,
  specialize hfa x,
  specialize hgb x,
  exact add_le_add hfa hgb,
end















/-!
### The existential quantifier
-/

-- demonstrate `use` and `norm_num`

theorem foo : ∃ x : ℝ, 2 < x ∧ x < 3 :=
begin
  use 2.5,
  norm_num,
end

-- set_option pp.notation false

example : 5 ∣ 20 :=
begin
--  use 4,
  norm_num,
end

-- demonstrate `cases` and `use`, and use `fn_ub_add`

section

def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a

variables {f g : ℝ → ℝ}



example (ubf : fn_has_ub f) (ubg : fn_has_ub g) :
  fn_has_ub (f + g) :=
begin
  cases ubf with a ha,
  cases ubg with c hc,
  use a + c,
  apply fn_ub_add ha hc,
end

end

/-!
### Negation
-/

section

variable {f : ℝ → ℝ}

example (h : ∀ a, ∃ x, f x > a) : ¬ fn_has_ub f :=
begin
  intro h1,
  cases h1 with a,
  specialize h a,
  cases h with b,
  specialize h1_h b,
  linarith,
end

example (h : ∀ a, ∃ x, f x > a) : ¬ fn_has_ub f :=
begin
  simp only [fn_has_ub, fn_ub],
  push_neg,
  exact h,
end











example (h : ∀ a, ∃ x, f x > a) : ¬ fn_has_ub f :=
begin
  intro h1,
  cases h1 with a h2,
  specialize h a,
  cases h with x h3,
  specialize h2 x,
  linarith,
end

example (h : ∀ a, ∃ x, f x > a) : ¬ fn_has_ub f :=
begin
  simp only [fn_has_ub, fn_ub],
  push_neg,
  exact h,
end


end

/-!
### Conjunction
-/

section

variables {x y : ℝ}

-- demonstrate `split`

example (h₀ : x ≤ y) (h₁ : ¬ y ≤ x) : x ≤ y ∧ x ≠ y :=
begin
  split,
  exact h₀,
  intro h,
  apply h₁,
  rw h,
end


example (h₀ : x ≤ y) (h₁ : ¬ y ≤ x) : x ≤ y ∧ x ≠ y :=
begin
  split,
  { exact h₀ },
  -- linarith,
  contrapose! h₁,
  rw h₁,
end






example (h₀ : x ≤ y) (h₁ : ¬ y ≤ x) : x ≤ y ∧ x ≠ y :=
begin
  split,
  { exact h₀ },
  -- linarith,
  intro h,
  apply h₁,
  rw h,
end

example (h₀ : x ≤ y) (h₁ : ¬ y ≤ x) : x ≤ y ∧ x ≠ y :=
begin
  split,
  { exact h₀ },
  -- linarith,
  contrapose! h₁,
  rw h₁
end

-- demonstrate `cases`, `h.1`, `h.2`

example (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x :=
begin
  cases h with h1 h2,
  contrapose! h2,
  apply le_antisymm h1 h2,
end

example (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x :=
begin
  intro h3,
  apply h.2,
  apply le_antisymm,
  apply h.1,
  apply h3
  --apply le_antisymm h2 h1
end

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
begin
  intro h,
  have h1: y < 0 ∨ y ≥ 0, {exact lt_or_ge y 0},
  cases h1 with ha hb,
  {
    right,
    have h3 : abs y = -y, {apply abs_of_neg ha},
    exact eq.trans_gt h3 h,
  },
  {
    left,
    have : abs y = y, {exact abs_eq_self.mpr hb},
    exact eq.trans_gt this h,
  },
end











example : x < abs y → x < y ∨ x < -y :=
begin
  intro h,
  have h1 : 0 ≤ y ∨ y < 0,
  { exact le_or_lt 0 y },
  cases h1 with h2 h2,
  { left, 
    rwa abs_of_nonneg h2 at h },
  { right, 
    rwa abs_of_neg h2 at h, }
end

end

/-
More examples.
-/

section
variables p q : Prop
variables r s : ℕ → Prop

example : p ∧ q → q ∧ p :=
begin
  intro h,
  split,
  exact h.2,
  exact h.1,
end

example : p ∨ q → q ∨ p :=
begin
  intro h,
  cases h with h1 h2,
  {
    right,
    exact h1,
  },
  {
    left,
    exact h2,
  }
end

example : (∃ x, r x ∧ s x) → (∃ x, r x) ∧ (∃ x, s x) :=
begin
  intro h,
  cases h with x h₁,
  split,
  use x,
  exact h₁.1,
  use x,
  exact h₁.2,
end

example : ∀ z, (∃ x y, r x ∧ s y ∧ y = z) → ∃ x, r x ∧ s z :=
begin
  intro z,
  intro h,
  cases h with x h₁,
  cases h₁ with y h₂,
  use x,
  split,
  exact h₂.1,
  have h₃ : s y, {exact h₂.2.1},
  have h₄ : y = z, {exact h₂.2.2},
  exact h₄ ▸ h₃,
end

end

/-
More stuff.
-/

def converges_to (s : ℕ → ℝ) (a : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

theorem converges_to_const (a : ℝ) : converges_to (λ x : ℕ, a) a :=
begin
  intros ε he,
  use 1,
  intros n hn,
  rw sub_self,
  rw abs_zero,
  exact he,
end

variables x y: ℝ


example : abs ((x - a)+ (y -  b)) ≤ abs (x - a) + abs (y -  b) :=
begin
  let c := x-a,
  let d := y-b,
  exact abs_add c d,
end

theorem converges_to_add {s t : ℕ → ℝ} {a b : ℝ}
    (cs : converges_to s a) (ct : converges_to t b):
  converges_to (λ n, s n + t n) (a + b) :=
begin
  intros ε he,
  dsimp,
  cases cs (ε / 2) (half_pos he) with n1 h1,
  cases ct (ε / 2) (half_pos he) with n2 h2,
  use max n1 n2,
  intro n,
  intro hl,
  have hn1 : n ≥ n1, {exact le_of_max_le_left hl},
  have hn2 : n ≥ n2, {exact le_of_max_le_right hl},
  --specialize h1 n,
  specialize h2 n,
  have c1 : |s n - a| < ε / 2, {apply h1 n(le_of_max_le_left hl)},
  have c2 : |t n - b| < ε / 2, {apply h2 hn2},
  have w: abs (s n + t n - (a + b)) = abs ((s n - a) + (t n -  b)), {ring_nf},
  rw add_sub_add_comm,
  --rw w,
  have w2: abs ((s n - a) + (t n -  b)) ≤ abs (s n - a) + abs (t n -  b), 
    begin
      let a1 := (s n - a),
      let a2 := (t n - b),
      apply abs_add a1 a2,
    end,
  
  have : abs ((s n - a) + (t n -  b)) < ε, 
    begin
      calc 
        abs ((s n - a) + (t n -  b)) ≤ abs (s n - a) + abs (t n -  b) : by exact w2
        ... < ε / 2 +  abs (t n -  b) : by linarith
        ... < ε / 2+  ε / 2 : by linarith
        ... = ε : by linarith
    end,
    exact this,
  end



theorem converges_to_mul_const {s : ℕ → ℝ} {a : ℝ}
    (c : ℝ) (cs : converges_to s a) :
  converges_to (λ n, c * s n) (c * a) :=
sorry

theorem exists_abs_le_of_converges_to {s : ℕ → ℝ} {a : ℝ}
    (cs : converges_to s a) :
  ∃ N b, ∀ n, N ≤ n → abs (s n) < b :=
sorry

lemma aux {s t : ℕ → ℝ} {a : ℝ}
    (cs : converges_to s a) (ct : converges_to t 0) :
  converges_to (λ n, s n * t n) 0 :=
sorry

theorem converges_to_mul {s t : ℕ → ℝ} {a b : ℝ}
    (cs : converges_to s a) (ct : converges_to t b):
  converges_to (λ n, s n * t n) (a * b) :=
sorry

theorem converges_to_unique {s : ℕ → ℝ} {a b : ℝ}
    (sa : converges_to s a) (sb : converges_to s b) :
  a = b :=
sorry


