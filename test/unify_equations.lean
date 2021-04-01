/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import tactic.unify_equations

-- An example which exercises the injectivity, substitution and heterogeneous
-- downgrading rules.
example (P : ∀ n, fin n → Prop) (n m : ℕ) (f : fin n) (g : fin m)
  (h₁ : n + 1 = m + 1) (h₂ : f == g) (h₃ : P n f) : P m g :=
begin
  unify_equations h₁ h₂,
  exact h₃
end

-- An example which exercises the injectivity and no-confusion rules.
example (n m : ℕ) (h : [n] = [n, m]) : false :=
begin
  unify_equations h
end

-- An example which exercises the deletion rule.
example (n) (h : n + 1 = n + 1) : true :=
begin
  unify_equations h,
  guard_hyp n : ℕ,
  guard_target true,
  trivial
end

-- An example which exercises the substitution and cycle elimination rules.
example (n m : ℕ) (h₁ : n = m) (h₂ : n = m + 3) : false :=
begin
  unify_equations h₁ h₂
end

-- The tactic should also support generalised inductive types. Here's a nested
-- type.
inductive rose : Type
| tip : ℕ → rose
| node : list rose → rose

open rose

example (t u v : rose) (h : node [t] = node [u, v]) : false :=
begin
  unify_equations h
end

-- However, the cycle elimination rule currently does not work with generalised
-- inductive types.
example (t u : rose) (h : t = node [t]) : true :=
begin
  unify_equations h,
  guard_hyp h : t = node [t],
  trivial
end
