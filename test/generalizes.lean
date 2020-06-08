/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jannis Limperg
-/

import tactic.generalizes

universes u

lemma example_from_docs (P : ∀ n, fin n → Prop) (n : ℕ) (f : fin n)
  (p : ∀ n xs, P n xs) : P (nat.succ n) (fin.succ f) :=
begin
  -- TODO: `generalizes` fails if we write `n + 1` instead of `nat.succ n`,
  -- even though these are defeq at transparency semireducible.
  (do n ← tactic.get_local `n,
      h₁ ← tactic.to_expr ``(%%n + 1),
      h₂ ← tactic.to_expr ``(nat.succ %%n),
      tactic.is_def_eq h₁ h₂ semireducible ff
  ),
  generalizes [n'_eq : (nat.succ n) = n', f'_eq : fin.succ f == f'],
  exact p n' f'
end

inductive Vec (α : Sort u) : ℕ → Sort (max 1 u)
| nil : Vec 0
| cons {n} (x : α) (xs : Vec n) : Vec (n + 1)

namespace Vec

inductive eq {α} : ∀ (n m : ℕ), Vec α n → Vec α m → Prop
| nil : eq 0 0 nil nil
| cons {n m x y xs ys}
  : x = y
  → eq n m xs ys
  → eq (n + 1) (m + 1) (cons x xs) (cons y ys)

inductive fancy_unit {α} : ∀ n, Vec α n → Prop
| intro (n xs) : fancy_unit n xs

lemma test {α n} {x : α} {xs} : fancy_unit (n + 1) (cons x xs) :=
begin
  -- Successive `generalize` invocations don't give us the right goal:
  -- The second generalisation fails due to the dependency between
  -- `xs' : Vec α (n + 1)` and `n + 1`.
  success_if_fail {
    generalize eq_xs' : cons x xs = xs',
    generalize eq_n' : n + 1 = n',
    exact fancy_unit.intro n' xs'
  },
  -- `generalizes` gives us the expected result with everything generalised.
  generalizes [eq_n' : n + 1 = n', eq_xs' : cons x xs = xs'],
  exact fancy_unit.intro n' xs'
end

-- An example where `generalizes` enables a successful `induction` (though in
-- this case, `cases` would suffice and already performs the generalisation).
lemma eq_cons_inversion {α} {n m x y} {xs : Vec α n} {ys : Vec α m}
  : eq (n + 1) (m + 1) (cons x xs) (cons y ys)
  → eq n m xs ys :=
begin
  generalizes
    [ n'_eq : n + 1 = n'
    , m'_eq : m + 1 = m'
    , xs'_eq : cons x xs = xs'
    , ys'_eq : cons y ys = ys'
    ],
  intro h,
  induction h,
  case nil {
    cases n'_eq,
  },
  case cons : n'' m'' x y xs'' ys'' eq_xy eq_xsys'' ih {
    cases n'_eq, clear n'_eq,
    cases m'_eq, clear m'_eq,
    cases xs'_eq, clear xs'_eq,
    cases ys'_eq, clear ys'_eq,
    exact eq_xsys'',
  }
end

end Vec
