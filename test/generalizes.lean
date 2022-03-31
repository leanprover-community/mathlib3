/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import tactic.generalizes

universes u

lemma example_from_docs₁ (P : ∀ n, fin n → Prop) (n : ℕ) (f : fin n)
  (p : ∀ n xs, P n xs) : P (nat.succ n) (fin.succ f) :=
begin
  generalizes [n'_eq : nat.succ n = n', f'_eq : fin.succ f == f'],
  guard_hyp n' : ℕ,
  guard_hyp n'_eq : n' = nat.succ n,
  guard_hyp f' : fin n',
  guard_hyp f'_eq : f' == fin.succ f,
  exact p n' f'
  -- Note: `generalizes` fails if we write `n + 1` instead of `nat.succ n` in
  -- the target because `kabstract` works with a notion of equality that is
  -- weaker than definitional equality. This is annoying, but we can't do much
  -- about it short of reimplementing `kabstract`.
end

lemma example_from_docs₂ (P : ∀ n, fin n → Prop) (n : ℕ) (f : fin n)
  (p : ∀ n xs, P n xs) : P (nat.succ n) (fin.succ f) :=
begin
  generalizes [(nat.succ n = n'), (fin.succ f == f')],
  guard_hyp n' : ℕ,
  success_if_fail { guard_hyp n'_eq : n' = nat.succ n },
  guard_hyp f' : fin n',
  success_if_fail { guard_hyp f'_eq : f' == fin.succ f },
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

-- An example of the difference between multiple calls to `generalize` and
-- one call to `generalizes`.
lemma test₁ {α n} {x : α} {xs} : fancy_unit (n + 1) (cons x xs) :=
begin
  -- Successive `generalize` invocations don't give us the right goal:
  -- The second generalisation fails due to the dependency between
  -- `xs' : Vec α (n + 1)` and `n + 1`.
  success_if_fail {
    generalize eq_xs' : cons x xs = xs',
    generalize eq_n' : n + 1 = n',
    exact fancy_unit.intro n' xs' },
  -- `generalizes` gives us the expected result with everything generalised.
  generalizes [eq_n' : n + 1 = n', eq_xs' : cons x xs = xs'],
  guard_hyp n' : ℕ,
  guard_hyp eq_n' : n' = n + 1,
  guard_hyp xs' : Vec α n',
  guard_hyp eq_xs' : xs' == cons x xs,
  exact fancy_unit.intro n' xs'
end

-- We can also choose to introduce equations for only some of the generalised
-- expressions.
lemma test₂ {α n} {x : α} {xs} : fancy_unit (n + 1) (cons x xs) :=
begin
  generalizes [n + 1 = n', eq_xs' : cons x xs = xs'],
  guard_hyp n' : ℕ,
  success_if_fail { guard_hyp eq_n' : n' = n + 1 },
  guard_hyp xs' : Vec α n',
  guard_hyp eq_xs' : xs' == cons x xs,
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
    cases n'_eq, },
  case cons : n'' m'' x y xs'' ys'' eq_xy eq_xsys'' ih {
    cases n'_eq, clear n'_eq,
    cases m'_eq, clear m'_eq,
    cases xs'_eq, clear xs'_eq,
    cases ys'_eq, clear ys'_eq,
    exact eq_xsys'', }
end

end Vec
