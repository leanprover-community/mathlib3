/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jannis Limperg
-/

import tactic.generalizes

universes u

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
