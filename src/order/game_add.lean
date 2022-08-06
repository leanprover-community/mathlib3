/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/

import logic.relation
import order.basic

/-!
# Game addition relation

This file defines, given relations `rα : α → α → Prop` and `rβ : β → β → Prop`, a relation
`game_add` on pairs, such that `game_add rα rβ x y` iff `x` can be reached from `y` by decreasing
either entry (with respect to `rα` and `rβ`). It is so called since it models the subsequency
relation on the addition of combinatorial games.

## Main result

- `well_founded.game_add`: formalizes induction on ordered pairs, where exactly one entry decreases
  at a time.

## Todo

- Add custom `induction` and `fix` lemmas.
- Define `sym2.game_add`.
-/

variables {α β : Type*} (rα : α → α → Prop) (rβ : β → β → Prop)

namespace prod

/-- `game_add rα rβ x y` means that  -/
inductive game_add : α × β → α × β → Prop
| fst {a₁ a₂ b} : rα a₁ a₂ → game_add (a₁, b) (a₂, b)
| snd {a b' b} : rβ b' b → game_add (a,b') (a,b)

/-- `prod.game_add` is a `subrelation` of `prod.lex`. -/
lemma game_add_le_lex : game_add rα rβ ≤ prod.lex rα rβ :=
λ _ _ h, h.rec (λ _ _ b, prod.lex.left b b) (λ a _ _, prod.lex.right a)

/-- `prod.rprod` is a subrelation of the transitive closure of `prod.game_add`. -/
lemma rprod_le_trans_gen_game_add : rprod rα rβ ≤ relation.trans_gen (game_add rα rβ) :=
λ _ _ h, h.rec begin
  intros _ _ _ _ hα hβ,
  exact relation.trans_gen.tail (relation.trans_gen.single $ game_add.fst hα) (game_add.snd hβ),
end

end prod

variables {rα rβ}

/-- If `a` is accessible under `rα` and `b` is accessible under `rβ`, then `(a, b)` is
  accessible under `prod.game_add rα rβ`. Notice that `prod.lex_accessible` requires the
  stronger condition `∀ b, acc rβ b`. -/
lemma acc.game_add {a b} (ha : acc rα a) (hb : acc rβ b) : acc (prod.game_add rα rβ) (a, b) :=
begin
  induction ha with a ha iha generalizing b,
  induction hb with b hb ihb,
  refine acc.intro _ (λ h, _),
  rintro (⟨_,_,_,ra⟩|⟨_,_,_,rb⟩),
  exacts [iha _ ra (acc.intro b hb), ihb _ rb],
end

/-- The sum of two well-founded games is well-founded. -/
lemma well_founded.game_add (hα : well_founded rα) (hβ : well_founded rβ) :
  well_founded (prod.game_add rα rβ) := ⟨λ ⟨a,b⟩, (hα.apply a).game_add (hβ.apply b)⟩
