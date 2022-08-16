/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/

import data.sym.sym2
import logic.relation

/-!
# Game addition relation

This file defines, given relations `rα : α → α → Prop` and `rβ : β → β → Prop`, a relation
`prod.game_add` on pairs, such that `game_add rα rβ x y` iff `x` can be reached from `y` by
decreasing either entry (with respect to `rα` and `rβ`). It is so called since it models the
subsequency relation on the addition of combinatorial games.

## Main definitions and results

- `prod.game_add`: the game addition relation on ordered pairs.
- `well_founded.prod_game_add`: formalizes induction on ordered pairs, where exactly one entry
  decreases at a time.

- `sym2.game_add`: the game addition relation on unordered pairs.
- `well_founded.sym2_game_add`: formalizes induction on unordered pairs, where exactly one entry
  decreases at a time.
-/

variables {α β : Type*} {rα : α → α → Prop} {rβ : β → β → Prop}

/-! ### `prod.game_add` -/

namespace prod

variables (rα rβ)

/-- `prod.game_add rα rβ x y` means that `x` can be reached from `y` by decreasing either entry. -/
inductive game_add : α × β → α × β → Prop
| fst {a₁ a₂ b} : rα a₁ a₂ → game_add (a₁, b) (a₂, b)
| snd {a b₁ b₂} : rβ b₁ b₂ → game_add (a, b₁) (a, b₂)

lemma game_add_iff {rα rβ} {x y : α × β} :
  game_add rα rβ x y ↔ rα x.1 y.1 ∧ x.2 = y.2 ∨ rβ x.2 y.2 ∧ x.1 = y.1 :=
begin
  split,
  { rintro (⟨a₁, a₂, b, h⟩ | ⟨a, b₁, b₂, h⟩),
    exacts [or.inl ⟨h, rfl⟩, or.inr ⟨h, rfl⟩] },
  { revert x y,
    rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ (⟨h, rfl : b₁ = b₂⟩ | ⟨h, rfl : a₁ = a₂⟩),
    exacts [game_add.fst h, game_add.snd h] }
end

lemma game_add_mk_iff {rα rβ} {a₁ a₂ : α} {b₁ b₂ : β} :
  game_add rα rβ (a₁, b₁) (a₂, b₂) ↔ rα a₁ a₂ ∧ b₁ = b₂ ∨ rβ b₁ b₂ ∧ a₁ = a₂ :=
game_add_iff

@[simp] lemma game_add_swap_swap : ∀ a b : α × β,
  game_add rβ rα a.swap b.swap ↔ game_add rα rβ a b :=
λ ⟨a₁, b₁⟩ ⟨a₂, b₂⟩, begin
  split;
  { rintro (⟨_, _, _, rb⟩ | ⟨_, _, _, ra⟩),
    exacts [game_add.snd rb, game_add.fst ra] }
end

lemma game_add_swap_swap_mk (a₁ a₂ : α) (b₁ b₂ : β) :
  game_add rα rβ (a₁, b₁) (a₂, b₂) ↔ game_add rβ rα (b₁, a₁) (b₂, a₂) :=
game_add_swap_swap rβ rα (b₁, a₁) (b₂, a₂)

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

/-- If `a` is accessible under `rα` and `b` is accessible under `rβ`, then `(a, b)` is
  accessible under `prod.game_add rα rβ`. Notice that `prod.lex_accessible` requires the
  stronger condition `∀ b, acc rβ b`. -/
lemma acc.prod_game_add {a b} (ha : acc rα a) (hb : acc rβ b) : acc (prod.game_add rα rβ) (a, b) :=
begin
  induction ha with a ha iha generalizing b,
  induction hb with b hb ihb,
  refine acc.intro _ (λ h, _),
  rintro (⟨_,_,_,ra⟩|⟨_,_,_,rb⟩),
  exacts [iha _ ra (acc.intro b hb), ihb _ rb],
end

/-- The `prod.game_add` relation is well-founded. -/
lemma well_founded.prod_game_add (hα : well_founded rα) (hβ : well_founded rβ) :
  well_founded (prod.game_add rα rβ) := ⟨λ ⟨a, b⟩, (hα.apply a).prod_game_add (hβ.apply b)⟩

namespace prod

/-- Recursion on the well-founded `prod.game_add` relation.

Note that it's strictly more general to recurse on the lexicographic order instead. -/
def game_add.fix {C : α → β → Sort*} (hα : well_founded rα) (hβ : well_founded rβ)
  (IH : Π a₁ b₁, (Π a₂ b₂, game_add rα rβ (a₂, b₂) (a₁, b₁) → C a₂ b₂) → C a₁ b₁) (a : α) (b : β) :
  C a b :=
@well_founded.fix (α × β) (λ x, C x.1 x.2) _ (hα.prod_game_add hβ)
  (λ ⟨x₁, x₂⟩ IH', IH x₁ x₂ $ λ a' b', IH' ⟨a', b'⟩) ⟨a, b⟩

lemma game_add.fix_eq {C : α → β → Sort*} (hα : well_founded rα) (hβ : well_founded rβ)
  (IH : Π a₁ b₁, (Π a₂ b₂, game_add rα rβ (a₂, b₂) (a₁, b₁) → C a₂ b₂) → C a₁ b₁) (a : α) (b : β) :
  game_add.fix hα hβ IH a b = IH a b (λ a' b' h, game_add.fix hα hβ IH a' b') :=
by { rw [game_add.fix, well_founded.fix_eq], refl }

/-- Induction on the well-founded `prod.game_add` relation.

Note that it's strictly more general to induct on the lexicographic order instead. -/
lemma game_add.induction {C : α → β → Prop} : well_founded rα → well_founded rβ →
  (∀ a₁ b₁, (∀ a₂ b₂, game_add rα rβ (a₂, b₂) (a₁, b₁) → C a₂ b₂) → C a₁ b₁) → ∀ a b, C a b :=
game_add.fix

end prod.game_add

/-! ### `sym2.game_add` -/

namespace sym2

variables (rα rβ)

/-- `sym2.game_add rα x y` means that `x` can be reached from `y` by decreasing either entry. -/
def game_add : sym2 α → sym2 α → Prop :=
sym2.lift₂
⟨λ a₁ b₁ a₂ b₂, prod.game_add rα rα (a₁, b₁) (a₂, b₂) ∨ prod.game_add rα rα (b₁, a₁) (a₂, b₂),
  λ a₁ b₁ a₂ b₂, begin
    rw [prod.game_add_swap_swap_mk _ _ b₁ b₂ a₁ a₂, prod.game_add_swap_swap_mk _ _ a₁ b₂ b₁ a₂],
    simp [or_comm]
  end⟩

lemma game_add_mk_iff {rα} {a₁ a₂ b₁ b₂ : α} : game_add rα ⟦(a₁, b₁)⟧ ⟦(a₂, b₂)⟧ ↔
  prod.game_add rα rα (a₁, b₁) (a₂, b₂) ∨ prod.game_add rα rα (b₁, a₁) (a₂, b₂) :=
iff.rfl

lemma _root_.prod.game_add.to_sym2 {rα} {a₁ a₂ b₁ b₂ : α}
  (h : prod.game_add rα rα (a₁, b₁) (a₂, b₂)) : sym2.game_add rα ⟦(a₁, b₁)⟧ ⟦(a₂, b₂)⟧ :=
game_add_mk_iff.2 $ or.inl $ h

lemma game_add.fst {a₁ a₂ b : α} (h : rα a₁ a₂) : game_add rα ⟦(a₁, b)⟧ ⟦(a₂, b)⟧ :=
(prod.game_add.fst h).to_sym2

lemma game_add.snd {a b₁ b₂ : α} (h : rα b₁ b₂) : game_add rα ⟦(a, b₁)⟧ ⟦(a, b₂)⟧ :=
(prod.game_add.snd h).to_sym2

end sym2

private lemma acc_game_add_aux {a b} (ha : acc rα a) (hb : acc rα b) :
  acc (sym2.game_add rα) ⟦(a, b)⟧ ∧ acc (sym2.game_add rα) ⟦(b, a)⟧ :=
begin
  induction ha with a ha iha generalizing b,
  induction hb with b hb ihb,
  split; split; rintros ⟨c, d⟩ ((⟨_, _, _, rc⟩ | ⟨_, _, _, rd⟩) | (⟨_, _, _, rd⟩ | ⟨_, _, _, rc⟩)),
  exacts [(iha c rc ⟨b, hb⟩).1, (ihb d rd).1, (iha d rd ⟨b, hb⟩).2, (ihb c rc).2,
    (ihb c rc).2, (iha d rd ⟨b, hb⟩).2, (ihb d rd).1, (iha c rc ⟨b, hb⟩).1]
end

lemma acc.sym2_game_add {a b} (ha : acc rα a) (hb : acc rα b) :
  acc (sym2.game_add rα) ⟦(a, b)⟧ := (acc_game_add_aux ha hb).1

/-- The `sym2.game_add` relation is well-founded. -/
lemma well_founded.sym2_game_add (h : well_founded rα) : well_founded (sym2.game_add rα) :=
⟨λ i, sym2.induction_on i $ λ x y, (h.apply x).sym2_game_add (h.apply y)⟩

namespace sym2

/-- Recursion on the well-founded `sym2.game_add` relation. -/
def game_add.fix {C : α → α → Sort*} (hr : well_founded rα)
  (IH : Π a₁ b₁, (Π a₂ b₂, sym2.game_add rα ⟦(a₂, b₂)⟧ ⟦(a₁, b₁)⟧ → C a₂ b₂) → C a₁ b₁) (a b : α) :
  C a b :=
@well_founded.fix (α × α) (λ x, C x.1 x.2) _ hr.sym2_game_add.of_quotient_lift₂
  (λ ⟨x₁, x₂⟩ IH', IH x₁ x₂ $ λ a' b', IH' ⟨a', b'⟩) (a, b)

lemma game_add.fix_eq {C : α → α → Sort*} (hr : well_founded rα)
  (IH : Π a₁ b₁, (Π a₂ b₂, sym2.game_add rα ⟦(a₂, b₂)⟧ ⟦(a₁, b₁)⟧ → C a₂ b₂) → C a₁ b₁) (a b : α) :
  game_add_swap.fix hr IH a b = IH a b (λ a' b' h, game_add_swap.fix hr IH a' b') :=
by { rw [game_add_swap.fix, well_founded.fix_eq], refl }

/-- Induction on the well-founded `sym2.game_add` relation. -/
lemma game_add.induction {C : α → α → Prop} : well_founded rα →
  (∀ a₁ b₁, (∀ a₂ b₂, sym2.game_add rα ⟦(a₂, b₂)⟧ ⟦(a₁, b₁)⟧ → C a₂ b₂) → C a₁ b₁) → ∀ a b, C a b :=
game_add_swap.fix

end sym2
