/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import data.multiset.basic
import order.well_founded

/-!
# Termination of a hydra game

This file deals with the following version of the hydra game: each head of the hydra is
labelled by an element in a type `α`, and when you cut off one head with label `a`, it
grows back an arbitrary but finite number of heads, all labelled by elements smaller than
`a` with respect to a well-founded relation `r` on `α`. We show that no matter how (in
what order) you choose cut off the heads, the game always terminates, i.e. all heads will
eventually be cut off (but of course it can last arbitrarily long, i.e. takes an
arbitrary finite number of steps).

This result is stated as the well-foundedness of the `cut_expand` relation defined in
this file: we model the heads of the hydra as a multiset of elements of `α`, and the
valid "moves" of the game are modelled by the relation `cut_expand r` on `multiset α`:
`cut_expand r s' s` is true iff `s'` is obtained by removing one head `a ∈ s` and
adding back an arbitrary multiset `t` of heads such that all `a' ∈ t` satisfy `r a' a`.

To prove this theorem, we follow the proof by Peter LeFanu Lumsdaine at
https://mathoverflow.net/a/229084/3332, and along the way we introduce the notion of `fibration`
of relations, and a new operation `game_add` that combines to relations to form a relation on the
product type, which is used to define addition of games in combinatorial game theory.

TODO: formalize the relations corresponding to more powerful (e.g. Kirby–Paris and Buchholz)
hydras, and prove their well-foundedness.
-/

namespace relation

variables {α β : Type*}

section two_rels
variables (rα : α → α → Prop) (rβ : β → β → Prop) (f : α → β)

/-- A function `f : α → β` is a fibration between the relation `rα` and `rβ` if for all
  `a : α` and `b : β`, whenever `b : β` and `f a` are related by `rβ`, `b` is the image
  of some `a' : α` under `f`, and `a'` and `a` are related by `rα`. -/
def fibration := ∀ ⦃a b⦄, rβ b (f a) → ∃ a', rα a' a ∧ f a' = b

variables {rα rβ}

/-- If `f : α → β` is a fibration between relations `rα` and `rβ`, and `a : α` is
  accessible under `rα`, then `f a` is accessible under `rβ`. -/
lemma _root_.acc.of_fibration (fib : fibration rα rβ f) {a} (ha : acc rα a) : acc rβ (f a) :=
begin
  induction ha with a ha ih,
  refine acc.intro (f a) (λ b hr, _),
  obtain ⟨a', hr', rfl⟩ := fib hr,
  exact ih a' hr',
end

lemma _root_.acc.of_downward_closed (dc : ∀ {a b}, rβ b (f a) → b ∈ set.range f)
  (a : α) (ha : acc (inv_image rβ f) a) : acc rβ (f a) :=
ha.of_fibration f (λ a b h, let ⟨a', he⟩ := dc h in ⟨a', he.substr h, he⟩)

variables (rα rβ)

/-- The "addition of games" relation in combinatorial game theory, on the product type: if
  `rα a' a` means that `a ⟶ a'` is a valid move in game `α`, and `rβ b' b` means that `b ⟶ b'`
  is a valid move in game `β`, then `game_add rα rβ` specifies the valid moves in the juxtaposition
  of `α` and `β`: the player is free to choose one of the games and make a move in it,
  while leaving the other game unchanged. -/
inductive game_add : α × β → α × β → Prop
| fst {a' a b} : rα a' a → game_add (a',b) (a,b)
| snd {a b' b} : rβ b' b → game_add (a,b') (a,b)

/-- `game_add` is a `subrelation` of `prod.lex`. -/
lemma game_add_le_lex : game_add rα rβ ≤ prod.lex rα rβ :=
λ _ _ h, h.rec (λ _ _ b, prod.lex.left b b) (λ a _ _, prod.lex.right a)

/-- `prod.rprod` is a subrelation of the transitive closure of `game_add`. -/
lemma rprod_le_trans_gen_game_add : prod.rprod rα rβ ≤ trans_gen (game_add rα rβ) :=
λ _ _ h, h.rec begin
  intros _ _ _ _ hα hβ,
  exact trans_gen.tail (trans_gen.single $ game_add.fst hα) (game_add.snd hβ),
end

variables {rα rβ}

/-- If `a` is accessible under `rα` and `b` is accessible under `rβ`, then `(a, b)` is
  accessible under `relation.game_add rα rβ`. Notice that `prod.lex_accessible` requires the
  stronger condition `∀ b, acc rβ b`. -/
lemma _root_.acc.game_add {a b} (ha : acc rα a) (hb : acc rβ b) : acc (game_add rα rβ) (a, b) :=
begin
  induction ha with a ha iha generalizing b,
  induction hb with b hb ihb,
  refine acc.intro _ (λ h, _),
  rintro (⟨_,_,_,ra⟩|⟨_,_,_,rb⟩),
  exacts [iha _ ra (acc.intro b hb), ihb _ rb],
end

/-- The sum of two well-founded games is well-founded. -/
lemma _root_.well_founded.game_add (hα : well_founded rα) (hβ : well_founded rβ) :
  well_founded (game_add rα rβ) := ⟨λ ⟨a,b⟩, (hα.apply a).game_add (hβ.apply b)⟩

end two_rels

section hydra
open game_add multiset

/-- The relation that specifies valid moves in our hydra game. `cut_expand r s' s`
  means that `s'` is obtained by removing one head `a ∈ s` and adding back an arbitrary
  multiset `t` of heads such that all `a' ∈ t` satisfy `r a' a`.

  This is most directly translated into `s' = s.erase a + t`, but `multiset.erase` requires
  `decidable_eq α`, so we use the equivalent condition `s' + {a} = s + t` instead, which
  is also easier to verify for explicit multisets `s'`, `s` and `t`.

  We also don't include the condition `a ∈ s` because `s' + {a} = s + t` already
  guarantees `a ∈ s + t`, and if `r` is irreflexive then `a ∉ t`, which is the
  case when `r` is well-founded, the case we are primarily interested in.

  The lemma `relation.cut_expand_iff` below converts between this convenient definition
  and the direct translation when `r` is irreflexive. -/
def cut_expand (r : α → α → Prop) (s' s : multiset α) : Prop :=
∃ (t : multiset α) (a : α), (∀ a' ∈ t, r a' a) ∧ s' + {a} = s + t

variable {r : α → α → Prop}

theorem cut_expand_singleton {s x} (h : ∀ x' ∈ s, r x' x) : cut_expand r s {x} :=
⟨s, x, h, add_comm s _⟩

theorem cut_expand_singleton_singleton {x' x} (h : r x' x) : cut_expand r {x'} {x} :=
cut_expand_singleton (λ a h, by rwa mem_singleton.1 h)

theorem cut_expand_add_left {t u} (s) : cut_expand r (s + t) (s + u) ↔ cut_expand r t u :=
exists₂_congr $ λ _ _, and_congr iff.rfl $ by rw [add_assoc, add_assoc, add_left_cancel_iff]

lemma cut_expand_iff [decidable_eq α] [is_irrefl α r] {s' s : multiset α} :
  cut_expand r s' s ↔ ∃ (t : multiset α) a, (∀ a' ∈ t, r a' a) ∧ a ∈ s ∧ s' = s.erase a + t :=
begin
  simp_rw [cut_expand, add_singleton_eq_iff],
  refine exists₂_congr (λ t a, ⟨_, _⟩),
  { rintro ⟨ht, ha, rfl⟩,
    obtain (h|h) := mem_add.1 ha,
    exacts [⟨ht, h, t.erase_add_left_pos h⟩, (@irrefl α r _ a (ht a h)).elim] },
  { rintro ⟨ht, h, rfl⟩,
    exact ⟨ht, mem_add.2 (or.inl h), (t.erase_add_left_pos h).symm⟩ },
end

theorem not_cut_expand_zero [is_irrefl α r] (s) : ¬ cut_expand r s 0 :=
by { classical, rw cut_expand_iff, rintro ⟨_, _, _, ⟨⟩, _⟩ }

/-- For any relation `r` on `α`, multiset addition `multiset α × multiset α → multiset α` is a
  fibration between the game sum of `cut_expand r` with itself and `cut_expand r` itself. -/
lemma cut_expand_fibration (r : α → α → Prop) :
  fibration (game_add (cut_expand r) (cut_expand r)) (cut_expand r) (λ s, s.1 + s.2) :=
begin
  rintro ⟨s₁, s₂⟩ s ⟨t, a, hr, he⟩, dsimp at he ⊢,
  classical, obtain ⟨ha, rfl⟩ := add_singleton_eq_iff.1 he,
  rw [add_assoc, mem_add] at ha, obtain (h|h) := ha,
  { refine ⟨(s₁.erase a + t, s₂), fst ⟨t, a, hr, _⟩, _⟩,
    { rw [add_comm, ← add_assoc, singleton_add, cons_erase h] },
    { rw [add_assoc s₁, erase_add_left_pos _ h, add_right_comm, add_assoc] } },
  { refine ⟨(s₁, (s₂ + t).erase a), snd ⟨t, a, hr, _⟩, _⟩,
    { rw [add_comm, singleton_add, cons_erase h] },
    { rw [add_assoc, erase_add_right_pos _ h] } },
end

/-- A multiset is accessible under `cut_expand` if all its singleton subsets are,
  assuming `r` is irreflexive. -/
lemma acc_of_singleton [is_irrefl α r] {s : multiset α} :
  (∀ a ∈ s, acc (cut_expand r) {a}) → acc (cut_expand r) s :=
begin
  refine multiset.induction _ _ s,
  { exact λ _, acc.intro 0 $ λ s h, (not_cut_expand_zero s h).elim },
  { intros a s ih hacc, rw ← s.singleton_add a,
    exact ((hacc a $ s.mem_cons_self a).game_add $ ih $ λ a ha,
      hacc a $ mem_cons_of_mem ha).of_fibration _ (cut_expand_fibration r) },
end

/-- A singleton `{a}` is accessible under `cut_expand r` if `a` is accessible under `r`,
  assuming `r` is irreflexive. -/
lemma _root_.acc.cut_expand [is_irrefl α r] {a : α} (hacc : acc r a) : acc (cut_expand r) {a} :=
begin
  induction hacc with a h ih,
  refine acc.intro _ (λ s, _),
  classical, rw cut_expand_iff,
  rintro ⟨t, a, hr, rfl|⟨⟨⟩⟩, rfl⟩,
  refine acc_of_singleton (λ a', _),
  rw [erase_singleton, zero_add],
  exact ih a' ∘ hr a',
end

/-- `cut_expand r` is well-founded when `r` is. -/
theorem _root_.well_founded.cut_expand (hr : well_founded r) : well_founded (cut_expand r) :=
⟨by { letI h := hr.is_irrefl, exact λ s, acc_of_singleton $ λ a _, (hr.apply a).cut_expand }⟩
end hydra

end relation
