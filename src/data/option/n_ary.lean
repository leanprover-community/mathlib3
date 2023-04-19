/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.option.basic

/-!
# Binary map of options

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the binary map of `option`. This is mostly useful to define pointwise operations
on intervals.

## Main declarations

* `option.map₂`: Binary map of options.

## Notes

This file is very similar to `data.set.n_ary`, `data.finset.n_ary` and `order.filter.n_ary`. Please
keep them in sync.

We do not define `option.map₃` as its only purpose so far would be to prove properties of
`option.map₂` and casing already fulfills this task.
-/

open function

namespace option
variables {α α' β β' γ γ' δ δ' ε ε' : Type*} {f : α → β → γ} {a : option α} {b : option β}
  {c : option γ}

/-- The image of a binary function `f : α → β → γ` as a function `option α → option β → option γ`.
Mathematically this should be thought of as the image of the corresponding function `α × β → γ`. -/
def map₂ (f : α → β → γ) (a : option α) (b : option β) : option γ := a.bind $ λ a, b.map $ f a

/-- `option.map₂` in terms of monadic operations. Note that this can't be taken as the definition
because of the lack of universe polymorphism. -/
lemma map₂_def {α β γ : Type*} (f : α → β → γ) (a : option α) (b : option β) :
  map₂ f a b = f <$> a <*> b := by cases a; refl

@[simp] lemma map₂_some_some (f : α → β → γ) (a : α) (b : β) :
  map₂ f (some a) (some b) = some (f a b) :=
rfl

lemma map₂_coe_coe (f : α → β → γ) (a : α) (b : β) : map₂ f a b = f a b := rfl
@[simp] lemma map₂_none_left (f : α → β → γ) (b : option β) : map₂ f none b = none := rfl
@[simp] lemma map₂_none_right (f : α → β → γ) (a : option α) : map₂ f a none = none :=
by cases a; refl
@[simp] lemma map₂_coe_left (f : α → β → γ) (a : α) (b : option β) :
  map₂ f a b = b.map (λ b, f a b) := rfl
@[simp] lemma map₂_coe_right (f : α → β → γ) (a : option α) (b : β) :
  map₂ f a b = a.map (λ a, f a b) := rfl

@[simp] lemma mem_map₂_iff {c : γ} : c ∈ map₂ f a b ↔ ∃ a' b', a' ∈ a ∧ b' ∈ b ∧ f a' b' = c :=
by simp [map₂]

@[simp] lemma map₂_eq_none_iff : map₂ f a b = none ↔ a = none ∨ b = none :=
by cases a; cases b; simp

lemma map₂_swap (f : α → β → γ) (a : option α) (b : option β) :
  map₂ f a b = map₂ (λ a b, f b a) b a :=
by cases a; cases b; refl

lemma map_map₂ (f : α → β → γ) (g : γ → δ) : (map₂ f a b).map g = map₂ (λ a b, g (f a b)) a b :=
by cases a; cases b; refl

lemma map₂_map_left (f : γ → β → δ) (g : α → γ) :
  map₂ f (a.map g) b = map₂ (λ a b, f (g a) b) a b :=
by cases a; refl

lemma map₂_map_right (f : α → γ → δ) (g : β → γ) :
  map₂ f a (b.map g) = map₂ (λ a b, f a (g b)) a b :=
by cases b; refl

@[simp] lemma map₂_curry (f : α × β → γ) (a : option α) (b : option β) :
  map₂ (curry f) a b = option.map f (map₂ prod.mk a b) := (map_map₂ _ _).symm

@[simp] lemma map_uncurry (f : α → β → γ) (x : option (α × β)) :
  x.map (uncurry f) = map₂ f (x.map prod.fst) (x.map prod.snd) := by cases x; refl

/-!
### Algebraic replacement rules

A collection of lemmas to transfer associativity, commutativity, distributivity, ... of operations
to the associativity, commutativity, distributivity, ... of `option.map₂` of those operations.
The proof pattern is `map₂_lemma operation_lemma`. For example, `map₂_comm mul_comm` proves that
`map₂ (*) a b = map₂ (*) g f` in a `comm_semigroup`.
-/

lemma map₂_assoc {f : δ → γ → ε} {g : α → β → δ} {f' : α → ε' → ε} {g' : β → γ → ε'}
  (h_assoc : ∀ a b c, f (g a b) c = f' a (g' b c)) :
  map₂ f (map₂ g a b) c = map₂ f' a (map₂ g' b c) :=
by cases a; cases b; cases c; simp [h_assoc]

lemma map₂_comm {g : β → α → γ} (h_comm : ∀ a b, f a b = g b a) : map₂ f a b = map₂ g b a :=
by cases a; cases b; simp [h_comm]

lemma map₂_left_comm {f : α → δ → ε} {g : β → γ → δ} {f' : α → γ → δ'} {g' : β → δ' → ε}
  (h_left_comm : ∀ a b c, f a (g b c) = g' b (f' a c)) :
  map₂ f a (map₂ g b c) = map₂ g' b (map₂ f' a c) :=
by cases a; cases b; cases c; simp [h_left_comm]

lemma map₂_right_comm {f : δ → γ → ε} {g : α → β → δ} {f' : α → γ → δ'} {g' : δ' → β → ε}
  (h_right_comm : ∀ a b c, f (g a b) c = g' (f' a c) b) :
  map₂ f (map₂ g a b) c = map₂ g' (map₂ f' a c) b :=
by cases a; cases b; cases c; simp [h_right_comm]

lemma map_map₂_distrib {g : γ → δ} {f' : α' → β' → δ} {g₁ : α → α'} {g₂ : β → β'}
  (h_distrib : ∀ a b, g (f a b) = f' (g₁ a) (g₂ b)) :
  (map₂ f a b).map g = map₂ f' (a.map g₁) (b.map g₂) :=
by cases a; cases b; simp [h_distrib]

/-!
The following symmetric restatement are needed because unification has a hard time figuring all the
functions if you symmetrize on the spot. This is also how the other n-ary APIs do it.
-/

/-- Symmetric statement to `option.map₂_map_left_comm`. -/
lemma map_map₂_distrib_left {g : γ → δ} {f' : α' → β → δ} {g' : α → α'}
  (h_distrib : ∀ a b, g (f a b) = f' (g' a) b) :
  (map₂ f a b).map g = map₂ f' (a.map g') b :=
by cases a; cases b; simp [h_distrib]

/-- Symmetric statement to `option.map_map₂_right_comm`. -/
lemma map_map₂_distrib_right {g : γ → δ} {f' : α → β' → δ} {g' : β → β'}
  (h_distrib : ∀ a b, g (f a b) = f' a (g' b)) :
  (map₂ f a b).map g = map₂ f' a (b.map g') :=
by cases a; cases b; simp [h_distrib]

/-- Symmetric statement to `option.map_map₂_distrib_left`. -/
lemma map₂_map_left_comm {f : α' → β → γ} {g : α → α'} {f' : α → β → δ} {g' : δ → γ}
  (h_left_comm : ∀ a b, f (g a) b = g' (f' a b)) :
  map₂ f (a.map g) b = (map₂ f' a b).map g' :=
by cases a; cases b; simp [h_left_comm]

/-- Symmetric statement to `option.map_map₂_distrib_right`. -/
lemma map_map₂_right_comm {f : α → β' → γ} {g : β → β'} {f' : α → β → δ} {g' : δ → γ}
  (h_right_comm : ∀ a b, f a (g b) = g' (f' a b)) :
  map₂ f a (b.map g) = (map₂ f' a b).map g' :=
by cases a; cases b; simp [h_right_comm]

lemma map_map₂_antidistrib {g : γ → δ} {f' : β' → α' → δ} {g₁ : β → β'} {g₂ : α → α'}
  (h_antidistrib : ∀ a b, g (f a b) = f' (g₁ b) (g₂ a)) :
  (map₂ f a b).map g = map₂ f' (b.map g₁) (a.map g₂) :=
by cases a; cases b; simp [h_antidistrib]

/-- Symmetric statement to `option.map₂_map_left_anticomm`. -/
lemma map_map₂_antidistrib_left {g : γ → δ} {f' : β' → α → δ} {g' : β → β'}
  (h_antidistrib : ∀ a b, g (f a b) = f' (g' b) a) :
  (map₂ f a b).map g = map₂ f' (b.map g') a :=
by cases a; cases b; simp [h_antidistrib]

/-- Symmetric statement to `option.map_map₂_right_anticomm`. -/
lemma map_map₂_antidistrib_right {g : γ → δ} {f' : β → α' → δ} {g' : α → α'}
  (h_antidistrib : ∀ a b, g (f a b) = f' b (g' a)) :
  (map₂ f a b).map g = map₂ f' b (a.map g') :=
by cases a; cases b; simp [h_antidistrib]

/-- Symmetric statement to `option.map_map₂_antidistrib_left`. -/
lemma map₂_map_left_anticomm {f : α' → β → γ} {g : α → α'} {f' : β → α → δ} {g' : δ → γ}
  (h_left_anticomm : ∀ a b, f (g a) b = g' (f' b a)) :
  map₂ f (a.map g) b = (map₂ f' b a).map g' :=
by cases a; cases b; simp [h_left_anticomm]

/-- Symmetric statement to `option.map_map₂_antidistrib_right`. -/
lemma map_map₂_right_anticomm {f : α → β' → γ} {g : β → β'} {f' : β → α → δ} {g' : δ → γ}
  (h_right_anticomm : ∀ a b, f a (g b) = g' (f' b a)) :
  map₂ f a (b.map g) = (map₂ f' b a).map g' :=
by cases a; cases b; simp [h_right_anticomm]

/-- If `a` is a left identity for a binary operation `f`, then `some a` is a left identity for
`option.map₂ f`. -/
lemma map₂_left_identity {f : α → β → β} {a : α} (h : ∀ b, f a b = b) (o : option β) :
  map₂ f (some a) o = o :=
by { cases o, exacts [rfl, congr_arg some (h _)] }

/-- If `b` is a right identity for a binary operation `f`, then `some b` is a right identity for
`option.map₂ f`. -/
lemma map₂_right_identity {f : α → β → α} {b : β} (h : ∀ a, f a b = a) (o : option α) :
  map₂ f o (some b) = o :=
by simp [h, map₂]

end option
