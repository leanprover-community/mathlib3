/-
Copyright (c) 2021 David Wärn,. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn, Scott Morrison
-/
import combinatorics.quiver.basic
import logic.lemmas

/-!
# Paths in quivers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Given a quiver `V`, we define the type of paths from `a : V` to `b : V` as an inductive
family. We define composition of paths and the action of prefunctors on paths.
-/

open function

universes v v₁ v₂ u u₁ u₂

namespace quiver

/-- `G.path a b` is the type of paths from `a` to `b` through the arrows of `G`. -/
inductive path {V : Type u} [quiver.{v} V] (a : V) : V → Sort (max (u+1) v)
| nil  : path a
| cons : Π {b c : V}, path b → (b ⟶ c) → path c

/-- An arrow viewed as a path of length one. -/
def hom.to_path {V} [quiver V] {a b : V} (e : a ⟶ b) : path a b :=
path.nil.cons e

namespace path

variables {V : Type u} [quiver V] {a b c d : V}

lemma nil_ne_cons (p : path a b) (e : b ⟶ a) : path.nil ≠ p.cons e.

lemma cons_ne_nil (p : path a b) (e : b ⟶ a) : p.cons e ≠ path.nil.

lemma obj_eq_of_cons_eq_cons {p : path a b} {p' : path a c}
  {e : b ⟶ d} {e' : c ⟶ d} (h : p.cons e = p'.cons e') : b = c := by injection h

lemma heq_of_cons_eq_cons {p : path a b} {p' : path a c}
  {e : b ⟶ d} {e' : c ⟶ d} (h : p.cons e = p'.cons e') : p == p' := by injection h

lemma hom_heq_of_cons_eq_cons {p : path a b} {p' : path a c}
  {e : b ⟶ d} {e' : c ⟶ d} (h : p.cons e = p'.cons e') : e == e' := by injection h

/-- The length of a path is the number of arrows it uses. -/
def length {a : V} : Π {b : V}, path a b → ℕ
| _ path.nil        := 0
| _ (path.cons p _) := p.length + 1

instance {a : V} : inhabited (path a a) := ⟨path.nil⟩

@[simp] lemma length_nil {a : V} :
  (path.nil : path a a).length = 0 := rfl

@[simp] lemma length_cons (a b c : V) (p : path a b)
  (e : b ⟶ c) : (p.cons e).length = p.length + 1 := rfl

lemma eq_of_length_zero (p : path a b) (hzero : p.length = 0) : a = b :=
by { cases p, { refl }, { cases nat.succ_ne_zero _ hzero } }

/-- Composition of paths. -/
def comp {a b : V} : Π {c}, path a b → path b c → path a c
| _ p (path.nil) := p
| _ p (path.cons q e) := (p.comp q).cons e

@[simp] lemma comp_cons {a b c d : V} (p : path a b) (q : path b c) (e : c ⟶ d) :
  p.comp (q.cons e) = (p.comp q).cons e := rfl

@[simp] lemma comp_nil {a b : V} (p : path a b) : p.comp path.nil = p := rfl

@[simp] lemma nil_comp {a : V} : ∀ {b} (p : path a b), path.nil.comp p = p
| a path.nil := rfl
| b (path.cons p e) := by rw [comp_cons, nil_comp]

@[simp] lemma comp_assoc {a b c : V} : ∀ {d}
  (p : path a b) (q : path b c) (r : path c d),
    (p.comp q).comp r = p.comp (q.comp r)
| c p q path.nil := rfl
| d p q (path.cons r e) := by rw [comp_cons, comp_cons, comp_cons, comp_assoc]

@[simp] lemma length_comp (p : path a b) :
  ∀ {c} (q : path b c), (p.comp q).length = p.length + q.length
| c nil := rfl
| c (cons q h) := congr_arg nat.succ q.length_comp

lemma comp_inj {p₁ p₂ : path a b} {q₁ q₂ : path b c} (hq : q₁.length = q₂.length) :
  p₁.comp q₁ = p₂.comp q₂ ↔ p₁ = p₂ ∧ q₁ = q₂ :=
begin
  refine ⟨λ h, _, by { rintro ⟨rfl, rfl⟩, refl }⟩,
  induction q₁ with d₁ e₁ q₁ f₁ ih generalizing q₂; obtain _ | ⟨q₂, f₂⟩ := q₂,
  { exact ⟨h, rfl⟩ },
  { cases hq },
  { cases hq },
  simp only [comp_cons] at h,
  obtain rfl := h.1,
  obtain ⟨rfl, rfl⟩ := ih (nat.succ.inj hq) h.2.1.eq,
  rw h.2.2.eq,
  exact ⟨rfl, rfl⟩,
end

lemma comp_inj' {p₁ p₂ : path a b} {q₁ q₂ : path b c} (h : p₁.length = p₂.length) :
  p₁.comp q₁ = p₂.comp q₂ ↔ p₁ = p₂ ∧ q₁ = q₂ :=
⟨λ h_eq, (comp_inj $ nat.add_left_cancel $
  by simpa [h] using congr_arg length h_eq).1 h_eq, by { rintro ⟨rfl, rfl⟩, refl }⟩

lemma comp_injective_left (q : path b c) : injective (λ p : path a b, p.comp q) :=
λ p₁ p₂ h, ((comp_inj rfl).1 h).1

lemma comp_injective_right (p : path a b) : injective (p.comp : path b c → path a c) :=
λ q₁ q₂ h, ((comp_inj' rfl).1 h).2

@[simp] lemma comp_inj_left {p₁ p₂ : path a b} {q : path b c} : p₁.comp q = p₂.comp q ↔ p₁ = p₂ :=
q.comp_injective_left.eq_iff

@[simp] lemma comp_inj_right {p : path a b} {q₁ q₂ : path b c} : p.comp q₁ = p.comp q₂ ↔ q₁ = q₂ :=
p.comp_injective_right.eq_iff

/-- Turn a path into a list. The list contains `a` at its head, but not `b` a priori. -/
@[simp] def to_list : Π {b : V}, path a b → list V
| b nil := []
| b (@cons _ _ _ c _ p f) := c :: p.to_list

/-- `quiver.path.to_list` is a contravariant functor. The inversion comes from `quiver.path` and
`list` having different preferred directions for adding elements. -/
@[simp] lemma to_list_comp (p : path a b) :
  ∀ {c} (q : path b c), (p.comp q).to_list = q.to_list ++ p.to_list
| c nil := by simp
| c (@cons _ _ _ d _ q f) := by simp [to_list_comp]

lemma to_list_chain_nonempty :
  ∀ {b} (p : path a b), p.to_list.chain (λ x y, nonempty (y ⟶ x)) b
| b nil := list.chain.nil
| b (cons p f) := p.to_list_chain_nonempty.cons ⟨f⟩

variables [∀ a b : V, subsingleton (a ⟶ b)]

lemma to_list_injective (a : V) : ∀ b, injective (to_list : path a b → list V)
| b nil nil h := rfl
| b nil (@cons _ _ _ c _ p f) h := by cases h
| b (@cons _ _ _ c _ p f) nil h := by cases h
| b (@cons _ _ _ c _ p f) (@cons _ _ s t u C D) h := begin
  simp only [to_list] at h,
  obtain ⟨rfl, hAC⟩ := h,
  simp [to_list_injective _ hAC],
end

@[simp] lemma to_list_inj {p q : path a b} : p.to_list = q.to_list ↔ p = q :=
(to_list_injective _ _).eq_iff

end path

end quiver

namespace prefunctor

open quiver

variables {V : Type u₁} [quiver.{v₁} V] {W : Type u₂} [quiver.{v₂} W] (F : V ⥤q W)

/-- The image of a path under a prefunctor. -/
def map_path {a : V} :
  Π {b : V}, path a b → path (F.obj a) (F.obj b)
| _ path.nil := path.nil
| _ (path.cons p e) := path.cons (map_path p) (F.map e)

@[simp] lemma map_path_nil (a : V) : F.map_path (path.nil : path a a) = path.nil := rfl
@[simp] lemma map_path_cons {a b c : V} (p : path a b) (e : b ⟶ c) :
  F.map_path (path.cons p e) = path.cons (F.map_path p) (F.map e) := rfl

@[simp] lemma map_path_comp {a b : V} (p : path a b) :
  ∀ {c : V} (q : path b c), F.map_path (p.comp q) = (F.map_path p).comp (F.map_path q)
| _ path.nil := rfl
| _ (path.cons p e) := begin dsimp, rw [map_path_comp], end

@[simp]
lemma map_path_to_path {a b : V} (f : a ⟶ b) : F.map_path f.to_path = (F.map f).to_path := rfl

end prefunctor
