/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison
-/
import logic.relation
import data.option.basic
import data.subtype
import algebra.group.defs

open_locale classical
noncomputable theory

def option.choice (α : Type*) : option α :=
if h : nonempty α then
  some h.some
else
  none

lemma option.choice_eq {α : Type*} [subsingleton α] (a : α) : option.choice α = some a :=
begin
  dsimp [option.choice],
  let w : nonempty α := ⟨a⟩,
  rw dif_pos w,
  simp only [option.map_some', subtype.val_eq_coe],
  apply subsingleton.elim,
end

/--
A `c : complex_shape ι` describes the shape of a chain complex,
with chain groups indexed by `ι`.
Typically `ι` will be `ℕ`, `ℤ`, or `fin n`.

There is a relation `rel : ι → ι → Prop`,
and we will only allow a non-zero differential from `i` to `j` when `rel i j`.

There are axioms which imply `{ j // c.rel i j }` and `{ i // c.rel i j }` are subsingletons.
This means that the shape consists of some union of lines, rays, intervals, and circles.

Below we define `c.next` and `c.prev` which provide, as an `option`, these related elements.
-/
@[ext]
structure complex_shape (ι : Type*) :=
(rel : ι → ι → Prop)
(next_eq : ∀ {i j j'}, rel i j → rel i j' → j = j')
(prev_eq : ∀ {i i' j}, rel i j → rel i' j → i = i')

namespace complex_shape
variables {ι : Type*}

@[simps]
def refl (ι : Type*) : complex_shape ι :=
{ rel := λ i j, i = j,
  next_eq := λ i j j' w w', w.symm.trans w',
  prev_eq := λ i i' j w w', w.trans w'.symm, }

@[simps]
def symm (c : complex_shape ι) : complex_shape ι :=
{ rel := λ i j, c.rel j i,
  next_eq := λ i j j' w w', c.prev_eq w w',
  prev_eq := λ i i' j w w', c.next_eq w w', }

lemma symm_symm (c : complex_shape ι) : c.symm.symm = c :=
by { ext, simp, }

-- We need this to define "related in k steps" later.
@[simp]
def trans (c₁ c₂ : complex_shape ι) : complex_shape ι :=
{ rel := relation.comp c₁.rel c₂.rel,
  next_eq := λ i j j' w w',
  begin
    obtain ⟨k, w₁, w₂⟩ := w,
    obtain ⟨k', w₁', w₂'⟩ := w',
    rw c₁.next_eq w₁ w₁' at w₂,
    exact c₂.next_eq w₂ w₂',
  end,
  prev_eq := λ i i' j w w',
  begin
    obtain ⟨k, w₁, w₂⟩ := w,
    obtain ⟨k', w₁', w₂'⟩ := w',
    rw c₂.prev_eq w₂ w₂' at w₁,
    exact c₁.prev_eq w₁ w₁',
  end }

instance subsingleton_next (c : complex_shape ι) (i : ι) :
  subsingleton { j // c.rel i j } :=
begin
  fsplit,
  rintros ⟨j, rij⟩ ⟨k, rik⟩,
  congr,
  exact c.next_eq rij rik,
end

instance subsingleton_prev (c : complex_shape ι) (j : ι) :
  subsingleton { i // c.rel i j } :=
begin
  fsplit,
  rintros ⟨i, rik⟩ ⟨j, rjk⟩,
  congr,
  exact c.prev_eq rik rjk,
end

def next (c : complex_shape ι) (i : ι) : option { j // c.rel i j } :=
option.choice _

def prev (c : complex_shape ι) (j : ι) : option { i // c.rel i j } :=
option.choice _

lemma next_eq_some (c : complex_shape ι) {i j : ι} (h : c.rel i j) : c.next i = some ⟨j, h⟩ :=
option.choice_eq _

lemma prev_eq_some (c : complex_shape ι) {i j : ι} (h : c.rel i j) : c.prev j = some ⟨i, h⟩ :=
option.choice_eq _

/--
The relation of being related in `k` steps.
-/
def rel_step (c : complex_shape ι) (k : ℤ) : ι → ι → Prop :=
if h : 0 ≤ k then
  ((complex_shape.trans c)^[k.nat_abs] (complex_shape.refl ι)).rel
else
  ((complex_shape.trans c.symm)^[k.nat_abs] (complex_shape.refl ι)).rel

instance subsingleton_rel_step (c : complex_shape ι) (k : ℤ) (i : ι) :
  subsingleton { j // c.rel_step k i j } :=
begin
  dsimp [rel_step],
  split_ifs,
  apply complex_shape.subsingleton_next,
  apply complex_shape.subsingleton_next,
end

-- TODO we may need to prove that `c.rel_step n i j → c.rel_step m j k → c.rel_step (n+m) i k`
-- (and also the converse, when `n` and `m` are both non-negative).

@[simps]
def up' {α : Type*} [add_right_cancel_semigroup α] (a : α) : complex_shape α :=
{ rel := λ i j , i + a = j,
  next_eq := λ i j k hi hj, hi.symm.trans hj,
  prev_eq := λ i j k hi hj, add_right_cancel (hi.trans hj.symm), }

@[simps]
def down' {α : Type*} [add_right_cancel_semigroup α] (a : α) : complex_shape α :=
{ rel := λ i j , j + a = i,
  next_eq := λ i j k hi hj, add_right_cancel (hi.trans (hj.symm)),
  prev_eq := λ i j k hi hj, hi.symm.trans hj, }

/--
The `complex_shape` appropriate for cohomology, so `d : X i ⟶ X j` only when `j = i + 1`.
-/
@[simps]
def up (α : Type*) [add_right_cancel_semigroup α] [has_one α] : complex_shape α :=
up' 1

/--
The `complex_shape` appropriate for homology, so `d : X i ⟶ X j` only when `i = j + 1`.
-/
@[simps]
def down (α : Type*) [add_right_cancel_semigroup α] [has_one α] : complex_shape α :=
down' 1

end complex_shape
