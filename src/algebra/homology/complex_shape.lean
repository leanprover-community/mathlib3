/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison
-/
import logic.relation
import data.option.basic
import data.subtype
import algebra.group.defs

/-!
# Shapes of homological complexes

We define a structure `complex_shape ι` for describing the shapes of homological complexes
indexed by a type `ι`.
This is intended to capture chain complexes and cochain complexes, indexed by either `ℕ` or `ℤ`,
as well as more exotic examples.

Rather than insisting that the indexing type has a `succ` function
specifying where differentials should go,
inside `c : complex_shape` we have `c.rel : ι → ι → Prop`,
and when we define `homological_complex`
we only allow nonzero differentials `d i j` from `i` to `j` if `c.rel i j`.
Further, we require that `{ j // c.rel i j }` and `{ i // c.rel i j }` are subsingletons.
This means that the shape consists of some union of lines, rays, intervals, and circles.

Convenience functions `c.next` and `c.prev` provide, as an `option`, these related elements
when they exist.

This design aims to avoid certain problems arising from dependent type theory.
In particular we never have to ensure morphisms `d i : X i ⟶ X (succ i)` compose as
expected (which would often require rewriting by equations in the indexing type).
Instead such identities become separate proof obligations when verifying that a
complex we've constructed is of the desired shape.

If `α` is an `add_right_cancel_semigroup`, then we define `up α : complex_shape α`,
the shape appropriate for cohomology,so `d : X i ⟶ X j` is nonzero only when `j = i + 1`,
as well as `down α : complex_shape α`, appropriate for homology,
so `d : X i ⟶ X j` is nonzero only when `i = j + 1`.
(Later we'll introduce `cochain_complex` and `chain_complex` as abbreviations for
`homological_complex` with one of these shapes baked in.)
-/

open_locale classical
noncomputable theory

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
@[ext, nolint has_inhabited_instance]
structure complex_shape (ι : Type*) :=
(rel : ι → ι → Prop)
(next_eq : ∀ {i j j'}, rel i j → rel i j' → j = j')
(prev_eq : ∀ {i i' j}, rel i j → rel i' j → i = i')

namespace complex_shape
variables {ι : Type*}

/--
The complex shape where only differentials from each `X.i` to itself are allowed.

This is mostly only useful so we can describe the relation of "related in `k` steps" below.
-/
@[simps]
def refl (ι : Type*) : complex_shape ι :=
{ rel := λ i j, i = j,
  next_eq := λ i j j' w w', w.symm.trans w',
  prev_eq := λ i i' j w w', w.trans w'.symm, }

/--
The reverse of a `complex_shape`.
-/
@[simps]
def symm (c : complex_shape ι) : complex_shape ι :=
{ rel := λ i j, c.rel j i,
  next_eq := λ i j j' w w', c.prev_eq w w',
  prev_eq := λ i i' j w w', c.next_eq w w', }

@[simp]
lemma symm_symm (c : complex_shape ι) : c.symm.symm = c :=
by { ext, simp, }

/--
The "composition" of two `complex_shape`s.

We need this to define "related in k steps" later.
-/
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

/--
An option-valued arbitary choice of index `j` such that `rel i j`, if such exists.
-/
def next (c : complex_shape ι) (i : ι) : option { j // c.rel i j } :=
option.choice _

/--
An option-valued arbitary choice of index `i` such that `rel i j`, if such exists.
-/
def prev (c : complex_shape ι) (j : ι) : option { i // c.rel i j } :=
option.choice _

lemma next_eq_some (c : complex_shape ι) {i j : ι} (h : c.rel i j) : c.next i = some ⟨j, h⟩ :=
option.choice_eq _

lemma prev_eq_some (c : complex_shape ι) {i j : ι} (h : c.rel i j) : c.prev j = some ⟨i, h⟩ :=
option.choice_eq _

/--
The `complex_shape` allowing differentials from `X i` to `X (i+a)`.
(For example when `a = 1`, a cohomology theory indexed by `ℕ` or `ℤ`)
-/
@[simps]
def up' {α : Type*} [add_right_cancel_semigroup α] (a : α) : complex_shape α :=
{ rel := λ i j , i + a = j,
  next_eq := λ i j k hi hj, hi.symm.trans hj,
  prev_eq := λ i j k hi hj, add_right_cancel (hi.trans hj.symm), }

/--
The `complex_shape` allowing differentials from `X (j+a)` to `X j`.
(For example when `a = 1`, a homology theory indexed by `ℕ` or `ℤ`)
-/
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
