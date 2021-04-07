import tactic.basic
import tactic.linarith

open_locale classical
noncomputable theory

def option.choice (α : Type*) : option α :=
if h : nonempty α then
  some h.some
else
  none

/--
A `c : complex_shape ι` describes the shape of a chain complex,
with chain groups indexed by `ι`.
Typically `ι` will be `ℕ`, `ℤ`, or `fin n`.

There is a relation `r : ι → ι → Prop`,
and we will only allow a non-zero differential from `i` to `j` when `r i j`.

There are axioms which imply `{ j // c.r i j }` and `{ i // c.r i j }` are subsingletons.
This means that the shape consists of some union of lines, rays, intervals, and circles.

Below we define `c.next` and `c.prev` which provide, as an `option`, these related elements.
-/
structure complex_shape (ι : Type*) :=
(r : ι → ι → Prop)
(next_eq : ∀ {i j j'}, r i j → r i j' → j = j')
(prev_eq : ∀ {i i' k}, r i k → r i' k → i = i')

namespace complex_shape
variables {ι : Type*}

instance subsingleton_next (c : complex_shape ι) (i : ι) :
  subsingleton { j // c.r i j } :=
begin
  fsplit,
  rintros ⟨j, rij⟩ ⟨k, rik⟩,
  congr,
  exact c.next_eq rij rik,
end

instance subsingleton_prev (c : complex_shape ι) (j : ι) :
  subsingleton { i // c.r i j } :=
begin
  fsplit,
  rintros ⟨i, rik⟩ ⟨j, rjk⟩,
  congr,
  exact c.prev_eq rik rjk,
end

def next (c : complex_shape ι) (i : ι) : option { j // c.r i j } :=
option.choice _

def prev (c : complex_shape ι) (j : ι) : option { i // c.r i j } :=
option.choice _

lemma next_eq_some (c : complex_shape ι) {i j : ι} (h : c.r i j) : c.next i = some ⟨j, h⟩ :=
begin
  dsimp [next, option.choice],
  let w : nonempty { j // c.r i j } := ⟨⟨j, h⟩⟩,
  rw dif_pos w,
  simp only [option.map_some', subtype.val_eq_coe],
  apply subsingleton.elim,
end
lemma prev_eq_some (c : complex_shape ι) {i j : ι} (h : c.r i j) : c.prev j = some ⟨i, h⟩ :=
begin
  dsimp [prev, option.choice],
  let w : nonempty { i // c.r i j } := ⟨⟨i, h⟩⟩,
  rw dif_pos w,
  simp only [option.map_some', subtype.val_eq_coe],
  apply subsingleton.elim,
end

def r_step (c : complex_shape ι) : ℤ → ι → ι → Prop
| (int.of_nat 0) i j := i = j
| (int.of_nat (n+1)) i j := ∃ k, c.r i k ∧ r_step (int.of_nat n) k j
| (int.neg_succ_of_nat 0) i j := c.r j i
| (int.neg_succ_of_nat (n+1)) i j := ∃ k, c.r j k ∧ r_step (int.neg_succ_of_nat n) k j

def up' {α : Type*} [add_right_cancel_semigroup α] (a : α) : complex_shape α :=
{ r := λ i j , i + a = j,
  next_eq := λ i j k hi hj, hi.symm.trans hj,
  prev_eq := λ i j k hi hj, add_right_cancel (hi.trans hj.symm), }

def down' {α : Type*} [add_right_cancel_semigroup α] (a : α) : complex_shape α :=
{ r := λ i j , j + a = i,
  next_eq := λ i j k hi hj, add_right_cancel (hi.trans (hj.symm)),
  prev_eq := λ i j k hi hj, hi.symm.trans hj, }

def up {α : Type*} [add_right_cancel_semigroup α] [has_one α] : complex_shape α :=
up' 1

def down {α : Type*} [add_right_cancel_semigroup α] [has_one α] : complex_shape α :=
down' 1

end complex_shape
