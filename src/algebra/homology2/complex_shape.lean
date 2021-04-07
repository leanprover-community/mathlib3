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
-/
structure complex_shape (ι : Type*) :=
(r : ι → ι → Prop)
(succ_eq : ∀ {i j j'}, r i j → r i j' → j = j')
(pred_eq : ∀ {i i' k}, r i k → r i' k → i = i')

namespace complex_shape
variables {ι : Type*}

instance subsingleton_next (c : complex_shape ι) (i : ι) :
  subsingleton { j // c.r i j } :=
begin
  fsplit,
  rintros ⟨j, rij⟩ ⟨k, rik⟩,
  congr,
  exact c.succ_eq rij rik,
end

instance subsingleton_prev (c : complex_shape ι) (j : ι) :
  subsingleton { i // c.r i j } :=
begin
  fsplit,
  rintros ⟨i, rik⟩ ⟨j, rjk⟩,
  congr,
  exact c.pred_eq rik rjk,
end

def next' (c : complex_shape ι) (i : ι) : option { j // c.r i j } :=
option.choice _

def next (c : complex_shape ι) (i : ι) : option ι :=
(c.next' i).map (λ p, p.1)

def prev' (c : complex_shape ι) (j : ι) : option { i // c.r i j } :=
option.choice _

def prev (c : complex_shape ι) (j : ι) : option ι :=
(c.prev' j).map (λ p, p.1)

lemma r_next (c : complex_shape ι) (i j : ι) (w : j ∈ c.next i) : c.r i j :=
begin
  dsimp [next, next', option.choice] at w,
  split_ifs at w,
  { simp at w, subst w,
    exact h.some.2, },
  { cases w, },
end
lemma prev_r (c : complex_shape ι) (i j : ι) (w : i ∈ c.prev j) : c.r i j :=
begin
  dsimp [prev, prev', option.choice] at w,
  split_ifs at w,
  { simp at w, subst w,
    exact h.some.2, },
  { cases w, },
end

lemma next'_eq_some (c : complex_shape ι) {i j : ι} (h : c.r i j) : c.next' i = some ⟨j, h⟩ :=
begin
  dsimp [next, next', option.choice],
  let w : nonempty { j // c.r i j } := ⟨⟨j, h⟩⟩,
  rw dif_pos w,
  simp only [option.map_some', subtype.val_eq_coe],
  apply subsingleton.elim,
end
lemma prev'_eq_some (c : complex_shape ι) {i j : ι} (h : c.r i j) : c.prev' j = some ⟨i, h⟩ :=
begin
  dsimp [prev, prev', option.choice],
  let w : nonempty { i // c.r i j } := ⟨⟨i, h⟩⟩,
  rw dif_pos w,
  simp only [option.map_some', subtype.val_eq_coe],
  apply subsingleton.elim,
end

lemma next_eq_some (c : complex_shape ι) {i j : ι} (h : c.r i j) : c.next i = some j :=
begin
  dsimp [next, next', option.choice],
  let w : nonempty { j // c.r i j } := ⟨⟨j, h⟩⟩,
  rw dif_pos w,
  simp only [option.map_some', subtype.val_eq_coe],
  apply c.succ_eq w.some.2 h,
end
lemma prev_eq_some (c : complex_shape ι) {i j : ι} (h : c.r i j) : c.prev j = some i :=
begin
  dsimp [prev, prev', option.choice],
  let w : nonempty { i // c.r i j } := ⟨⟨i, h⟩⟩,
  rw dif_pos w,
  simp only [option.map_some', subtype.val_eq_coe],
  apply c.pred_eq w.some.2 h,
end

def succ (c : complex_shape ι) (i : ι) := { j // c.r i j }
def pred (c : complex_shape ι) (j : ι) := { i // c.r i j }

lemma r_of_nonempty_succ (c : complex_shape ι) {i : ι} (h : nonempty (c.succ i)) :
  c.r i h.some.1 := h.some.2
lemma r_of_nonempty_pred (c : complex_shape ι) {j : ι} (h : nonempty (c.pred j)) :
  c.r h.some.1 j := h.some.2

lemma nonempty_succ (c : complex_shape ι) {i j : ι} (r : c.r i j) : nonempty (c.succ i) :=
⟨⟨j, r⟩⟩
lemma nonempty_pred (c : complex_shape ι) {i j : ι} (r : c.r i j) : nonempty (c.pred j) :=
⟨⟨i, r⟩⟩

lemma nonempty_succ_some (c : complex_shape ι) {i j : ι} (r : c.r i j) :
  (c.nonempty_succ r).some.1 = j :=
c.succ_eq (c.nonempty_succ r).some.2 r
lemma nonempty_pred_some (c : complex_shape ι) {i j : ι} (r : c.r i j) :
  (c.nonempty_pred r).some.1 = i :=
c.pred_eq (c.nonempty_pred r).some.2 r

instance (c : complex_shape ι) (i : ι) : subsingleton (c.succ i) :=
begin
  fsplit,
  rintros ⟨j, rij⟩ ⟨k, rik⟩,
  congr,
  exact c.succ_eq rij rik,
end

instance (c : complex_shape ι) (k : ι) : subsingleton (c.pred k) :=
begin
  fsplit,
  rintros ⟨i, rik⟩ ⟨j, rjk⟩,
  congr,
  exact c.pred_eq rik rjk,
end

def r' (c : complex_shape ι) : ℤ → ι → ι → Prop
| (int.of_nat 0) i j := i = j
| (int.of_nat (n+1)) i j := ∃ k, c.r i k ∧ r' (int.of_nat n) k j
| (int.neg_succ_of_nat 0) i j := c.r j i
| (int.neg_succ_of_nat (n+1)) i j := ∃ k, c.r j k ∧ r' (int.neg_succ_of_nat n) k j

def up' {α : Type*} [add_right_cancel_semigroup α] (a : α) : complex_shape α :=
{ r := λ i j , i + a = j,
  succ_eq := λ i j k hi hj, hi.symm.trans hj,
  pred_eq := λ i j k hi hj, add_right_cancel (hi.trans hj.symm), }

def down' {α : Type*} [add_right_cancel_semigroup α] (a : α) : complex_shape α :=
{ r := λ i j , j + a = i,
  succ_eq := λ i j k hi hj, add_right_cancel (hi.trans (hj.symm)),
  pred_eq := λ i j k hi hj, hi.symm.trans hj, }

def up {α : Type*} [add_right_cancel_semigroup α] [has_one α] : complex_shape α :=
up' 1

def down {α : Type*} [add_right_cancel_semigroup α] [has_one α] : complex_shape α :=
down' 1

end complex_shape
