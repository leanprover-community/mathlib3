import tactic.basic
import tactic.linarith

/--
A `c : complex_shape ι` describes the shape of a chain complex,
with chain groups indexed by `ι`.
Typically `ι` will be `ℕ`, `ℤ`, or `fin n`.

There is a relation `r : ι → ι → Prop`, and we will only allow a non-zero differential from `i` to `j`
when `r i j`.

There are axioms which imply `{ j // c.r i j }` and `{ i // c.r i j }` are subsingletons.
This means that the shape consists of some union of lines, rays, intervals, and circles.
-/
structure complex_shape (ι : Type*) :=
(r : ι → ι → Prop)
(succ_eq : ∀ {i j k}, r i j → r i k → j = k)
(pred_eq : ∀ {i j k}, r i k → r j k → i = j)

namespace complex_shape
variables {ι : Type*}

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

def nat (s : ℕ) : complex_shape ℕ :=
{ r := λ i j, i + s = j,
  succ_eq := by tidy,
  pred_eq := λ i j k hi hj, by linarith, }

def int (s : ℤ) : complex_shape ℤ :=
{ r := λ i j, i + s = j,
  succ_eq := by tidy,
  pred_eq := λ i j k hi hj, by linarith, }

end complex_shape
