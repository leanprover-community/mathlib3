import tactic.basic

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

end complex_shape
