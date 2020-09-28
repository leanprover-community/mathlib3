import algebra.ordered_ring
import algebra.invertible

-- Perhaps this is not generally true...
example {α : Type*} [ordered_semiring α] {a : α} [invertible a] : 0 ≤ ⅟a ↔ 0 ≤ a :=
sorry
