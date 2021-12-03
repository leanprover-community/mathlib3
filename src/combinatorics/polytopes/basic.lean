import combinatorics.polytopes.flag

namespace polytope

universe u

/-- A prepolytope is a graded partial order satisfying the diamond condition. -/
class prepolytope (α : Type u) extends partial_order α, order_top α, graded α : Type u :=
(diamond : ∀ {a b : α}, a < b → grade b = grade a + 2 → ∃ x y, set.Ioo a b = {x, y})

/-- A polytope is a strongly connected prepolytope. -/
class polytope (α : Type u) extends prepolytope α : Type u :=
(scon : graded.strong_connected α)

end polytope
