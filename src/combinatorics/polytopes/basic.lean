import combinatorics.polytopes.flag

namespace polytope

universe u

class prepolytope {α : Type u} extends partial_order α, order_top α, graded α : Type u :=
(flag_height : ℕ)
(flags_same_height : ∀ Φ : flag α, fintype.card Φ = flag_height)
(diamond : ∀ {a b : α}, a < b → grade b = grade a + 2 → ∃ x y, set.Ioo a b = {x, y})

end polytope
