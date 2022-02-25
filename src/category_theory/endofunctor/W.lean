import data.W.basic
import category_theory.endofunctor.algebra

universes u₀ u₁

namespace category_theory

namespace W_type

open endofunctor

/-
We fix a W-type consisting of an index α of constructors and
their dependently indexed arities β.
-/
variables {α : Type u₀} (β : α → Type u₁)

/-- The polynomial endofunctor associated to a `W_type` -/
def polynomial : Type (max u₀ u₁) ⥤ Type (max u₀ u₁) :=
{ obj := λ X, Σ (a : α), β a → X,
  map := λ X Y f ⟨ a , b ⟩, ⟨ a , f ∘ b ⟩ }

/-- `W_type` β as an algebra of its associated polynomial endofunctor -/
def as_algebra : algebra (polynomial β) :=
{ A   := W_type β,
  str := W_type.of_sigma }

variables {β} (Y : algebra (polynomial β))

/-- The map in `Type` from the initial algebra `W_type` to any other algebra -/
def lift_f : Π (w : W_type β), Y.A
| (W_type.mk a b) := Y.str ⟨ a , λ x, lift_f (b x) ⟩

/-- The map in `endofunctor.algebra` from the initial algebra `W_type` to any other algebra -/
def lift : as_algebra β ⟶ Y := { f := lift_f Y }

lemma lift_uniq (f : as_algebra β ⟶ Y) : f = lift Y :=
begin
  ext w,
  induction w with a b hw,
  simp only [lift, lift_f],
  convert (congr_fun f.2 ⟨ a , b ⟩).symm,
  funext x,
  exact (hw x).symm,
end

instance (Y : algebra (polynomial β)) : unique (as_algebra β ⟶ Y) :=
{ default := lift Y,
  uniq := lift_uniq Y }.

/-- A `W_Type` is the initial algebra of its associated polynomial endofunctor -/
def is_initial : limits.is_initial (as_algebra β) :=
limits.is_initial.of_unique _


end W_type


end category_theory
