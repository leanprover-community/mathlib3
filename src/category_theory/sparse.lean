import category_theory.category

universes u v

namespace category_theory

variables {C : Type u} [category_struct.{v} C]

-- This doesn't work well as an instance; use it to construct specific cases.
def sparse_category [∀ X Y : C, subsingleton (X ⟶ Y)] : category.{v} C := { }

end category_theory
