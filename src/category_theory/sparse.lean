import category_theory.category

universes u v

namespace category_theory

variables {C : Type u} [category_struct.{v} C]

instance sparse_category [∀ X Y : C, subsingleton (X ⟶ Y)] : category.{v} C := { }

lemma foo [∀ X Y : C, subsingleton (X ⟶ Y)] (X Y : C) (f : X ⟶ Y) : 𝟙 X ≫ f = f :=
begin
  simp,
end

end category_theory
