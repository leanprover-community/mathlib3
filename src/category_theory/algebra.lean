import category_theory.functor_category

universes v₁ u₁

namespace category_theory

variables {C : Type u₁} [category.{v₁} C]

structure algebra (F : C ⥤ C) :=
(carrier : C)
(str_map : F.obj carrier ⟶ carrier)

namespace algebra

variables {F : C ⥤ C} (A : algebra F) {A₀ A₁ A₂ : algebra F}

structure hom (A₀ A₁ : algebra F) :=
(to_hom : A₀.1 ⟶ A₁.1)
(square' : F.map to_hom ≫ A₁.str_map = A₀.str_map ≫ to_hom . obviously)

restate_axiom hom.square'
attribute [simp, reassoc] hom.square
namespace hom

def id : hom A A := { to_hom := 𝟙 _ }

instance : inhabited (hom A A) := ⟨{ to_hom := 𝟙 _ }⟩

def comp (f : hom A₀ A₁) (g : hom A₁ A₂) : hom A₀ A₂ := { to_hom := f.1 ≫ g.1 }

end hom

instance (F : C ⥤ C) : category_struct (algebra F) :=
{ hom := hom,
  id := hom.id,
  comp := @hom.comp _ _ _ }

@[simp] lemma id_eq_id : algebra.hom.id A = 𝟙 A := rfl

@[simp] lemma id_f : (𝟙 _ : A ⟶ A).1 = 𝟙 A.1 := rfl

variables {A₀ A₁ A₂} (f : A₀ ⟶ A₁) (g : A₁ ⟶ A₂)

@[simp] lemma comp_eq_comp : algebra.hom.comp f g = f ≫ g := rfl

@[simp] lemma comp_f : (f ≫ g).1 = f.1 ≫ g.1 := rfl

instance (F : C ⥤ C) : category (algebra F) := sorry

end algebra


namespace algebra



end algebra

end category_theory
