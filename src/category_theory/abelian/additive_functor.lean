import category_theory.preadditive
import category_theory.abelian.basic

namespace category_theory

class functor.additive {C D : Type*} [category C] [category D]
  [preadditive C] [preadditive D] (F : C ⥤ D) : Prop :=
(exists_hom' : ∀ (X Y : C), ∃ f : (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y),
  ∀ g : X ⟶ Y, F.map g = f g)

section preadditive
variables {C D : Type*} [category C] [category D] [preadditive C]
  [preadditive D] (F : C ⥤ D) [functor.additive F]

namespace functor.additive

lemma exists_hom (X Y : C) : ∃ f : (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y),
  ∀ g : X ⟶ Y, F.map g = f g := functor.additive.exists_hom' _ _

def of_is_hom (G : C ⥤ D)
  (map_zero : ∀ X Y : C, G.map (0 : X ⟶ Y) = 0)
  (map_add : ∀ (X Y : C) (f g : X ⟶ Y), G.map (f + g) = G.map f + G.map g) :
  functor.additive G := functor.additive.mk $ λ X Y,
⟨⟨λ f, G.map f, map_zero _ _, map_add _ _⟩, λ g, rfl⟩

end functor.additive

namespace functor

@[simps]
def add_map {X Y : C} : (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y) :=
{ to_fun := λ f, F.map f,
  map_zero' := begin
    rcases functor.additive.exists_hom F X Y with ⟨f, hf⟩,
    simp [hf],
  end,
  map_add' := begin
    rcases functor.additive.exists_hom F X Y with ⟨f, hf⟩,
    simp [hf],
  end }

lemma add_map_spec {X Y : C} {f : X ⟶ Y} : F.add_map f = F.map f := rfl

@[simp]
lemma map_zero {X Y : C} : F.map (0 : X ⟶ Y) = 0 := F.add_map.map_zero

@[simp]
lemma map_add {X Y : C} {f g : X ⟶ Y} : F.map (f + g) = F.map f + F.map g :=
F.add_map.map_add _ _

@[simp]
lemma map_neg {X Y : C} {f : X ⟶ Y} : F.map (-f) = - F.map f :=
F.add_map.map_neg _

@[simp]
lemma map_sub {X Y : C} {f g : X ⟶ Y} : F.map (f - g) = F.map f - F.map g :=
F.add_map.map_sub _ _

end functor
end preadditive

--PROJECT: Prove that an additive functor preserves finite biproducts
--PROJECT: Prove that a functor is additive it it preserves finite biproducts

end category_theory
