import category_theory.category
import category_theory.concrete_category

universes w v u

namespace category_theory

-- https://ncatlab.org/nlab/show/bicategory
class two_category_struct (obj : Type u) extends category_struct.{v} obj :=
[hom_cats : Π (a b : obj), category.{w} (a ⟶ b)]
(left_whisker : Π {a b c : obj} {f g : a ⟶ b} (h : b ⟶ c) (η : f ⟶ g), f ≫ h ⟶ g ≫ h)
(right_whisker : Π {a b c : obj} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h), f ≫ g ⟶ f ≫ h)
(left_unitor : Π {a b : obj} (f : a ⟶ b), 𝟙 _ ≫ f ≅ f)
(right_unitor : Π {a b : obj} (f : a ⟶ b), f ≫ 𝟙 _ ≅ f)
(associator : Π {a b c d : obj} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d), (f ≫ g) ≫ h ≅ f ≫ g ≫ h)

attribute [instance] two_category_struct.hom_cats

notation η ` ▶ ` f:50 := two_category_struct.right_whisker f η
notation η ` ◄ ` f:50 := two_category_struct.left_whisker η f

notation `λ_` := two_category_struct.left_unitor
notation `ρ_` := two_category_struct.right_unitor
notation `α_` := two_category_struct.associator

-- https://ncatlab.org/nlab/show/bicategory
class two_category (obj : Type u) extends two_category_struct.{w v} obj :=
(ax₁ : ∀ {a b c : obj} (f : a ⟶ b) (g : b ⟶ c), 𝟙 g ▶ f = 𝟙 (f ≫ g) . obviously)
(ax₂ : ∀ {a b c : obj} (f : a ⟶ b) (g : b ⟶ c), g ◄ 𝟙 f = 𝟙 (f ≫ g) . obviously)
(ax₃ : ∀ {a b c : obj} {f g h : a ⟶ b} (i : b ⟶ c) (η : f ⟶ g) (θ : g ⟶ h),
  (i ◄ η) ≫ (i ◄ θ) = (i ◄ (η ≫ θ)) . obviously)
(ax₄ : ∀ {a b c : obj} {f : a ⟶ b} (g h i : b ⟶ c) (η : g ⟶ h) (θ : h ⟶ i),
  (η ▶ f) ≫ (θ ▶ f) = ((η ≫ θ) ▶ f) . obviously)
(ax₅ : ∀ {a b : obj} (f g : a ⟶ b) (η : f ⟶ g),
  (𝟙 _ ◄ η) ≫ (ρ_ g).hom = (ρ_ f).hom ≫ η . obviously)
(ax₆ : ∀ {a b : obj} (f g : a ⟶ b) (η : f ⟶ g),
  (η ▶ 𝟙 _) ≫ (λ_ g).hom = (λ_ f).hom ≫ η . obviously)
(ax₇ : ∀ {a b c d : obj} (f : a ⟶ b) (g : b ⟶ c) (h i : c ⟶ d) (η : h ⟶ i),
  (η ▶ (f ≫ g)) ≫ (associator f g i).hom = (associator f g h).hom ≫ ((η ▶ g) ▶ f) . obviously)
(ax₈ : ∀ {a b c d : obj} (f : a ⟶ b) {g h : b ⟶ c} (i : c ⟶ d) (η : g ⟶ h),
  (i ◄ (η ▶ f)) ≫ (associator f h i).hom = (associator f g i).hom ≫ ((i ◄ η) ▶ f) . obviously)
(ax₉ : ∀ {a b c d : obj} {f g : a ⟶ b} (h : b ⟶ c) (i : c ⟶ d) (η : f ⟶ g),
  (_ ◄ (_ ◄ η)) ≫ (associator g h i).hom = (associator f h i).hom ≫ (_ ◄ η) . obviously)
(ax₁₀ : ∀ {a b c : obj} {f g : a ⟶ b} {h i : b ⟶ c} (η : f ⟶ g) (θ : h ⟶ i),
  (θ ▶ _) ≫ (_ ◄ η) = (_ ◄ η) ≫ (θ ▶ _) . obviously)
(ax₁₁ : ∀ {a b c : obj} (f : a ⟶ b) (g : b ⟶ c),
  (associator f _ g).hom ≫ ((λ_ g).hom ▶ _) = (g ◄ (ρ_ f).hom) . obviously)
(ax₁₂ : ∀ {a b c d e : obj} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e),
    (i ◄ (associator f g h).hom) ≫ (associator f (g ≫ h) i).hom ≫ ((associator g h i).hom ▶ f)
  = (associator (f ≫ g) h i).hom ≫ (associator f g (h ≫ i)).hom . obviously)

variables (C D : Type u) [two_category.{w v} C] [two_category.{w v} D]

-- https://ncatlab.org/nlab/show/pseudofunctor
structure pseudofunctor :=
(P : C → D)
(func : Π (x y : C), (x ⟶ y) ⥤ (P x ⟶ P y))
(ids : Π (x : C), 𝟙 (P x) ≅ (func _ _).obj (𝟙 x))
(comps : Π {x y z : C} (f : x ⟶ y) (g : y ⟶ z),
  (func x y).obj f ≫ (func y z).obj g ≅ (func x z).obj (f ≫ g))
(comps_natural_left : ∀ {x y z : C} {f f' : x ⟶ y} (g : y ⟶ z) (η : f ⟶ f'),
  (comps f g).hom ≫ (func x z).map (_ ◄ η) = (_ ◄ (func x y).map η) ≫ (comps f' g).hom
    . obviously)
(comps_natural_right : ∀ {x y z : C} (f : x ⟶ y) {g g' : y ⟶ z} (η : g ⟶ g'),
  (comps f g).hom ≫ (func x z).map (η ▶ _) = ((func y z).map η ▶ _) ≫ (comps f g').hom
    . obviously)
(left_unitors : ∀ {x y : C} (f : x ⟶ y),
  (_ ◄ (ids _).hom) ≫ (comps _ _).hom ≫ (func _ _).map (λ_ f).hom = (λ_ _).hom
    . obviously)
(right_unitors : ∀ {x y : C} (f : x ⟶ y),
  ((ids _).hom ▶ _) ≫ (comps _ _).hom ≫ (func _ _).map (ρ_ f).hom = (ρ_ _).hom
    . obviously)
(assoc : ∀ {w x y z : C} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z),
  (α_ ((func _ _).obj f) ((func _ _).obj g) ((func _ _).obj h)).hom ≫ ((comps _ _).hom ▶ _) ≫ (comps _ _).hom =
  (_ ◄ (comps _ _).hom) ≫ (comps _ _).hom ≫ (func _ _).map (α_ f g h).hom . obviously)

def pseudofunctor.id : pseudofunctor C C :=
{ P := λ X, X,
  func := λ X Y, 𝟭 _,
  ids := λ X, iso.refl _,
  comps := λ X Y Z f g, iso.refl _ }

structure CAT :=
{α : Type u}
[str : category.{v} α]

instance : has_coe_to_sort CAT :=
{ S := Type u,
  coe := CAT.α }

instance str (C : CAT.{v u}) : category.{v u} C := C.str

instance : two_category CAT :=
{ hom := λ X Y, X ⥤ Y,
  id := λ X, 𝟭 _,
  comp := λ X Y Z f g, f ⋙ g,
  left_unitor := λ X Y, functor.right_unitor,
  right_unitor := λ X Y, functor.left_unitor,
  left_whisker := λ X Y Z f g h α, whisker_right α _,
  right_whisker := λ X Y Z f g h α, whisker_left _ α,
  associator := λ X Y Z W f g h, functor.associator _ _ _ }

end category_theory
