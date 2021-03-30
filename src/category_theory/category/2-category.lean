import category_theory.category
import category_theory.concrete_category

universes w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

namespace category_theory
open category

-- https://ncatlab.org/nlab/show/bicategory
class two_category_struct (obj : Type u₁) extends category_struct.{v₁} obj :=
[hom_cats : Π (a b : obj), category.{w₁} (a ⟶ b)]
(left_whisker : Π {a b c : obj} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c), f ≫ h ⟶ g ≫ h)
(right_whisker : Π {a b c : obj} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h), f ≫ g ⟶ f ≫ h)
(left_unitor : Π {a b : obj} (f : a ⟶ b), 𝟙 _ ≫ f ≅ f)
(right_unitor : Π {a b : obj} (f : a ⟶ b), f ≫ 𝟙 _ ≅ f)
(associator : Π {a b c d : obj} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d), (f ≫ g) ≫ h ≅ f ≫ g ≫ h)

attribute [instance] two_category_struct.hom_cats

infixr ` ◀ `:70 := two_category_struct.right_whisker
infixr ` ▶ `:70 := two_category_struct.left_whisker

notation `λ_` := two_category_struct.left_unitor
notation `ρ_` := two_category_struct.right_unitor
notation `α_` := two_category_struct.associator

-- https://ncatlab.org/nlab/show/bicategory
class two_category (obj : Type u₁) extends two_category_struct.{w₁ v₁} obj :=
(left_whisker_id' : ∀ {a b c : obj} (f : a ⟶ b) (g : b ⟶ c), 𝟙 f ▶ g = 𝟙 (f ≫ g) . obviously)
(id_right_whisker' : ∀ {a b c : obj} (f : a ⟶ b) (g : b ⟶ c), f ◀ 𝟙 g = 𝟙 (f ≫ g) . obviously)
(left_whisker_comp' : ∀ {a b c : obj} {f g h : a ⟶ b} (i : b ⟶ c) (η : f ⟶ g) (θ : g ⟶ h),
  (η ▶ i) ≫ (θ ▶ i) = ((η ≫ θ) ▶ i) . obviously)
(right_whisker_comp' : ∀ {a b c : obj} {f : a ⟶ b} (g h i : b ⟶ c) (η : g ⟶ h) (θ : h ⟶ i),
  (f ◀ η) ≫ (f ◀ θ) = (f ◀ (η ≫ θ)) . obviously)
(left_unitor_naturality' : ∀ {a b : obj} (f g : a ⟶ b) (η : f ⟶ g),
  (𝟙 _ ◀ η) ≫ (λ_ g).hom = (λ_ f).hom ≫ η . obviously)
(right_unitor_naturality' : ∀ {a b : obj} (f g : a ⟶ b) (η : f ⟶ g),
  (η ▶ 𝟙 _) ≫ (ρ_ g).hom = (ρ_ f).hom ≫ η . obviously)
(associator_naturality_right' : ∀ {a b c d : obj} (f : a ⟶ b) (g : b ⟶ c) (h i : c ⟶ d) (η : h ⟶ i),
  ((f ≫ g) ◀ η) ≫ (α_ f g i).hom = (α_ f g h).hom ≫ (f ◀ (g ◀ η)) . obviously)
(associator_naturality_middle' : ∀ {a b c d} (f : a ⟶ b) {g h : b ⟶ c} (i : c ⟶ d) (η : g ⟶ h),
  ((f ◀ η) ▶ i) ≫ (α_ f h i).hom = (associator f g i).hom ≫ (f ◀ (η ▶ i)) . obviously)
(associator_naturality_left' : ∀ {a b c d : obj} {f g : a ⟶ b} (h : b ⟶ c) (i : c ⟶ d) (η : f ⟶ g),
  ((η ▶ _) ▶ _) ≫ (α_ g h i).hom = (α_ f h i).hom ≫ (η ▶ _) . obviously)
(exchange' : ∀ {a b c : obj} {f g : a ⟶ b} {h i : b ⟶ c} (η : f ⟶ g) (θ : h ⟶ i),
  (_ ◀ θ) ≫ (η ▶ _) = (η ▶ _) ≫ (_ ◀ θ) . obviously)
(triangle' : ∀ {a b c : obj} (f : a ⟶ b) (g : b ⟶ c),
  (α_ f _ g).hom ≫ (_ ◀ (λ_ g).hom) = ((ρ_ f).hom ▶ g) . obviously)
(pentagon' : ∀ {a b c d e : obj} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e),
    ((α_ f g h).hom ▶ i) ≫ (α_ f (g ≫ h) i).hom ≫ (f ◀ (α_ g h i).hom)
  = (α_ (f ≫ g) h i).hom ≫ (α_ f g (h ≫ i)).hom . obviously)

restate_axiom two_category.left_whisker_id'
restate_axiom two_category.id_right_whisker'
restate_axiom two_category.left_whisker_comp'
restate_axiom two_category.right_whisker_comp'
restate_axiom two_category.left_unitor_naturality'
restate_axiom two_category.right_unitor_naturality'
restate_axiom two_category.associator_naturality_right'
restate_axiom two_category.associator_naturality_middle'
restate_axiom two_category.associator_naturality_left'
restate_axiom two_category.exchange'
restate_axiom two_category.triangle'
restate_axiom two_category.pentagon'

attribute [simp] two_category.left_whisker_id two_category.id_right_whisker
attribute [simp, reassoc]
  two_category.left_whisker_comp
  two_category.right_whisker_comp
  two_category.left_unitor_naturality
  two_category.right_unitor_naturality
  two_category.associator_naturality_right
  two_category.associator_naturality_middle
  two_category.associator_naturality_left
  two_category.triangle
  two_category.pentagon

open two_category

variables {C : Type u₁} [two_category.{w₁ v₁} C]
variables {D : Type u₂} [two_category.{w₂ v₂} D]
variables {E : Type u₃} [two_category.{w₃ v₃} E]

def hcomp {a b c : C} {f f' : a ⟶ b} {g g' : b ⟶ c} (η : f ⟶ f') (θ : g ⟶ g') :
  f ≫ g ⟶ f' ≫ g' :=
(_ ◀ θ) ≫ (η ▶ _)

infixr ` ■ `:65 := hcomp

@[reassoc]
lemma hcomp_eq_right_comp_left {a b c : C} {f f' : a ⟶ b} {g g' : b ⟶ c} (η : f ⟶ f') (θ : g ⟶ g') :
  η ■ θ = (_ ◀ θ) ≫ (η ▶ _) :=
rfl

@[reassoc]
lemma hcomp_eq_left_comp_right {a b c : C} {f f' : a ⟶ b} {g g' : b ⟶ c} (η : f ⟶ f') (θ : g ⟶ g') :
  η ■ θ = (η ▶ _) ≫ (_ ◀ θ) :=
exchange _ _

lemma associator_naturality {a b c d : C} {f f' : a ⟶ b} {g g' : b ⟶ c} {h h' : c ⟶ d}
  (η : f ⟶ f') (θ : g ⟶ g') (ι : h ⟶ h') :
  ((η ■ θ) ■ ι) ≫ (α_ f' g' h').hom = (α_ f g h).hom ≫ (η ■ (θ ■ ι)) :=
by
  rw [hcomp_eq_left_comp_right, category.assoc, associator_naturality_right,
    hcomp_eq_left_comp_right, ←left_whisker_comp, category.assoc,
    associator_naturality_middle_assoc, associator_naturality_left_assoc, right_whisker_comp,
    ←hcomp_eq_left_comp_right, ←hcomp_eq_left_comp_right]

@[simps]
def left_whisker_iso {a b c : C} {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c) :
  f ≫ h ≅ g ≫ h :=
{ hom := η.hom ▶ h,
  inv := η.inv ▶ h }

@[simps]
def right_whisker_iso {a b c : C} {g h : b ⟶ c} (η : g ≅ h) (f : a ⟶ b) :
  f ≫ g ≅ f ≫ h :=
{ hom := _ ◀ η.hom,
  inv := _ ◀ η.inv }

infixr ` ▶ `:70 := left_whisker_iso

lemma id_right_whisker_eq_iff {x y : C} (f g : x ⟶ y) (η η' : f ⟶ g):
  𝟙 _ ◀ η = 𝟙 _ ◀ η' ↔ η = η' :=
by simp [←cancel_mono (λ_ g).hom]

lemma left_whisker_id_eq_iff {x y : C} (f g : x ⟶ y) (η η' : f ⟶ g):
  η ▶ 𝟙 _ = η' ▶ 𝟙 _ ↔ η = η' :=
by simp [←cancel_mono (ρ_ g).hom]

@[reassoc]
lemma associator_left_unitor {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
  (α_ (𝟙 x) f g).hom ≫ (λ_ (f ≫ g)).hom = (λ_ _).hom ▶ _ :=
begin
  rw [←id_right_whisker_eq_iff, ←cancel_epi (α_ (𝟙 x) (𝟙 x ≫ f) g).hom,
    ←cancel_epi ((α_ (𝟙 _) (𝟙 _) f) ▶ g).hom, ←associator_naturality_middle, left_whisker_iso_hom,
    left_whisker_comp_assoc, triangle, ←right_whisker_comp, pentagon_assoc, triangle,
    associator_naturality_left],
end

lemma associator_right_unitor {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
  (α_ f g (𝟙 z)).hom ≫ (f ◀ (ρ_ _).hom) = (ρ_ _).hom :=
begin
  rw [←left_whisker_id_eq_iff, ←cancel_mono (α_ f g (𝟙 _)).hom, ←triangle_assoc,
    ←left_whisker_comp_assoc, associator_naturality_middle, associator_naturality_right, ←triangle,
    ←right_whisker_comp, pentagon_assoc],
end

lemma unitors_equal {x : C} : (λ_ (𝟙 x)).hom = (ρ_ (𝟙 x)).hom :=
begin
  rw [←id_right_whisker_eq_iff, ←cancel_epi (α_ (𝟙 x) (𝟙 _) (𝟙 _)).hom, ←cancel_mono (ρ_ (𝟙 x)).hom,
    triangle, associator_right_unitor, right_unitor_naturality],
end

variables (C D E)

-- https://ncatlab.org/nlab/show/pseudofunctor
structure pseudofunctor :=
(obj : C → D)
(func : Π {x y : C}, functor (x ⟶ y) (obj x ⟶ obj y))
(ids : Π (x : C), func.obj (𝟙 x) ≅ 𝟙 (obj x))
(comps : Π {x y z : C} (f : x ⟶ y) (g : y ⟶ z),
  func.obj (f ≫ g) ≅ func.obj f ≫ func.obj g)
(comps_natural_left' : ∀ {x y z : C} {f f' : x ⟶ y} (g : y ⟶ z) (η : f ⟶ f'),
  (comps f g).hom ≫ (func.map η ▶ _) = func.map (η ▶ _) ≫ (comps f' g).hom . obviously)
(comps_natural_right' : ∀ {x y z : C} (f : x ⟶ y) {g g' : y ⟶ z} (η : g ⟶ g'),
  (comps f g).hom ≫ (_ ◀ func.map η) = func.map (_ ◀ η) ≫ (comps f g').hom . obviously)
(left_unitors' : ∀ {x y : C} (f : x ⟶ y),
  (comps _ _).hom ≫ ((ids _).hom ▶ _) ≫ (λ_ _).hom = func.map (λ_ f).hom . obviously)
(right_unitors' : ∀ {x y : C} (f : x ⟶ y),
  (comps _ _).hom ≫ (_ ◀ (ids _).hom) ≫ (ρ_ _).hom = func.map (ρ_ f).hom . obviously)
(assoc' : ∀ {w x y z : C} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z),
  (comps _ _).hom ≫ ((comps _ _).hom ▶ _) ≫ (α_ (func.obj f) (func.obj g) (func.obj h)).hom =
    func.map (α_ f g h).hom ≫ (comps _ _).hom ≫ (_ ◀ (comps _ _).hom) . obviously)

restate_axiom pseudofunctor.comps_natural_left'
restate_axiom pseudofunctor.comps_natural_right'
restate_axiom pseudofunctor.left_unitors'
restate_axiom pseudofunctor.right_unitors'
restate_axiom pseudofunctor.assoc'

attribute [simp, reassoc]
  pseudofunctor.comps_natural_left
  pseudofunctor.comps_natural_right
  pseudofunctor.left_unitors
  pseudofunctor.right_unitors
  pseudofunctor.assoc

def pseudofunctor.id : pseudofunctor C C :=
{ obj := λ X, X,
  func := λ X Y, 𝟭 _,
  ids := λ X, iso.refl _,
  comps := λ X Y Z f g, iso.refl _ }

variables {C D E}

abbreviation pseudofunctor.hom_functor (P : pseudofunctor C D) {x y : C} :
  (x ⟶ y) ⥤ (P.obj x ⟶ P.obj y) :=
pseudofunctor.func P

abbreviation pseudofunctor.map (P : pseudofunctor C D) {x y : C} (f : x ⟶ y) : P.obj x ⟶ P.obj y :=
P.hom_functor.obj f

abbreviation pseudofunctor.cell (P : pseudofunctor C D) {x y : C} {f f' : x ⟶ y} (θ : f ⟶ f') :
  P.map f ⟶ P.map f' :=
P.hom_functor.map θ

abbreviation pseudofunctor.cell_iso (P : pseudofunctor C D) {x y : C} {f f' : x ⟶ y} (θ : f ≅ f') :
  P.map f ≅ P.map f' :=
P.hom_functor.map_iso θ

@[simp]
lemma pseudofunctor_hom_functor_obj {P : pseudofunctor C D} {x y : C} (f : x ⟶ y) :
  P.hom_functor.obj f = P.map f := rfl

@[simp]
lemma pseudofunctor_hom_functor_map {P : pseudofunctor C D} {x y : C} {f g : x ⟶ y} (η : f ⟶ g) :
  P.hom_functor.map η = P.cell η := rfl

@[simp]
lemma pseudofunctor_hom_functor_map_iso {P : pseudofunctor C D}
  {x y : C} {f g : x ⟶ y} (η : f ≅ g) :
  P.hom_functor.map_iso η = P.cell_iso η :=
rfl

@[reassoc]
lemma pseudofunctor.cell_comp (P : pseudofunctor C D) {x y : C} {f f' f'' : x ⟶ y}
  {θ : f ⟶ f'} {θ' : f' ⟶ f''} :
  P.cell (θ ≫ θ') = P.cell θ ≫ P.cell θ' :=
P.hom_functor.map_comp _ _

lemma comps_natural {P : pseudofunctor C D}
  {x y z : C} {f f' : x ⟶ y} {g g' : y ⟶ z} (η : f ⟶ f') (θ : g ⟶ g') :
   (P.comps f g).hom ≫ (P.cell η ■ P.cell θ) = P.cell (η ■ θ) ≫ (P.comps f' g').hom :=
by rw [hcomp_eq_left_comp_right, P.comps_natural_left_assoc, P.comps_natural_right,
       ←P.cell_comp_assoc, hcomp_eq_left_comp_right]

def pseudofunctor.comp (P : pseudofunctor C D) (Q : pseudofunctor D E) :
  pseudofunctor C E :=
{ obj := λ X, Q.obj (P.obj X),
  func := λ X Y, P.hom_functor ⋙ Q.hom_functor,
  ids := λ X, Q.cell_iso (P.ids _) ≪≫ Q.ids (P.obj X),
  comps := λ X Y Z f g, Q.cell_iso (P.comps _ _) ≪≫ Q.comps _ _,
  comps_natural_left' := λ X Y Z f f' g η,
  begin
    dsimp,
    rw [assoc, Q.comps_natural_left, ←Q.cell_comp_assoc, P.comps_natural_left, Q.cell_comp_assoc],
  end,
  comps_natural_right' := λ X Y Z f g g' η,
  begin
    dsimp,
    rw [assoc, Q.comps_natural_right, ←Q.cell_comp_assoc, P.comps_natural_right, Q.cell_comp_assoc],
  end,
  left_unitors' := λ X Y f,
  begin
    dsimp,
    rw [assoc, ←left_whisker_comp_assoc, Q.comps_natural_left_assoc, ←Q.cell_comp_assoc,
      Q.left_unitors, ←Q.cell_comp, assoc, P.left_unitors],
  end,
  right_unitors' := λ X Y f,
  begin
    dsimp,
    rw [assoc, ←right_whisker_comp_assoc, Q.comps_natural_right_assoc, ←Q.cell_comp_assoc,
        Q.right_unitors, ←Q.cell_comp, assoc, P.right_unitors],
  end,
  assoc' := λ W X Y Z f g h,
  begin
    dsimp,
    rw [assoc, assoc, ←left_whisker_comp_assoc, Q.comps_natural_left_assoc, ←Q.cell_comp_assoc,
      Q.assoc, ←Q.cell_comp_assoc, assoc, P.assoc, Q.cell_comp_assoc, Q.cell_comp_assoc,
      ←right_whisker_comp, Q.comps_natural_right_assoc],
  end }

variables (P Q : pseudofunctor C D)

structure pseudonatural_transformation :=
(obj_app : Π (x : C), P.obj x ⟶ Q.obj x)
(mor_app : Π {x y : C} (f : x ⟶ y),
  P.map f ≫ obj_app y ≅ obj_app x ≫ Q.map f)
(comps' : ∀ {x y z : C} (f : x ⟶ y) (g : y ⟶ z),
  ((P.comps _ _).hom ▶ _) ≫ (α_ _ _ _).hom ≫ (_ ◀ (mor_app _).hom) ≫ (α_ _ _ _).inv ≫
    ((mor_app _).hom ▶ _) ≫ (α_ _ _ _).hom = (mor_app (f ≫ g)).hom ≫ (_ ◀ (Q.comps _ _).hom)
      . obviously)
(ids' : ∀ (x : C),
  (mor_app (𝟙 x)).hom ≫ (_ ◀ (Q.ids _).hom) ≫ (ρ_ _).hom = ((P.ids _).hom ▶ _) ≫ (λ_ _).hom
    . obviously)
(naturality : ∀ {x y : C} {f g : x ⟶ y} (η : f ⟶ g),
  (mor_app f).hom ≫ (_ ◀ Q.cell η) = (P.cell η ▶ _) ≫ (mor_app g).hom
    . obviously)

structure CAT :=
{α : Type u₁}
[str : category.{v₁} α]

instance : has_coe_to_sort CAT :=
{ S := Type u₁,
  coe := CAT.α }

instance str (C : CAT.{v₁ u₁}) : category.{v₁} C := C.str

instance : two_category CAT.{v₁ u₁} :=
{ hom := λ X Y, X ⥤ Y,
  id := λ X, 𝟭 _,
  comp := λ X Y Z f g, f ⋙ g,
  left_unitor := λ X Y, functor.right_unitor,
  right_unitor := λ X Y, functor.left_unitor,
  left_whisker := λ X Y Z f g α h, whisker_right α _,
  right_whisker := λ X Y Z f g h α, whisker_left _ α,
  associator := λ X Y Z W f g h, functor.associator _ _ _ }

end category_theory
