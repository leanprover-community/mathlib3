import category_theory.functor
import category_theory.category

universes v u

namespace category_theory

structure prefunctor (C : Type*) [has_hom C] (D : Type*) [has_hom D] := 
(obj : C → D)
(map {X Y : C} : (X ⟶ Y) → (obj X ⟶ obj Y))

def free (C : Type*) [has_hom C] := C 
namespace free

inductive pre {C : Type u} [has_hom.{v} C] : free C → free C → Type (max u v)
| of {X Y : C} : (X ⟶ Y) → pre X Y
| id {X : C} : pre X X
| comp {X Y Z : C} : pre X Y → pre Y Z → pre X Z

inductive rel {C : Type u} [has_hom.{v} C] : Π {X Y : free C}, pre X Y → pre X Y → Prop
| id_comp {X Y : C} (f : pre X Y) : rel (pre.comp pre.id f) f
| comp_id {X Y : C} (f : pre X Y) : rel (pre.comp f pre.id) f
| comp_assoc {X Y Z W : C} (f : pre X Y) (g : pre Y Z) (h : pre Z W) :
    rel (pre.comp (pre.comp f g) h) (pre.comp f (pre.comp g h))
| comp_left {X Y Z : C} {f g : pre X Y} {h : pre Y Z} : rel f g → rel (pre.comp f h) (pre.comp g h)
| comp_right {X Y Z : C} {f : pre X Y} {g h : pre Y Z} : rel g h → rel (pre.comp f g) (pre.comp f h)

def hom {C : Type*} [has_hom C] (X Y : free C) := quot (@rel _ _ X Y)

instance {C : Type*} [has_hom C] : category (free C) := 
{ hom := hom,
  id := λ X, quot.mk _ pre.id,
  comp := λ X Y Z f g, quot.lift_on₂ f g (λ F G, quot.mk rel $ pre.comp F G) 
    (λ _ _ _ h, quot.sound (rel.comp_right h))
    (λ _ _ _ h, quot.sound (rel.comp_left h)),
  id_comp' := by {rintro _ _ ⟨⟩, exact quot.sound (rel.id_comp _)},
  comp_id' := by {rintro _ _ ⟨⟩, exact quot.sound (rel.comp_id _)},
  assoc' := by {rintro _ _ _ _ ⟨⟩ ⟨⟩ ⟨⟩, exact quot.sound (rel.comp_assoc _ _ _)} }
  
def ι (C : Type*) [has_hom C] : prefunctor C (free C) := 
{ obj := λ X, X,
  map := λ X Y f, quot.mk _ $ pre.of f }
  
@[simp]
def pre_lift_map {C : Type*} [has_hom C] {X Y : C} {D : Type*} [category D] (F : prefunctor C D) 
  (f : pre X Y) : (F.obj X ⟶ F.obj Y) := 
  pre.rec_on f (λ _ _ g, F.map g) (λ _, 𝟙 _) (λ _ _ _ _ _ a b, a ≫ b)
local attribute [reducible] pre_lift_map
  
@[simps]
def lift {C : Type*} [has_hom C] {D : Type*} [category D] (F : prefunctor C D) : functor (free C) D := 
{ obj := λ X, F.obj X,
  map := λ X Y, quot.lift (pre_lift_map _) begin -- lift_on does not work?!? 
    intros a b h, 
    induction h,
    tidy 
  end,
  map_id' := by tauto,
  map_comp' := by {rintro _ _ _ ⟨⟩ ⟨⟩, refl} }

end free

end category_theory
