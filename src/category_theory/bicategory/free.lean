/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import category_theory.bicategory.functor

/-!
# Free bicategories

We define the free bicategory over a quiver. In this bicategory, the 1-morphisms are freely
generated by the arrows in the quiver, and the 2-morphisms are freely generated by the formal
identities, the formal unitors, and the formal associators modulo the relation derived from the
axioms of a bicategory.

## Main definitions

* `free_bicategory B`: the free bicategory over a quiver `B`.
* `free_bicategory.lift F`: the pseudofunctor from `free_bicategory B` to `C` associated with a
  prefunctor `F` from `B` to `C`.
-/

universes w w₁ w₂ v v₁ v₂ u u₁ u₂

namespace category_theory
open category bicategory
open_locale bicategory

/-- Free bicategory over a quiver. Its objects are the same as those in the underlying quiver. -/
def free_bicategory (B : Type u) := B

instance (B : Type u) : Π [inhabited B], inhabited (free_bicategory B) := id

namespace free_bicategory

section
variables {B : Type u} [quiver.{v+1} B]

/-- 1-morphisms in the free bicategory. -/
inductive hom : B → B → Type (max u v)
| of {a b : B} (f : a ⟶ b) : hom a b
| id (a : B) : hom a a
| comp {a b c : B} (f : hom a b) (g : hom b c) : hom a c

instance (a b : B) [inhabited (a ⟶ b)] : inhabited (hom a b) := ⟨hom.of default⟩

/-- Representatives of 2-morphisms in the free bicategory. -/
@[nolint has_nonempty_instance]
inductive hom₂ : Π {a b : B}, hom a b → hom a b → Type (max u v)
| id {a b} (f : hom a b) : hom₂ f f
| vcomp {a b} {f g h : hom a b} (η : hom₂ f g) (θ : hom₂ g h) : hom₂ f h
| whisker_left {a b c} (f : hom a b) {g h : hom b c} (η : hom₂ g h) : hom₂ (f.comp g) (f.comp h)
-- `η` cannot be earlier than `h` since it is a recursive argument.
| whisker_right {a b c} {f g : hom a b} (h : hom b c) (η : hom₂ f g) : hom₂ (f.comp h) (g.comp h)
| associator {a b c d} (f : hom a b) (g : hom b c) (h : hom c d) :
    hom₂ ((f.comp g).comp h) (f.comp (g.comp h))
| associator_inv {a b c d} (f : hom a b) (g : hom b c) (h : hom c d) :
    hom₂ (f.comp (g.comp h)) ((f.comp g).comp h)
| right_unitor     {a b} (f : hom a b) : hom₂ (f.comp (hom.id b)) f
| right_unitor_inv {a b} (f : hom a b) : hom₂ f (f.comp (hom.id b))
| left_unitor      {a b} (f : hom a b) : hom₂ ((hom.id a).comp f) f
| left_unitor_inv  {a b} (f : hom a b) : hom₂ f ((hom.id a).comp f)

section
variables {B}

-- The following notations are only used in the definition of `rel` to simplify the notation.
local infixr ` ≫ ` := hom₂.vcomp
local notation `𝟙` := hom₂.id
local notation f ` ◁ ` η := hom₂.whisker_left f η
local notation η ` ▷ ` h := hom₂.whisker_right h η
local notation `α_` := hom₂.associator
local notation `λ_` := hom₂.left_unitor
local notation `ρ_` := hom₂.right_unitor
local notation `α⁻¹_` := hom₂.associator_inv
local notation `λ⁻¹_` := hom₂.left_unitor_inv
local notation `ρ⁻¹_` := hom₂.right_unitor_inv

/-- Relations between 2-morphisms in the free bicategory. -/
inductive rel : Π {a b : B} {f g : hom a b}, hom₂ f g → hom₂ f g → Prop
| vcomp_right {a b} {f g h : hom a b} (η : hom₂ f g) (θ₁ θ₂ : hom₂ g h) :
    rel θ₁ θ₂ → rel (η ≫ θ₁) (η ≫ θ₂)
| vcomp_left {a b} {f g h : hom a b} (η₁ η₂ : hom₂ f g) (θ : hom₂ g h) :
    rel η₁ η₂ → rel (η₁ ≫ θ) (η₂ ≫ θ)
| id_comp {a b} {f g : hom a b} (η : hom₂ f g) :
    rel (𝟙 f ≫ η) η
| comp_id {a b} {f g : hom a b} (η : hom₂ f g) :
    rel (η ≫ 𝟙 g) η
| assoc {a b} {f g h i : hom a b} (η : hom₂ f g) (θ : hom₂ g h) (ι : hom₂ h i) :
    rel ((η ≫ θ) ≫ ι) (η ≫ (θ ≫ ι))
| whisker_left {a b c} (f : hom a b) (g h : hom b c) (η η' : hom₂ g h) :
    rel η η' → rel (f ◁ η) (f ◁ η')
| whisker_left_id {a b c} (f : hom a b) (g : hom b c) :
    rel (f ◁ 𝟙 g) (𝟙 (f.comp g))
| whisker_left_comp {a b c} (f : hom a b) {g h i : hom b c} (η : hom₂ g h) (θ : hom₂ h i) :
    rel (f ◁ (η ≫ θ)) (f ◁ η ≫ f ◁ θ)
| id_whisker_left {a b} {f g : hom a b} (η : hom₂ f g) :
    rel (hom.id a ◁ η) (λ_ f ≫ η ≫ λ⁻¹_ g)
| comp_whisker_left
    {a b c d} (f : hom a b) (g : hom b c) {h h' : hom c d} (η : hom₂ h h') :
    rel ((f.comp g) ◁ η) (α_ f g h ≫ f ◁ g ◁ η ≫ α⁻¹_ f g h')
| whisker_right {a b c} (f g : hom a b) (h : hom b c) (η η' : hom₂ f g) :
    rel η η' → rel (η ▷ h) (η' ▷ h)
| id_whisker_right {a b c} (f : hom a b) (g : hom b c) :
    rel (𝟙 f ▷ g) (𝟙 (f.comp g))
| comp_whisker_right {a b c} {f g h : hom a b} (i : hom b c) (η : hom₂ f g) (θ : hom₂ g h) :
    rel ((η ≫ θ) ▷ i) (η ▷ i ≫ θ ▷ i)
| whisker_right_id {a b} {f g : hom a b} (η : hom₂ f g) :
    rel (η ▷ hom.id b) (ρ_ f ≫ η ≫ ρ⁻¹_ g)
| whisker_right_comp
    {a b c d} {f f' : hom a b} (g : hom b c) (h : hom c d) (η : hom₂ f f') :
    rel (η ▷ (g.comp h)) (α⁻¹_ f g h ≫ η ▷ g ▷ h ≫ α_ f' g h)
| whisker_assoc
    {a b c d} (f : hom a b) {g g' : hom b c} (η : hom₂ g g') (h : hom c d) :
    rel ((f ◁ η) ▷ h) (α_ f g h ≫ f ◁ (η ▷ h)≫ α⁻¹_ f g' h)
| whisker_exchange {a b c} {f g : hom a b} {h i : hom b c} (η : hom₂ f g) (θ : hom₂ h i) :
    rel (f ◁ θ ≫ η ▷ i) (η ▷ h ≫ g ◁ θ)
| associator_hom_inv {a b c d} (f : hom a b) (g : hom b c) (h : hom c d) :
    rel (α_ f g h ≫ α⁻¹_ f g h) (𝟙 ((f.comp g).comp h))
| associator_inv_hom {a b c d} (f : hom a b) (g : hom b c) (h : hom c d) :
    rel (α⁻¹_ f g h ≫ α_ f g h) (𝟙 (f.comp (g.comp h)))
| left_unitor_hom_inv {a b} (f : hom a b) :
    rel (λ_ f ≫ λ⁻¹_ f) (𝟙 ((hom.id a).comp f))
| left_unitor_inv_hom {a b} (f : hom a b) :
    rel (λ⁻¹_ f ≫ λ_ f) (𝟙 f)
| right_unitor_hom_inv {a b} (f : hom a b) :
    rel (ρ_ f ≫ ρ⁻¹_ f) (𝟙 (f.comp (hom.id b)))
| right_unitor_inv_hom {a b} (f : hom a b) :
    rel (ρ⁻¹_ f ≫ ρ_ f) (𝟙 f)
| pentagon {a b c d e} (f : hom a b) (g : hom b c) (h : hom c d) (i : hom d e) :
    rel (α_ f g h ▷ i ≫ α_ f (g.comp h) i ≫ f ◁ α_ g h i)
        (α_ (f.comp g) h i ≫ α_ f g (h.comp i))
| triangle {a b c} (f : hom a b) (g : hom b c) :
    rel (α_ f (hom.id b) g ≫ f ◁ λ_ g) (ρ_ f ▷ g)

end

variables {B}

instance hom_category (a b : B) : category (hom a b) :=
{ hom       := λ f g, quot (@rel _ _ _ _ f g),
  id        := λ f, quot.mk rel (hom₂.id f),
  comp      := λ f g h, quot.map₂ hom₂.vcomp rel.vcomp_right rel.vcomp_left,
  id_comp'  := by { rintros f g ⟨η⟩, exact quot.sound (rel.id_comp η) },
  comp_id'  := by { rintros f g ⟨η⟩, exact quot.sound (rel.comp_id η) },
  assoc'    := by { rintros f g h i ⟨η⟩ ⟨θ⟩ ⟨ι⟩, exact quot.sound (rel.assoc η θ ι) } }

/-- Bicategory structure on the free bicategory. -/
instance bicategory : bicategory (free_bicategory B) :=
{ hom   := λ a b : B, hom a b,
  id    := hom.id,
  comp  := λ a b c, hom.comp,
  hom_category := free_bicategory.hom_category,
  whisker_left := λ a b c f g h η,
    quot.map (hom₂.whisker_left f) (rel.whisker_left f g h) η,
  whisker_left_id' := λ a b c f g, quot.sound (rel.whisker_left_id f g),
  whisker_left_comp' := by
  { rintros a b c f g h i ⟨η⟩ ⟨θ⟩, exact quot.sound (rel.whisker_left_comp f η θ) },
  id_whisker_left' := by
  { rintros a b f g ⟨η⟩, exact quot.sound (rel.id_whisker_left η) },
  comp_whisker_left' := by
  { rintros a b c d f g h h' ⟨η⟩, exact quot.sound (rel.comp_whisker_left f g η) },
  whisker_right := λ a b c f g η h,
    quot.map (hom₂.whisker_right h) (rel.whisker_right f g h) η,
  id_whisker_right' := λ a b c f g, quot.sound (rel.id_whisker_right f g),
  comp_whisker_right' := by
  { rintros a b c f g h ⟨η⟩ ⟨θ⟩ i, exact quot.sound (rel.comp_whisker_right i η θ) },
  whisker_right_id' := by
  { rintros a b f g ⟨η⟩, exact quot.sound (rel.whisker_right_id η) },
  whisker_right_comp' := by
  { rintros a b c d f f' ⟨η⟩ g h, exact quot.sound (rel.whisker_right_comp g h η) },
  whisker_assoc' := by
  { rintros a b c d f g g' ⟨η⟩ h, exact quot.sound (rel.whisker_assoc f η h) },
  whisker_exchange' := by
  { rintros a b c f g h i ⟨η⟩ ⟨θ⟩, exact quot.sound (rel.whisker_exchange η θ) },
  associator := λ a b c d f g h,
  { hom := quot.mk rel (hom₂.associator f g h),
    inv := quot.mk rel (hom₂.associator_inv f g h),
    hom_inv_id' := quot.sound (rel.associator_hom_inv f g h),
    inv_hom_id' := quot.sound (rel.associator_inv_hom f g h) },
  left_unitor := λ a b f,
  { hom := quot.mk rel (hom₂.left_unitor f),
    inv := quot.mk rel (hom₂.left_unitor_inv f),
    hom_inv_id' := quot.sound (rel.left_unitor_hom_inv f),
    inv_hom_id' := quot.sound (rel.left_unitor_inv_hom f) },
  right_unitor := λ a b f,
  { hom := quot.mk rel (hom₂.right_unitor f),
    inv := quot.mk rel (hom₂.right_unitor_inv f),
    hom_inv_id' := quot.sound (rel.right_unitor_hom_inv f),
    inv_hom_id' := quot.sound (rel.right_unitor_inv_hom f) },
  pentagon' := λ a b c d e f g h i, quot.sound (rel.pentagon f g h i),
  triangle' := λ a b c f g, quot.sound (rel.triangle f g) }

variables {a b c d : free_bicategory B}

@[simp] lemma mk_vcomp {f g h : a ⟶ b} (η : hom₂ f g) (θ : hom₂ g h) :
  quot.mk rel (η.vcomp θ) = (quot.mk rel η ≫ quot.mk rel θ : f ⟶ h) := rfl
@[simp] lemma mk_whisker_left (f : a ⟶ b) {g h : b ⟶ c} (η : hom₂ g h) :
  quot.mk rel (hom₂.whisker_left f η) = (f ◁ quot.mk rel η : f ≫ g ⟶ f ≫ h) := rfl
@[simp] lemma mk_whisker_right {f g : a ⟶ b} (η : hom₂ f g) (h : b ⟶ c) :
  quot.mk rel (hom₂.whisker_right h η) = (quot.mk rel η ▷ h : f ≫ h ⟶ g ≫ h) := rfl

variables (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)

lemma id_def : hom.id a = 𝟙 a := rfl
lemma comp_def : hom.comp f g = f ≫ g := rfl
@[simp] lemma mk_id : quot.mk _ (hom₂.id f) = 𝟙 f := rfl
@[simp] lemma mk_associator_hom : quot.mk _ (hom₂.associator f g h) = (α_ f g h).hom := rfl
@[simp] lemma mk_associator_inv : quot.mk _ (hom₂.associator_inv f g h) = (α_ f g h).inv := rfl
@[simp] lemma mk_left_unitor_hom : quot.mk _ (hom₂.left_unitor f) = (λ_ f).hom := rfl
@[simp] lemma mk_left_unitor_inv : quot.mk _ (hom₂.left_unitor_inv f) = (λ_ f).inv := rfl
@[simp] lemma mk_right_unitor_hom : quot.mk _ (hom₂.right_unitor f) = (ρ_ f).hom := rfl
@[simp] lemma mk_right_unitor_inv : quot.mk _ (hom₂.right_unitor_inv f) = (ρ_ f).inv := rfl

/-- Canonical prefunctor from `B` to `free_bicategory B`. -/
@[simps]
def of : prefunctor B (free_bicategory B) :=
{ obj := id,
  map := λ a b, hom.of }

end

section
variables {B : Type u₁} [quiver.{v₁+1} B] {C : Type u₂} [category_struct.{v₂} C]
variables (F : prefunctor B C)

/-- Auxiliary definition for `lift`. -/
@[simp]
def lift_hom : ∀ {a b : B}, hom a b → (F.obj a ⟶ F.obj b)
| _ _ (hom.of f)      := F.map f
| _ _ (hom.id a)      := 𝟙 (F.obj a)
| _ _ (hom.comp f g)  := lift_hom f ≫ lift_hom g

@[simp] lemma lift_hom_id (a : free_bicategory B) : lift_hom F (𝟙 a) = 𝟙 (F.obj a) := rfl
@[simp] lemma lift_hom_comp {a b c : free_bicategory B} (f : a ⟶ b) (g : b ⟶ c) :
  lift_hom F (f ≫ g) = lift_hom F f ≫ lift_hom F g := rfl

end

section
variables {B : Type u₁} [quiver.{v₁+1} B] {C : Type u₂} [bicategory.{w₂ v₂} C]
variables (F : prefunctor B C)

/-- Auxiliary definition for `lift`. -/
@[simp]
def lift_hom₂ : ∀ {a b : B} {f g : hom a b}, hom₂ f g → (lift_hom F f ⟶ lift_hom F g)
| _ _ _ _ (hom₂.id _)                   := 𝟙 _
| _ _ _ _ (hom₂.associator _ _ _)       := (α_ _ _ _).hom
| _ _ _ _ (hom₂.associator_inv _ _ _)   := (α_ _ _ _).inv
| _ _ _ _ (hom₂.left_unitor _)          := (λ_ _).hom
| _ _ _ _ (hom₂.left_unitor_inv _)      := (λ_ _).inv
| _ _ _ _ (hom₂.right_unitor _)         := (ρ_ _).hom
| _ _ _ _ (hom₂.right_unitor_inv _)     := (ρ_ _).inv
| _ _ _ _ (hom₂.vcomp η θ)              := lift_hom₂ η ≫ lift_hom₂ θ
| _ _ _ _ (hom₂.whisker_left f η)       := lift_hom F f ◁ lift_hom₂ η
| _ _ _ _ (hom₂.whisker_right h η)      := lift_hom₂ η ▷ lift_hom F h

local attribute [simv] whisker_exchange

lemma lift_hom₂_congr {a b : B} {f g : hom a b} {η θ : hom₂ f g} (H : rel η θ) :
  lift_hom₂ F η = lift_hom₂ F θ :=
by induction H; tidy

/--
A prefunctor from a quiver `B` to a bicategory `C` can be lifted to a pseudofunctor from
`free_bicategory B` to `C`.
-/
@[simps]
def lift : pseudofunctor (free_bicategory B) C :=
{ obj       := F.obj,
  map       := λ a b, lift_hom F,
  map₂      := λ a b f g, quot.lift (lift_hom₂ F) (λ η θ H, lift_hom₂_congr F H),
  map_id    := λ a, iso.refl _,
  map_comp  := λ a b c f g, iso.refl _ }

end

end free_bicategory

end category_theory
