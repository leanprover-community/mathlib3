import category_theory.bicategory.functor
--import category_theory.path_category

--open paths

namespace category_theory

open bicategory category
open_locale bicategory

universes w w₁ w₂ v v₁ v₂ u u₁ u₂

def free_bicategory (B : Type u) := B

section free

variables {B : Type u}

namespace bicategory

def free.of₀ (a : B) : free_bicategory B := a

variables [quiver.{v+1} B]

namespace free

/--
Generators of 1-morphisms in the free bicategory.
-/
inductive gen₁ : free_bicategory B → free_bicategory B → Type (max u v)
| of {a b : B} (f : a ⟶ b) : gen₁ (of₀ a) (of₀ b)
| id (a : free_bicategory B) : gen₁ a a
| comp {a b c : free_bicategory B} (f : gen₁ a b) (g : gen₁ b c) : gen₁ a c

end free

end bicategory

variables (B) [quiver.{v+1} B]

instance : category_struct (free_bicategory B) :=
{ hom := bicategory.free.gen₁,
  id := bicategory.free.gen₁.id,
  comp := λ a b c, bicategory.free.gen₁.comp }

variables {B} [∀ a b : B, quiver.{w+1} (a ⟶ b)]

namespace bicategory.free

/--
Generators of 2-morphisms in the free bicategory.
-/
inductive gen₂ : Π {a b : free_bicategory B}, (a ⟶ b) → (a ⟶ b) → Type (max u v w)
| of {a b : B} {f g : a ⟶ b} (η : f ⟶ g) : gen₂ (gen₁.of f) (gen₁.of g)
| id {a b : free_bicategory B} (f : a ⟶ b) : gen₂ f f
| vcomp {a b : free_bicategory B} {f g h : a ⟶ b} : gen₂ f g → gen₂ g h → gen₂ f h
| whisker_left {a b c} (f : a ⟶ b) {g h : b ⟶ c} (η : gen₂ g h) : gen₂ (f ≫ g) (f ≫ h)
-- `η` is not earlier than `h` due to the "invalid occurrence of recursive" error
| whisker_right {a b c} {f g : a ⟶ b} (h : b ⟶ c) (η : gen₂ f g) : gen₂ (f ≫ h) (g ≫ h)
| associator {a b c d} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) : gen₂ ((f ≫ g) ≫ h) (f ≫ (g ≫ h))
| associator_inv {a b c d} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) : gen₂ (f ≫ (g ≫ h)) ((f ≫ g) ≫ h)
| right_unitor {a b} (f : a ⟶ b) : gen₂ (f ≫ 𝟙 b) f
| right_unitor_inv {a b} (f : a ⟶ b) : gen₂ f (f ≫ 𝟙 b)
| left_unitor {a b} (f : a ⟶ b) : gen₂ (𝟙 a ≫ f) f
| left_unitor_inv {a b} (f : a ⟶ b) : gen₂ f (𝟙 a ≫ f)

end bicategory.free

def free_bicategory.hom_category_struct (a b : free_bicategory B) :
  category_struct (a ⟶ b) :=
{ hom := bicategory.free.gen₂,
  id := bicategory.free.gen₂.id,
  comp := λ a b c, bicategory.free.gen₂.vcomp }

namespace bicategory.free

local attribute [instance] free_bicategory.hom_category_struct
local notation f ` ◁ `:70 η:70 := gen₂.whisker_left f η
local notation η ` ▷ `:70 h:70 := gen₂.whisker_right h η
local notation `α_` := gen₂.associator
local notation `λ_` := gen₂.left_unitor
local notation `ρ_` := gen₂.right_unitor
local notation `α⁻¹_` := gen₂.associator_inv
local notation `λ⁻¹_` := gen₂.left_unitor_inv
local notation `ρ⁻¹_` := gen₂.right_unitor_inv

/--
Relations between 2-morphisms in the free bicategory.
-/
inductive rel : Π {a b : free_bicategory B} {f g : a ⟶ b}, (f ⟶ g) → (f ⟶ g) → Prop
| vcomp_right {a b} {f g h : a ⟶ b} (η : f ⟶ g) (θ₁ θ₂ : g ⟶ h) :
    rel θ₁ θ₂ → rel (η ≫ θ₁) (η ≫ θ₂)
| vcomp_left {a b} {f g h : a ⟶ b} (η₁ η₂ : f ⟶ g) (θ : g ⟶ h) :
    rel η₁ η₂ → rel (η₁ ≫ θ) (η₂ ≫ θ)
| id_comp {a b} {f g : a ⟶ b} (η : f ⟶ g) :
    rel (𝟙 f ≫ η) η
| comp_id {a b} {f g : a ⟶ b} (η : f ⟶ g) :
    rel (η ≫ 𝟙 g) η
| assoc {a b} {f g h i : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) (ι : h ⟶ i) :
    rel ((η ≫ θ) ≫ ι) (η ≫ (θ ≫ ι))
| whisker_left {a b c} (f : a ⟶ b) (g h : b ⟶ c) (η η' : g ⟶ h) :
    rel η η' → rel (f ◁ η) (f ◁ η')
| whisker_left_id {a b c} (f : a ⟶ b) (g : b ⟶ c) :
    rel (f ◁ 𝟙 g) (𝟙 (f ≫ g))
| whisker_left_comp  {a b c} (f : a ⟶ b) {g h i : b ⟶ c} (η : g ⟶ h) (θ : h ⟶ i) :
    rel (f ◁ (η ≫ θ)) ((f ◁ η) ≫ (f ◁ θ))
| whisker_right {a b c} (f g : a ⟶ b) (h : b ⟶ c) (η η' : f ⟶ g) :
    rel η η' → rel (η ▷ h) (η' ▷ h)
| whisker_right_id {a b c} (f : a ⟶ b) (g : b ⟶ c) :
    rel (𝟙 f ▷ g) (𝟙 (f ≫ g))
| whisker_right_comp {a b c} {f g h : a ⟶ b} (i : b ⟶ c) (η : f ⟶ g) (θ : g ⟶ h) :
    rel ((η ≫ θ) ▷ i) ((η ▷ i) ≫ (θ ▷ i))
| whisker_exchange {a b c} {f g : a ⟶ b} {h i : b ⟶ c} (η : f ⟶ g) (θ : h ⟶ i) :
    rel ((f ◁ θ) ≫ (η ▷ i)) ((η ▷ h) ≫ (g ◁ θ))
| associator_naturality_left {a b c d} {f f' : a ⟶ b} (g : b ⟶ c) (h : c ⟶ d) (η : f ⟶ f') :
    rel (((η ▷ g) ▷ h) ≫ α_ f' g h) (α_ f g h ≫ (η ▷ (g ≫ h)))
| associator_naturality_middle {a b c d} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d) :
    rel ((f ◁ η ▷ h) ≫ α_ f g' h) (α_ f g h ≫ (f ◁ (η ▷ h)))
| associator_naturality_right {a b c d} (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h') :
    rel ((f ≫ g ◁ η) ≫ α_ f g h') (α_ f g h ≫ (f ◁ (g ◁ η)))
| associator_hom_inv {a b c d} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    rel (α_ f g h ≫ α⁻¹_ f g h) (𝟙 ((f ≫ g) ≫ h))
| associator_inv_hom {a b c d} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    rel (α⁻¹_ f g h ≫ α_ f g h) (𝟙 (f ≫ (g ≫ h)))
| left_unitor_hom_inv {a b} (f : a ⟶ b) :
    rel (λ_ f ≫ λ⁻¹_ f) (𝟙 (𝟙 a ≫ f))
| left_unitor_inv_hom {a b} (f : a ⟶ b) :
    rel (λ⁻¹_ f ≫ λ_ f) (𝟙 f)
| left_unitor_naturality {a b} {f f' : a ⟶ b} (η : f ⟶ f') :
    rel ((𝟙 a ◁ η) ≫ λ_ f') (λ_ f ≫ η)
| right_unitor_hom_inv {a b} (f : a ⟶ b) :
    rel (ρ_ f ≫ ρ⁻¹_ f) (𝟙 (f ≫ 𝟙 b))
| right_unitor_inv_hom {a b} (f : a ⟶ b) :
    rel (ρ⁻¹_ f ≫ ρ_ f) (𝟙 f)
| right_unitor_naturality {a b} {f f' : a ⟶ b} (η : f ⟶ f') :
    rel ((η ▷ 𝟙 b) ≫ ρ_ f') (ρ_ f ≫ η)
| pentagon {a b c d e} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
    rel ((α_ f g h ▷ i) ≫ (α_ f (g ≫ h) i ≫ (f ◁ α_ g h i))) (α_ (f ≫ g) h i ≫ α_ f g (h ≫ i))
| triangle {a b c} (f : a ⟶ b) (g : b ⟶ c) :
    rel (α_ f (𝟙 b) g ≫ (f ◁ λ_ g)) (ρ_ f ▷ g)

end bicategory.free

open bicategory.free

instance free_bicategory.bicategory
  (B : Type u) [quiver.{v+1} B] [∀ a b : B, quiver.{w+1} (a ⟶ b)] :
  bicategory (free_bicategory B) :=
{ hom_category := λ a b,
  { hom := λ f g, quot (@rel _ _ _ _ _ f g),
    id := λ f, quot.mk rel (gen₂.id f),
    comp := λ f g h, quot.map₂ gen₂.vcomp rel.vcomp_right rel.vcomp_left,
    id_comp' := by { rintros f g ⟨η⟩, apply quot.sound (rel.id_comp η) },
    comp_id' := by { rintros f g ⟨η⟩, apply quot.sound (rel.comp_id η) },
    assoc' := by { rintros f g h i ⟨η⟩ ⟨θ⟩ ⟨ι⟩, apply quot.sound (rel.assoc η θ ι) } },
  whisker_left := λ a b c f g h η,
    quot.map (gen₂.whisker_left f) (rel.whisker_left f g h) η,
  whisker_left_id' := by
  { intros a b c f g, apply quot.sound (rel.whisker_left_id f g) },
  whisker_left_comp' := by
  { rintros a b c f g h i ⟨η⟩ ⟨θ⟩, apply quot.sound (rel.whisker_left_comp f η θ) },
  whisker_right := λ a b c f g η h,
    quot.map (gen₂.whisker_right h) (rel.whisker_right f g h) η,
  whisker_right_id' := by
  { intros a b c f g, apply quot.sound (rel.whisker_right_id f g) },
  whisker_right_comp' := by
  { rintros a b c f g h ⟨η⟩ ⟨θ⟩ i, apply quot.sound (rel.whisker_right_comp i η θ) },
  whisker_exchange' := by
  { rintros a b c f g h i ⟨η⟩ ⟨θ⟩, apply quot.sound (rel.whisker_exchange η θ) },
  associator := λ a b c d f g h,
  { hom := quot.mk rel (gen₂.associator f g h),
    inv := quot.mk rel (gen₂.associator_inv f g h),
    hom_inv_id' := by apply quot.sound (rel.associator_hom_inv f g h),
    inv_hom_id' := by apply quot.sound (rel.associator_inv_hom f g h) },
  associator_naturality_left' := by
  { rintros a b c d f f' ⟨η⟩ g h, apply quot.sound (rel.associator_naturality_left g h η) },
  associator_naturality_middle' := by
  { rintros a b c d f g g' ⟨η⟩ h, apply quot.sound (rel.associator_naturality_middle f η h) },
  associator_naturality_right' := by
  { rintros a b c d f g h h' ⟨η⟩, apply quot.sound (rel.associator_naturality_right f g η) },
  left_unitor := λ a b f,
  { hom := quot.mk rel (gen₂.left_unitor f),
    inv := quot.mk rel (gen₂.left_unitor_inv f),
    hom_inv_id' := by
    { apply quot.sound (rel.left_unitor_hom_inv f) },
    inv_hom_id' := by
    { apply quot.sound (rel.left_unitor_inv_hom f) } },
  left_unitor_naturality' := by
  { rintros a b f f' ⟨η⟩, apply quot.sound (rel.left_unitor_naturality η) },
  right_unitor := λ a b f,
  { hom := quot.mk rel (gen₂.right_unitor f),
    inv := quot.mk rel (gen₂.right_unitor_inv f),
    hom_inv_id' := by
    { apply quot.sound (rel.right_unitor_hom_inv f) },
    inv_hom_id' := by
    { apply quot.sound (rel.right_unitor_inv_hom f) } },
  right_unitor_naturality' := by
  { rintros a b f f' ⟨η⟩, apply quot.sound (rel.right_unitor_naturality η) },
  pentagon' := by
  { intros a b c d e f g h i, apply quot.sound (rel.pentagon f g h i) },
  triangle' := by
  { intros a b c f g, apply quot.sound (rel.triangle f g) } }

namespace bicategory.free

def of₁ {a b : B} (f : a ⟶ b) : of₀ a ⟶ of₀ b :=
gen₁.of f

def of₂ {a b : B} {f g : a ⟶ b} (η : f ⟶ g) : of₁ f ⟶ of₁ g :=
quot.mk rel (gen₂.of η)

end bicategory.free

end free

section functor

open bicategory.free

variables {B : Type u₁} [quiver.{v₁+1} B] [∀ a b : B, quiver.{w₁+1} (a ⟶ b)]
variables {C : Type u₂} [bicategory.{w₂ v₂} C]
variables (F : prelax_functor B C)

namespace prelax_functor

open bicategory

open_locale bicategory

/-- Auxiliary definition for `bicategory.free.lift`. -/
def free_lift_gen₁ : ∀ {a b : free_bicategory B}, (gen₁ a b) → (F.obj a ⟶ F.obj b)
| _ _ (gen₁.of f)      := F.map f
| _ _ (gen₁.id a)      := 𝟙 (F.obj a)
| _ _ (gen₁.comp f g)  := free_lift_gen₁ f ≫ free_lift_gen₁ g

/-- Auxiliary definition for `bicategory.free.lift`. -/
def free_lift_gen₂ :
  ∀ {a b} {f g : a ⟶ b}, gen₂ f g → (F.free_lift_gen₁ f ⟶ F.free_lift_gen₁ g)
| _ _ _ _ (gen₂.of η)                   := F.map₂ η
| _ _ _ _ (gen₂.id _)                   := 𝟙 _
| _ _ _ _ (gen₂.associator _ _ _)       := (α_ _ _ _).hom
| _ _ _ _ (gen₂.associator_inv _ _ _)   := (α_ _ _ _).inv
| _ _ _ _ (gen₂.left_unitor _)          := (λ_ _).hom
| _ _ _ _ (gen₂.left_unitor_inv _)      := (λ_ _).inv
| _ _ _ _ (gen₂.right_unitor _)         := (ρ_ _).hom
| _ _ _ _ (gen₂.right_unitor_inv _)     := (ρ_ _).inv
| _ _ _ _ (gen₂.vcomp η θ)              := free_lift_gen₂ η ≫ free_lift_gen₂ θ
| _ _ _ _ (gen₂.whisker_left f η)       := F.free_lift_gen₁ f ◁ free_lift_gen₂ η
| _ _ _ _ (gen₂.whisker_right h η)      := free_lift_gen₂ η ▷ F.free_lift_gen₁ h

lemma lift_map₂_aux
  {a b : free_bicategory B}
  {f g : a ⟶ b}
  {η η' : free.gen₂ f g}
  (H : free.rel η η') :
  F.free_lift_gen₂ η = F.free_lift_gen₂ η' :=
begin
  induction H,
  case vcomp_right    { change _ ≫ _ = _ ≫ _, congr' 2 },
  case vcomp_left     { change _ ≫ _ = _ ≫ _, congr' 2 },
  case id_comp        { apply id_comp },
  case comp_id        { apply comp_id },
  case assoc          { apply assoc },
  case whisker_left       { change _ ◁ _ = _ ◁ _, congr' 2 },
  case whisker_left_id    { apply bicategory.whisker_left_id },
  case whisker_left_comp  { apply bicategory.whisker_left_comp },
  case whisker_right      { change _ ▷ _ = _ ▷ _, congr' 2 },
  case whisker_right_id   { apply bicategory.whisker_right_id },
  case whisker_right_comp { apply bicategory.whisker_right_comp },
  case whisker_exchange   { apply bicategory.whisker_exchange },
  case associator_naturality_left { apply associator_naturality_left },
  case associator_naturality_middle { apply associator_naturality_middle },
  case associator_naturality_right { apply associator_naturality_right },
  case associator_hom_inv { apply iso.hom_inv_id },
  case associator_inv_hom { apply iso.inv_hom_id },
  case left_unitor_naturality { apply left_unitor_naturality },
  case left_unitor_hom_inv { apply iso.hom_inv_id },
  case left_unitor_inv_hom { apply iso.inv_hom_id },
  case right_unitor_naturality { apply right_unitor_naturality },
  case right_unitor_hom_inv { apply iso.hom_inv_id },
  case right_unitor_inv_hom { apply iso.inv_hom_id },
  case pentagon { apply pentagon },
  case triangle { apply triangle }
end

@[simps]
def lift : oplax_functor (free_bicategory B) C :=
{ obj := F.obj,
  map := λ a b, F.free_lift_gen₁,
  map₂ := λ a b f g, quot.lift F.free_lift_gen₂ (λ η θ H, F.lift_map₂_aux H),
  map_id := λ a, 𝟙 _,
  map_comp := λ a b c f g, 𝟙 _,
  map_comp_naturality_left' := by
  { rintros a b c f f' ⟨η⟩ g, dsimp only, simp only [id_comp, comp_id], refl },
  map_comp_naturality_right' := by
  { rintros a b c f g g' ⟨η⟩, dsimp only, simp only [id_comp, comp_id], refl },
  map₂_id' := by { intros, refl },
  map₂_comp' := by { rintros a b f g h ⟨η⟩ ⟨θ⟩, refl },
  map₂_associator' := by
  { intros, dsimp,
    simp only [bicategory.whisker_right_id, id_comp, free_lift_gen₂, bicategory.whisker_left_id, comp_id],
    refl },
  map₂_left_unitor' := by
  { intros, dsimp only, simp only [bicategory.whisker_right_id, id_comp], refl },
  map₂_right_unitor' := by
  { intros, dsimp only, simp only [bicategory.whisker_left_id, id_comp], refl } }

end prelax_functor

end functor

end category_theory
