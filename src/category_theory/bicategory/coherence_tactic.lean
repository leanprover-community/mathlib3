import category_theory.monoidal.free.coherence
import category_theory.bicategory.coherence

open category_theory

namespace tactic

namespace monoidal_category
open category_theory.monoidal_category category_theory.free_monoidal_category

meta def to_free_aux₁ : expr → tactic expr
| `(tensor_obj %%X %%Y) := do
    X' ← to_free_aux₁ X,
    Y' ← to_free_aux₁ Y,
    to_expr ``(tensor_obj %%X' %%Y')
| `(@tensor_unit %%C %%cat_inst %%mon_inst) := do
    to_expr ``(tensor_unit (free_monoidal_category %%C))
| f := to_expr ``(free_monoidal_category.of %%f)

meta def to_free_aux₂ : expr → tactic expr
| `(%%η ≫ %%θ) := do
    η' ← to_free_aux₂ η,
    θ' ← to_free_aux₂ θ,
    to_expr ``(%%η' ≫ %%θ')
| `(tensor_hom %%η %%θ) := do η' ← to_free_aux₂ η, θ' ← to_free_aux₂ θ,
    to_expr ``(tensor_hom %%η' %%θ')
| `(iso.hom (α_ %%f %%g %%h)) := do
    f' ← to_free_aux₁ f,
    g' ← to_free_aux₁ g,
    h' ← to_free_aux₁ h,
    to_expr ``(iso.hom (α_ %%f' %%g' %%h'))
| `(iso.inv (α_ %%f %%g %%h)) := do
    f' ← to_free_aux₁ f,
    g' ← to_free_aux₁ g,
    h' ← to_free_aux₁ h,
    to_expr ``(iso.inv (α_ %%f' %%g' %%h'))
| `(iso.hom (λ_ %%f)) := do
    f' ← to_free_aux₁ f,
    to_expr ``(iso.hom (λ_ %%f'))
| `(iso.inv (λ_ %%f)) := do
    f' ← to_free_aux₁ f,
    to_expr ``(iso.inv (λ_ %%f'))
| `(iso.hom (ρ_ %%f)) := do
    f' ← to_free_aux₁ f,
    to_expr ``(iso.hom (ρ_ %%f'))
| `(iso.inv (ρ_ %%f)) := do
    f' ← to_free_aux₁ f,
    to_expr ``(iso.inv (ρ_ %%f'))
| `(𝟙 %%f) := do
    f' ← to_free_aux₁ f,
    to_expr ``(𝟙 %%f')
| _ := fail "expression is not a morphism consisting of associators and unitors."

end monoidal_category

namespace bicategory
open category_theory.bicategory category_theory.free_bicategory
open_locale bicategory

set_option eqn_compiler.max_steps 2500

meta def to_free_aux₁ : expr → tactic expr
| `(%%f ≫ %%g) := do
    f' ← to_free_aux₁ f,
    g' ← to_free_aux₁ g,
    to_expr ``(%%f' ≫ %%g')
| `(𝟙 %%a) := to_expr ``(𝟙 (of.obj %%a))
| f := to_expr ``(of.map %%f)

meta def to_free_aux₂ : expr → tactic expr
| `(%%η ≫ %%θ) := do
    η' ← to_free_aux₂ η,
    θ' ← to_free_aux₂ θ,
    to_expr ``(%%η' ≫ %%θ')
| `(%%f ◁ %%η) := do f' ← to_free_aux₁ f, η' ← to_free_aux₂ η, to_expr ``(%%f' ◁ %%η')
| `(%%η ▷ %%h) := do η' ← to_free_aux₂ η, h' ← to_free_aux₁ h, to_expr ``(%%η' ▷ %%h')
| `(iso.hom (α_ %%f %%g %%h)) := do
    f' ← to_free_aux₁ f,
    g' ← to_free_aux₁ g,
    h' ← to_free_aux₁ h,
    to_expr ``(iso.hom (α_ %%f' %%g' %%h'))
| `(iso.inv (α_ %%f %%g %%h)) := do
    f' ← to_free_aux₁ f,
    g' ← to_free_aux₁ g,
    h' ← to_free_aux₁ h,
    to_expr ``(iso.inv (α_ %%f' %%g' %%h'))
| `(iso.hom (λ_ %%f)) := do
    f' ← to_free_aux₁ f,
    to_expr ``(iso.hom (λ_ %%f'))
| `(iso.inv (λ_ %%f)) := do
    f' ← to_free_aux₁ f,
    to_expr ``(iso.inv (λ_ %%f'))
| `(iso.hom (ρ_ %%f)) := do
    f' ← to_free_aux₁ f,
    to_expr ``(iso.hom (ρ_ %%f'))
| `(iso.inv (ρ_ %%f)) := do
    f' ← to_free_aux₁ f,
    to_expr ``(iso.inv (ρ_ %%f'))
| `(𝟙 %%f) := do
    f' ← to_free_aux₁ f,
    to_expr ``(𝟙 %%f')
| _ := fail "expression is not a 2-morphism consisting of associators and unitors."

end bicategory

namespace interactive
setup_tactic_parser

meta def coherence : tactic unit :=
do
  (lhs, rhs) ← get_goal >>= infer_type >>= match_eq,
  lhs' ← monoidal_category.to_free_aux₂ lhs <|> bicategory.to_free_aux₂ lhs,
  rhs' ← monoidal_category.to_free_aux₂ rhs <|> bicategory.to_free_aux₂ rhs,
  n ← mk_fresh_name,
  «have» n ``(%%lhs' = %%rhs') ``(subsingleton.elim _ _),
  h ← get_local n,
  apply ``(congr_arg (λ η, (free_monoidal_category.project id).map η) %%h) <|>
  apply ``(congr_arg (λ η, (free_bicategory.lift (prefunctor.id _)).map₂ η) %%h)

end interactive

end tactic

section test

universes w v u

section bicategory
open_locale bicategory

variables {B : Type u} [bicategory.{w v} B] {a b c d e : B}

example : (λ_ (𝟙 a)).hom = (ρ_ (𝟙 a)).hom := by coherence

example : (λ_ (𝟙 a)).inv = (ρ_ (𝟙 a)).inv := by coherence

example (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
  (f ◁ (α_ g h i).hom) ≫ (α_ f g (h ≫ i)).inv ≫ (α_ (f ≫ g) h i).inv =
    (α_ f (g ≫ h) i).inv ≫ ((α_ f g h).inv ▷ i) :=
by coherence

example (f : a ⟶ b) (g : b ⟶ c) :
  (f ◁ (λ_ g).inv) ≫ (α_ f (𝟙 b) g).inv = (ρ_ f).inv ▷ g :=
by coherence

end bicategory

section monoidal

variables {C : Type u} [category.{v} C] [monoidal_category C]

example : (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom := by coherence

example : (λ_ (𝟙_ C)).inv = (ρ_ (𝟙_ C)).inv := by coherence

example (X Y Z W : C) :
  (𝟙 X ⊗ (α_ Y Z W).hom) ≫ (α_ X Y (Z ⊗ W)).inv ≫ (α_ (X ⊗ Y) Z W).inv =
    (α_ X (Y ⊗ Z) W).inv ≫ ((α_ X Y Z).inv ⊗ 𝟙 W) :=
by coherence

example (X Y : C) :
  (𝟙 X ⊗ (λ_ Y).inv) ≫ (α_ X (𝟙_ C) Y).inv = (ρ_ X).inv ⊗ 𝟙 Y :=
by coherence

end monoidal

end test
