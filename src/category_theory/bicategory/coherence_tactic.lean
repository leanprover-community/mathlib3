import category_theory.bicategory.coherence

open category_theory category_theory.bicategory category_theory.free_bicategory
open_locale bicategory

namespace tactic

set_option eqn_compiler.max_steps 5000

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

namespace interactive
setup_tactic_parser

meta def coherence : tactic unit :=
do
  g ← get_goal,
  t ← infer_type g,
  (lhs, rhs) ← match_eq t,
  `(%%f ⟶ %%g) ← infer_type lhs,
  `(%%a ⟶ %%b) ← infer_type f,
  B ← infer_type a,
  lhs' ← to_free_aux₂ lhs,
  rhs' ← to_free_aux₂ rhs,
  n ← mk_fresh_name,
  «have» n ``(%%lhs' = %%rhs') ``(subsingleton.elim _ _),
  h ← get_local n,
  apply ``(congr_arg (λ η, (free_bicategory.lift (prefunctor.id %%B)).map₂ η) %%h)

end interactive

section test

universes w v u

variables {B : Type u} [bicategory.{w v} B] {a : B}

example : (λ_ (𝟙 a)).inv = (ρ_ (𝟙 a)).inv := by coherence

end test

end tactic
