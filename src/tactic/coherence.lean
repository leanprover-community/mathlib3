/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
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

/--
`coherence` uses coherence theorem for monoidal categories or bicategories to prove the goal. It
can prove any equality made up only of associators and unitors.
-/
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

add_tactic_doc
{ name        := "coherence",
  category    := doc_category.tactic,
  decl_names  := [`tactic.interactive.coherence],
  tags        := ["category theory"] }

end interactive

end tactic
