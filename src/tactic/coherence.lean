/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import category_theory.monoidal.free.coherence
import category_theory.bicategory.coherence

/-!
# Coherence tactic for monoidal categories and bicategories

The coherence theorem for monoidal categories (resp. bicategories) asserts that every diagram in
a monoidal category (resp. bicategory) made up of associators and unitors commutes. This file
gives a tactic counterpart of this theorem.
-/

open category_theory

namespace tactic

namespace monoidal_category
open category_theory.monoidal_category category_theory.free_monoidal_category

/-- Embedding of objects in a monoidal category into the free monoidal category. -/
meta def free₁ : expr → tactic expr
| `(tensor_obj %%X %%Y) := do X' ← free₁ X, Y' ← free₁ Y, to_expr ``(tensor_obj %%X' %%Y')
| `(@tensor_unit %%C %%_ %%_) := do to_expr ``(tensor_unit (free_monoidal_category %%C))
| f := to_expr ``(of %%f)

/-- Embedding of morphism in a monoidal category into the free monoidal category. -/
meta def free₂ : expr → tactic expr
| `(%%η ≫ %%θ) := do η' ← free₂ η, θ' ← free₂ θ, to_expr ``(%%η' ≫ %%θ')
| `(tensor_hom %%η %%θ) := do η' ← free₂ η, θ' ← free₂ θ, to_expr ``(tensor_hom %%η' %%θ')
| `(iso.hom (α_ %%f %%g %%h)) := do
    f' ← free₁ f, g' ← free₁ g, h' ← free₁ h,
    to_expr ``(iso.hom (α_ %%f' %%g' %%h'))
| `(iso.inv (α_ %%f %%g %%h)) := do
    f' ← free₁ f, g' ← free₁ g, h' ← free₁ h,
    to_expr ``(iso.inv (α_ %%f' %%g' %%h'))
| `(iso.hom (λ_ %%f)) := do f' ← free₁ f, to_expr ``(iso.hom (λ_ %%f'))
| `(iso.inv (λ_ %%f)) := do f' ← free₁ f, to_expr ``(iso.inv (λ_ %%f'))
| `(iso.hom (ρ_ %%f)) := do f' ← free₁ f, to_expr ``(iso.hom (ρ_ %%f'))
| `(iso.inv (ρ_ %%f)) := do f' ← free₁ f, to_expr ``(iso.inv (ρ_ %%f'))
| `(𝟙 %%f)           := do f' ← free₁ f, to_expr ``(𝟙 %%f')
| _ := fail "expression is not a morphism made up only of associators and unitors."

end monoidal_category

namespace bicategory
open category_theory.bicategory category_theory.free_bicategory
open_locale bicategory

set_option eqn_compiler.max_steps 2500

/-- Embedding of 1-morphisms in a bicategory into the free bicategory. -/
meta def free₁ : expr → tactic expr
| `(%%f ≫ %%g) := do f' ← free₁ f, g' ← free₁ g, to_expr ``(%%f' ≫ %%g')
| `(𝟙 %%a) := to_expr ``(𝟙 (of.obj %%a))
| f := to_expr ``(of.map %%f)

/-- Embedding of 2-morphisms in a bicategory into the free bicategory. -/
meta def free₂ : expr → tactic expr
| `(%%η ≫ %%θ) := do η' ← free₂ η, θ' ← free₂ θ, to_expr ``(%%η' ≫ %%θ')
| `(%%f ◁ %%η)  := do f' ← free₁ f, η' ← free₂ η, to_expr ``(%%f' ◁ %%η')
| `(%%η ▷ %%h)  := do η' ← free₂ η, h' ← free₁ h, to_expr ``(%%η' ▷ %%h')
| `(iso.hom (α_ %%f %%g %%h)) := do
    f' ← free₁ f, g' ← free₁ g, h' ← free₁ h,
    to_expr ``(iso.hom (α_ %%f' %%g' %%h'))
| `(iso.inv (α_ %%f %%g %%h)) := do
    f' ← free₁ f, g' ← free₁ g, h' ← free₁ h,
    to_expr ``(iso.inv (α_ %%f' %%g' %%h'))
| `(iso.hom (λ_ %%f)) := do f' ← free₁ f, to_expr ``(iso.hom (λ_ %%f'))
| `(iso.inv (λ_ %%f)) := do f' ← free₁ f, to_expr ``(iso.inv (λ_ %%f'))
| `(iso.hom (ρ_ %%f)) := do f' ← free₁ f, to_expr ``(iso.hom (ρ_ %%f'))
| `(iso.inv (ρ_ %%f)) := do f' ← free₁ f, to_expr ``(iso.inv (ρ_ %%f'))
| `(𝟙 %%f)           := do f' ← free₁ f, to_expr ``(𝟙 %%f')
| _ := fail "expression is not a 2-morphism made up only of associators and unitors."

end bicategory

namespace interactive
setup_tactic_parser

meta def bicategory.coherence : tactic unit :=
do
  (lhs, rhs) ← get_goal >>= infer_type >>= match_eq,
  lhs' ← bicategory.free₂ lhs,
  rhs' ← bicategory.free₂ rhs,
  n ← get_unused_name,
  «have» n ``(%%lhs' = %%rhs') ``(subsingleton.elim _ _),
  h ← get_local n,
  apply ``(congr_arg (λ η, (free_bicategory.lift (prefunctor.id _)).map₂ η) %%h)

meta def monoical_category.coherence : tactic unit :=
do
  (lhs, rhs) ← get_goal >>= infer_type >>= match_eq,
  lhs' ← monoidal_category.free₂ lhs,
  rhs' ← monoidal_category.free₂ rhs,
  n ← get_unused_name,
  «have» n ``(%%lhs' = %%rhs') ``(subsingleton.elim _ _),
  h ← get_local n,
  apply ``(congr_arg (λ η, (free_monoidal_category.project id).map η) %%h)

/--
`coherence` uses the coherence theorem for monoidal categories or bicategories to prove the goal.
It can prove any equality made up only of associators and unitors.

```lean
example {C : Type} [category C] [monoidal_category C] :
  (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom :=
by coherence
```
-/
meta def coherence : tactic unit :=
do monoical_category.coherence <|> bicategory.coherence

add_tactic_doc
{ name        := "coherence",
  category    := doc_category.tactic,
  decl_names  := [`tactic.interactive.coherence],
  tags        := ["category theory"] }

end interactive

end tactic
