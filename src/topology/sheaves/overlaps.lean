import topology.sheaves.sheaf

universes v u

open topological_space
open Top
open opposite
open category_theory
open category_theory.limits

inductive overlap (ι : Type v)
| single : ι → overlap
| pair : ι → ι → overlap

namespace overlap

variables {ι : Type v}

inductive hom : overlap ι → overlap ι → Type v
| id_single : Π i, hom (single i) (single i)
| id_pair : Π i j, hom (pair i j) (pair i j)
| left : Π i j, hom (single i) (pair i j)
| right : Π i j, hom (single j) (pair i j)

open hom

def id : Π (o : overlap ι), hom o o
| (single i) := id_single i
| (pair i j) := id_pair i j

def comp : Π {o₁ o₂ o₃ : overlap ι} (f : hom o₁ o₂) (g : hom o₂ o₃), hom o₁ o₃
| _ _ _ (id_single i) g := g
| _ _ _ (id_pair i j) g := g
| _ _ _ (left i j) (id_pair _ _) := left i j
| _ _ _ (right i j) (id_pair _ _) := right i j

local attribute [tidy] tactic.case_bash

instance : category (overlap ι) :=
{ hom := hom,
  id := id,
  comp := λ X Y Z f g, comp f g, }

variables {X : Top.{v}}
variables (U : ι → opens X)

def diagram_obj : overlap ι → (opens X)ᵒᵖ
| (single i) := op (U i)
| (pair i j) := op (U i ⊓ U j)

def diagram_map : Π {o₁ o₂ : overlap ι} (f : o₁ ⟶ o₂), diagram_obj U o₁ ⟶ diagram_obj U o₂
| _ _ (id_single i) := 𝟙 _
| _ _ (id_pair i j) := 𝟙 _
| _ _ (left i j) := (opens.inf_le_left _ _).op
| _ _ (right i j) := (opens.inf_le_right _ _).op

def diagram : overlap ι ⥤ (opens X)ᵒᵖ :=
{ obj := diagram_obj U,
  map := λ X Y f, diagram_map U f, }

def cone_π_app : Π (o : overlap ι), op (supr U) ⟶ diagram_obj U o
| (single i) := (opens.le_supr _ _).op
| (pair i j) := (opens.inf_le_left _ _ ≫ opens.le_supr _ _).op

def cone : cone (diagram U) :=
{ X := op (supr U),
  π := { app := cone_π_app U, } }

-- TODO observe this is a limit cone?

variables {C : Type u} [category.{v} C] [has_products C]

@[derive subsingleton]
def sheaf_condition (F : presheaf C X) : Type (max u (v+1)) :=
Π ⦃ι : Type v⦄ (U : ι → opens X), is_limit (F.map_cone (cone U))

def sheaf_condition_equiv (F : presheaf C X) :
  F.sheaf_condition ≃ overlap.sheaf_condition F := sorry

end overlap
