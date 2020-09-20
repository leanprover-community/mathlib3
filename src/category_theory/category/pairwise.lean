import topology.sheaves.sheaf
import category_theory.limits.preserves.basic

/-!
# The category of "pairwise intersections".

Given `ι : Type v`, we build the diagram category `pairwise ι`
with objects `single i` and `pair i j`, for `i j : ι`,
whose only non-identity morphisms are
`left : single i ⟶ pair i j` and `right : single j ⟶ pair i j`.

We use this later in describing the sheaf condition.

Given any function `U : ι → α`, where `α` is some complete lattice (e.g. `opens X`),
we produce a functor `pairwise ι ⥤ αᵒᵖ` in the obvious way,
and show that `supr U` provides a limit cone over this functor.
-/

noncomputable theory

universes v u

open topological_space
open Top
open opposite
open category_theory
open category_theory.limits

namespace category_theory

inductive pairwise (ι : Type v)
| single : ι → pairwise
| pair : ι → ι → pairwise

variables {ι : Type v}

namespace pairwise

inductive hom : pairwise ι → pairwise ι → Type v
| id_single : Π i, hom (single i) (single i)
| id_pair : Π i j, hom (pair i j) (pair i j)
| left : Π i j, hom (single i) (pair i j)
| right : Π i j, hom (single j) (pair i j)

open hom

def id : Π (o : pairwise ι), hom o o
| (single i) := id_single i
| (pair i j) := id_pair i j

def comp : Π {o₁ o₂ o₃ : pairwise ι} (f : hom o₁ o₂) (g : hom o₂ o₃), hom o₁ o₃
| _ _ _ (id_single i) g := g
| _ _ _ (id_pair i j) g := g
| _ _ _ (left i j) (id_pair _ _) := left i j
| _ _ _ (right i j) (id_pair _ _) := right i j

section
local attribute [tidy] tactic.case_bash

instance : category (pairwise ι) :=
{ hom := hom,
  id := id,
  comp := λ X Y Z f g, comp f g, }

end

variables {α : Type v} (U : ι → α)

section
variables [semilattice_inf α]

def diagram_obj : pairwise ι → αᵒᵖ
| (single i) := op (U i)
| (pair i j) := op (U i ⊓ U j)

def diagram_map : Π {o₁ o₂ : pairwise ι} (f : o₁ ⟶ o₂), diagram_obj U o₁ ⟶ diagram_obj U o₂
| _ _ (id_single i) := 𝟙 _
| _ _ (id_pair i j) := 𝟙 _
| _ _ (left i j) := (hom_of_le inf_le_left).op
| _ _ (right i j) := (hom_of_le inf_le_right).op

def diagram : pairwise ι ⥤ αᵒᵖ :=
{ obj := diagram_obj U,
  map := λ X Y f, diagram_map U f, }

end

section
-- `complete_lattice` is not really needed, as we only ever use `inf`,
-- but the appropriate structure has not been defined.
variables [complete_lattice α]

def cone_π_app : Π (o : pairwise ι), op (supr U) ⟶ diagram_obj U o
| (single i) := (hom_of_le (le_supr _ _)).op
| (pair i j) := (hom_of_le inf_le_left ≫ hom_of_le (le_supr U i)).op

@[simps]
def cone : cone (diagram U) :=
{ X := op (supr U),
  π := { app := cone_π_app U, } }

-- move
def op_hom_of_le {U V : αᵒᵖ} (h : unop V ≤ unop U) : U ⟶ V :=
has_hom.hom.op (hom_of_le h)
def le_of_op_hom {U V : αᵒᵖ} (h : U ⟶ V) : unop V ≤ unop U :=
le_of_hom (h.unop)

def cone_is_limit : is_limit (cone U) :=
{ lift := λ s, op_hom_of_le
  begin
    apply complete_lattice.Sup_le,
    rintros _ ⟨j, rfl⟩,
    exact le_of_op_hom (s.π.app (single j))
  end }

end

end pairwise

end category_theory
