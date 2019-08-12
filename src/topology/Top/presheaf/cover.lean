import topology.Top.presheaf
import category_theory.full_subcategory
import category_theory.limits.opposites

universes v u

open category_theory
open category_theory.limits
open topological_space
open opposite

namespace Top

variables (X : Top.{v})

structure cover : Type (v+1) :=
(ι : Type v)
(i : ι → opens X)

variables {X}

namespace cover

/-- The union of all the open sets in the cover. -/
-- Implementation note: I was uncertain whether it would be better to parametrise cover by the union,
-- and include a condition specifying `total = lattice.supr c.i`.
def total (c : cover X) : opens X := lattice.supr c.i

/--
A morphism of covers.
-/
structure hom (c d : cover X) :=
(s : c.ι → d.ι)
(r : Π i : c.ι, c.i i ⟶ d.i (s i))

namespace hom

@[extensionality] lemma ext {c d : cover X} {f g : hom c d} (h : f.s = g.s) : f = g :=
by { cases f, cases g, congr, assumption }

def id (c : cover X) : hom c c :=
{ s := id,
  r := λ i, 𝟙 _ }

def comp (c d e : cover X) (f : hom c d) (g : hom d e) : hom c e :=
{ s := g.s ∘ f.s,
  r := λ i, f.r i ≫ g.r (f.s i) }

instance : category (cover X) :=
{ hom := hom,
  id := id,
  comp := comp }

end hom

end cover

def cover_of (U : opens X) := { c : cover X // c.total = U }

instance (U : opens X) : category (cover_of U) := sorry

namespace cover

inductive intersections (ι : Type v)
| single : ι → intersections
| double : ι → ι → intersections
.

variable (ι : Type v)

namespace intersections

inductive hom : intersections ι → intersections ι → Type v
| id_single : Π (a : ι), hom (single a) (single a)
| id_double : Π (a b : ι), hom (double a b) (double a b)
| left : Π (a b : ι), hom (single a) (double a b)
| right : Π (a b : ι), hom (single b) (double a b)
.

def id : Π j : intersections ι, hom ι j j
| (single a) := hom.id_single a
| (double a b) := hom.id_double a b
.

def comp : Π j₁ j₂ j₃ : intersections ι, hom ι j₁ j₂ → hom ι j₂ j₃ → hom ι j₁ j₃
| _ _ _ (hom.id_single _) x := x
| _ _ _ (hom.id_double _ _) x := x
| _ _ _ (hom.left a b) (hom.id_double _ _) := hom.left a b
| _ _ _ (hom.right a b) (hom.id_double _ _) := hom.right a b

local attribute [tidy] tactic.case_bash
instance : small_category (intersections ι) :=
{ hom := hom ι,
  id := id ι,
  comp := comp ι }

end intersections

open intersections

variable (c : cover X)

def diagram_obj : intersections (c.ι) → (opens X)ᵒᵖ
| (single a) := op (c.i a)
| (double a b) := op ((c.i a) ∩ (c.i b))

@[simp] def diagram_map : Π (x y : intersections (c.ι)) (f : x ⟶ y), diagram_obj c x ⟶ diagram_obj c y
| _ _ (hom.id_single _)   := 𝟙 _
| _ _ (hom.id_double _ _) := 𝟙 _
| _ _ (hom.left a b)      := has_hom.hom.op ⟨⟨lattice.inf_le_left⟩⟩ -- TODO lemma for this
| _ _ (hom.right a b)     := has_hom.hom.op ⟨⟨lattice.inf_le_right⟩⟩

def diagram : intersections (c.ι) ⥤ (opens X)ᵒᵖ :=
{ obj := diagram_obj c,
  map := diagram_map c, }

@[simp] lemma diagram_obj_single (a) : c.diagram.obj (single a) = op (c.i a) := rfl
@[simp] lemma diagram_obj_double (a b) : c.diagram.obj (double a b) = op ((c.i a) ∩ (c.i b)) := rfl

/--
The union of all the sets in the cover is the same as the union of all the sets and
all the pairwise intersections.
-/
lemma supr_eq_supr_diagram : lattice.supr (c.i) = lattice.supr ((functor.left_op (diagram c)).obj) :=
begin
  ext,
  split,
  { rintro ⟨U, ⟨⟨V, ⟨⟨i, rfl⟩, rfl⟩⟩, m⟩⟩,
    apply set.mem_of_subset_of_mem _ m,
    apply opens.subset_iff_val_subset.1,
    exact lattice.le_supr ((functor.left_op (diagram c)).obj) (op (single i)) },
  { rintro ⟨U, ⟨⟨V, ⟨⟨i, rfl⟩, rfl⟩⟩, w⟩⟩,
    apply set.mem_of_subset_of_mem _ w, clear w,
    apply opens.subset_iff_val_subset.1,
    -- Unfortunately the `op_induction` tactic doesn't work here:
    revert i,
    apply @opposite.op_induction (intersections (c.ι))
      (λ i, unop ((diagram c).obj (unop i)) ⊆ lattice.supr (c.i)),
    rintro (i | ⟨i₁,i₂⟩),
    { exact lattice.le_supr c.i i },
    { exact le_trans lattice.inf_le_left (lattice.le_supr c.i i₁) }}
end

/-- The limit of the intersection diagram in `(opens X)ᵒᵖ` is just the union of the open sets. -/
lemma diagram_limit_total : limit (c.diagram) = op (c.total) :=
opens.op_eq_of_iso $ calc
    limit (c.diagram) ≅ _         : limit_in_op_iso_op_colimit _
    ... ≅ _                       : iso.op (colimit_in_complete_lattice _).symm
    ... ≅ op (lattice.supr (c.i)) : iso.op (eq_to_iso (supr_eq_supr_diagram c))

variables {Y : Top.{v}}

/-- Pull back a cover by a continuous map. -/
def map (f : X ⟶ Y) (c : cover Y) : cover X :=
{ ι := c.ι,
  i := λ i, (opens.map f).obj (c.i i) }

/-- Pulling back an intersection diagram is just the intersection diagram for the pulled back cover. -/
def map_diagram (f : X ⟶ Y) (c : cover Y) :
  c.diagram ⋙ (opens.map f).op ≅ (c.map f).diagram :=
{ hom := { app := λ X, by { cases X; exact 𝟙 _ } },
  inv := { app := λ X, by { cases X; exact 𝟙 _ } } }

end cover

end Top
