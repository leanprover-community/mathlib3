/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
import combinatorics.quiver.connected_component

/-!
# Single-object quiver

Single object quiver with a given edge type.

## Main definitions

Given a type `α`, `single_obj α` is `unit` type, whose single object is called `star α`, with
`quiver` structure such that `star α ⟶ star α` is the type `α`.
An element `x : α` can be reinterpreted as an element of `star α ⟶ star α` using
`to_hom`. More generally, a list of elements of `a` can be reinterpreted as a path from `star α` to
itself using `path_equiv_list`.
-/

namespace quiver

/-- Type tag on `unit` used to define single-object quivers. -/
@[nolint unused_arguments]
def single_obj (α : Type*) : Type := unit

namespace single_obj

variables (α β γ : Type*)

instance : quiver (single_obj α) := ⟨λ _ _, α⟩

/-- The single object in `single_obj α`. -/
def star : single_obj α := unit.star

instance : inhabited (single_obj α) := ⟨star α⟩

variables {α β γ}

/-- The `has_reverse` structure on `single_obj α` given a function on `α`. -/
def has_reverse (rev : α → α) : has_reverse (single_obj α) := ⟨λ _ _, rev⟩

/-- The `has_involutive_reverse` structure on `single_obj α` given an involution on `α`. -/
def has_involutive_reverse (rev : α → α) (h : function.involutive rev) :
  has_involutive_reverse (single_obj α) :=
{ to_has_reverse := has_reverse rev,
  inv' := λ _ _, h}

/-- The type of arrows from `star α` to itself is equivalent to the original type `α`. -/
@[simps] def to_hom : α ≃ (star α ⟶ star α) := equiv.refl _

/-- Prefunctors between two `single_obj` quivers correspond to functions between the corresponding
edge types. -/
def map_fun :
  (α → β) ≃ (single_obj α ⥤q single_obj β) :=
{ to_fun := λ f, ⟨id, λ _ _, f⟩,
  inv_fun := λ f a, f.map (to_hom a),
  left_inv := λ _, rfl,
  right_inv :=  λ f, by cases f; obviously }

lemma map_fun_id : map_fun id = 𝟭q (single_obj α) := rfl

@[simp] lemma map_fun_symm_id :
  map_fun.symm (𝟭q (single_obj α)) = id := rfl

lemma map_fun_comp (f : α → β) (g : β → γ) :
  map_fun (g ∘ f) = (map_fun f ⋙q map_fun g) := rfl

@[simp] lemma map_fun_symm_comp (f : single_obj α ⥤q single_obj β)
  (g : single_obj β ⥤q single_obj γ) : map_fun.symm (f ⋙q g) =
  (map_fun.symm g ∘ map_fun.symm f) :=
by simp only [equiv.symm_apply_eq, map_fun_comp, equiv.apply_symm_apply]



/-- Auxiliary definition for `quiver.single_obj.path_equiv_list`.
Converts a path in the quiver `single_obj α` into a list of elements of type `a`. -/
def path_to_list : Π {x : single_obj α}, path (star α) x → list α
| _ path.nil := []
| _ (path.cons p a) := a :: (path_to_list p)

@[simp] lemma path_to_list_nil : path_to_list path.nil = ([] : list α) := rfl
@[simp] lemma path_to_list_cons {x y : single_obj α} (p : path (star α) x) (a : x ⟶ y) :
  path_to_list (p.cons a) = a :: path_to_list p := rfl

/-- Auxiliary definition for `quiver.single_obj.path_equiv_list`.
Converts a list of elements of type `α` into a path in the quiver `single_obj α`. -/
def list_to_path : list α → path (star α) (star α)
| [] := path.nil
| (a :: l) := (list_to_path l).cons a

@[simp] lemma list_to_path_nil : list_to_path ([] : list α) = path.nil := rfl
@[simp] lemma list_to_path_cons (l : list α) (a : α) :
  list_to_path (a :: l) = (list_to_path l).cons a := rfl

lemma path_to_list_to_path {x : single_obj α} (p : path (star α) x) :
  list_to_path (path_to_list p) == p :=
by { induction p with y z p a ih, refl, tidy }

lemma list_to_path_to_list (l : list α) :
  path_to_list (list_to_path l) = l :=
by { induction l with a l ih, refl, simp [ih] }

/-- Paths in `single_obj α` quiver correspond to lists of elements of type `α`. -/
@[simps] def path_equiv_list : path (star α) (star α) ≃ list α :=
⟨path_to_list, list_to_path, λ p, eq_of_heq (path_to_list_to_path p), list_to_path_to_list⟩

end single_obj

end quiver
