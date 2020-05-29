/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import data.set.function
import logic.function.iterate

/-!
# Fixed points of a self-map

In this file we define

* the predicate `is_fixed_pt f x := f x = x`;
* the set `fixed_points f` of fixed points of a self-map `f`.

We also prove some simple lemmas about `is_fixed_pt` and `∘`, `iterate`, and `semiconj`.

## Tags

fixed point
-/

universes u v

variables {α : Type u} {β : Type v} {f fa g : α → α} {x y : α} {fb : β → β} {m n k : ℕ}

namespace function

/-- A point `x` is a fixed point of `f : α → α` if `f x = x`. -/
def is_fixed_pt (f : α → α) (x : α) := f x = x

-- TODO: why this is not `rfl`?
/-- Every point is a fixed point of `id`. -/
lemma is_fixed_pt_id (x : α) : is_fixed_pt id x := (rfl : _)

namespace is_fixed_pt

instance [h : decidable_eq α] {f : α → α} {x : α} : decidable (is_fixed_pt f x) :=
h (f x) x

/-- If `x` is a fixed point of `f`, then `f x = x`. This is useful, e.g., for `rw` or `simp`.-/
protected lemma eq (hf : is_fixed_pt f x) : f x = x := hf

/-- If `x` is a fixed point of `f` and `g`, then it is a fixed point of `f ∘ g`. -/
protected lemma comp (hf : is_fixed_pt f x) (hg : is_fixed_pt g x) : is_fixed_pt (f ∘ g) x :=
calc f (g x) = f x : congr_arg f hg
         ... = x   : hf

/-- If `x` is a fixed point of `f`, then it is a fixed point of `f^[n]`. -/
protected lemma iterate (hf : is_fixed_pt f x) (n : ℕ) : is_fixed_pt (f^[n]) x :=
iterate_fixed hf n

/-- If `x` is a fixed point of `f ∘ g` and `g`, then it is a fixed point of `f`. -/
lemma left_of_comp (hfg : is_fixed_pt (f ∘ g) x) (hg : is_fixed_pt g x) : is_fixed_pt f x :=
calc f x = f (g x) : congr_arg f hg.symm
     ... = x       : hfg

/-- If `x` is a fixed point of `f` and `g` is a left inverse of `f`, then `x` is a fixed
point of `g`. -/
lemma to_left_inverse (hf : is_fixed_pt f x) (h : left_inverse g f) : is_fixed_pt g x :=
calc g x = g (f x) : congr_arg g hf.symm
     ... = x       : h x

/-- If `g` (semi)conjugates `fa` to `fb`, then it sends fixed points of `fa` to fixed points
of `fb`. -/
protected lemma map {x : α} (hx : is_fixed_pt fa x) {g : α → β} (h : semiconj g fa fb) :
  is_fixed_pt fb (g x) :=
calc fb (g x) = g (fa x) : (h.eq x).symm
          ... = g x      : congr_arg g hx

end is_fixed_pt

/-- The set of fixed points of a map `f : α → α`. -/
def fixed_points (f : α → α) : set α := {x : α | is_fixed_pt f x}

@[simp] lemma mem_fixed_points : x ∈ fixed_points f ↔ is_fixed_pt f x := iff.rfl

lemma semiconj.maps_to_fixed_pts {g : α → β} (h : semiconj g fa fb) :
  set.maps_to g (fixed_points fa) (fixed_points fb) :=
λ x hx, hx.map h

lemma left_inv_on_fixed_pts_comp (f g : α → α) :
  set.left_inv_on f g (fixed_points $ f ∘ g) :=
λ x, id

lemma commute.inv_on_fixed_pts_comp (h : commute f g) :
  set.inv_on f g (fixed_points $ f ∘ g) (fixed_points $ f ∘ g) :=
⟨λ x, id, h.symm.comp_eq ▸ λ x, id⟩

lemma commute.left_bij_on_fixed_pts_comp (h : commute f g) :
  set.bij_on f (fixed_points $ f ∘ g) (fixed_points $ f ∘ g) :=
h.inv_on_fixed_pts_comp.symm.bij_on
  ((commute.refl f).comp_right h).maps_to_fixed_pts
  (h.symm.comp_right (commute.refl g)).maps_to_fixed_pts

lemma commute.right_bij_on_fixed_pts_comp (h : commute f g) :
  set.bij_on g (fixed_points $ f ∘ g) (fixed_points $ f ∘ g) :=
h.symm.comp_eq ▸ h.symm.left_bij_on_fixed_pts_comp

end function
