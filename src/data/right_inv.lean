/-
Copyright © 2021 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/

import data.bundle
import data.equiv.transfer_instance
import data.pi

/-!
# Bundled right inverse (section)

In this file we implement the bundled version of a right inverse function. The final purpose of
this type is to conviniently implement sections of bundles.

## Implementation notes

Let `E : B → Type*` be the collection of fibers of a bundle on `B`.
In the case of sections of bundle we prove that the type of right inverses of `bundle.proj E` is
equivalent to the type `Π x : B, E x`. Both implementations of sections have their advantages:
`right_inv (proj E)` is better to talk about properties such as continuity, whereas `Π x : B, E x`
works better with algebraic structures, it naturally inherits the algebraic structures present on
the fibers, thanks to the `Π` instances. It is hence a good idea to implement both and write down
the equivalence between them, but then we have to choose only one for our final implementation of
sections. We chose `right_inv (proj E)` because: it is more general (some of the results in the
theory of sections are true for `right_inv f`, for a generic `f`), and it has a more natural
coercion to a function `B → bundle.total_space E` which is finally what we want. Note that we could
also register a coercion to `B → bundle.total_space E` from `Π x : B, E x`, and it is not a bad idea
to implement things this way, but it is just slightly more clumsy: in the case of continuous
sections, in the first case one can implement continuous sections as
`structure continuous_section (f : α → β) extends right_inv f, C(β, α)`
whereas in the second way one would have to write continuity manually; it is not a big deal but the
first way is slightly more natural. Also note that to recover the value of the section on the fiber
in the first way one can use `.2` whereas the second way would make use of coercions.

-/

/-- Bundled right inverse of a function. Note that here the `nolint` has a true mathematical
meaning: the structure is inhabited iff the function is surjective. -/
@[nolint has_inhabited_instance]
structure right_inv {α: Type*} {β: Type*} (f : α → β) :=
(to_fun : β → α)
(right_inv' : f ∘ to_fun = id)

namespace right_inv

variables {α: Type*} {β: Type*} {f : α → β} {g h : right_inv f}

instance : has_coe_to_fun (right_inv f) := ⟨_, right_inv.to_fun⟩

@[simp] lemma to_fun_eq_coe (g : right_inv f) : g.to_fun = ⇑g := rfl

lemma coe_injective (H : ⇑g = h) : g = h :=
by { cases g, cases h, congr' }

@[ext] theorem ext (H : ∀ a, g a = h a) : g = h :=
coe_injective $ funext H

lemma right_inv_def {f : α → β} (g : right_inv f) : f ∘ g = id := g.right_inv'

end right_inv

section bundle_sections

/-! ## Section of bundles -/

open bundle

variables {B : Type*} {E : B → Type*}

@[simp] lemma right_inv.right_inv_apply (f : right_inv (proj E)) (b : B) : proj E (f b) = b :=
by { exact congr_fun f.right_inv_def b, }

@[simp] lemma right_inv.fst_eq_id (f : right_inv (proj E)) (b : B) : (f b).fst = b :=
by { have h : (f b).fst = (proj E) (f b) := rfl, rw [h, f.right_inv_apply] }

/-- Pi function from a right inverse. -/
def right_inv.to_pi'' (g : right_inv (proj E)) : Π x : B, E x :=
λ x, cast (congr_arg E (congr_fun g.right_inv' x)) (g x).2

lemma right_inv.to_pi_apply (g : right_inv (proj E)) (x : B) : g.to_pi'' x == (g x).2 :=
cast_heq (right_inv.to_pi''._proof_1 g x) (g x).snd

/-- Righ inverse from a Pi function. -/
def pi.to_right_inv (g : Π x, E x) : right_inv (proj E) :=
{ to_fun := λ x, ⟨x, g x⟩, right_inv' := rfl }

lemma pi.to_right_inv_apply (g : Π x, E x) (x : B) : (pi.to_right_inv g) x = ⟨x, g x⟩ := rfl

/-- Equivalence between Pi functions and righ inverses. -/
def right_inv.to_pi' : equiv (right_inv (proj E)) (Π x, E x) :=
{ to_fun := right_inv.to_pi'',
  inv_fun := pi.to_right_inv,
  left_inv := λ g, by { ext, exacts [(congr_fun g.right_inv' a).symm, right_inv.to_pi_apply g a] },
  right_inv := λ g, rfl }

lemma right_inv.snd_eq_to_pi_fst' {g : right_inv (proj E)} {b : B} :
  (right_inv.to_pi' g) (g b).fst = (g b).snd :=
begin
  rw [← heq_iff_eq],
  apply (cast_heq _ _).trans,
  exact congr_arg_heq sigma.snd (congr_arg g (g.fst_eq_id b)),
end

section monoid

variables (R : Type*) [semiring R] [∀ x, add_comm_monoid (E x)] [∀ x, module R (E x)]

instance : add_comm_monoid (right_inv (proj E)) := equiv.add_comm_monoid right_inv.to_pi'
instance : module R (right_inv (proj E)) := equiv.module R right_inv.to_pi'

/-- Linear equivalence between Pi functions and righ inverses. -/
def right_inv.to_pi : (right_inv (proj E)) ≃ₗ[R] (Π x, E x) :=
{ map_add' := λ g h, rfl,
  map_smul' := λ r g, rfl,
  ..right_inv.to_pi' }

@[simp] lemma right_inv.snd_eq_to_pi_fst {g : right_inv (proj E)} {b : B} :
  (right_inv.to_pi R g) (g b).fst = (g b).snd := right_inv.snd_eq_to_pi_fst'

end monoid

section group

variable [∀ x, add_comm_group (E x)]

instance : add_comm_group (right_inv (proj E)) := equiv.add_comm_group right_inv.to_pi'

end group

end bundle_sections
