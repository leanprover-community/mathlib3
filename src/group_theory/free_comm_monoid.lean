/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury G. Kudryashov
-/
import data.multiset

/-!
# Free commutative monoid

This is a tiny wrapper over `multiplicative (multiset α)` that provides some definitions and
lemmas expected from a `free_*` object.
-/

/-- Free commutative monoid over `α`. Defined as `multiplicative (multiset α)`. -/
@[reducible] def free_comm_monoid (α : Type*) := multiplicative (multiset α)

namespace free_comm_monoid

section lift

variables {α : Type*} {M : Type*} {N : Type*} [comm_monoid M] [comm_monoid N]

/-- Canonical embedding of `α` into `free_comm_monoid α`. -/
def of (x : α) : free_comm_monoid α := multiplicative.of_add [x]

@[simp] lemma to_add_of (x : α) : (of x).to_add = [x] := rfl

@[elab_as_eliminator]
lemma induction_on (x : free_comm_monoid α) {p : free_comm_monoid α → Prop}
  (h1 : p 1) (h : ∀ x s, p s → p (of x * s)) :
  p x :=
multiset.induction_on x h1 h

@[ext] lemma hom_eq {f g : free_comm_monoid α →* M} (h : ∀ x : α, f (of x) = g (of x)) :
  f = g :=
monoid_hom.ext $ λ x, induction_on x (f.map_one.trans g.map_one.symm) $ λ a s hs, by simp [*]

/-- Every map from `α` to a commutative monoid `M` lifts to a monoid homomorphism from
`free_comm_monoid α`. -/
def lift : (α → M) ≃ (free_comm_monoid α →* M) :=
{ to_fun := λ f, ⟨λ s, (s.to_add.map f).prod, rfl, λ x y, by simp⟩,
  inv_fun := λ f, f ∘ of,
  left_inv := λ f, by { ext x, simp },
  right_inv := λ f, by { ext x, simp } }

@[simp] lemma lift_symm_apply (f : free_comm_monoid α →* M) :
  lift.symm f = f ∘ of := rfl

lemma lift_comp_of (f : α → M) : (lift f) ∘ of = f := lift.symm_apply_apply f

@[simp]
lemma lift_eval_of (f : α → M) (x : α) : lift f (of x) = f x :=
congr_fun (lift_comp_of f) x

@[simp]
lemma lift_restrict (f : free_comm_monoid α →* M) : lift (f ∘ of) = f :=
lift.apply_symm_apply f

lemma comp_lift (g : M →* N) (f : α → M) : g.comp (lift f) = lift (g ∘ f) :=
by { ext, simp }

lemma hom_map_lift (g : M →* N) (f : α → M) (x : free_comm_monoid α) :
  g (lift f x) = lift (g ∘ f) x :=
monoid_hom.ext_iff.1 (comp_lift g f) x

end lift

end free_comm_monoid
