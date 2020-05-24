/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Johan Commelin
-/
import data.polynomial

universes u v

def free_ring (α : Type u) : Type u :=
free_abelian_group $ free_monoid α

namespace free_ring

variables (α : Type u)

instance : ring (free_ring α) := free_abelian_group.ring _

instance : inhabited (free_ring α) := ⟨0⟩

variables {α}
def of (x : α) : free_ring α :=
free_abelian_group.of $ free_monoid.of x

@[elab_as_eliminator] protected lemma induction_on
  {C : free_ring α → Prop} (z : free_ring α)
  (hn1 : C (-1)) (hb : ∀ b, C (of b))
  (ha : ∀ x y, C x → C y → C (x + y))
  (hm : ∀ x y, C x → C y → C (x * y)) : C z :=
have hn : ∀ x, C x → C (-x), from λ x ih, neg_one_mul x ▸ hm _ _ hn1 ih,
have h1 : C 1, from neg_neg (1 : free_ring α) ▸ hn _ hn1,
free_abelian_group.induction_on z
  (add_left_neg (1 : free_ring α) ▸ ha _ _ hn1 h1)
  (λ m, list.rec_on m h1 $ λ a m ih, hm _ _ (hb a) ih)
  (λ m ih, hn _ ih)
  ha

section lift

variables {R : Type v} [ring R] (f : α → R)

def lift : (α → R) ≃ (free_ring α →+* R) :=
free_monoid.lift.trans free_abelian_group.ring_lift

@[simp] lemma lift_symm_apply (f : free_ring α →+* R) : lift.symm f = f ∘ of := rfl

@[simp] lemma lift_eval_of (x : α) : lift f (of x) = f x :=
(free_abelian_group.lift_eval_of _ _).trans (free_monoid.lift_eval_of _ _)

@[simp] lemma lift_comp_of (f : free_ring α →+* R) : lift (f ∘ of) = f :=
lift.apply_symm_apply f

end lift

variables {β : Type v} (f : α → β)

def map : free_ring α →+* free_ring β :=
lift $ of ∘ f

end free_ring
