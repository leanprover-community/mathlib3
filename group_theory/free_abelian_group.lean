/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Free abelian groups as abelianizatin of free groups.
-/

import group_theory.free_group
import group_theory.abelianization

universes u v

variables (α : Type u)

def free_abelian_group : Type u :=
additive $ abelianization $ free_group α

instance : add_comm_group (free_abelian_group α) :=
@additive.add_comm_group _ $ abelianization.comm_group _

variable {α}

namespace free_abelian_group

def of (x : α) : free_abelian_group α :=
abelianization.of $ free_group.of x

instance : has_coe α (free_abelian_group α) :=
⟨of⟩

theorem coe_def (x : α) : (x : free_abelian_group α) = of x :=
rfl

section to_comm_group

variables {β : Type v} [add_comm_group β] (f : α → β)

def to_add_comm_group (x : free_abelian_group α) : β :=
@abelianization.to_comm_group _ _ (multiplicative β) _ (@free_group.to_group _ (multiplicative β) _ f) _ x

def to_add_comm_group.is_add_group_hom :
  is_add_group_hom (to_add_comm_group f) :=
⟨λ x y, @is_group_hom.mul _ (multiplicative β) _ _ _ (abelianization.to_comm_group.is_group_hom _) x y⟩

local attribute [instance] to_add_comm_group.is_add_group_hom

@[simp] lemma to_add_comm_group.add (x y : free_abelian_group α) :
  to_add_comm_group f (x + y) = to_add_comm_group f x + to_add_comm_group f y :=
is_add_group_hom.add _ _ _

@[simp] lemma to_add_comm_group.neg (x : free_abelian_group α) :
  to_add_comm_group f (-x) = -to_add_comm_group f x :=
is_add_group_hom.neg _ _

@[simp] lemma to_add_comm_group.sub (x y : free_abelian_group α) :
  to_add_comm_group f (x - y) = to_add_comm_group f x - to_add_comm_group f y :=
by simp

@[simp] lemma to_add_comm_group.zero :
  to_add_comm_group f 0 = 0 :=
is_add_group_hom.zero _

@[simp] lemma to_add_comm_group.of (x : α) :
  to_add_comm_group f (of x) = f x :=
by unfold of; unfold to_add_comm_group; simp

@[simp] lemma to_add_comm_group.coe (x : α) :
  to_add_comm_group f ↑x = f x :=
to_add_comm_group.of f x

theorem to_add_comm_group.unique
  (g : free_abelian_group α → β) [is_add_group_hom g]
  (hg : ∀ x, g (of x) = f x) {x} :
  g x = to_add_comm_group f x :=
@abelianization.to_comm_group.unique (free_group α) _ (multiplicative β) _ _ _ g
  ⟨λ x y, @is_add_group_hom.add (additive $ abelianization (free_group α)) _ _ _ _ _ x y⟩ (λ x,
  @free_group.to_group.unique α (multiplicative β) _ _ (g ∘ abelianization.of)
    ⟨λ m n, is_add_group_hom.add g (abelianization.of m) (abelianization.of n)⟩ hg _) _

theorem to_add_comm_group.ext
  (g h : free_abelian_group α → β)
  [is_add_group_hom g] [is_add_group_hom h]
  (H : ∀ x, g (of x) = h (of x)) {x} :
  g x = h x :=
(to_add_comm_group.unique (g ∘ of) g (λ _, rfl)).trans $
eq.symm $ to_add_comm_group.unique _ _ $ λ x, eq.symm $ H x

def UMP : (α → β) ≃ { f : free_abelian_group α → β // is_add_group_hom f } :=
{ to_fun := λ f, ⟨_, to_add_comm_group.is_add_group_hom f⟩,
  inv_fun := λ f, f.1 ∘ of,
  left_inv := λ f, funext $ λ x, to_add_comm_group.of f x,
  right_inv := λ f, subtype.eq $ funext $ λ x, eq.symm $ by letI := f.2; from
    to_add_comm_group.unique _ _ (λ _, rfl) }

end to_comm_group

local attribute [instance] quotient_group.left_rel normal_subgroup.to_is_subgroup

@[elab_as_eliminator]
protected theorem induction_on
  {C : free_abelian_group α → Prop}
  (z : free_abelian_group α)
  (C0 : C 0)
  (C1 : ∀ x, C $ of x)
  (Cn : ∀ x, C (of x) → C (-of x))
  (Cp : ∀ x y, C x → C y → C (x + y)) : C z :=
quotient.induction_on z $ λ x, quot.induction_on x $ λ L,
list.rec_on L C0 $ λ ⟨x, b⟩ tl ih,
bool.rec_on b (Cp _ _ (Cn _ (C1 x)) ih) (Cp _ _ (C1 x) ih)

end free_abelian_group