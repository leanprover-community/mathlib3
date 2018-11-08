/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Free abelian groups as abelianization of free groups.
-/
import algebra.pi_instances
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

def lift {β : Type v} [add_comm_group β] (f : α → β) (x : free_abelian_group α) : β :=
@abelianization.lift _ _ (multiplicative β) _ (@free_group.to_group _ (multiplicative β) _ f) _ x

namespace lift
variables {β : Type v} [add_comm_group β] (f : α → β)
open free_abelian_group

instance is_add_group_hom : is_add_group_hom (lift f) :=
⟨λ x y, @is_group_hom.mul _ (multiplicative β) _ _ _ (abelianization.lift.is_group_hom _) x y⟩

@[simp] protected lemma add (x y : free_abelian_group α) :
  lift f (x + y) = lift f x + lift f y :=
is_add_group_hom.add _ _ _

@[simp] protected lemma neg (x : free_abelian_group α) : lift f (-x) = -lift f x :=
is_add_group_hom.neg _ _

@[simp] protected lemma sub (x y : free_abelian_group α) :
  lift f (x - y) = lift f x - lift f y :=
by simp

@[simp] protected lemma zero : lift f 0 = 0 :=
is_add_group_hom.zero _

@[simp] protected lemma of (x : α) : lift f (of x) = f x :=
by unfold of; unfold lift; simp

protected theorem unique (g : free_abelian_group α → β) [is_add_group_hom g]
  (hg : ∀ x, g (of x) = f x) {x} :
  g x = lift f x :=
@abelianization.lift.unique (free_group α) _ (multiplicative β) _ _ _ g
  ⟨λ x y, @is_add_group_hom.add (additive $ abelianization (free_group α)) _ _ _ _ _ x y⟩ (λ x,
  @free_group.to_group.unique α (multiplicative β) _ _ (g ∘ abelianization.of)
    ⟨λ m n, is_add_group_hom.add g (abelianization.of m) (abelianization.of n)⟩ hg _) _

protected theorem ext (g h : free_abelian_group α → β)
  [is_add_group_hom g] [is_add_group_hom h]
  (H : ∀ x, g (of x) = h (of x)) {x} :
  g x = h x :=
(lift.unique (g ∘ of) g (λ _, rfl)).trans $
eq.symm $ lift.unique _ _ $ λ x, eq.symm $ H x

lemma map_hom {α β γ} [add_comm_group β] [add_comm_group γ]
  (a : free_abelian_group α) (f : α → β) (g : β → γ) [is_add_group_hom g] :
  g (a.lift f) = a.lift (g ∘ f) :=
show (g ∘ lift f) a = a.lift (g ∘ f),
begin
  apply @lift.unique,
  assume a,
  simp only [(∘), lift.of]
end

def universal : (α → β) ≃ { f : free_abelian_group α → β // is_add_group_hom f } :=
{ to_fun := λ f, ⟨_, lift.is_add_group_hom f⟩,
  inv_fun := λ f, f.1 ∘ of,
  left_inv := λ f, funext $ λ x, lift.of f x,
  right_inv := λ f, subtype.eq $ funext $ λ x, eq.symm $ by letI := f.2; from
    lift.unique _ _ (λ _, rfl) }

end lift

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

instance is_add_group_hom_lift' {α} (β) [add_comm_group β] (a : free_abelian_group α) :
  is_add_group_hom (λf, (a.lift f : β)) :=
begin
  refine ⟨assume f g, free_abelian_group.induction_on a _ _ _ _⟩,
  { simp [is_add_group_hom.zero (free_abelian_group.lift f)] },
  { simp [lift.of], assume x, refl },
  { simp [is_add_group_hom.neg (free_abelian_group.lift f)],
    assume x h, show - (f x + g x) = -f x + - g x, exact neg_add _ _ },
  { simp [is_add_group_hom.add (free_abelian_group.lift f)],
    assume x y hx hy,
    rw [hx, hy],
    ac_refl }
end

end free_abelian_group
