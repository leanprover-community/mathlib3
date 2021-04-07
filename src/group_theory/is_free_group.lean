/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import group_theory.free_group
/-!
This file defines the universal property of free groups, and proves some things about
groups with this property. For an explicit construction of free groups, see
`group_theory/free_group`.
-/
noncomputable theory
universes u w

/-- `is_free_group G` means that `G` has the universal property of a free group.
    That is, it has a family `generators G` of elements, such that a group homomorphism
    `G →* X` is uniquely determined by a function `generators G → X`. -/
class is_free_group (G : Type u) [group G] : Type (u+1) :=
(generators : Type u)
(of : generators → G)
(unique_lift : ∀ {X : Type u} [group X] (f : generators → X),
                ∃! F : G →* X, ∀ a, F (of a) = f a)

instance free_group_is_free_group {A} : is_free_group (free_group A) :=
{ generators := A,
  of := free_group.of,
  unique_lift := begin
    introsI X _ f,
    exact ⟨free_group.lift f,
      λ _, free_group.lift.of,
      λ g hg, monoid_hom.ext (λ _, free_group.lift.unique g hg)⟩
  end }

namespace is_free_group

variables {G H : Type u} [group G] [group H] [is_free_group G]

/-- The group homomorphism from a free group given by some function on the generators. -/
def lift' (f : generators G → H) : G →* H := classical.some (unique_lift f)
@[simp] lemma lift'_of (f : generators G → H) (a : generators G) : (lift' f) (of a) = f a :=
(classical.some_spec (unique_lift f)).left a
lemma eq_lift' (f : generators G → H) (F : G →* H) (h : ∀ a, F (of a) = f a) : F = lift' f :=
(classical.some_spec (unique_lift f)).right F h

lemma end_is_id (f : G →* G) (h : ∀ a, f (of a) = of a) : ∀ g, f g = g :=
let u := eq_lift' (f ∘ of) in
have claim : f = monoid_hom.id G := trans (u _ (λ _, rfl)) (u _ (by simp [h])).symm,
monoid_hom.ext_iff.mp claim

variable (G)
/-- Any free group is isomorphic to "the" free group. -/
@[simps] def iso_free_group_of_is_free_group : G ≃* free_group (generators G) :=
{ to_fun := lift' free_group.of,
  inv_fun := free_group.lift of,
  left_inv := end_is_id ((free_group.lift of).comp (lift' free_group.of)) (by simp),
  right_inv := begin
    have : (lift' free_group.of).comp (free_group.lift of) =
      monoid_hom.id (free_group (generators G)),
    { ext, simp },
    rwa monoid_hom.ext_iff at this,
  end,
  map_mul' := (lift' free_group.of).map_mul }

variable {G}

/-- Being a free group transports across group isomorphisms. -/
def of_mul_equiv (h : G ≃* H) : is_free_group H :=
{ generators := generators G,
  of := h ∘ of,
  unique_lift := begin
    introsI X _ f,
    refine ⟨(lift' f).comp h.symm.to_monoid_hom, _, _⟩,
    { simp },
    intros F' hF',
    suffices : F'.comp h.to_monoid_hom = lift' f,
    { rw ←this, ext, apply congr_arg, symmetry, apply mul_equiv.apply_symm_apply },
    apply eq_lift',
    apply hF',
  end }

/-- A universe-polymorphic version of `unique_lift`. -/
lemma unique_lift' {X : Type w} [group X] (f : generators G → X) :
  ∃! F : G →* X, ∀ a, F (of a) = f a :=
⟨(free_group.lift f).comp (iso_free_group_of_is_free_group G).to_monoid_hom, by simp,
  begin
    intros F' hF',
    suffices : F'.comp (iso_free_group_of_is_free_group G).symm.to_monoid_hom = free_group.lift f,
    { rw ←this,
      ext, apply congr_arg,
      rw [mul_equiv.coe_to_monoid_hom, mul_equiv.coe_to_monoid_hom, mul_equiv.symm_apply_apply ] },
    ext, simp [hF'],
  end⟩

end is_free_group
