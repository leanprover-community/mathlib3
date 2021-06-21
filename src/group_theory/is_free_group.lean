/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn, Eric Wieser
-/
import group_theory.free_group
/-!
# Free groups structures on arbitrary types

This file defines the universal property of free groups, and proves some things about
groups with this property. For an explicit construction of free groups, see
`group_theory/free_group`.

## Main definitions

* `is_free_group G` - a typeclass to indicate that `G` is free over some generators
* `is_free_group.lift` - the (noncomputable) universal property of the free group
* `is_free_group.to_free_group` - any free group with generators `A` is equivalent to
  `free_group A`.

## Implementation notes

While the typeclass only requires the universal property hold within a single universe `u`, our
explicit construction of `free_group` allows this to be extended universe polymorphically. The
primed definition names in this file refer to the non-polymorphic versions.

-/
noncomputable theory
universes u w

/-- `is_free_group G` means that `G` has the universal property of a free group,
That is, it has a family `generators G` of elements, such that a group homomorphism
`G →* X` is uniquely determined by a function `generators G → X`. -/
class is_free_group (G : Type u) [group G] : Type (u+1) :=
(generators : Type u)
(of : generators → G)
(unique_lift' : ∀ {X : Type u} [group X] (f : generators → X),
                ∃! F : G →* X, ∀ a, F (of a) = f a)

instance free_group_is_free_group {A} : is_free_group (free_group A) :=
{ generators := A,
  of := free_group.of,
  unique_lift' := begin
    introsI X _ f,
    have := free_group.lift.symm.bijective.exists_unique f,
    simp_rw function.funext_iff at this,
    exact this,
  end }

namespace is_free_group

variables {G H : Type u} {X : Type w} [group G] [group H] [group X] [is_free_group G]

/-- The equivalence between functions on the generators and group homomorphisms from a free group
given by those generators. -/
@[simps symm_apply]
def lift' : (generators G → H) ≃ (G →* H) :=
{ to_fun := λ f, classical.some (unique_lift' f),
  inv_fun := λ F, F ∘ of,
  left_inv := λ f, funext (classical.some_spec (unique_lift' f)).left,
  right_inv := λ F, ((classical.some_spec (unique_lift' (F ∘ of))).right F (λ _, rfl)).symm }

@[simp] lemma lift'_of (f : generators G → H) (a : generators G) : (lift' f) (of a) = f a :=
congr_fun (lift'.symm_apply_apply f) a

@[simp] lemma lift'_eq_free_group_lift {A : Type u} :
  (@lift' (free_group A) H _ _ _) = free_group.lift :=
begin
  -- TODO: `apply equiv.symm_bijective.injective`,
  rw [←free_group.lift.symm_symm, ←(@lift' (free_group A) H _ _ _).symm_symm],
  congr' 1,
  ext,
  refl,
end

@[simp] lemma of_eq_free_group_of {A : Type u} : (@of (free_group A) _ _) = free_group.of :=
rfl

@[ext]
lemma ext_hom' ⦃f g : G →* H⦄ (h : ∀ a, f (of a) = g (of a)) :
  f = g :=
lift'.symm.injective $ funext h

/-- Being a free group transports across group isomorphisms within a universe. -/
def of_mul_equiv (h : G ≃* H) : is_free_group H :=
{ generators := generators G,
  of := h ∘ of,
  unique_lift' := begin
    introsI X _ f,
    refine ⟨(lift' f).comp h.symm.to_monoid_hom, _, _⟩,
    { simp },
    intros F' hF',
    suffices : F'.comp h.to_monoid_hom = lift' f,
    { rw ←this, ext, apply congr_arg, symmetry, apply mul_equiv.apply_symm_apply },
    ext,
    simp [hF'],
  end }

/-!
### Universe-polymorphic definitions


The primed definitions and lemmas above require `G` and `H` to be in the same universe `u`.
The lemmas below use `X` in a different universe `w`
-/

variable (G)

/-- Any free group is isomorphic to "the" free group. -/
@[simps] def to_free_group : G ≃* free_group (generators G) :=
{ to_fun := lift' free_group.of,
  inv_fun := free_group.lift of,
  left_inv :=
    suffices (free_group.lift of).comp (lift' free_group.of) = monoid_hom.id G,
    from monoid_hom.congr_fun this,
    by { ext, simp },
  right_inv :=
    suffices
      (lift' free_group.of).comp (free_group.lift of) = monoid_hom.id (free_group (generators G)),
    from monoid_hom.congr_fun this,
    by { ext, simp },
  map_mul' := (lift' free_group.of).map_mul }

variable {G}

private lemma lift_right_inv_aux (F : G →* X) :
  free_group.lift.symm (F.comp (to_free_group G).symm.to_monoid_hom) = F ∘ of :=
by { ext, simp }

/-- A universe-polymorphic version of `is_free_group.lift'`. -/
@[simps symm_apply]
def lift : (generators G → X) ≃ (G →* X) :=
{ to_fun := λ f, (free_group.lift f).comp (to_free_group G).to_monoid_hom,
  inv_fun := λ F, F ∘ of,
  left_inv := λ f, free_group.lift.injective begin
    ext x,
    simp,
  end,
  right_inv := λ F, begin
    dsimp,
    rw ←lift_right_inv_aux,
    simp only [equiv.apply_symm_apply],
    ext x,
    dsimp only [monoid_hom.comp_apply, mul_equiv.coe_to_monoid_hom],
    rw mul_equiv.symm_apply_apply,
  end}

@[ext]
lemma ext_hom ⦃f g : G →* X⦄ (h : ∀ a, f (of a) = g (of a)) :
  f = g :=
is_free_group.lift.symm.injective $ funext h

@[simp] lemma lift_of (f : generators G → X) (a : generators G) : (lift f) (of a) = f a :=
congr_fun (lift.symm_apply_apply f) a

@[simp] lemma lift_eq_free_group_lift {A : Type u} :
  (@lift (free_group A) H _ _ _) = free_group.lift :=
begin
  -- TODO: `apply equiv.symm_bijective.injective`,
  rw [←free_group.lift.symm_symm, ←(@lift (free_group A) H _ _ _).symm_symm],
  congr' 1,
  ext,
  refl,
end

/-- A universe-polymorphic version of `unique_lift`. -/
lemma unique_lift {X : Type w} [group X] (f : generators G → X) :
  ∃! F : G →* X, ∀ a, F (of a) = f a :=
begin
  have := lift.symm.bijective.exists_unique f,
  simp_rw function.funext_iff at this,
  exact this,
end

end is_free_group
