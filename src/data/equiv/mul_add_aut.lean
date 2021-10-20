/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import group_theory.perm.basic

/-!
# Multiplicative and additive group automorphisms

This file defines the automorphism group structure on `add_aut R := add_equiv R R` and
`mul_aut R := mul_equiv R R`.

## Implementation notes

The definition of multiplication in the automorphism groups agrees with function composition,
multiplication in `equiv.perm`, and multiplication in `category_theory.End`, but not with
`category_theory.comp`.

This file is kept separate from `data/equiv/mul_add` so that `group_theory.perm` is free to use
equivalences (and other files that use them) before the group structure is defined.

## Tags

mul_aut, add_aut
-/
variables {A : Type*} {M : Type*} {G : Type*}

/-- The group of multiplicative automorphisms. -/
@[reducible, to_additive "The group of additive automorphisms."]
def mul_aut (M : Type*) [has_mul M] := M ≃* M

namespace mul_aut

variables (M) [has_mul M]

/--
The group operation on multiplicative automorphisms is defined by
`λ g h, mul_equiv.trans h g`.
This means that multiplication agrees with composition, `(g*h)(x) = g (h x)`.
-/
instance : group (mul_aut M) :=
by refine_struct
{ mul := λ g h, mul_equiv.trans h g,
  one := mul_equiv.refl M,
  inv := mul_equiv.symm,
  div := _,
  npow := @npow_rec _ ⟨mul_equiv.refl M⟩ ⟨λ g h, mul_equiv.trans h g⟩,
  gpow := @gpow_rec _ ⟨mul_equiv.refl M⟩ ⟨λ g h, mul_equiv.trans h g⟩ ⟨mul_equiv.symm⟩ };
intros; ext; try { refl }; apply equiv.left_inv

instance : inhabited (mul_aut M) := ⟨1⟩

@[simp] lemma coe_mul (e₁ e₂ : mul_aut M) : ⇑(e₁ * e₂) = e₁ ∘ e₂ := rfl
@[simp] lemma coe_one : ⇑(1 : mul_aut M) = id := rfl

lemma mul_def (e₁ e₂ : mul_aut M) : e₁ * e₂ = e₂.trans e₁ := rfl
lemma one_def : (1 : mul_aut M) = mul_equiv.refl _ := rfl
lemma inv_def (e₁ : mul_aut M) : e₁⁻¹ = e₁.symm := rfl
@[simp] lemma mul_apply (e₁ e₂ : mul_aut M) (m : M) : (e₁ * e₂) m = e₁ (e₂ m) := rfl
@[simp] lemma one_apply (m : M) : (1 : mul_aut M) m = m := rfl

@[simp] lemma apply_inv_self (e : mul_aut M) (m : M) : e (e⁻¹ m) = m :=
mul_equiv.apply_symm_apply _ _

@[simp] lemma inv_apply_self (e : mul_aut M) (m : M) : e⁻¹ (e m) = m :=
mul_equiv.apply_symm_apply _ _

/-- Monoid hom from the group of multiplicative automorphisms to the group of permutations. -/
def to_perm : mul_aut M →* equiv.perm M :=
by refine_struct { to_fun := mul_equiv.to_equiv }; intros; refl

/-- The tautological action by `mul_aut M` on `M`.

This generalizes `function.End.apply_mul_action`. -/
instance apply_mul_distrib_mul_action {M} [monoid M] : mul_distrib_mul_action (mul_aut M) M :=
{ smul := ($),
  one_smul := λ _, rfl,
  mul_smul := λ _ _ _, rfl,
  smul_one := mul_equiv.map_one,
  smul_mul := mul_equiv.map_mul }

@[simp] protected lemma smul_def {M} [monoid M] (f : mul_aut M) (a : M) : f • a = f a := rfl

/-- `mul_aut.apply_mul_action` is faithful. -/
instance apply_has_faithful_scalar {M} [monoid M] : has_faithful_scalar (mul_aut M) M :=
⟨λ _ _, mul_equiv.ext⟩

/-- Group conjugation, `mul_aut.conj g h = g * h * g⁻¹`, as a monoid homomorphism
mapping multiplication in `G` into multiplication in the automorphism group `mul_aut G`.
See also the type `conj_act G` for any group `G`, which has a `mul_action (conj_act G) G` instance
where `conj G` acts on `G` by conjugation. -/
def conj [group G] : G →* mul_aut G :=
{ to_fun := λ g,
  { to_fun := λ h, g * h * g⁻¹,
    inv_fun := λ h, g⁻¹ * h * g,
    left_inv := λ _, by simp [mul_assoc],
    right_inv := λ _, by simp [mul_assoc],
    map_mul' := by simp [mul_assoc] },
  map_mul' := λ _ _, by ext; simp [mul_assoc],
  map_one' := by ext; simp [mul_assoc] }

@[simp] lemma conj_apply [group G] (g h : G) : conj g h = g * h * g⁻¹ := rfl
@[simp] lemma conj_symm_apply [group G] (g h : G) : (conj g).symm h = g⁻¹ * h * g := rfl
@[simp] lemma conj_inv_apply [group G] (g h : G) : (conj g)⁻¹ h = g⁻¹ * h * g := rfl

end mul_aut

namespace add_aut

variables (A) [has_add A]

/--
The group operation on additive automorphisms is defined by
`λ g h, add_equiv.trans h g`.
This means that multiplication agrees with composition, `(g*h)(x) = g (h x)`.
-/
instance group : group (add_aut A) :=
by refine_struct
{ mul := λ g h, add_equiv.trans h g,
  one := add_equiv.refl A,
  inv := add_equiv.symm,
  div := _,
  npow := @npow_rec _ ⟨add_equiv.refl A⟩ ⟨λ g h, add_equiv.trans h g⟩,
  gpow := @gpow_rec _ ⟨add_equiv.refl A⟩ ⟨λ g h, add_equiv.trans h g⟩ ⟨add_equiv.symm⟩ };
intros; ext; try { refl }; apply equiv.left_inv

instance : inhabited (add_aut A) := ⟨1⟩

@[simp] lemma coe_mul (e₁ e₂ : add_aut A) : ⇑(e₁ * e₂) = e₁ ∘ e₂ := rfl
@[simp] lemma coe_one : ⇑(1 : add_aut A) = id := rfl

lemma mul_def (e₁ e₂ : add_aut A) : e₁ * e₂ = e₂.trans e₁ := rfl
lemma one_def : (1 : add_aut A) = add_equiv.refl _ := rfl
lemma inv_def (e₁ : add_aut A) : e₁⁻¹ = e₁.symm := rfl
@[simp] lemma mul_apply (e₁ e₂ : add_aut A) (a : A) : (e₁ * e₂) a = e₁ (e₂ a) := rfl
@[simp] lemma one_apply (a : A) : (1 : add_aut A) a = a := rfl

@[simp] lemma apply_inv_self (e : add_aut A) (a : A) : e⁻¹ (e a) = a :=
add_equiv.apply_symm_apply _ _

@[simp] lemma inv_apply_self (e : add_aut A) (a : A) : e (e⁻¹ a) = a :=
add_equiv.apply_symm_apply _ _

/-- Monoid hom from the group of multiplicative automorphisms to the group of permutations. -/
def to_perm : add_aut A →* equiv.perm A :=
by refine_struct { to_fun := add_equiv.to_equiv }; intros; refl

/-- The tautological action by `add_aut A` on `A`.

This generalizes `function.End.apply_mul_action`. -/
instance apply_distrib_mul_action {A} [add_monoid A] : distrib_mul_action (add_aut A) A :=
{ smul := ($),
  smul_zero := add_equiv.map_zero,
  smul_add := add_equiv.map_add,
  one_smul := λ _, rfl,
  mul_smul := λ _ _ _, rfl }

@[simp] protected lemma smul_def {A} [add_monoid A] (f : add_aut A) (a : A) : f • a = f a := rfl

/-- `add_aut.apply_distrib_mul_action` is faithful. -/
instance apply_has_faithful_scalar {A} [add_monoid A] : has_faithful_scalar (add_aut A) A :=
⟨λ _ _, add_equiv.ext⟩

/-- Additive group conjugation, `add_aut.conj g h = g + h - g`, as an additive monoid
homomorphism mapping addition in `G` into multiplication in the automorphism group `add_aut G`
(written additively in order to define the map). -/
def conj [add_group G] : G →+ additive (add_aut G) :=
{ to_fun := λ g, @additive.of_mul (add_aut G)
  { to_fun := λ h, g + h - g,
    inv_fun := λ h, -g + h + g,
    left_inv := λ _, by simp [add_assoc],
    right_inv := λ _, by simp [add_assoc],
    map_add' := by simp [add_assoc, sub_eq_add_neg] },
  map_add' := λ _ _, by apply additive.to_mul.injective; ext; simp [add_assoc, sub_eq_add_neg],
  map_zero' := by ext; simpa }

@[simp] lemma conj_apply [add_group G] (g h : G) : conj g h = g + h - g := rfl
@[simp] lemma conj_symm_apply [add_group G] (g h : G) : (conj g).symm h = -g + h + g := rfl
@[simp] lemma conj_inv_apply [add_group G] (g h : G) : (-(conj g)) h = -g + h + g := rfl

end add_aut
