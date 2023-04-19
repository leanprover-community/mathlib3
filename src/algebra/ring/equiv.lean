/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import algebra.group.opposite
import algebra.hom.ring
import logic.equiv.set
import tactic.assert_exists

/-!
# (Semi)ring equivs

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define extension of `equiv` called `ring_equiv`, which is a datatype representing an
isomorphism of `semiring`s, `ring`s, `division_ring`s, or `field`s. We also introduce the
corresponding group of automorphisms `ring_aut`.

## Notations

* ``infix ` ≃+* `:25 := ring_equiv``

The extended equiv have coercions to functions, and the coercion is the canonical notation when
treating the isomorphism as maps.

## Implementation notes

The fields for `ring_equiv` now avoid the unbundled `is_mul_hom` and `is_add_hom`, as these are
deprecated.

Definition of multiplication in the groups of automorphisms agrees with function composition,
multiplication in `equiv.perm`, and multiplication in `category_theory.End`, not with
`category_theory.comp`.

## Tags

equiv, mul_equiv, add_equiv, ring_equiv, mul_aut, add_aut, ring_aut
-/


variables {F α β R S S' : Type*}

set_option old_structure_cmd true

/-- An equivalence between two (non-unital non-associative semi)rings that preserves the
algebraic structure. -/
structure ring_equiv (R S : Type*) [has_mul R] [has_add R] [has_mul S] [has_add S]
  extends R ≃ S, R ≃* S, R ≃+ S

infix ` ≃+* `:25 := ring_equiv

/-- The "plain" equivalence of types underlying an equivalence of (semi)rings. -/
add_decl_doc ring_equiv.to_equiv

/-- The equivalence of additive monoids underlying an equivalence of (semi)rings. -/
add_decl_doc ring_equiv.to_add_equiv

/-- The equivalence of multiplicative monoids underlying an equivalence of (semi)rings. -/
add_decl_doc ring_equiv.to_mul_equiv

/-- `ring_equiv_class F R S` states that `F` is a type of ring structure preserving equivalences.
You should extend this class when you extend `ring_equiv`. -/
class ring_equiv_class (F : Type*) (R S : out_param Type*)
  [has_mul R] [has_add R] [has_mul S] [has_add S]
  extends mul_equiv_class F R S :=
(map_add : ∀ (f : F) a b, f (a + b) = f a + f b)

namespace ring_equiv_class

@[priority 100] -- See note [lower instance priority]
instance to_add_equiv_class (F R S : Type*)
  [has_mul R] [has_add R] [has_mul S] [has_add S] [h : ring_equiv_class F R S] :
  add_equiv_class F R S :=
{ coe := coe_fn,
  .. h }

@[priority 100] -- See note [lower instance priority]
instance to_ring_hom_class (F R S : Type*)
  [non_assoc_semiring R] [non_assoc_semiring S] [h : ring_equiv_class F R S] :
  ring_hom_class F R S :=
{ coe := coe_fn,
  coe_injective' := fun_like.coe_injective,
  map_zero := map_zero,
  map_one := map_one,
  .. h }

@[priority 100] -- See note [lower instance priority]
instance to_non_unital_ring_hom_class (F R S : Type*)
  [non_unital_non_assoc_semiring R] [non_unital_non_assoc_semiring S] [h : ring_equiv_class F R S] :
  non_unital_ring_hom_class F R S :=
{ coe := coe_fn,
  coe_injective' := fun_like.coe_injective,
  map_zero := map_zero,
  .. h }

end ring_equiv_class

instance [has_mul α] [has_add α] [has_mul β] [has_add β] [ring_equiv_class F α β] :
  has_coe_t F (α ≃+* β) :=
⟨λ f, { to_fun := f, inv_fun := equiv_like.inv f, left_inv := equiv_like.left_inv f,
  right_inv := equiv_like.right_inv f, map_mul' := map_mul f, map_add' := map_add f }⟩

namespace ring_equiv

section basic

variables [has_mul R] [has_add R] [has_mul S] [has_add S] [has_mul S'] [has_add S']

instance : ring_equiv_class (R ≃+* S) R S :=
{ coe := to_fun,
  inv := inv_fun,
  coe_injective' := λ e f h₁ h₂, by { cases e, cases f, congr' },
  map_add := map_add',
  map_mul := map_mul',
  left_inv := ring_equiv.left_inv,
  right_inv := ring_equiv.right_inv }

instance : has_coe_to_fun (R ≃+* S) (λ _, R → S) := ⟨ring_equiv.to_fun⟩

@[simp] lemma to_equiv_eq_coe (f : R ≃+* S) : f.to_equiv = f := rfl

@[simp] lemma to_fun_eq_coe (f : R ≃+* S) : f.to_fun = f := rfl

@[simp] lemma coe_to_equiv (f : R ≃+* S) : ⇑(f : R ≃ S) = f := rfl

/-- A ring isomorphism preserves multiplication. -/
protected lemma map_mul (e : R ≃+* S) (x y : R) : e (x * y) = e x * e y := map_mul e x y

/-- A ring isomorphism preserves addition. -/
protected lemma map_add (e : R ≃+* S) (x y : R) : e (x + y) = e x + e y := map_add e x y

/-- Two ring isomorphisms agree if they are defined by the
    same underlying function. -/
@[ext] lemma ext {f g : R ≃+* S} (h : ∀ x, f x = g x) : f = g := fun_like.ext f g h

@[simp] theorem coe_mk (e e' h₁ h₂ h₃ h₄) :
  ⇑(⟨e, e', h₁, h₂, h₃, h₄⟩ : R ≃+* S) = e := rfl

@[simp] theorem mk_coe (e : R ≃+* S) (e' h₁ h₂ h₃ h₄) :
  (⟨e, e', h₁, h₂, h₃, h₄⟩ : R ≃+* S) = e := ext $ λ _, rfl

protected lemma congr_arg {f : R ≃+* S} {x x' : R} : x = x' → f x = f x' := fun_like.congr_arg f

protected lemma congr_fun {f g : R ≃+* S} (h : f = g) (x : R) : f x = g x := fun_like.congr_fun h x

protected lemma ext_iff {f g : R ≃+* S} : f = g ↔ ∀ x, f x = g x := fun_like.ext_iff

@[simp] lemma to_add_equiv_eq_coe (f : R ≃+* S) : f.to_add_equiv = ↑f := rfl

@[simp] lemma to_mul_equiv_eq_coe (f : R ≃+* S) : f.to_mul_equiv = ↑f := rfl

@[simp, norm_cast] lemma coe_to_mul_equiv (f : R ≃+* S) : ⇑(f : R ≃* S) = f := rfl

@[simp, norm_cast] lemma coe_to_add_equiv (f : R ≃+* S) : ⇑(f : R ≃+ S) = f := rfl

/-- The `ring_equiv` between two semirings with a unique element. -/
def ring_equiv_of_unique {M N}
  [unique M] [unique N] [has_add M] [has_mul M] [has_add N] [has_mul N] : M ≃+* N :=
{ ..add_equiv.add_equiv_of_unique,
  ..mul_equiv.mul_equiv_of_unique}

instance {M N} [unique M] [unique N] [has_add M] [has_mul M] [has_add N] [has_mul N] :
  unique (M ≃+* N) :=
{ default := ring_equiv_of_unique,
  uniq := λ _, ext $ λ x, subsingleton.elim _ _ }

variable (R)

/-- The identity map is a ring isomorphism. -/
@[refl] protected def refl : R ≃+* R := { .. mul_equiv.refl R, .. add_equiv.refl R }

@[simp] lemma refl_apply (x : R) : ring_equiv.refl R x = x := rfl

@[simp] lemma coe_add_equiv_refl : (ring_equiv.refl R : R ≃+ R) = add_equiv.refl R := rfl

@[simp] lemma coe_mul_equiv_refl : (ring_equiv.refl R : R ≃* R) = mul_equiv.refl R := rfl

instance : inhabited (R ≃+* R) := ⟨ring_equiv.refl R⟩

variables {R}

/-- The inverse of a ring isomorphism is a ring isomorphism. -/
@[symm] protected def symm (e : R ≃+* S) : S ≃+* R :=
{ .. e.to_mul_equiv.symm, .. e.to_add_equiv.symm }

/-- See Note [custom simps projection] -/
def simps.symm_apply (e : R ≃+* S) : S → R := e.symm

initialize_simps_projections ring_equiv (to_fun → apply, inv_fun → symm_apply)

@[simp] lemma inv_fun_eq_symm (f : R ≃+* S) : f.inv_fun = f.symm := rfl

@[simp] lemma symm_symm (e : R ≃+* S) : e.symm.symm = e := ext $ λ x, rfl

@[simp]
lemma coe_to_equiv_symm (e : R ≃+* S) : (e.symm : S ≃ R) = (e : R ≃ S).symm := rfl

lemma symm_bijective : function.bijective (ring_equiv.symm : (R ≃+* S) → (S ≃+* R)) :=
equiv.bijective ⟨ring_equiv.symm, ring_equiv.symm, symm_symm, symm_symm⟩

@[simp] lemma mk_coe' (e : R ≃+* S) (f h₁ h₂ h₃ h₄) :
  (ring_equiv.mk f ⇑e h₁ h₂ h₃ h₄ : S ≃+* R) = e.symm :=
symm_bijective.injective $ ext $ λ x, rfl

@[simp] lemma symm_mk (f : R → S) (g h₁ h₂ h₃ h₄) :
  (mk f g h₁ h₂ h₃ h₄).symm =
  { to_fun := g, inv_fun := f, ..(mk f g h₁ h₂ h₃ h₄).symm} := rfl

/-- Transitivity of `ring_equiv`. -/
@[trans] protected def trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') : R ≃+* S' :=
{ .. (e₁.to_mul_equiv.trans e₂.to_mul_equiv), .. (e₁.to_add_equiv.trans e₂.to_add_equiv) }

lemma trans_apply (e₁ : R ≃+* S) (e₂ : S ≃+* S') (a : R) :
  e₁.trans e₂ a = e₂ (e₁ a) := rfl

@[simp] lemma coe_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
  (e₁.trans e₂ : R → S') = e₂ ∘ e₁ := rfl

@[simp]
lemma symm_trans_apply (e₁ : R ≃+* S) (e₂ : S ≃+* S') (a : S') :
  (e₁.trans e₂).symm a = e₁.symm (e₂.symm a) := rfl

lemma symm_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
  (e₁.trans e₂).symm = e₂.symm.trans (e₁.symm) := rfl

protected lemma bijective (e : R ≃+* S) : function.bijective e := equiv_like.bijective e
protected lemma injective (e : R ≃+* S) : function.injective e := equiv_like.injective e
protected lemma surjective (e : R ≃+* S) : function.surjective e := equiv_like.surjective e

@[simp] lemma apply_symm_apply (e : R ≃+* S) : ∀ x, e (e.symm x) = x := e.to_equiv.apply_symm_apply
@[simp] lemma symm_apply_apply (e : R ≃+* S) : ∀ x, e.symm (e x) = x := e.to_equiv.symm_apply_apply

lemma image_eq_preimage (e : R ≃+* S) (s : set R) : e '' s = e.symm ⁻¹' s :=
e.to_equiv.image_eq_preimage s

@[simp] lemma coe_mul_equiv_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
  (e₁.trans e₂ : R ≃* S') = (e₁ : R ≃* S).trans ↑e₂:= rfl
@[simp] lemma coe_add_equiv_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
  (e₁.trans e₂ : R ≃+ S') = (e₁ : R ≃+ S).trans ↑e₂:= rfl

end basic

section opposite
open mul_opposite

/-- A ring iso `α ≃+* β` can equivalently be viewed as a ring iso `αᵐᵒᵖ ≃+* βᵐᵒᵖ`. -/
@[simps]
protected def op {α β} [has_add α] [has_mul α] [has_add β] [has_mul β] :
  (α ≃+* β) ≃ (αᵐᵒᵖ ≃+* βᵐᵒᵖ) :=
{ to_fun    := λ f, { ..f.to_add_equiv.mul_op, ..f.to_mul_equiv.op},
  inv_fun   := λ f, { ..add_equiv.mul_op.symm f.to_add_equiv, ..mul_equiv.op.symm f.to_mul_equiv },
  left_inv  := λ f, by { ext, refl },
  right_inv := λ f, by { ext, refl } }

/-- The 'unopposite' of a ring iso `αᵐᵒᵖ ≃+* βᵐᵒᵖ`. Inverse to `ring_equiv.op`. -/
@[simp] protected def unop {α β} [has_add α] [has_mul α] [has_add β] [has_mul β] :
  (αᵐᵒᵖ ≃+* βᵐᵒᵖ) ≃ (α ≃+* β) := ring_equiv.op.symm

section non_unital_comm_semiring

variables (R) [non_unital_comm_semiring R]

/-- A non-unital commutative ring is isomorphic to its opposite. -/
def to_opposite : R ≃+* Rᵐᵒᵖ :=
{ map_add' := λ x y, rfl,
  map_mul' := λ x y, mul_comm (op y) (op x),
  .. mul_opposite.op_equiv }

@[simp]
lemma to_opposite_apply (r : R) : to_opposite R r = op r := rfl

@[simp]
lemma to_opposite_symm_apply (r : Rᵐᵒᵖ) : (to_opposite R).symm r = unop r := rfl

end non_unital_comm_semiring

end opposite

section non_unital_semiring

variables [non_unital_non_assoc_semiring R] [non_unital_non_assoc_semiring S]
  (f : R ≃+* S) (x y : R)

/-- A ring isomorphism sends zero to zero. -/
protected lemma map_zero : f 0 = 0 := map_zero f

variable {x}

protected lemma map_eq_zero_iff : f x = 0 ↔ x = 0 := add_equiv_class.map_eq_zero_iff f

lemma map_ne_zero_iff : f x ≠ 0 ↔ x ≠ 0 := add_equiv_class.map_ne_zero_iff f

/-- Produce a ring isomorphism from a bijective ring homomorphism. -/
noncomputable def of_bijective [non_unital_ring_hom_class F R S] (f : F)
  (hf : function.bijective f) : R ≃+* S :=
{ map_mul' := map_mul f,
  map_add' := map_add f,
  .. equiv.of_bijective f hf,}

@[simp] lemma coe_of_bijective [non_unital_ring_hom_class F R S] (f : F)
  (hf : function.bijective f) : (of_bijective f hf : R → S) = f := rfl

lemma of_bijective_apply [non_unital_ring_hom_class F R S] (f : F)
  (hf : function.bijective f) (x : R) : of_bijective f hf x = f x := rfl

/-- A family of ring isomorphisms `Π j, (R j ≃+* S j)` generates a
ring isomorphisms between `Π j, R j` and `Π j, S j`.

This is the `ring_equiv` version of `equiv.Pi_congr_right`, and the dependent version of
`ring_equiv.arrow_congr`.
-/
@[simps apply]
def Pi_congr_right {ι : Type*} {R S : ι → Type*}
  [Π i, non_unital_non_assoc_semiring (R i)] [Π i, non_unital_non_assoc_semiring (S i)]
  (e : Π i, R i ≃+* S i) : (Π i, R i) ≃+* Π i, S i :=
{ to_fun := λ x j, e j (x j),
  inv_fun := λ x j, (e j).symm (x j),
  .. @mul_equiv.Pi_congr_right ι R S _ _ (λ i, (e i).to_mul_equiv),
  .. @add_equiv.Pi_congr_right ι R S _ _ (λ i, (e i).to_add_equiv) }

@[simp]
lemma Pi_congr_right_refl {ι : Type*} {R : ι → Type*} [Π i, non_unital_non_assoc_semiring (R i)] :
  Pi_congr_right (λ i, ring_equiv.refl (R i)) = ring_equiv.refl _ := rfl

@[simp]
lemma Pi_congr_right_symm {ι : Type*} {R S : ι → Type*}
  [Π i, non_unital_non_assoc_semiring (R i)] [Π i, non_unital_non_assoc_semiring (S i)]
  (e : Π i, R i ≃+* S i) : (Pi_congr_right e).symm = (Pi_congr_right $ λ i, (e i).symm) := rfl

@[simp]
lemma Pi_congr_right_trans {ι : Type*} {R S T : ι → Type*}
  [Π i, non_unital_non_assoc_semiring (R i)] [Π i, non_unital_non_assoc_semiring (S i)]
  [Π i, non_unital_non_assoc_semiring (T i)]
  (e : Π i, R i ≃+* S i) (f : Π i, S i ≃+* T i) :
  (Pi_congr_right e).trans (Pi_congr_right f) = (Pi_congr_right $ λ i, (e i).trans (f i)) := rfl

end non_unital_semiring

section semiring

variables [non_assoc_semiring R] [non_assoc_semiring S] (f : R ≃+* S) (x y : R)

/-- A ring isomorphism sends one to one. -/
protected lemma map_one : f 1 = 1 := map_one f

variable {x}

protected lemma map_eq_one_iff : f x = 1 ↔ x = 1 := mul_equiv_class.map_eq_one_iff f

lemma map_ne_one_iff : f x ≠ 1 ↔ x ≠ 1 := mul_equiv_class.map_ne_one_iff f

lemma coe_monoid_hom_refl : (ring_equiv.refl R : R →* R) = monoid_hom.id R := rfl
@[simp] lemma coe_add_monoid_hom_refl : (ring_equiv.refl R : R →+ R) = add_monoid_hom.id R := rfl
/-! `ring_equiv.coe_mul_equiv_refl` and `ring_equiv.coe_add_equiv_refl` are proved above
in higher generality -/
@[simp] lemma coe_ring_hom_refl : (ring_equiv.refl R : R →* R) = ring_hom.id R := rfl

@[simp] lemma coe_monoid_hom_trans [non_assoc_semiring S'] (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
  (e₁.trans e₂ : R →* S') = (e₂ : S →* S').comp ↑e₁ := rfl
@[simp] lemma coe_add_monoid_hom_trans [non_assoc_semiring S'] (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
  (e₁.trans e₂ : R →+ S') = (e₂ : S →+ S').comp ↑e₁ := rfl
/-! `ring_equiv.coe_mul_equiv_trans` and `ring_equiv.coe_add_equiv_trans` are proved above
in higher generality -/
@[simp] lemma coe_ring_hom_trans [non_assoc_semiring S'] (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
  (e₁.trans e₂ : R →+* S') = (e₂ : S →+* S').comp ↑e₁ := rfl

@[simp] lemma comp_symm (e : R ≃+* S) :
  (e : R →+* S).comp (e.symm : S →+* R) = ring_hom.id S :=
ring_hom.ext e.apply_symm_apply

@[simp] lemma symm_comp (e : R ≃+* S) :
  (e.symm : S →+* R).comp (e : R →+* S) = ring_hom.id R :=
ring_hom.ext e.symm_apply_apply

end semiring

section non_unital_ring

variables [non_unital_non_assoc_ring R] [non_unital_non_assoc_ring S] (f : R ≃+* S) (x y : R)

protected lemma map_neg : f (-x) = -f x := map_neg f x

protected lemma map_sub : f (x - y) = f x - f y := map_sub f x y

end non_unital_ring

section ring

variables [non_assoc_ring R] [non_assoc_ring S] (f : R ≃+* S) (x y : R)

@[simp] lemma map_neg_one : f (-1) = -1 := f.map_one ▸ f.map_neg 1

end ring

section non_unital_semiring_hom

variables [non_unital_non_assoc_semiring R] [non_unital_non_assoc_semiring S]
  [non_unital_non_assoc_semiring S']

/-- Reinterpret a ring equivalence as a non-unital ring homomorphism. -/
def to_non_unital_ring_hom (e : R ≃+* S) : R →ₙ+* S :=
{ .. e.to_mul_equiv.to_mul_hom, .. e.to_add_equiv.to_add_monoid_hom }

lemma to_non_unital_ring_hom_injective :
  function.injective (to_non_unital_ring_hom : (R ≃+* S) → R →ₙ+* S) :=
λ f g h, ring_equiv.ext (non_unital_ring_hom.ext_iff.1 h)

/- The instance priority is lowered here so that in the case when `R` and `S` are both unital, Lean
will first find and use `ring_equiv.has_coe_to_ring_hom`. -/
@[priority 900]
instance has_coe_to_non_unital_ring_hom : has_coe (R ≃+* S) (R →ₙ+* S) :=
⟨ring_equiv.to_non_unital_ring_hom⟩

lemma to_non_unital_ring_hom_eq_coe (f : R ≃+* S) : f.to_non_unital_ring_hom = ↑f := rfl

@[simp, norm_cast] lemma coe_to_non_unital_ring_hom (f : R ≃+* S) : ⇑(f : R →ₙ+* S) = f := rfl

lemma coe_non_unital_ring_hom_inj_iff {R S : Type*}
  [non_unital_non_assoc_semiring R] [non_unital_non_assoc_semiring S]
  (f g : R ≃+* S) :
  f = g ↔ (f : R →ₙ+* S) = g :=
⟨congr_arg _, λ h, ext $ non_unital_ring_hom.ext_iff.mp h⟩

@[simp]
lemma to_non_unital_ring_hom_refl :
  (ring_equiv.refl R).to_non_unital_ring_hom = non_unital_ring_hom.id R := rfl

@[simp]
lemma to_non_unital_ring_hom_apply_symm_to_non_unital_ring_hom_apply (e : R ≃+* S) :
  ∀ (y : S), e.to_non_unital_ring_hom (e.symm.to_non_unital_ring_hom y) = y :=
e.to_equiv.apply_symm_apply

@[simp]
lemma symm_to_non_unital_ring_hom_apply_to_non_unital_ring_hom_apply (e : R ≃+* S) :
  ∀ (x : R), e.symm.to_non_unital_ring_hom (e.to_non_unital_ring_hom x) = x :=
equiv.symm_apply_apply (e.to_equiv)

@[simp]
lemma to_non_unital_ring_hom_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
  (e₁.trans e₂).to_non_unital_ring_hom = e₂.to_non_unital_ring_hom.comp e₁.to_non_unital_ring_hom :=
rfl

@[simp]
lemma to_non_unital_ring_hom_comp_symm_to_non_unital_ring_hom (e : R ≃+* S) :
  e.to_non_unital_ring_hom.comp e.symm.to_non_unital_ring_hom = non_unital_ring_hom.id _ :=
by { ext, simp }

@[simp]
lemma symm_to_non_unital_ring_hom_comp_to_non_unital_ring_hom (e : R ≃+* S) :
  e.symm.to_non_unital_ring_hom.comp e.to_non_unital_ring_hom = non_unital_ring_hom.id _ :=
by { ext, simp }
end non_unital_semiring_hom

section semiring_hom

variables [non_assoc_semiring R] [non_assoc_semiring S] [non_assoc_semiring S']

/-- Reinterpret a ring equivalence as a ring homomorphism. -/
def to_ring_hom (e : R ≃+* S) : R →+* S :=
{ .. e.to_mul_equiv.to_monoid_hom, .. e.to_add_equiv.to_add_monoid_hom }

lemma to_ring_hom_injective : function.injective (to_ring_hom : (R ≃+* S) → R →+* S) :=
λ f g h, ring_equiv.ext (ring_hom.ext_iff.1 h)

instance has_coe_to_ring_hom : has_coe (R ≃+* S) (R →+* S) := ⟨ring_equiv.to_ring_hom⟩

lemma to_ring_hom_eq_coe (f : R ≃+* S) : f.to_ring_hom = ↑f := rfl

@[simp, norm_cast] lemma coe_to_ring_hom (f : R ≃+* S) : ⇑(f : R →+* S) = f := rfl

lemma coe_ring_hom_inj_iff {R S : Type*} [non_assoc_semiring R] [non_assoc_semiring S]
  (f g : R ≃+* S) :
  f = g ↔ (f : R →+* S) = g :=
⟨congr_arg _, λ h, ext $ ring_hom.ext_iff.mp h⟩

/-- The two paths coercion can take to a `non_unital_ring_hom` are equivalent -/
@[simp, norm_cast] lemma to_non_unital_ring_hom_commutes (f : R ≃+* S) :
  ((f : R →+* S) : R →ₙ+* S) = (f : R →ₙ+* S) :=
rfl

/-- Reinterpret a ring equivalence as a monoid homomorphism. -/
abbreviation to_monoid_hom (e : R ≃+* S) : R →* S := e.to_ring_hom.to_monoid_hom

/-- Reinterpret a ring equivalence as an `add_monoid` homomorphism. -/
abbreviation to_add_monoid_hom (e : R ≃+* S) : R →+ S := e.to_ring_hom.to_add_monoid_hom

/-- The two paths coercion can take to an `add_monoid_hom` are equivalent -/
lemma to_add_monoid_hom_commutes (f : R ≃+* S) :
  (f : R →+* S).to_add_monoid_hom = (f : R ≃+ S).to_add_monoid_hom :=
rfl

/-- The two paths coercion can take to an `monoid_hom` are equivalent -/
lemma to_monoid_hom_commutes (f : R ≃+* S) :
  (f : R →+* S).to_monoid_hom = (f : R ≃* S).to_monoid_hom :=
rfl

/-- The two paths coercion can take to an `equiv` are equivalent -/
lemma to_equiv_commutes (f : R ≃+* S) :
  (f : R ≃+ S).to_equiv = (f : R ≃* S).to_equiv :=
rfl

@[simp]
lemma to_ring_hom_refl : (ring_equiv.refl R).to_ring_hom = ring_hom.id R := rfl

@[simp]
lemma to_monoid_hom_refl : (ring_equiv.refl R).to_monoid_hom = monoid_hom.id R := rfl

@[simp]
lemma to_add_monoid_hom_refl : (ring_equiv.refl R).to_add_monoid_hom = add_monoid_hom.id R := rfl

@[simp]
lemma to_ring_hom_apply_symm_to_ring_hom_apply (e : R ≃+* S) :
  ∀ (y : S), e.to_ring_hom (e.symm.to_ring_hom y) = y :=
e.to_equiv.apply_symm_apply

@[simp]
lemma symm_to_ring_hom_apply_to_ring_hom_apply (e : R ≃+* S) :
  ∀ (x : R), e.symm.to_ring_hom (e.to_ring_hom x) = x :=
equiv.symm_apply_apply (e.to_equiv)

@[simp]
lemma to_ring_hom_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
  (e₁.trans e₂).to_ring_hom = e₂.to_ring_hom.comp e₁.to_ring_hom := rfl

@[simp]
lemma to_ring_hom_comp_symm_to_ring_hom (e : R ≃+* S) :
  e.to_ring_hom.comp e.symm.to_ring_hom = ring_hom.id _ :=
by { ext, simp }

@[simp]
lemma symm_to_ring_hom_comp_to_ring_hom (e : R ≃+* S) :
  e.symm.to_ring_hom.comp e.to_ring_hom = ring_hom.id _ :=
by { ext, simp }

/--
Construct an equivalence of rings from homomorphisms in both directions, which are inverses.
-/
@[simps]
def of_hom_inv' {R S F G : Type*} [non_unital_non_assoc_semiring R]
  [non_unital_non_assoc_semiring S] [non_unital_ring_hom_class F R S]
  [non_unital_ring_hom_class G S R] (hom : F) (inv : G)
  (hom_inv_id : (inv : S →ₙ+* R).comp (hom : R →ₙ+* S) = non_unital_ring_hom.id R)
  (inv_hom_id : (hom : R →ₙ+* S).comp (inv : S →ₙ+* R) = non_unital_ring_hom.id S) :
  R ≃+* S :=
{ to_fun := hom,
  inv_fun := inv,
  left_inv := fun_like.congr_fun hom_inv_id,
  right_inv := fun_like.congr_fun inv_hom_id,
  map_mul' := map_mul hom,
  map_add' := map_add hom, }

/--
Construct an equivalence of rings from unital homomorphisms in both directions, which are inverses.
-/
@[simps]
def of_hom_inv {R S F G : Type*} [non_assoc_semiring R] [non_assoc_semiring S]
  [ring_hom_class F R S] [ring_hom_class G S R] (hom : F) (inv : G)
  (hom_inv_id : (inv : S →+* R).comp (hom : R →+* S) = ring_hom.id R)
  (inv_hom_id : (hom : R →+* S).comp (inv : S →+* R) = ring_hom.id S) :
  R ≃+* S :=
{ to_fun := hom,
  inv_fun := inv,
  left_inv := fun_like.congr_fun hom_inv_id,
  right_inv := fun_like.congr_fun inv_hom_id,
  map_mul' := map_mul hom,
  map_add' := map_add hom, }

end semiring_hom

section group_power

variables [semiring R] [semiring S]

protected lemma map_pow (f : R ≃+* S) (a) : ∀ n : ℕ, f (a ^ n) = (f a) ^ n := map_pow f a

end group_power

end ring_equiv

namespace mul_equiv

/-- Gives a `ring_equiv` from an element of a `mul_equiv_class` preserving addition.-/
def to_ring_equiv {R S F : Type*} [has_add R] [has_add S] [has_mul R] [has_mul S]
  [mul_equiv_class F R S] (f : F) (H : ∀ x y : R, f (x + y) = f x + f y) : R ≃+* S :=
{ ..(f : R ≃* S).to_equiv, ..(f : R ≃* S), ..add_equiv.mk' (f : R ≃* S).to_equiv H }

end mul_equiv

namespace add_equiv

/-- Gives a `ring_equiv` from an element of an `add_equiv_class` preserving addition.-/
def to_ring_equiv {R S F : Type*} [has_add R] [has_add S] [has_mul R] [has_mul S]
  [add_equiv_class F R S] (f : F) (H : ∀ x y : R, f (x * y) = f x * f y) : R ≃+* S :=
{ ..(f : R ≃+ S).to_equiv, ..(f : R ≃+ S), ..mul_equiv.mk' (f : R ≃+ S).to_equiv H }

end add_equiv

namespace ring_equiv

variables [has_add R] [has_add S] [has_mul R] [has_mul S]

@[simp] theorem self_trans_symm (e : R ≃+* S) : e.trans e.symm = ring_equiv.refl R := ext e.3
@[simp] theorem symm_trans_self (e : R ≃+* S) : e.symm.trans e = ring_equiv.refl S := ext e.4

/-- If two rings are isomorphic, and the second doesn't have zero divisors,
then so does the first. -/
protected lemma no_zero_divisors
  {A : Type*} (B : Type*) [ring A] [ring B] [no_zero_divisors B]
  (e : A ≃+* B) : no_zero_divisors A :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := λ x y hxy,
    have e x * e y = 0, by rw [← e.map_mul, hxy, e.map_zero],
    by simpa using eq_zero_or_eq_zero_of_mul_eq_zero this }

/-- If two rings are isomorphic, and the second is a domain, then so is the first. -/
protected lemma is_domain
  {A : Type*} (B : Type*) [ring A] [ring B] [is_domain B]
  (e : A ≃+* B) : is_domain A :=
begin
  haveI : nontrivial A := ⟨⟨e.symm 0, e.symm 1, e.symm.injective.ne zero_ne_one⟩⟩,
  haveI := e.no_zero_divisors B,
  exact no_zero_divisors.to_is_domain _
end

end ring_equiv

-- Guard against import creep
assert_not_exists fintype
