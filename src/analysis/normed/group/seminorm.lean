/-
Copyright (c) 2022 María Inés de Frutos-Fernández, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Yaël Dillies
-/
import data.real.nnreal

/-!
# Group seminorms

This file defines seminorms in a group. A group seminorm is a function to the reals which is
positive-semidefinite and subadditive.

## Main declarations

* `add_group_seminorm`: A function `f` from an additive group `G` to the reals that preserves zero,
  takes nonnegative values, is subadditive and such that `f (-x) = f x` for all `x`.
* `group_seminorm`: A function `f` from a group `G` to the reals that sends one to zero, takes
  nonnegative values, is submultiplicative and such that `f x⁻¹ = f x` for all `x`.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

seminorm
-/

set_option old_structure_cmd true

open set
open_locale nnreal

variables {ι R R' E F G : Type*}

/-- A seminorm on an additive group `G` is a function `f : G → ℝ` that preserves zero, is
subadditive and such that `f (-x) = f x` for all `x`. -/
structure add_group_seminorm (G : Type*) [add_group G] extends zero_hom G ℝ :=
(add_le' : ∀ r s, to_fun (r + s) ≤ to_fun r + to_fun s)
(neg' : ∀ r, to_fun (-r) = to_fun r)

/-- A seminorm on a group `G` is a function `f : G → ℝ` that sends one to zero, is submultiplicative
and such that `f x⁻¹ = f x` for all `x`. -/
@[to_additive]
structure group_seminorm (G : Type*) [group G] :=
(to_fun : G → ℝ)
(map_one' : to_fun 1 = 0)
(mul_le' : ∀ x y, to_fun (x * y) ≤ to_fun x + to_fun y)
(inv' : ∀ x, to_fun x⁻¹ = to_fun x)

attribute [nolint doc_blame] add_group_seminorm.to_zero_hom

namespace group_seminorm
section group
variables [group E] [group F] [group G]

@[to_additive] instance fun_like : fun_like (group_seminorm E) E (λ _, ℝ) :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
@[to_additive "Helper instance for when there's too many metavariables to apply
`fun_like.has_coe_to_fun`. "]
instance : has_coe_to_fun (group_seminorm E) (λ _, E → ℝ) := ⟨to_fun⟩

@[ext, to_additive] lemma ext {p q : group_seminorm E} : (∀ x, (p : E → ℝ) x = q x) → p = q :=
fun_like.ext p q

variables (p q : group_seminorm E) (x y : E) (r : ℝ)

@[simp, to_additive] protected lemma map_one : p 1 = 0 := p.map_one'
@[to_additive] protected lemma mul_le : p (x * y) ≤ p x + p y := p.mul_le' _ _
@[simp, to_additive] protected lemma inv : p x⁻¹ = p x := p.inv' _

@[to_additive] protected lemma div_le : p (x / y) ≤ p x + p y :=
by { rw [div_eq_mul_inv, ←p.inv y], exact p.mul_le _ _ }

@[to_additive] protected lemma nonneg : 0 ≤ p x :=
nonneg_of_mul_nonneg_right (by { rw [two_mul, ←p.map_one, ←div_self' x], apply p.div_le }) two_pos

@[to_additive] lemma div_rev : p (x / y) = p (y / x) := by rw [←inv_div, p.inv]

@[to_additive] instance : partial_order (group_seminorm E) :=
partial_order.lift _ fun_like.coe_injective

@[to_additive] lemma le_def : p ≤ q ↔ (p : E → ℝ) ≤ q := iff.rfl
@[to_additive] lemma lt_def : p < q ↔ (p : E → ℝ) < q := iff.rfl

variables {p q}

@[simp, to_additive] lemma coe_le_coe : (p : E → ℝ) ≤ q ↔ p ≤ q := iff.rfl
@[simp, to_additive] lemma coe_lt_coe : (p : E → ℝ) < q ↔ p < q := iff.rfl

variables (p q) (f : F →* E)

@[to_additive] instance : has_zero (group_seminorm E) :=
⟨{ to_fun := 0,
  map_one' := pi.zero_apply _,
  mul_le' := λ _ _, (zero_add _).ge,
  inv' := λ x, rfl}⟩

@[simp, to_additive] lemma coe_zero : ⇑(0 : group_seminorm E) = 0 := rfl
@[simp, to_additive] lemma zero_apply (x : E) : (0 : group_seminorm E) x = 0 := rfl

@[to_additive] instance : inhabited (group_seminorm E) := ⟨0⟩

@[to_additive] instance : has_add (group_seminorm E) :=
⟨λ p q,
  { to_fun := λ x, p x + q x,
    map_one' := by rw [p.map_one, q.map_one, zero_add],
    mul_le' := λ _ _, (add_le_add (p.mul_le _ _) $ q.mul_le _ _).trans_eq $
      add_add_add_comm _ _ _ _,
    inv' := λ x, by rw [p.inv, q.inv] }⟩

@[simp, to_additive] lemma coe_add : ⇑(p + q) = p + q := rfl
@[simp, to_additive] lemma add_apply (x : E) : (p + q) x = p x + q x := rfl

-- TODO: define `has_Sup` too, from the skeleton at
-- https://github.com/leanprover-community/mathlib/pull/11329#issuecomment-1008915345
@[to_additive] noncomputable instance : has_sup (group_seminorm E) :=
⟨λ p q,
  { to_fun := p ⊔ q,
    map_one' := by rw [pi.sup_apply, ←p.map_one, sup_eq_left, p.map_one, q.map_one],
    mul_le' := λ x y, sup_le
      ((p.mul_le x y).trans $ add_le_add le_sup_left le_sup_left)
      ((q.mul_le x y).trans $ add_le_add le_sup_right le_sup_right),
    inv' := λ x, by rw [pi.sup_apply, pi.sup_apply, p.inv, q.inv] }⟩

@[simp, to_additive] lemma coe_sup : ⇑(p ⊔ q) = p ⊔ q := rfl
@[simp, to_additive] lemma sup_apply (x : E) : (p ⊔ q) x = p x ⊔ q x := rfl

@[to_additive] noncomputable instance : semilattice_sup (group_seminorm E) :=
fun_like.coe_injective.semilattice_sup _ coe_sup

/-- Composition of a group seminorm with a monoid homomorphism as a group seminorm. -/
@[to_additive "Composition of an additive group seminorm with an additive monoid homomorphism as an
additive group seminorm."]
def comp (p : group_seminorm E) (f : F →* E) : group_seminorm F :=
{ to_fun := λ x, p (f x),
  map_one' := by rw [f.map_one, p.map_one],
  mul_le' := λ _ _, (congr_arg p $ f.map_mul _ _).trans_le $ p.mul_le _ _,
  inv' := λ x, by rw [map_inv, p.inv] }

@[simp, to_additive] lemma coe_comp : ⇑(p.comp f) = p ∘ f := rfl
@[simp, to_additive] lemma comp_apply (x : F) : (p.comp f) x = p (f x) := rfl
@[simp, to_additive] lemma comp_id : p.comp (monoid_hom.id _) = p := ext $ λ _, rfl
@[simp, to_additive] lemma comp_zero : p.comp (1 : F →* E) = 0 := ext $ λ _, p.map_one
@[simp, to_additive] lemma zero_comp : (0 : group_seminorm E).comp f = 0 := ext $ λ _, rfl

@[to_additive] lemma comp_assoc (g : F →* E) (f : G →* F) : p.comp (g.comp f) = (p.comp g).comp f :=
ext $ λ _, rfl

@[to_additive] lemma add_comp (f : F →* E) : (p + q).comp f = p.comp f + q.comp f := ext $ λ _, rfl

variables {p q}

@[to_additive] lemma comp_mono (hp : p ≤ q) : p.comp f ≤ q.comp f := λ _, hp _

end group

section comm_group
variables [comm_group E] [comm_group F] (p q : group_seminorm E) (x y : E)

/-- The direct path from `1` to `y` is shorter than the path with `x` "inserted" in between. -/
@[to_additive "The direct path from `0` to `y` is shorter than the path with `x` \"inserted\" in
between."]
lemma le_insert : p y ≤ p x + p (x / y) := (p.div_le _ _).trans_eq' $ by rw div_div_cancel

/-- The direct path from `1` to `x` is shorter than the path with `y` "inserted" in between. -/
@[to_additive "The direct path from `0` to `x` is shorter than the path with `y` \"inserted\" in
between."]
lemma le_insert' : p x ≤ p y + p (x / y) := by { rw div_rev, exact le_insert _ _ _ }

@[to_additive] lemma comp_mul_le (f g : F →* E) : p.comp (f * g) ≤ p.comp f + p.comp g :=
λ _, p.mul_le _ _

@[to_additive] private lemma mul_bdd_below_range_add {p q : group_seminorm E} {x : E} :
  bdd_below (range $ λ y, p y + q (x / y)) :=
⟨0, by { rintro _ ⟨x, rfl⟩, exact add_nonneg (p.nonneg _) (q.nonneg _) }⟩

@[to_additive] noncomputable instance : has_inf (group_seminorm E) :=
⟨λ p q,
  { to_fun := λ x, ⨅ y, p y + q (x / y),
    map_one' := cinfi_eq_of_forall_ge_of_forall_gt_exists_lt
        (λ x, add_nonneg (p.nonneg _) (q.nonneg _))
        (λ r hr, ⟨1, by rwa [div_one, p.map_one, q.map_one, add_zero]⟩),
    mul_le' := λ x y, le_cinfi_add_cinfi $ λ u v, begin
      refine cinfi_le_of_le mul_bdd_below_range_add (u * v) _,
      rw [mul_div_mul_comm, add_add_add_comm],
      exact add_le_add (p.mul_le _ _) (q.mul_le _ _),
    end,
    inv' := λ x, (inv_surjective.infi_comp _).symm.trans $ by simp_rw [p.inv, ←inv_div', q.inv] }⟩

@[simp, to_additive] lemma inf_apply : (p ⊓ q) x = ⨅ y, p y + q (x / y) := rfl

@[to_additive] noncomputable instance : lattice (group_seminorm E) :=
{ inf := (⊓),
  inf_le_left := λ p q x, cinfi_le_of_le mul_bdd_below_range_add x $
    by rw [div_self', q.map_one, add_zero],
  inf_le_right := λ p q x, cinfi_le_of_le mul_bdd_below_range_add (1 : E) $
    by simp only [div_one, p.map_one, zero_add],
  le_inf := λ a b c hb hc x, le_cinfi $ λ u, (a.le_insert' _ _).trans $ add_le_add (hb _) (hc _),
  ..group_seminorm.semilattice_sup }

end comm_group
end group_seminorm

namespace add_group_seminorm
variables [add_group E] (p : add_group_seminorm E) (x y : E) (r : ℝ)

instance zero_hom_class : zero_hom_class (add_group_seminorm E) E ℝ :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_zero := λ f, f.map_zero' }

/- TODO: All the following ought to be automated using `to_additive`. The problem is that it doesn't
see that `has_smul R ℝ` should be fixed because `ℝ` is fixed. -/

variables [has_smul R ℝ] [has_smul R ℝ≥0] [is_scalar_tower R ℝ≥0 ℝ]

/-- Any action on `ℝ` which factors through `ℝ≥0` applies to an `add_group_seminorm`. -/
instance : has_smul R (add_group_seminorm E) :=
⟨λ r p,
  { to_fun := λ x, r • p x,
    map_zero' := by simp only [←smul_one_smul ℝ≥0 r (_ : ℝ), nnreal.smul_def, smul_eq_mul,
      p.map_zero, mul_zero],
    add_le' := λ _ _, begin
      simp only [←smul_one_smul ℝ≥0 r (_ : ℝ), nnreal.smul_def, smul_eq_mul],
      exact (mul_le_mul_of_nonneg_left (p.add_le _ _) (nnreal.coe_nonneg _)).trans_eq
        (mul_add _ _ _),
    end,
    neg' := λ x, by rw p.neg }⟩

@[simp] lemma coe_smul (r : R) (p : add_group_seminorm E) : ⇑(r • p) = r • p := rfl
@[simp] lemma smul_apply (r : R) (p : add_group_seminorm E) (x : E) : (r • p) x = r • p x := rfl

instance [has_smul R' ℝ] [has_smul R' ℝ≥0] [is_scalar_tower R' ℝ≥0 ℝ]
  [has_smul R R'] [is_scalar_tower R R' ℝ] :
  is_scalar_tower R R' (add_group_seminorm E) :=
⟨λ r a p, ext $ λ x, smul_assoc r a (p x)⟩

lemma smul_sup (r : R) (p q : add_group_seminorm E) : r • (p ⊔ q) = r • p ⊔ r • q :=
have real.smul_max : ∀ x y : ℝ, r • max x y = max (r • x) (r • y),
from λ x y, by simpa only [←smul_eq_mul, ←nnreal.smul_def, smul_one_smul ℝ≥0 r (_ : ℝ)]
                     using mul_max_of_nonneg x y (r • 1 : ℝ≥0).prop,
ext $ λ x, real.smul_max _ _

end add_group_seminorm

namespace group_seminorm
variables [group E] [has_smul R ℝ] [has_smul R ℝ≥0] [is_scalar_tower R ℝ≥0 ℝ]

/-- Any action on `ℝ` which factors through `ℝ≥0` applies to an `add_group_seminorm`. -/
@[to_additive add_group_seminorm.has_smul] instance : has_smul R (group_seminorm E) :=
⟨λ r p,
  { to_fun := λ x, r • p x,
    map_one' := by simp only [←smul_one_smul ℝ≥0 r (_ : ℝ), nnreal.smul_def, smul_eq_mul,
      p.map_one, mul_zero],
    mul_le' := λ _ _, begin
      simp only [←smul_one_smul ℝ≥0 r (_ : ℝ), nnreal.smul_def, smul_eq_mul],
      exact (mul_le_mul_of_nonneg_left (p.mul_le _ _) $ nnreal.coe_nonneg _).trans_eq
        (mul_add _ _ _),
    end,
    inv' := λ x, by rw p.inv }⟩

@[to_additive add_group_seminorm.is_scalar_tower]
instance [has_smul R' ℝ] [has_smul R' ℝ≥0] [is_scalar_tower R' ℝ≥0 ℝ] [has_smul R R']
  [is_scalar_tower R R' ℝ] : is_scalar_tower R R' (group_seminorm E) :=
⟨λ r a p, ext $ λ x, smul_assoc r a $ p x⟩

@[simp, to_additive add_group_seminorm.coe_smul]
lemma coe_smul (r : R) (p : group_seminorm E) : ⇑(r • p) = r • p := rfl

@[simp, to_additive add_group_seminorm.smul_apply]
lemma smul_apply (r : R) (p : group_seminorm E) (x : E) : (r • p) x = r • p x := rfl

@[to_additive add_group_seminorm.smul_sup]
lemma smul_sup (r : R) (p q : group_seminorm E) : r • (p ⊔ q) = r • p ⊔ r • q :=
have real.smul_max : ∀ x y : ℝ, r • max x y = max (r • x) (r • y),
from λ x y, by simpa only [←smul_eq_mul, ←nnreal.smul_def, smul_one_smul ℝ≥0 r (_ : ℝ)]
                     using mul_max_of_nonneg x y (r • 1 : ℝ≥0).prop,
ext $ λ x, real.smul_max _ _

end group_seminorm
