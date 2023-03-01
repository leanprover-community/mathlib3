/-
Copyright (c) 2022 María Inés de Frutos-Fernández, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Yaël Dillies
-/
import tactic.positivity
import data.real.nnreal

/-!
# Group seminorms

This file defines norms and seminorms in a group. A group seminorm is a function to the reals which
is positive-semidefinite and subadditive. A norm further only maps zero to zero.

## Main declarations

* `add_group_seminorm`: A function `f` from an additive group `G` to the reals that preserves zero,
  takes nonnegative values, is subadditive and such that `f (-x) = f x` for all `x`.
* `group_seminorm`: A function `f` from a group `G` to the reals that sends one to zero, takes
  nonnegative values, is submultiplicative and such that `f x⁻¹ = f x` for all `x`.
* `add_group_norm`: A seminorm `f` such that `f x = 0 → x = 0` for all `x`.
* `group_norm`: A seminorm `f` such that `f x = 0 → x = 1` for all `x`.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

norm, seminorm
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

/-- A norm on an additive group `G` is a function `f : G → ℝ` that preserves zero, is subadditive
and such that `f (-x) = f x` and `f x = 0 → x = 0` for all `x`. -/
@[protect_proj]
structure add_group_norm (G : Type*) [add_group G] extends add_group_seminorm G :=
(eq_zero_of_map_eq_zero' : ∀ x, to_fun x = 0 → x = 0)

/-- A seminorm on a group `G` is a function `f : G → ℝ` that sends one to zero, is submultiplicative
and such that `f x⁻¹ = f x` and `f x = 0 → x = 1` for all `x`. -/
@[protect_proj, to_additive]
structure group_norm (G : Type*) [group G] extends group_seminorm G :=
(eq_one_of_map_eq_zero' : ∀ x, to_fun x = 0 → x = 1)

attribute [nolint doc_blame] add_group_seminorm.to_zero_hom  add_group_norm.to_add_group_seminorm
  group_norm.to_group_seminorm

/-- `add_group_seminorm_class F α` states that `F` is a type of seminorms on the additive group `α`.

You should extend this class when you extend `add_group_seminorm`. -/
class add_group_seminorm_class (F : Type*) (α : out_param $ Type*) [add_group α]
  extends subadditive_hom_class F α ℝ :=
(map_zero (f : F) : f 0 = 0)
(map_neg_eq_map (f : F) (a : α) : f (-a) = f a)

/-- `group_seminorm_class F α` states that `F` is a type of seminorms on the group `α`.

You should extend this class when you extend `group_seminorm`. -/
@[to_additive]
class group_seminorm_class (F : Type*) (α : out_param $ Type*) [group α]
  extends mul_le_add_hom_class F α ℝ :=
(map_one_eq_zero (f : F) : f 1 = 0)
(map_inv_eq_map (f : F) (a : α) : f a⁻¹ = f a)

/-- `add_group_norm_class F α` states that `F` is a type of norms on the additive group `α`.

You should extend this class when you extend `add_group_norm`. -/
class add_group_norm_class (F : Type*) (α : out_param $ Type*) [add_group α]
  extends add_group_seminorm_class F α :=
(eq_zero_of_map_eq_zero (f : F) {a : α} : f a = 0 → a = 0)

/-- `group_norm_class F α` states that `F` is a type of norms on the group `α`.

You should extend this class when you extend `group_norm`. -/
@[to_additive]
class group_norm_class (F : Type*) (α : out_param $ Type*) [group α]
  extends group_seminorm_class F α :=
(eq_one_of_map_eq_zero (f : F) {a : α} : f a = 0 → a = 1)

export add_group_seminorm_class (map_neg_eq_map)
       group_seminorm_class     (map_one_eq_zero map_inv_eq_map)
       add_group_norm_class     (eq_zero_of_map_eq_zero)
       group_norm_class         (eq_one_of_map_eq_zero)

attribute [simp, to_additive map_zero] map_one_eq_zero
attribute [simp] map_neg_eq_map
attribute [simp, to_additive] map_inv_eq_map
attribute [to_additive] group_seminorm_class.to_mul_le_add_hom_class
attribute [to_additive] group_norm.to_group_seminorm
attribute [to_additive] group_norm_class.to_group_seminorm_class

@[priority 100] -- See note [lower instance priority]
instance add_group_seminorm_class.to_zero_hom_class [add_group E] [add_group_seminorm_class F E] :
  zero_hom_class F E ℝ :=
{ ..‹add_group_seminorm_class F E› }

section group_seminorm_class
variables [group E] [group_seminorm_class F E] (f : F) (x y : E)
include E

@[to_additive] lemma map_div_le_add : f (x / y) ≤ f x + f y :=
by { rw [div_eq_mul_inv, ←map_inv_eq_map f y], exact map_mul_le_add _ _ _ }

@[to_additive] lemma map_div_rev : f (x / y) = f (y / x) := by rw [←inv_div, map_inv_eq_map]

@[to_additive] lemma le_map_add_map_div' : f x ≤ f y + f (y / x) :=
by simpa only [add_comm, map_div_rev, div_mul_cancel'] using map_mul_le_add f (x / y) y

@[to_additive] lemma abs_sub_map_le_div : |f x - f y| ≤ f (x / y) :=
begin
  rw [abs_sub_le_iff, sub_le_iff_le_add', sub_le_iff_le_add'],
  exact ⟨le_map_add_map_div _ _ _, le_map_add_map_div' _ _ _⟩
end

end group_seminorm_class

@[to_additive, priority 100] -- See note [lower instance priority]
instance group_seminorm_class.to_nonneg_hom_class [group E] [group_seminorm_class F E] :
  nonneg_hom_class F E ℝ :=
{ map_nonneg := λ f a, nonneg_of_mul_nonneg_right
    (by { rw [two_mul, ←map_one_eq_zero f, ←div_self' a], exact map_div_le_add _ _ _ }) two_pos,
  ..‹group_seminorm_class F E› }

section group_norm_class
variables [group E] [group_norm_class F E] (f : F) {x : E}
include E

@[to_additive] lemma map_pos_of_ne_one (hx : x ≠ 1) : 0 < f x :=
(map_nonneg _ _).lt_of_ne $ λ h, hx $ eq_one_of_map_eq_zero _ h.symm

@[simp, to_additive] lemma map_eq_zero_iff_eq_one : f x = 0 ↔ x = 1 :=
⟨eq_one_of_map_eq_zero _, by { rintro rfl, exact map_one_eq_zero _ }⟩

@[to_additive] lemma map_ne_zero_iff_ne_one : f x ≠ 0 ↔ x ≠ 1 := (map_eq_zero_iff_eq_one _).not

end group_norm_class

/-! ### Seminorms -/

namespace group_seminorm
section group
variables [group E] [group F] [group G] {p q : group_seminorm E}

@[to_additive] instance group_seminorm_class : group_seminorm_class (group_seminorm E) E :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_one_eq_zero := λ f, f.map_one',
  map_mul_le_add := λ f, f.mul_le',
  map_inv_eq_map := λ f, f.inv' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
@[to_additive "Helper instance for when there's too many metavariables to apply
`fun_like.has_coe_to_fun`. "]
instance : has_coe_to_fun (group_seminorm E) (λ _, E → ℝ) := ⟨to_fun⟩

@[simp, to_additive] lemma to_fun_eq_coe : p.to_fun = p := rfl

@[ext, to_additive] lemma ext : (∀ x, p x = q x) → p = q := fun_like.ext p q

@[to_additive] instance : partial_order (group_seminorm E) :=
partial_order.lift _ fun_like.coe_injective

@[to_additive] lemma le_def : p ≤ q ↔ (p : E → ℝ) ≤ q := iff.rfl
@[to_additive] lemma lt_def : p < q ↔ (p : E → ℝ) < q := iff.rfl

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
    map_one' := by rw [map_one_eq_zero p, map_one_eq_zero q, zero_add],
    mul_le' := λ _ _, (add_le_add (map_mul_le_add p _ _) $ map_mul_le_add q _ _).trans_eq $
      add_add_add_comm _ _ _ _,
    inv' := λ x, by rw [map_inv_eq_map p, map_inv_eq_map q] }⟩

@[simp, to_additive] lemma coe_add : ⇑(p + q) = p + q := rfl
@[simp, to_additive] lemma add_apply (x : E) : (p + q) x = p x + q x := rfl

-- TODO: define `has_Sup` too, from the skeleton at
-- https://github.com/leanprover-community/mathlib/pull/11329#issuecomment-1008915345
@[to_additive] instance : has_sup (group_seminorm E) :=
⟨λ p q,
  { to_fun := p ⊔ q,
    map_one' :=
      by rw [pi.sup_apply, ←map_one_eq_zero p, sup_eq_left, map_one_eq_zero p, map_one_eq_zero q],
    mul_le' := λ x y, sup_le
      ((map_mul_le_add p x y).trans $ add_le_add le_sup_left le_sup_left)
      ((map_mul_le_add q x y).trans $ add_le_add le_sup_right le_sup_right),
    inv' := λ x, by rw [pi.sup_apply, pi.sup_apply, map_inv_eq_map p, map_inv_eq_map q] }⟩

@[simp, to_additive] lemma coe_sup : ⇑(p ⊔ q) = p ⊔ q := rfl
@[simp, to_additive] lemma sup_apply (x : E) : (p ⊔ q) x = p x ⊔ q x := rfl

@[to_additive] instance : semilattice_sup (group_seminorm E) :=
fun_like.coe_injective.semilattice_sup _ coe_sup

/-- Composition of a group seminorm with a monoid homomorphism as a group seminorm. -/
@[to_additive "Composition of an additive group seminorm with an additive monoid homomorphism as an
additive group seminorm."]
def comp (p : group_seminorm E) (f : F →* E) : group_seminorm F :=
{ to_fun := λ x, p (f x),
  map_one' := by rw [f.map_one, map_one_eq_zero p],
  mul_le' := λ _ _, (congr_arg p $ f.map_mul _ _).trans_le $ map_mul_le_add p _ _,
  inv' := λ x, by rw [map_inv, map_inv_eq_map p] }

@[simp, to_additive] lemma coe_comp : ⇑(p.comp f) = p ∘ f := rfl
@[simp, to_additive] lemma comp_apply (x : F) : (p.comp f) x = p (f x) := rfl
@[simp, to_additive] lemma comp_id : p.comp (monoid_hom.id _) = p := ext $ λ _, rfl
@[simp, to_additive] lemma comp_zero : p.comp (1 : F →* E) = 0 := ext $ λ _, map_one_eq_zero p
@[simp, to_additive] lemma zero_comp : (0 : group_seminorm E).comp f = 0 := ext $ λ _, rfl

@[to_additive] lemma comp_assoc (g : F →* E) (f : G →* F) : p.comp (g.comp f) = (p.comp g).comp f :=
ext $ λ _, rfl

@[to_additive] lemma add_comp (f : F →* E) : (p + q).comp f = p.comp f + q.comp f := ext $ λ _, rfl

variables {p q}

@[to_additive] lemma comp_mono (hp : p ≤ q) : p.comp f ≤ q.comp f := λ _, hp _

end group

section comm_group
variables [comm_group E] [comm_group F] (p q : group_seminorm E) (x y : E)

@[to_additive] lemma comp_mul_le (f g : F →* E) : p.comp (f * g) ≤ p.comp f + p.comp g :=
λ _, map_mul_le_add p _ _

@[to_additive] lemma mul_bdd_below_range_add {p q : group_seminorm E} {x : E} :
  bdd_below (range $ λ y, p y + q (x / y)) :=
⟨0, by { rintro _ ⟨x, rfl⟩, dsimp, positivity }⟩

@[to_additive] noncomputable instance : has_inf (group_seminorm E) :=
⟨λ p q,
  { to_fun := λ x, ⨅ y, p y + q (x / y),
    map_one' := cinfi_eq_of_forall_ge_of_forall_gt_exists_lt (λ x, by positivity)
        (λ r hr, ⟨1, by rwa [div_one, map_one_eq_zero p, map_one_eq_zero q, add_zero]⟩),
    mul_le' := λ x y, le_cinfi_add_cinfi $ λ u v, begin
      refine cinfi_le_of_le mul_bdd_below_range_add (u * v) _,
      rw [mul_div_mul_comm, add_add_add_comm],
      exact add_le_add (map_mul_le_add p _ _) (map_mul_le_add q _ _),
    end,
    inv' := λ x, (inv_surjective.infi_comp _).symm.trans $
      by simp_rw [map_inv_eq_map p, ←inv_div', map_inv_eq_map q] }⟩

@[simp, to_additive] lemma inf_apply : (p ⊓ q) x = ⨅ y, p y + q (x / y) := rfl

@[to_additive] noncomputable instance : lattice (group_seminorm E) :=
{ inf := (⊓),
  inf_le_left := λ p q x, cinfi_le_of_le mul_bdd_below_range_add x $
    by rw [div_self', map_one_eq_zero q, add_zero],
  inf_le_right := λ p q x, cinfi_le_of_le mul_bdd_below_range_add (1 : E) $
    by simp only [div_one, map_one_eq_zero p, zero_add],
  le_inf := λ a b c hb hc x, le_cinfi $ λ u, (le_map_add_map_div a _ _).trans $
    add_le_add (hb _) (hc _),
  ..group_seminorm.semilattice_sup }

end comm_group
end group_seminorm

/- TODO: All the following ought to be automated using `to_additive`. The problem is that it doesn't
see that `has_smul R ℝ` should be fixed because `ℝ` is fixed. -/

namespace add_group_seminorm
variables [add_group E] [has_smul R ℝ] [has_smul R ℝ≥0] [is_scalar_tower R ℝ≥0 ℝ]
  (p : add_group_seminorm E)

instance [decidable_eq E] : has_one (add_group_seminorm E) :=
⟨{ to_fun := λ x, if x = 0 then 0 else 1,
  map_zero' := if_pos rfl,
  add_le' := λ x y, begin
    by_cases hx : x = 0,
    { rw [if_pos hx, hx, zero_add, zero_add] },
    { rw if_neg hx,
      refine le_add_of_le_of_nonneg _ _; split_ifs; norm_num }
  end,
  neg' := λ x, by simp_rw neg_eq_zero }⟩

@[simp] lemma apply_one [decidable_eq E] (x : E) :
  (1 : add_group_seminorm E) x = if x = 0 then 0 else 1 := rfl

/-- Any action on `ℝ` which factors through `ℝ≥0` applies to an `add_group_seminorm`. -/
instance : has_smul R (add_group_seminorm E) :=
⟨λ r p,
  { to_fun := λ x, r • p x,
    map_zero' := by simp only [←smul_one_smul ℝ≥0 r (_ : ℝ), nnreal.smul_def, smul_eq_mul,
      map_zero, mul_zero],
    add_le' := λ _ _, begin
      simp only [←smul_one_smul ℝ≥0 r (_ : ℝ), nnreal.smul_def, smul_eq_mul],
      exact (mul_le_mul_of_nonneg_left (map_add_le_add _ _ _) $ nnreal.coe_nonneg _).trans_eq
        (mul_add _ _ _),
    end,
    neg' := λ x, by rw map_neg_eq_map }⟩

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

@[to_additive add_group_seminorm.has_one]
instance [decidable_eq E] : has_one (group_seminorm E) :=
⟨{ to_fun := λ x, if x = 1 then 0 else 1,
  map_one' := if_pos rfl,
  mul_le' := λ x y, begin
    by_cases hx : x = 1,
    { rw [if_pos hx, hx, one_mul, zero_add] },
    { rw if_neg hx,
      refine le_add_of_le_of_nonneg _ _; split_ifs; norm_num }
  end,
  inv' := λ x, by simp_rw inv_eq_one }⟩

@[simp, to_additive add_group_seminorm.apply_one] lemma apply_one [decidable_eq E] (x : E) :
  (1 : group_seminorm E) x = if x = 1 then 0 else 1 := rfl

/-- Any action on `ℝ` which factors through `ℝ≥0` applies to an `add_group_seminorm`. -/
@[to_additive add_group_seminorm.has_smul] instance : has_smul R (group_seminorm E) :=
⟨λ r p,
  { to_fun := λ x, r • p x,
    map_one' := by simp only [←smul_one_smul ℝ≥0 r (_ : ℝ), nnreal.smul_def, smul_eq_mul,
      map_one_eq_zero p, mul_zero],
    mul_le' := λ _ _, begin
      simp only [←smul_one_smul ℝ≥0 r (_ : ℝ), nnreal.smul_def, smul_eq_mul],
      exact (mul_le_mul_of_nonneg_left (map_mul_le_add p _ _) $ nnreal.coe_nonneg _).trans_eq
        (mul_add _ _ _),
    end,
    inv' := λ x, by rw map_inv_eq_map p }⟩

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

/-! ### Norms -/

namespace group_norm
section group
variables [group E] [group F] [group G] {p q : group_norm E}

@[to_additive] instance group_norm_class : group_norm_class (group_norm E) E :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_one_eq_zero := λ f, f.map_one',
  map_mul_le_add := λ f, f.mul_le',
  map_inv_eq_map := λ f, f.inv',
  eq_one_of_map_eq_zero := λ f, f.eq_one_of_map_eq_zero' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
@[to_additive "Helper instance for when there's too many metavariables to apply
`fun_like.has_coe_to_fun` directly. "]
instance : has_coe_to_fun (group_norm E) (λ _, E → ℝ) := fun_like.has_coe_to_fun

@[simp, to_additive] lemma to_fun_eq_coe : p.to_fun = p := rfl

@[ext, to_additive] lemma ext : (∀ x, p x = q x) → p = q := fun_like.ext p q

@[to_additive] instance : partial_order (group_norm E) :=
partial_order.lift _ fun_like.coe_injective

@[to_additive] lemma le_def : p ≤ q ↔ (p : E → ℝ) ≤ q := iff.rfl
@[to_additive] lemma lt_def : p < q ↔ (p : E → ℝ) < q := iff.rfl

@[simp, to_additive] lemma coe_le_coe : (p : E → ℝ) ≤ q ↔ p ≤ q := iff.rfl
@[simp, to_additive] lemma coe_lt_coe : (p : E → ℝ) < q ↔ p < q := iff.rfl

variables (p q) (f : F →* E)

@[to_additive] instance : has_add (group_norm E) :=
⟨λ p q, { eq_one_of_map_eq_zero' := λ x hx, of_not_not $ λ h,
            hx.not_gt $ add_pos (map_pos_of_ne_one p h) (map_pos_of_ne_one q h),
          ..p.to_group_seminorm + q.to_group_seminorm }⟩

@[simp, to_additive] lemma coe_add : ⇑(p + q) = p + q := rfl
@[simp, to_additive] lemma add_apply (x : E) : (p + q) x = p x + q x := rfl

-- TODO: define `has_Sup`
@[to_additive] instance : has_sup (group_norm E) :=
⟨λ p q,
  { eq_one_of_map_eq_zero' := λ x hx, of_not_not $ λ h, hx.not_gt $
      lt_sup_iff.2 $ or.inl $ map_pos_of_ne_one p h,
    ..p.to_group_seminorm ⊔ q.to_group_seminorm }⟩

@[simp, to_additive] lemma coe_sup : ⇑(p ⊔ q) = p ⊔ q := rfl
@[simp, to_additive] lemma sup_apply (x : E) : (p ⊔ q) x = p x ⊔ q x := rfl

@[to_additive] instance : semilattice_sup (group_norm E) :=
fun_like.coe_injective.semilattice_sup _ coe_sup

end group
end group_norm

namespace add_group_norm
variables [add_group E] [decidable_eq E]

instance : has_one (add_group_norm E) :=
⟨{ eq_zero_of_map_eq_zero' := λ x, zero_ne_one.ite_eq_left_iff.1,
  ..(1 : add_group_seminorm E) }⟩

@[simp] lemma apply_one (x : E) : (1 : add_group_norm E) x = if x = 0 then 0 else 1 := rfl

instance : inhabited (add_group_norm E) := ⟨1⟩

end add_group_norm

namespace group_norm
variables [group E] [decidable_eq E]

@[to_additive add_group_norm.has_one] instance : has_one (group_norm E) :=
⟨{ eq_one_of_map_eq_zero' := λ x, zero_ne_one.ite_eq_left_iff.1,
  ..(1 : group_seminorm E) }⟩

@[simp, to_additive add_group_norm.apply_one]
lemma apply_one (x : E) : (1 : group_norm E) x = if x = 1 then 0 else 1 := rfl

@[to_additive] instance : inhabited (group_norm E) := ⟨1⟩

end group_norm
