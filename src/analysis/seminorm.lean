/-
Copyright (c) 2019 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo, Yaël Dillies, Moritz Doll
-/
import data.real.pointwise
import analysis.convex.function
import analysis.locally_convex.basic
import analysis.normed.group.add_torsor

/-!
# Seminorms

This file defines seminorms.

A seminorm is a function to the reals which is positive-semidefinite, absolutely homogeneous, and
subadditive. They are closely related to convex sets and a topological vector space is locally
convex if and only if its topology is induced by a family of seminorms.

## Main declarations

For a module over a normed ring:
* `seminorm`: A function to the reals that is positive-semidefinite, absolutely homogeneous, and
  subadditive.
* `norm_seminorm 𝕜 E`: The norm on `E` as a seminorm.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

seminorm, locally convex, LCTVS
-/

set_option old_structure_cmd true

open normed_field set
open_locale big_operators nnreal pointwise topology

variables {R R' 𝕜 𝕜₂ 𝕜₃ 𝕝 E E₂ E₃ F G ι : Type*}

/-- A seminorm on a module over a normed ring is a function to the reals that is positive
semidefinite, positive homogeneous, and subadditive. -/
structure seminorm (𝕜 : Type*) (E : Type*) [semi_normed_ring 𝕜] [add_group E] [has_smul 𝕜 E]
  extends add_group_seminorm E :=
(smul' : ∀ (a : 𝕜) (x : E), to_fun (a • x) = ‖a‖ * to_fun x)

attribute [nolint doc_blame] seminorm.to_add_group_seminorm

/-- `seminorm_class F 𝕜 E` states that `F` is a type of seminorms on the `𝕜`-module E.

You should extend this class when you extend `seminorm`. -/
class seminorm_class (F : Type*) (𝕜 E : out_param $ Type*) [semi_normed_ring 𝕜] [add_group E]
  [has_smul 𝕜 E] extends add_group_seminorm_class F E ℝ :=
(map_smul_eq_mul (f : F) (a : 𝕜) (x : E) : f (a • x) = ‖a‖ * f x)

export seminorm_class (map_smul_eq_mul)

-- `𝕜` is an `out_param`, so this is a false positive.
attribute [nolint dangerous_instance] seminorm_class.to_add_group_seminorm_class

section of

/-- Alternative constructor for a `seminorm` on an `add_comm_group E` that is a module over a
`semi_norm_ring 𝕜`. -/
def seminorm.of [semi_normed_ring 𝕜] [add_comm_group E] [module 𝕜 E] (f : E → ℝ)
  (add_le : ∀ (x y : E), f (x + y) ≤ f x + f y)
  (smul : ∀ (a : 𝕜) (x : E), f (a • x) = ‖a‖ * f x) : seminorm 𝕜 E :=
{ to_fun    := f,
  map_zero' := by rw [←zero_smul 𝕜 (0 : E), smul, norm_zero, zero_mul],
  add_le'   := add_le,
  smul'     := smul,
  neg'      := λ x, by rw [←neg_one_smul 𝕜, smul, norm_neg, ← smul, one_smul] }

/-- Alternative constructor for a `seminorm` over a normed field `𝕜` that only assumes `f 0 = 0`
and an inequality for the scalar multiplication. -/
def seminorm.of_smul_le [normed_field 𝕜] [add_comm_group E] [module 𝕜 E] (f : E → ℝ)
  (map_zero : f 0 = 0) (add_le : ∀ x y, f (x + y) ≤ f x + f y)
  (smul_le : ∀ (r : 𝕜) x, f (r • x) ≤ ‖r‖ * f x) : seminorm 𝕜 E :=
seminorm.of f add_le
  (λ r x, begin
    refine le_antisymm (smul_le r x) _,
    by_cases r = 0,
    { simp [h, map_zero] },
    rw ←mul_le_mul_left (inv_pos.mpr (norm_pos_iff.mpr h)),
    rw inv_mul_cancel_left₀ (norm_ne_zero_iff.mpr h),
    specialize smul_le r⁻¹ (r • x),
    rw norm_inv at smul_le,
    convert smul_le,
    simp [h],
  end)

end of

namespace seminorm

section semi_normed_ring
variables [semi_normed_ring 𝕜]

section add_group
variables [add_group E]

section has_smul
variables [has_smul 𝕜 E]

instance seminorm_class : seminorm_class (seminorm 𝕜 E) 𝕜 E :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_zero := λ f, f.map_zero',
  map_add_le_add := λ f, f.add_le',
  map_neg_eq_map := λ f, f.neg',
  map_smul_eq_mul := λ f, f.smul' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
instance : has_coe_to_fun (seminorm 𝕜 E) (λ _, E → ℝ) := fun_like.has_coe_to_fun

@[ext] lemma ext {p q : seminorm 𝕜 E} (h : ∀ x, (p : E → ℝ) x = q x) : p = q := fun_like.ext p q h

instance : has_zero (seminorm 𝕜 E) :=
⟨{ smul' := λ _ _, (mul_zero _).symm,
  ..add_group_seminorm.has_zero.zero }⟩

@[simp] lemma coe_zero : ⇑(0 : seminorm 𝕜 E) = 0 := rfl

@[simp] lemma zero_apply (x : E) : (0 : seminorm 𝕜 E) x = 0 := rfl

instance : inhabited (seminorm 𝕜 E) := ⟨0⟩

variables (p : seminorm 𝕜 E) (c : 𝕜) (x y : E) (r : ℝ)

/-- Any action on `ℝ` which factors through `ℝ≥0` applies to a seminorm. -/
instance [has_smul R ℝ] [has_smul R ℝ≥0] [is_scalar_tower R ℝ≥0 ℝ] :
  has_smul R (seminorm 𝕜 E) :=
{ smul := λ r p,
  { to_fun  := λ x, r • p x,
    smul' := λ _ _, begin
      simp only [←smul_one_smul ℝ≥0 r (_ : ℝ), nnreal.smul_def, smul_eq_mul],
      rw [map_smul_eq_mul, mul_left_comm],
    end,
    ..(r • p.to_add_group_seminorm) }}

instance [has_smul R ℝ] [has_smul R ℝ≥0] [is_scalar_tower R ℝ≥0 ℝ]
  [has_smul R' ℝ] [has_smul R' ℝ≥0] [is_scalar_tower R' ℝ≥0 ℝ]
  [has_smul R R'] [is_scalar_tower R R' ℝ] :
  is_scalar_tower R R' (seminorm 𝕜 E) :=
{ smul_assoc := λ r a p, ext $ λ x, smul_assoc r a (p x) }

lemma coe_smul [has_smul R ℝ] [has_smul R ℝ≥0] [is_scalar_tower R ℝ≥0 ℝ]
  (r : R) (p : seminorm 𝕜 E) : ⇑(r • p) = r • p := rfl

@[simp] lemma smul_apply [has_smul R ℝ] [has_smul R ℝ≥0] [is_scalar_tower R ℝ≥0 ℝ]
  (r : R) (p : seminorm 𝕜 E) (x : E) : (r • p) x = r • p x := rfl

instance : has_add (seminorm 𝕜 E) :=
{ add := λ p q,
  { to_fun    := λ x, p x + q x,
    smul'     := λ a x, by simp only [map_smul_eq_mul, map_smul_eq_mul, mul_add],
    ..(p.to_add_group_seminorm + q.to_add_group_seminorm) }}

lemma coe_add (p q : seminorm 𝕜 E) : ⇑(p + q) = p + q := rfl

@[simp] lemma add_apply (p q : seminorm 𝕜 E) (x : E) : (p + q) x = p x + q x := rfl

instance : add_monoid (seminorm 𝕜 E) :=
fun_like.coe_injective.add_monoid _ rfl coe_add (λ p n, coe_smul n p)

instance : ordered_cancel_add_comm_monoid (seminorm 𝕜 E) :=
fun_like.coe_injective.ordered_cancel_add_comm_monoid _ rfl coe_add (λ p n, coe_smul n p)

instance [monoid R] [mul_action R ℝ] [has_smul R ℝ≥0] [is_scalar_tower R ℝ≥0 ℝ] :
  mul_action R (seminorm 𝕜 E) :=
fun_like.coe_injective.mul_action _ coe_smul

variables (𝕜 E)

/-- `coe_fn` as an `add_monoid_hom`. Helper definition for showing that `seminorm 𝕜 E` is
a module. -/
@[simps]
def coe_fn_add_monoid_hom : add_monoid_hom (seminorm 𝕜 E) (E → ℝ) := ⟨coe_fn, coe_zero, coe_add⟩

lemma coe_fn_add_monoid_hom_injective : function.injective (coe_fn_add_monoid_hom 𝕜 E) :=
show @function.injective (seminorm 𝕜 E) (E → ℝ) coe_fn, from fun_like.coe_injective

variables {𝕜 E}

instance [monoid R] [distrib_mul_action R ℝ] [has_smul R ℝ≥0] [is_scalar_tower R ℝ≥0 ℝ] :
  distrib_mul_action R (seminorm 𝕜 E) :=
(coe_fn_add_monoid_hom_injective 𝕜 E).distrib_mul_action _ coe_smul

instance [semiring R] [module R ℝ] [has_smul R ℝ≥0] [is_scalar_tower R ℝ≥0 ℝ] :
  module R (seminorm 𝕜 E) :=
(coe_fn_add_monoid_hom_injective 𝕜 E).module R _ coe_smul

instance : has_sup (seminorm 𝕜 E) :=
{ sup := λ p q,
  { to_fun  := p ⊔ q,
    smul' := λ x v, (congr_arg2 max (map_smul_eq_mul p x v) (map_smul_eq_mul q x v)).trans $
      (mul_max_of_nonneg _ _ $ norm_nonneg x).symm,
    ..(p.to_add_group_seminorm ⊔ q.to_add_group_seminorm) } }

@[simp] lemma coe_sup (p q : seminorm 𝕜 E) : ⇑(p ⊔ q) = p ⊔ q := rfl
lemma sup_apply (p q : seminorm 𝕜 E) (x : E) : (p ⊔ q) x = p x ⊔ q x := rfl

lemma smul_sup [has_smul R ℝ] [has_smul R ℝ≥0] [is_scalar_tower R ℝ≥0 ℝ]
  (r : R) (p q : seminorm 𝕜 E) :
  r • (p ⊔ q) = r • p ⊔ r • q :=
have real.smul_max : ∀ x y : ℝ, r • max x y = max (r • x) (r • y),
from λ x y, by simpa only [←smul_eq_mul, ←nnreal.smul_def, smul_one_smul ℝ≥0 r (_ : ℝ)]
                     using mul_max_of_nonneg x y (r • 1 : ℝ≥0).prop,
ext $ λ x, real.smul_max _ _

instance : partial_order (seminorm 𝕜 E) :=
  partial_order.lift _ fun_like.coe_injective

lemma le_def (p q : seminorm 𝕜 E) : p ≤ q ↔ (p : E → ℝ) ≤ q := iff.rfl
lemma lt_def (p q : seminorm 𝕜 E) : p < q ↔ (p : E → ℝ) < q := iff.rfl

instance : semilattice_sup (seminorm 𝕜 E) :=
function.injective.semilattice_sup _ fun_like.coe_injective coe_sup

end has_smul

end add_group

section module
variables [semi_normed_ring 𝕜₂] [semi_normed_ring 𝕜₃]
variables {σ₁₂ : 𝕜 →+* 𝕜₂} [ring_hom_isometric σ₁₂]
variables {σ₂₃ : 𝕜₂ →+* 𝕜₃} [ring_hom_isometric σ₂₃]
variables {σ₁₃ : 𝕜 →+* 𝕜₃} [ring_hom_isometric σ₁₃]
variables [add_comm_group E] [add_comm_group E₂] [add_comm_group E₃]
variables [add_comm_group F] [add_comm_group G]
variables [module 𝕜 E] [module 𝕜₂ E₂] [module 𝕜₃ E₃] [module 𝕜 F] [module 𝕜 G]
variables [has_smul R ℝ] [has_smul R ℝ≥0] [is_scalar_tower R ℝ≥0 ℝ]

/-- Composition of a seminorm with a linear map is a seminorm. -/
def comp (p : seminorm 𝕜₂ E₂) (f : E →ₛₗ[σ₁₂] E₂) : seminorm 𝕜 E :=
{ to_fun    := λ x, p (f x),
  smul'     := λ _ _, by rw [map_smulₛₗ, map_smul_eq_mul, ring_hom_isometric.is_iso],
  ..(p.to_add_group_seminorm.comp f.to_add_monoid_hom) }

lemma coe_comp (p : seminorm 𝕜₂ E₂) (f : E →ₛₗ[σ₁₂] E₂) : ⇑(p.comp f) = p ∘ f := rfl

@[simp] lemma comp_apply (p : seminorm 𝕜₂ E₂) (f : E →ₛₗ[σ₁₂] E₂) (x : E) :
  (p.comp f) x = p (f x) := rfl

@[simp] lemma comp_id (p : seminorm 𝕜 E) : p.comp linear_map.id = p :=
ext $ λ _, rfl

@[simp] lemma comp_zero (p : seminorm 𝕜₂ E₂) : p.comp (0 : E →ₛₗ[σ₁₂] E₂) = 0 :=
ext $ λ _, map_zero p

@[simp] lemma zero_comp (f : E →ₛₗ[σ₁₂] E₂) : (0 : seminorm 𝕜₂ E₂).comp f = 0 :=
ext $ λ _, rfl

lemma comp_comp [ring_hom_comp_triple σ₁₂ σ₂₃ σ₁₃] (p : seminorm 𝕜₃ E₃)
  (g : E₂ →ₛₗ[σ₂₃] E₃) (f : E →ₛₗ[σ₁₂] E₂) :
  p.comp (g.comp f) = (p.comp g).comp f :=
ext $ λ _, rfl

lemma add_comp (p q : seminorm 𝕜₂ E₂) (f : E →ₛₗ[σ₁₂] E₂) : (p + q).comp f = p.comp f + q.comp f :=
ext $ λ _, rfl

lemma comp_add_le (p : seminorm 𝕜₂ E₂) (f g : E →ₛₗ[σ₁₂] E₂) :
  p.comp (f + g) ≤ p.comp f + p.comp g :=
λ _, map_add_le_add p _ _

lemma smul_comp (p : seminorm 𝕜₂ E₂) (f : E →ₛₗ[σ₁₂] E₂) (c : R) :
  (c • p).comp f = c • (p.comp f) :=
ext $ λ _, rfl

lemma comp_mono {p q : seminorm 𝕜₂ E₂} (f : E →ₛₗ[σ₁₂] E₂) (hp : p ≤ q) :
  p.comp f ≤ q.comp f := λ _, hp _

/-- The composition as an `add_monoid_hom`. -/
@[simps] def pullback (f : E →ₛₗ[σ₁₂] E₂) : seminorm 𝕜₂ E₂ →+ seminorm 𝕜 E :=
⟨λ p, p.comp f, zero_comp f, λ p q, add_comp p q f⟩

instance : order_bot (seminorm 𝕜 E) := ⟨0, map_nonneg⟩

@[simp] lemma coe_bot : ⇑(⊥ : seminorm 𝕜 E) = 0 := rfl

lemma bot_eq_zero : (⊥ : seminorm 𝕜 E) = 0 := rfl

lemma smul_le_smul {p q : seminorm 𝕜 E} {a b : ℝ≥0} (hpq : p ≤ q) (hab : a ≤ b) :
  a • p ≤ b • q :=
begin
  simp_rw [le_def, pi.le_def, coe_smul],
  intros x,
  simp_rw [pi.smul_apply, nnreal.smul_def, smul_eq_mul],
  exact mul_le_mul hab (hpq x) (map_nonneg p x) (nnreal.coe_nonneg b),
end

lemma finset_sup_apply (p : ι → seminorm 𝕜 E) (s : finset ι) (x : E) :
  s.sup p x = ↑(s.sup (λ i, ⟨p i x, map_nonneg (p i) x⟩) : ℝ≥0) :=
begin
  induction s using finset.cons_induction_on with a s ha ih,
  { rw [finset.sup_empty, finset.sup_empty, coe_bot, _root_.bot_eq_zero, pi.zero_apply,
        nonneg.coe_zero] },
  { rw [finset.sup_cons, finset.sup_cons, coe_sup, sup_eq_max, pi.sup_apply, sup_eq_max,
        nnreal.coe_max, subtype.coe_mk, ih] }
end

lemma finset_sup_le_sum (p : ι → seminorm 𝕜 E) (s : finset ι) : s.sup p ≤ ∑ i in s, p i :=
begin
  classical,
  refine finset.sup_le_iff.mpr _,
  intros i hi,
  rw [finset.sum_eq_sum_diff_singleton_add hi, le_add_iff_nonneg_left],
  exact bot_le,
end

lemma finset_sup_apply_le {p : ι → seminorm 𝕜 E} {s : finset ι} {x : E} {a : ℝ} (ha : 0 ≤ a)
  (h : ∀ i, i ∈ s → p i x ≤ a) : s.sup p x ≤ a :=
begin
  lift a to ℝ≥0 using ha,
  rw [finset_sup_apply, nnreal.coe_le_coe],
  exact finset.sup_le h,
end

lemma finset_sup_apply_lt {p : ι → seminorm 𝕜 E} {s : finset ι} {x : E} {a : ℝ} (ha : 0 < a)
  (h : ∀ i, i ∈ s → p i x < a) : s.sup p x < a :=
begin
  lift a to ℝ≥0 using ha.le,
  rw [finset_sup_apply, nnreal.coe_lt_coe, finset.sup_lt_iff],
  { exact h },
  { exact nnreal.coe_pos.mpr ha },
end

lemma norm_sub_map_le_sub (p : seminorm 𝕜 E) (x y : E) : ‖p x - p y‖ ≤ p (x - y) :=
abs_sub_map_le_sub p x y

end module
end semi_normed_ring

section semi_normed_comm_ring
variables [semi_normed_ring 𝕜] [semi_normed_comm_ring 𝕜₂]
variables {σ₁₂ : 𝕜 →+* 𝕜₂} [ring_hom_isometric σ₁₂]
variables [add_comm_group E] [add_comm_group E₂] [module 𝕜 E] [module 𝕜₂ E₂]

lemma comp_smul (p : seminorm 𝕜₂ E₂) (f : E →ₛₗ[σ₁₂] E₂) (c : 𝕜₂) :
  p.comp (c • f) = ‖c‖₊ • p.comp f :=
ext $ λ _, by rw [comp_apply, smul_apply, linear_map.smul_apply, map_smul_eq_mul, nnreal.smul_def,
  coe_nnnorm, smul_eq_mul, comp_apply]

lemma comp_smul_apply (p : seminorm 𝕜₂ E₂) (f : E →ₛₗ[σ₁₂] E₂) (c : 𝕜₂) (x : E) :
  p.comp (c • f) x = ‖c‖ * p (f x) := map_smul_eq_mul p _ _

end semi_normed_comm_ring

section normed_field
variables [normed_field 𝕜] [add_comm_group E] [module 𝕜 E] {p q : seminorm 𝕜 E} {x : E}

/-- Auxiliary lemma to show that the infimum of seminorms is well-defined. -/
lemma bdd_below_range_add : bdd_below (range $ λ u, p u + q (x - u)) :=
⟨0, by { rintro _ ⟨x, rfl⟩, dsimp, positivity }⟩

noncomputable instance : has_inf (seminorm 𝕜 E) :=
{ inf := λ p q,
  { to_fun  := λ x, ⨅ u : E, p u + q (x-u),
    smul' :=
    begin
      intros a x,
      obtain rfl | ha := eq_or_ne a 0,
      { rw [norm_zero, zero_mul, zero_smul],
        refine cinfi_eq_of_forall_ge_of_forall_gt_exists_lt (λ i, by positivity)
          (λ x hx, ⟨0, by rwa [map_zero, sub_zero, map_zero, add_zero]⟩) },
      simp_rw [real.mul_infi_of_nonneg (norm_nonneg a), mul_add, ←map_smul_eq_mul p,
        ←map_smul_eq_mul q, smul_sub],
      refine function.surjective.infi_congr ((•) a⁻¹ : E → E) (λ u, ⟨a • u, inv_smul_smul₀ ha u⟩)
        (λ u, _),
      rw smul_inv_smul₀ ha
    end,
    ..(p.to_add_group_seminorm ⊓ q.to_add_group_seminorm) }}

@[simp] lemma inf_apply (p q : seminorm 𝕜 E) (x : E) : (p ⊓ q) x = ⨅ u : E, p u + q (x-u) := rfl

noncomputable instance : lattice (seminorm 𝕜 E) :=
{ inf := (⊓),
  inf_le_left := λ p q x, cinfi_le_of_le bdd_below_range_add x $
    by simp only [sub_self, map_zero, add_zero],
  inf_le_right := λ p q x, cinfi_le_of_le bdd_below_range_add 0 $
    by simp only [sub_self, map_zero, zero_add, sub_zero],
  le_inf := λ a b c hab hac x,
    le_cinfi $ λ u, (le_map_add_map_sub a _ _).trans $ add_le_add (hab _) (hac _),
  ..seminorm.semilattice_sup }

lemma smul_inf [has_smul R ℝ] [has_smul R ℝ≥0] [is_scalar_tower R ℝ≥0 ℝ]
  (r : R) (p q : seminorm 𝕜 E) :
  r • (p ⊓ q) = r • p ⊓ r • q :=
begin
  ext,
  simp_rw [smul_apply, inf_apply, smul_apply, ←smul_one_smul ℝ≥0 r (_ : ℝ), nnreal.smul_def,
    smul_eq_mul, real.mul_infi_of_nonneg (subtype.prop _), mul_add],
end

section classical

open_locale classical

/-- We define the supremum of an arbitrary subset of `seminorm 𝕜 E` as follows:
* if `s` is `bdd_above` *as a set of functions `E → ℝ`* (that is, if `s` is pointwise bounded
above), we take the pointwise supremum of all elements of `s`, and we prove that it is indeed a
seminorm.
* otherwise, we take the zero seminorm `⊥`.

There are two things worth mentionning here:
* First, it is not trivial at first that `s` being bounded above *by a function* implies
being bounded above *as a seminorm*. We show this in `seminorm.bdd_above_iff` by using
that the `Sup s` as defined here is then a bounding seminorm for `s`. So it is important to make
the case disjunction on `bdd_above (coe_fn '' s : set (E → ℝ))` and not `bdd_above s`.
* Since the pointwise `Sup` already gives `0` at points where a family of functions is
not bounded above, one could hope that just using the pointwise `Sup` would work here, without the
need for an additional case disjunction. As discussed on Zulip, this doesn't work because this can
give a function which does *not* satisfy the seminorm axioms (typically sub-additivity).
-/
noncomputable instance : has_Sup (seminorm 𝕜 E) :=
{ Sup := λ s, if h : bdd_above (coe_fn '' s : set (E → ℝ)) then
  { to_fun := ⨆ p : s, ((p : seminorm 𝕜 E) : E → ℝ),
    map_zero' :=
    begin
      rw [supr_apply, ← @real.csupr_const_zero s],
      congrm ⨆ i, _,
      exact map_zero i.1
    end,
    add_le' := λ x y,
    begin
      rcases h with ⟨q, hq⟩,
      obtain rfl | h := s.eq_empty_or_nonempty,
      { simp [real.csupr_empty] },
      haveI : nonempty ↥s := h.coe_sort,
      simp only [supr_apply],
      refine csupr_le (λ i, ((i : seminorm 𝕜 E).add_le' x y).trans $
        add_le_add (le_csupr ⟨q x, _⟩ i) (le_csupr ⟨q y, _⟩ i));
      rw [mem_upper_bounds, forall_range_iff];
      exact λ j, hq (mem_image_of_mem _ j.2) _,
    end,
    neg' := λ x,
    begin
      simp only [supr_apply],
      congrm ⨆ i, _,
      exact i.1.neg' _
    end,
    smul' := λ a x,
    begin
      simp only [supr_apply],
      rw [← smul_eq_mul, real.smul_supr_of_nonneg (norm_nonneg a) (λ i : s, (i : seminorm 𝕜 E) x)],
      congrm ⨆ i, _,
      exact i.1.smul' a x
    end }
  else ⊥ }

protected lemma coe_Sup_eq' {s : set $ seminorm 𝕜 E} (hs : bdd_above (coe_fn '' s : set (E → ℝ))) :
  coe_fn (Sup s) = ⨆ p : s, p :=
congr_arg _ (dif_pos hs)

protected lemma bdd_above_iff {s : set $ seminorm 𝕜 E} :
  bdd_above s ↔ bdd_above (coe_fn '' s : set (E → ℝ)) :=
⟨λ ⟨q, hq⟩, ⟨q, ball_image_of_ball $ λ p hp, hq hp⟩,
  λ H, ⟨Sup s, λ p hp x,
  begin
    rw [seminorm.coe_Sup_eq' H, supr_apply],
    rcases H with ⟨q, hq⟩,
    exact le_csupr ⟨q x, forall_range_iff.mpr $ λ i : s, hq (mem_image_of_mem _ i.2) x⟩ ⟨p, hp⟩
  end ⟩⟩

protected lemma coe_Sup_eq {s : set $ seminorm 𝕜 E} (hs : bdd_above s) :
  coe_fn (Sup s) = ⨆ p : s, p :=
seminorm.coe_Sup_eq' (seminorm.bdd_above_iff.mp hs)

protected lemma coe_supr_eq {ι : Type*} {p : ι → seminorm 𝕜 E} (hp : bdd_above (range p)) :
  coe_fn (⨆ i, p i) = ⨆ i, p i :=
by rw [← Sup_range, seminorm.coe_Sup_eq hp]; exact supr_range' (coe_fn : seminorm 𝕜 E → E → ℝ) p

private lemma seminorm.is_lub_Sup (s : set (seminorm 𝕜 E)) (hs₁ : bdd_above s) (hs₂ : s.nonempty) :
  is_lub s (Sup s) :=
begin
  refine ⟨λ p hp x, _, λ p hp x, _⟩;
  haveI : nonempty ↥s := hs₂.coe_sort;
  rw [seminorm.coe_Sup_eq hs₁, supr_apply],
  { rcases hs₁ with ⟨q, hq⟩,
    exact le_csupr ⟨q x, forall_range_iff.mpr $ λ i : s, hq i.2 x⟩ ⟨p, hp⟩ },
  { exact csupr_le (λ q, hp q.2 x) }
end

/-- `seminorm 𝕜 E` is a conditionally complete lattice.

Note that, while `inf`, `sup` and `Sup` have good definitional properties (corresponding to
`seminorm.has_inf`, `seminorm.has_sup` and `seminorm.has_Sup` respectively), `Inf s` is just
defined as the supremum of the lower bounds of `s`, which is not really useful in practice. If you
need to use `Inf` on seminorms, then you should probably provide a more workable definition first,
but this is unlikely to happen so we keep the "bad" definition for now. -/
noncomputable instance : conditionally_complete_lattice (seminorm 𝕜 E) :=
conditionally_complete_lattice_of_lattice_of_Sup (seminorm 𝕜 E) seminorm.is_lub_Sup

end classical

end normed_field

/-! ### Seminorm ball -/

section semi_normed_ring
variables [semi_normed_ring 𝕜]

section add_comm_group
variables [add_comm_group E]

section has_smul
variables [has_smul 𝕜 E] (p : seminorm 𝕜 E)

/-- The ball of radius `r` at `x` with respect to seminorm `p` is the set of elements `y` with
`p (y - x) < r`. -/
def ball (x : E) (r : ℝ) := { y : E | p (y - x) < r }

/-- The closed ball of radius `r` at `x` with respect to seminorm `p` is the set of elements `y`
with `p (y - x) ≤ r`. -/
def closed_ball (x : E) (r : ℝ) := { y : E | p (y - x) ≤ r }

variables {x y : E} {r : ℝ}

@[simp] lemma mem_ball : y ∈ ball p x r ↔ p (y - x) < r := iff.rfl
@[simp] lemma mem_closed_ball : y ∈ closed_ball p x r ↔ p (y - x) ≤ r := iff.rfl

lemma mem_ball_self (hr : 0 < r) : x ∈ ball p x r := by simp [hr]
lemma mem_closed_ball_self (hr : 0 ≤ r) : x ∈ closed_ball p x r := by simp [hr]

lemma mem_ball_zero : y ∈ ball p 0 r ↔ p y < r := by rw [mem_ball, sub_zero]
lemma mem_closed_ball_zero : y ∈ closed_ball p 0 r ↔ p y ≤ r := by rw [mem_closed_ball, sub_zero]

lemma ball_zero_eq : ball p 0 r = { y : E | p y < r } := set.ext $ λ x, p.mem_ball_zero
lemma closed_ball_zero_eq : closed_ball p 0 r = { y : E | p y ≤ r } :=
set.ext $ λ x, p.mem_closed_ball_zero

lemma ball_subset_closed_ball (x r) : ball p x r ⊆ closed_ball p x r := λ y (hy : _ < _), hy.le

lemma closed_ball_eq_bInter_ball (x r) : closed_ball p x r = ⋂ ρ > r, ball p x ρ :=
by ext y; simp_rw [mem_closed_ball, mem_Inter₂, mem_ball, ← forall_lt_iff_le']

@[simp] lemma ball_zero' (x : E) (hr : 0 < r) : ball (0 : seminorm 𝕜 E) x r = set.univ :=
begin
  rw [set.eq_univ_iff_forall, ball],
  simp [hr],
end

@[simp] lemma closed_ball_zero' (x : E) (hr : 0 < r) :
  closed_ball (0 : seminorm 𝕜 E) x r = set.univ :=
eq_univ_of_subset (ball_subset_closed_ball _ _ _) (ball_zero' x hr)

lemma ball_smul (p : seminorm 𝕜 E) {c : nnreal} (hc : 0 < c) (r : ℝ) (x : E) :
  (c • p).ball x r = p.ball x (r / c) :=
by { ext, rw [mem_ball, mem_ball, smul_apply, nnreal.smul_def, smul_eq_mul, mul_comm,
  lt_div_iff (nnreal.coe_pos.mpr hc)] }

lemma closed_ball_smul (p : seminorm 𝕜 E) {c : nnreal} (hc : 0 < c) (r : ℝ) (x : E) :
  (c • p).closed_ball x r = p.closed_ball x (r / c) :=
by { ext, rw [mem_closed_ball, mem_closed_ball, smul_apply, nnreal.smul_def, smul_eq_mul, mul_comm,
  le_div_iff (nnreal.coe_pos.mpr hc)] }

lemma ball_sup (p : seminorm 𝕜 E) (q : seminorm 𝕜 E) (e : E) (r : ℝ) :
  ball (p ⊔ q) e r = ball p e r ∩ ball q e r :=
by simp_rw [ball, ←set.set_of_and, coe_sup, pi.sup_apply, sup_lt_iff]

lemma closed_ball_sup (p : seminorm 𝕜 E) (q : seminorm 𝕜 E) (e : E) (r : ℝ) :
  closed_ball (p ⊔ q) e r = closed_ball p e r ∩ closed_ball q e r :=
by simp_rw [closed_ball, ←set.set_of_and, coe_sup, pi.sup_apply, sup_le_iff]

lemma ball_finset_sup' (p : ι → seminorm 𝕜 E) (s : finset ι) (H : s.nonempty) (e : E) (r : ℝ) :
  ball (s.sup' H p) e r = s.inf' H (λ i, ball (p i) e r) :=
begin
  induction H using finset.nonempty.cons_induction with a a s ha hs ih,
  { classical, simp },
  { rw [finset.sup'_cons hs, finset.inf'_cons hs, ball_sup, inf_eq_inter, ih] },
end

lemma closed_ball_finset_sup' (p : ι → seminorm 𝕜 E) (s : finset ι) (H : s.nonempty) (e : E)
  (r : ℝ) : closed_ball (s.sup' H p) e r = s.inf' H (λ i, closed_ball (p i) e r) :=
begin
  induction H using finset.nonempty.cons_induction with a a s ha hs ih,
  { classical, simp },
  { rw [finset.sup'_cons hs, finset.inf'_cons hs, closed_ball_sup, inf_eq_inter, ih] },
end

lemma ball_mono {p : seminorm 𝕜 E} {r₁ r₂ : ℝ} (h : r₁ ≤ r₂) : p.ball x r₁ ⊆ p.ball x r₂ :=
λ _ (hx : _ < _), hx.trans_le h

lemma closed_ball_mono {p : seminorm 𝕜 E} {r₁ r₂ : ℝ} (h : r₁ ≤ r₂) :
  p.closed_ball x r₁ ⊆ p.closed_ball x r₂ :=
λ _ (hx : _ ≤ _), hx.trans h

lemma ball_antitone {p q : seminorm 𝕜 E} (h : q ≤ p) : p.ball x r ⊆ q.ball x r :=
λ _, (h _).trans_lt

lemma closed_ball_antitone {p q : seminorm 𝕜 E} (h : q ≤ p) :
  p.closed_ball x r ⊆ q.closed_ball x r :=
λ _, (h _).trans

lemma ball_add_ball_subset (p : seminorm 𝕜 E) (r₁ r₂ : ℝ) (x₁ x₂ : E):
  p.ball (x₁ : E) r₁ + p.ball (x₂ : E) r₂ ⊆ p.ball (x₁ + x₂) (r₁ + r₂) :=
begin
  rintros x ⟨y₁, y₂, hy₁, hy₂, rfl⟩,
  rw [mem_ball, add_sub_add_comm],
  exact (map_add_le_add p _ _).trans_lt (add_lt_add hy₁ hy₂),
end

lemma closed_ball_add_closed_ball_subset (p : seminorm 𝕜 E) (r₁ r₂ : ℝ) (x₁ x₂ : E) :
  p.closed_ball (x₁ : E) r₁ + p.closed_ball (x₂ : E) r₂ ⊆ p.closed_ball (x₁ + x₂) (r₁ + r₂) :=
begin
  rintros x ⟨y₁, y₂, hy₁, hy₂, rfl⟩,
  rw [mem_closed_ball, add_sub_add_comm],
  exact (map_add_le_add p _ _).trans (add_le_add hy₁ hy₂)
end

lemma sub_mem_ball (p : seminorm 𝕜 E) (x₁ x₂ y : E) (r : ℝ) :
  x₁ - x₂ ∈ p.ball y r ↔ x₁ ∈ p.ball (x₂ + y) r :=
by simp_rw [mem_ball, sub_sub]

/-- The image of a ball under addition with a singleton is another ball. -/
lemma vadd_ball (p : seminorm 𝕜 E) :
  x +ᵥ p.ball y r = p.ball (x +ᵥ y) r :=
begin
  letI := add_group_seminorm.to_seminormed_add_comm_group p.to_add_group_seminorm,
  exact metric.vadd_ball x y r,
end

/-- The image of a closed ball under addition with a singleton is another closed ball. -/
lemma vadd_closed_ball (p : seminorm 𝕜 E) :
  x +ᵥ p.closed_ball y r = p.closed_ball (x +ᵥ y) r :=
begin
  letI := add_group_seminorm.to_seminormed_add_comm_group p.to_add_group_seminorm,
  exact metric.vadd_closed_ball x y r,
end

end has_smul

section module

variables [module 𝕜 E]
variables [semi_normed_ring 𝕜₂] [add_comm_group E₂] [module 𝕜₂ E₂]
variables {σ₁₂ : 𝕜 →+* 𝕜₂} [ring_hom_isometric σ₁₂]

lemma ball_comp (p : seminorm 𝕜₂ E₂) (f : E →ₛₗ[σ₁₂] E₂) (x : E) (r : ℝ) :
  (p.comp f).ball x r = f ⁻¹' (p.ball (f x) r) :=
begin
  ext,
  simp_rw [ball, mem_preimage, comp_apply, set.mem_set_of_eq, map_sub],
end

lemma closed_ball_comp (p : seminorm 𝕜₂ E₂) (f : E →ₛₗ[σ₁₂] E₂) (x : E) (r : ℝ) :
  (p.comp f).closed_ball x r = f ⁻¹' (p.closed_ball (f x) r) :=
begin
  ext,
  simp_rw [closed_ball, mem_preimage, comp_apply, set.mem_set_of_eq, map_sub],
end

variables (p : seminorm 𝕜 E)

lemma preimage_metric_ball {r : ℝ} :
  p ⁻¹' (metric.ball 0 r) = {x | p x < r} :=
begin
  ext x,
  simp only [mem_set_of, mem_preimage, mem_ball_zero_iff, real.norm_of_nonneg (map_nonneg p _)]
end

lemma preimage_metric_closed_ball {r : ℝ} :
  p ⁻¹' (metric.closed_ball 0 r) = {x | p x ≤ r} :=
begin
  ext x,
  simp only [mem_set_of, mem_preimage, mem_closed_ball_zero_iff,
    real.norm_of_nonneg (map_nonneg p _)]
end

lemma ball_zero_eq_preimage_ball {r : ℝ} :
  p.ball 0 r = p ⁻¹' (metric.ball 0 r) :=
by rw [ball_zero_eq, preimage_metric_ball]

lemma closed_ball_zero_eq_preimage_closed_ball {r : ℝ} :
  p.closed_ball 0 r = p ⁻¹' (metric.closed_ball 0 r) :=
by rw [closed_ball_zero_eq, preimage_metric_closed_ball]

@[simp] lemma ball_bot {r : ℝ} (x : E) (hr : 0 < r) :
  ball (⊥ : seminorm 𝕜 E) x r = set.univ :=
ball_zero' x hr

@[simp] lemma closed_ball_bot {r : ℝ} (x : E) (hr : 0 < r) :
  closed_ball (⊥ : seminorm 𝕜 E) x r = set.univ :=
closed_ball_zero' x hr

/-- Seminorm-balls at the origin are balanced. -/
lemma balanced_ball_zero (r : ℝ) : balanced 𝕜 (ball p 0 r) :=
begin
  rintro a ha x ⟨y, hy, hx⟩,
  rw [mem_ball_zero, ←hx, map_smul_eq_mul],
  calc _ ≤ p y : mul_le_of_le_one_left (map_nonneg p _) ha
  ...    < r   : by rwa mem_ball_zero at hy,
end

/-- Closed seminorm-balls at the origin are balanced. -/
lemma balanced_closed_ball_zero (r : ℝ) : balanced 𝕜 (closed_ball p 0 r) :=
begin
  rintro a ha x ⟨y, hy, hx⟩,
  rw [mem_closed_ball_zero, ←hx, map_smul_eq_mul],
  calc _ ≤ p y : mul_le_of_le_one_left (map_nonneg p _) ha
  ...    ≤ r   : by rwa mem_closed_ball_zero at hy
end

lemma ball_finset_sup_eq_Inter (p : ι → seminorm 𝕜 E) (s : finset ι) (x : E) {r : ℝ} (hr : 0 < r) :
  ball (s.sup p) x r = ⋂ (i ∈ s), ball (p i) x r :=
begin
  lift r to nnreal using hr.le,
  simp_rw [ball, Inter_set_of, finset_sup_apply, nnreal.coe_lt_coe,
    finset.sup_lt_iff (show ⊥ < r, from hr), ←nnreal.coe_lt_coe, subtype.coe_mk],
end

lemma closed_ball_finset_sup_eq_Inter (p : ι → seminorm 𝕜 E) (s : finset ι) (x : E) {r : ℝ}
  (hr : 0 ≤ r) : closed_ball (s.sup p) x r = ⋂ (i ∈ s), closed_ball (p i) x r :=
begin
  lift r to nnreal using hr,
  simp_rw [closed_ball, Inter_set_of, finset_sup_apply, nnreal.coe_le_coe,
    finset.sup_le_iff, ←nnreal.coe_le_coe, subtype.coe_mk]
end

lemma ball_finset_sup (p : ι → seminorm 𝕜 E) (s : finset ι) (x : E) {r : ℝ} (hr : 0 < r) :
  ball (s.sup p) x r = s.inf (λ i, ball (p i) x r) :=
begin
  rw finset.inf_eq_infi,
  exact ball_finset_sup_eq_Inter _ _ _ hr,
end

lemma closed_ball_finset_sup (p : ι → seminorm 𝕜 E) (s : finset ι) (x : E) {r : ℝ} (hr : 0 ≤ r) :
  closed_ball (s.sup p) x r = s.inf (λ i, closed_ball (p i) x r) :=
begin
  rw finset.inf_eq_infi,
  exact closed_ball_finset_sup_eq_Inter _ _ _ hr,
end

lemma ball_smul_ball (p : seminorm 𝕜 E) (r₁ r₂ : ℝ) :
  metric.ball (0 : 𝕜) r₁ • p.ball 0 r₂ ⊆ p.ball 0 (r₁ * r₂) :=
begin
  rw set.subset_def,
  intros x hx,
  rw set.mem_smul at hx,
  rcases hx with ⟨a, y, ha, hy, hx⟩,
  rw [←hx, mem_ball_zero, map_smul_eq_mul],
  exact mul_lt_mul'' (mem_ball_zero_iff.mp ha) (p.mem_ball_zero.mp hy) (norm_nonneg a)
    (map_nonneg p y),
end

lemma closed_ball_smul_closed_ball (p : seminorm 𝕜 E) (r₁ r₂ : ℝ) :
  metric.closed_ball (0 : 𝕜) r₁ • p.closed_ball 0 r₂ ⊆ p.closed_ball 0 (r₁ * r₂) :=
begin
  rw set.subset_def,
  intros x hx,
  rw set.mem_smul at hx,
  rcases hx with ⟨a, y, ha, hy, hx⟩,
  rw [←hx, mem_closed_ball_zero, map_smul_eq_mul],
  rw mem_closed_ball_zero_iff at ha,
  exact mul_le_mul ha (p.mem_closed_ball_zero.mp hy) (map_nonneg _ y) ((norm_nonneg a).trans ha)
end

@[simp] lemma ball_eq_emptyset (p : seminorm 𝕜 E) {x : E} {r : ℝ} (hr : r ≤ 0) : p.ball x r = ∅ :=
begin
  ext,
  rw [seminorm.mem_ball, set.mem_empty_iff_false, iff_false, not_lt],
  exact hr.trans (map_nonneg p _),
end

@[simp] lemma closed_ball_eq_emptyset (p : seminorm 𝕜 E) {x : E} {r : ℝ} (hr : r < 0) :
  p.closed_ball x r = ∅ :=
begin
  ext,
  rw [seminorm.mem_closed_ball, set.mem_empty_iff_false, iff_false, not_le],
  exact hr.trans_le (map_nonneg _ _),
end

end module
end add_comm_group
end semi_normed_ring

section normed_field
variables [normed_field 𝕜] [add_comm_group E] [module 𝕜 E] (p : seminorm 𝕜 E) {A B : set E}
  {a : 𝕜} {r : ℝ} {x : E}

lemma ball_norm_mul_subset {p : seminorm 𝕜 E} {k : 𝕜} {r : ℝ} :
  p.ball 0 (‖k‖ * r) ⊆ k • p.ball 0 r :=
begin
  rcases eq_or_ne k 0 with (rfl | hk),
  { rw [norm_zero, zero_mul, ball_eq_emptyset  _ le_rfl],
    exact empty_subset _ },
  { intro x,
    rw [set.mem_smul_set, seminorm.mem_ball_zero],
    refine λ hx, ⟨k⁻¹ • x, _, _⟩,
    { rwa [seminorm.mem_ball_zero, map_smul_eq_mul, norm_inv,
      ←(mul_lt_mul_left $ norm_pos_iff.mpr hk), ←mul_assoc, ←(div_eq_mul_inv ‖k‖ ‖k‖),
      div_self (ne_of_gt $ norm_pos_iff.mpr hk), one_mul] },
    rw [←smul_assoc, smul_eq_mul, ←div_eq_mul_inv, div_self hk, one_smul] }
end

lemma smul_ball_zero {p : seminorm 𝕜 E} {k : 𝕜} {r : ℝ} (hk : k ≠ 0) :
  k • p.ball 0 r = p.ball 0 (‖k‖ * r) :=
begin
  ext,
  rw [mem_smul_set_iff_inv_smul_mem₀ hk, p.mem_ball_zero, p.mem_ball_zero, map_smul_eq_mul,
    norm_inv, ← div_eq_inv_mul, div_lt_iff (norm_pos_iff.2 hk), mul_comm]
end

lemma smul_closed_ball_subset {p : seminorm 𝕜 E} {k : 𝕜} {r : ℝ} :
  k • p.closed_ball 0 r ⊆ p.closed_ball 0 (‖k‖ * r) :=
begin
  rintros x ⟨y, hy, h⟩,
  rw [seminorm.mem_closed_ball_zero, ←h, map_smul_eq_mul],
  rw seminorm.mem_closed_ball_zero at hy,
  exact mul_le_mul_of_nonneg_left hy (norm_nonneg _)
end

lemma smul_closed_ball_zero {p : seminorm 𝕜 E} {k : 𝕜} {r : ℝ} (hk : 0 < ‖k‖) :
  k • p.closed_ball 0 r = p.closed_ball 0 (‖k‖ * r) :=
begin
  refine subset_antisymm smul_closed_ball_subset _,
  intro x,
  rw [set.mem_smul_set, seminorm.mem_closed_ball_zero],
  refine λ hx, ⟨k⁻¹ • x, _, _⟩,
  { rwa [seminorm.mem_closed_ball_zero, map_smul_eq_mul, norm_inv, ←(mul_le_mul_left hk),
      ←mul_assoc, ←(div_eq_mul_inv ‖k‖ ‖k‖), div_self (ne_of_gt hk), one_mul] },
  rw [←smul_assoc, smul_eq_mul, ←div_eq_mul_inv, div_self (norm_pos_iff.mp hk), one_smul],
end

lemma ball_zero_absorbs_ball_zero (p : seminorm 𝕜 E) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) :
  absorbs 𝕜 (p.ball 0 r₁) (p.ball 0 r₂) :=
begin
  rcases exists_pos_lt_mul hr₁ r₂ with ⟨r, hr₀, hr⟩,
  refine ⟨r, hr₀, λ a ha x hx, _⟩,
  rw [smul_ball_zero (norm_pos_iff.1 $ hr₀.trans_le ha), p.mem_ball_zero],
  rw p.mem_ball_zero at hx,
  exact hx.trans (hr.trans_le $ mul_le_mul_of_nonneg_right ha hr₁.le)
end

/-- Seminorm-balls at the origin are absorbent. -/
protected lemma absorbent_ball_zero (hr : 0 < r) : absorbent 𝕜 (ball p (0 : E) r) :=
absorbent_iff_forall_absorbs_singleton.2 $ λ x, (p.ball_zero_absorbs_ball_zero hr).mono_right $
  singleton_subset_iff.2 $ p.mem_ball_zero.2 $ lt_add_one _

/-- Closed seminorm-balls at the origin are absorbent. -/
protected lemma absorbent_closed_ball_zero (hr : 0 < r) : absorbent 𝕜 (closed_ball p (0 : E) r) :=
(p.absorbent_ball_zero hr).subset (p.ball_subset_closed_ball _ _)

/-- Seminorm-balls containing the origin are absorbent. -/
protected lemma absorbent_ball (hpr : p x < r) : absorbent 𝕜 (ball p x r) :=
begin
  refine (p.absorbent_ball_zero $ sub_pos.2 hpr).subset (λ y hy, _),
  rw p.mem_ball_zero at hy,
  exact p.mem_ball.2 ((map_sub_le_add p _ _).trans_lt $ add_lt_of_lt_sub_right hy),
end

/-- Seminorm-balls containing the origin are absorbent. -/
protected lemma absorbent_closed_ball (hpr : p x < r) : absorbent 𝕜 (closed_ball p x r) :=
begin
  refine (p.absorbent_closed_ball_zero $ sub_pos.2 hpr).subset (λ y hy, _),
  rw p.mem_closed_ball_zero at hy,
  exact p.mem_closed_ball.2 ((map_sub_le_add p _ _).trans $ add_le_of_le_sub_right hy),
end

lemma symmetric_ball_zero (r : ℝ) (hx : x ∈ ball p 0 r) : -x ∈ ball p 0 r :=
balanced_ball_zero p r (-1) (by rw [norm_neg, norm_one]) ⟨x, hx, by rw [neg_smul, one_smul]⟩

@[simp]
lemma neg_ball (p : seminorm 𝕜 E) (r : ℝ) (x : E) :
  -ball p x r = ball p (-x) r :=
by { ext, rw [mem_neg, mem_ball, mem_ball, ←neg_add', sub_neg_eq_add, map_neg_eq_map] }

@[simp]
lemma smul_ball_preimage (p : seminorm 𝕜 E) (y : E) (r : ℝ) (a : 𝕜) (ha : a ≠ 0) :
  ((•) a) ⁻¹' p.ball y r = p.ball (a⁻¹ • y) (r / ‖a‖) :=
set.ext $ λ _, by rw [mem_preimage, mem_ball, mem_ball,
  lt_div_iff (norm_pos_iff.mpr ha), mul_comm, ←map_smul_eq_mul p, smul_sub, smul_inv_smul₀ ha]

end normed_field

section convex
variables [normed_field 𝕜] [add_comm_group E] [normed_space ℝ 𝕜] [module 𝕜 E]

section has_smul
variables [has_smul ℝ E] [is_scalar_tower ℝ 𝕜 E] (p : seminorm 𝕜 E)

/-- A seminorm is convex. Also see `convex_on_norm`. -/
protected lemma convex_on : convex_on ℝ univ p :=
begin
  refine ⟨convex_univ, λ x _ y _ a b ha hb hab, _⟩,
  calc p (a • x + b • y) ≤ p (a • x) + p (b • y) : map_add_le_add p _ _
    ... = ‖a • (1 : 𝕜)‖ * p x + ‖b • (1 : 𝕜)‖ * p y
        : by rw [←map_smul_eq_mul p, ←map_smul_eq_mul p, smul_one_smul, smul_one_smul]
    ... = a * p x + b * p y
        : by rw [norm_smul, norm_smul, norm_one, mul_one, mul_one, real.norm_of_nonneg ha,
            real.norm_of_nonneg hb],
end

end has_smul

section module
variables [module ℝ E] [is_scalar_tower ℝ 𝕜 E] (p : seminorm 𝕜 E) (x : E) (r : ℝ)

/-- Seminorm-balls are convex. -/
lemma convex_ball : convex ℝ (ball p x r) :=
begin
  convert (p.convex_on.translate_left (-x)).convex_lt r,
  ext y,
  rw [preimage_univ, sep_univ, p.mem_ball, sub_eq_add_neg],
  refl,
end

/-- Closed seminorm-balls are convex. -/
lemma convex_closed_ball : convex ℝ (closed_ball p x r) :=
begin
  rw closed_ball_eq_bInter_ball,
  exact convex_Inter₂ (λ _ _, convex_ball _ _ _)
end

end module
end convex

section restrict_scalars

variables (𝕜) {𝕜' : Type*} [normed_field 𝕜] [semi_normed_ring 𝕜'] [normed_algebra 𝕜 𝕜']
  [norm_one_class 𝕜'] [add_comm_group E] [module 𝕜' E] [has_smul 𝕜 E] [is_scalar_tower 𝕜 𝕜' E]

/-- Reinterpret a seminorm over a field `𝕜'` as a seminorm over a smaller field `𝕜`. This will
typically be used with `is_R_or_C 𝕜'` and `𝕜 = ℝ`. -/
protected def restrict_scalars (p : seminorm 𝕜' E) :
  seminorm 𝕜 E :=
{ smul' := λ a x, by rw [← smul_one_smul 𝕜' a x, p.smul', norm_smul, norm_one, mul_one],
  ..p }

@[simp] lemma coe_restrict_scalars (p : seminorm 𝕜' E) :
  (p.restrict_scalars 𝕜 : E → ℝ) = p :=
rfl

@[simp] lemma restrict_scalars_ball (p : seminorm 𝕜' E) :
  (p.restrict_scalars 𝕜).ball = p.ball :=
rfl

@[simp] lemma restrict_scalars_closed_ball (p : seminorm 𝕜' E) :
  (p.restrict_scalars 𝕜).closed_ball = p.closed_ball :=
rfl

end restrict_scalars

/-! ### Continuity criterions for seminorms -/

section continuity

variables [nontrivially_normed_field 𝕜] [semi_normed_ring 𝕝] [add_comm_group E] [module 𝕜 E]
variables [module 𝕝 E]

lemma continuous_at_zero' [topological_space E] [has_continuous_const_smul 𝕜 E] {p : seminorm 𝕜 E}
  {r : ℝ} (hr : 0 < r) (hp : p.closed_ball 0 r ∈ (𝓝 0 : filter E)) :
  continuous_at p 0 :=
begin
  refine metric.nhds_basis_closed_ball.tendsto_right_iff.mpr _,
  intros ε hε,
  rw map_zero,
  suffices : p.closed_ball 0 ε ∈ (𝓝 0 : filter E),
  { rwa seminorm.closed_ball_zero_eq_preimage_closed_ball at this },
  rcases exists_norm_lt 𝕜 (div_pos hε hr) with ⟨k, hk0, hkε⟩,
  have hk0' := norm_pos_iff.mp hk0,
  have := (set_smul_mem_nhds_zero_iff hk0').mpr hp,
  refine filter.mem_of_superset this (smul_set_subset_iff.mpr $ λ x hx, _),
  rw [mem_closed_ball_zero, map_smul_eq_mul, ← div_mul_cancel ε hr.ne.symm],
  exact mul_le_mul hkε.le (p.mem_closed_ball_zero.mp hx) (map_nonneg _ _) (div_nonneg hε.le hr.le)
end

lemma continuous_at_zero [topological_space E] [has_continuous_const_smul 𝕜 E] {p : seminorm 𝕜 E}
  {r : ℝ} (hr : 0 < r) (hp : p.ball 0 r ∈ (𝓝 0 : filter E)) :
  continuous_at p 0 :=
continuous_at_zero' hr (filter.mem_of_superset hp $ p.ball_subset_closed_ball _ _)

protected lemma uniform_continuous_of_continuous_at_zero [uniform_space E] [uniform_add_group E]
  {p : seminorm 𝕝 E} (hp : continuous_at p 0) :
  uniform_continuous p :=
begin
  have hp : filter.tendsto p (𝓝 0) (𝓝 0) := map_zero p ▸ hp,
  rw [uniform_continuous, uniformity_eq_comap_nhds_zero_swapped,
      metric.uniformity_eq_comap_nhds_zero, filter.tendsto_comap_iff],
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hp.comp filter.tendsto_comap) (λ xy, dist_nonneg) (λ xy, p.norm_sub_map_le_sub _ _)
end

protected lemma continuous_of_continuous_at_zero [topological_space E] [topological_add_group E]
  {p : seminorm 𝕝 E} (hp : continuous_at p 0) :
  continuous p :=
begin
  letI := topological_add_group.to_uniform_space E,
  haveI : uniform_add_group E := topological_add_comm_group_is_uniform,
  exact (seminorm.uniform_continuous_of_continuous_at_zero hp).continuous
end

protected lemma uniform_continuous [uniform_space E] [uniform_add_group E]
  [has_continuous_const_smul 𝕜 E] {p : seminorm 𝕜 E} {r : ℝ} (hr : 0 < r)
  (hp : p.ball 0 r ∈ (𝓝 0 : filter E)) : uniform_continuous p :=
seminorm.uniform_continuous_of_continuous_at_zero (continuous_at_zero hr hp)

protected lemma uniform_continuous' [uniform_space E] [uniform_add_group E]
  [has_continuous_const_smul 𝕜 E] {p : seminorm 𝕜 E} {r : ℝ} (hr : 0 < r)
  (hp : p.closed_ball 0 r ∈ (𝓝 0 : filter E)) : uniform_continuous p :=
seminorm.uniform_continuous_of_continuous_at_zero (continuous_at_zero' hr hp)

protected lemma continuous [topological_space E] [topological_add_group E]
  [has_continuous_const_smul 𝕜 E] {p : seminorm 𝕜 E} {r : ℝ} (hr : 0 < r)
  (hp : p.ball 0 r ∈ (𝓝 0 : filter E)) : continuous p :=
seminorm.continuous_of_continuous_at_zero (continuous_at_zero hr hp)

protected lemma continuous' [topological_space E] [topological_add_group E]
  [has_continuous_const_smul 𝕜 E] {p : seminorm 𝕜 E} {r : ℝ} (hr : 0 < r)
  (hp : p.closed_ball 0 r ∈ (𝓝 0 : filter E)) : continuous p :=
seminorm.continuous_of_continuous_at_zero (continuous_at_zero' hr hp)

lemma continuous_of_le [topological_space E] [topological_add_group E]
  [has_continuous_const_smul 𝕜 E] {p q : seminorm 𝕜 E} (hq : continuous q) (hpq : p ≤ q) :
  continuous p :=
begin
  refine seminorm.continuous one_pos (filter.mem_of_superset
    (is_open.mem_nhds _ $ q.mem_ball_self zero_lt_one) (ball_antitone hpq)),
  rw ball_zero_eq,
  exact is_open_lt hq continuous_const
end

end continuity

end seminorm

/-! ### The norm as a seminorm -/

section norm_seminorm
variables (𝕜) (E) [normed_field 𝕜] [seminormed_add_comm_group E] [normed_space 𝕜 E] {r : ℝ}

/-- The norm of a seminormed group as a seminorm. -/
def norm_seminorm : seminorm 𝕜 E :=
{ smul' := norm_smul,
  ..(norm_add_group_seminorm E)}

@[simp] lemma coe_norm_seminorm : ⇑(norm_seminorm 𝕜 E) = norm := rfl

@[simp] lemma ball_norm_seminorm : (norm_seminorm 𝕜 E).ball = metric.ball :=
by { ext x r y, simp only [seminorm.mem_ball, metric.mem_ball, coe_norm_seminorm, dist_eq_norm] }

variables {𝕜 E} {x : E}

/-- Balls at the origin are absorbent. -/
lemma absorbent_ball_zero (hr : 0 < r) : absorbent 𝕜 (metric.ball (0 : E) r) :=
by { rw ←ball_norm_seminorm 𝕜, exact (norm_seminorm _ _).absorbent_ball_zero hr }

/-- Balls containing the origin are absorbent. -/
lemma absorbent_ball (hx : ‖x‖ < r) : absorbent 𝕜 (metric.ball x r) :=
by { rw ←ball_norm_seminorm 𝕜, exact (norm_seminorm _ _).absorbent_ball hx }

/-- Balls at the origin are balanced. -/
lemma balanced_ball_zero : balanced 𝕜 (metric.ball (0 : E) r) :=
by { rw ←ball_norm_seminorm 𝕜, exact (norm_seminorm _ _).balanced_ball_zero r }

end norm_seminorm

-- Guard against import creep.
assert_not_exists balanced_core
