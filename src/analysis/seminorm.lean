/-
Copyright (c) 2019 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo, Yaël Dillies, Moritz Doll
-/
import data.real.pointwise
import data.real.sqrt
import topology.algebra.filter_basis
import topology.algebra.module.locally_convex

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
open_locale big_operators nnreal pointwise topological_space

variables {R R' 𝕜 E F G ι : Type*}

/-- A seminorm on a module over a normed ring is a function to the reals that is positive
semidefinite, positive homogeneous, and subadditive. -/
structure seminorm (𝕜 : Type*) (E : Type*) [semi_normed_ring 𝕜] [add_group E] [has_smul 𝕜 E]
  extends add_group_seminorm E :=
(smul' : ∀ (a : 𝕜) (x : E), to_fun (a • x) = ∥a∥ * to_fun x)

attribute [nolint doc_blame] seminorm.to_add_group_seminorm

/-- `seminorm_class F 𝕜 E` states that `F` is a type of seminorms on the `𝕜`-module E.

You should extend this class when you extend `seminorm`. -/
class seminorm_class (F : Type*) (𝕜 E : out_param $ Type*) [semi_normed_ring 𝕜] [add_group E]
  [has_smul 𝕜 E] extends add_group_seminorm_class F E :=
(map_smul_eq_mul (f : F) (a : 𝕜) (x : E) : f (a • x) = ∥a∥ * f x)

export seminorm_class (map_smul_eq_mul)

-- `𝕜` is an `out_param`, so this is a false positive.
attribute [nolint dangerous_instance] seminorm_class.to_add_group_seminorm_class

section of

/-- Alternative constructor for a `seminorm` on an `add_comm_group E` that is a module over a
`semi_norm_ring 𝕜`. -/
def seminorm.of [semi_normed_ring 𝕜] [add_comm_group E] [module 𝕜 E] (f : E → ℝ)
  (add_le : ∀ (x y : E), f (x + y) ≤ f x + f y)
  (smul : ∀ (a : 𝕜) (x : E), f (a • x) = ∥a∥ * f x) : seminorm 𝕜 E :=
{ to_fun    := f,
  map_zero' := by rw [←zero_smul 𝕜 (0 : E), smul, norm_zero, zero_mul],
  add_le'   := add_le,
  smul'     := smul,
  neg'      := λ x, by rw [←neg_one_smul 𝕜, smul, norm_neg, ← smul, one_smul] }

/-- Alternative constructor for a `seminorm` over a normed field `𝕜` that only assumes `f 0 = 0`
and an inequality for the scalar multiplication. -/
def seminorm.of_smul_le [normed_field 𝕜] [add_comm_group E] [module 𝕜 E] (f : E → ℝ)
  (map_zero : f 0 = 0) (add_le : ∀ x y, f (x + y) ≤ f x + f y)
  (smul_le : ∀ (r : 𝕜) x, f (r • x) ≤ ∥r∥ * f x) : seminorm 𝕜 E :=
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

-- TODO: define `has_Sup` too, from the skeleton at
-- https://github.com/leanprover-community/mathlib/pull/11329#issuecomment-1008915345
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
variables [add_comm_group E] [add_comm_group F] [add_comm_group G]
variables [module 𝕜 E] [module 𝕜 F] [module 𝕜 G]
variables [has_smul R ℝ] [has_smul R ℝ≥0] [is_scalar_tower R ℝ≥0 ℝ]

/-- Composition of a seminorm with a linear map is a seminorm. -/
def comp (p : seminorm 𝕜 F) (f : E →ₗ[𝕜] F) : seminorm 𝕜 E :=
{ to_fun    := λ x, p (f x),
  smul'     := λ _ _, (congr_arg p (f.map_smul _ _)).trans (map_smul_eq_mul p _ _),
  ..(p.to_add_group_seminorm.comp f.to_add_monoid_hom) }

lemma coe_comp (p : seminorm 𝕜 F) (f : E →ₗ[𝕜] F) : ⇑(p.comp f) = p ∘ f := rfl

@[simp] lemma comp_apply (p : seminorm 𝕜 F) (f : E →ₗ[𝕜] F) (x : E) : (p.comp f) x = p (f x) := rfl

@[simp] lemma comp_id (p : seminorm 𝕜 E) : p.comp linear_map.id = p :=
ext $ λ _, rfl

@[simp] lemma comp_zero (p : seminorm 𝕜 F) : p.comp (0 : E →ₗ[𝕜] F) = 0 :=
ext $ λ _, map_zero p

@[simp] lemma zero_comp (f : E →ₗ[𝕜] F) : (0 : seminorm 𝕜 F).comp f = 0 :=
ext $ λ _, rfl

lemma comp_comp (p : seminorm 𝕜 G) (g : F →ₗ[𝕜] G) (f : E →ₗ[𝕜] F) :
  p.comp (g.comp f) = (p.comp g).comp f :=
ext $ λ _, rfl

lemma add_comp (p q : seminorm 𝕜 F) (f : E →ₗ[𝕜] F) : (p + q).comp f = p.comp f + q.comp f :=
ext $ λ _, rfl

lemma comp_add_le (p : seminorm 𝕜 F) (f g : E →ₗ[𝕜] F) : p.comp (f + g) ≤ p.comp f + p.comp g :=
λ _, map_add_le_add p _ _

lemma smul_comp (p : seminorm 𝕜 F) (f : E →ₗ[𝕜] F) (c : R) : (c • p).comp f = c • (p.comp f) :=
ext $ λ _, rfl

lemma comp_mono {p : seminorm 𝕜 F} {q : seminorm 𝕜 F} (f : E →ₗ[𝕜] F) (hp : p ≤ q) :
  p.comp f ≤ q.comp f := λ _, hp _

/-- The composition as an `add_monoid_hom`. -/
@[simps] def pullback (f : E →ₗ[𝕜] F) : seminorm 𝕜 F →+ seminorm 𝕜 E :=
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

lemma norm_sub_map_le_sub (p : seminorm 𝕜 E) (x y : E) : ∥p x - p y∥ ≤ p (x - y) :=
abs_sub_map_le_sub p x y

end module
end semi_normed_ring

section semi_normed_comm_ring
variables [semi_normed_comm_ring 𝕜] [add_comm_group E] [add_comm_group F] [module 𝕜 E] [module 𝕜 F]

lemma comp_smul (p : seminorm 𝕜 F) (f : E →ₗ[𝕜] F) (c : 𝕜) :
  p.comp (c • f) = ∥c∥₊ • p.comp f :=
ext $ λ _, by rw [comp_apply, smul_apply, linear_map.smul_apply, map_smul_eq_mul, nnreal.smul_def,
  coe_nnnorm, smul_eq_mul, comp_apply]

lemma comp_smul_apply (p : seminorm 𝕜 F) (f : E →ₗ[𝕜] F) (c : 𝕜) (x : E) :
  p.comp (c • f) x = ∥c∥ * p (f x) := map_smul_eq_mul p _ _

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

end normed_field

/-! ### Seminorm ball -/

section semi_normed_ring
variables [semi_normed_ring 𝕜]

section add_comm_group
variables [add_comm_group E]

section has_smul
variables [has_smul 𝕜 E] (p : seminorm 𝕜 E)

/-- The ball of radius `r` at `x` with respect to seminorm `p` is the set of elements `y` with
`p (y - x) < `r`. -/
def ball (x : E) (r : ℝ) := { y : E | p (y - x) < r }

variables {x y : E} {r : ℝ}

@[simp] lemma mem_ball : y ∈ ball p x r ↔ p (y - x) < r := iff.rfl

lemma mem_ball_self (hr : 0 < r) : x ∈ ball p x r := by simp [hr]

lemma mem_ball_zero : y ∈ ball p 0 r ↔ p y < r := by rw [mem_ball, sub_zero]

lemma ball_zero_eq : ball p 0 r = { y : E | p y < r } := set.ext $ λ x, p.mem_ball_zero

@[simp] lemma ball_zero' (x : E) (hr : 0 < r) : ball (0 : seminorm 𝕜 E) x r = set.univ :=
begin
  rw [set.eq_univ_iff_forall, ball],
  simp [hr],
end

lemma ball_smul (p : seminorm 𝕜 E) {c : nnreal} (hc : 0 < c) (r : ℝ) (x : E) :
  (c • p).ball x r = p.ball x (r / c) :=
by { ext, rw [mem_ball, mem_ball, smul_apply, nnreal.smul_def, smul_eq_mul, mul_comm,
  lt_div_iff (nnreal.coe_pos.mpr hc)] }

lemma ball_sup (p : seminorm 𝕜 E) (q : seminorm 𝕜 E) (e : E) (r : ℝ) :
  ball (p ⊔ q) e r = ball p e r ∩ ball q e r :=
by simp_rw [ball, ←set.set_of_and, coe_sup, pi.sup_apply, sup_lt_iff]

lemma ball_finset_sup' (p : ι → seminorm 𝕜 E) (s : finset ι) (H : s.nonempty) (e : E) (r : ℝ) :
  ball (s.sup' H p) e r = s.inf' H (λ i, ball (p i) e r) :=
begin
  induction H using finset.nonempty.cons_induction with a a s ha hs ih,
  { classical, simp },
  { rw [finset.sup'_cons hs, finset.inf'_cons hs, ball_sup, inf_eq_inter, ih] },
end

lemma ball_mono {p : seminorm 𝕜 E} {r₁ r₂ : ℝ} (h : r₁ ≤ r₂) : p.ball x r₁ ⊆ p.ball x r₂ :=
λ _ (hx : _ < _), hx.trans_le h

lemma ball_antitone {p q : seminorm 𝕜 E} (h : q ≤ p) : p.ball x r ⊆ q.ball x r :=
λ _, (h _).trans_lt

lemma ball_add_ball_subset (p : seminorm 𝕜 E) (r₁ r₂ : ℝ) (x₁ x₂ : E):
  p.ball (x₁ : E) r₁ + p.ball (x₂ : E) r₂ ⊆ p.ball (x₁ + x₂) (r₁ + r₂) :=
begin
  rintros x ⟨y₁, y₂, hy₁, hy₂, rfl⟩,
  rw [mem_ball, add_sub_add_comm],
  exact (map_add_le_add p _ _).trans_lt (add_lt_add hy₁ hy₂),
end

end has_smul

section module

variables [module 𝕜 E]
variables [add_comm_group F] [module 𝕜 F]

lemma ball_comp (p : seminorm 𝕜 F) (f : E →ₗ[𝕜] F) (x : E) (r : ℝ) :
  (p.comp f).ball x r = f ⁻¹' (p.ball (f x) r) :=
begin
  ext,
  simp_rw [ball, mem_preimage, comp_apply, set.mem_set_of_eq, map_sub],
end

variables (p : seminorm 𝕜 E)

lemma ball_zero_eq_preimage_ball {r : ℝ} :
  p.ball 0 r = p ⁻¹' (metric.ball 0 r) :=
begin
  ext x,
  simp only [mem_ball, sub_zero, mem_preimage, mem_ball_zero_iff],
  rw real.norm_of_nonneg,
  exact map_nonneg p _,
end

@[simp] lemma ball_bot {r : ℝ} (x : E) (hr : 0 < r) :
  ball (⊥ : seminorm 𝕜 E) x r = set.univ :=
ball_zero' x hr

/-- Seminorm-balls at the origin are balanced. -/
lemma balanced_ball_zero (r : ℝ) : balanced 𝕜 (ball p 0 r) :=
begin
  rintro a ha x ⟨y, hy, hx⟩,
  rw [mem_ball_zero, ←hx, map_smul_eq_mul],
  calc _ ≤ p y : mul_le_of_le_one_left (map_nonneg p _) ha
  ...    < r   : by rwa mem_ball_zero at hy,
end

lemma ball_finset_sup_eq_Inter (p : ι → seminorm 𝕜 E) (s : finset ι) (x : E) {r : ℝ} (hr : 0 < r) :
  ball (s.sup p) x r = ⋂ (i ∈ s), ball (p i) x r :=
begin
  lift r to nnreal using hr.le,
  simp_rw [ball, Inter_set_of, finset_sup_apply, nnreal.coe_lt_coe,
    finset.sup_lt_iff (show ⊥ < r, from hr), ←nnreal.coe_lt_coe, subtype.coe_mk],
end

lemma ball_finset_sup (p : ι → seminorm 𝕜 E) (s : finset ι) (x : E) {r : ℝ} (hr : 0 < r) :
  ball (s.sup p) x r = s.inf (λ i, ball (p i) x r) :=
begin
  rw finset.inf_eq_infi,
  exact ball_finset_sup_eq_Inter _ _ _ hr,
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

@[simp] lemma ball_eq_emptyset (p : seminorm 𝕜 E) {x : E} {r : ℝ} (hr : r ≤ 0) : p.ball x r = ∅ :=
begin
  ext,
  rw [seminorm.mem_ball, set.mem_empty_iff_false, iff_false, not_lt],
  exact hr.trans (map_nonneg p _),
end

end module
end add_comm_group
end semi_normed_ring

section normed_field
variables [normed_field 𝕜] [add_comm_group E] [module 𝕜 E] (p : seminorm 𝕜 E) {A B : set E}
  {a : 𝕜} {r : ℝ} {x : E}

lemma smul_ball_zero {p : seminorm 𝕜 E} {k : 𝕜} {r : ℝ} (hk : 0 < ∥k∥) :
  k • p.ball 0 r = p.ball 0 (∥k∥ * r) :=
begin
  ext,
  rw [set.mem_smul_set, seminorm.mem_ball_zero],
  split; intro h,
  { rcases h with ⟨y, hy, h⟩,
    rw [←h, map_smul_eq_mul],
    rw seminorm.mem_ball_zero at hy,
    exact (mul_lt_mul_left hk).mpr hy },
  refine ⟨k⁻¹ • x, _, _⟩,
  { rw [seminorm.mem_ball_zero, map_smul_eq_mul, norm_inv, ←(mul_lt_mul_left hk),
      ←mul_assoc, ←(div_eq_mul_inv ∥k∥ ∥k∥), div_self (ne_of_gt hk), one_mul],
    exact h},
  rw [←smul_assoc, smul_eq_mul, ←div_eq_mul_inv, div_self (norm_pos_iff.mp hk), one_smul],
end

lemma ball_zero_absorbs_ball_zero (p : seminorm 𝕜 E) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) :
  absorbs 𝕜 (p.ball 0 r₁) (p.ball 0 r₂) :=
begin
  by_cases hr₂ : r₂ ≤ 0,
  { rw ball_eq_emptyset p hr₂, exact absorbs_empty },
  rw [not_le] at hr₂,
  rcases exists_between hr₁ with ⟨r, hr, hr'⟩,
  refine ⟨r₂/r, div_pos hr₂ hr, _⟩,
  simp_rw set.subset_def,
  intros a ha x hx,
  have ha' : 0 < ∥a∥ := lt_of_lt_of_le (div_pos hr₂ hr) ha,
  rw [smul_ball_zero ha', p.mem_ball_zero],
  rw p.mem_ball_zero at hx,
  rw div_le_iff hr at ha,
  exact hx.trans (lt_of_le_of_lt ha ((mul_lt_mul_left ha').mpr hr')),
end

/-- Seminorm-balls at the origin are absorbent. -/
protected lemma absorbent_ball_zero (hr : 0 < r) : absorbent 𝕜 (ball p (0 : E) r) :=
begin
  rw absorbent_iff_nonneg_lt,
  rintro x,
  have hxr : 0 ≤ p x / r := by positivity,
  refine ⟨p x/r, hxr, λ a ha, _⟩,
  have ha₀ : 0 < ∥a∥ := hxr.trans_lt ha,
  refine ⟨a⁻¹ • x, _, smul_inv_smul₀ (norm_pos_iff.1 ha₀) x⟩,
  rwa [mem_ball_zero, map_smul_eq_mul, norm_inv, inv_mul_lt_iff ha₀, ←div_lt_iff hr],
end

/-- Seminorm-balls containing the origin are absorbent. -/
protected lemma absorbent_ball (hpr : p x < r) : absorbent 𝕜 (ball p x r) :=
begin
  refine (p.absorbent_ball_zero $ sub_pos.2 hpr).subset (λ y hy, _),
  rw p.mem_ball_zero at hy,
  exact p.mem_ball.2 ((map_sub_le_add p _ _).trans_lt $ add_lt_of_lt_sub_right hy),
end

lemma symmetric_ball_zero (r : ℝ) (hx : x ∈ ball p 0 r) : -x ∈ ball p 0 r :=
balanced_ball_zero p r (-1) (by rw [norm_neg, norm_one]) ⟨x, hx, by rw [neg_smul, one_smul]⟩

@[simp]
lemma neg_ball (p : seminorm 𝕜 E) (r : ℝ) (x : E) :
  -ball p x r = ball p (-x) r :=
by { ext, rw [mem_neg, mem_ball, mem_ball, ←neg_add', sub_neg_eq_add, map_neg_eq_map] }

@[simp]
lemma smul_ball_preimage (p : seminorm 𝕜 E) (y : E) (r : ℝ) (a : 𝕜) (ha : a ≠ 0) :
  ((•) a) ⁻¹' p.ball y r = p.ball (a⁻¹ • y) (r / ∥a∥) :=
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
    ... = ∥a • (1 : 𝕜)∥ * p x + ∥b • (1 : 𝕜)∥ * p y
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

end restrict_scalars

/-! ### Continuity criterions for seminorms -/

section continuity

variables [semi_normed_ring 𝕜] [add_comm_group E]
  [module 𝕜 E]

lemma continuous_at_zero [norm_one_class 𝕜] [normed_algebra ℝ 𝕜] [module ℝ E]
  [is_scalar_tower ℝ 𝕜 E] [topological_space E] [has_continuous_const_smul ℝ E] {p : seminorm 𝕜 E}
  (hp : p.ball 0 1 ∈ (𝓝 0 : filter E)) :
  continuous_at p 0 :=
begin
  change continuous_at (p.restrict_scalars ℝ) 0,
  rw ← p.restrict_scalars_ball ℝ at hp,
  refine metric.nhds_basis_ball.tendsto_right_iff.mpr _,
  intros ε hε,
  rw map_zero,
  suffices : (p.restrict_scalars ℝ).ball 0 ε ∈ (𝓝 0 : filter E),
  { rwa seminorm.ball_zero_eq_preimage_ball at this },
  have := (set_smul_mem_nhds_zero_iff hε.ne.symm).mpr hp,
  rwa [seminorm.smul_ball_zero (norm_pos_iff.mpr hε.ne.symm),
      real.norm_of_nonneg hε.le, mul_one] at this
end

protected lemma uniform_continuous_of_continuous_at_zero [uniform_space E] [uniform_add_group E]
  {p : seminorm 𝕜 E} (hp : continuous_at p 0) :
  uniform_continuous p :=
begin
  have hp : filter.tendsto p (𝓝 0) (𝓝 0) := map_zero p ▸ hp,
  rw [uniform_continuous, uniformity_eq_comap_nhds_zero_swapped,
      metric.uniformity_eq_comap_nhds_zero, filter.tendsto_comap_iff],
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hp.comp filter.tendsto_comap) (λ xy, dist_nonneg) (λ xy, p.norm_sub_map_le_sub _ _)
end

protected lemma continuous_of_continuous_at_zero [topological_space E] [topological_add_group E]
  {p : seminorm 𝕜 E} (hp : continuous_at p 0) :
  continuous p :=
begin
  letI := topological_add_group.to_uniform_space E,
  haveI : uniform_add_group E := topological_add_comm_group_is_uniform,
  exact (seminorm.uniform_continuous_of_continuous_at_zero hp).continuous
end

protected lemma uniform_continuous [norm_one_class 𝕜] [normed_algebra ℝ 𝕜] [module ℝ E]
  [is_scalar_tower ℝ 𝕜 E] [uniform_space E] [uniform_add_group E] [has_continuous_const_smul ℝ E]
  {p : seminorm 𝕜 E} (hp : p.ball 0 1 ∈ (𝓝 0 : filter E)) :
  uniform_continuous p :=
seminorm.uniform_continuous_of_continuous_at_zero (continuous_at_zero hp)

protected lemma continuous [norm_one_class 𝕜] [normed_algebra ℝ 𝕜] [module ℝ E]
  [is_scalar_tower ℝ 𝕜 E] [topological_space E] [topological_add_group E]
  [has_continuous_const_smul ℝ E] {p : seminorm 𝕜 E} (hp : p.ball 0 1 ∈ (𝓝 0 : filter E)) :
  continuous p :=
seminorm.continuous_of_continuous_at_zero (continuous_at_zero hp)

lemma continuous_of_le [norm_one_class 𝕜] [normed_algebra ℝ 𝕜] [module ℝ E]
  [is_scalar_tower ℝ 𝕜 E] [topological_space E] [topological_add_group E]
  [has_continuous_const_smul ℝ E] {p q : seminorm 𝕜 E} (hq : continuous q) (hpq : p ≤ q) :
  continuous p :=
begin
  refine seminorm.continuous (filter.mem_of_superset
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
lemma absorbent_ball (hx : ∥x∥ < r) : absorbent 𝕜 (metric.ball x r) :=
by { rw ←ball_norm_seminorm 𝕜, exact (norm_seminorm _ _).absorbent_ball hx }

/-- Balls at the origin are balanced. -/
lemma balanced_ball_zero : balanced 𝕜 (metric.ball (0 : E) r) :=
by { rw ←ball_norm_seminorm 𝕜, exact (norm_seminorm _ _).balanced_ball_zero r }

end norm_seminorm
