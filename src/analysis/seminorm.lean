/-
Copyright (c) 2019 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo, Yaël Dillies, Moritz Doll
-/
import analysis.locally_convex.basic
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

open normed_field set
open_locale big_operators nnreal pointwise topological_space

variables {R R' 𝕜 E F G ι : Type*}

/-- A seminorm on a module over a normed ring is a function to the reals that is positive
semidefinite, positive homogeneous, and subadditive. -/
structure seminorm (𝕜 : Type*) (E : Type*) [semi_normed_ring 𝕜] [add_monoid E] [has_scalar 𝕜 E] :=
(to_fun    : E → ℝ)
(smul'     : ∀ (a : 𝕜) (x : E), to_fun (a • x) = ∥a∥ * to_fun x)
(triangle' : ∀ x y : E, to_fun (x + y) ≤ to_fun x + to_fun y)

namespace seminorm

section semi_normed_ring
variables [semi_normed_ring 𝕜]

section add_monoid
variables [add_monoid E]

section has_scalar
variables [has_scalar 𝕜 E]

instance fun_like : fun_like (seminorm 𝕜 E) E (λ _, ℝ) :=
{ coe := seminorm.to_fun, coe_injective' := λ f g h, by cases f; cases g; congr' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
instance : has_coe_to_fun (seminorm 𝕜 E) (λ _, E → ℝ) := ⟨λ p, p.to_fun⟩

@[ext] lemma ext {p q : seminorm 𝕜 E} (h : ∀ x, (p : E → ℝ) x = q x) : p = q := fun_like.ext p q h

instance : has_zero (seminorm 𝕜 E) :=
⟨{ to_fun    := 0,
  smul'     := λ _ _, (mul_zero _).symm,
  triangle' := λ _ _, eq.ge (zero_add _) }⟩

@[simp] lemma coe_zero : ⇑(0 : seminorm 𝕜 E) = 0 := rfl

@[simp] lemma zero_apply (x : E) : (0 : seminorm 𝕜 E) x = 0 := rfl

instance : inhabited (seminorm 𝕜 E) := ⟨0⟩

variables (p : seminorm 𝕜 E) (c : 𝕜) (x y : E) (r : ℝ)

protected lemma smul : p (c • x) = ∥c∥ * p x := p.smul' _ _
protected lemma triangle : p (x + y) ≤ p x + p y := p.triangle' _ _

/-- Any action on `ℝ` which factors through `ℝ≥0` applies to a seminorm. -/
instance [has_scalar R ℝ] [has_scalar R ℝ≥0] [is_scalar_tower R ℝ≥0 ℝ] :
  has_scalar R (seminorm 𝕜 E) :=
{ smul := λ r p,
  { to_fun := λ x, r • p x,
    smul' := λ _ _, begin
      simp only [←smul_one_smul ℝ≥0 r (_ : ℝ), nnreal.smul_def, smul_eq_mul],
      rw [p.smul, mul_left_comm],
    end,
    triangle' := λ _ _, begin
      simp only [←smul_one_smul ℝ≥0 r (_ : ℝ), nnreal.smul_def, smul_eq_mul],
      exact (mul_le_mul_of_nonneg_left (p.triangle _ _) (nnreal.coe_nonneg _)).trans_eq
        (mul_add _ _ _),
    end } }

instance [has_scalar R ℝ] [has_scalar R ℝ≥0] [is_scalar_tower R ℝ≥0 ℝ]
  [has_scalar R' ℝ] [has_scalar R' ℝ≥0] [is_scalar_tower R' ℝ≥0 ℝ]
  [has_scalar R R'] [is_scalar_tower R R' ℝ] :
  is_scalar_tower R R' (seminorm 𝕜 E) :=
{ smul_assoc := λ r a p, ext $ λ x, smul_assoc r a (p x) }

lemma coe_smul [has_scalar R ℝ] [has_scalar R ℝ≥0] [is_scalar_tower R ℝ≥0 ℝ]
  (r : R) (p : seminorm 𝕜 E) : ⇑(r • p) = r • p := rfl

@[simp] lemma smul_apply [has_scalar R ℝ] [has_scalar R ℝ≥0] [is_scalar_tower R ℝ≥0 ℝ]
  (r : R) (p : seminorm 𝕜 E) (x : E) : (r • p) x = r • p x := rfl

instance : has_add (seminorm 𝕜 E) :=
{ add := λ p q,
  { to_fun := λ x, p x + q x,
    smul' := λ a x, by rw [p.smul, q.smul, mul_add],
    triangle' := λ _ _, has_le.le.trans_eq (add_le_add (p.triangle _ _) (q.triangle _ _))
      (add_add_add_comm _ _ _ _) } }

lemma coe_add (p q : seminorm 𝕜 E) : ⇑(p + q) = p + q := rfl

@[simp] lemma add_apply (p q : seminorm 𝕜 E) (x : E) : (p + q) x = p x + q x := rfl

instance : add_monoid (seminorm 𝕜 E) :=
fun_like.coe_injective.add_monoid _ rfl coe_add (λ p n, coe_smul n p)

instance : ordered_cancel_add_comm_monoid (seminorm 𝕜 E) :=
fun_like.coe_injective.ordered_cancel_add_comm_monoid _ rfl coe_add (λ p n, coe_smul n p)

instance [monoid R] [mul_action R ℝ] [has_scalar R ℝ≥0] [is_scalar_tower R ℝ≥0 ℝ] :
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

instance [monoid R] [distrib_mul_action R ℝ] [has_scalar R ℝ≥0] [is_scalar_tower R ℝ≥0 ℝ] :
  distrib_mul_action R (seminorm 𝕜 E) :=
(coe_fn_add_monoid_hom_injective 𝕜 E).distrib_mul_action _ coe_smul

instance [semiring R] [module R ℝ] [has_scalar R ℝ≥0] [is_scalar_tower R ℝ≥0 ℝ] :
  module R (seminorm 𝕜 E) :=
(coe_fn_add_monoid_hom_injective 𝕜 E).module R _ coe_smul

-- TODO: define `has_Sup` too, from the skeleton at
-- https://github.com/leanprover-community/mathlib/pull/11329#issuecomment-1008915345
noncomputable instance : has_sup (seminorm 𝕜 E) :=
{ sup := λ p q,
  { to_fun := p ⊔ q,
    triangle' := λ x y, sup_le
      ((p.triangle x y).trans $ add_le_add le_sup_left le_sup_left)
      ((q.triangle x y).trans $ add_le_add le_sup_right le_sup_right),
    smul' := λ x v, (congr_arg2 max (p.smul x v) (q.smul x v)).trans $
      (mul_max_of_nonneg _ _ $ norm_nonneg x).symm } }

@[simp] lemma coe_sup (p q : seminorm 𝕜 E) : ⇑(p ⊔ q) = p ⊔ q := rfl
lemma sup_apply (p q : seminorm 𝕜 E) (x : E) : (p ⊔ q) x = p x ⊔ q x := rfl

lemma smul_sup [has_scalar R ℝ] [has_scalar R ℝ≥0] [is_scalar_tower R ℝ≥0 ℝ]
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

noncomputable instance : semilattice_sup (seminorm 𝕜 E) :=
function.injective.semilattice_sup _ fun_like.coe_injective coe_sup

end has_scalar

section smul_with_zero
variables [smul_with_zero 𝕜 E] (p : seminorm 𝕜 E)

@[simp]
protected lemma zero : p 0 = 0 :=
calc p 0 = p ((0 : 𝕜) • 0) : by rw zero_smul
...      = 0 : by rw [p.smul, norm_zero, zero_mul]

end smul_with_zero
end add_monoid

section module
variables [add_comm_group E] [add_comm_group F] [add_comm_group G]
variables [module 𝕜 E] [module 𝕜 F] [module 𝕜 G]
variables [has_scalar R ℝ] [has_scalar R ℝ≥0] [is_scalar_tower R ℝ≥0 ℝ]

/-- Composition of a seminorm with a linear map is a seminorm. -/
def comp (p : seminorm 𝕜 F) (f : E →ₗ[𝕜] F) : seminorm 𝕜 E :=
{ to_fun := λ x, p(f x),
  smul' := λ _ _, (congr_arg p (f.map_smul _ _)).trans (p.smul _ _),
  triangle' := λ _ _, eq.trans_le (congr_arg p (f.map_add _ _)) (p.triangle _ _) }

lemma coe_comp (p : seminorm 𝕜 F) (f : E →ₗ[𝕜] F) : ⇑(p.comp f) = p ∘ f := rfl

@[simp] lemma comp_apply (p : seminorm 𝕜 F) (f : E →ₗ[𝕜] F) (x : E) : (p.comp f) x = p (f x) := rfl

@[simp] lemma comp_id (p : seminorm 𝕜 E) : p.comp linear_map.id = p :=
ext $ λ _, rfl

@[simp] lemma comp_zero (p : seminorm 𝕜 F) : p.comp (0 : E →ₗ[𝕜] F) = 0 :=
ext $ λ _, seminorm.zero _

@[simp] lemma zero_comp (f : E →ₗ[𝕜] F) : (0 : seminorm 𝕜 F).comp f = 0 :=
ext $ λ _, rfl

lemma comp_comp (p : seminorm 𝕜 G) (g : F →ₗ[𝕜] G) (f : E →ₗ[𝕜] F) :
  p.comp (g.comp f) = (p.comp g).comp f :=
ext $ λ _, rfl

lemma add_comp (p q : seminorm 𝕜 F) (f : E →ₗ[𝕜] F) : (p + q).comp f = p.comp f + q.comp f :=
ext $ λ _, rfl

lemma comp_triangle (p : seminorm 𝕜 F) (f g : E →ₗ[𝕜] F) : p.comp (f + g) ≤ p.comp f + p.comp g :=
λ _, p.triangle _ _

lemma smul_comp (p : seminorm 𝕜 F) (f : E →ₗ[𝕜] F) (c : R) : (c • p).comp f = c • (p.comp f) :=
ext $ λ _, rfl

lemma comp_mono {p : seminorm 𝕜 F} {q : seminorm 𝕜 F} (f : E →ₗ[𝕜] F) (hp : p ≤ q) :
  p.comp f ≤ q.comp f := λ _, hp _

/-- The composition as an `add_monoid_hom`. -/
@[simps] def pullback (f : E →ₗ[𝕜] F) : add_monoid_hom (seminorm 𝕜 F) (seminorm 𝕜 E) :=
⟨λ p, p.comp f, zero_comp f, λ p q, add_comp p q f⟩

section norm_one_class
variables [norm_one_class 𝕜] (p : seminorm 𝕜 E) (x y : E) (r : ℝ)

@[simp]
protected lemma neg : p (-x) = p x :=
calc p (-x) = p ((-1 : 𝕜) • x) : by rw neg_one_smul
...         = p x : by rw [p.smul, norm_neg, norm_one, one_mul]

protected lemma sub_le : p (x - y) ≤ p x + p y :=
calc
  p (x - y)
      = p (x + -y) : by rw sub_eq_add_neg
  ... ≤ p x + p (-y) : p.triangle x (-y)
  ... = p x + p y : by rw p.neg

lemma nonneg : 0 ≤ p x :=
have h: 0 ≤ 2 * p x, from
calc 0 = p (x + (- x)) : by rw [add_neg_self, p.zero]
...    ≤ p x + p (-x)  : p.triangle _ _
...    = 2 * p x : by rw [p.neg, two_mul],
nonneg_of_mul_nonneg_left h zero_lt_two

lemma sub_rev : p (x - y) = p (y - x) := by rw [←neg_sub, p.neg]

/-- The direct path from 0 to y is shorter than the path with x "inserted" in between. -/
lemma le_insert : p y ≤ p x + p (x - y) :=
calc p y = p (x - (x - y)) : by rw sub_sub_cancel
... ≤ p x + p (x - y) : p.sub_le _ _

/-- The direct path from 0 to x is shorter than the path with y "inserted" in between. -/
lemma le_insert' : p x ≤ p y + p (x - y) := by { rw sub_rev, exact le_insert _ _ _ }

instance : order_bot (seminorm 𝕜 E) := ⟨0, nonneg⟩

@[simp] lemma coe_bot : ⇑(⊥ : seminorm 𝕜 E) = 0 := rfl

lemma bot_eq_zero : (⊥ : seminorm 𝕜 E) = 0 := rfl

lemma smul_le_smul {p q : seminorm 𝕜 E} {a b : ℝ≥0} (hpq : p ≤ q) (hab : a ≤ b) :
  a • p ≤ b • q :=
begin
  simp_rw [le_def, pi.le_def, coe_smul],
  intros x,
  simp_rw [pi.smul_apply, nnreal.smul_def, smul_eq_mul],
  exact mul_le_mul hab (hpq x) (nonneg p x) (nnreal.coe_nonneg b),
end

lemma finset_sup_apply (p : ι → seminorm 𝕜 E) (s : finset ι) (x : E) :
  s.sup p x = ↑(s.sup (λ i, ⟨p i x, nonneg (p i) x⟩) : ℝ≥0) :=
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

end norm_one_class
end module
end semi_normed_ring

section semi_normed_comm_ring
variables [semi_normed_comm_ring 𝕜] [add_comm_group E] [add_comm_group F] [module 𝕜 E] [module 𝕜 F]

lemma comp_smul (p : seminorm 𝕜 F) (f : E →ₗ[𝕜] F) (c : 𝕜) :
  p.comp (c • f) = ∥c∥₊ • p.comp f :=
ext $ λ _, by rw [comp_apply, smul_apply, linear_map.smul_apply, p.smul, nnreal.smul_def,
  coe_nnnorm, smul_eq_mul, comp_apply]

lemma comp_smul_apply (p : seminorm 𝕜 F) (f : E →ₗ[𝕜] F) (c : 𝕜) (x : E) :
  p.comp (c • f) x = ∥c∥ * p (f x) := p.smul _ _

end semi_normed_comm_ring

section normed_field
variables [normed_field 𝕜] [add_comm_group E] [module 𝕜 E]

private lemma bdd_below_range_add (x : E) (p q : seminorm 𝕜 E) :
  bdd_below (range (λ (u : E), p u + q (x - u))) :=
by { use 0, rintro _ ⟨x, rfl⟩, exact add_nonneg (p.nonneg _) (q.nonneg _) }

noncomputable instance : has_inf (seminorm 𝕜 E) :=
{ inf := λ p q,
  { to_fun := λ x, ⨅ u : E, p u + q (x-u),
    triangle' := λ x y, begin
      refine le_cinfi_add_cinfi (λ u v, _),
      apply cinfi_le_of_le (bdd_below_range_add _ _ _) (v+u), dsimp only,
      convert add_le_add (p.triangle v u) (q.triangle (y-v) (x-u)) using 1,
      { rw show x + y - (v + u) = y - v + (x - u), by abel },
      { abel },
    end,
    smul' := λ a x, begin
      obtain rfl | ha := eq_or_ne a 0,
      { simp_rw [norm_zero, zero_mul, zero_smul, zero_sub, seminorm.neg],
        refine cinfi_eq_of_forall_ge_of_forall_gt_exists_lt
          (λ i, add_nonneg (p.nonneg _) (q.nonneg _))
          (λ x hx, ⟨0, by rwa [p.zero, q.zero, add_zero]⟩) },
      simp_rw [real.mul_infi_of_nonneg (norm_nonneg a), mul_add, ←p.smul, ←q.smul, smul_sub],
      refine function.surjective.infi_congr ((•) a⁻¹ : E → E) (λ u, ⟨a • u, inv_smul_smul₀ ha u⟩)
        (λ u, _),
      rw smul_inv_smul₀ ha,
    end } }

@[simp] lemma inf_apply (p q : seminorm 𝕜 E) (x : E) : (p ⊓ q) x = ⨅ u : E, p u + q (x-u) := rfl

noncomputable instance : lattice (seminorm 𝕜 E) :=
{ inf := (⊓),
  inf_le_left := λ p q x, begin
    apply cinfi_le_of_le (bdd_below_range_add _ _ _) x,
    simp only [sub_self, seminorm.zero, add_zero],
  end,
  inf_le_right := λ p q x, begin
    apply cinfi_le_of_le (bdd_below_range_add _ _ _) (0:E),
    simp only [sub_self, seminorm.zero, zero_add, sub_zero],
  end,
  le_inf := λ a b c hab hac x,
    le_cinfi $ λ u, le_trans (a.le_insert' _ _) (add_le_add (hab _) (hac _)),
  ..seminorm.semilattice_sup }

lemma smul_inf [has_scalar R ℝ] [has_scalar R ℝ≥0] [is_scalar_tower R ℝ≥0 ℝ]
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

section has_scalar
variables [has_scalar 𝕜 E] (p : seminorm 𝕜 E)

/-- The ball of radius `r` at `x` with respect to seminorm `p` is the set of elements `y` with
`p (y - x) < `r`. -/
def ball (x : E) (r : ℝ) := { y : E | p (y - x) < r }

variables {x y : E} {r : ℝ}

@[simp] lemma mem_ball : y ∈ ball p x r ↔ p (y - x) < r := iff.rfl

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
  exact (p.triangle _ _).trans_lt (add_lt_add hy₁ hy₂),
end

end has_scalar

section module

variables [module 𝕜 E]
variables [add_comm_group F] [module 𝕜 F]

lemma ball_comp (p : seminorm 𝕜 F) (f : E →ₗ[𝕜] F) (x : E) (r : ℝ) :
  (p.comp f).ball x r = f ⁻¹' (p.ball (f x) r) :=
begin
  ext,
  simp_rw [ball, mem_preimage, comp_apply, set.mem_set_of_eq, map_sub],
end

section norm_one_class
variables [norm_one_class 𝕜] (p : seminorm 𝕜 E)

lemma ball_zero_eq_preimage_ball {r : ℝ} :
  p.ball 0 r = p ⁻¹' (metric.ball 0 r) :=
begin
  ext x,
  simp only [mem_ball, sub_zero, mem_preimage, mem_ball_zero_iff, real.norm_of_nonneg (p.nonneg x)],
end

@[simp] lemma ball_bot {r : ℝ} (x : E) (hr : 0 < r) : ball (⊥ : seminorm 𝕜 E) x r = set.univ :=
ball_zero' x hr

/-- Seminorm-balls at the origin are balanced. -/
lemma balanced_ball_zero (r : ℝ) : balanced 𝕜 (ball p 0 r) :=
begin
  rintro a ha x ⟨y, hy, hx⟩,
  rw [mem_ball_zero, ←hx, p.smul],
  calc _ ≤ p y : mul_le_of_le_one_left (p.nonneg _) ha
  ...    < r   : by rwa mem_ball_zero at hy,
end

lemma ball_finset_sup_eq_Inter (p : ι → seminorm 𝕜 E) (s : finset ι) (x : E) {r : ℝ} (hr : 0 < r) :
  ball (s.sup p) x r = ⋂ (i ∈ s), ball (p i) x r :=
begin
  lift r to nnreal using hr.le,
  simp_rw [ball, Inter_set_of, finset_sup_apply, nnreal.coe_lt_coe,
    finset.sup_lt_iff (show ⊥ < r, from hr), ←nnreal.coe_lt_coe, subtype.coe_mk],
end

lemma ball_finset_sup (p : ι → seminorm 𝕜 E) (s : finset ι) (x : E) {r : ℝ}
  (hr : 0 < r) : ball (s.sup p) x r = s.inf (λ i, ball (p i) x r) :=
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
  rw [←hx, mem_ball_zero, seminorm.smul],
  exact mul_lt_mul'' (mem_ball_zero_iff.mp ha) (p.mem_ball_zero.mp hy) (norm_nonneg a) (p.nonneg y),
end

@[simp] lemma ball_eq_emptyset (p : seminorm 𝕜 E) {x : E} {r : ℝ} (hr : r ≤ 0) : p.ball x r = ∅ :=
begin
  ext,
  rw [seminorm.mem_ball, set.mem_empty_eq, iff_false, not_lt],
  exact hr.trans (p.nonneg _),
end

end norm_one_class
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
    rw [←h, seminorm.smul],
    rw seminorm.mem_ball_zero at hy,
    exact (mul_lt_mul_left hk).mpr hy },
  refine ⟨k⁻¹ • x, _, _⟩,
  { rw [seminorm.mem_ball_zero, seminorm.smul, norm_inv, ←(mul_lt_mul_left hk),
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
  have hxr : 0 ≤ p x/r := div_nonneg (p.nonneg _) hr.le,
  refine ⟨p x/r, hxr, λ a ha, _⟩,
  have ha₀ : 0 < ∥a∥ := hxr.trans_lt ha,
  refine ⟨a⁻¹ • x, _, smul_inv_smul₀ (norm_pos_iff.1 ha₀) x⟩,
  rwa [mem_ball_zero, p.smul, norm_inv, inv_mul_lt_iff ha₀, ←div_lt_iff hr],
end

/-- Seminorm-balls containing the origin are absorbent. -/
protected lemma absorbent_ball (hpr : p x < r) : absorbent 𝕜 (ball p x r) :=
begin
  refine (p.absorbent_ball_zero $ sub_pos.2 hpr).subset (λ y hy, _),
  rw p.mem_ball_zero at hy,
  exact p.mem_ball.2 ((p.sub_le _ _).trans_lt $ add_lt_of_lt_sub_right hy),
end

lemma symmetric_ball_zero (r : ℝ) (hx : x ∈ ball p 0 r) : -x ∈ ball p 0 r :=
balanced_ball_zero p r (-1) (by rw [norm_neg, norm_one]) ⟨x, hx, by rw [neg_smul, one_smul]⟩

@[simp]
lemma neg_ball (p : seminorm 𝕜 E) (r : ℝ) (x : E) :
  -ball p x r = ball p (-x) r :=
by { ext, rw [mem_neg, mem_ball, mem_ball, ←neg_add', sub_neg_eq_add, p.neg], }

@[simp]
lemma smul_ball_preimage (p : seminorm 𝕜 E) (y : E) (r : ℝ) (a : 𝕜) (ha : a ≠ 0) :
  ((•) a) ⁻¹' p.ball y r = p.ball (a⁻¹ • y) (r / ∥a∥) :=
set.ext $ λ _, by rw [mem_preimage, mem_ball, mem_ball,
  lt_div_iff (norm_pos_iff.mpr ha), mul_comm, ←p.smul, smul_sub, smul_inv_smul₀ ha]

end normed_field

section convex
variables [normed_field 𝕜] [add_comm_group E] [normed_space ℝ 𝕜] [module 𝕜 E]

section has_scalar
variables [has_scalar ℝ E] [is_scalar_tower ℝ 𝕜 E] (p : seminorm 𝕜 E)

/-- A seminorm is convex. Also see `convex_on_norm`. -/
protected lemma convex_on : convex_on ℝ univ p :=
begin
  refine ⟨convex_univ, λ x y _ _ a b ha hb hab, _⟩,
  calc p (a • x + b • y) ≤ p (a • x) + p (b • y) : p.triangle _ _
    ... = ∥a • (1 : 𝕜)∥ * p x + ∥b • (1 : 𝕜)∥ * p y
        : by rw [←p.smul, ←p.smul, smul_one_smul, smul_one_smul]
    ... = a * p x + b * p y
        : by rw [norm_smul, norm_smul, norm_one, mul_one, mul_one, real.norm_of_nonneg ha,
            real.norm_of_nonneg hb],
end

end has_scalar

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
end seminorm

/-! ### The norm as a seminorm -/

section norm_seminorm
variables (𝕜 E) [normed_field 𝕜] [semi_normed_group E] [normed_space 𝕜 E] {r : ℝ}

/-- The norm of a seminormed group as a seminorm. -/
def norm_seminorm : seminorm 𝕜 E := ⟨norm, norm_smul, norm_add_le⟩

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
lemma balanced_ball_zero [norm_one_class 𝕜] : balanced 𝕜 (metric.ball (0 : E) r) :=
by { rw ←ball_norm_seminorm 𝕜, exact (norm_seminorm _ _).balanced_ball_zero r }

end norm_seminorm
