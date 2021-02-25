/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import analysis.normed_space.basic
import topology.sequences

/-!
# Normed groups homomorphisms

This file gathers definitions and elementary constructions about bounded group homomorphisms
between normed (abelian) groups (abbreviated to "normed group homs").

The main lemmas relate the boundedness condition to continuity and Lispschitzness.

The main construction is to endow the type of normed group homs between two given normed groups
with a group structure and a norm (we haven't proved yet that these two make a normed group
structure).

Some easy other constructions are related to subgroups of normed groups.
-/

open_locale nnreal big_operators

set_option old_structure_cmd true

/-- A morphism of normed abelian groups is a bounded group homomorphism. -/
structure normed_group_hom (V W : Type*) [normed_group V] [normed_group W] extends V →+ W :=
(bound' : ∃ C, ∀ v, ∥to_fun v∥ ≤ C * ∥v∥)

attribute [nolint doc_blame] normed_group_hom.to_add_monoid_hom

namespace normed_group_hom

variables {V V₁ V₂ V₃ : Type*}
variables [normed_group V] [normed_group V₁] [normed_group V₂] [normed_group V₃]
variables {f g : normed_group_hom V₁ V₂}

instance : has_coe_to_fun (normed_group_hom V₁ V₂) := ⟨_, normed_group_hom.to_fun⟩

initialize_simps_projections normed_group_hom (to_fun → apply)

lemma coe_inj (H : ⇑f = g) : f = g :=
by cases f; cases g; congr'; exact funext H

lemma coe_inj_iff : f = g ↔ ⇑f = g := ⟨congr_arg _, coe_inj⟩

@[ext] lemma ext (H : ∀ x, f x = g x) : f = g := coe_inj $ funext H

lemma ext_iff : f = g ↔ ∀ x, f x = g x := ⟨by rintro rfl x; refl, ext⟩

variables (f g)

@[simp] lemma to_fun_eq_coe : f.to_fun = f := rfl

@[simp] lemma coe_mk (f) (h₁) (h₂) (h₃) : ⇑(⟨f, h₁, h₂, h₃⟩ : normed_group_hom V₁ V₂) = f := rfl

@[simp] lemma coe_to_add_monoid_hom : ⇑f.to_add_monoid_hom = f := rfl

lemma to_add_monoid_hom_injective :
  function.injective (@normed_group_hom.to_add_monoid_hom V₁ V₂ _ _) :=
λ f g h, coe_inj $ show ⇑f.to_add_monoid_hom = g, by { rw h, refl }

@[simp] lemma mk_to_add_monoid_hom (f) (h₁) (h₂) (h₃) :
  (⟨f, h₁, h₂, h₃⟩ : normed_group_hom V₁ V₂).to_add_monoid_hom = ⟨f, h₁, h₂⟩ := rfl

@[simp] lemma map_zero : f 0 = 0 := f.to_add_monoid_hom.map_zero

@[simp] lemma map_add (x y) : f (x + y) = f x + f y := f.to_add_monoid_hom.map_add _ _

@[simp] lemma map_sum {ι : Type*} (v : ι → V₁) (s : finset ι) :
  f (∑ i in s, v i) = ∑ i in s, f (v i) :=
f.to_add_monoid_hom.map_sum _ _

@[simp] lemma map_sub (x y) : f (x - y) = f x - f y := f.to_add_monoid_hom.map_sub _ _

@[simp] lemma map_neg (x) : f (-x) = -(f x) := f.to_add_monoid_hom.map_neg _

/-- Make a normed group hom from a group hom and a norm bound. -/
def mk' (f : V₁ →+ V₂) (C : ℝ≥0) (hC : ∀ x, ∥f x∥ ≤ C * ∥x∥) : normed_group_hom V₁ V₂ :=
{ bound' := ⟨C, hC⟩ .. f}

@[simp] lemma coe_mk' (f : V₁ →+ V₂) (C) (hC) : ⇑(mk' f C hC) = f := rfl

/-- Predicate asserting a norm bound on a normed group hom. -/
def bound_by (f : normed_group_hom V₁ V₂) (C : ℝ≥0) : Prop := ∀ x, ∥f x∥ ≤ C * ∥x∥

lemma mk'_bound_by (f : V₁ →+ V₂) (C) (hC) : (mk' f C hC).bound_by C := hC

lemma bound : ∃ C, 0 < C ∧ f.bound_by C :=
begin
  obtain ⟨C, hC⟩ := f.bound',
  let C' : ℝ≥0 := ⟨max C 1, le_max_right_of_le zero_le_one⟩,
  use C',
  simp only [C', ← nnreal.coe_lt_coe, subtype.coe_mk, nnreal.coe_zero,
    lt_max_iff, zero_lt_one, or_true, true_and],
  intro v,
  calc ∥f v∥
      ≤ C * ∥v∥ : hC v
  ... ≤ max C 1 * ∥v∥ : mul_le_mul (le_max_left _ _) le_rfl (norm_nonneg _) _,
  exact zero_le_one.trans (le_max_right _ _)
end

lemma lipschitz_of_bound_by (C : ℝ≥0) (h : f.bound_by C) :
  lipschitz_with (nnreal.of_real C) f :=
lipschitz_with.of_dist_le' $ λ x y, by simpa only [dist_eq_norm, f.map_sub] using h (x - y)

theorem antilipschitz_of_bound_by {K : ℝ≥0} (h : ∀ x, ∥x∥ ≤ K * ∥f x∥) :
  antilipschitz_with K f :=
antilipschitz_with.of_le_mul_dist $
λ x y, by simpa only [dist_eq_norm, f.map_sub] using h (x - y)

protected lemma uniform_continuous (f : normed_group_hom V₁ V₂) :
  uniform_continuous f :=
let ⟨C, C_pos, hC⟩ := f.bound in (lipschitz_of_bound_by f C hC).uniform_continuous

@[continuity]
protected lemma continuous (f : normed_group_hom V₁ V₂) : continuous f :=
f.uniform_continuous.continuous

/-- The norm of a normed group hom. -/
noncomputable instance : has_norm (normed_group_hom V₁ V₂) :=
⟨λ f, ↑(⨅ (r : ℝ≥0) (h : f.bound_by r), r)⟩

variables {f g}

instance : has_zero (normed_group_hom V₁ V₂) :=
⟨{ bound' := ⟨0, λ v, show ∥(0 : V₂)∥ ≤ 0 * _, by rw [norm_zero, zero_mul]⟩,
   .. (0 : V₁ →+ V₂) }⟩

instance : inhabited (normed_group_hom V₁ V₂) := ⟨0⟩

/-- The identity as a continuous normed group hom. -/
@[simps]
def id : normed_group_hom V V :=
{ bound' := ⟨1, λ v, show ∥v∥ ≤ 1 * ∥v∥, by rw [one_mul]⟩,
  .. add_monoid_hom.id V }

/-- The composition of continuous normed group homs. -/
@[simps]
def comp (g : normed_group_hom V₂ V₃) (f : normed_group_hom V₁ V₂) :
  normed_group_hom V₁ V₃ :=
{ bound' :=
  begin
    obtain ⟨Cf, Cf_pos, hf⟩ := f.bound,
    obtain ⟨Cg, Cg_pos, hg⟩ := g.bound,
    use [Cg * Cf],
    assume v,
    calc ∥g (f v)∥
        ≤ Cg * ∥f v∥    : hg _
    ... ≤ Cg * Cf * ∥v∥ : _,
    rw mul_assoc,
    exact mul_le_mul le_rfl (hf v) (norm_nonneg _) Cg_pos.le
  end
  .. g.to_add_monoid_hom.comp f.to_add_monoid_hom }

/-- Addition of normed group homs. -/
instance : has_add (normed_group_hom V₁ V₂) :=
⟨λ f g,
{ bound' :=
  begin
    obtain ⟨Cf, Cf_pos, hCf⟩ := f.bound,
    obtain ⟨Cg, Cg_pos, hCg⟩ := g.bound,
    use [Cf + Cg],
    assume v,
    calc ∥f v + g v∥
        ≤ ∥f v∥ + ∥g v∥ : norm_add_le _ _
    ... ≤ Cf * ∥v∥ + Cg * ∥v∥ : add_le_add (hCf _) (hCg _)
    ... = (Cf + Cg) * ∥v∥ : by rw add_mul
  end,
  .. (f.to_add_monoid_hom + g.to_add_monoid_hom) }⟩

/-- Opposite of a normed group hom. -/
instance : has_neg (normed_group_hom V₁ V₂) :=
⟨λ f,
{ bound' :=
  begin
    obtain ⟨C, C_pos, hC⟩ := f.bound,
    use C,
    assume v,
    calc ∥-(f v)∥
        = ∥f v∥ : norm_neg _
    ... ≤ C * ∥v∥ : hC _
  end, .. (-f.to_add_monoid_hom) }⟩

/-- Subtraction of normed group homs. -/
instance : has_sub (normed_group_hom V₁ V₂) :=
⟨λ f g,
{ bound' :=
  begin
    simp only [add_monoid_hom.sub_apply, add_monoid_hom.to_fun_eq_coe, sub_eq_add_neg],
    exact (f + -g).bound'
  end,
  .. (f.to_add_monoid_hom - g.to_add_monoid_hom) }⟩

@[simp] lemma coe_zero : ⇑(0 : normed_group_hom V₁ V₂) = 0 := rfl

@[simp] lemma coe_neg (f : normed_group_hom V₁ V₂) : ⇑(-f) = -f := rfl

@[simp] lemma coe_add (f g : normed_group_hom V₁ V₂) : ⇑(f + g) = f + g := rfl

@[simp] lemma coe_sub (f g : normed_group_hom V₁ V₂) : ⇑(f - g) = f - g := rfl

/-- Homs between two given normed groups form a commutative additive group. -/
instance : add_comm_group (normed_group_hom V₁ V₂) :=
by refine_struct
{ .. normed_group_hom.has_add, .. normed_group_hom.has_zero,
  .. normed_group_hom.has_neg, ..normed_group_hom.has_sub };
{ intros, ext, simp [add_assoc, add_comm, add_left_comm, sub_eq_add_neg] }
.

lemma sum_apply {ι : Type*} (s : finset ι) (f : ι → normed_group_hom V₁ V₂) (v : V₁) :
  (∑ i in s, f i) v = ∑ i in s, (f i v) :=
begin
  classical,
  apply finset.induction_on s,
  { simp only [coe_zero, finset.sum_empty, pi.zero_apply] },
  { intros i s his IH,
    simp only [his, IH, pi.add_apply, finset.sum_insert, not_false_iff, coe_add] }
end

@[simp] lemma coe_sum {ι : Type*} (s : finset ι) (f : ι → normed_group_hom V₁ V₂) :
  ⇑(∑ i in s, f i) = ∑ i in s, (f i) :=
by { ext v, rw [finset.sum_apply, sum_apply] }

/-- Composition of normed groups hom as an additive group morphism. -/
def comp_hom : (normed_group_hom V₂ V₃) →+ (normed_group_hom V₁ V₂) →+ (normed_group_hom V₁ V₃) :=
add_monoid_hom.mk' (λ g, add_monoid_hom.mk' (λ f, g.comp f)
  (by { intros, ext, exact g.map_add _ _ }))
  (by { intros, ext, refl })

@[simp] lemma comp_zero (f : normed_group_hom V₂ V₃) : f.comp (0 : normed_group_hom V₁ V₂) = 0 :=
by { ext, exact f.map_zero' }

@[simp] lemma zero_comp (f : normed_group_hom V₁ V₂) : (0 : normed_group_hom V₂ V₃).comp f = 0 :=
by { ext, refl }

end normed_group_hom

namespace normed_group_hom

section kernels

variables {V V₁ V₂ V₃ : Type*}
variables [normed_group V] [normed_group V₁] [normed_group V₂] [normed_group V₃]
variables (f : normed_group_hom V₁ V₂) (g : normed_group_hom V₂ V₃)

/-- The kernel of a bounded group homomorphism. Naturally endowed with a `normed_group` instance. -/
def ker : add_subgroup V₁ := f.to_add_monoid_hom.ker

/-- The normed group structure on the kernel of a normed group hom. -/
instance : normed_group f.ker :=
{ dist_eq := λ v w, dist_eq_norm _ _ }

lemma mem_ker (v : V₁) : v ∈ f.ker ↔ f v = 0 :=
by { erw f.to_add_monoid_hom.mem_ker, refl }

/-- The inclusion of the kernel, as bounded group homomorphism. -/
@[simps] def ker.incl : normed_group_hom f.ker V₁ :=
{ to_fun := (coe : f.ker → V₁),
  map_zero' := add_subgroup.coe_zero _,
  map_add' := λ v w, add_subgroup.coe_add _ _ _,
  bound' := ⟨1, λ v, by { rw [one_mul], refl }⟩ }

/-- Given a normed group hom `f : V₁ → V₂` satisfying `g.comp f = 0` for some `g : V₂ → V₃`,
    the corestriction of `f` to the kernel of `g`. -/
@[simps] def ker.lift (h : g.comp f = 0) :
  normed_group_hom V₁ g.ker :=
{ to_fun := λ v, ⟨f v, by { erw g.mem_ker, show (g.comp f) v = 0, rw h, refl }⟩,
  map_zero' := by { simp only [map_zero], refl },
  map_add' := λ v w, by { simp only [map_add], refl },
  bound' := f.bound' }

@[simp] lemma ker.incl_comp_lift (h : g.comp f = 0) :
  (ker.incl g).comp (ker.lift f g h) = f :=
by { ext, refl }

end kernels

section range

variables {V V₁ V₂ V₃ : Type*}
variables [normed_group V] [normed_group V₁] [normed_group V₂] [normed_group V₃]
variables (f : normed_group_hom V₁ V₂) (g : normed_group_hom V₂ V₃)

/-- The image of a bounded group homomorphism. Naturally endowed with a `normed_group` instance. -/
def range : add_subgroup V₂ := f.to_add_monoid_hom.range

lemma mem_range (v : V₂) : v ∈ f.range ↔ ∃ w, f w = v :=
by { rw [range, add_monoid_hom.mem_range], refl }

end range

variables {V W V₁ V₂ V₃ : Type*}
variables [normed_group V] [normed_group W]
variables [normed_group V₁] [normed_group V₂] [normed_group V₃]
variables {f : normed_group_hom V W}

/-- A `normed_group_hom` is *norm-nonincreasing* if `∥f v∥ ≤ ∥v∥` for all `v`. -/
def norm_noninc (f : normed_group_hom V W) : Prop :=
∀ v, ∥f v∥ ≤ ∥v∥

/-- A strict `normed_group_hom` is a `normed_group_hom` that preserves the norm. -/
def is_strict (f : normed_group_hom V W) : Prop :=
∀ v, ∥f v∥ = ∥v∥

namespace norm_noninc

lemma bound_by_one (hf : f.norm_noninc) : f.bound_by 1 :=
λ v, by simpa only [one_mul, nnreal.coe_one] using hf v

lemma id : (id : normed_group_hom V V).norm_noninc :=
λ v, le_rfl

lemma comp {g : normed_group_hom V₂ V₃} {f : normed_group_hom V₁ V₂}
  (hg : g.norm_noninc) (hf : f.norm_noninc) :
  (g.comp f).norm_noninc :=
λ v, (hg (f v)).trans (hf v)

end norm_noninc

namespace is_strict

lemma injective (hf : f.is_strict) :
  function.injective f :=
begin
  intros x y h,
  rw ← sub_eq_zero at *,
  suffices : ∥ x - y ∥ = 0, by simpa,
  rw ← hf,
  simpa,
end

lemma norm_noninc (hf : f.is_strict) : f.norm_noninc :=
λ v, le_of_eq $ hf v

lemma bound_by_one (hf : f.is_strict) : f.bound_by 1 :=
hf.norm_noninc.bound_by_one

lemma id : (id : normed_group_hom V V).is_strict :=
λ v, rfl

lemma comp {g : normed_group_hom V₂ V₃} {f : normed_group_hom V₁ V₂}
  (hg : g.is_strict) (hf : f.is_strict) :
  (g.comp f).is_strict :=
λ v, (hg (f v)).trans (hf v)

end is_strict

end normed_group_hom
