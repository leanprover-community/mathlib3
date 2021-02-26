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

The main lemmas relate the boundedness condition to continuity and Lipschitzness.

The main construction is to endow the type of normed group homs between two given normed groups
with a group structure and a norm, giving rise to a normed group structure.

Some easy other constructions are related to subgroups of normed groups.
-/
noncomputable theory
open_locale nnreal big_operators

set_option old_structure_cmd true

/-- A morphism of normed abelian groups is a bounded group homomorphism. -/
structure normed_group_hom (V W : Type*) [normed_group V] [normed_group W] extends V →+ W :=
(bound' : ∃ C, ∀ v, ∥to_fun v∥ ≤ C * ∥v∥)

/-- Associate to a group homomorphism a bounded group homomorphism under a norm control condition.
-/
def add_monoid_hom.mk_continuous {V W : Type*} [normed_group V] [normed_group W] (f : V →+ W)
  (C : ℝ) (h : ∀ v, ∥f v∥ ≤ C * ∥v∥) : normed_group_hom V W :=
{ bound' := ⟨C, h⟩, ..f }

attribute [nolint doc_blame] normed_group_hom.to_add_monoid_hom

lemma exists_pos_bound_of_bound {V W : Type*} [normed_group V] [normed_group W]
  {f : V → W} (M : ℝ) (h : ∀x, ∥f x∥ ≤ M * ∥x∥) :
  ∃ N, 0 < N ∧ ∀x, ∥f x∥ ≤ N * ∥x∥ :=
⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), λx, calc
  ∥f x∥ ≤ M * ∥x∥ : h x
  ... ≤ max M 1 * ∥x∥ : mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _) ⟩

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
  rcases exists_pos_bound_of_bound _ hC with ⟨C', C'pos, hC'⟩,
  exact ⟨⟨C', C'pos.le⟩, C'pos, hC'⟩,
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

/-! ### The operator norm -/

/-- The operator norm of a normed group homomorphism is the inf of all its bounds. -/
def op_norm (f : normed_group_hom V₁ V₂) := Inf {c | 0 ≤ c ∧ ∀ x, ∥f x∥ ≤ c * ∥x∥}
instance has_op_norm : has_norm (normed_group_hom V₁ V₂) := ⟨op_norm⟩

lemma norm_def : ∥f∥ = Inf {c | 0 ≤ c ∧ ∀ x, ∥f x∥ ≤ c * ∥x∥} := rfl

-- So that invocations of `real.Inf_le` make sense: we show that the set of
-- bounds is nonempty and bounded below.
lemma bounds_nonempty {f : normed_group_hom V₁ V₂} :
  ∃ c, c ∈ { c | 0 ≤ c ∧ ∀ x, ∥f x∥ ≤ c * ∥x∥ } :=
let ⟨M, hMp, hMb⟩ := f.bound in ⟨M, le_of_lt hMp, hMb⟩

lemma bounds_bdd_below {f : normed_group_hom V₁ V₂} :
  bdd_below { c | 0 ≤ c ∧ ∀ x, ∥f x∥ ≤ c * ∥x∥ } :=
⟨0, λ _ ⟨hn, _⟩, hn⟩

lemma op_norm_nonneg : 0 ≤ ∥f∥ :=
real.lb_le_Inf _ bounds_nonempty (λ _ ⟨hx, _⟩, hx)

/-- The fundamental property of the operator norm: `∥f x∥ ≤ ∥f∥ * ∥x∥`. -/
theorem le_op_norm (x : V₁) : ∥f x∥ ≤ ∥f∥ * ∥x∥ :=
classical.by_cases
  (λ heq : x = 0, by { rw heq, simp })
  (λ hne, have hlt : 0 < ∥x∥, from norm_pos_iff.2 hne,
    (div_le_iff hlt).mp ((real.le_Inf _ bounds_nonempty bounds_bdd_below).2
    (λ c ⟨_, hc⟩, (div_le_iff hlt).mpr $ by { apply hc })))

theorem le_op_norm_of_le {c : ℝ} {x} (h : ∥x∥ ≤ c) : ∥f x∥ ≤ ∥f∥ * c :=
le_trans (f.le_op_norm x) (mul_le_mul_of_nonneg_left h f.op_norm_nonneg)

theorem le_of_op_norm_le {c : ℝ} (h : ∥f∥ ≤ c) (x : V₁) : ∥f x∥ ≤ c * ∥x∥ :=
(f.le_op_norm x).trans (mul_le_mul_of_nonneg_right h (norm_nonneg x))

/-- continuous linear maps are Lipschitz continuous. -/
theorem lipschitz : lipschitz_with ⟨∥f∥, op_norm_nonneg f⟩ f :=
lipschitz_with.of_dist_le_mul $ λ x y,
  by { rw [dist_eq_norm, dist_eq_norm, ←map_sub], apply le_op_norm }

lemma ratio_le_op_norm (x : V₁) : ∥f x∥ / ∥x∥ ≤ ∥f∥ :=
div_le_of_nonneg_of_le_mul (norm_nonneg _) f.op_norm_nonneg (le_op_norm _ _)

/-- If one controls the norm of every `f x`, then one controls the norm of `f`. -/
lemma op_norm_le_bound {M : ℝ} (hMp: 0 ≤ M) (hM : ∀ x, ∥f x∥ ≤ M * ∥x∥) :
  ∥f∥ ≤ M :=
real.Inf_le _ bounds_bdd_below ⟨hMp, hM⟩

theorem op_norm_le_of_lipschitz {f : normed_group_hom V₁ V₂} {K : ℝ≥0} (hf : lipschitz_with K f) :
  ∥f∥ ≤ K :=
f.op_norm_le_bound K.2 $ λ x, by simpa only [dist_zero_right, f.map_zero] using hf.dist_le_mul x 0

/-- If a bounded group homomorphism map is constructed from a group homomorphism via the constructor
`mk_continuous`, then its norm is bounded by the bound given to the constructor if it is
nonnegative. -/
lemma mk_continuous_norm_le (f : V₁ →+ V₂) {C : ℝ} (hC : 0 ≤ C) (h : ∀x, ∥f x∥ ≤ C * ∥x∥) :
  ∥f.mk_continuous C h∥ ≤ C :=
op_norm_le_bound _ hC h

/-- If a bounded group homomorphism map is constructed from a group homomorphism via the constructor
`mk_continuous`, then its norm is bounded by the bound given to the constructor or zero if this
bound is negative. -/
lemma mk_continuous_norm_le' (f : V₁ →+ V₂) {C : ℝ} (h : ∀x, ∥f x∥ ≤ C * ∥x∥) :
  ∥f.mk_continuous C h∥ ≤ max C 0 :=
op_norm_le_bound _ (le_max_right _ _) $ λ x, (h x).trans $
  mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg x)

alias mk_continuous_norm_le ← add_monoid_hom.mk_continuous_norm_le
alias mk_continuous_norm_le' ← add_monoid_hom.mk_continuous_norm_le'

/-! ### Addition of normed group homs -/

/-- Addition of normed group homs. -/
instance : has_add (normed_group_hom V₁ V₂) :=
⟨λ f g, (f.to_add_monoid_hom + g.to_add_monoid_hom).mk_continuous (∥f∥ + ∥g∥) $ λ v, calc
  ∥f v + g v∥
      ≤ ∥f v∥ + ∥g v∥ : norm_add_le _ _
  ... ≤ ∥f∥ * ∥v∥ + ∥g∥ * ∥v∥ : add_le_add (le_op_norm f v) (le_op_norm g v)
  ... = (∥f∥ + ∥g∥) * ∥v∥ : by rw add_mul⟩

/-- The operator norm satisfies the triangle inequality. -/
theorem op_norm_add_le : ∥f + g∥ ≤ ∥f∥ + ∥g∥ :=
mk_continuous_norm_le _ (add_nonneg (op_norm_nonneg _) (op_norm_nonneg _)) _

@[simp] lemma coe_add (f g : normed_group_hom V₁ V₂) : ⇑(f + g) = f + g := rfl
lemma add_apply (f g : normed_group_hom V₁ V₂) (v : V₁) :
  ((f + g : normed_group_hom V₁ V₂)) v = f v + g v := rfl

/-! ### The zero normed group hom -/

instance : has_zero (normed_group_hom V₁ V₂) :=
⟨(0 : V₁ →+ V₂).mk_continuous 0 (by simp)⟩

instance : inhabited (normed_group_hom V₁ V₂) := ⟨0⟩

/-- An operator is zero iff its norm vanishes. -/
theorem op_norm_zero_iff : ∥f∥ = 0 ↔ f = 0 :=
iff.intro
  (λ hn, ext (λ x, norm_le_zero_iff.1
    (calc _ ≤ ∥f∥ * ∥x∥ : le_op_norm _ _
     ...     = _ : by rw [hn, zero_mul])))
  (λ hf, le_antisymm (real.Inf_le _ bounds_bdd_below
    ⟨ge_of_eq rfl, λ _, le_of_eq (by { rw [zero_mul, hf], exact norm_zero })⟩)
    (op_norm_nonneg _))

@[simp] lemma coe_zero : ⇑(0 : normed_group_hom V₁ V₂) = 0 := rfl
lemma zero_apply (v : V₁) : ((0 : normed_group_hom V₁ V₂)) v = 0 := rfl

variables {f g}

/-! ### The identity normed group hom -/

/-- The identity as a continuous normed group hom. -/
@[simps]
def id : normed_group_hom V V :=
(add_monoid_hom.id V).mk_continuous 1 (by simp [le_refl])

/-- The norm of the identity is at most `1`. It is in fact `1`, except when the space is trivial
where it is `0`. It means that one can not do better than an inequality in general. -/
lemma norm_id_le : ∥(id : normed_group_hom V V)∥ ≤ 1 :=
op_norm_le_bound _ zero_le_one (λx, by simp)

/-- If a space is non-trivial, then the norm of the identity equals `1`. -/
lemma norm_id [nontrivial V] : ∥(id : normed_group_hom V V)∥ = 1 :=
le_antisymm norm_id_le $ let ⟨x, hx⟩ := exists_ne (0 : V) in
have _ := (id : normed_group_hom V V).ratio_le_op_norm x,
by rwa [id_apply, div_self (ne_of_gt $ norm_pos_iff.2 hx)] at this

/-! ### The negation of a normed group hom -/

/-- Opposite of a normed group hom. -/
instance : has_neg (normed_group_hom V₁ V₂) :=
⟨λ f, (-f.to_add_monoid_hom).mk_continuous (∥f∥) (λ v, by simp [le_op_norm f v])⟩

@[simp] lemma coe_neg (f : normed_group_hom V₁ V₂) : ⇑(-f) = -f := rfl
lemma neg_apply (f : normed_group_hom V₁ V₂) (v : V₁) :
  ((-f : normed_group_hom V₁ V₂)) v = - (f v) := rfl

lemma op_norm_neg (f : normed_group_hom V₁ V₂) : ∥-f∥ = ∥f∥ :=
by simp only [norm_def, coe_neg, norm_neg, pi.neg_apply]

/-! ### Subtraction of normed group homs -/

/-- Subtraction of normed group homs. -/
instance : has_sub (normed_group_hom V₁ V₂) :=
⟨λ f g,
{ bound' :=
  begin
    simp only [add_monoid_hom.sub_apply, add_monoid_hom.to_fun_eq_coe, sub_eq_add_neg],
    exact (f + -g).bound'
  end,
  .. (f.to_add_monoid_hom - g.to_add_monoid_hom) }⟩

@[simp] lemma coe_sub (f g : normed_group_hom V₁ V₂) : ⇑(f - g) = f - g := rfl
@[simp] lemma sub_apply (f g : normed_group_hom V₁ V₂) (v : V₁) :
  ((f - g : normed_group_hom V₁ V₂)) v = f v - g v := rfl

/-! ### Normed group structure on normed group homs -/

/-- Homs between two given normed groups form a commutative additive group. -/
instance : add_comm_group (normed_group_hom V₁ V₂) :=
by refine_struct
{ .. normed_group_hom.has_add, .. normed_group_hom.has_zero,
  .. normed_group_hom.has_neg, ..normed_group_hom.has_sub };
{ intros, ext, simp [add_assoc, add_comm, add_left_comm, sub_eq_add_neg] }

/-- Normed group homomorphisms themselves form a normed group with respect to
    the operator norm. -/
instance to_normed_group : normed_group (normed_group_hom V₁ V₂) :=
normed_group.of_core _ ⟨op_norm_zero_iff, op_norm_add_le, op_norm_neg⟩

/-- Coercion of a `normed_group_hom` is an `add_monoid_hom`. Similar to `add_monoid_hom.coe_fn` -/
@[simps]
def coe_fn_add_hom : normed_group_hom V₁ V₂ →+ (V₁ → V₂) :=
{ to_fun := coe_fn, map_zero' := coe_zero, map_add' := coe_add}

@[simp] lemma coe_sum {ι : Type*} (s : finset ι) (f : ι → normed_group_hom V₁ V₂) :
  ⇑(∑ i in s, f i) = ∑ i in s, (f i) :=
(coe_fn_add_hom : _ →+ (V₁ → V₂)).map_sum f s

lemma sum_apply {ι : Type*} (s : finset ι) (f : ι → normed_group_hom V₁ V₂) (v : V₁) :
  (∑ i in s, f i) v = ∑ i in s, (f i v) :=
by simp only [coe_sum, finset.sum_apply]

/-! ### Composition of normed group homs -/

/-- The composition of continuous normed group homs. -/
@[simps]
protected def comp (g : normed_group_hom V₂ V₃) (f : normed_group_hom V₁ V₂) :
  normed_group_hom V₁ V₃ :=
(g.to_add_monoid_hom.comp f.to_add_monoid_hom).mk_continuous (∥g∥ * ∥f∥) $ λ v, calc
∥g (f v)∥ ≤ ∥g∥ * ∥f v∥ : le_op_norm _ _
... ≤ ∥g∥ * (∥f∥ * ∥v∥) : mul_le_mul_of_nonneg_left (le_op_norm _ _) (op_norm_nonneg _)
... = ∥g∥ * ∥f∥ * ∥v∥   : by rw mul_assoc

lemma norm_comp_le (g : normed_group_hom V₂ V₃) (f : normed_group_hom V₁ V₂) :
  ∥g.comp f∥ ≤ ∥g∥ * ∥f∥ :=
mk_continuous_norm_le _ (mul_nonneg (op_norm_nonneg _) (op_norm_nonneg _)) _

/-- Composition of normed groups hom as an additive group morphism. -/
def comp_hom : (normed_group_hom V₂ V₃) →+ (normed_group_hom V₁ V₂) →+ (normed_group_hom V₁ V₃) :=
add_monoid_hom.mk' (λ g, add_monoid_hom.mk' (λ f, g.comp f)
  (by { intros, ext, exact g.map_add _ _ }))
  (by { intros, ext, simp only [comp_apply, pi.add_apply, function.comp_app,
                                add_monoid_hom.add_apply, add_monoid_hom.coe_mk', coe_add] })

@[simp] lemma comp_zero (f : normed_group_hom V₂ V₃) : f.comp (0 : normed_group_hom V₁ V₂) = 0 :=
by { ext, exact f.map_zero' }

@[simp] lemma zero_comp (f : normed_group_hom V₁ V₂) : (0 : normed_group_hom V₂ V₃).comp f = 0 :=
by { ext, refl }

end normed_group_hom

namespace normed_group_hom

/-!### Kernel -/
section kernels

variables {V V₁ V₂ V₃ : Type*}
variables [normed_group V] [normed_group V₁] [normed_group V₂] [normed_group V₃]
variables (f : normed_group_hom V₁ V₂) (g : normed_group_hom V₂ V₃)

/-- The kernel of a bounded group homomorphism. Naturally endowed with a `normed_group` instance. -/
def ker : add_subgroup V₁ := f.to_add_monoid_hom.ker

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

/-! ### Range -/
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

/-- A isometry `normed_group_hom` is a `normed_group_hom` that preserves the norm. -/
def is_isometry (f : normed_group_hom V W) : Prop :=
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

namespace is_isometry

lemma injective (hf : f.is_isometry) :
  function.injective f :=
begin
  intros x y h,
  rw ← sub_eq_zero at *,
  suffices : ∥ x - y ∥ = 0, by simpa,
  rw ← hf,
  simpa,
end

lemma norm_noninc (hf : f.is_isometry) : f.norm_noninc :=
λ v, le_of_eq $ hf v

lemma bound_by_one (hf : f.is_isometry) : f.bound_by 1 :=
hf.norm_noninc.bound_by_one

lemma id : (id : normed_group_hom V V).is_isometry :=
λ v, rfl

lemma comp {g : normed_group_hom V₂ V₃} {f : normed_group_hom V₁ V₂}
  (hg : g.is_isometry) (hf : f.is_isometry) :
  (g.comp f).is_isometry :=
λ v, (hg (f v)).trans (hf v)

end is_isometry

end normed_group_hom
