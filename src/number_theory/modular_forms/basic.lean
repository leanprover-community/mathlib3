/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import geometry.manifold.mfderiv
import analysis.complex.upper_half_plane.functions_bounded_at_infty
import analysis.complex.upper_half_plane.topology
import number_theory.modular_forms.slash_invariant_forms
import ring_theory.graded_algebra.basic
/-!
# Modular forms

This file defines modular forms and proves some basic properties about them.

We begin by defining modular forms and cusp forms as extension of `slash_invariant_forms` then we
define the space of modular forms, cusp forms and prove that the product of two modular forms is a
modular form.
-/

open complex upper_half_plane

open_locale topological_space manifold upper_half_plane

noncomputable theory

instance upper_half_plane.charted_space : charted_space ℂ ℍ :=
upper_half_plane.open_embedding_coe.singleton_charted_space

instance upper_half_plane.smooth_manifold_with_corners : smooth_manifold_with_corners 𝓘(ℂ) ℍ :=
upper_half_plane.open_embedding_coe.singleton_smooth_manifold_with_corners 𝓘(ℂ)

local prefix `↑ₘ`:1024 := @coe _ (matrix (fin 2) (fin 2) _) _

local notation `GL(` n `, ` R `)`⁺ := matrix.GL_pos (fin n) R

local notation `SL(` n `, ` R `)` := matrix.special_linear_group (fin n) R

section modular_form

open modular_form

variables (F : Type*) (Γ : subgroup SL(2, ℤ)) (k : ℤ)

local notation f `∣[`:73 k:0, A `]` :72 := slash_action.map ℂ k A f

set_option old_structure_cmd true

/--These are `slash_invariant_form`'s that are holomophic and bounded at infinity. -/
structure modular_form extends slash_invariant_form Γ k :=
(hol' : mdifferentiable 𝓘(ℂ) 𝓘(ℂ) (to_fun : ℍ → ℂ))
(bdd_at_infty' : ∀ (A : SL(2, ℤ)), is_bounded_at_im_infty (to_fun ∣[k, A]))

/-- The `slash_invariant_form` associated to a `modular_form`. -/
add_decl_doc modular_form.to_slash_invariant_form

/--These are `slash_invariant_form`s that are holomophic and zero at infinity. -/
structure cusp_form extends slash_invariant_form Γ k :=
(hol' : mdifferentiable 𝓘(ℂ) 𝓘(ℂ) (to_fun : ℍ → ℂ))
(zero_at_infty' : ∀ (A : SL(2, ℤ)), is_zero_at_im_infty (to_fun ∣[k, A]))

/-- The `slash_invariant_form` associated to a `cusp_form`. -/
add_decl_doc cusp_form.to_slash_invariant_form

/--`modular_form_class F Γ k` says that `F` is a type of bundled functions that extend
`slash_invariant_forms_class` by requiring that the functions be holomorphic and bounded
at infinity. -/
class modular_form_class extends slash_invariant_form_class F Γ k :=
(hol : ∀ f : F, mdifferentiable 𝓘(ℂ) 𝓘(ℂ) (f : ℍ → ℂ))
(bdd_at_infty : ∀ (f : F) (A : SL(2, ℤ)), is_bounded_at_im_infty (f ∣[k, A]))

/--`cusp_form_class F Γ k` says that `F` is a type of bundled functions that extend
`slash_invariant_forms_class` by requiring that the functions be holomorphic and zero
at infinity. -/
class cusp_form_class extends slash_invariant_form_class F Γ k :=
(hol : ∀ f : F, mdifferentiable 𝓘(ℂ) 𝓘(ℂ) (f : ℍ → ℂ))
(zero_at_infty : ∀ (f : F) (A : SL(2, ℤ)), is_zero_at_im_infty (f ∣[k, A]))

@[priority 100]
instance modular_form_class.modular_form : modular_form_class (modular_form Γ k) Γ k :=
{ coe := modular_form.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  slash_action_eq := modular_form.slash_action_eq',
  hol := modular_form.hol',
  bdd_at_infty := modular_form.bdd_at_infty' }

@[priority 100]
instance cusp_form_class.cusp_form : cusp_form_class (cusp_form Γ k) Γ k :=
{ coe := cusp_form.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  slash_action_eq := cusp_form.slash_action_eq',
  hol := cusp_form.hol',
  zero_at_infty := cusp_form.zero_at_infty' }

variables {F Γ k}

@[simp] lemma modular_form_to_fun_eq_coe {f : modular_form Γ k} : f.to_fun = (f : ℍ → ℂ) := rfl
@[simp] lemma cusp_form_to_fun_eq_coe {f : cusp_form Γ k} : f.to_fun = (f : ℍ → ℂ) := rfl

@[ext] theorem modular_form.ext {f g : modular_form Γ k} (h : ∀ x, f x = g x) : f = g :=
fun_like.ext f g h

@[ext] theorem cusp_form.ext {f g : cusp_form Γ k} (h : ∀ x, f x = g x) : f = g :=
fun_like.ext f g h

/-- Copy of a `modular_form` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def modular_form.copy (f : modular_form Γ k) (f' : ℍ → ℂ) (h : f' = ⇑f) :
  modular_form Γ k :=
{ to_fun := f',
  slash_action_eq' := h.symm ▸ f.slash_action_eq',
  hol' := h.symm ▸ f.hol',
  bdd_at_infty' := λ A, h.symm ▸ f.bdd_at_infty' A }

/-- Copy of a `cusp_form` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def cusp_form.copy (f : cusp_form Γ k) (f' : ℍ → ℂ) (h : f' = ⇑f) :
  cusp_form Γ k :=
{ to_fun := f',
  slash_action_eq' := h.symm ▸ f.slash_action_eq',
  hol' := h.symm ▸ f.hol',
  zero_at_infty' := λ A, h.symm ▸ f.zero_at_infty' A }

end modular_form

namespace modular_form

open slash_invariant_form

variables {F : Type*} {Γ : subgroup SL(2, ℤ)} {k : ℤ}

instance has_add : has_add (modular_form Γ k) :=
⟨ λ f g,
  { hol' := f.hol'.add g.hol',
    bdd_at_infty' := λ A, by simpa using (f.bdd_at_infty' A).add (g.bdd_at_infty' A),
    .. (f : slash_invariant_form Γ k) + g }⟩

@[simp] lemma coe_add (f g : modular_form Γ k) : ⇑(f + g) = f + g := rfl

@[simp] lemma add_apply (f g : modular_form Γ k) (z : ℍ) : (f + g) z = f z + g z := rfl

instance has_zero : has_zero (modular_form Γ k) :=
⟨ { hol' := (λ _, mdifferentiable_at_const 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)),
    bdd_at_infty' := λ A, by simpa using zero_form_is_bounded_at_im_infty,
    .. (0 : slash_invariant_form Γ k) } ⟩

@[simp] lemma coe_zero : ⇑(0 : modular_form Γ k) = (0 : ℍ → ℂ) := rfl

@[simp] lemma zero_apply (z : ℍ) : (0 : modular_form Γ k) z = 0 := rfl

section
variables {α : Type*} [has_smul α ℂ] [is_scalar_tower α ℂ ℂ]

instance has_smul : has_smul α (modular_form Γ k) :=
⟨ λ c f,
  { to_fun := c • f,
    hol' := by simpa using f.hol'.const_smul (c • (1 : ℂ)),
    bdd_at_infty' := λ A, by simpa using (f.bdd_at_infty' A).const_smul_left (c • (1 : ℂ)),
     .. c • (f : slash_invariant_form Γ k)}⟩

@[simp] lemma coe_smul (f : (modular_form Γ k)) (n : α) : ⇑(n • f) = n • f := rfl
@[simp] lemma smul_apply (f : (modular_form Γ k)) (n : α) (z : ℍ) :
   (n • f) z = n • (f z) := rfl
end

instance has_neg : has_neg (modular_form Γ k) :=
⟨λ f,
  { to_fun := -f,
    hol' := f.hol'.neg,
    bdd_at_infty':= λ A, by simpa using (f.bdd_at_infty' A).neg,
    .. -(f : slash_invariant_form Γ k) }⟩

@[simp] lemma coe_neg (f : modular_form Γ k) : ⇑(-f) = -f := rfl

@[simp] lemma neg_apply (f : modular_form Γ k) (z : ℍ) : (-f) z = - (f z) := rfl

instance has_sub : has_sub (modular_form Γ k) :=
⟨ λ f g, f + -g ⟩

@[simp] lemma coe_sub (f g : (modular_form Γ k)) : ⇑(f - g) = f - g := rfl

@[simp] lemma sub_apply (f g : modular_form Γ k) (z : ℍ) : (f - g) z = f z - g z := rfl

instance : add_comm_group (modular_form Γ k) :=
fun_like.coe_injective.add_comm_group _ rfl coe_add coe_neg coe_sub coe_smul coe_smul

/--Additive coercion from `modular_form` to `ℍ → ℂ`. -/
@[simps] def coe_hom : (modular_form Γ k) →+ (ℍ → ℂ) :=
{ to_fun := λ f, f,
  map_zero' := coe_zero,
  map_add' := λ _ _, rfl }

instance : module ℂ (modular_form Γ k) :=
function.injective.module ℂ coe_hom fun_like.coe_injective (λ _ _, rfl)

instance : inhabited (modular_form Γ k) := ⟨0⟩

/--The modular form of weight `k_1 + k_2` given by the product of two modular forms of weights
`k_1` and `k_2`. -/
def mul {k_1 k_2 : ℤ} {Γ : subgroup SL(2, ℤ)} (f : (modular_form Γ k_1))
  (g : (modular_form Γ k_2)) : (modular_form Γ (k_1 + k_2)) :=
{ to_fun := f * g,
  slash_action_eq' := λ A, by simp_rw [mul_slash_subgroup, modular_form_class.slash_action_eq],
  hol' := f.hol'.mul g.hol',
  bdd_at_infty' := λ A, by simpa using (f.bdd_at_infty' A).mul (g.bdd_at_infty' A) }

@[simp] lemma mul_coe {k_1 k_2 : ℤ} {Γ : subgroup SL(2, ℤ)} (f : (modular_form Γ k_1))
  (g : (modular_form Γ k_2)) : ((f.mul g) : ℍ → ℂ) = f * g := rfl

instance : has_one (modular_form Γ 0) :=
⟨{  hol' := λ x, mdifferentiable_at_const 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ),
    bdd_at_infty' := λ A, by simpa using at_im_infty.const_bounded_at_filter (1:ℂ),
      .. (1 : slash_invariant_form Γ 0) }⟩

@[simp] lemma one_coe_eq_one : ((1 : modular_form Γ 0) : ℍ → ℂ) = 1 := rfl

def mcast {a b : ℤ} {Γ : subgroup SL(2, ℤ)} (h : a = b) (f : modular_form Γ a) :
  (modular_form Γ b) :=
{ to_fun := (f : ℍ → ℂ),
  slash_action_eq' := by {intro A, have := f.slash_action_eq' A, convert this, exact h.symm,},
  hol' := f.hol',
  bdd_at_infty' := by {intro A, convert f.bdd_at_infty' A, exact h.symm }}

lemma type_eq {a b : ℤ} (Γ : subgroup SL(2, ℤ)) (h : a = b) :
  (modular_form Γ a) = (modular_form Γ b) :=
begin
  induction h,
  refl,
end

lemma cast_eq_mcast {a b : ℤ} {Γ : subgroup SL(2, ℤ)} (h : a = b) (f : modular_form Γ a) :
  cast (type_eq Γ h) f = mcast h f :=
begin
  induction h,
  ext1,
  refl,
end

lemma heq_one_mul (k : ℤ) {Γ : subgroup SL(2, ℤ)} (f : modular_form Γ k) :
  (1 : modular_form Γ 0).mul f == f :=
begin
   apply heq_of_cast_eq (type_eq Γ (zero_add k).symm).symm,
    funext,
    rw [cast_eq_mcast, mcast, mul],
    simp only [one_coe_eq_one, one_mul],
    ext1,
    refl,
    simp only [zero_add]
end

lemma heq_mul_one (k : ℤ) {Γ : subgroup SL(2, ℤ)} (f : modular_form Γ k) :
  f.mul (1 : modular_form Γ 0) == f :=
begin
      apply heq_of_cast_eq (type_eq Γ (add_zero k).symm).symm,
      funext,
      rw [cast_eq_mcast, mcast, mul],
      simp only [one_coe_eq_one, mul_one],
      ext1,
      refl,
      simp only [add_zero]
end

lemma heq_mul_assoc {a b c : ℤ} (f : modular_form Γ a) (g : modular_form Γ b)
  (h : modular_form Γ c) : (f.mul g).mul h ==  f.mul (g.mul h) :=
begin
  apply heq_of_cast_eq (type_eq Γ (add_assoc a b c)),
  rw [cast_eq_mcast, mcast],
  ext1,
  simp only [mul_coe, pi.mul_apply, ←mul_assoc],
  refl,
end

lemma heq_mul_comm (a b : ℤ) (f : modular_form Γ a) (g : modular_form Γ b) : f.mul g == g.mul f :=
begin
  apply heq_of_cast_eq (type_eq Γ (add_comm a b)),
  rw [cast_eq_mcast, mcast],
  ext1,
  simp only [mul_coe, pi.mul_apply, mul_comm],
  refl,
end

instance graded_mod_ring (Γ : subgroup SL(2, ℤ)) : direct_sum.gcomm_ring (λ k, modular_form Γ k) :={
  mul := λ k_1, λ k_2, λ f g, f.mul g,
  one := 1,
  one_mul := by {intro f,
    rw [graded_monoid.ghas_one.to_has_one, graded_monoid.ghas_mul.to_has_mul],
    apply sigma.ext,
    { simp only [zero_add] },
    { simp only [submodule.coe_mk, one_mul, heq_one_mul] }},
  mul_one := by {intro f,
    rw [graded_monoid.ghas_one.to_has_one, graded_monoid.ghas_mul.to_has_mul],
    apply sigma.ext,
    { simp only [add_zero] },
    { simp only [submodule.coe_mk, mul_one, heq_mul_one]}},
  mul_assoc := by {intros f g h,
    rw graded_monoid.ghas_mul.to_has_mul,
    apply sigma.ext,
    { apply add_assoc },
    { simp only [submodule.coe_mk, heq_mul_assoc] }},
  mul_zero := by {intros i j f, ext1, simp,},
  zero_mul := by {intros i j f, ext1, simp,},
  mul_add := by {intros i j f g h,
    ext1,
    simp only [pi.mul_apply, mul_add, mul_coe, add_apply],},
  add_mul := by {intros i j f g h,
    ext1,
    simp only [add_mul, mul_coe, pi.mul_apply, add_apply],},
  mul_comm := by {intros f g,
    rw graded_monoid.ghas_mul.to_has_mul,
    apply sigma.ext,
    { apply add_comm },
    { apply heq_mul_comm }},
  gnpow_zero' := by {intro f,
    apply sigma.ext,
    repeat {refl}},
  gnpow_succ' := by {intros n f,
    rw graded_monoid.ghas_mul.to_has_mul,
    apply sigma.ext,
    repeat {refl}},
  nat_cast := λ n, n • (1 : (modular_form Γ 0)),
  nat_cast_zero := by {simp},
  nat_cast_succ := by {intro n, simp only [add_smul, one_nsmul, add_right_inj], refl,},
  int_cast := λ n, n • (1 : (modular_form Γ 0)),
  int_cast_of_nat := by {simp},
  int_cast_neg_succ_of_nat := by {intro , apply _root_.neg_smul }}

end modular_form

namespace cusp_form
open modular_form

variables {F : Type*} {Γ : subgroup SL(2, ℤ)} {k : ℤ}

instance has_add : has_add (cusp_form Γ k) :=
⟨ λ f g,
  { to_fun := f + g,
    hol' := f.hol'.add g.hol',
    zero_at_infty' := λ A, by simpa using (f.zero_at_infty' A).add (g.zero_at_infty' A),
    .. (f : slash_invariant_form Γ k) + g }⟩

@[simp] lemma coe_add (f g : cusp_form Γ k) : ⇑(f + g) = f + g := rfl

@[simp] lemma add_apply (f g : cusp_form Γ k) (z : ℍ) : (f + g) z = f z + g z := rfl

instance has_zero : has_zero (cusp_form Γ k) :=
⟨ { to_fun := 0,
    hol' := (λ _, mdifferentiable_at_const 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)),
    zero_at_infty' := by simpa using filter.zero_zero_at_filter _,
    .. (0 : slash_invariant_form Γ k) }⟩

@[simp] lemma coe_zero : ⇑(0 : cusp_form Γ k) = (0 : ℍ → ℂ) := rfl

@[simp] lemma zero_apply (z : ℍ) : (0 : cusp_form Γ k) z = 0 := rfl

section
variables {α : Type*} [has_smul α ℂ] [is_scalar_tower α ℂ ℂ]

instance has_smul : has_smul α (cusp_form Γ k) :=
⟨ λ c f,
  { to_fun := c • f,
    hol' := by simpa using f.hol'.const_smul (c • (1 : ℂ)),
    zero_at_infty' := λ A, by simpa using (f.zero_at_infty' A).smul (c • (1 : ℂ)),
    .. c • (f : slash_invariant_form Γ k) }⟩

@[simp] lemma coe_smul (f : (cusp_form Γ k)) (n : α) : ⇑(n • f) = n • f := rfl
@[simp] lemma smul_apply (f : (cusp_form Γ k)) (n : α) {z : ℍ} :
   (n • f) z = n • (f z) := rfl

end

instance has_neg : has_neg (cusp_form Γ k) :=
⟨λ f,
  { to_fun := -f,
    hol' := f.hol'.neg,
    zero_at_infty':= λ A, by simpa using (f.zero_at_infty' A).neg,
    .. -(f : slash_invariant_form Γ k)} ⟩

@[simp] lemma coe_neg (f : cusp_form Γ k) : ⇑(-f) = -f := rfl
@[simp] lemma neg_apply (f : cusp_form Γ k) (z : ℍ) : (-f) z = -(f z) := rfl

instance has_sub : has_sub (cusp_form Γ k) :=
⟨ λ f g, f + -g ⟩

@[simp] lemma coe_sub (f g : cusp_form Γ k) : ⇑(f - g) = f - g := rfl
@[simp] lemma sub_apply (f g : cusp_form Γ k) (z : ℍ) : (f - g) z = f z - g z := rfl

instance : add_comm_group (cusp_form Γ k) :=
fun_like.coe_injective.add_comm_group _ rfl coe_add coe_neg coe_sub coe_smul coe_smul

/--Additive coercion from `cusp_form` to `ℍ → ℂ`. -/
@[simps] def coe_hom : (cusp_form Γ k) →+ (ℍ → ℂ) :=
{ to_fun := λ f, f,
  map_zero' := cusp_form.coe_zero,
  map_add' := λ _ _, rfl }

instance : module ℂ (cusp_form Γ k) :=
function.injective.module ℂ coe_hom fun_like.coe_injective (λ _ _, rfl)

instance : inhabited (cusp_form Γ k) := ⟨0⟩

@[priority 99]
instance [cusp_form_class F Γ k] : modular_form_class F Γ k :=
{ coe := fun_like.coe,
  coe_injective' := fun_like.coe_injective',
  slash_action_eq := cusp_form_class.slash_action_eq,
  hol := cusp_form_class.hol,
  bdd_at_infty := λ _ _, (cusp_form_class.zero_at_infty _ _).bounded_at_filter}

end cusp_form
