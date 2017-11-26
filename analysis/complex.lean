/-
Copyright (c) 2017 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kevin Buzzard

The complex numbers, modelled as R^2 in the obvious way.

TODO: Add topology, and prove that the complexes are a topological ring.
-/
import analysis.real
noncomputable theory

local attribute [instance] classical.decidable_inhabited classical.prop_decidable

structure complex : Type :=
(re : ℝ) (im : ℝ)

notation `ℂ` := complex

namespace complex

theorem eta (z : complex) : complex.mk z.re z.im = z :=
  cases_on z (λ _ _, rfl)

theorem eq_of_re_eq_and_im_eq (z w : complex) : z.re=w.re ∧ z.im=w.im → z=w :=
begin
intro H,rw [←eta z,←eta w,H.left,H.right],
end

-- simp version

theorem eq_iff_re_eq_and_im_eq (z w : complex) : z=w ↔ z.re=w.re ∧ z.im=w.im :=
begin
split,
  intro H,rw [H],split;trivial,
exact eq_of_re_eq_and_im_eq _ _,
end

lemma proj_re (r0 i0 : real) : (complex.mk r0 i0).re = r0 := rfl
lemma proj_im (r0 i0 : real) : (complex.mk r0 i0).im = i0 := rfl

local attribute [simp] eq_iff_re_eq_and_im_eq proj_re proj_im

def of_real : ℝ → ℂ := λ x, { re := x, im := 0 }

instance coe_real_complex : has_coe ℝ ℂ := ⟨of_real⟩
instance has_zero_complex : has_zero complex := ⟨of_real 0⟩
instance has_one_complex : has_one complex := ⟨of_real 1⟩
instance inhabited_complex : inhabited complex := ⟨0⟩

def I : complex := {re := 0, im := 1}

def conjugate (z : complex) : complex := {re := z.re, im := -(z.im)}

-- Are these supposed to be protected too?

protected def add : complex → complex → complex :=
λ z w, { re :=z.re+w.re, im:=z.im+w.im}

protected def neg : complex → complex :=
λ z, { re := -z.re, im := -z.im}

protected def mul : complex → complex → complex :=
λ z w, { re := z.re*w.re - z.im*w.im,
         im := z.re*w.im + z.im*w.re}

def norm_squared : complex → real :=
λ z, z.re*z.re+z.im*z.im

protected def inv : complex → complex :=
λ z,  { re := z.re / norm_squared z,
        im := -z.im / norm_squared z }

instance : has_add complex := ⟨complex.add⟩
instance : has_neg complex := ⟨complex.neg⟩
instance : has_mul complex := ⟨complex.mul⟩
instance : has_inv complex := ⟨complex.inv⟩

lemma proj_zero_re : (0:complex).re=0 := rfl
lemma proj_zero_im : (0:complex).im=0 := rfl
lemma proj_one_re : (1:complex).re=1 := rfl
lemma proj_one_im : (1:complex).im=0 := rfl
lemma proj_I_re : complex.I.re=0 := rfl
lemma proj_I_im : complex.I.im=1 := rfl
lemma proj_conj_re (z : complex) : (conjugate z).re = z.re := rfl
lemma proj_conj_im (z : complex) : (conjugate z).im = -z.im := rfl
lemma proj_add_re (z w: complex) : (z+w).re=z.re+w.re := rfl
lemma proj_add_im (z w: complex) : (z+w).im=z.im+w.im := rfl
lemma proj_add_re' (z w: complex) : (complex.add z w).re=z.re+w.re := rfl
lemma proj_add_im' (z w: complex) : (complex.add z w).im=z.im+w.im := rfl
lemma proj_add_re'' (z w: complex) : (has_add.add z w).re=z.re+w.re := rfl
lemma proj_add_im'' (z w: complex) : (has_add.add z w).im=z.im+w.im := rfl
lemma proj_neg_re (z: complex) : (-z).re=-z.re := rfl
lemma proj_neg_im (z: complex) : (-z).im=-z.im := rfl
lemma proj_neg_re' (z: complex) : (complex.neg z).re=-z.re := rfl
lemma proj_neg_im' (z: complex) : (complex.neg z).im=-z.im := rfl

local attribute [simp] proj_zero_re proj_zero_im proj_one_re proj_one_im
local attribute [simp] proj_I_re proj_I_im proj_conj_re proj_conj_im
local attribute [simp] proj_add_re proj_add_im proj_add_re' proj_add_im' proj_add_re'' proj_add_im''
local attribute [simp] proj_neg_re proj_neg_im proj_neg_re' proj_neg_im'

meta def crunch : tactic unit := do
`[intros],
`[rw [eq_iff_re_eq_and_im_eq]],
`[split;simp[add_mul,mul_add]]

instance : add_comm_group complex :=
{ add_comm_group .
  zero         := 0,
  add          := complex.add,
  neg          := complex.neg,
  zero_add     := by crunch,
  add_zero     := by crunch,
  add_comm     := by crunch,
  add_assoc    := by crunch,
  add_left_neg := by crunch
}

lemma proj_sub_re (z w : complex) : (z-w).re=z.re-w.re := rfl
lemma proj_sub_im (z w : complex) : (z-w).im=z.im-w.im := rfl
lemma proj_mul_re (z w: complex) : (z*w).re=z.re*w.re-z.im*w.im := rfl
lemma proj_mul_im (z w: complex) : (z*w).im=z.re*w.im+z.im*w.re := rfl
lemma proj_mul_re' (z w: complex) : (complex.mul z w).re=z.re*w.re-z.im*w.im := rfl
lemma proj_mul_im' (z w: complex) : (complex.mul z w).im=z.re*w.im+z.im*w.re := rfl
lemma proj_of_real_re (r:real) : (of_real r).re = r := rfl
lemma proj_of_real_im (r:real) : (of_real r).im = 0 := rfl
local attribute [simp] proj_sub_re proj_sub_im proj_of_real_re proj_of_real_im
local attribute [simp] proj_mul_re proj_mul_im proj_mul_re' proj_mul_im'

lemma norm_squared_pos_of_nonzero (z : complex) (H : z ≠ 0) : norm_squared z > 0 :=
begin -- far more painful than it should be but I need it for inverses
suffices : z.re ≠ 0 ∨ z.im ≠ 0,
  apply lt_of_le_of_ne,
    exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _),
  intro H2,
  cases this with Hre Him,
    exact Hre (eq_zero_of_mul_self_add_mul_self_eq_zero (eq.symm H2)),
  unfold norm_squared at H2,rw [add_comm] at H2,
  exact Him (eq_zero_of_mul_self_add_mul_self_eq_zero (eq.symm H2)),
have : ¬ (z.re = 0 ∧ z.im = 0),
  intro H2,
  exact H (eq_of_re_eq_and_im_eq z 0 H2),
cases classical.em (z.re = 0) with Hre_eq Hre_ne,
  right,
  intro H2,
  apply this,
  exact ⟨Hre_eq,H2⟩,
left,assumption,
end

lemma of_real_injective : function.injective of_real :=
begin
intros x₁ x₂ H,
exact congr_arg complex.re H,
end

lemma of_real_zero : of_real 0 = (0:complex) := rfl
lemma of_real_one : of_real 1 = (1:complex) := rfl

lemma of_real_neg (r : real) : -of_real r = of_real (-r) := by crunch

lemma of_real_add (r s: real) : of_real r + of_real s = of_real (r+s) := by crunch

lemma of_real_sub (r s:real) : of_real r - of_real s = of_real(r-s) := by crunch

lemma of_real_mul (r s:real) : of_real r * of_real s = of_real (r*s) := by crunch

lemma of_real_inv (r:real) : (of_real r)⁻¹ = of_real (r⁻¹) :=
begin
rw [eq_iff_re_eq_and_im_eq],
split,
  suffices : r/(r*r+0*0) = r⁻¹,
  exact this,
  cases classical.em (r=0) with Heq Hne,
  -- this is taking longer than it should be.
    rw [Heq],
    simp [inv_zero,div_zero],
  rw [mul_zero,add_zero,div_mul_left r Hne,inv_eq_one_div],
  suffices : -0/(r*r+0*0) = 0,
  exact this,
  rw [neg_zero,zero_div],
end

lemma of_real_abs_squared (r:real) : norm_squared (of_real r) = (abs r)*(abs r) :=
begin
rw [abs_mul_abs_self],
  suffices : r*r+0*0=r*r,
  exact this,
  simp,
end

instance : discrete_field complex :=
{ discrete_field .
  add              := (+),
  zero             := 0,
  neg          := complex.neg,
  zero_add     := by crunch,
  add_zero     := by crunch,
  add_comm     := by crunch,
  add_assoc    := by crunch,
  add_left_neg := by crunch,
  one              := 1,
  mul              := has_mul.mul,
  inv              := has_inv.inv,
  mul_one          := by crunch,
  one_mul          := by crunch,
  mul_comm         := by crunch,
  mul_assoc        := by crunch,
  left_distrib     := by crunch,
  right_distrib    := by crunch,
  zero_ne_one      := begin
    intro H,
    suffices : (0:complex).re = (1:complex).re,
      revert this,
      apply zero_ne_one,
    rw [←H],
    end,
  mul_inv_cancel   := begin
    intros z H,
    have H2 : norm_squared z ≠ 0 := ne_of_gt (norm_squared_pos_of_nonzero z H),
    apply eq_of_re_eq_and_im_eq,
    unfold has_inv.inv complex.inv,
    rw [proj_mul_re,proj_mul_im],
    split,
      suffices : z.re*(z.re/norm_squared z) + -z.im*(-z.im/norm_squared z) = 1,
        by simpa,
      rw [←mul_div_assoc,←mul_div_assoc,neg_mul_neg,div_add_div_same],
      unfold norm_squared at *,
      exact div_self H2,
    suffices : z.im * (z.re / norm_squared z) + z.re * (-z.im / norm_squared z) = 0,
      by simpa,
    rw [←mul_div_assoc,←mul_div_assoc,div_add_div_same],
    simp [zero_div],
  end,
  inv_mul_cancel   := begin -- let's try cut and pasting mul_inv_cancel proof
    intros z H,
    have H2 : norm_squared z ≠ 0 := ne_of_gt (norm_squared_pos_of_nonzero z H),
    apply eq_of_re_eq_and_im_eq,
    unfold has_inv.inv complex.inv,
    rw [proj_mul_re,proj_mul_im],
    split,
      suffices : z.re*(z.re/norm_squared z) + -z.im*(-z.im/norm_squared z) = 1,
        by simpa,
      rw [←mul_div_assoc,←mul_div_assoc,neg_mul_neg,div_add_div_same],
      unfold norm_squared at *,
      exact div_self H2,
    suffices : z.im * (z.re / norm_squared z) + z.re * (-z.im / norm_squared z) = 0,
      by simpa,
    rw [←mul_div_assoc,←mul_div_assoc,div_add_div_same],
    simp [zero_div],
  end, -- it worked without modification! 
  -- Presumably I could just have proved mul_comm outside the verification that C is a field
  -- and then used that too?
  inv_zero         := begin
  unfold has_inv.inv complex.inv add_comm_group.zero,
  apply eq_of_re_eq_and_im_eq,
  split;simp [zero_div],
  end,
  has_decidable_eq := by apply_instance,
  }

-- instance : topological_ring complex := missing

end complex

