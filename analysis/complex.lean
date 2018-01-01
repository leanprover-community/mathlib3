/-
Copyright (c) 2017 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kevin Buzzard

The complex numbers, modelled as R^2 in the obvious way.

TODO: Add topology, and prove that the complexes are a topological ring.
-/
import analysis.real
noncomputable theory

-- I have no idea about whether I should be proving that
-- C is a field or a discrete field. As far as I am personally
-- concerned these structures are the same. I have gone for
-- a field which enables me to comment out the next line.

--local attribute [instance] classical.decidable_inhabited classical.prop_decidable

structure complex : Type :=
(re : ℝ) (im : ℝ)

notation `ℂ` := complex

namespace complex

theorem eta (z : complex) : complex.mk z.re z.im = z :=
cases_on z (λ _ _, rfl)

theorem eq_of_re_eq_and_im_eq : ∀ (z w : complex), z.re=w.re → z.im=w.im → z=w
| ⟨zr, zi⟩ ⟨wr, wi⟩ rfl rfl := rfl


-- simp version

theorem eq_iff_re_eq_and_im_eq (z w : complex) : z=w ↔ z.re=w.re ∧ z.im=w.im :=
⟨λ H, ⟨by rw [H],by rw [H]⟩,λ H, eq_of_re_eq_and_im_eq _ _ H.left H.right⟩


--  begin
--split,
--  intro H,rw [H],split;trivial,
--exact eq_of_re_eq_and_im_eq _ _,
--end

lemma proj_re (r0 i0 : real) : (complex.mk r0 i0).re = r0 := rfl
lemma proj_im (r0 i0 : real) : (complex.mk r0 i0).im = i0 := rfl

local attribute [simp] eq_iff_re_eq_and_im_eq proj_re proj_im

def of_real (r : ℝ) : ℂ := { re := r, im := 0 }

protected def zero := of_real 0
protected def one := of_real 1

instance coe_real_complex : has_coe ℝ ℂ := ⟨of_real⟩
instance has_zero_complex : has_zero complex := ⟨complex.zero⟩
instance has_one_complex : has_one complex := ⟨complex.one⟩
instance inhabited_complex : inhabited complex := ⟨complex.zero⟩ 

@[simp] lemma coe_re (r:real) : ((↑r):complex).re = r := rfl
@[simp] lemma coe_im (r:real) : ((↑r):complex).im = 0 := rfl

def I : complex := {re := 0, im := 1}

def conjugate (z : complex) : complex := {re := z.re, im := -(z.im)}

def norm_squared : complex → real :=
λ z, z.re*z.re+z.im*z.im

protected def inv : complex → complex :=
λ z,  { re := z.re / norm_squared z,
        im := -z.im / norm_squared z }

instance : has_add complex := ⟨λ z w, { re :=z.re+w.re, im:=z.im+w.im}⟩
instance : has_neg complex := ⟨λ z, { re := -z.re, im := -z.im}⟩
instance : has_mul complex := ⟨λ z w, { re := z.re*w.re - z.im*w.im,
                                        im := z.re*w.im + z.im*w.re}⟩ 
instance : has_inv complex := ⟨λ z, { re := z.re / norm_squared z,
                                      im := -z.im / norm_squared z }⟩

@[simp] lemma zero_re : (0:complex).re=0 := rfl
@[simp] lemma zero_im : (0:complex).im=0 := rfl
@[simp] lemma one_re : (1:complex).re=1 := rfl
@[simp] lemma one_im : (1:complex).im=0 := rfl
@[simp] lemma I_re : complex.I.re=0 := rfl
@[simp] lemma I_im : complex.I.im=1 := rfl
@[simp] lemma conj_re (z : complex) : (conjugate z).re = z.re := rfl
@[simp] lemma conj_im (z : complex) : (conjugate z).im = -z.im := rfl
@[simp] lemma add_re (z w: complex) : (z+w).re=z.re+w.re := rfl
@[simp] lemma add_im (z w: complex) : (z+w).im=z.im+w.im := rfl
@[simp] lemma neg_re (z: complex) : (-z).re=-z.re := rfl
@[simp] lemma neg_im (z: complex) : (-z).im=-z.im := rfl

-- one size fits all tactic 

meta def crunch : tactic unit := do
`[intros],
`[rw [eq_iff_re_eq_and_im_eq]],
`[split;simp [add_mul,mul_add,mul_assoc]]

meta def crunch2 : tactic unit := do 
`[simp [add_mul, mul_add, eq_iff_re_eq_and_im_eq] {contextual:=tt}]


meta def crunch3 : tactic unit := do 
`[simp [add_mul, mul_add, mul_comm, mul_assoc, eq_iff_re_eq_and_im_eq] {contextual:=tt}]

instance : add_comm_group complex :=
{ add_comm_group .
  zero         := 0,
  add          := (+),
  neg          := has_neg.neg,
  zero_add     := by crunch,
  add_zero     := by crunch,
  add_comm     := by crunch,
  add_assoc    := by crunch,
  add_left_neg := by crunch
}

@[simp] lemma sub_re (z w : complex) : (z-w).re=z.re-w.re := rfl
@[simp] lemma sub_im (z w : complex) : (z-w).im=z.im-w.im := rfl
@[simp] lemma mul_re (z w: complex) : (z*w).re=z.re*w.re-z.im*w.im := rfl
@[simp] lemma mul_im (z w: complex) : (z*w).im=z.re*w.im+z.im*w.re := rfl


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
    exact H (eq_of_re_eq_and_im_eq z 0 H2.left H2.right),
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
lemma of_real_eq_coe (r : real) : of_real r = ↑r := rfl

lemma of_real_neg (r : real) : -(r:complex) = ((-r:ℝ):complex) := by crunch

lemma of_real_add (r s: real) : (r:complex) + (s:complex) = ((r+s):complex) := by crunch

lemma of_real_sub (r s:real) : (r:complex) - (s:complex) = ((r-s):complex) := by crunch

lemma of_real_mul (r s:real) : (r:complex) * (s:complex) = ((r*s):complex) := by crunch

lemma of_real_inv (r:real) : (r:complex)⁻¹ = ((r⁻¹):complex) :=
begin
rw [eq_iff_re_eq_and_im_eq],
split,
  unfold has_inv.inv,
  unfold has_inv.inv,
end

lemma of_real_abs_squared (r:real) : norm_squared (of_real r) = (abs r)*(abs r) :=
begin
rw [abs_mul_abs_self],
  suffices : r*r+0*0=r*r,
  exact this,
  simp,
end

#print field 

--set_option pp.all true
--set_option trace.simp_lemmas_cache true
instance : field complex :=
{ --field .
  add              := (+), -- I need this!
  zero             := 0, -- later crunch proofs won't work without these.
--  neg          := complex.neg,
--  zero_add     := by crunch,
--  add_zero     := by crunch,
--  add_comm     := by crunch,
--  add_assoc    := by crunch,
--  add_left_neg := by crunch,

  one              := 1,
  mul              := has_mul.mul,
  inv              := has_inv.inv,
  mul_one          := by crunch,
  one_mul          := by crunch,
  mul_comm         := by crunch3,
  mul_assoc        := by crunch,
  left_distrib := by begin
    intros,
    apply eq_of_re_eq_and_im_eq,
    { rw [mul_re,add_re,add_re,add_im,mul_re,mul_re],
    simp [add_mul,mul_add] },
    { rw [mul_im,add_re,add_im,add_im,mul_im,mul_im],
    simp [add_mul,mul_add] },
  end,
--  left_distrib     := by crunch,
  right_distrib    := by begin
    intros,
    apply eq_of_re_eq_and_im_eq,
    { rw [mul_re,add_re,add_re,add_im,mul_re,mul_re],
    simp [add_mul,mul_add] },
    { rw [mul_im,add_re,add_im,add_im,mul_im,mul_im],
    simp [add_mul,mul_add] },
  end,
  zero_ne_one      := begin
    intro H,
    suffices : ((0:real):complex).re = ((1:real):complex).re,
    { revert this,
      apply zero_ne_one },
    { show (0:complex).re = (1:complex).re,
    rw [←H],refl},
    end,
  mul_inv_cancel   := begin
    intros z H,
    have H2 : norm_squared z ≠ 0 := ne_of_gt (norm_squared_pos_of_nonzero z H),
    apply eq_of_re_eq_and_im_eq,
    { unfold has_inv.inv complex.inv,
      rw [mul_re],
      show z.re * (z.re / norm_squared z) -
      z.im * (-z.im / norm_squared z) =
    (1:complex).re,
      suffices : z.re*(z.re/norm_squared z) + -z.im*(-z.im/norm_squared z) = 1,
        by simpa,
      rw [←mul_div_assoc,←mul_div_assoc,neg_mul_neg,div_add_div_same],
      unfold norm_squared at *,
      exact div_self H2},
    { suffices : z.im * (z.re / norm_squared z) + z.re * (-z.im / norm_squared z) = 0,
      by simpa,
    rw [←mul_div_assoc,←mul_div_assoc,div_add_div_same],
    simp [zero_div,mul_comm],
    }
  end,
  inv_mul_cancel   := begin
    intros z H,
    have H2 : norm_squared z ≠ 0 := ne_of_gt (norm_squared_pos_of_nonzero z H),
    apply eq_of_re_eq_and_im_eq,
    { unfold has_inv.inv complex.inv,
     rw [mul_re],
     show (z.re / norm_squared z) * z.re -
      (-z.im / norm_squared z) * z.im =
    (1:complex).re,
      suffices : z.re*(z.re/norm_squared z) + -z.im*(-z.im/norm_squared z) = 1,
        by simpa [mul_comm],
      rw [←mul_div_assoc,←mul_div_assoc,neg_mul_neg,div_add_div_same],
      unfold norm_squared at *,
      exact div_self H2 },
    unfold has_inv.inv complex.inv,
    rw [mul_im],
    show (z.re / norm_squared z) * z.im +
      (-z.im / norm_squared z) * z.re =
    (1:complex).im,
    suffices : z.im * (z.re / norm_squared z) + z.re * (-z.im / norm_squared z) = 0,
      by simpa [mul_comm],
    rw [←mul_div_assoc,←mul_div_assoc,div_add_div_same],
    simp [zero_div,mul_comm]
  end,
  /-
  inv_zero         := begin
  unfold has_inv.inv complex.inv add_comm_group.zero,
  apply eq_of_re_eq_and_im_eq,
  split;simp [zero_div],
  end,
  -/
--  has_decidable_eq := by apply_instance,
  ..complex.add_comm_group,
  }

theorem im_eq_zero_of_complex_nat (n : ℕ) : (n:complex).im = 0 :=
begin
induction n with d Hd,
simp,
simp [Hd],
end

#print char_zero 
theorem T : has_coe ℕ complex := by apply_instance
#print nat.cast_coe

theorem of_real_nat_eq_complex_nat {n : ℕ} : ↑(n:ℝ) = (n:complex) :=
begin
  induction n with d Hd,refl,
  show ↑↑(d+1) = ↑(d+1),
  rw [nat.cast_add,nat.cast_add,←Hd],
  simp
end

instance char_zero_complex : char_zero complex :=
⟨begin
  intros,
  split,
  { rw [←complex.of_real_nat_eq_complex_nat,←complex.of_real_nat_eq_complex_nat],
    intro H,
    have real_eq := of_real_injective H,
    revert real_eq,
    have H2 : char_zero ℝ := by apply_instance,
    exact (char_zero.cast_inj ℝ).1 },
  intro H,rw [H],
end⟩

theorem of_real_int_eq_complex_int {n : ℤ} : of_real (n:ℝ) = (n:complex) :=
begin
  cases n with nnat nneg,exact of_real_nat_eq_complex_nat,
  rw [int.cast_neg_succ_of_nat,int.cast_neg_succ_of_nat],
  rw [←nat.cast_one,←nat.cast_add],
  rw [←@nat.cast_one complex,←nat.cast_add],
  rw [of_real_eq_coe,←of_real_neg],
  rw [of_real_nat_eq_complex_nat],
end 

/-
theorem of_real_rat_eq_complex_rat {q : ℚ} : of_real (q:ℝ) = (q:complex) :=
begin
rw [rat.num_denom q], -- this line doesn't even work now. I don't even understand goal.
rw [rat.cast_mk q.num ↑(q.denom)],
rw [rat.cast_mk q.num ↑(q.denom)],
rw [div_eq_mul_inv,div_eq_mul_inv,←of_real_mul],
rw [of_real_int_eq_complex_int],
rw [←@of_real_int_eq_complex_int ((q.denom):ℤ)],
rw [of_real_inv],
tactic.swap,
apply_instance,
-- exact complex.char_zero_complex, -- times out
admit,
end
-/
-- TODO : instance : topological_ring complex := missing

end complex

