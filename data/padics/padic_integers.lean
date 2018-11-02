/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis

Define the p-adic integers ℤ_p as a subtype of ℚ_p. Construct algebraic structures on ℤ_p.
-/

import data.padics.padic_numbers ring_theory.ideals data.int.modeq
import tactic.linarith

open nat padic
noncomputable theory
local attribute [instance] classical.prop_decidable

def padic_int (p : ℕ) [p.prime] := {x : ℚ_[p] // ∥x∥ ≤ 1}
notation `ℤ_[`p`]` := padic_int p

namespace padic_int
variables {p : ℕ} [nat.prime p]

def add : ℤ_[p] → ℤ_[p] → ℤ_[p]
| ⟨x, hx⟩ ⟨y, hy⟩ := ⟨x+y,
    le_trans (padic_norm_e.nonarchimedean _ _) (max_le_iff.2 ⟨hx,hy⟩)⟩

def mul : ℤ_[p] → ℤ_[p] → ℤ_[p]
| ⟨x, hx⟩ ⟨y, hy⟩ := ⟨x*y,
    begin rw padic_norm_e.mul, apply mul_le_one; {assumption <|> apply norm_nonneg} end⟩

def neg : ℤ_[p] → ℤ_[p]
| ⟨x, hx⟩ := ⟨-x, by simpa⟩

instance : ring ℤ_[p] :=
begin
  refine { add := add,
           mul := mul,
           neg := neg,
           zero := ⟨0, by simp [zero_le_one]⟩,
           one := ⟨1, by simp⟩,
           .. };
  {repeat {rintro ⟨_, _⟩}, simp [mul_assoc, left_distrib, right_distrib, add, mul, neg]}
end

lemma zero_def : ∀ x : ℤ_[p], x = 0 ↔ x.val = 0
| ⟨x, _⟩ := ⟨subtype.mk.inj, λ h, by simp at h; simp only [h]; refl⟩

@[simp] lemma add_def : ∀ (x y : ℤ_[p]), (x+y).val = x.val + y.val
| ⟨x, hx⟩ ⟨y, hy⟩ := rfl

@[simp] lemma mul_def : ∀ (x y : ℤ_[p]), (x*y).val = x.val * y.val
| ⟨x, hx⟩ ⟨y, hy⟩ := rfl

@[simp] lemma mk_zero {h} : (⟨0, h⟩ : ℤ_[p]) = (0 : ℤ_[p]) := rfl

instance : has_coe ℤ_[p] ℚ_[p] := ⟨subtype.val⟩

@[simp] lemma val_eq_coe (z : ℤ_[p]) : z.val = ↑z := rfl

@[simp] lemma coe_add : ∀ (z1 z2 : ℤ_[p]), (↑(z1 + z2) : ℚ_[p]) = ↑z1 + ↑z2
| ⟨_, _⟩ ⟨_, _⟩ := rfl

@[simp] lemma coe_mul : ∀ (z1 z2 : ℤ_[p]), (↑(z1 * z2) : ℚ_[p]) = ↑z1 * ↑z2
| ⟨_, _⟩ ⟨_, _⟩ := rfl

@[simp] lemma coe_neg : ∀ (z1 : ℤ_[p]), (↑(-z1) : ℚ_[p]) = -↑z1
| ⟨_, _⟩ := rfl

@[simp] lemma coe_sub : ∀ (z1 z2 : ℤ_[p]), (↑(z1 - z2) : ℚ_[p]) = ↑z1 - ↑z2
| ⟨_, _⟩ ⟨_, _⟩ := rfl

@[simp] lemma coe_one : (↑(1 : ℤ_[p]) : ℚ_[p]) = 1 := rfl

@[simp] lemma coe_coe : ∀ n : ℕ, (↑(↑n : ℤ_[p]) : ℚ_[p]) = (↑n : ℚ_[p])
| 0 := rfl
| (k+1) := by simp [coe_coe]

@[simp] lemma coe_zero : (↑(0 : ℤ_[p]) : ℚ_[p]) = 0 := rfl

@[simp] lemma cast_pow (x : ℤ_[p]) : ∀ (n : ℕ), (↑(x^n) : ℚ_[p]) = (↑x : ℚ_[p])^n
| 0 := by simp
| (k+1) := by simp [monoid.pow, pow]; congr; apply cast_pow

lemma mk_coe : ∀ (k : ℤ_[p]), (⟨↑k, k.2⟩ : ℤ_[p]) = k
| ⟨_, _⟩ := rfl

def inv : ℤ_[p] → ℤ_[p]
| ⟨k, _⟩ := if h : ∥k∥ = 1 then ⟨1/k, by simp [h]⟩ else 0

end padic_int

section instances
variables {p : ℕ} [nat.prime p]

@[reducible] def padic_norm_z (z : ℤ_[p]) : ℝ := ∥z.val∥

instance : metric_space ℤ_[p] :=
subtype.metric_space

instance : has_norm ℤ_[p] := ⟨padic_norm_z⟩

instance : normed_ring ℤ_[p] :=
{ dist_eq := λ ⟨_, _⟩ ⟨_, _⟩, rfl,
  norm_mul := λ ⟨_, _⟩ ⟨_, _⟩, norm_mul _ _ }

instance padic_norm_z.is_absolute_value : is_absolute_value (λ z : ℤ_[p], ∥z∥) :=
{ abv_nonneg := norm_nonneg,
  abv_eq_zero := λ ⟨_, _⟩, by simp [norm_eq_zero, padic_int.zero_def],
  abv_add := λ ⟨_,_⟩ ⟨_, _⟩, norm_triangle _ _,
  abv_mul := λ _ _, by unfold norm; simp [padic_norm_z] }

protected lemma padic_int.pmul_comm : ∀ z1 z2 : ℤ_[p], z1*z2 = z2*z1
| ⟨q1, h1⟩ ⟨q2, h2⟩ := show (⟨q1*q2, _⟩ : ℤ_[p]) = ⟨q2*q1, _⟩, by simp [mul_comm]

instance : comm_ring ℤ_[p] :=
{ mul_comm := padic_int.pmul_comm,
  ..padic_int.ring }

protected lemma padic_int.zero_ne_one : (0 : ℤ_[p]) ≠ 1 :=
show (⟨(0 : ℚ_[p]), _⟩ : ℤ_[p]) ≠ ⟨(1 : ℚ_[p]), _⟩, from mt subtype.ext.1 zero_ne_one

protected lemma padic_int.eq_zero_or_eq_zero_of_mul_eq_zero :
          ∀ (a b : ℤ_[p]), a * b = 0 → a = 0 ∨ b = 0
| ⟨a, ha⟩ ⟨b, hb⟩ := λ h : (⟨a * b, _⟩ : ℤ_[p]) = ⟨0, _⟩,
have a * b = 0, from subtype.ext.1 h,
(mul_eq_zero_iff_eq_zero_or_eq_zero.1 this).elim
  (λ h1, or.inl (by simp [h1]; refl))
  (λ h2, or.inr (by simp [h2]; refl))

instance : integral_domain ℤ_[p] :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := padic_int.eq_zero_or_eq_zero_of_mul_eq_zero,
  zero_ne_one := padic_int.zero_ne_one,
  ..padic_int.comm_ring }

end instances

namespace padic_norm_z

variables {p : ℕ} [nat.prime p]

lemma le_one : ∀ z : ℤ_[p], ∥z∥ ≤ 1
| ⟨_, h⟩ := h

@[simp] lemma one : ∥(1 : ℤ_[p])∥ = 1 := by simp [norm, padic_norm_z]

@[simp] lemma mul (z1 z2 : ℤ_[p]) : ∥z1 * z2∥ = ∥z1∥ * ∥z2∥ :=
by unfold norm; simp [padic_norm_z]

@[simp] lemma pow (z : ℤ_[p]) : ∀ n : ℕ, ∥z^n∥ = ∥z∥^n
| 0 := by simp
| (k+1) := show ∥z*z^k∥ = ∥z∥*∥z∥^k, by {rw mul, congr, apply pow}

theorem nonarchimedean : ∀ (q r : ℤ_[p]), ∥q + r∥ ≤ max (∥q∥) (∥r∥)
| ⟨_, _⟩ ⟨_, _⟩ := padic_norm_e.nonarchimedean _ _

theorem add_eq_max_of_ne : ∀ {q r : ℤ_[p]}, ∥q∥ ≠ ∥r∥ → ∥q+r∥ = max (∥q∥) (∥r∥)
| ⟨_, _⟩ ⟨_, _⟩ := padic_norm_e.add_eq_max_of_ne

@[simp] lemma norm_one : ∥(1 : ℤ_[p])∥ = 1 := norm_one

lemma eq_of_norm_add_lt_right {z1 z2 : ℤ_[p]}
  (h : ∥z1 + z2∥ < ∥z2∥) : ∥z1∥ = ∥z2∥ :=
by_contradiction $ λ hne,
  not_lt_of_ge (by rw padic_norm_z.add_eq_max_of_ne hne; apply le_max_right) h

lemma eq_of_norm_add_lt_left {z1 z2 : ℤ_[p]}
  (h : ∥z1 + z2∥ < ∥z1∥) : ∥z1∥ = ∥z2∥ :=
by_contradiction $ λ hne,
  not_lt_of_ge (by rw padic_norm_z.add_eq_max_of_ne hne; apply le_max_left) h

@[simp] lemma padic_norm_e_of_padic_int (z : ℤ_[p]) : ∥(↑z : ℚ_[p])∥ = ∥z∥ :=
by simp [norm, padic_norm_z]

@[simp] lemma padic_norm_z_eq_padic_norm_e {q : ℚ_[p]} (hq : ∥q∥ ≤ 1) :
  @norm ℤ_[p] _ ⟨q, hq⟩ = ∥q∥ := rfl

end padic_norm_z

private lemma mul_lt_one  {α} [decidable_linear_ordered_comm_ring α] {a b : α} (hbz : 0 < b)
  (ha : a < 1) (hb : b < 1) : a * b < 1 :=
suffices a*b < 1*1, by simpa,
mul_lt_mul ha (le_of_lt hb) hbz zero_le_one

private lemma mul_lt_one_of_le_of_lt {α} [decidable_linear_ordered_comm_ring α] {a b : α} (ha : a ≤ 1)
  (hbz : 0 ≤ b) (hb : b < 1) : a * b < 1 :=
if hb' : b = 0 then by simpa [hb'] using zero_lt_one
else if ha' : a = 1 then by simpa [ha']
else mul_lt_one (lt_of_le_of_ne hbz (ne.symm hb')) (lt_of_le_of_ne ha ha') hb

namespace padic_int

variables {p : ℕ} [nat.prime p]

local attribute [reducible] padic_int

lemma mul_inv : ∀ {z : ℤ_[p]}, ∥z∥ = 1 → z * z.inv = 1
| ⟨k, _⟩ h :=
  begin
    have hk : k ≠ 0, from λ h', @zero_ne_one ℚ_[p] _ (by simpa [h'] using h),
    unfold padic_int.inv, split_ifs,
    { change (⟨k * (1/k), _⟩ : ℤ_[p]) = 1,
      simp [hk], refl },
    { apply subtype.ext.2, simp [mul_inv_cancel hk] }
  end

lemma inv_mul {z : ℤ_[p]} (hz : ∥z∥ = 1) : z.inv * z = 1 :=
by rw [mul_comm, mul_inv hz]


lemma maximal_ideal_add {z1 z2 : ℤ_[p]} (hz1 : ∥z1∥ < 1) (hz2 : ∥z2∥ < 1) : ∥z1 + z2∥ < 1 :=
lt_of_le_of_lt (padic_norm_z.nonarchimedean _ _) (max_lt hz1 hz2)

lemma maximal_ideal_mul {z1 z2 : ℤ_[p]} (hz2 : ∥z2∥ < 1) : ∥z1 * z2∥ < 1 :=
calc  ∥z1 * z2∥ = ∥z1∥ * ∥z2∥ : by simp
           ... < 1 : mul_lt_one_of_le_of_lt (padic_norm_z.le_one _) (norm_nonneg _) hz2

def maximal_ideal (p : ℕ) [p.prime] : ideal ℤ_[p] :=
{ carrier := {z | ∥z∥ < 1},
  zero := show ∥(0 : ℤ_[p])∥ < 1, by simp [zero_lt_one],
  add := @maximal_ideal_add _ _,
  smul := @maximal_ideal_mul _ _ }

lemma maximal_ideal_ne_top : maximal_ideal p ≠ ⊤ :=
(ideal.ne_top_iff_one _).2 $ assume : ∥(1:ℤ_[p])∥ < 1,
by rw padic_norm_z.one at this; exact lt_irrefl 1 this

lemma maximal_ideal_eq_nonunits : ↑(maximal_ideal p) = nonunits ℤ_[p] :=
begin
  ext,
  constructor,
  { intros hx hex,
    cases hex with y hy,
    have hym : ∥(y*x)∥ < 1, from submodule.smul _ _ hx,
    apply lt_irrefl (1 : ℝ),
    rw hy at hym, simpa using hym },
  { intro hx,
    by_contradiction hnm,
    apply hx,
    have : ∥x∥ = 1, from le_antisymm (padic_norm_z.le_one _) (le_of_not_gt hnm),
    existsi x.inv, apply inv_mul this }
end

/-instance : is_proper_ideal (maximal_ideal p) :=
{ ne_univ := maximal_ideal_ne_univ }-/

/-lemma maximal_ideal_eq_or_univ_of_subset (T : set ℤ_[p]) [_inst_2 : is_ideal T]
      (hss : maximal_ideal p ⊆ T) : T = maximal_ideal p ∨ T = set.univ :=
have T ≠ maximal_ideal p → T = set.univ, from
  (assume h : T ≠ maximal_ideal p,
   let ⟨k, hkt, hknm⟩ := set.exists_of_ssubset ⟨hss, ne.symm h⟩ in
   set.eq_univ_of_forall $ λ z,
     have hknm : ∥k∥ = 1, from le_antisymm (padic_norm_z.le_one _) (le_of_not_gt hknm),
     have hkzt : z*k ∈ T, from is_submodule.smul _ hkt,
     have hkzt' : (inv k)*(z*k) ∈ T, from is_submodule.smul _ hkzt,
     by rw [mul_comm, mul_assoc, mul_inv] at hkzt'; simpa using hkzt'),
if hT : T = maximal_ideal p then or.inl hT else or.inr (this hT)-/

instance : ideal.is_maximal (maximal_ideal p) :=
⟨maximal_ideal_ne_top, λ T h, let ⟨k, hkt, hknm⟩ := set.exists_of_ssubset ⟨h.1, mt ge_of_eq h.2⟩ in
ideal.eq_top_of_unit_mem _ k (inv k) hkt $ inv_mul $ le_antisymm (padic_norm_z.le_one _) $ le_of_not_lt hknm⟩

/-lemma maximal_ideal_unique (T : set ℤ_[p]) [_inst_2 : is_maximal_ideal T] : maximal_ideal p = T :=
let htmax := @is_maximal_ideal.eq_or_univ_of_subset _ _ T _ (maximal_ideal p) _ in
have htsub : T ⊆ maximal_ideal p,
  by rw maximal_ideal_eq_nonunits; apply not_unit_of_mem_proper_ideal,
or.resolve_right (htmax htsub) maximal_ideal_ne_univ-/

instance : is_local_ring ℤ_[p] :=
local_of_nonunits_ideal zero_ne_one $ λ x y,
by rw [← maximal_ideal_eq_nonunits, submodule.mem_coe];
exact submodule.add_mem _
/-{ S := maximal_ideal p,
  max := by apply_instance,
  unique := maximal_ideal_unique }-/

private def cau_seq_to_rat_cau_seq (f : cau_seq ℤ_[p] norm) :
  cau_seq ℚ_[p] (λ a, ∥a∥) :=
⟨ λ n, f n,
  λ _ hε, by simpa [norm, padic_norm_z] using f.cauchy hε ⟩

instance complete : cau_seq.is_complete ℤ_[p] norm :=
⟨ λ f,
  have hqn : ∥cau_seq.lim (cau_seq_to_rat_cau_seq f)∥ ≤ 1,
    from padic_norm_e_lim_le zero_lt_one (λ _, padic_norm_z.le_one _),
  ⟨ ⟨_, hqn⟩,
    by simpa [norm, padic_norm_z] using cau_seq.lim_spec (cau_seq_to_rat_cau_seq f) ⟩⟩

end padic_int

namespace padic_norm_z
variables {p : ℕ} [nat.prime p]

lemma padic_val_of_cong_pow_p {z1 z2 : ℤ} {n : ℕ} (hz : z1 ≡ z2 [ZMOD ↑(p^n)]) :
      ∥(z1 - z2 : ℚ_[p])∥ ≤ ↑(fpow ↑p (-n) : ℚ) :=
have hdvd : ↑(p^n) ∣ z2 - z1, from int.modeq.modeq_iff_dvd.1 hz,
have (↑(z2 - z1) : ℚ_[p]) = padic.of_rat p ↑(z2 - z1), by simp,
begin
  rw [norm_sub_rev, ←int.cast_sub, this, padic_norm_e.eq_padic_norm],
  simpa using padic_norm.le_of_dvd p hdvd
end

end padic_norm_z