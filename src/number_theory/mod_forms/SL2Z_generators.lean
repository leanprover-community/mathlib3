import .modular_group
import group_theory.group_action.basic
import linear_algebra.matrix
import linear_algebra.determinant
import data.matrix.notation

/-  This is an attempt to update the kbb birthday repo, so most is not orginal to me-/

@[simp] lemma not_one_lt_zero {α : Type*} [linear_ordered_semiring α] : ¬ (1:α) < 0 :=
not_lt_of_gt zero_lt_one

namespace int

theorem mul_eq_one {m n : ℤ} :
  m * n = 1 ↔ m = 1 ∧ n = 1 ∨ m = -1 ∧ n = -1 :=
⟨λ H, or.cases_on (int.units_eq_one_or ⟨m, n, H, by rwa [mul_comm] at H⟩)
  (λ H1, have H2 : m = 1, from units.ext_iff.1 H1,
    or.inl ⟨H2, by rwa [H2, one_mul] at H⟩)
  (λ H1, have H2 : m = -1, from units.ext_iff.1 H1,
    or.inr ⟨H2, by rwa [H2, neg_one_mul, neg_eq_iff_neg_eq, eq_comm] at H⟩),
by simp [or_imp_distrib] {contextual := tt}⟩

lemma nat_abs_lt_nat_abs (i k : ℤ) (hi : 0 ≤ i) (h : i < abs k) : nat_abs i < nat_abs k :=
coe_nat_lt.1 $ by rwa [nat_abs_of_nonneg hi, ← int.abs_eq_nat_abs]

end int

variables (a b c d : ℕ )

namespace SL2Z_M



def S': matrix  (fin 2) (fin 2 ) ℤ:= ![![0, -1], ![1, 0]]
def T' : matrix  (fin 2) (fin 2 ) ℤ:= ![![1, 1], ![0, 1]]

lemma SD: S'.det =1 :=
begin
rw S',
refl,
end

lemma TD: T'.det =1 :=
begin
rw T',
refl,
end

def S : SL2Z := ⟨ S', SD ⟩
def T: SL2Z := ⟨ T',TD⟩

@[simp] lemma S_a : S 0 0 = 0 := rfl
@[simp] lemma S_b : S 0 1 = -1 := rfl
@[simp] lemma S_c : S 1 0 = 1 := rfl
@[simp] lemma S_d : S 1 1 = 0 := rfl
@[simp] lemma T_a : T 0 0 = 1 := rfl
@[simp] lemma T_b : T 0 1 = 1 := rfl
@[simp] lemma T_c : T 1 0 = 0 := rfl
@[simp] lemma T_d : T 1 1 = 1 := rfl

variable (m : ℤ)

local notation `Mat` := integral_matrices_with_determinant

@[simp] lemma S_mul_a (A : Mat m) : (S • A) 0 0 = -A 1 0 :=
begin
  rw   SL2Z_M_aa,
 simp only [neg_mul_eq_neg_mul_symm, one_mul, S_a, zero_mul, S_b, zero_add],
end


@[simp] lemma S_mul_b (A : Mat m) : (S • A) 0 1 = -A 1 1 :=
begin
  rw   SL2Z_M_ba,
   simp only [neg_mul_eq_neg_mul_symm, one_mul, S_a, zero_mul, S_b, zero_add],
end

@[simp] lemma S_mul_c (A : Mat m) : (S • A) 1 0 = A 0 0 := by simp only [add_zero, one_mul, SL2Z_M_ca, zero_mul, S_c, S_d]
@[simp] lemma S_mul_d (A : Mat m) : (S • A) 1 1 =  A 0 1 := by simp only [add_zero, one_mul, zero_mul, S_c, SL2Z_M_da, S_d]
@[simp] lemma T_mul_a (A : Mat m) : (T • A) 0 0 = A 0 0 + A 1 0 := by simp only [one_mul, T_a, T_b, SL2Z_M_aa]
@[simp] lemma T_mul_b (A : Mat m) : (T • A) 0 1 = A 0 1 + A 1 1 := by simp only [one_mul, SL2Z_M_ba, T_a, T_b]
@[simp] lemma T_mul_c (A : Mat m) : (T • A) 1 0 = A 1 0 := by simp only [T_d, one_mul, SL2Z_M_ca, zero_mul, T_c, zero_add]
@[simp] lemma T_mul_d (A : Mat m) : (T • A) 1 1 = A 1 1 := by simp only [T_d, one_mul, zero_mul, T_c, zero_add, SL2Z_M_da]

lemma T_pow_aux' (n : ℕ ) : (T^n) 0 0 = 1 ∧ (T^n) 0 1 = n ∧ (T^n) 1 0 = 0 ∧ (T^n) 1 1 = 1 :=
begin
induction n with d hd,
simp only [SL2Z_one_b, SL2Z_one_d, int.coe_nat_zero, SL2Z_one_a, eq_self_iff_true, and_self, SL2Z_one_c, pow_zero],
simp only [pow_succ, T_d, one_mul, zero_mul, T_a, T_c, int.coe_nat_succ, T_b, zero_add, SL2Z_mul_d, SL2Z_mul_c, SL2Z_mul_a,
  SL2Z_mul_b],
rw [hd.1], simp only [add_right_eq_self], rw [hd.2.1], simp only [add_right_inj], rw hd.2.2.1, rw hd.2.2.2, simp only [eq_self_iff_true, and_self],
end

lemma T_pow_aux (n : ℤ  ) : (T^n) 0 0 = 1 ∧ (T^n) 0 1 = n ∧ (T^n) 1 0 = 0 ∧ (T^n) 1 1 = 1 :=
begin
induction n with d hd,
simp only [int.of_nat_eq_coe, gpow_coe_nat],
apply T_pow_aux',
simp only [SL2Z_inv_d, SL2Z_inv_c, SL2Z_inv_b, gpow_neg_succ_of_nat, SL2Z_inv_a, neg_eq_zero],
simp only [pow_succ, T_d, one_mul, zero_mul, T_a, T_c, T_b, neg_add_rev, zero_add, SL2Z_mul_d, SL2Z_mul_c, SL2Z_mul_a,
  SL2Z_mul_b], rw (T_pow_aux' hd).2.2.1, rw (T_pow_aux' hd).2.2.2, rw (T_pow_aux' hd).1, rw (T_pow_aux' hd).2.1,
simp only [true_and, add_zero, and_true, eq_self_iff_true], rw int.neg_succ_of_nat_eq', ring,
end

@[simp] lemma T_pow_a (n : ℤ) : (T^n) 0 0 = 1 := (T_pow_aux n).1
@[simp] lemma T_pow_b (n : ℤ) : (T^n) 0 1 = n := (T_pow_aux n).2.1
@[simp] lemma T_pow_c (n : ℤ) : (T^n) 1 0 = 0 := (T_pow_aux n).2.2.1
@[simp] lemma T_pow_d (n : ℤ) : (T^n) 1 1 = 1 := (T_pow_aux n).2.2.2

@[simp] lemma S_mul_S : S * S = (-1: SL2Z) :=
begin
ext i j,
fin_cases i; fin_cases j,
simp  [integral_matrices_with_determinant.neg_a, SL2Z_one_a], refl,
simp only [SL2Z_one_b, integral_matrices_with_determinant.neg_b, neg_zero], refl,
simp only [SL2Z_one_c, neg_zero, integral_matrices_with_determinant.neg_c], refl,
end

@[simp] lemma S_min: -S = -1 * S:=
begin
simp only [SL2Z.neg_one_mul],
end

@[simp] lemma S_inv' : -S * S= 1:=
begin
rw S_min,
rw  mul_assoc,
rw S_mul_S,
simp only [mul_one, SL2Z.neg_mul_neg],
end

@[simp] lemma S_inv: -S = S⁻¹ :=
begin
rw  eq_inv_iff_mul_eq_one,
rw S_inv',
end

@[simp] lemma S_n_T: S*S*S*T*S*T*S=T⁻¹:=
begin
simp only [SL2Z.neg_one_mul, S_mul_S, S_inv],
ext i j,
fin_cases i; fin_cases j,
simp only [T_d, add_zero, mul_one, S_a, T_a, T_c, SL2Z_inv_b, S_c, mul_neg_eq_neg_mul_symm, S_b, T_b, SL2Z_inv_a, zero_add,
  neg_neg, SL2Z_mul_a, S_d, mul_zero, SL2Z_mul_b, neg_zero],
   simp only [T_d, add_zero, mul_one, zero_mul, T_a, T_c, SL2Z_inv_b, S_c, mul_neg_eq_neg_mul_symm, S_b, T_b, SL2Z_inv_a, zero_add,
  neg_neg, SL2Z_mul_a, S_d, mul_zero, SL2Z_mul_b],
  simp only [T_d, SL2Z_inv_d, add_zero, mul_one, S_a, zero_sub, T_a, T_c, SL2Z_inv_c, S_c, mul_neg_eq_neg_mul_symm, S_b, T_b,
  add_left_neg, SL2Z_mul_d, SL2Z_mul_c, neg_neg, int.add_neg_one, S_d, mul_zero, neg_zero],
  simp only [SL2Z_inv_d, add_zero, mul_one, S_a, zero_sub, zero_mul, T_a, T_c, SL2Z_inv_c, S_c, mul_neg_eq_neg_mul_symm, S_b, T_b,
  SL2Z_mul_d, SL2Z_mul_c, neg_neg, int.add_neg_one, S_d, mul_zero],
end


lemma fixlem (m : ℤ) (A : Mat m) (H : int.nat_abs (A 1 0) ≠ 0): A 0 0 + -(A 0 0/ A 1 0)*( A 1 0)= A 0 0 % A 1 0:=
begin
simp only [neg_mul_eq_neg_mul_symm],
rw  ← sub_eq_add_neg,
rw mul_comm,
rw  ← int.mod_def,
end

attribute [elab_as_eliminator] nat.strong_induction_on

def gengrp :subgroup SL2Z := subgroup.closure ({ S, T,S⁻¹,T⁻¹} : set SL2Z)



lemma Tpows (n: ℤ) : T^n ∈ gengrp:=
begin
have  h1: T ∈ gengrp, by {rw gengrp, apply subgroup.subset_closure, simp,}  ,
 apply subgroup.gpow_mem _ h1,
end

lemma TSS (n: ℤ): T^n*S*S ∈ gengrp :=
begin
have h1:= Tpows n,
have h2: S ∈ gengrp , by {rw gengrp, apply subgroup.subset_closure, simp,},
have:= subgroup.mul_mem _ h1 h2,
apply subgroup.mul_mem _ this h2,
end

lemma UST (n: ℤ) (U ∈ gengrp ): U * S * (T^n)⁻¹ ∈ gengrp:=
begin
 have h1:= Tpows n,
 have hh1: (T^n)⁻¹ ∈ gengrp , by {rw subgroup.inv_mem_iff, exact h1 } ,
 have h2: S ∈ gengrp , by {rw gengrp, apply subgroup.subset_closure, simp,},
 have h3:= subgroup.mul_mem _ h2 hh1,
have:= subgroup.mul_mem _ H h3,
rw ← mul_assoc at this,
exact this,
end

def reps (m : ℤ) : set (Mat m) :=
{A : Mat m | A 1 0 = 0 ∧ 0 < A 0 0 ∧ 0 ≤ A 0 1 ∧ int.nat_abs (A 0 1) < int.nat_abs (A 1 1) }

theorem reduce_aux (m : ℤ) (A : Mat m) (H : int.nat_abs (A 1 0) ≠ 0) :
  int.nat_abs (( S • ( (T^(-((A 0 0) / (A 1 0)))) • A)) 1 0) < int.nat_abs (A 1 0) :=
begin
  have H2 : A 1 0 ≠ 0, from mt (λ H2, show int.nat_abs (A 1 0) = 0, by rw H2; refl) H,
  simp [one_mul, zero_mul, add_zero] with SL2Z,
  have:= fixlem m A H, simp at this, rw this,
  rw  [← int.coe_nat_lt], rw  int.nat_abs_of_nonneg ( int.mod_nonneg _ H2),
  rw [← int.abs_eq_nat_abs],
  exact int.mod_lt _ H2,
end

def reduce_step (A : Mat m) : Mat m :=  S • ( (T^(-((A 0 0)/(A 1 0)))) • A)

def c_entry (m :ℤ) (A: Mat m):= A 1 0

@[elab_as_eliminator]
def reduce_rec (m : ℤ) {C : Mat m → Sort*}
  (h₀ : ∀A:Mat m, (A 1 0) = 0 → C A)
  (h₁ : ∀A:Mat m, int.nat_abs (A 1 0) ≠ 0 → C (reduce_step m A) → C A) :
  ∀A, C A | A :=
if hc : int.nat_abs (A 1 0) = 0 then h₀ A (int.eq_zero_of_nat_abs_eq_zero hc)
else
  have int.nat_abs ((reduce_step m A) 1 0) < int.nat_abs (A 1 0), from reduce_aux m A hc,
  h₁ A hc (reduce_rec (reduce_step m A))
using_well_founded
  { rel_tac := λ _ _, `[exact ⟨_, measure_wf (int.nat_abs ∘ c_entry m ) ⟩]}

/-- correct if m ≠ 0 -/
def reduce (m : ℤ) : Mat m → Mat m | A :=
if hc : int.nat_abs (A 1 0) = 0
then if ha : 0 < (A 0 0)
  then (T^(-(A 0 1/A 1 1)))•  A
  else (T^(-(-A 0 1/ -A 1 1))) •  ( S • ( S • A))
else
  have int.nat_abs ((reduce_step m A) 1 0) < int.nat_abs (A 1 0), from reduce_aux m A hc,
  reduce (reduce_step  m A)
using_well_founded
  { rel_tac := λ _ _, `[exact ⟨_, measure_wf (int.nat_abs ∘ c_entry m )⟩]}

@[simp] theorem reduce_eq1 (m : ℤ) {A : Mat m} (hc : int.nat_abs (A 1 0) = 0) (ha : 0 < (A 0 0)) :
  reduce m A =  (T^(-(A 0 1/A 1 1))) •  A :=
by rw [reduce.equations._eqn_1 _ _, if_pos hc, if_pos ha]; refl

@[simp] theorem reduce_eq2 (m : ℤ) {A : Mat m} (hc : int.nat_abs (A 1 0) = 0) (ha : ¬ 0 < (A 0 0)) :
  reduce m A =  (T^(-(-A 0 1/ -A 1 1)))•  ( S • ( S • A)) :=
by rw [reduce.equations._eqn_1 _ _, if_pos hc, if_neg ha]; refl

@[simp] theorem reduce_eq3 (m : ℤ) {A : Mat m} (h : int.nat_abs (A 1 0) ≠ 0) :
  reduce m A = reduce m (reduce_step m A) :=
by rw [reduce.equations._eqn_1 _ _, if_neg h]

theorem reduce_spec (m : ℤ) : ∀A : Mat m, ∃ (S: SL2Z), S • A = reduce m A :=
begin
  refine reduce_rec m _ _,
  { intros A hc,
    by_cases ha : 0 < (A 0 0),
    { simp only [*, int.nat_abs_eq_zero, reduce_eq1, exists_apply_eq_apply]},
    {simp only [*, int.div_neg, int.nat_abs_eq_zero, not_false_iff, neg_neg, reduce_eq2],
    erw [← mul_smul], rw [← mul_smul], simp only [exists_apply_eq_apply],} },
  { rintros A hc ⟨S, eq⟩,
    rw [reduce_eq3 m hc, ← eq, reduce_step, ← mul_smul, ← mul_smul],
    exact ⟨_, rfl⟩ }
end

theorem reduce_spec' (m : ℤ) : ∀A : Mat m, ∃ (R: gengrp), R • A = reduce m A :=
begin
  refine reduce_rec m _ _,
  { intros A hc,
    by_cases ha : 0 < (A 0 0),
    {have:= reduce_eq1 m, simp at this, have h1:=this hc ha, simp only at h1, simp  [*, int.nat_abs_eq_zero, h1 , exists_apply_eq_apply],
     let gg:= (T ^ (A 0 1 / A 1 1))⁻¹,
     use gg,
     simp only [subgroup.inv_mem_iff],
     apply Tpows,
     simp_rw gg, refl, },
    {simp only [*, int.div_neg, int.nat_abs_eq_zero, not_false_iff, neg_neg, reduce_eq2],
    erw [← mul_smul], rw [← mul_smul],
    let g:= (T ^ (-A 0 1 / A 1 1))*S*S,
    use g,
    apply TSS,
    simp_rw g,refl,} },
  { rintros A hc ⟨U, eq⟩, rw reduce_eq3 m hc, rw ← eq, rw reduce_step, simp only [gpow_neg],
    simp only [int.nat_abs_eq_zero, ne.def] at *,
    use (U : SL2Z) * S *(T ^ (A 0 0 / A 1 0))⁻¹,
    have Umem:= set_like.coe_mem U,
    apply UST _ U Umem,
    have j: ∀ (x y z : SL2Z) (M: Mat m), x • y • z • M = (x * y*z)• M , by {simp_rw ← mul_smul, intros x y z A,
    rw mul_assoc,},
    have:= j (U : SL2Z)  (SL2Z_M.S) (T ^ (A 0 0 / A 1 0))⁻¹ A,
   apply this.symm,



   }
end


theorem reduce_mem_reps (m : ℤ) (hm : m ≠ 0) : ∀(A : Mat m), reduce m A ∈ reps m :=
begin
  refine reduce_rec m (assume A (c_eq : A 1 0 = 0), _) (assume A hc ih, _),
  { have hd : A 1 1 ≠ 0, { intro d_eq, apply hm, rw [← A.2], rw ← det_m', rw d_eq,rw c_eq,simp only [zero_mul, sub_zero, mul_zero],  },
    have eq : ∀b d, b + -(b / d * d) = b % d, { intros, rw [← sub_eq_add_neg, mul_comm, ← int.mod_def] },
    have h : ∀(a b : ℤ), 0 < a → 0 < a ∧ 0 ≤ b % (A 1 1) ∧ int.nat_abs (b % (A 1 1)) < int.nat_abs (A 1 1) :=
      assume a b ha, ⟨ha, int.mod_nonneg _ hd, int.nat_abs_lt_nat_abs _ _ (int.mod_nonneg _ hd) (int.mod_lt _ hd)⟩,
    by_cases ha : 0 < A 0 0,
    {simpa [reduce_eq1, reps, c_eq, ha, eq] using h _ _ ha },
    { have a_ne : A 0 0 ≠ 0,
      { intro a_eq, apply hm, rw [← A.2, ← det_m', a_eq, c_eq], simp only [zero_mul, sub_zero], },
      have a_pos : -A 0 0 > 0 := neg_pos_of_neg (lt_of_le_of_ne (le_of_not_gt ha) a_ne),
      simpa [reduce_eq2, reps, c_eq, ha, eq] using h _ _ a_pos } },
  { rwa [reduce_eq3 m hc] }
end

@[elab_as_eliminator]
protected theorem induction_on {C : Mat m → Prop} (A : Mat m) (mne0 : m ≠ 0)
  (h0 : ∀{A:Mat m}, A 1 0 = 0 → A 0 0 * A 1 1 = m → 0 < A 0 0 → 0 ≤ A 0 1 → int.nat_abs (A 0 1) < int.nat_abs (A 1 1) → C A)
  (hS : ∀ B, C B → C (S • B)) (hT : ∀ B, C B → C ( T • B)) :
  C A :=
have S_eq : ∀ (B : Mat m), (S • ( S • (S • ( S • B)))) = B,
  by  intro b; {rw ← mul_smul, rw S_mul_S, rw ← mul_smul,simp only [SL2Z.neg_one_mul, S_inv, inv_smul_smul],},
have hS' : ∀{B}, C (S • B) → C B, from
  λ B ih, have h : _ := (hS _ $ hS _ $ hS _ ih), by rwa S_eq B at h,
have eq : ∀ (B: Mat m),
  (S • S • S • T • S • T • S • B) = T⁻¹ • B,
  by intro b; {repeat {rw [← mul_smul]}, rw S_n_T, }; congr,
have hT_inv : ∀ B, C B → C (T⁻¹ • B), from
  λ B ih, have h : _ := (hS _ $ hS _ $ hS _ $ hT _ $ hS _ $ hT _ $ hS _ ih), by rwa eq at h,
have hT' : ∀B, C (T • B) → C B,
{ assume B ih,
  have h := hT_inv (T • B) ih,
  rwa [←mul_smul, mul_left_inv, one_smul] at h },
have hT_inv' : ∀ B, C  (T⁻¹ • B) → C B,
{ assume B ih,
  have H := hT ( T⁻¹ • B) ih,
  rwa [←mul_smul, mul_right_inv, one_smul] at H },
have hTpow' : ∀{B} {n:ℤ}, C ( (T^n) • B) → C B,
{ refine assume B n, int.induction_on n (λh, _) (λi ih1 ih2, ih1 $ hT' _ _) (λi ih1 ih2, ih1 $ hT_inv' _ _),
  { rwa [gpow_zero, one_smul] at h },
  { rwa [add_comm, gpow_add, gpow_one, mul_smul] at ih2 },
  { rwa [sub_eq_neg_add, gpow_add, gpow_neg_one, mul_smul] at ih2 } },
have h_reduce : C (reduce m A),
{ rcases reduce_mem_reps m mne0 A with ⟨H1, H2, H3, H4⟩,
  refine h0 H1 _ H2 H3 H4,
  rw det_m''', exact H1},
suffices ∀A : Mat m, C (reduce m A) → C A, from this _ h_reduce,
begin
  refine reduce_rec m _ _,
  { assume A c_eq ih,
    by_cases ha : 0 < A 0 0,
    { simp [reduce_eq1, c_eq, ha, -gpow_neg] at ih, exact hTpow' ih },
    { simp [reduce_eq2, c_eq, ha] at ih, exact (hS' $ hS' $ hTpow' ih) } },
  { assume A hc ih hA,
    rw [reduce_eq3 m hc] at hA,
    exact (hTpow' $ hS' $ ih hA) }
end






lemma num_gt_sum (h f b  : ℤ)  (h2: f ≥ 0) (h4: h.nat_abs > f.nat_abs) (h5: (f+b*h) ≥ 0) (h6: h.nat_abs > (f+b*h).nat_abs):  b = 0:=

begin
simp at *,
rw ←  int.coe_nat_lt at h4,
rw  int.nat_abs_of_nonneg h2 at h4,
rw ←  int.coe_nat_lt at h6,
rw  int.nat_abs_of_nonneg h5 at h6,
rw ← int.abs_eq_nat_abs at h6,
rw ← int.abs_eq_nat_abs at h4,
have hg0: abs h > 0, {apply lt_of_le_of_lt h2 h4,   },
have hgn0: h ≠ 0, {intros ᾰ, simp at *, solve_by_elim, },
have hn:  f % abs h = f, { apply   int.mod_eq_of_lt h2 h4, },
have hn2:  (f +b*h) % abs h = f+b*h, { apply   int.mod_eq_of_lt h5 h6, },
simp only [int.mod_abs, int.add_mul_mod_self] at hn2,
simp only [int.mod_abs] at hn,
have ht: f = f+b*h , {rw ←  hn2, rw hn,    },
simp only [self_eq_add_right, mul_eq_zero] at ht,
rw lt_iff_le_not_le at h4,
cases h4, cases ht, work_on_goal 0 { assumption }, dsimp at *, simp at *, solve_by_elim,
end

lemma one_time (a b c : ℤ) (h1: a > 0) (h2: c > 0) (h3: a = b*c): b > 0:=
begin
simp at *,
have h4: b*c >0 ,{ rw h3 at h1, exact h1},
replace h2:= le_of_lt h2,
apply pos_of_mul_pos_right  h4 h2,
end

lemma one_time' (a b : ℤ) (h1: a > 0) (h2: (a = 1 ∧ b=1) ∨ (a=-1 ∧ b=-1)): (a=1 ∧ b=1):=
begin
by_contra h,
cases h2, work_on_goal 0 { cases h2, simp at *, solve_by_elim }, cases h2, simp at *,
 rw h2_left at h1, have h4 : 0 < (-1: ℤ) ↔ false, simp only [neg_nonpos, not_lt, iff_false],
work_on_goal 0 { exact dec_trivial }, cases h4, simp at *, solve_by_elim,
end



theorem reps_unique (m : ℤ) (hm : m ≠ 0) :
  ∀(M : SL2Z) (A B : Mat m), A ∈ reps m → B ∈ reps m →  M • A = B → A = B :=
begin
  rintros  M A B
    ⟨g_eq, e_pos, f_nonneg, f_bound⟩ ⟨k_eq, H6, f'_nonneg, f'_bound⟩ B_eq, rw ← B_eq,
    rw m_a_b at B_eq,
  have ht: M 1 0 = 0, {rw [k_eq, g_eq] at B_eq, simp only [add_zero, zero_eq_mul, mul_zero] at B_eq,
   cases B_eq.2.2.1, exact h, rw h at e_pos, exact (irrefl _ e_pos).elim, },
  have d1: (M 0 0)*(M 1 1)=1, { rw ← det_onne M, rw ht, simp only [zero_mul, sub_zero],   },
  have mg0: (M  0 0) > 0, {rw g_eq at B_eq, simp only [add_zero, mul_zero] at B_eq,
   exact one_time (B 0 0) (M 0 0) (A 0 0) H6 e_pos B_eq.1, },
  have htt: M 0 0 =1 ∧ M 1 1 =1, { rw int.mul_eq_one at d1, apply one_time' (M 0 0) (M 1 1) mg0 d1,  },
  have httv: M 1 1 =1, { simp only [htt], },
  have htv: ((A 0 1)+ (M 0 1)*(A 1 1)) ≥ 0, {rw B_eq.2.1 at f'_nonneg, rw htt.1 at f'_nonneg,
  simp only [one_mul] at f'_nonneg, exact f'_nonneg},
  have httt: M 0 1 =0, {rw B_eq.2.2.2 at f'_bound, rw B_eq.2.1 at f'_bound,
  rw ht at f'_bound, rw htt.1 at f'_bound,  rw httv at f'_bound, simp only [one_mul, zero_mul,
  zero_add] at f'_bound, apply num_gt_sum (A 1 1) (A 0 1) (M 0 1)  f_nonneg  f_bound htv, exact f'_bound, },
  have M1: M = (1: SL2Z),{ext i j, fin_cases i; fin_cases j, exact htt.1, exact  httt, exact ht, exact httv},
  rw M1, simp only [one_smul], exact hm,
end

lemma m_a_b' (m : ℤ) (hm : m ≠ 0) (A : gengrp) (M N : integral_matrices_with_determinant m):
 (A • M) = N ↔  N 0 0= A 0 0 * M 0 0 + A 0 1 * M 1 0 ∧
 N 0 1= A 0 0 * M 0 1 + A 0 1 * M 1 1 ∧
 N 1 0= A 1 0 * M 0 0 + A 1 1 * M 1 0 ∧
 N 1 1= A 1 0 * M 0 1 + A 1 1 * M 1 1 :=
begin
apply m_a_b, exact hm,
end

theorem reps_unique' (m : ℤ) (hm : m ≠ 0) :
  ∀(M : gengrp) (A B : Mat m), A ∈ reps m → B ∈ reps m →  M • A = B → A = B :=
begin
  rintros  M A B
    ⟨g_eq, e_pos, f_nonneg, f_bound⟩ ⟨k_eq, H6, f'_nonneg, f'_bound⟩ B_eq, rw ← B_eq,
    rw m_a_b' at B_eq,
  have ht: M 1 0 = 0, {rw [k_eq, g_eq] at B_eq, simp only [add_zero, zero_eq_mul, mul_zero] at B_eq,
   cases B_eq.2.2.1, exact h, rw h at e_pos, exact (irrefl _ e_pos).elim, },
  have d1: (M 0 0)*(M 1 1)=1, { rw ← det_onne M, simp at *, rw ht, simp only [zero_mul, sub_zero],   },
  have mg0: (M  0 0) > 0, {rw g_eq at B_eq, simp only [add_zero, mul_zero] at B_eq,
   exact one_time (B 0 0) (M 0 0) (A 0 0) H6 e_pos B_eq.1, },
  have htt: M 0 0 =1 ∧ M 1 1 =1, { rw int.mul_eq_one at d1, apply one_time' (M 0 0) (M 1 1) mg0 d1,  },
  have httv: M 1 1 =1, { simp only [htt], },
  have htv: ((A 0 1)+ (M 0 1)*(A 1 1)) ≥ 0, {rw B_eq.2.1 at f'_nonneg, rw htt.1 at f'_nonneg,
  simp only [one_mul] at f'_nonneg, exact f'_nonneg},
  have httt: M 0 1 =0, {rw B_eq.2.2.2 at f'_bound, rw B_eq.2.1 at f'_bound,
  rw ht at f'_bound, rw htt.1 at f'_bound,  rw httv at f'_bound, simp only [one_mul, zero_mul,
  zero_add] at f'_bound, apply num_gt_sum (A 1 1) (A 0 1) (M 0 1)  f_nonneg  f_bound htv, exact f'_bound, },
  have M1: ↑M = (1: SL2Z),{ext i j, fin_cases i; fin_cases j, exact htt.1, exact  httt, exact ht, exact httv}, norm_cast at M1,
  rw M1, simp only [one_smul], exact hm,
end


variable (n:ℕ+)




def  PT (a b c d : ℤ ): matrix  (fin 2) (fin 2 ) ℤ:= ![![a, b], ![c, d]]

lemma dm  (a b c d : ℤ ) : (PT a b c d).det = a*d-b*c:=

begin
rw PT,
apply det_of_22 (PT a b c d),
end


@[simp] lemma em  (a b c d : ℤ ) :  (PT a b c d) 0 0 = a ∧ (PT a b c d) 0 1 = b ∧ (PT a b c d) 1 0 = c ∧ (PT a b c d) 1 1 = d  :=

begin
rw PT,
simp only [matrix.head_cons, eq_self_iff_true, and_self, matrix.cons_val_one, matrix.cons_val_zero],
end


lemma nat_pos (m: ℕ+) (a : fin(m+1)): a ≥ 0:=
begin
exact dec_trivial,
end


lemma pos_nat (m: ℕ+) (a : fin(m+1)): 0 ≤ a:=
begin
exact dec_trivial,
end

lemma en_pos (m : ℕ+) (A: matrix (fin 2) (fin 2) ℤ) (h1: A.det= ↑ m) (h2: 0 < A 0 0) (h3: A 1 0 =0) : 0 ≤ A 1 1:=
begin
rw det_of_22 at h1,
rw h3 at h1,
simp only [sub_zero, mul_zero, coe_coe] at h1,
by_contradiction h,
simp only [not_le] at h,
have h5: A 1 1 * A 0 0 < 0, {apply mul_neg_of_neg_of_pos h h2},
 rw mul_comm at h1, rw h1 at h5, cases m, dsimp at *, rw ← int.coe_nat_lt at m_property, rw ←  not_le at h5, dsimp at *, simp at *, assumption,
end

instance reps.fintype_pos (m:ℕ+) : fintype (reps m) :=
fintype.of_equiv {v : fin (m+1) × fin (m+1) × fin (m+1) // v.1.1 * v.2.2.1 = m ∧ v.2.1.1 < v.2.2.1}
{ to_fun := λ A, ⟨ ⟨PT  A.1.1.1  A.1.2.1.1 (0: ℤ)  A.1.2.2.1 , by {rw  [dm  A.1.1.1  A.1.2.1.1 (0 : ℤ)  A.1.2.2.1], rw [ mul_zero, sub_zero, ← int.coe_nat_mul, A.2.1, coe_coe]}⟩,
rfl, by {simp only [vale, int.coe_nat_pos, em, subtype.val_eq_coe], have agt: 0 <A.1.1.1, {have age: 0 ≤ A.1.1.1, {apply nat_pos,}, rw le_iff_lt_or_eq at age, cases age, cases A, cases m, work_on_goal 0 { assumption }, cases A, cases m, cases A_property, cases A_val, cases A_val_snd, cases A_val_fst, cases A_val_snd_snd, cases A_val_snd_fst, dsimp at *, induction age, induction A_property_left, simp at *, assumption,  }, exact agt, } , by {simp only [vale, true_and, int.nat_abs_of_nat, fin.coe_fin_lt, int.coe_nat_nonneg, em, subtype.val_eq_coe], exact A.2.2,   }⟩,
  inv_fun := λ A, ⟨    (     ⟨int.nat_abs (A.1 0 0), nat.lt_succ_of_le $ nat.le_of_dvd m.2 ⟨int.nat_abs (A.1 1 1),
      have a1: (A).val 1 0 = 0, {apply A.2.1},
      have ao: (A.1).val 1 0 = 0, {simp only [vale, subtype.val_eq_coe] at a1, simp only [subtype.val_eq_coe], apply a1},
      by have := A.1.2; {simp only [subtype.val_eq_coe, coe_coe] at this, rw det_of_22 at this,  rw ←   coe_coe at this, simp only [subtype.val_eq_coe] at ao, rw ← coe_coe at ao, rw ao at this, simp only [sub_zero, mul_zero, coe_coe] at this, rw ← coe_coe at this,
      rw ← coe_coe at this, rw [← int.nat_abs_mul], simp only [subtype.val_eq_coe], rw coe_coe at this, simp only [vale, subtype.val_eq_coe], rw this, simp only [int.nat_abs_of_nat, coe_coe]}  ⟩ ⟩,
    ⟨int.nat_abs (A.1 0 1), nat.lt_succ_of_le $ le_trans (le_of_lt A.2.2.2.2) $ nat.le_of_dvd m.2 ⟨int.nat_abs (A.1 0 0),
     have a1: (A).val 1 0 = 0, {apply A.2.1},
      have ao: (A.1).val 1 0 = 0, {simp only [vale, subtype.val_eq_coe] at a1, simp only [subtype.val_eq_coe], apply a1,},
     by have := A.1.2; {simp only [subtype.val_eq_coe, coe_coe] at this, rw det_of_22 at this,  rw ←   coe_coe at this, simp only [subtype.val_eq_coe] at ao, rw ← coe_coe at ao, rw ao at this, simp only [sub_zero, mul_zero, coe_coe] at this, rw ← coe_coe at this,
      rw ← coe_coe at this, rw [← int.nat_abs_mul], simp only [subtype.val_eq_coe], rw coe_coe at this, rw ← mul_comm at this, simp only [vale, subtype.val_eq_coe], rw this, simp only [int.nat_abs_of_nat, coe_coe],},  ⟩⟩,
    ⟨int.nat_abs (A.1 1 1), nat.lt_succ_of_le $ nat.le_of_dvd m.2 ⟨int.nat_abs (A.1 0 0),
      have a1: (A).val 1 0 = 0, {apply A.2.1},
      have ao: (A.1).val 1 0 = 0, {simp only [vale, subtype.val_eq_coe] at a1, simp, apply a1,},
       by have := A.1.2; {simp only [subtype.val_eq_coe, coe_coe] at this, rw det_of_22 at this,  rw ←   coe_coe at this, simp at ao, rw ← coe_coe at ao, rw ao at this, simp only [sub_zero, mul_zero, coe_coe] at this, rw ← coe_coe at this,
      rw ← coe_coe at this, rw [← int.nat_abs_mul], simp only [subtype.val_eq_coe], rw coe_coe at this, rw ← mul_comm at this, simp only [vale, subtype.val_eq_coe], rw this, simp only [int.nat_abs_of_nat, coe_coe],},  ⟩⟩),
     have a1: (A).val 1 0 = 0, {apply A.2.1},
      have ao: (A.1).val 1 0 = 0, {simp only [vale, subtype.val_eq_coe] at a1, simp, apply a1,},
      by have := A.1.2; {simp only [subtype.val_eq_coe, coe_coe] at this, rw det_of_22 at this,  rw ←   coe_coe at this, simp only [subtype.val_eq_coe] at ao, rw ← coe_coe at ao, rw ao at this, simp only [sub_zero, mul_zero, coe_coe] at this, rw ← coe_coe at this,
      rw ← coe_coe at this, rw [← int.nat_abs_mul], simp only [subtype.val_eq_coe], rw coe_coe at this,  simp only [vale, subtype.val_eq_coe], rw this, simp only [int.nat_abs_of_nat, coe_coe],}, A.2.2.2.2⟩,
  left_inv := λ ⟨⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨d, hd⟩⟩, H1, H2⟩, subtype.eq $ prod.ext
    (fin.eq_of_veq $ int.nat_abs_of_nat _) $ prod.ext
    (fin.eq_of_veq $ int.nat_abs_of_nat _)
    (fin.eq_of_veq $ int.nat_abs_of_nat _),

  right_inv := λ ⟨ ⟨A ,H1⟩,  H2, H3, H4, H5⟩,  by {simp only [vale, subtype.mk_eq_mk], ext i j, fin_cases i; fin_cases j, simp only [em],
   simp only [vale] at H3, rw ← int.abs_eq_nat_abs, apply abs_of_pos H3,  simp only [em],  simp only [vale] at H4, rw ← int.abs_eq_nat_abs,
   apply abs_of_nonneg H4, simp only [em], simp only [vale] at H2, simp only [H2], simp only [em],  simp only [vale] at H5,
   have h7: A 0 1 < (A 1 1).nat_abs, {simp only [vale] at H4, rw ← int.coe_nat_lt at H5, rw  int.nat_abs_of_nonneg H4 at H5, exact H5},
    simp only [vale] at H4, have h8: 0 <(A 1 1).nat_abs, {rw ← int.coe_nat_lt, apply lt_of_le_of_lt H4 h7 },
     rw ← int.abs_eq_nat_abs, rw ← int.coe_nat_lt at h8, rw ← int.abs_eq_nat_abs at h8, simp only [abs_eq_self],
     simp only [vale] at H3, apply en_pos m A H1 H3 H2}}



def reps.fintype : Π m : ℤ, m ≠ 0 → fintype (reps m)
| (int.of_nat $ n+1) H := reps.fintype_pos ⟨n+1, nat.zero_lt_succ n⟩
| 0 H := (H rfl).elim
| -[1+ n] H := fintype.of_equiv (reps (⟨n+1, nat.zero_lt_succ _⟩:pnat))
{to_fun := λ A, ⟨ ⟨PT (A.1 0 0) (A.1 0 1) (A.1 1 0) (-A.1 1 1),
  have a1: (A).val 1 0 = 0, {apply A.2.1},
  have ao: (A.1).val 1 0 = 0, {simp only [vale, subtype.val_eq_coe] at a1, simp only [subtype.val_eq_coe], apply a1,},
 by have := A.1.2; {simp only [subtype.val_eq_coe, coe_coe] at this, simp only [pnat.mk_coe, int.coe_nat_succ] at this,
rw det_of_22 at this, rw dm, simp only [vale, mul_neg_eq_neg_mul_symm, subtype.val_eq_coe],simp only [subtype.val_eq_coe] at ao, rw ao,  rw ao at this, simp only [sub_zero, mul_zero], simp only [sub_zero, mul_zero] at this, rw this, rw int.neg_succ_of_nat_coe,  refl} ⟩,
    A.2.1, A.2.2.1, A.2.2.2.1, trans_rel_left _ A.2.2.2.2 $ eq.symm $ int.nat_abs_neg _⟩,

  inv_fun := λ A, ⟨⟨PT (A.1 0 0) (A.1 0 1) (A.1 1 0) (-A.1 1 1),
 have a1: (A).val 1 0 = 0, {apply A.2.1},
  have ao: (A.1).val 1 0 = 0, {simp only [vale, subtype.val_eq_coe] at a1, simp only [subtype.val_eq_coe], apply a1,},
 by have := A.1.2; {simp only [subtype.val_eq_coe, coe_coe] at this, rw det_of_22 at this, rw dm, simp only [vale, mul_neg_eq_neg_mul_symm, subtype.val_eq_coe],
  simp only [subtype.val_eq_coe] at ao, rw ao, rw ao at this, simp only [sub_zero, mul_zero], simp only [pnat.mk_coe, int.coe_nat_succ, coe_coe], simp only [sub_zero, mul_zero] at this, rw this, refl} ⟩,
    A.2.1, A.2.2.1, A.2.2.2.1, trans_rel_left _ A.2.2.2.2 $ eq.symm $ int.nat_abs_neg _⟩,
  left_inv := λ ⟨ ⟨A, H1⟩, H2⟩, by {simp only [vale, subtype.mk_eq_mk, neg_neg, em], ext i j, fin_cases i; fin_cases j, simp only [em], simp only [em], simp only [em], simp only [em],  },
  right_inv := λ ⟨⟨A, H1⟩, H2⟩, by {simp only [vale, subtype.mk_eq_mk, neg_neg, em], ext i j, fin_cases i; fin_cases j, simp only [em], simp only [em], simp only [em], simp only [em],  },
   }


section

def orbit_rel'' (m : ℤ): setoid (Mat m) :=
{ r := λ a b, a ∈ mul_action.orbit SL2Z b,
  iseqv := ⟨mul_action.mem_orbit_self, λ a b, by simp only [mul_action.orbit_eq_iff.symm, eq_comm, imp_self],
    λ a b, by simp only [mul_action.orbit_eq_iff.symm, implies_true_iff, eq_self_iff_true] {contextual := tt}⟩ }



def orbit_rel''' (m : ℤ): setoid (Mat m) :=
{ r := λ a b, a ∈ mul_action.orbit gengrp b,
  iseqv := ⟨mul_action.mem_orbit_self, λ a b, by simp only [mul_action.orbit_eq_iff.symm, eq_comm, imp_self],
    λ a b, by simp only [mul_action.orbit_eq_iff.symm, implies_true_iff, eq_self_iff_true] {contextual := tt}⟩ }


def π : reps m → quotient (orbit_rel'' m ) :=
  λ A, (@quotient.mk _ (orbit_rel'' m)) A

def π' : reps m → quotient (orbit_rel''' m ) :=
  λ A, (@quotient.mk _ (orbit_rel''' m)) A


set_option eqn_compiler.zeta true
def reps_equiv (hm : m ≠ 0) : quotient (orbit_rel'' m ) ≃ reps m :=
by letI := (orbit_rel'' m ); from
{ to_fun := λ x, quotient.lift_on x (λ A, (⟨reduce m A, reduce_mem_reps m hm A⟩ : reps m)) $ λ A B ⟨M, H⟩,
    let ⟨MA, HA⟩ := reduce_spec m A in
    let ⟨MB, HB⟩ := reduce_spec m B in
    subtype.eq $ reps_unique m hm (MB * M⁻¹ * MA⁻¹) _ _ (reduce_mem_reps m hm A) (reduce_mem_reps m hm B) $
    by {simp only, rw ← HA, rw mul_smul, simp only [inv_smul_smul], rw mul_smul, simp only [_x, forall_true_left] at _fun_match,
    simp only at H, rw ← H,  simp only [exists_imp_distrib] at _let_match, rw H, rw ← HB, simp, rw ← H, simp only [inv_smul_smul],},
  inv_fun := λ A, ⟦A.1⟧,
  left_inv := λ x, by {simp only [subtype.val_eq_coe], induction x, work_on_goal 0 { cases x, dsimp at *, simp at * }, work_on_goal 1 { refl },
  apply quotient.sound, apply reduce_spec m ⟨ x_val, x_property⟩},


  right_inv := λ A, subtype.eq $
    let ⟨MA, HA⟩ := reduce_spec m A in
    reps_unique m hm MA⁻¹ _ _ (reduce_mem_reps m hm A) A.2 $
    show  MA⁻¹ • (reduce m A) = A,
    by {rw [← HA], simp only [inv_smul_smul], }, }
end

def reps_equiv' (hm : m ≠ 0) : quotient (orbit_rel''' m ) ≃ reps m :=
by letI := (orbit_rel''' m ); from
{ to_fun := λ x, quotient.lift_on x (λ A, (⟨reduce m A, reduce_mem_reps m hm A⟩ : reps m)) $ λ A B ⟨M, H⟩,
    let ⟨MA, HA⟩ := reduce_spec' m A in
    let ⟨MB, HB⟩ := reduce_spec' m B in
    subtype.eq $ reps_unique' m hm (MB * M⁻¹ * MA⁻¹) _ _ (reduce_mem_reps m hm A) (reduce_mem_reps m hm B) $
    by {simp only, rw ← HA, rw mul_smul, simp only [inv_smul_smul], rw mul_smul, simp only [_x, forall_true_left] at _fun_match,
    simp only at H, rw ← H,  simp only [exists_imp_distrib] at _let_match, rw H, rw ← HB, simp, rw ← H, simp [inv_smul_smul],},
  inv_fun := λ A, ⟦A.1⟧,
  left_inv := λ x, by {simp only [subtype.val_eq_coe], induction x, work_on_goal 0 { cases x, dsimp at *, simp at * }, work_on_goal 1 { refl },
  apply quotient.sound, apply reduce_spec' m ⟨ x_val, x_property⟩},


  right_inv := λ A, subtype.eq $
    let ⟨MA, HA⟩ := reduce_spec' m A in
    reps_unique' m hm MA⁻¹ _ _ (reduce_mem_reps m hm A) A.2 $
    show  MA⁻¹ • (reduce m A) = A,
    by {rw [← HA], simp only [inv_smul_smul], }, }






protected def decidable_eq (hm : m ≠ 0) : decidable_eq (quotient (orbit_rel'' m )) :=
equiv.decidable_eq (reps_equiv m hm)

def finiteness (hm : m ≠ 0) : fintype (quotient $ orbit_rel'' m) :=
@fintype.of_equiv _ _ (reps.fintype m hm) (reps_equiv m hm).symm



lemma Mat1_eq_SL2Z: Mat 1 = SL2Z :=
begin
refl,
end

lemma reps_sl2z: reps 1 = {(1: SL2Z)}:=
begin
rw reps, dsimp,
ext1, split,
intro hx, simp at *,
have detsl:= det_of_22  x,
simp at detsl,
rw hx.1 at detsl, simp at detsl,
have:= detsl.symm,
rw int.mul_eq_one at this,
have hx2:= hx.2.1,
have hh:= one_time' _ _ hx2 this,
have hx3: x 0 1 = 0, by {
have i1:= hx.2.2.2, rw hh.2 at i1, simp at i1, simp [i1],},
simp at hx3, ext,
fin_cases i; fin_cases j,
simp [hh.1], simp [hx3],
simp [hx.1], simp [hh.2],
intro hx, simp at *, split,
simp [hx],
split,
simp [hx],
split,
simp [hx],
simp [hx],
end

universe u
variables {G : Type*} {α : Sort*} [group G] [H : subgroup G]

def triv_rel (α: Sort u) : α → α → Prop :=
λ a b, true



lemma rel_triv (α: Type u) (r: α → α → Prop ) (h: quot r ≃ trunc α) : eqv_gen r = triv_rel α :=
begin
ext, rw triv_rel, simp, rw trunc at h, have:h  (quot.mk r x) = h (quot.mk r x_1), by {apply trunc.eq,},
simp at this, have h2:= quot.exact r this, exact h2,
end

lemma eqv_gen_is_triv (α: Type u) (r: α → α → Prop ) (h: eqv_gen r = triv_rel α) (h2 : equivalence r) : r = triv_rel α:=
begin
 rw ← h, ext,
simp_rw relation.eqv_gen_iff_of_equivalence h2,
end

def quotient_r (A: subgroup G) : Type* := quotient (quotient_group.right_rel A)


lemma top_trunc : quotient_group.quotient (⊤: subgroup G) = trunc G :=
begin
rw trunc, congr',
end

lemma top_trunc_r : quotient_r (⊤: subgroup G) = trunc G :=
begin
rw trunc, congr',
end


lemma lef_rel_triv (H :subgroup G) (h: (quotient_group.left_rel H).r = triv_rel G ) : ∀ x y : G , x⁻¹ * y ∈ H:=
begin
rw triv_rel at h,
let s:=(quotient_group.left_rel H).r,
have h2: ∀ x y : G, s x y ↔ x⁻¹ * y ∈ H, by {intros x y, refl,  },
intros x y,
have h3:= h2 x y, rw ← h3, simp_rw s, rw h, tauto,
end


lemma lef_rel_triv_r (H :subgroup G) (h: (quotient_group.right_rel H).r = triv_rel G ) : ∀ x y : G , y * x⁻¹ ∈ H:=
begin
rw triv_rel at h,
let s:=(quotient_group.right_rel H).r,
have h2: ∀ x y : G, s x y ↔ y * x⁻¹ ∈ H, by {intros x y, refl,  },
intros x y,
have h3:= h2 x y, rw ← h3, simp_rw s, rw h, tauto,
end

lemma quot_triv  (h: quotient_group.quotient H ≃ quotient_group.quotient (⊤: subgroup G)) : H = ⊤ :=
begin
ext1, simp at *, rw top_trunc at h,
rw quotient_group.quotient at h,
have H2:= rel_triv _ _ h,
let rr:= quotient_group.left_rel H,
simp_rw quotient_group.left_rel at h,
have HH:= setoid.iseqv,
have H3:= eqv_gen_is_triv _ _ H2 HH,
have H4:= lef_rel_triv H H3,
have H5:= H4 1 x, simp at H5, exact H5,
end


lemma quot_triv_r  (h: quotient_r H ≃ quotient_r (⊤: subgroup G)) : H = ⊤ :=
begin
ext1, simp at *, rw top_trunc_r at h,
rw quotient_r at h,
have H2:= rel_triv _ _ h,
let rr:= quotient_group.right_rel H,
simp_rw quotient_group.right_rel at h,
have HH:= setoid.iseqv,
have H3:= eqv_gen_is_triv _ _ H2 HH,
have H4:= lef_rel_triv_r H H3,
have H5:= H4 1 x, simp at H5, exact H5,
end

instance subsingtruc : subsingleton (trunc SL2Z) := infer_instance

instance subsingtruc2 : subsingleton ( {(1: SL2Z)} : set (Mat 1) ) := infer_instance

def trunceq : (trunc SL2Z) ≃ ( {(1: SL2Z)} : set (Mat 1) ) :=
{ to_fun := λ _, default ( {(1: SL2Z)} : set (Mat 1) ),
  inv_fun := λ _, default (trunc SL2Z),
  left_inv := λ _, subsingleton.elim _ _,
  right_inv := λ _, subsingleton.elim _ _ }

lemma grpinv (a : G) : a ∈ H ↔ a⁻¹ ∈ H:=
begin
exact (subgroup.inv_mem_iff H).symm,

end

lemma sl2z_gens: gengrp = (⊤ : subgroup SL2Z) :=
begin
have h0: (1: ℤ) ≠ 0, by {simp,},
have h1:= reps_equiv' 1 h0,
have h2:= reps_sl2z,   rw h2 at h1, dsimp at h1, simp_rw orbit_rel''' at h1,
 simp_rw mul_action.orbit at h1,simp at h1, dsimp at h1,
apply quot_triv_r,
rw top_trunc_r,
have hh: quotient (orbit_rel''' 1) ≃ trunc SL2Z, by { apply equiv.trans h1, exact trunceq.symm,},

have hh2: quotient_r (gengrp) ≃ quotient (orbit_rel''' 1) , by {
  let r1:=(orbit_rel''' 1).r,
  let r2:=(quotient_group.right_rel (gengrp)).r,
  apply quot.congr_right,
  have rh1: ∀ x y : SL2Z, r1 x y ↔ x ∈ mul_action.orbit gengrp y, by {intros x y, refl,   },
  have rh2: ∀ x y : SL2Z, r2 x y ↔ y * x⁻¹ ∈ gengrp, by {intros x y, refl,},
  intros a b, simp at *,
  have goal: r2 a b ↔ r1 a b, by {rw rh1, rw rh2,
  rw mul_action.orbit, simp, split,
  intro ha, use a* b⁻¹ ,
  have haa: a*b⁻¹ ∈ gengrp, by {rw (subgroup.inv_mem_iff gengrp).symm, simp , exact ha,},
  exact haa, have:= smul_is_mul_1 (a * b⁻¹) b, convert this, simp,
  intro hb,
  have HB: ∃ y : gengrp , (y : SL2Z) * b =a, by {apply hb, },
  rw (subgroup.inv_mem_iff gengrp).symm, simp,
  have HBB: ∀ (x y z : SL2Z), x* y= z ↔ x = z* y⁻¹, by {intros x y z, split, intro x1, rw ← x1,
   simp, intro x2, rw x2, simp,},
  simp_rw HBB at HB,
  simp at *,
  let v:= classical.some HB,
  have hv: (v : SL2Z)= a * b⁻¹, by {simp_rw v, apply classical.some_spec HB,},
  rw ← hv, simp,},
  apply goal,  },
apply equiv.trans hh2 hh,
end


def Gens:=({ S, T} : set SL2Z)

lemma Gens_subgroup_eq_gengrp : subgroup.closure (Gens) = gengrp :=
begin
rw Gens, rw gengrp,
 refine le_antisymm ((subgroup.closure_le _).2 _) ((subgroup.closure_le _).2 _),

sorry,
end

theorem SL2Z_Generators : subgroup.closure (Gens) = ⊤ :=
begin
rw Gens_subgroup_eq_gengrp,
apply sl2z_gens,
end


end SL2Z_M
