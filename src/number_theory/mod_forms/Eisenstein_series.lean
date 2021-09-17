
import tactic.pi_instances
import .modular_group
import linear_algebra.general_linear_group
import .modular_forms
import data.matrix.notation
import data.setoid.partition
import topology.instances.ennreal
import topology.instances.nnreal
import .Riemann_zeta_fin
import .holomorphic_functions
import order.filter.archimedean
import .Weierstrass_M_test
import analysis.complex.upper_half_plane
import topology.compact_open


universes u v w

open complex

open_locale big_operators nnreal classical filter

local notation `ℍ` := upper_half_plane

local notation `ℍ'`:=(⟨upper_half_space, upper_half_plane_is_open⟩: open_subs)
noncomputable theory


/-! ### Eisenstein series -/

namespace Eisenstein_series




/- Note that here we are using that 1/0=0, so there is nothing wrong with this defn or the resulting sum-/

def Eise (k: ℤ) (z : ℍ) : ℤ × ℤ →  ℂ:=
λ x, 1/(x.1*z+x.2)^k

def Eisen (k : ℤ) (x : ℤ × ℤ) : C(ℍ, ℂ) :=
⟨λ z, 1/(x.1*z+x.2)^k, by {simp,  sorry}⟩

instance : topological_space C(ℍ, ℂ) :=infer_instance



def Eise' (k: ℤ) (z : ℂ) : ℤ × ℤ →  ℂ:=
λ x, 1/(x.1*z+x.2)^k

def real_Eise (k: ℤ) (z : ℍ) : ℤ × ℤ →  ℝ:=
λ x, complex.abs(1/(x.1*z+x.2)^k)


def Eise_deriv (k: ℤ) (z : ℂ) : ℤ × ℤ →  ℂ:=
λ x, (-k*x.1)/(x.1*z+x.2)^(k+1)



/--This defines the Eisenstein series of weight k and level one. At the moment there is no restriction on the weight,
but in order to make it an actual modular form some constraints will be needed -/
def Eisenstein_series_of_weight_ (k: ℤ) : ℍ' → ℂ:=
 λ z, ∑' (x : ℤ × ℤ), (Eise k z x)



def real_Eisenstein_series_of_weight_ (k: ℤ) : ℍ' → ℝ:=
 λ z, ∑' (x : ℤ × ℤ), (real_Eise k z x)

def Eisenstein_deriv_weight (k: ℤ) : ℍ' → ℂ:=
 λ z, ∑' (x : ℤ × ℤ), (Eise_deriv k z x)



lemma summable2 (k : ℤ) (h: 3 ≤ k) : summable (Eisen k):=
begin
  sorry,
end


def Eisenstein_series_of_weight_' (k: ℤ) : C(ℍ, ℂ):=
 ∑' (x : ℤ × ℤ), Eisen k x


lemma ridic (a b c d : ℤ): a*d-b*c=1 → a*d-c*b=1:=
begin
intro h, linarith,
end


lemma ridic2 (a b c d z : ℤ) (h: a*d-b*c=1):  z*d*a-z*c*b=z:=
begin
ring_nf, rw h, rw one_mul,
end




/- This is the permutation of the summation index coming from the moebius action-/
def Ind_perm (A : SL2Z ): ℤ × ℤ →  ℤ × ℤ:=
λ z, (z.1* (A.1 0 0) +z.2* (A.1 1 0), z.1*(A.1 0 1)+z.2* (A.1 1 1))



def Ind_equiv (A : SL2Z): ℤ × ℤ ≃ ℤ × ℤ:={
to_fun:=Ind_perm A,
inv_fun:=Ind_perm A⁻¹,
left_inv:=λ z, by {rw Ind_perm, rw Ind_perm,
have ha:= SL2Z_inv_a A, simp only [vale] at ha,
have hb:= SL2Z_inv_b A, simp only [vale] at hb,
have hc:= SL2Z_inv_c A, simp only [vale] at hc,
have hd:= SL2Z_inv_d A, simp only [vale] at hd,
have hdet:=det_onne A, simp only [vale] at hdet,
simp only, ring_nf, simp only [ha, hb, hc, hd], ring_nf, rw mul_comm at hdet, simp only [hdet],
have ht: A.val 1 1 * A.val 1 0 - A.val 1 0 * A.val 1 1=0, by {ring, }, simp only [ht],
have ht2: -(A.val 0 1 * A.val 0 0) + A.val 0 0 * A.val 0 1=0, by {ring,}, simp only [ht2],
have ht3: -(A.val 0 1 * A.val 1 0) + A.val 0 0 * A.val 1 1 =1, by {rw add_comm,  rw mul_comm at hdet, simp,
simp at *, ring_nf, rw ridic, exact hdet, }, simp only [ht3], ring_nf, simp only [prod.mk.eta, add_zero, zero_mul, zero_add], },
right_inv:= λ z, by { rw Ind_perm, rw Ind_perm,
have ha:= SL2Z_inv_a A, simp only [vale] at ha,
have hb:= SL2Z_inv_b A, simp only [vale] at hb,
have hc:= SL2Z_inv_c A, simp only [vale] at hc,
have hd:= SL2Z_inv_d A, simp only [vale] at hd,
have hdet:=det_onne A, simp only [vale] at hdet,
simp only, ring_nf, simp only [ha, hb, hc, hd], ring_nf,
have hz1:= ridic2 (A.val 0 0) (A.val 1 0) (A.val 0 1) (A.val 1 1) z.fst hdet, simp only [hz1],
have hz2:= ridic2 (A.val 0 0) (A.val 1 0) (A.val 0 1) (A.val 1 1) z.snd hdet, simp only [hz2], simp only [prod.mk.eta],} ,
}



@[simp]lemma ind_simp (A: SL2Z) (z : ℤ × ℤ): Ind_equiv A z=(z.1* (A.1 0 0) +z.2* (A.1 1 0), z.1*(A.1 0 1)+z.2* (A.1 1 1)):=
begin
refl,
end







lemma wa (a b c: ℂ) (h: a ≠ 0) :  b=c → a*b⁻¹=a*c⁻¹ :=
begin
simp [h],
end

lemma Eise_is_nonneg (k: ℤ) (z : ℍ) (y : ℤ × ℤ): 0 ≤ abs (Eise k z y):=
begin
 apply complex.abs_nonneg,
end


lemma calc_lem (k: ℤ) (a b c d i1 i2: ℂ) (z : ℍ) (h: c*z+d ≠ 0) : ((i1* ((a*z+b)/(c*z+d))+i2)^k)⁻¹=(c*z+d)^k* (  ((i1 * a + i2 * c) * z + (i1 * b + i2 * d))^k   )⁻¹:=
begin
have h1: i1*((a*z+b)/(c*z+d))+i2=(i1*(a*z+b)/(c*z+d)+i2), by {ring  }, rw h1,
have h2:  (i1*(a*z+b)/(c*z+d)+i2)=((i1*(a*z+b))/(c*z+d)+i2), by {ring}, rw h2,
have h3:=div_add' (i1*(a*z+b)) i2 (c*z+d) h, rw h3, simp [inv_pow], rw div_eq_inv_mul,
have h4: (((c * ↑z + d) ^ k)⁻¹ * (i1 * (a * ↑z + b) + i2 * (c * ↑z + d)) ^ k)⁻¹ =(c * ↑z + d) ^ k * ((i1 * (a * ↑z + b) + i2 * (c * ↑z + d)) ^ k)⁻¹, by {rw ← div_eq_inv_mul, rw inv_div, rw div_eq_inv_mul, ring,},
rw h4, have h5: (c*z+d)^k ≠ 0, by {apply fpow_ne_zero _ h,  }, have:=mul_left_cancel'  h5 ,apply wa _ _ _ h5, ring_nf, tauto, tauto,
end





lemma coe_chain (A: SL2Z) (i j : fin (2)): (A.1 i j : ℂ)= ((A.1 : (matrix (fin 2) (fin 2) ℝ) ) i j : ℂ):=
begin

simp, rw ← coe_coe, fin_cases i; fin_cases j, simp only [coe_coe],
 work_on_goal 0 { cases A, dsimp at *, tactic.ext1 [] {new_goals := tactic.new_goals.all},
  work_on_goal 0 { dsimp at *, simp only [int_cast_re] at *, refl }, dsimp at *, simp only [int_cast_im] at *},
  work_on_goal 0 { cases A, dsimp at *, tactic.ext1 [] {new_goals := tactic.new_goals.all},
  work_on_goal 0 { dsimp at *, simp only [int_cast_re] at *, refl }, dsimp at *, simp only [int_cast_im] at *},
  work_on_goal 0 { cases A, dsimp at *, tactic.ext1 [] {new_goals := tactic.new_goals.all},
  work_on_goal 0 { dsimp at *, simp only [int_cast_re] at *, refl }, dsimp at *, simp only [int_cast_im] at *},
  cases A, dsimp at *, tactic.ext1 [] {new_goals := tactic.new_goals.all},
  work_on_goal 0 { dsimp at *,simp only [int_cast_re] at *, refl }, dsimp at *, simp only [int_cast_im] at *,
end


/- How the Eise function changes under the Moebius action-/
lemma Eise_moeb (k: ℤ) (z : ℍ) (A : SL2Z) (i : ℤ × ℤ ):
Eise k ( (A : matrix.GL_pos (fin 2) ℝ) • z) i=  ((A.1 1 0*z+A.1 1 1)^k)*(Eise k z (Ind_equiv A i ) ):=

begin
rw Eise, rw Eise,  simp,   dsimp, rw ← coe_coe, rw ← coe_coe, rw calc_lem,
have h1:= coe_chain A, simp at h1, rw h1, rw h1, rw h1, rw h1, rw ← coe_coe,
simp,rw ← coe_coe, rw ← coe_coe, simp, refl,
apply upper_half_plane.denom_ne_zero A,
end






lemma Eisenstein_is_modular (Γ : subgroup SL2Z) (k: ℤ)  :  (Eisenstein_series_of_weight_ k) ∈ is_modular_of_level_and_weight Γ k :=

begin
rw is_modular_of_level_and_weight, rw Eisenstein_series_of_weight_, simp only [set.mem_set_of_eq],
intros A z, have h1:= Eise_moeb k z A,  have h2:=tsum_congr h1, convert h2, simp only [subtype.val_eq_coe],
have h3:=equiv.tsum_eq (Ind_equiv A) (Eise k z),
rw tsum_mul_left, rw h3,refl,
end




lemma max_aux' (a b : ℕ): max a b = a ∨ max a b =b:=
begin
apply max_choice,
end

lemma max_aux (a b : ℕ):a= max a b  ∨  b=max a b :=
begin
have:= (max_aux' a b),  cases this, work_on_goal 0 { simp at * }, work_on_goal 1 { simp at * },
have h1: max a b = a, apply max_eq_left this, rw h1, simp only [true_or, eq_self_iff_true],rw max_comm,
have h2: max b a=b, apply max_eq_left this, rw h2, simp only [eq_self_iff_true, or_true],
end

lemma max_aux'' (a b n : ℕ) (h: max a b =n): a=n ∨ b =n :=
begin
rw ← h,
apply max_aux,
end


lemma max_aux3 (a b n : ℕ) (h: max a b =n): a ≤ n ∧ b ≤ n :=
begin
rw ← h, split, exact le_max_left a b, exact le_max_right a b,
end




def Square (m: ℕ): finset (ℤ × ℤ):=((finset.Ico_ℤ (-m) (m+1)).product (finset.Ico_ℤ (-m) (m+1))).filter (λ x, max (x.1).nat_abs (x.2).nat_abs = m)



def Square2 (m: ℕ): finset (ℤ × ℤ):=
(finset.Ico_ℤ (-m) (m+1)).product {m } ∪ (finset.Ico_ℤ (-m) (m+1)).product {-(m: ℤ)} ∪    ({m} : finset (ℤ)).product (finset.Ico_ℤ (-m+1) (m)) ∪   ({-m} : finset (ℤ)).product (finset.Ico_ℤ (-m+1) (m))


lemma square2_card (n: ℕ) (h: 1 ≤ n): finset.card (Square2 n)=8*n:=
begin
rw Square2, rw finset.card_union_eq, rw finset.card_union_eq,rw finset.card_union_eq, rw finset.card_product,
 rw finset.card_product,rw finset.card_product, rw finset.card_product, simp only [mul_one, one_mul,
 finset.Ico_ℤ.card, sub_neg_eq_add, finset.card_singleton], ring_nf,
 have N1:(n: ℤ)+1+(n : ℤ)=2*(n:ℤ)+1, by {ring,},
 have N2:(n: ℤ)-(-(n: ℤ)+1)=2*(n: ℤ)-1, by {ring,},
 rw [N1,N2], norm_cast, rw int.to_nat_coe_nat,
 have M1: (((2*n): ℤ)-1).to_nat=2*n-1, by {simp only [int.pred_to_nat] at *, refl, }, norm_cast at M1, rw M1,
 have M2: 2 * (2 * n + 1) + 2 * (2 * n - 1)=8*n+2-2, by {ring_nf, dsimp at *, simp only [nat.add_sub_cancel,
 int.pred_to_nat, zero_add] at *, injections_and_clear,
 have M3: 2*(2*n-1)=4*n-2, by {rw nat.mul_sub_left_distrib,ring_nf,}, rw M3, rw nat.sub_add_cancel, ring, linarith,
 },

rw M2, simp only [nat.add_sub_cancel],

 rw finset.disjoint_iff_ne,  intros a ha, intros b hb, simp only [ne.def, finset.mem_singleton, finset.Ico_ℤ.mem,
  finset.mem_product] at *, by_contra H, have haa:=ha.2, have hbb:=hb.2,
  rw H at haa, rw hbb at haa, have hv:=eq_zero_of_neg_eq haa, simp only [int.coe_nat_eq_zero] at hv, rw hv at h, simp only [nat.one_ne_zero,
   le_zero_iff] at h, exact h,
rw finset.disjoint_iff_ne, intros a ha, intros b hb,simp only [ne.def, finset.mem_union, finset.mem_singleton,
finset.Ico_ℤ.mem, neg_add_le_iff_le_add, finset.mem_product] at *, cases ha, have hbb:=hb.2, have haa:=ha.2, by_contra H,
 rw ← H at hbb,
rw haa at hbb, simp only [lt_self_iff_false, and_false] at hbb,exact hbb,have hbb:=hb.2, have haa:=ha.2, by_contra H, rw ← H at hbb, rw haa at hbb, simp at hbb,
have hk:=hbb.1, linarith,

rw finset.disjoint_iff_ne, intros a ha, intros b hb, simp only [ne.def, finset.mem_union, finset.union_assoc,
finset.mem_singleton, finset.Ico_ℤ.mem, neg_add_le_iff_le_add,
  finset.mem_product] at *, by_contra H, cases ha, have hbb:=hb.2,
have haa:=ha.2,rw ← H at hbb,
rw haa at hbb, simp only [lt_self_iff_false, and_false] at hbb,exact hbb, cases ha, have hbb:=hb.2, have haa:=ha.2,rw ← H at hbb,
rw haa at hbb, simp only [int.coe_nat_pos, neg_lt_self_iff, add_right_neg] at hbb, linarith,
have hbb:=hb.1, have haa:=ha.1,rw H at haa, rw hbb at haa, have hv:=eq_zero_of_neg_eq haa, simp only [int.coe_nat_eq_zero] at hv, rw hv at h,
 simp only [nat.one_ne_zero, le_zero_iff] at h, exact h,
end

lemma nat_abs_inter (a: ℤ) (n: ℕ) (h: a.nat_abs < n): a < (n: ℤ) ∧  0 <(n: ℤ)+ a:=
begin
have:= int.nat_abs_eq  a, cases this,rw this, norm_cast, simp_rw h,simp,linarith,rw this,
split, linarith, rw ←int.coe_nat_lt at h, rw ← sub_pos at h,convert h,
end

lemma nat_abs_inter2 (a: ℤ) (n: ℕ) (h: a.nat_abs ≤ n): a ≤ (n: ℤ) ∧  0 ≤ (n: ℤ)+ a:=
begin
have := lt_or_eq_of_le h, cases this,
have H:= nat_abs_inter a n this, have H1:= le_of_lt H.1, have H2:=le_of_lt H.2, simp [H1,H2], rw ← this,
split, exact int.le_nat_abs, rw add_comm, rw ← neg_le_iff_add_nonneg', rw ← int.abs_eq_nat_abs,
simp_rw neg_le_abs_self ,
end


@[simp]lemma square_mem (n : ℕ) (x : ℤ × ℤ ) : x ∈ (Square n) ↔ max (x.1).nat_abs (x.2).nat_abs=n:=
begin
split,
intro x,
rw Square at x, simp at x, simp_rw x,
intro hx, rw Square, simp, simp [hx],
have h2:=max_aux3 _ _ _ hx, have h21:= nat_abs_inter2 _ _ h2.1, have h22:= nat_abs_inter2 _ _ h2.2,
split, split,rw  neg_le_iff_add_nonneg',exact h21.2, have:= h21.1,linarith,
split,rw  neg_le_iff_add_nonneg',exact h22.2, have:= h22.1,linarith,

end

lemma square_mem' (n : ℕ) (x : ℤ × ℤ ) : x ∈ (Square n) ↔  ((x.1).nat_abs=n ∧ (x.2).nat_abs <  n) ∨ ((x.2).nat_abs=n ∧ (x.1).nat_abs < n) ∨ ((x.1).nat_abs=n ∧ (x.2).nat_abs=n) :=
begin
simp, split, intro c1, have:= max_aux3 _ _ _ c1,  have H:= max_aux'' _ _ _ c1, have h1:= this.1, have h2:=this.2,
rw le_iff_lt_or_eq at h2, rw le_iff_lt_or_eq at h1, cases H, simp_rw H, simp,exact h2, simp_rw H, simp,
exact h1,
intro c2, cases c2, rw c2.1,simp, have :=c2.2, linarith,
cases c2, rw c2.1, simp,have:=c2.2, linarith,rw [c2.1,c2.2], simp,
end




lemma auxin (a: ℤ) (n: ℕ)(h: 0 < (n: ℤ)+a):  1 ≤  (n: ℤ)+a:=
begin
assumption,
end


lemma auxin2 (a: ℤ) (n: ℕ)(h: 0 < (n: ℤ)+a):   -(n: ℤ) ≤ a:=
begin
linarith,
end

lemma tofind : (0: ℤ) < 1 ↔  true:=
begin
exact dec_trivial,
end

lemma tofind2 (a : ℕ) : a ≤ a ↔  true:=
begin
simp only [iff_true] at *,
end

lemma cat (a b : ℤ) (n: ℕ)  (h1: b=(n:ℤ)) (h2: -(n:ℤ) ≤ a ∧ a < (n:ℤ)+1 ): b.nat_abs= n ∧ (a.nat_abs < n ∨ a.nat_abs=n) :=
begin
 rw h1, simp, have:=int.nat_abs_eq a,cases this,rw this at h2,norm_cast at h2, have h22:=h2.2,exact nat.lt_succ_iff_lt_or_eq.mp h22,
 rw this at h2,simp at *,have h22:=h2.1, exact lt_or_eq_of_le h22,
end

lemma cat1 (a b : ℤ) (n: ℕ)  (h1: b=-(n:ℤ)) (h2: -(n:ℤ) ≤ a ∧ a < (n:ℤ)+1 ): b.nat_abs= n ∧ (a.nat_abs < n ∨ a.nat_abs=n) :=
begin
 rw h1, simp, have:=int.nat_abs_eq a,cases this,rw this at h2,norm_cast at h2, have h22:=h2.2,exact nat.lt_succ_iff_lt_or_eq.mp h22,
 rw this at h2,simp at *,have h22:=h2.1, exact lt_or_eq_of_le h22,
end

lemma dog (a b : ℤ) (n: ℕ)  (h1: a=(n:ℤ)) (h2: 1 ≤ (n: ℤ)+ b ∧ b < (n:ℤ) ): a.nat_abs= n ∧ b.nat_abs < n :=
begin
 rw h1, simp,  have:=int.nat_abs_eq b, cases this, rw this at h2, norm_cast at h2,exact h2.2,
 rw this at h2, have h22:= h2.1, linarith,
end

lemma dog1 (a b : ℤ) (n: ℕ)  (h1: a=-(n:ℤ)) (h2: 1 ≤ (n: ℤ)+ b ∧ b < (n:ℤ) ): a.nat_abs= n ∧ b.nat_abs < n :=
begin
 rw h1, simp,  have:=int.nat_abs_eq b, cases this, rw this at h2, norm_cast at h2,exact h2.2,
 rw this at h2, have h22:= h2.1, linarith,
end

lemma sqr_eq_sqr2 (n: ℕ): (Square n)=(Square2 n):=
begin
ext1, split, rw square_mem', intro ha,rw Square2, simp_rw int.nat_abs_eq_iff at ha, cases ha, cases ha.1, simp,
have h1:= nat_abs_inter _ _ ha.2, have h2:= auxin _ _ h1.2, simp_rw [h,h1,h2],
simp only [true_or, eq_self_iff_true, or_true, and_self],
simp only [finset.mem_union, finset.union_assoc, finset.mem_singleton, finset.Ico_ℤ.mem, neg_add_le_iff_le_add,
  finset.mem_product],
have h1:= nat_abs_inter _ _ ha.2, have h2:= auxin _ _ h1.2, simp_rw [h,h1,h2],
simp only [true_or, eq_self_iff_true, or_true, and_self], cases ha, cases ha.1,
simp only [finset.mem_union, finset.union_assoc, finset.mem_singleton, finset.Ico_ℤ.mem, neg_add_le_iff_le_add,
  finset.mem_product],
have h1:= nat_abs_inter _ _ ha.2, have h2:= auxin2 _ _ h1.2, simp_rw [h,h2],
simp only [true_and, lt_self_iff_false, and_true, eq_self_iff_true, or_false, and_false], have h3:=h1.1,
have Hk: a.1 < (n: ℤ)+1, by {linarith, }, simp only [Hk, true_or],
simp only [finset.mem_union, finset.union_assoc, finset.mem_singleton, finset.Ico_ℤ.mem, neg_add_le_iff_le_add,
  finset.mem_product],
have h1:= nat_abs_inter _ _ ha.2, have h2:= auxin2 _ _ h1.2, simp_rw [h,h2],
simp only [true_and, and_true, int.coe_nat_pos, eq_self_iff_true, neg_lt_self_iff, add_right_neg], have h3:=h1.1,
have Hk: a.1 < (n: ℤ)+1, by {linarith, }, simp only [Hk, true_or, or_true],simp only [finset.mem_union, finset.union_assoc, finset.mem_singleton, finset.Ico_ℤ.mem, neg_add_le_iff_le_add,
  finset.mem_product],
cases  ha.1, cases  ha.2, simp_rw [h,h_1], have n1: -(n: ℤ) ≤ (n: ℤ), by {linarith,}, simp_rw [n1],
simp only [lt_add_iff_pos_right, true_or, eq_self_iff_true, and_self, zero_lt_one],

simp_rw [h,h_1],  have n1: -(n: ℤ) ≤ (n: ℤ), by {linarith,}, simp_rw [n1],
simp only [lt_add_iff_pos_right, true_or, eq_self_iff_true, or_true, and_self, zero_lt_one],
 cases ha.2, simp_rw [h,h_1],
 simp only [true_and, lt_self_iff_false, le_refl, and_true, eq_self_iff_true, or_false, and_false] at *,
 have n1: -(n: ℤ) < (n: ℤ)+1, by {linarith,} , simp_rw [n1],  simp only [true_or],
have hg: -(n: ℤ) < n+1, by {linarith,}, simp_rw [h,h_1, hg], simp only [le_refl, true_or, eq_self_iff_true, or_true, and_self],

intro ha, rw Square2 at ha,
simp only [finset.mem_union, finset.union_assoc, finset.mem_singleton, finset.Ico_ℤ.mem, neg_add_le_iff_le_add,
  finset.mem_product] at ha, rw square_mem', cases ha, have:= cat _ _ _ ha.2 ha.1, simp_rw this,
simp only [true_and, lt_self_iff_false, and_true, false_or, eq_self_iff_true, and_false], exact this.2,
cases ha,  have:= cat1 _ _ _ ha.2 ha.1, simp_rw this,simp, exact this.2, cases ha, have:= dog _ _ _ ha.1 ha.2,
simp_rw this,simp only [true_or, eq_self_iff_true, and_self],
 have:= dog1 _ _ _ ha.1 ha.2,  simp_rw this,simp only [true_or, eq_self_iff_true, and_self],
end


lemma Square_size (n : ℕ) (h: 1 ≤ n) : finset.card (Square (n))=8*(n):=
begin
rw sqr_eq_sqr2, apply square2_card, exact h,
end

lemma Squares_are_disjoint: ∀ (i j : ℕ), i ≠ j → disjoint (Square i) (Square j):=
begin
intros i j hij,  rw finset.disjoint_iff_ne, intros a ha, simp at ha,intros b hb, simp at hb,by_contradiction,
simp at h,rw h at ha, rw hb at ha,induction ha, induction h,
cases a, induction hb, cases b, dsimp at *, simp at *, assumption,

end

lemma Squares_cover_all :  ∀ (y : ℤ × ℤ), ∃! (i : ℕ), y ∈ Square (i) :=
begin
intro y, use max y.1.nat_abs y.2.nat_abs,simp only [square_mem, and_self, forall_eq'],
end



lemma Square_zero : Square (0: ℕ)={(0,0)}:=
begin
refl,
end

lemma Square_zero_card: finset.card (Square 0)=1:=
begin
rw Square_zero, refl,
end




/- Some summable lemmas-/

variables {α : Type u} {β : Type v} {γ : Type w} {i : α → set β}

instance  (a: α): has_lift_t (i a) (set.Union i):=
begin
fsplit, intros ᾰ, cases ᾰ, fsplit, work_on_goal 1 { simp at *, fsplit, work_on_goal 1 { assumption } },
end



instance: has_coe_t  (finset (ℤ × ℤ))  (set (ℤ × ℤ)):=infer_instance

def coef (s : finset (ℤ × ℤ)): set (ℤ × ℤ):=
(s: set (ℤ × ℤ ))

def fn (In: ℕ → finset (ℤ × ℤ))  (HI: ∀ (y : ℤ × ℤ), ∃! (i : ℕ), y ∈ In (i) ) (x : ℤ × ℤ): x ∈  (⋃ (s: ℕ), coef (In s)):=
begin

have h1:=HI x,
rw set.mem_Union, cases h1, cases x, cases h1_h, dsimp at *, simp at *, fsplit, work_on_goal 1 { assumption },
end

def fnn  (In: ℕ → finset (ℤ × ℤ))  (HI: ∀ (y : ℤ × ℤ), ∃! (i : ℕ), y ∈ In (i) ) (x:  ℤ × ℤ)  : (⋃ (s: ℕ), coef (In s)):=
⟨x, fn In HI x⟩


def union_equiv (In: ℕ → finset (ℤ × ℤ))  (HI: ∀ (y : ℤ × ℤ), ∃! (i : ℕ), y ∈ In (i) ) : (⋃ (s: ℕ), coef (In s)) ≃ ℤ × ℤ:=
{
to_fun:=λ x, x.1 ,
inv_fun:=λ x,   fnn In HI x,
left_inv:= by {simp, intros x, cases x, refl},
right_inv:=by {simp, intros x, refl}
}





lemma unionmem (i: α → set β) (x : α) (y : i x): (coe y)  ∈ (⋃ x, i x):=
begin
simp, use x, cases y, assumption,
end




lemma summable_disjoint_union_of_nonneg {i : α →  set β} {f : (⋃ x, i x) → ℝ} (h: ∀ a b, a ≠ b →  disjoint (i a) (i b)) (hf : ∀ x, 0 ≤ f x) :
  summable f ↔ (∀ x, summable (λ (y : i x), f ⟨y, unionmem i x y⟩ )) ∧ summable (λ x, ∑' (y : i x), f ⟨y , unionmem i x y⟩) :=
 begin
let h0:=(set.Union_eq_sigma_of_disjoint h).symm,
have h01: summable f ↔ summable ( f ∘ h0 ), by {have:= equiv.summable_iff h0 , rw this, },
have h22: ∀ y : (Σ (s: α ), i s), 0 ≤ (f ∘ h0) y:= by {simp_rw h0,
 rw set.Union_eq_sigma_of_disjoint, simp only [equiv.symm_symm, function.comp_app, sigma.forall, equiv.of_bijective_apply], simp_rw set.sigma_to_Union, simp_rw hf, simp only [forall_2_true_iff],},
have h1:=summable_sigma_of_nonneg h22 ,
rw h01, rw h1,
have H1: ∀ (x : α), summable (λ (y : (λ (s : α), ↥(i s)) x), f (h0 ⟨x, y⟩)) ↔ summable (λ (y : ↥(i x)), f ⟨y,  unionmem i x y⟩),
 by {
  intro x, dsimp, simp_rw h0, rw set.Union_eq_sigma_of_disjoint, simp only [equiv.symm_symm, equiv.of_bijective_apply], simp_rw set.sigma_to_Union, },
simp_rw H1, simp only [ and.congr_right_iff], intro hfin,
have H2: ∀  (x : α), ∑' (y : (λ (s : α), ↥(i s)) x), (f ∘ ⇑h0) ⟨x, y⟩=∑' (y : ↥(i x)), f ⟨↑y, unionmem i x y⟩, by {
  intro x, simp only [function.comp_app], simp_rw h0,  rw set.Union_eq_sigma_of_disjoint, simp only [equiv.symm_symm, equiv.of_bijective_apply], simp_rw set.sigma_to_Union,},

simp_rw H2,
 end


lemma tsum_disjoint_union_of_nonneg' {i : α →  set β} {f : (⋃ x, i x) → ℝ} (h: ∀ a b, a ≠ b →  disjoint (i a) (i b))
 (h1: summable f):
 ∑' x, f x= ∑' x , ∑' (y : i x), f ⟨y , unionmem i x y⟩   :=
 begin
let h0:=(set.Union_eq_sigma_of_disjoint h).symm,
have h01: ∑' x, f x = ∑' y , ( f  (h0 y)) , by {have:= equiv.tsum_eq h0 f,rw ← this,   },
rw h01,  rw tsum_sigma, simp_rw h0,  rw set.Union_eq_sigma_of_disjoint,simp, simp_rw set.sigma_to_Union,
have h01: summable f ↔ summable ( f ∘ h0 ), by {have:= equiv.summable_iff h0 , rw this, },
rw ← h01, exact h1,
 end
lemma tsum_disjoint_union_of_nonneg'' {i : α →  set β} {f : (⋃ x, i x) → ℂ} (h: ∀ a b, a ≠ b →  disjoint (i a) (i b))
 (h1: summable f):
 ∑' x, f x= ∑' x , ∑' (y : i x), f ⟨y , unionmem i x y⟩   :=
 begin
let h0:=(set.Union_eq_sigma_of_disjoint h).symm,
have h01: ∑' x, f x = ∑' y , ( f  (h0 y)) , by {have:= equiv.tsum_eq h0 f,rw ← this,   },
rw h01,  rw tsum_sigma, simp_rw h0,  rw set.Union_eq_sigma_of_disjoint,simp, simp_rw set.sigma_to_Union,
have h01: summable f ↔ summable ( f ∘ h0 ), by {have:= equiv.summable_iff h0 , rw this, },
rw ← h01, exact h1,
 end


lemma disjoint_aux (In: ℕ → finset (ℤ × ℤ))  (HI: ∀ (y : ℤ × ℤ), ∃! (i : ℕ), y ∈ In (i) ) : ∀ (i j : ℕ), i ≠ j → disjoint (In i) (In j):=
begin
intros i j h, intros a α, cases a, dsimp at *, simp at *, cases α,
have HI0:=HI a_fst a_snd,
have:= exists_unique.unique HI0 α_left α_right, rw this at h, simp at *, exact h,
end



lemma sum_lemma (f: ℤ × ℤ → ℝ) (h: ∀ y : ℤ × ℤ, 0 ≤ f y) (In: ℕ → finset (ℤ × ℤ))  (HI: ∀ (y : ℤ × ℤ), ∃! (i : ℕ), y ∈ In (i) )  :
summable f ↔ summable (λ ( n : ℕ), ∑ x in In (n), f x)  :=
begin
let h2:= union_equiv In HI,
have h22: ∀ y : (⋃ (s: ℕ), coef (In s)), 0 ≤ (f ∘ h2) y:= by {simp_rw h2, simp_rw union_equiv, simp,
simp_rw coef, simp_rw h, simp only [forall_const, implies_true_iff],},
have hdis':=disjoint_aux In HI,
have h5: ∀ (x : ℕ), finset ((coef (In x))), by {intro x, rw coef, exact finset.univ,},
have hg:∀ (x : ℕ), (coef (In x))={y : ℤ × ℤ | y ∈ In x}, by {intros x, refl,},
have hdis:∀ (a b : ℕ) , a ≠ b →  disjoint (coef (In a)) (coef (In b)), by {intros a b hab, simp_rw coef,
rw ← finset.disjoint_iff_disjoint_coe, apply hdis', exact hab,},
have h3:=summable_disjoint_union_of_nonneg  hdis h22 ,
have h4: summable f ↔ summable (f ∘ h2), by {have:= equiv.summable_iff h2 , rw this, },
rw h4, rw h3, simp only [function.comp_app], dsimp,

have h6: ∀ (x : ℕ), ∑' (y : ↥(coef (In x))), f (h2 ⟨y,_⟩) = ∑ y in  (In x), f y, by {
  simp only, intro x, apply finset.tsum_subtype', },
simp_rw h6,  simp only [and_iff_right_iff_imp], simp_rw h2, rw union_equiv,  simp only [equiv.coe_fn_mk, subtype.coe_mk],
intros H x, rw hg, apply finset.summable,
 apply unionmem,

end


lemma tsum_lemma (f: ℤ × ℤ → ℝ) (In: ℕ → finset (ℤ × ℤ))  (HI: ∀ (y : ℤ × ℤ), ∃! (i : ℕ), y ∈ In (i) )
(hs :summable f): ∑' x, f x =  ∑'  ( n : ℕ), (∑ x in In (n), f x)  :=
begin
let h2:= union_equiv In HI,
have hdis':=disjoint_aux In HI,
have h5: ∀ (x : ℕ), finset ((coef (In x))), by {intro x, rw coef, exact finset.univ,},
have hg:∀ (x : ℕ), (coef (In x))={y : ℤ × ℤ | y ∈ In x}, by {intros x, refl,},
have hdis:∀ (a b : ℕ) , a ≠ b →  disjoint (coef (In a)) (coef (In b)), by {intros a b hab, simp_rw coef,
rw ← finset.disjoint_iff_disjoint_coe, apply hdis', exact hab,},

have h6: ∀ (x : ℕ), ∑' (y : ↥(coef (In x))), f (h2 ⟨y,_⟩) = ∑ y in  (In x), f y, by {
  simp only, intro x, apply finset.tsum_subtype', },
simp_rw h6,
have HS:summable (f ∘ h2), by {rw equiv.summable_iff  h2, exact hs,},

have HH:= tsum_disjoint_union_of_nonneg'  hdis HS, simp at HH, have:= equiv.tsum_eq h2 f, rw ← this,
rw HH, simp_rw h6, apply unionmem,
end

lemma tsum_lemma' (f: ℤ × ℤ → ℂ) (In: ℕ → finset (ℤ × ℤ))  (HI: ∀ (y : ℤ × ℤ), ∃! (i : ℕ), y ∈ In (i) )
(hs :summable f): ∑' x, f x =  ∑'  ( n : ℕ), (∑ x in In (n), f x)  :=
begin
let h2:= union_equiv In HI,
have hdis':=disjoint_aux In HI,
have h5: ∀ (x : ℕ), finset ((coef (In x))), by {intro x, rw coef, exact finset.univ,},
have hg:∀ (x : ℕ), (coef (In x))={y : ℤ × ℤ | y ∈ In x}, by {intros x, refl,},
have hdis:∀ (a b : ℕ) , a ≠ b →  disjoint (coef (In a)) (coef (In b)), by {intros a b hab, simp_rw coef,
rw ← finset.disjoint_iff_disjoint_coe, apply hdis', exact hab,},

have h6: ∀ (x : ℕ), ∑' (y : ↥(coef (In x))), f (h2 ⟨y,_⟩) = ∑ y in  (In x), f y, by {
  simp only, intro x, apply finset.tsum_subtype', },
simp_rw h6,
have HS:summable (f ∘ h2), by {rw equiv.summable_iff  h2, exact hs,},

have HH:= tsum_disjoint_union_of_nonneg''  hdis HS, simp at HH, have:= equiv.tsum_eq h2 f, rw ← this,
rw HH, simp_rw h6, apply unionmem,
end

lemma realpow (n : ℕ ) (k : ℤ): (n: ℝ)^((k : ℝ)-1)= n^(k-1):=
begin
have:=real.rpow_int_cast (n: ℝ) (k-1), rw ← this, simp only [int.cast_one, int.cast_sub],
end




lemma summable_if_complex_abs_summable {f : α → ℂ} :
  summable (λ x, complex.abs (f x)) →  summable f :=
begin
intro h,
apply summable_of_norm_bounded  (λ x, complex.abs (f x))  h,
intro i,
unfold norm, exact complete_of_proper,
end

lemma upper_gt_zero (z: ℍ) : 0<(z: ℂ ).im:=
begin
 have H:= z.property,  simp at H,  apply H,
end

def lb (z: ℍ): ℝ:=((z.1.2)^4 + (z.1.1*z.1.2)^2)/(z.1.1^2+z.1.2^2)^2

lemma lb_pos (z : ℍ): 0 < lb z :=
begin
rw lb, simp,
have H1: 0 < ((z.1.2)^4 + (z.1.1*z.1.2)^2), by {rw add_comm, apply add_pos_of_nonneg_of_pos,   nlinarith,
have h1: z.1.2^4=z.1.2^2*z.1.2^2, ring, rw h1, apply mul_pos, simp, have:=upper_gt_zero z, rw pow_two, apply mul_pos, exact this, exact this,
simp, have:=upper_gt_zero z, rw pow_two, apply mul_pos, exact this, exact this, },
have H2: 0 < (z.1.1^2+z.1.2^2)^2, by {nlinarith,},
have H3: ((z.1.2)^4 + (z.1.1*z.1.2)^2)/(z.1.1^2+z.1.2^2)^2=((z.1.2)^4 + (z.1.1*z.1.2)^2)*((z.1.1^2+z.1.2^2)^2)⁻¹ , by {ring,},
simp at H3, rw H3,
have H4: 0 < ((z.1.1^2+z.1.2^2)^2)⁻¹, by {rw inv_pos, exact H2,},
apply mul_pos H1 H4,
end

def rfunct (z: ℍ): ℝ:=
min (real.sqrt((z.1.2)^2)) (real.sqrt(lb z))

lemma rfunct_pos (z : ℍ): 0 < (rfunct z):=
begin
 have H:= z.property, simp at H,
rw rfunct, simp, split, rw pow_two, apply mul_pos, exact H, exact H, apply lb_pos,
end


lemma alem (a b c : ℝ): (a-b) ≤ a+c ↔ -b ≤ c:=
begin
have: a-b= a+(-b), by {ring,},
split,
rw this, simp_rw add_le_add_iff_left, simp,
rw this, simp_rw add_le_add_iff_left, simp,
end

lemma ineq1 (x y d: ℝ  ): 0 ≤ d^2*(x^2+y^2)^2+2*d*x*(x^2+y^2)+x^2:=
begin
have h1: d^2*(x^2+y^2)^2+2*d*x*(x^2+y^2)+x^2 =(d*(x^2+y^2)+x)^2, by {ring,},
rw h1,
nlinarith,
end

lemma lowbound (z : ℍ) (δ : ℝ): ((z.1.2)^4 + (z.1.1*z.1.2)^2)/(z.1.1^2+z.1.2^2)^2 ≤ (δ*z.1.1+1)^2+(δ*z.1.2)^2:=
begin
simp,
have H1: (δ*z.1.1+1)^2+(δ*z.1.2)^2=δ^2*(z.1.1^2+z.1.2^2)+2*δ*z.1.1+1, by {ring,}, simp at H1, rw H1, rw div_le_iff, simp,
have H2: (δ ^ 2 * ( (z: ℂ).re ^ 2 +  (z: ℂ).im ^ 2) + 2 * δ *  (z: ℂ).re + 1) * ( (z: ℂ).re ^ 2 +  (z: ℂ).im ^ 2) ^ 2=δ ^ 2 * ( (z: ℂ).re ^ 2 +  (z: ℂ).im ^ 2)^3 + 2 * δ *  (z: ℂ).re* ( (z: ℂ).re ^ 2 +  (z: ℂ).im ^ 2) ^ 2+   ( (z: ℂ).re ^ 2 +  (z: ℂ).im ^ 2) ^ 2,
by {ring,}, simp at H2, rw H2, rw ← sub_nonneg,
have H3:( (z: ℂ).re ^ 2 +  (z: ℂ).im ^ 2) ^ 2-((z: ℂ).im ^ 4 + ((z: ℂ).re * (z: ℂ).im) ^ 2)=((z: ℂ).re)^2*( (z: ℂ).re ^ 2 +  (z: ℂ).im ^ 2), by {ring,},


have H4: δ ^ 2 * ((z: ℂ).re ^ 2 + (z: ℂ).im ^ 2) ^ 3 + 2 * δ * (z: ℂ).re * ((z: ℂ).re ^ 2 + (z: ℂ).im ^ 2) ^ 2 + ((z: ℂ).re ^ 2 + (z: ℂ).im ^ 2) ^ 2 - ((z: ℂ).im ^ 4 + ((z: ℂ).re * (z: ℂ).im) ^ 2)=(((z: ℂ).re ^ 2 + (z: ℂ).im ^ 2))*(δ ^ 2 * ((z: ℂ).re ^ 2 + (z: ℂ).im ^ 2)^2 + 2 * δ * (z: ℂ).re * ((z: ℂ).re ^ 2 + (z: ℂ).im ^ 2) +(z: ℂ).re ^ 2), by {ring,},
simp at H4, rw H4,
have H5: 0 ≤ (δ ^ 2 * ((z: ℂ).re ^ 2 + (z: ℂ).im ^ 2)^2 + 2 * δ * (z: ℂ).re * ((z: ℂ).re ^ 2 + (z: ℂ).im ^ 2) +(z: ℂ).re ^ 2), by {apply ineq1,},
have H6: 0 ≤ (((z: ℂ).re ^ 2 + (z: ℂ).im ^ 2)), by {nlinarith,},
apply mul_nonneg H6 H5,
have H7:= z.property, simp at H7,
have H8:0 < (z: ℂ).im ^ 2, by {simp [H7], },
have H9: 0 <((z: ℂ).im ^ 2+(z: ℂ).re ^ 2), by {nlinarith,},
apply pow_two_pos_of_ne_zero,
nlinarith,
end





lemma auxlem (z : ℍ) (δ : ℝ) : (rfunct z) ≤ complex.abs ( (z: ℂ)+δ ) ∧ (rfunct z) ≤ complex.abs ( δ*(z: ℂ) +1):=
begin
split,
{
rw rfunct, rw complex.abs, rw norm_sq, simp only [add_zero, of_real_im, monoid_with_zero_hom.coe_mk, of_real_re, add_re, add_im, min_le_iff, subtype.val_eq_coe],
have H1: real.sqrt (((z: ℂ).im)^2) ≤ real.sqrt (((z: ℂ).re + δ) * ((z: ℂ).re + δ) + (z: ℂ).im * (z: ℂ).im), by {
  rw real.sqrt_le_sqrt_iff, nlinarith,nlinarith,
},
simp_rw H1, simp,

},

{
  rw rfunct, rw complex.abs, rw norm_sq, simp,
 have H1:  real.sqrt (lb z) ≤ real.sqrt ((δ*(z: ℂ).re  + 1) * (δ*(z: ℂ).re  + 1) + δ*(z: ℂ).im *  (δ*(z: ℂ).im )), by {
   rw lb, rw real.sqrt_le_sqrt_iff,have:= lowbound z δ, rw ← pow_two, rw ← pow_two,  simp at *, apply this,nlinarith,}, simp at H1,
  simp_rw H1, simp,
  },


end

lemma complex_abs_pow' (k : ℕ) (a : ℂ): complex.abs (a^k)= (complex.abs (a))^k:=
begin
induction k with n hd, simp, rw [pow_succ, pow_succ], have h1:= complex.abs_mul (a) (a^n), rw hd at h1, apply h1,
end

lemma complex_abs_pow (k : ℤ) (a : ℂ): complex.abs (a^k)= (complex.abs (a))^k:=
begin
induction k with n hd, apply complex_abs_pow', simp , apply complex_abs_pow',
end

lemma le_of_pow' (a b : ℝ) (k: ℕ)(h : 0 ≤ a) (h2: 0 ≤ b) (h3: a ≤ b): a^k ≤ b^k:=
begin
exact pow_le_pow_of_le_left h h3 k,
end




lemma baux (a : ℝ) (k : ℕ) (b : ℂ) (h: 0 ≤ a) (h2: a ≤ complex.abs b): a^k ≤ complex.abs (b^k):=
begin
rw complex_abs_pow', apply le_of_pow', exact h, apply complex.abs_nonneg, exact h2,

end


lemma baux2 (z : ℍ) (k: ℕ): complex.abs ((rfunct z)^k)=(rfunct z)^k:=
begin
norm_cast,
let a:=rfunct z, simp,
have ha: 0 ≤ a, by {simp_rw a, have:= rfunct_pos z , apply le_of_lt this, },
have:= complex.abs_of_nonneg ha, norm_cast at this, simp_rw a at this, rw this,
end

lemma auxlem2 (z : ℍ) (n : ℕ)  (x: ℤ × ℤ) (h2: x ∈ Square n) (k : ℕ)  :   complex.abs (((rfunct z): ℂ)^k) ≤   complex.abs (( (z: ℂ)+(x.2: ℂ)/(x.1 : ℂ) )^k):=

begin
norm_cast,
have H1: complex.abs ((rfunct z)^k)=(rfunct z)^k, by {apply baux2,}, norm_cast at H1, rw H1,  apply baux, have:= rfunct_pos z, apply le_of_lt this,
have:= auxlem z ((x.2/x.1): ℝ), norm_cast at this, apply this.1,
end


lemma auxlem3 (z : ℍ) (n : ℕ)  (x: ℤ × ℤ) (h2: x ∈ Square n) (k : ℕ)  :   complex.abs (((rfunct z): ℂ)^k) ≤   complex.abs (( ((x.1: ℂ)/(x.2 : ℂ))*(z: ℂ) +1)^k):=

begin
norm_cast,
have H1:= (baux2 z k), norm_cast at H1, rw H1,  apply baux, have:= rfunct_pos z, apply le_of_lt this,
have:= auxlem z ((x.1/x.2): ℝ), norm_cast at *, apply this.2,
end

lemma Eise_on_square_is_bounded ( k : ℕ) (z : ℍ) (n : ℕ) (x: ℤ × ℤ) (h: x ∈ Square n) (hn: 1 ≤ n):  (complex.abs(((x.1: ℂ)*z+(x.2: ℂ))^k))⁻¹ ≤ (complex.abs ((rfunct z)^k* n^k))⁻¹ :=
begin
by_cases C1: complex.abs (x.1: ℂ)=n,
rw inv_le_inv,
have h0: (x.1:ℂ) ≠ 0, by {norm_cast, intro hx, rw hx at C1, simp only [int.cast_zero, complex.abs_zero] at C1, norm_cast at C1, rw ← C1 at hn, simp only [nat.one_ne_zero, le_zero_iff] at hn, exact hn,},
have h1:(↑(x.fst) * ↑z + ↑(x.snd)) ^ k =  (↑(x.fst))^k* ((z: ℂ)+(x.2: ℂ)/(↑(x.fst)))^k, by { rw ← mul_pow, rw div_eq_mul_inv,
have: (x.fst: ℂ) * ((z: ℂ)  + (x.snd: ℂ) * ((x.fst: ℂ))⁻¹)=(x.fst: ℂ) * (z: ℂ) + (x.snd: ℂ), by {
 have p1: (x.fst: ℂ) * ((z: ℂ)  + (x.snd: ℂ) * ((x.fst: ℂ))⁻¹)= ((x.fst: ℂ) * (z: ℂ)  + (x.fst : ℂ) * ((x.fst: ℂ))⁻¹ * (x.snd: ℂ)),
 ring,  rw mul_inv_cancel at p1, simp only [one_mul] at p1,rw p1, exact h0,},rw this,


},
rw h1, rw complex.abs_mul, rw complex.abs_mul,
have h3: complex.abs (↑(x.fst) ^ k)=  (complex.abs (↑(x.fst)))^k , by {apply complex_abs_pow', },
rw h3, rw C1,
have h4: complex.abs (↑n ^ k)=↑n ^ k, by {norm_cast, },


rw h4, rw mul_comm, apply mul_le_mul_of_nonneg_left,
have:=auxlem2 z n  x h k , apply this, norm_cast, simp only [zero_le'], simp only [complex.abs_pos, ne.def],
have hh : ((x.fst): ℂ) * (z: ℂ) + (x.snd: ℂ) ≠ 0, by {
intro H,
have H1 : x.1 = 0 ∨ (z: ℂ).im = 0, by simpa using congr_arg complex.im H,
cases H1, {rw H1 at C1, simp only [int.cast_zero, complex.abs_zero] at C1, norm_cast at C1, rw ← C1 at hn, simp only [nat.one_ne_zero, square_mem, le_zero_iff] at *, exact hn,},
have HH:= z.property, simp only [subtype.val_eq_coe] at HH, rw H1 at HH, simp at HH, exact HH,},
apply pow_ne_zero, exact hh, simp only [complex.abs_mul], apply mul_pos, rw complex.abs_pos, apply pow_ne_zero, have:= rfunct_pos z,
norm_cast, intro np, rw np at this, simp only [lt_self_iff_false] at this, exact this, simp only [complex.abs_pos], apply pow_ne_zero, norm_cast,
intro Hn, rw Hn at hn, simp only [nat.one_ne_zero, le_zero_iff] at hn, exact hn,

have C2: complex.abs (x.2: ℂ)=n, by {simp only [square_mem] at h, have:=max_aux'' x.1.nat_abs x.2.nat_abs n h, norm_cast,
cases this, by_contra, norm_cast at C1, rw ← this at C1, rw int.abs_eq_nat_abs at C1, simp only [eq_self_iff_true, not_true] at C1, exact C1,
rw ← this, rw int.abs_eq_nat_abs,},


 rw inv_le_inv,
have h0: (x.2: ℂ ) ≠ 0, by {norm_cast, intro hx, rw hx at C2,simp only [int.cast_zero, complex.abs_zero] at C2, norm_cast at C2, rw ← C2 at hn, simp only [nat.one_ne_zero, le_zero_iff] at hn, exact hn,},
have h1:(↑(x.fst) * ↑z + ↑(x.snd)) ^ k =  (↑(x.snd))^k* (((x.1:ℂ)/(x.2: ℂ))*(z: ℂ)+1)^k, by {
  rw ← mul_pow,simp only, rw div_eq_mul_inv,
  have: (x.snd: ℂ) * ((x.fst: ℂ) * ((x.snd: ℂ))⁻¹ * (z:ℂ) + 1)=((x.snd: ℂ ) * ((x.snd : ℂ))⁻¹ * (x.fst : ℂ )* (z: ℂ) + (x.snd: ℂ)), by {ring,},
  rw this, rw mul_inv_cancel, simp only [one_mul], exact h0,},
rw h1, rw complex.abs_mul, rw complex.abs_mul,
have h3: complex.abs (↑(x.2) ^ k)=  (complex.abs (↑(x.2)))^k , by {apply complex_abs_pow', },
rw h3, rw C2,
have h4: complex.abs (↑n ^ k)=↑n ^ k, by {norm_cast, }, rw h4, rw mul_comm, apply mul_le_mul_of_nonneg_left,
have:=auxlem3 z n  x h k , apply this, norm_cast, simp only [zero_le'],
have hh : ((x.fst): ℂ) * (z: ℂ) + (x.snd: ℂ) ≠ 0, by {
 intro H,
 have H1 : x.1 = 0 ∨ (z: ℂ).im = 0, by simpa using congr_arg complex.im H,
 cases H1,
 {rw H1 at H, simp only [int.cast_eq_zero, int.cast_zero, zero_mul, zero_add] at H, rw H at C2, simp only [int.cast_zero, complex.abs_zero] at C2, norm_cast at C2, rw ← C2 at hn, simp only [nat.one_ne_zero, square_mem, le_zero_iff] at *, exact hn},
 have HH:= z.property, simp only [subtype.val_eq_coe] at HH, rw H1 at HH, simp only [lt_self_iff_false] at HH, exact HH,},
rw complex.abs_pos, apply pow_ne_zero, exact hh,simp only [complex.abs_mul], apply mul_pos,  rw complex.abs_pos, apply pow_ne_zero, have:= rfunct_pos z,
norm_cast, intro np, rw np at this,  simp only [lt_self_iff_false] at this, exact this, simp only [complex.abs_pos], apply pow_ne_zero, norm_cast,
intro Hn, rw Hn at hn, simp only [nat.one_ne_zero, le_zero_iff] at hn, exact hn,

end



lemma Eise_on_square_is_bounded' ( k : ℕ) (z : ℍ) (n : ℕ) (hn: 1 ≤ n): ∀ (x: ℤ × ℤ),  x ∈ (Square n) →  (complex.abs(((x.1: ℂ)*z+(x.2: ℂ))^k))⁻¹ ≤ (complex.abs ((rfunct z)^k* n^k))⁻¹ :=
begin
intros x hx,
apply Eise_on_square_is_bounded k z n x hx hn,
end



lemma Eise_on_zero_Square (k : ℕ) (z : ℍ) (h: 1 ≤ k) :∀ (x: ℤ × ℤ),  x ∈ (Square 0) →  (complex.abs(((x.1: ℂ)*z+(x.2: ℂ))^k))⁻¹ ≤ (complex.abs ((rfunct z)^k* 0^k))⁻¹ :=
begin
intros x hx, rw Square_zero at hx, simp only [finset.mem_singleton] at hx, simp_rw hx, simp only [add_zero, int.cast_zero, zero_mul, complex.abs_mul],
have h1: (0: ℂ)^k=0, by {rw zero_pow_eq_zero, linarith,}, rw h1, rw complex.abs_zero, simp only [mul_zero],
end

lemma Eise_on_square_is_bounded'' ( k : ℕ) (z : ℍ) (n : ℕ) (hn: 1 ≤ k): ∀ (x: ℤ × ℤ),  x ∈ (Square n) →  (complex.abs(((x.1: ℂ)*z+(x.2: ℂ))^k))⁻¹ ≤ (complex.abs ((rfunct z)^k* n^k))⁻¹ :=
begin
by_cases h0: n=0,
{rw h0, apply Eise_on_zero_Square k z hn, },
have Hn: 1 ≤ n, by {have:=nat.pos_of_ne_zero, simp at this, work_on_goal 0 { cases z, solve_by_elim },},
intros x hx,
apply Eise_on_square_is_bounded k z n x hx Hn,
end




lemma natpows (x : ℝ) (n : ℤ)  (h2: x ≠ 0): x^(n-1)=x^n*x⁻¹:=
begin
apply fpow_sub_one, apply h2,


end

lemma natpowsinv (x : ℝ) (n : ℤ)  (h2: x ≠ 0): (x^(n-1))⁻¹=(x^n)⁻¹*x:=
begin
have:=natpows x n  h2, rw this, have h3:=mul_fpow (x^n) (x⁻¹) (-1), rw fpow_neg at h3, simp at h3, exact h3,
end

lemma BigClaim (k : ℕ) (z : ℍ) (h : 3 ≤ k):
∀ (n: ℕ), ∑ (y: ℤ × ℤ) in (Square n), ((real_Eise k z) y)  ≤(8/((rfunct z)^k))*(n^((k: ℤ)-1))⁻¹:=
begin
intro n,
rw real_Eise, simp,
have k0: 1 ≤ k, by {linarith,},
have BO:=  Eise_on_square_is_bounded'' ( k : ℕ) (z : ℍ) (n : ℕ) k0,
by_cases n0: n=0, { rw n0, rw Square_zero,
simp only [add_zero, int.cast_zero, nat.cast_zero, zero_mul, finset.sum_singleton],
have H0: (0: ℂ)^k=0, by {rw zero_pow_eq_zero, linarith,}, rw H0, simp only [complex.abs_zero, inv_zero],
have H00: (0: ℝ)^((k: ℤ)-1)=0, by { rw zero_fpow, linarith,}, rw H00, simp only [inv_zero, mul_zero],},
have:= finset.sum_le_sum BO, simp only [finset.sum_const, complex.abs_mul, nsmul_eq_mul] at this,

 rw Square_size n at this,
norm_cast at this,
have ne:( (8 * n) * (complex.abs (rfunct z ^ k) * ((n ^ k): ℝ))⁻¹ : ℝ)= (8/((rfunct z)^k))*(n^((k: ℤ)-1))⁻¹,
by {rw complex_abs_pow', rw complex.abs_of_nonneg, rw ← mul_pow, rw div_eq_inv_mul,
have:8* ↑n * ((rfunct z * ↑n) ^ k)⁻¹= 8*((rfunct z)^k)⁻¹ * (↑n^((k: ℤ)-1))⁻¹, by {
 have dis: ((rfunct z * ↑n) ^ k)⁻¹=((rfunct z)^k)⁻¹* (↑n^k)⁻¹, by {rw mul_pow,
 rw [← fpow_neg_one,← fpow_neg_one,← fpow_neg_one], rw ← mul_fpow,},
 simp [dis], rw natpowsinv, ring, norm_cast,  intro hN, rw hN at n0,
 simp only [eq_self_iff_true, not_true] at n0, exact n0,},
rw this, ring, have rpos:= rfunct_pos z, apply le_of_lt rpos,},
norm_cast at ne, rw ne at this, norm_cast,  apply this, have hhh:= nat.pos_of_ne_zero n0, linarith,

end


lemma SmallClaim (k : ℕ) (z : ℍ) (h : 3 ≤ k):
 ∀ (n : ℕ), (λ (x: ℕ), ∑ (y : ℤ × ℤ) in (Square x),  (real_Eise k z) y) n ≤  (8/(rfunct z)^k) * ((rie (k-1)) n):=
begin
 have BIGCLAIM:= BigClaim k z h,
 simp only at BIGCLAIM, rw rie, simp only [one_div], intro n,
 have tr :((↑n ^ ((k: ℤ) - 1))⁻¹: ℝ)=((↑n ^ ((k: ℝ) - 1))⁻¹: ℝ), by {simp only [inv_inj'],
 have:= realpow n k,
 norm_cast at this, rw ← this, simp only [int.cast_coe_nat, int.cast_one, int.cast_sub],},
 rw ← tr, apply BIGCLAIM n,
end


lemma real_eise_is_summable (k : ℕ) (z : ℍ) (h : 3 ≤ k): summable (real_Eise k z):=
begin
let In:=Square,
have HI:=Squares_cover_all,
let g:= λ (y : ℤ × ℤ), (real_Eise k z) y,
have gpos: ∀ (y : ℤ × ℤ), 0 ≤ g y, by {simp_rw g, intro y, rw real_Eise, simp,apply complex.abs_nonneg,},
have index_lem:= sum_lemma g  gpos In HI,
rw index_lem,

let e:=λ (x: ℕ), ∑ (y : ℤ × ℤ) in (In x), g y,




have BIGCLAIM: ∀ (n : ℕ), ∑ (y : ℤ × ℤ) in (In n), g y ≤(8/((rfunct z)^k))*(n^((k: ℤ)-1))⁻¹, by {

simp_rw g,
apply BigClaim k z h,
},

have smallerclaim:  ∀ (n : ℕ), e n ≤  (8/(rfunct z)^k) * ((rie (k-1)) n), by {
simp_rw e,
apply SmallClaim k z h,
},

have epos: ∀ (x : ℕ), 0 ≤ e x, by {simp_rw e, simp_rw g, intro x,
apply finset.sum_nonneg,  intros i hi, apply complex.abs_nonneg, },

have hk: 1 < ((k-1): ℤ), by { linarith, },
have nze: ((8/((rfunct z)^k)): ℝ)  ≠ 0, by {apply div_ne_zero, simp, apply pow_ne_zero,
 simp, by_contra HR, have:=rfunct_pos z, rw HR at this, simp at this, exact this, },
have riesum:=int_Riemann_zeta_is_summmable (k-1) hk,

have riesum': summable (λ (n : ℕ), (8 / (rfunct z)^k) * rie (↑k - 1) n), by {
  rw (summable_mul_left_iff nze).symm, simp at riesum, apply riesum,},
have:=summable_of_nonneg_of_le epos smallerclaim,

apply this,
apply riesum',
end


lemma Real_Eisenstein_bound (k : ℕ) (z : ℍ) (h : 3 ≤ k):
    (real_Eisenstein_series_of_weight_ k z) ≤ (8/(rfunct z)^k)*Riemann_zeta (k-1):=
begin
rw real_Eisenstein_series_of_weight_,rw Riemann_zeta,
  rw ← tsum_mul_left, let In:=Square,
have HI:=Squares_cover_all,
let g:= λ (y : ℤ × ℤ), (real_Eise k z) y,
have gpos: ∀ (y : ℤ × ℤ), 0 ≤ g y, by {simp_rw g, intro y, rw real_Eise, simp,apply complex.abs_nonneg,},
have hgsumm: summable g, by {simp_rw g, apply real_eise_is_summable k z h, },
have index_lem:= tsum_lemma g In HI hgsumm, simp_rw g at index_lem, simp, rw index_lem,
have ind_lem2:=sum_lemma g gpos In HI,


have smallclaim:= SmallClaim k z h,
have hk: 1 < ((k-1): ℤ), by { linarith, },
have nze: ((8/((rfunct z)^k)): ℝ)  ≠ 0, by {apply div_ne_zero, simp, apply pow_ne_zero,
 simp, by_contra HR, have:=rfunct_pos z, rw HR at this, simp at this, exact this, },
have riesum:=int_Riemann_zeta_is_summmable (k-1) hk,


have riesum': summable (λ (n : ℕ), (8 / (rfunct z)^k) * rie (↑k - 1) n), by {
  rw (summable_mul_left_iff nze).symm, simp at riesum, apply riesum,},
  apply tsum_le_tsum, apply smallclaim, simp_rw g at ind_lem2, rw ← ind_lem2, simp_rw g at hgsumm, apply hgsumm,apply riesum',
end

lemma Eisenstein_series_is_summable  (k : ℕ) (z : ℍ) (h : 3 ≤ k) : summable (Eise k z) :=

begin
let f:=(Eise k z),
have sum_Eq:  summable (λ x, abs (f x)) → summable f, by {apply summable_if_complex_abs_summable,},
apply sum_Eq,
simp_rw f,
have:=real_eise_is_summable k z h, rw real_Eise at this, exact this,
end


--example (x : ℂ) (a : ℤ × ℤ) (k: ℤ) (h : x ≠ 0)  : deriv (λ x,(x:ℂ)^-k) x = -k*(x: ℂ)^(-k-1) :=
--by {have:=deriv_fpow h, convert this, norm_cast,   }

def eisen_square (k : ℤ) (n: ℕ): ℍ → ℂ:=
λ z, ∑ x in Square n, Eise k z x

lemma Eisenstein_series_is_sum_eisen_squares (k: ℕ) (z: ℍ) (h : 3 ≤ k) :
(Eisenstein_series_of_weight_ k z) = ∑' (n : ℕ), eisen_square k n z:=
begin
rw Eisenstein_series_of_weight_, simp_rw eisen_square,

have HI:=Squares_cover_all,
let g:= λ (y : ℤ × ℤ),  (Eise k z ) y,
have hgsumm: summable g, by {simp_rw g, apply Eisenstein_series_is_summable k z h, },
have index_lem:= tsum_lemma' g Square HI hgsumm, simp_rw g at index_lem, exact index_lem,

end

def Eisen_partial_sums (k: ℤ) (n : ℕ): ℍ → ℂ:=
λ z, ∑ x in (finset.range n), (eisen_square k x z)

def upper_half_space_slice (A B : ℝ) :=
  {z: ℍ | complex.abs(z.1.1) ≤ A ∧ complex.abs(z.1.2) ≥ B  }

instance upper_half_space_slice_to_uhs (A B : ℝ) : has_coe (upper_half_space_slice A B) ℍ := ⟨λ z, z.1⟩

@[simp]lemma slice_mem (A B : ℝ) (z: ℍ): z ∈ (upper_half_space_slice A B) ↔
(complex.abs(z.1.1) ≤ A ∧ complex.abs(z.1.2) ≥ B) :=iff.rfl

def lbpoint (A B : ℝ) (h: 0 < B): ℍ:= ⟨⟨A,B⟩, by { simp, exact h,},⟩

lemma aux55 (a b : ℝ ) (h : a ≠ 0 ) : a/(a+b)=1/(b/a+1) :=
begin
have : b/a+1=(b+a)/a, by {ring_nf, simp [h],},
rw this,
simp,
rw add_comm,
end

lemma aux4 (a b : ℝ) (h: 0 < b): (b^4+(a*b)^2)/(a^2+b^2)^2=1/((a/b)^2 +1 ):=
begin
have h1 : (a^2+b^2)^2=(a^2+b^2)*(a^2+b^2), by {ring,},
rw h1,
have h2: (b^4+(a*b)^2)=b^2*(a^2+b^2) , by {ring},
rw h2,
rw mul_div_assoc,
simp,
field_simp,
have hb : b^2 ≠ 0 , by {simp [h], intro h3, linarith,},
have:= (aux55  (b^2) (a^2) hb),
rw add_comm,
exact this,
end

lemma aux5 (a b : ℝ): 0 < a^2/b^2+1:=
begin
have h1: 0 ≤a^2/b^2, by  {apply div_nonneg, nlinarith, nlinarith, },
linarith,
end

lemma aux6 (a b : ℝ) (h: 0 ≤  a) (h2: 0 ≤ b) : a ≤ b → a^2 ≤ b^2 :=
begin
intro hab,
nlinarith,
end

lemma rfunct_lower_bound_on_slice (A B : ℝ) (h: 0 < B) (z : upper_half_space_slice A B) :
rfunct (lbpoint A B h) ≤   rfunct(z.1) :=
begin
simp at *, simp_rw rfunct, simp_rw lbpoint, simp only [ min_le_iff, le_min_iff,subtype.val_eq_coe],
tidy, simp_rw lb, rw real.sqrt_le_sqrt_iff,
have h1: B^2 ≤ complex.abs (z_val_val.im)^2, by {norm_cast, nlinarith, },
norm_cast at h1, rw sq_abs at h1, simp [h1],
nlinarith,

simp_rw lb, rw real.sqrt_le_sqrt_iff,rw real.sqrt_le_sqrt_iff,rw aux4,  rw aux4, simp, rw inv_le_inv, simp,
have i1: (((z_val_val.im)^2)⁻¹ : ℝ)≤ ((B^2)⁻¹ : ℝ) ,
  by {rw inv_le_inv,
  have h' : 0 ≤ B , by {linarith,},
  have z_prop' : 0 ≤ z_val_val.im, by {linarith,},
  apply aux6 _ _ h' z_prop',
      have : z_val_val.im = complex.abs (z_val_val.im),
          by  {norm_cast, have:= abs_of_pos z_val_property, exact this.symm,},
      norm_cast at this,
      rw this,
      exact z_property_right,
      apply pow_two_pos_of_ne_zero,
      linarith,
      apply pow_two_pos_of_ne_zero, linarith,},
have i2: ((z_val_val.re)^2 : ℝ )≤ (A^2 : ℝ),
  by {have : (complex.abs (z_val_val.re))^2 = z_val_val.re^2,
      by {norm_cast, rw ← abs_pow, have he: even (2: ℤ), by {simp,},
          exact abs_fpow_even z_val_val.re he,},
  norm_cast at this,
  rw ← this,
  have v2: 0 ≤ complex.abs (z_val_val.re), by {apply complex.abs_nonneg,},
  norm_cast at v2,
  have v1: 0 ≤ A, by {apply le_trans v2 z_property_left,},
  apply aux6 _ _ v2 v1,
  exact z_property_left,
  },
ring_nf, simp at *,
have i3:= mul_le_mul i1 i2,
have i4: 0 ≤ (z_val_val.re)^2, by {nlinarith,},
have i5: 0 ≤ (B ^ 2)⁻¹ , by { simp, nlinarith,},
have i6:= i3 i4 i5,
simp_rw i6, simp,  apply aux5, apply aux5, exact h, exact z_val_property,

 apply div_nonneg, apply right.add_nonneg,
apply pow_even_nonneg, simp, nlinarith,  nlinarith, apply div_nonneg, apply right.add_nonneg,
apply pow_even_nonneg, simp, nlinarith,  nlinarith,
end


lemma rfunctbound (k : ℕ) (h : 3 ≤ k) (A B : ℝ) (hb : 0 < B) (z : upper_half_space_slice A B) :
(8/(rfunct z)^k)*Riemann_zeta (k-1)  ≤ (8/(rfunct (lbpoint A B hb) )^k)*Riemann_zeta (k-1) :=
begin
have h1:= rfunct_lower_bound_on_slice A B hb z,
    simp at h1,
    have v1: 0 ≤ rfunct z, by {have:= rfunct_pos z, linarith, },
    have v2: 0 ≤ rfunct (lbpoint A B hb), by {have:= rfunct_pos (lbpoint A B hb), linarith, },
    have h2:= le_of_pow'  (rfunct (lbpoint A B hb) ) (rfunct z) k v2 v1 h1,
    ring_nf,
    rw ← inv_le_inv at h2,
    have h3: 0 ≤  Riemann_zeta (k-1), by {have hk: 1 < (k-1 : ℤ), by { linarith,},
             have hkk: 1 < ((k-1 : ℤ) : ℝ), by {norm_cast, exact hk,},
             simp at hkk,
             have:= Riemann_zeta_pos (k-1) hkk, linarith,},
    nlinarith,
    apply pow_pos,
    apply rfunct_pos,
     apply pow_pos,
    apply rfunct_pos,
end


lemma rfunctbound' (k : ℕ) (h : 3 ≤ k) (A B : ℝ) (hb : 0 < B) (z : upper_half_space_slice A B) (n : ℕ) :
(8/(rfunct z)^k)* (rie (k-1) n)  ≤ (8/(rfunct (lbpoint A B hb) )^k)* (rie  (k-1) n) :=
begin
have h1:= rfunct_lower_bound_on_slice A B hb z,
    simp at h1,
    have v1: 0 ≤ rfunct z, by {have:= rfunct_pos z, linarith, },
    have v2: 0 ≤ rfunct (lbpoint A B hb), by {have:= rfunct_pos (lbpoint A B hb), linarith, },
    have h2:= le_of_pow'  (rfunct (lbpoint A B hb) ) (rfunct z) k v2 v1 h1,
    ring_nf,
    rw ← inv_le_inv at h2,
    have h3: 0 ≤  rie (k-1) n, by {
             rw rie,
             simp,
             apply real.rpow_nonneg_of_nonneg,
             simp,
             },
    nlinarith,
    apply pow_pos,
    apply rfunct_pos,
     apply pow_pos,
    apply rfunct_pos,
end



lemma Real_Eisenstein_bound_unifomly_on_stip (k : ℕ) (h : 3 ≤ k) (A B : ℝ) (hb : 0 < B)
  (z : upper_half_space_slice A B) :
    (real_Eisenstein_series_of_weight_ k z.1) ≤ (8/(rfunct (lbpoint A B hb) )^k)*Riemann_zeta (k-1):=
begin
have : (8/(rfunct z)^k)*Riemann_zeta (k-1)  ≤ (8/(rfunct (lbpoint A B hb) )^k)*Riemann_zeta (k-1),
by {apply rfunctbound, exact h},
apply le_trans (Real_Eisenstein_bound k z h) this,
end

def Eisen_square_slice (k : ℤ)  (A B : ℝ) (hb : 0 < B) (n : ℕ) : (upper_half_space_slice A B) → ℂ :=
λ x, (eisen_square k n x)

def Eisen_par_sum_slice (k : ℤ)  (A B : ℝ) (hb : 0 < B) (n : ℕ) : (upper_half_space_slice A B) → ℂ :=
λ z, ∑ x in (finset.range n), (Eisen_square_slice k A B hb x z)

instance : has_coe ℍ ℍ' :=
⟨ λ z, ⟨ z.1, by {simp, cases z, assumption,}, ⟩ ⟩

instance slice_coe (A B : ℝ) (hb : 0 < B) : has_coe (upper_half_space_slice A B) ℍ' :=
⟨λ (x : (upper_half_space_slice A B)), (x : ℍ')  ⟩

def Eisenstein_series_restrict (k : ℤ)  (A B : ℝ) (hb : 0 < B) : (upper_half_space_slice A B) → ℂ :=
λ x, Eisenstein_series_of_weight_ k x

def canelt (A B : ℝ) (hb : 0 < B) : ℂ :=
 ⟨ A, B ⟩




instance  nonemp (A B : ℝ) (ha : 0 ≤  A) (hb : 0 < B) : nonempty (upper_half_space_slice A B):=
begin
let z:= (⟨  A, B⟩ : ℂ),
rw ← exists_true_iff_nonempty,
simp,
use z,
have zim: z.im = B, by {refl,},
use hb,
simp_rw z,
simp_rw [upper_half_plane.re, upper_half_plane.im],
simp,
split,
have:= abs_eq_self.2 ha,
rw this,
apply le_abs_self,
end

lemma Eisenstein_series_is_sum_eisen_squares_slice (k: ℕ) (h : 3 ≤ k) (A B : ℝ) (hb : 0 < B)
 (z: (upper_half_space_slice A B)) :
(Eisenstein_series_restrict k A B hb z) = ∑' (n : ℕ), (Eisen_square_slice k A B hb n z):=
begin
rw Eisenstein_series_restrict, simp_rw Eisen_square_slice,

have HI:=Squares_cover_all,
let g:= λ (y : ℤ × ℤ),  (Eise k z ) y,
have hgsumm: summable g, by {simp_rw g, apply Eisenstein_series_is_summable k z h, },
have index_lem:= tsum_lemma' g Square HI hgsumm, simp_rw g at index_lem, exact index_lem,
end


lemma complex_abs_sum_le {ι : Type*} (s : finset ι) (f : ι → ℂ) :
complex.abs(∑ i in s, f i) ≤ ∑ i in s, complex.abs(f i) :=
begin
 exact abv_sum_le_sum_abv (λ (k : ι), f k) s,
end

lemma Eisen_partial_tends_to_uniformly (k: ℕ) (h : 3 ≤ k) (A B : ℝ) (ha : 0 ≤ A) (hb : 0 < B) :
tendsto_uniformly (Eisen_par_sum_slice k A B hb) (Eisenstein_series_restrict k A B hb) filter.at_top:=
begin
let M : ℕ → ℝ := λ x,   (8/(rfunct (lbpoint A B hb) )^k)* (rie  (k-1) x),

have:= M_test_uniform _ (Eisen_square_slice k A B hb) M,
simp_rw  ← (Eisenstein_series_is_sum_eisen_squares_slice k h A B hb _) at this,
apply this,
simp_rw Eisen_square_slice,
simp_rw eisen_square,
simp_rw M,


simp_rw Eise,
intros n a,
have SC:= SmallClaim k a h n,
rw real_Eise at SC,
simp at SC,
simp,
have ineq1:
    complex.abs (∑ (x : ℤ × ℤ) in Square n, ((↑(x.fst) * ↑↑a + ↑(x.snd)) ^ k)⁻¹) ≤
    ∑ (x : ℤ × ℤ) in Square n, (complex.abs ((↑(x.fst) * ↑↑a + ↑(x.snd)) ^ k))⁻¹,
    by {simp,
    have:= complex_abs_sum_le  (Square n) (λ  (x : ℤ × ℤ),  (((x.1 : ℂ) * (a : ℂ) + (x.2 : ℂ)) ^ k)⁻¹),
      simp at this, exact this, },
have SC2:= le_trans ineq1 SC,
have rb := rfunctbound' k h A B hb a n,
apply le_trans SC2 rb,

simp_rw M,
have hk: 1 < ((k-1): ℤ), by { linarith, },
have nze: ((8/((rfunct (lbpoint A B hb))^k)): ℝ)  ≠ 0, by {apply div_ne_zero, simp, apply pow_ne_zero,
 simp, by_contra HR, have:=rfunct_pos (lbpoint A B hb), rw HR at this, simp at this, exact this, },
have riesum:=int_Riemann_zeta_is_summmable (k-1) hk,
  rw (summable_mul_left_iff nze).symm, simp at riesum, apply riesum,
apply Eisenstein_series.nonemp A B ha hb,
end


def powfun  (k : ℤ) : ℂ → ℂ :=
λ x, x^k

def trans (a b : ℤ) : ℂ → ℂ :=
λ x, a*x+b

def ein (a b k : ℤ): ℂ → ℂ :=
λ x, (a*x+b)^k

lemma com (a b k : ℤ): (ein a b k) = (powfun k) ∘ trans a b :=
begin
refl,
end


lemma d1 (k: ℤ) (x : ℂ): deriv (λ x, x^k) x = k*x^(k-1) :=
by {simp only [deriv_fpow'], }

lemma d2 (a b k: ℤ) (x : ℂ) (h : (a: ℂ)*x+b ≠ 0) : deriv (ein a b k) x = k*a*(a*x+b)^(k-1):=
begin
rw com,
rw deriv.comp,
rw powfun,
rw trans,
simp,
ring,
rw powfun,
rw trans, simp, simp_rw differentiable_at_fpow ,
simp [h],
rw trans,
simp only [differentiable_at_const, differentiable_at_add_const_iff, differentiable_at_id', differentiable_at.mul],
end

lemma neg_inv_pow (x : ℂ) (k : ℤ) : (x^k)⁻¹= x^-k :=
begin
exact (fpow_neg x k).symm,
end

lemma aux8 (a b k: ℤ ) (x : ℂ): (((a : ℂ)*x+b)^k)⁻¹ =  ((a : ℂ)*x+b)^-k:=
begin
apply neg_inv_pow,
end

lemma dd2 (a b k: ℤ) (x : ℂ) (h : (a: ℂ)*x+b ≠ 0) : has_deriv_at (ein a b k)  (k*(a*x+b)^(k-1)*(a) : ℂ) x:=
begin
rw com,

apply has_deriv_at.comp,
rw powfun,
rw trans,
simp,
apply has_deriv_at_fpow,
simp [h],
rw trans,
apply has_deriv_at.add_const,
have:= has_deriv_at.const_mul (a: ℂ) (has_deriv_at_id x) , simp at *,
exact this,
end

lemma H_member (z : ℂ)  : z ∈ upper_half_space ↔ 0 < z.im:=iff.rfl

lemma Eise'_has_deriv_within_at (k : ℤ) (y: ℤ × ℤ) (hkn: k ≠ 0) : is_holomorphic_on (λ (z : ℍ'), Eise k z y):=
begin


rw is_holomorphic_on, intro z,
by_cases hy: (y.1 : ℂ)*z.1 + y.2 ≠ 0,

simp_rw Eise, ring_nf,
have:= aux8 y.1 y.2 k z.1, simp only [subtype.val_eq_coe] at this,

have nz: (y.1 : ℂ)*z.1 + y.2 ≠ 0 , by {apply hy,},
have hdd:= dd2 y.1 y.2 (-k) z nz,
rw ein at hdd,
have H:= has_deriv_at.has_deriv_within_at' upper_half_space hdd, simp at H,
let fx:=(-k*((y.1:ℂ)*z.1+y.2)^(-k-1)*(y.1) : ℂ),
use fx,
rw has_deriv_within_at_iff_tendsto at *, simp at *, rw metric.tendsto_nhds_within_nhds at *,
intros ε hε,
have HH:= H ε hε,
use classical.some HH,
have:= classical.some_spec HH, simp at this,
have hg:= this.1,
simp [hg] at *,

intros x hx hd, dsimp at *, simp_rw extend_by_zero,
simp [ ext_by_zero_apply],
 rw ← dite_eq_ite, rw dif_pos hx,
have H3:= this_1 hx hd,
simp_rw fx,
convert H3,
ring,

simp at hy,
have hz: y.1 =0 ∧ y.2 = 0, by {by_contra, simp  at h, cases z, cases y, dsimp at *, injections_and_clear,
     dsimp at *, simp at *, cases h_2, rw h_2 at h_1, simp at *,
   have:= h h_2, rw h_1 at this, simp at this, exact this, simp [H_member] at z_property, rw h_2 at z_property,
   simp at z_property, exact z_property,},
simp_rw Eise, rw [hz.1, hz.2], simp,
have zhol:= zero_hol ℍ' ,
rw is_holomorphic_on at zhol,
have zhol':= zhol z,
simp at zhol',
have zk: ((0: ℂ)^k)⁻¹ =0, by {simp, apply zero_fpow, apply hkn,},
rw zk,
exact zhol',


end


lemma Eisenstein_is_holomorphic (k : ℤ): is_holomorphic_on (Eisenstein_series_of_weight_ k):=
begin
rw is_holomorphic_on, simp, intros z hz, use (Eisenstein_deriv_weight k ⟨z, hz⟩),
rw has_deriv_within_at_iff_tendsto, simp, rw tendsto_zero_iff_norm_tendsto_zero,
simp,rw metric.tendsto_nhds_within_nhds,
intros ε hε, use ε, simp [hε],intros x hx hd, dsimp at *, rw extend_by_zero, simp [ ext_by_zero_apply], rw dif_pos hx,  rw dif_pos hz,
sorry,
end




end Eisenstein_series
