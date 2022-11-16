/-
Copyright (c) 2022 André Hernández-Espiet, Alex Kontorovich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: André Hernández-Espiet, Alex Kontorovich
-/

import data.complex.basic
import analysis.special_functions.trigonometric.basic

open_locale big_operators classical real

noncomputable theory

open real finset

def e (x : ℝ) : ℂ := complex.exp (x * (2 * π * complex.I))

lemma e_add {x y : ℝ} : e (x + y) = e x * e y :=
by { rw [e, complex.of_real_add, add_mul, complex.exp_add], refl }

lemma e_add_add (x y z: ℝ) : e (x + y + z) = e x * e y * e z:=
by
  rw [e_add, e_add]

lemma e_int (z : ℤ) : e z = 1 :=
by rw [e, complex.of_real_int_cast, complex.exp_int_mul_two_pi_mul_I]

@[simp] lemma e_nat (n : ℕ) : e n = 1 :=
by rw [←e_int n, int.cast_coe_nat]

@[simp] lemma e_zero : e 0 = 1 :=
by rw [←e_nat 0, nat.cast_zero]

theorem div_by_rem (a b : ℤ) (hb : 0 < b) : ∃ (q r : ℤ), (a = b*q + r)∧(0 ≤ r)∧(r<b) :=
⟨a / b, a % b, ⟨(a.div_add_mod b).symm, a.mod_nonneg hb.ne', a.mod_lt_of_pos hb⟩⟩

--move to data.int.gcd
lemma dvd_iff_dvd_of_gcd_one_right {a b c : ℤ} (hab : a.gcd c = 1) :
a ∣ b ↔ a ∣ b * c :=
 ⟨λ h, dvd_mul_of_dvd_left h c, λ h, int.dvd_of_dvd_mul_left_of_gcd_one h hab⟩

lemma dvd_iff_dvd_of_gcd_one_left {a b c : ℤ} (hab : a.gcd b = 1) :
a ∣ c ↔ a ∣ b * c :=
 ⟨λ h, dvd_mul_of_dvd_right h b, λ h, int.dvd_of_dvd_mul_right_of_gcd_one h hab⟩

lemma dumb (q z1 z2: ℂ)  (qh: z1 = z2) : q*z1=q*z2:=congr_arg (has_mul.mul q) qh

lemma dumb2 {a b c: ℤ} (a0:a≠  0)(h: a*b=a*c) : b=c := (mul_right_inj' a0).mp h

lemma dumb3 {a b c :ℤ } (h: a=b) : c*a=c*b := congr_arg (has_mul.mul c) h

lemma dumb4 {a b c: ℤ } (h: a≠ 0) : c*(a*b)/a = c*b:=
begin
  rw ← mul_assoc, rw mul_comm c a,rw mul_assoc,field_simp,
end

lemma dumb5 (P: Prop) (a b : ℤ ) : ite (P∧ a∣b) (1:ℂ ) 0 = ite P 1 0 * ite (a∣ b) 1 0:=
begin
  sorry,
  /-
  rw ite_eq_iff,
  by_cases pt: P=true,
  by_cases qt: a∣b,
  {
    left,rw pt,
    refine ⟨⟨by tauto,by tauto ⟩,_ ⟩,
    finish,
  },
  {
    right,
    finish,
  },
  right,
  finish, -/
end

lemma dumb6 (a b c: ℤ ) (ha: a=b*c) (a0:a>0) (b0:b>0): c>0:=
begin
  sorry,--finish,
end

theorem dumb7 (a q b r:ℤ ) (b0: b≠ 0): ite (∃ (x': Ioc 0 q), a= b*x'-r) (1:ℂ ) (0:ℂ ) =
  ∑ (x':ℤ ) in  Ioc 0 q, ite (a= b*x'-r) (1:ℂ ) (0:ℂ ):=
  begin
   sorry,
   /-    rw ite_eq_iff,
    by_cases hyp: ∃ (x' : (Ioc 0 q)), a =  b*x'-r,
    {
      left,split, exact hyp,
      rcases hyp with ⟨  ⟨ x,hhx⟩,hx⟩,
      symmetry,
      have dis: disjoint (((Ioc 0 q)) \ {x}) {x},
      {
        finish,
      },
      have un: ((Ioc 0 q))  =((Ioc 0 q) \ {x})∪  {x} ,
      {
        ext c,
        split,
        intro hyp,
        finish,
        intro hyp,
        rw finset.mem_union at hyp,
        cases hyp,
        finish,
        simp at hyp,rw hyp,
        exact hhx,
      },
      rw un,
      have :=finset.sum_union dis,
      rw this,clear this,
      have lol: a= b* x-r:= hx,
      simp_rw lol,
      have : ∀ (x_1: ℤ ), (b * x - r = b * x_1 - r ↔  x=x_1),
      {
        intro x_1,split,
        intro hyp, have : b*x=b*x_1 := by linarith,
        have b00: (b:ℚ )≠ 0 := by norm_cast; exact b0,
        field_simp at this,cases this,exact this,exfalso, exact b0 this,
        intro hyp, rw hyp,
      },
      simp_rw this,
      rw finset.sum_ite_eq,
      rw finset.sum_ite_eq,
      finish,
    },
    right,split, exact hyp, push_neg at hyp,
    have : ∀ (x': (Ioc 0 q) ) , ite ( a= b*x' -r) 1 0 = 0,
    {
      intro x',
      rw ite_eq_iff,right,refine ⟨hyp x' ,by refl⟩,
    },
    rw finset.sum_ite_of_false,
    simp,
    intros x hhhx, intro hypp,norm_cast at hyp,
    have := hyp ⟨ x,hhhx⟩,exact this hypp, -/
  end

lemma dumb8 (z:ℕ ) (h1: 0≤ z) (h2: z≠ 0) : 0<z := (ne.symm h2).lt_of_le h1

lemma dumb9 (a b c d: ℤ ) : ite (c∣d∧ a∣b) (1:ℂ ) 0 = ite (c∣ d) 1 0 * ite (a∣ b) 1 0:=
begin
  sorry,
  /- rw ite_eq_iff,
  by_cases pt: c∣ d,
  by_cases qt: a∣b,
  {
    left,
    refine ⟨⟨by tauto,by tauto ⟩,_ ⟩,
    finish,
  },
  {
    right,
    finish,
  },
  right,
  finish, -/
end

lemma dumb10 (a : ℤ ) (ha: 0<a) : 1≤ a := (id_tag tactic.id_tag.simp (eq.refl (1 ≤ a))).mpr
(classical.by_contradiction (λ (ᾰ : ¬1 ≤ a), absurd ha ᾰ))

def f (x x_1 a b c d A B C D P: ℤ  ) : ℤ := A*a+B*b+C*c+D*d+(A*c+B*d)*P *x+(B*a+D*c)*P *x_1+B*c*P^2*x*x_1

def S_four_one (q r k l a b c d A B C D P: ℤ   ) : ℂ := (1: ℂ )/q^2
  *(( ∑ x in (finset.Ioc 0 q), ∑ x_1 in (finset.Ioc 0 q),e ((r* (f x x_1 a b c d A B C D P)+ k * x+ l*x_1) / q)) )

lemma orthogonality {m : ℕ} (n : ℕ) {r s : ℤ} (hm : m ≠ 0) {I : finset ℤ} (hI : I = finset.Ioc r s)
  (hrs₁ : r < s) (hrs₂ : I.card = m) :
  (∑ h in I, e (h * n / m)) * (1 / m) =
    if m ∣ n then 1 else 0 :=
begin
  sorry,
  /- have hm' : (m : ℝ) ≠ 0, exact_mod_cast hm,
  have hm'' : (m : ℂ) ≠ 0, exact_mod_cast hm',
  split_ifs,
  { simp_rw [mul_div_assoc, ←nat.cast_div h hm', ←int.cast_coe_nat, ←int.cast_mul, e_int],
    rw [sum_const, nat.smul_one_eq_coe, int.cast_coe_nat, one_div, hrs₂, mul_inv_cancel hm''] },
  rw [mul_eq_zero, one_div, inv_eq_zero, nat.cast_eq_zero],
  simp only [hm, or_false],
  set S := ∑ h in I, e (h * n / m),
  have : S * e (n / m) = ∑ h in (finset.Ioc (r + 1) (s + 1)), e (h * n / m),
  { simp only [←finset.image_add_right_Ioc, finset.sum_image, add_left_inj, imp_self,
      implies_true_iff, int.cast_add, add_mul, int.cast_one, one_mul, add_div, e_add,
      finset.sum_mul, hI] },
  rw [int.Ioc_succ_succ hrs₁.le, finset.sum_erase_eq_sub, finset.sum_insert, add_comm,
    add_sub_assoc, sub_eq_zero_of_eq, add_zero, ←hI] at this,
  { apply eq_zero_of_mul_eq_self_right _ this,
    rw [ne.def, e_eq_one_iff, not_exists],
    intros i hi,
    rw [div_eq_iff_mul_eq hm', ←int.cast_coe_nat, ←int.cast_coe_nat, ←int.cast_mul,
      int.cast_inj] at hi,
    rw [←int.coe_nat_dvd, ←hi] at h,
    simpa using h },
  { have : s = m + r,
    { rw [←hrs₂, hI, int.card_Ioc, int.to_nat_sub_of_le hrs₁.le, sub_add_cancel] },
    rw [this, add_assoc, int.cast_add, add_mul, add_div, e_add, int.cast_coe_nat,
      mul_div_cancel_left _ hm', e_nat, one_mul] },
  { simp },
  { simp [int.add_one_le_iff, hrs₁] },  -/
end

lemma orthogonalityZ {m : ℕ} (n : ℤ ) {r s : ℤ} (hm : m ≠ 0) {I : finset ℤ} (hI : I = finset.Ioc r s)
  (hrs₁ : r < s) (hrs₂ : I.card = m) :
  (∑ h in I, e (h * n / m)) =
    m* if (m:ℤ ) ∣ n then 1 else 0 :=
begin
 sorry,
 /-  rcases div_by_rem n m _ with ⟨q,rr,h1,h2,h3 ⟩,
  rw h1,
  have mR: (m:ℝ )≠ 0:= by norm_cast; exact hm,
  field_simp,
  have :∀ (x:ℝ ), x * (m * q + rr) / m = x*rr/m+x*q := λ x,by field_simp;ring,
  simp_rw this, clear this,
  simp_rw e_add,
  have : ∀ (x:ℤ ), e((x:ℝ )*(q:ℝ ))=e(↑ (x*q) ):=λ x,by norm_cast,simp_rw this,
  simp_rw e_int,simp_rw mul_one,
  have := orthogonality (rr.nat_abs) hm hI hrs₁ hrs₂,
  have mC: (m:ℂ )≠ 0 := by norm_cast; exact hm,
  have key:= mul_left_inj' mC, rw ← key at this,field_simp at this,
  have hyp2: ((rr.nat_abs):ℝ)  = (rr:ℝ),
    {

      cases int.nat_abs_eq rr,norm_cast,exact h.symm,
      by_cases rr =0, rw h, simp,
      have :0<(rr.nat_abs:ℤ ) := by norm_cast;exact int.nat_abs_pos_of_ne_zero h,linarith,
    },
  simp_rw hyp2 at this,

  have : ite (m ∣ rr.nat_abs) (m:ℂ ) (0:ℂ ) = ite ((m:ℤ )∣ m*q+rr) (m:ℂ ) 0,
  {
    have : m ∣ rr.nat_abs ↔ (m:ℤ )∣ m*q+rr,
    {
      split,
      {

        intro hyp,
        cases hyp with y hy,
        use (q+y), rw mul_add,field_simp, norm_cast at hyp2,
        rw← hyp2,norm_cast,exact hy,
      },
      intro hyp,
      by_cases rr0:rr=0,
      rw rr0,use 0, ring,
      cases hyp with y hy,
      use (y-q).nat_abs,
      suffices : (rr.nat_abs:ℤ ) = m * (y - q).nat_abs,
      {
        norm_cast at this, exact this,
      },
      norm_cast at hyp2,
      rw hyp2,
      have : ((y - q).nat_abs :ℤ )= y-q,
      {
        cases int.nat_abs_eq (y-q),
        exact h.symm,
        have : rr = m*(y-q),
        {
          linarith,
        },
        have : 0<(((y - q).nat_abs):ℤ ), {

         norm_cast,
        apply int.nat_abs_pos_of_ne_zero,
        intro lol,
        rw lol at this,rw mul_zero at this, exact rr0 this,
        },
        have : y-q < 0 := by linarith,
        have : 0<(m:ℤ ),
        {
          have : 0≤  m:=by simp,
          have : 0 < m,
          exact dumb8 m this (by assumption),norm_cast, exact this,
        },
        exfalso,
        have : (m:ℝ  ) * (y - q) < 0,
        {
          have : 0<(m:ℝ ),norm_cast, norm_cast at this, assumption,
          have : (y-q : ℝ ) < 0, norm_cast at *,assumption,
          have := mul_lt_mul_of_neg_right  (by assumption: 0<(m:ℝ )) this, rw zero_mul at this,
          exact this,
        },
        norm_cast at this,
        linarith,
      },
      rw this,
      linarith,
    },
    simp_rw this,
  },

  simp_rw ← this,assumption,
  have : 0≤  m:=by simp,
          have : 0 < m,
          exact dumb8 m this (by assumption),norm_cast, exact this, -/
end

lemma orthogonality2 {l m : ℕ} (n : ℕ) {r s : ℤ} (hm : m ≠ 0)(iscoprime: l.coprime m) {I : finset ℤ} (hI : I = finset.Ioc r s)
  (hrs₁ : r < s) (hrs₂ : I.card = m) :
  (∑ h in I, e (h * n * l / m)) * (1 / m) =
    if m ∣ n then 1 else 0 :=
begin
sorry,
 /-  have := orthogonality (l*n) hm hI hrs₁ hrs₂,
  convert this using 1,
  {
    congr' 1,
    apply finset.sum_congr rfl,
    intros x hx,
    congr' 1,
    have : (m : ℝ) ≠ 0 := by simp [hm],
    field_simp,
    ring,
  },
  have : m ∣ n ↔ m ∣ l * n ,
  {
    have := nat.is_coprime_iff_coprime.mpr iscoprime.symm,

    have := int.gcd_eq_one_iff_coprime.mpr this,

    exact_mod_cast @dvd_iff_dvd_of_gcd_one_left _ _ (n : ℤ) this,

  },
  simp [this], -/
end

lemma orthoy (q r l a c B D P rbar q₁: ℕ  ) (q0:q≠ 0) (coprime_q_r : q.coprime r)(rbar_is: (q:ℤ )*q₁ ∣(r*rbar-1) )
{I : finset ℤ} (hI : I = finset.Ioc  0 q): ∀ (x : ℕ   ), 1/(q:ℂ )* ∑ (y : ℤ) in Ioc 0 (q:ℤ ),
 e ((r * ((B * a + D * c) * P * y + B * c * P ^ 2 * x * y) + l * y) / q)
 =ite ((q:ℤ )∣ B*c*P^2*x+l*rbar+(B*a+D*c)*P) 1 0 :=
begin
  sorry,
  /- intro x,
  have qg: (q:ℤ )>0,
  {
    norm_cast, exact zero_lt_iff.mpr q0,
  },
  have : (q:ℝ )≠ 0,
  {
    norm_cast, exact q0,
  },
  have := orthogonality2 (B * c * P ^ 2 * x + l * rbar + (B * a + D * c) * P) q0 coprime_q_r.symm hI qg (by rw hI;by simp),
  rw mul_comm at this,
  symmetry, have := this.symm,
  have lol: ite (q ∣ B * c * P ^ 2 * x + l * rbar + (B * a + D * c) * P) (1:ℂ ) 0 =
  ite ((q:ℤ ) ∣ B * c * P ^ 2 * x + l * rbar + (B * a + D * c) * P) (1:ℂ ) 0,
  {
    norm_cast,
  },
  rw lol at this,
  convert this using 1,
  congr' 1,rw hI,

  apply finset.sum_congr rfl, -- apply mod_congr congr implies exp is equal
  intros y hy,
  cases rbar_is with z hz,
  have : e (y * (B * c * P ^ 2 * x + l * rbar + (B * a + D * c) * P) * r / q) =
      e (y * (B * c * P ^ 2 * x*r + l * (rbar *r) + r*(B * a + D * c) * P)  / q),
      {
        congr' 1, ring,
      },
  symmetry, convert this using 1, congr' 1, field_simp,
  have hhz: (rbar:ℤ )*r = q*q₁*z +1 ,
  {
    	rw ← hz,ring,
  },
  have hhhz: (rbar:ℝ )*r = q*q₁*z +1 ,
  {
    norm_cast at hhz,norm_cast,exact hhz,
  },
  rw hhhz,
  have : e (y * (B * c * P ^ 2 * x * r + l * (q * q₁ * z + 1) + r * (B * a + D * c) * P) / q)
  = e (y * (B * c * P ^ 2 * x * r + l + r * (B * a + D * c) * P) / q+ y*l* q₁ * z),
  {
    congr' 1,
    field_simp,ring,


  },
  rw this,
     rw e_add,
    have : e(y*l* q₁ * z)=1,
    {
      norm_cast,
      exact e_int (y*l* q₁ * z),
    },
    rw this,
    rw mul_one,
    congr' 1,
    field_simp,ring, -/
end

lemma orthoymod (q r l a c B D P rbar q₁: ℕ  ) (q0:q≠ 0) (coprime_q_r : q.coprime r)(rbar_is: (q:ℤ )*q₁ ∣(r*rbar-1) )
{I : finset ℤ} (hI : I = finset.Ioc  0 q) (x: ℤ ) (xh: x≥ 0):  ∑ (y : ℤ) in Ioc 0 (q:ℤ ),
 e ((r * ((B * a + D * c) * P * y + B * c * P ^ 2 * x * y) + l * y) / q)
 =q*ite ((q:ℤ )∣ B*c*P^2*x+l*rbar+(B*a+D*c)*P) 1 0 :=
begin
  sorry,
    /-  have qg: (q:ℤ )>0,
      {
        norm_cast, exact zero_lt_iff.mpr q0,
      },
      have : (q:ℝ )≠ 0,
      {
        norm_cast, exact q0,
      },
      have : (q: ℂ)≠ 0, norm_cast,exact q0,

    have :=orthoy q r l a c B D P rbar q₁ q0 coprime_q_r rbar_is hI x.nat_abs,
    have dum: (x.nat_abs :ℤ ) = x,
    {
      cases int.nat_abs_eq x,
      exact h.symm,
      linarith,
    },
    rw ← dum,
    rw← this,
    field_simp,
    rw mul_comm, -/
end

lemma four_two (q r k l a b c d A B C D P E Ebar rbar q₁ q₂: ℕ  ) (coprime_q_r : q.coprime r) (qN: q≠ 0)
  (q₁_is: q₁ = gcd (B*c*P^2) q) (q_is: (q:ℤ )=q₁*q₂) (E_is: (B:ℤ )*c*P^2 = q₁* E) (Ebar_is: (q₂:ℤ ) ∣(E*Ebar-1) )
  (rbar_is:(q:ℤ )*q₁ ∣(r*rbar-1)) {I : finset ℤ} (hI : I = finset.Ioc  0 q)
  :S_four_one q r k l a b c d A B C D P = (q₁ / q) * e (r *(A*a + B*b + C*c + D*d)/q)
  *(ite ((q₁:ℤ ) ∣ r * P * (A * c + B * d) + k ∧
  (q₁:ℤ ) ∣ l * rbar + (B * a + D * c) * P) 1 0) * e ((-Ebar*(P*(B*a+D*c)+rbar*l)*(P*r*(A*c+B*d)+k))/(q*q₁)):=
begin
  have qZ: (q:ℤ  ) ≠ 0 := sorry,--by norm_cast; exact qN,
  have q10: (q₁: ℤ   ) ≠ 0,
  {
    sorry,
   -- intro zer,
    --rw zer at q_is,simp at q_is,norm_cast at qZ,
  },
   have q20: (q₂: ℤ   ) ≠ 0,
  {
    sorry,
   -- intro zer,
    --rw zer at q_is,simp at q_is,norm_cast at qZ,
  },

  have q0: (q:ℝ ) ≠ 0,
  {
    sorry,--norm_cast,exact qN,
  },
    have qC: (q:ℂ  ) ≠ 0 := sorry,--by norm_cast; exact qN,
     have ge0Z : 0<(q₁:ℤ ),
  {
    sorry,
    /- have : 0≤ (q₁:ℤ ) ,
    {
      norm_cast,
      exact nat.zero_le q₁,
    },
    by_contra,
    push_neg at h,
    have : (q₁:ℤ ) = 0,
    linarith,
    exact q10 this, -/
  },

   have : (q₁:ℝ )≠ 0,
  {
    sorry,
   /-  norm_cast,
    intro q10,
    rw q10 at q_is,simp at q_is,exact qN q_is, -/

  },
          have : (q₂:ℝ )≠ 0,
          {
            sorry,
            /- norm_cast,
                intro q10,
                rw q10 at q_is,simp at q_is,exact qN q_is, -/
          },

      have q1N: q₁≠ 0 := sorry,--by norm_cast at q10;exact q10,
      have q_isR: (q:ℝ ) = q₁ * q₂,
      {
          sorry,--norm_cast,norm_cast at q_is,exact q_is,
      },

      have q₂0:  0<(q₂:ℤ ),
  {
    sorry,
   /-  have : 0≤ (q₂:ℤ ) ,
    {
      norm_cast,
      exact nat.zero_le q₂,
    },
    by_contra,
    push_neg at h,
    have lol: (q₂:ℤ ) = 0,
    linarith,
    exact q20 lol, -/
  },

  unfold S_four_one,
  unfold f at *,
  have key : ∀ (x x_1 : ℤ      ), ((r:ℚ )*(A*a+B*b+C*c+D*d+(A*c+B*d)*P *x+(B*a+D*c)*P *x_1+B*c*P^2*x*x_1) + k*x +l*x_1)/q=
    (r*(A*a+B*b+C*c+D*d)/q + (r*((A*c+B*d)*P *x)+k*x)/q + (r*((B*a+D*c)*P*x_1+B*c*P^2*x*x_1)+l*x_1)/q),
    {
      sorry,
    /-   intros x y,field_simp,
      have lol : ∀ (x y  : ℤ       ) ,
      ((r:ℤ ) *(A * a + B * b + C * c + D * d + (A * c + B * d) * P * x +(B * a + D * c) * P * y
         +B * c * P ^ 2 * x * y) +
       k * x +
     l * y)  = (r * (A * a + B * b + C * c + D * d) +
       (r * ((A * c + B * d) * P * x) + k * x) +
     (r * ((B * a + D * c) * P * y + B * c * P ^ 2 * x * y) + l * y)),

    {
      intros x1 y1,
      ring,
    },
    norm_cast,
    norm_cast at lol,
    rw lol x y, -/
    },
    have :(1/(q:ℂ )^2)*( ∑ x in (finset.Ioc 0 (q:ℤ )), ∑ x_1 in (finset.Ioc 0 (q:ℤ )),
    e (
    ((r:ℚ )*(A*a+B*b+C*c+D*d+(A*c+B*d)*P *x+(B*a+D*c)*P *x_1+B*c*P^2*x*x_1) + k*x +l*x_1)/q))=
    (1/q^2)*( ∑ x in (finset.Ioc 0 (q:ℤ )), ∑ x_1 in (finset.Ioc 0 (q:ℤ )),
    e ( (r*(A*a+B*b+C*c+D*d)/q + (r*((A*c+B*d)*P *x)+k*x)/q + (r*((B*a+D*c)*P*x_1+B*c*P^2*x*x_1)+l*x_1)/q))),
   {
    sorry,
   /-  congr' 1,
    congr' 1,
    ext1 x,
    congr' 1,

      ext1 x_1,
  congr' 1,
  field_simp,
  ring, -/
    --extract_goal,
   },

     convert this using 1,
   {  sorry,
     /-  congr' 1,
      apply finset.sum_congr rfl,
      intros x hx,
      apply finset.sum_congr rfl,
      intros y hy,
      congr' 1,
      field_simp, -/
       },

  have : 1 / (q:ℂ ) ^ 2 * ∑ (x : ℤ ) in Ioc 0 (q:ℤ ), ∑ (y : ℤ ) in Ioc 0 (q:ℤ ), e((r * (A * a + B * b + C * c + D * d) / q) +
    ((r * ((A * c + B * d) * P * x) + k * x) / q) +
    ((r * ((B * a + D * c) * P * y + B * c * P ^ 2 * x * y) + l * y) / q))
    =  1 / (q:ℂ ) ^ 2 * ∑ (x : ℤ ) in Ioc 0 (q:ℤ ), ∑ (y : ℤ ) in Ioc 0 (q:ℤ ), e(r * (A * a + B * b + C * c + D * d) / q) *
    e((r * ((A * c + B * d) * P * x) + k * x) / q) *
    e((r * ((B * a + D * c) * P * y + B * c * P ^ 2 * x * y) + l * y) / q),
    {
      sorry,
      /- congr' 1,
      apply finset.sum_congr rfl,
      intros x hx,
      apply finset.sum_congr rfl,
      intros y hy,

      have := e_add_add (r * (A * a + B * b + C * c + D * d) / q)
      ((r * ((A * c + B * d) * P * x) + k * x) / q)
      ((r * ((B * a + D * c) * P * y + B * c * P ^ 2 * x * y) + l * y) / q),
      rw this, -/

    },
      rw this,
      clear this this key,
      have : ∑ (x: ℤ  ) in Ioc 0 (q:ℤ ), ∑ (y : ℤ ) in Ioc 0 (q:ℤ ), e (r * (A * a + B * b + C * c + D * d) / q) *
       e ((r * ((A * c + B * d) * P * x) + k * x) / q) *
       e ((r * ((B * a + D * c) * P * y + B * c * P ^ 2 * x * y) + l * y) / q)=
         ∑ (x: ℤ  ) in Ioc 0 (q:ℤ ),(e (r * (A * a + B * b + C * c + D * d) / q)) *∑ (y : ℤ ) in Ioc 0 (q:ℤ ),
       e ((r * ((A * c + B * d) * P * x) + k * x) / q) *
       e ((r * ((B * a + D * c) * P * y + B * c * P ^ 2 * x * y) + l * y) / q),

   {
    sorry,
    /- apply finset.sum_congr rfl,
    intros x hx,
    rw finset.mul_sum,
    apply finset.sum_congr rfl, intros y hy,ring, -/
   },

   rw this,
      have : e (r * (A * a + B * b + C * c + D * d) / q) *∑ (x: ℤ  ) in Ioc 0 (q:ℤ ), ∑ (y : ℤ ) in Ioc 0 (q:ℤ ),
       e ((r * ((A * c + B * d) * P * x) + k * x) / q) *
       e ((r * ((B * a + D * c) * P * y + B * c * P ^ 2 * x * y) + l * y) / q)=
         ∑ (x: ℤ  ) in Ioc 0 (q:ℤ ),(e (r * (A * a + B * b + C * c + D * d) / q)) *∑ (y : ℤ ) in Ioc 0 (q:ℤ ),
       e ((r * ((A * c + B * d) * P * x) + k * x) / q) *
       e ((r * ((B * a + D * c) * P * y + B * c * P ^ 2 * x * y) + l * y) / q),
    {
      sorry,--rw finset.mul_sum,
    },
    rw ← this,clear this this,
        have : ∑ (x: ℤ  ) in Ioc 0 (q:ℤ ), e ((r * ((A * c + B * d) * P * x) + k * x) / q) *
        ∑ (y : ℤ ) in Ioc 0 (q:ℤ ),  e ((r * ((B * a + D * c) * P * y + B * c * P ^ 2 * x * y) + l * y) / q)=
        ∑ (x: ℤ  ) in Ioc 0 (q:ℤ ),∑ (y : ℤ ) in Ioc 0 (q:ℤ ),
       e ((r * ((A * c + B * d) * P * x) + k * x) / q) *
       e ((r * ((B * a + D * c) * P * y + B * c * P ^ 2 * x * y) + l * y) / q),
    {
      sorry,
      /- apply finset.sum_congr rfl,
      intros x hx,
      rw finset.mul_sum, -/
    },

    rw ← this,clear this,
    symmetry,
    have key:= orthoymod q r l a c B D P rbar q₁ _ coprime_q_r rbar_is hI,
    have :
    ∑ (x : ℤ ) in Ioc 0 (q:ℤ ), e ((r * ((A * c + B * d) * P * x) + k * x) / q) *
    ∑ (y : ℤ ) in Ioc 0 (q:ℤ ), e ((r * ((B * a + D * c) * P * y + B * c * P ^ 2 * x * y)
    + l * y) / q)=
    ∑ (x : ℤ ) in Ioc 0 (q:ℤ ), e ((r * ((A * c + B * d) * P * x) + k * x) / q) *
     q * ite ((q:ℤ )  ∣ B * c * P ^ 2 * x + l * rbar + (B * a + D * c) * P) 1 0,
    {
      sorry,
    /-   apply finset.sum_congr rfl,
      intros x hx,
      rw mul_assoc (e ((r * ((A * c + B * d) * P * x) + k * x) / q)),
      apply dumb,
      have trivi: x≥ 0:=by linarith[((finset.mem_Ioc).mp hx).1],
      exact key x trivi, -/
    },

    rw this,clear this,clear key,
    have key2 : ∑ (x : ℤ ) in Ioc 0 (q:ℤ ), e ((r * ((A * c + B * d) * P * x) + k * x) / q) *
     q * ite ((q:ℤ )  ∣ B * c * P ^ 2 * x + l * rbar + (B * a + D * c) * P) 1 0 =
     ∑ (x : ℤ ) in Ioc 0 (q:ℤ ), e ((r * ((A * c + B * d) * P * x) + k * x) / q) *
     q * ite ((∃(x':ℤ),x=q₂*x'-(Ebar*(l*rbar+(B*a+D*c)*P)/q₁)) ∧ (q₁:ℤ )∣l*rbar+(B*a+D*c)*P) 1 0,
     {
      sorry,

    /-    apply finset.sum_congr rfl,
      intros x hx,
      field_simp,
      by_cases div: (q:ℤ ) ∣ B * c * P ^ 2 * x + l * rbar + (B * a + D * c) * P,
      rw ite_eq_iff, left, refine ⟨div,_ ⟩,
      {
          symmetry,
        rw ite_eq_iff, left, refine ⟨_,by refl ⟩,
        split,
        {

        cases div with z hz,
        rw q_is at hz,
        rw E_is at hz,
        have : (q₁:ℤ ) ∣ l*rbar + (B*a+D*c)*P,
        {
          use -(( E:ℤ ) * x - q₂ * z),
          linarith,
        },
        cases this with zz hzz,
        rw hzz,rw add_assoc at hz, rw hzz at hz,
        have : (E:ℤ ) * x + zz = q₂ * z,
        {
          have :  (q₁:ℤ ) * (E * x + zz) = q₁ * q₂ * z := by linarith,
          rw mul_assoc at this,
          exact dumb2 q10 this,
        },
        have :=@dumb3 _ _ Ebar this,
        rw mul_add at this, rw ← mul_assoc at this,
        cases Ebar_is with zzz hzzz,
        have junk: (Ebar:ℤ )* E = q₂ * zzz + 1 := by linarith,
        rw junk at this,use ((Ebar :ℤ )*z-zzz*x),
        rw dumb4 q10,rw mul_sub,rw← mul_assoc,rw mul_comm (q₂:ℤ ),
        rw mul_assoc, rw← this,
        ring,
        },

        cases div with z hz,
        rw q_is at hz,
        rw E_is at hz,use ((q₂:ℤ )*z-E*x),linarith,


      },
    rw ite_eq_iff, right, refine ⟨div,_ ⟩,
      {

        symmetry,
        rw ite_eq_iff, right, refine ⟨_,by refl ⟩,
        push_neg,
        intro hyp,

        intro hyp2,
        have : (q:ℤ ) ∣ B * c * P ^ 2 * x + l * rbar + (B * a + D * c) * P,
        {
          rw q_is,


          cases hyp2 with z hz,rw add_assoc, rw hz,rw E_is,rw mul_assoc,
          rw ← mul_add,
          apply (mul_dvd_mul_iff_left q10).mpr,
          cases hyp with x1 hx1,
          rw hx1,rw hz, rw dumb4 q10,
          rw (show (E:ℤ ) * (q₂ * x1 - Ebar * z) + z = q₂*(E*x1)+z-(E*Ebar)*z, by ring),
          cases Ebar_is with z2 hz2,
          rw (show (E:ℤ )*Ebar = q₂*z2 +1, by linarith),
          rw (show (q₂:ℤ ) * (E * x1) + z - (q₂ * z2 + 1) * z = q₂*(E*x1-z2*z), by ring),
          use ((E:ℤ ) * x1 - z2 * z),
        },exact div this,
      },  -/
     },

      rw key2, clear key2,
      have: 1 / (q:ℂ ) ^ 2 *(e (r * (A * a + B * b + C * c + D * d) / q) *
     ∑ (x : ℤ) in Ioc 0 (q:ℤ ),e ((r * ((A * c + B * d) * P * x) + k * x) / q) * q *
    ite ((∃ (x' : ℤ), x = q₂ * x' - Ebar * (l * rbar + (B * a + D * c) * P) / q₁) ∧
    (q₁:ℤ ) ∣ l * rbar + (B * a + D * c) * P) 1 0) =
 1 / (q:ℂ ) ^ 2 *
  (e (r * (A * a + B * b + C * c + D * d) / q) * ∑ (x : ℤ) in Ioc 0 (q:ℤ ),
       e ((r * ((A * c + B * d) * P * x) + k * x) / q) * q * (ite (∃ (x' : ℤ),
   x = q₂ * x' - Ebar * (l * rbar + (B * a + D * c) * P) / q₁) 1 0 * ite(
     (q₁:ℤ ) ∣ l * rbar + (B * a + D * c) * P) 1  0)),
      {
        sorry,

   /-      congr' 1,
        congr' 1,
       apply finset.sum_congr rfl,
       intros x hx,
        have:= dumb (e ((r * ((A * c + B * d) * P * x) + k * x) / q) * q) (ite
  ((∃ (x' : ℤ), x = q₂ * x' - Ebar * (l * rbar + (B * a + D * c) * P) / q₁) ∧
     (q₁:ℤ ) ∣ l * rbar + (B * a + D * c) * P)
  1
  0) (ite (∃ (x' : ℤ), x = q₂ * x' - Ebar * (l * rbar + (B * a + D * c) * P) / q₁) 1 0 * ite ((q₁:ℤ ) ∣ l * rbar + (B * a + D * c) * P) 1 0),
  apply this,clear this,
  rw dumb5, -/
      },

      rw this, clear this,

    have: 1 / (q:ℂ ) ^ 2 *(e (r * (A * a + B * b + C * c + D * d) / q) *
     ∑ (x : ℤ) in Ioc 0 (q:ℤ ),e ((r * ((A * c + B * d) * P * x) + k * x) / q) * q *
     (ite (∃ (x' : ℤ), x = q₂ * x' - Ebar * (l * rbar + (B * a + D * c) * P) / q₁) 1 0 *
      ite ((q₁:ℤ ) ∣ l * rbar + (B * a + D * c) * P) 1 0))=
    1 / (q:ℂ ) ^ 2 *(q:ℂ )* (ite ((q₁:ℤ ) ∣ l * rbar + (B * a + D * c) * P) 1 0)*(e (r * (A * a + B * b + C * c + D * d) / q) *
     ∑ (x : ℤ) in Ioc 0 (q:ℤ ),
     e ((r * ((A * c + B * d) * P * x) + k * x) / q)*
     (ite (∃ (x' : ℤ), x = q₂ * x' - Ebar * (l * rbar + (B * a + D * c) * P) / q₁) 1 0)),
     {
      sorry,
       /- rw finset.mul_sum,rw finset.mul_sum,rw finset.mul_sum,rw finset.mul_sum,
       apply finset.sum_congr rfl,
       intros x hx,
       ring, -/
     },
     rw this, clear this,
     have : 1 / (q:ℂ ) ^ 2 *(q:ℂ ) = 1/(q:ℂ ),
     {
      sorry,
      --field_simp;ring,
     },
     rw this, clear this,
     rw mul_assoc,
     have : (q₁:ℂ  ) / q = (1/q)*q₁ := sorry,--by field_simp;ring,
     rw this, clear this,rw mul_assoc (1/(q:ℂ )),rw mul_assoc (1/(q:ℂ )),rw mul_assoc (1/(q:ℂ )),

     congr' 1,
     rw mul_comm (q₁:ℂ ),
     rw ← mul_assoc, rw mul_comm _ (e (r * (A * a + B * b + C * c + D * d) / q)),
     repeat{rw mul_assoc (e (r * (A * a + B * b + C * c + D * d) / q))},
     congr' 1,
        have := div_by_rem (Ebar * (l * rbar + (B * a + D * c) * P) / q₁) q₂ q₂0,
        rcases this with ⟨q',r',div,hr ⟩,
        rw div,

    have : ite ((q₁:ℤ ) ∣ l * rbar + (B * a + D * c) * P) 1 0 * ∑ (x : ℤ) in Ioc 0 (q:ℤ ),
    e ((r * ((A * c + B * d) * P * x) + k * x) / q) * ite (∃ (x' : ℤ), x = q₂ * x' - (q₂ * q' + r')) 1 0=
    ite ((q₁:ℤ ) ∣ l * rbar + (B * a + D * c) * P) 1 0 * ∑ (x : ℤ) in Ioc 0 (q:ℤ ),
    e ((r * ((A * c + B * d) * P * x) + k * x) / q) * ite (∃ (x' : ℤ), x = q₂ * x' - r') 1 0,
    {
      sorry,
      /- congr' 1,
      apply finset.sum_congr rfl,
      intros x hx,
      congr' 1,
      by_cases hyp: ∃ (x' : ℤ), x = q₂ * x' - (q₂ * q' + r'),
      rw ite_eq_iff,
      left,
      refine ⟨hyp,_ ⟩,
      cases hyp with x' hx',
      symmetry,
      rw ite_eq_iff,
      left,
      use (x'-q'),
      rw hx', ring,
      rw ite_eq_iff,
      right,
      refine ⟨hyp,_ ⟩,
      push_neg at hyp,
      symmetry,
      rw ite_eq_iff,
      right,
      refine ⟨_,by refl ⟩,
      push_neg,
      intro x',
      have := hyp (x'+q'),
      by_contra,
      rw h at this,
      have lol:(q₂:ℤ ) * (x' + q') - (q₂ * q' + r')=q₂*x'-r':= by ring,
      rw lol at this,
      exact this (by refl: (q₂:ℤ )*x'-r'=q₂*x'-r'), -/
    },

 rw this, clear this,


    have : ite ((q₁:ℤ ) ∣ l * rbar + (B * a + D * c) * P) 1 0 * ∑ (x : ℤ) in Ioc 0 (q:ℤ ),
    e ((r * ((A * c + B * d) * P * x) + k * x) / q) * ite (∃ (x' : ℤ), x = q₂ * x' - r') 1 0
    =ite ((q₁:ℤ ) ∣ l * rbar + (B * a + D * c) * P) 1 0 * ∑ (x : ℤ) in Ioc 0 (q:ℤ ), e ((r * ((A * c + B * d) * P * x)
      + k * x) / q) * ite (∃ (x' : Ioc 0 (q₁:ℤ )), x = q₂ * x' - r') 1 0,
      {
        sorry,
        /-
        congr' 1,
        apply finset.sum_congr rfl,
        intros x hx,
        congr' 1,
        by_cases hyp: ∃ (x' : ℤ), x = q₂ * x' - r',
        rw ite_eq_iff, left,
        cases hyp with x' hx',
        split, use x',
        exact hx',
        symmetry,
        rw ite_eq_iff, left,
        refine ⟨_,by refl ⟩,
        use x',
        rw finset.mem_Ioc,
        rw finset.mem_Ioc at hx,

        split,
        {
          apply dumb6 (x+r') q₂,
          linarith,linarith,linarith,
        },
        by_contra,
        push_neg at h,
        have : (q₂:ℤ )*(q₁+1)≤ q₂*x' ,
        {
          have : (q₁:ℤ )+1≤ x',
          {
            suffices : (q₁:ℤ ) ≤ x' -1,
            {
              linarith,
            },
            rw int.le_sub_one_iff,
            exact h,
          },
          rw mul_le_mul_left ,exact this,
          exact q₂0,
        },
        rw mul_add at this,rw mul_comm at this, rw ← q_is at this,
        have hhx':  (q₂:ℤ ) * x' = x + r',
        {
          rw hx', ring,
        },
        rw hhx' at this,
        rw mul_one at this,
        linarith,
        exact hx',
        {
          rw ite_eq_iff,right,split, exact hyp, symmetry, rw ite_eq_iff,
          right, push_neg at hyp, refine ⟨_,by refl ⟩, push_neg,
          intros x', exact (hyp x'),
        }, -/
      },


        rw this, clear this,
        have : ite ((q₁:ℤ ) ∣ l * rbar + (B * a + D * c) * P) 1 0 *
  ∑ (x : ℤ) in
    Ioc 0 (q:ℤ ),
    e ((r * ((A * c + B * d) * P * x) + k * x) / q) *
      ite (∃ (x' : (Ioc 0 (q₁:ℤ ))), x = q₂ * x' - r') 1 0
 =
 ite ((q₁:ℤ ) ∣ l * rbar + (B * a + D * c) * P) 1 0 *
  ∑ (x : ℤ) in
    Ioc 0 (q:ℤ ),
    e ((r * ((A * c + B * d) * P * x) + k * x) / q) *
      ∑ (x' : ℤ) in Ioc 0 (q₁:ℤ ), ite (x = q₂ * x' - r') 1 0,
      {
        sorry,
       /-  congr' 1,
        apply finset.sum_congr rfl,
        intros x hx,
        congr' 1,
        have:= dumb7 x (q₁:ℤ ) (q₂:ℤ ) (r': ℤ ) (by linarith),
        rw this, -/
      },

      rw this,clear this,
      rw finset.mul_sum,
      simp_rw finset.mul_sum,
      rw finset.sum_comm,
      simp_rw ← finset.mul_sum,
      simp_rw mul_ite,
      simp_rw mul_zero,
      have : ∀ (x:ℤ )(x_1:ℤ ),x_1 = q₂ * x - r'↔(q₂:ℤ ) * x - r' = x_1:=λ a b ,⟨ (λ hyp,by exact hyp.symm),(λ hyp,by exact hyp.symm)⟩,
      simp_rw this,
      simp_rw finset.sum_ite_eq, clear this,
      rw finset.sum_ite_of_true,
      simp_rw mul_one,
      have : ∀ (x:ℤ  ),((r:ℝ   ) * ((A * c + B * d) * P * (↑((q₂:ℤ ) * x - r') )) + k * (↑((q₂:ℤ ) * x - r'))) / q
      = (-r'*r*P*(A*c+B*d)-k*r')/q + q₂*(x*(r*P*(A*c+B*d)+k))/q,
      {
        sorry,--intro x, field_simp,ring,
      },
      simp_rw this,
      simp_rw e_add,
      simp_rw ← finset.mul_sum,
      simp_rw q_isR,
      have : ∀ (x:ℤ ), (q₂:ℝ) * (x * (r * P * (A * c + B * d) + k)) / (q₁ * q₂)=
       (x * (r * P * (A * c + B * d) + k)) / q₁,
       {
        sorry,
        /- intro x,
        field_simp, ring, -/
       },
       simp_rw this, clear this,
      have key:= orthogonalityZ (r * P * (A * c + B * d) + k) q1N _ _ _,
      have : (↑ ((r:ℤ ) * (P:ℤ ) * ((A:ℤ ) * (c:ℤ ) + (B:ℤ ) * (d:ℤ )) + (k:ℤ )) ) = ((r:ℝ  ) * P * (A * c + B * d) + k),
      {
          sorry,--norm_cast,
      } ,
      rw this at key,
      rw key,

      by_cases div2: ¬ ((q₁:ℤ ) ∣ r * P * (A * c + B * d) + k),
      {
        sorry,
        /- have := (ne.ite_eq_right_iff _).mpr div2,
        rw this,
        have : ¬ ((q₁:ℤ ) ∣ r * P * (A * c + B * d) + k ∧
  (q₁:ℤ ) ∣ l * rbar + (B * a + D * c) * P),
  {
        push_neg,contrapose,intro lol, exact div2,
  },
        have := (ne.ite_eq_right_iff _).mpr this,
        rw this,
        ring,
        norm_cast at q10, norm_cast,exact q10,
        simp, -/
      },
      by_cases div3 :¬ ((q₁:ℤ ) ∣ l * rbar + (B * a + D * c) * P),
      {
        sorry,
       /-  have := (ne.ite_eq_right_iff _).mpr div3,
        rw this,
     have : ¬ ((q₁:ℤ ) ∣ r * P * (A * c + B * d) + k ∧
  (q₁:ℤ ) ∣ l * rbar + (B * a + D * c) * P),
  {
        push_neg,contrapose,intro lol, exfalso,exact lol div3,
  },
        have := (ne.ite_eq_right_iff _).mpr this,
        rw this,
        ring,
        norm_cast at q10, norm_cast,exact q10,
        simp, -/
      },

      have :ite ((q₁:ℤ ) ∣ l * rbar + (B * a + D * c) * P) (1:ℂ ) 0 *
  (e ((-(r':ℤ ) * r * P * (A * c + B * d) - k * r') / (q₁ * q₂)) *
     (q₁ * ite ((q₁:ℤ ) ∣ r * P * (A * c + B * d) + k) 1 0))=
 (q₁:ℂ) * (ite ((q₁:ℤ ) ∣ r * P * (A * c + B * d) + k) 1 0 *
      ite ((q₁:ℤ ) ∣ l * rbar + (B * a + D * c) * P) 1 0) *
      e ((-(r' :ℤ ) * r * P * (A * c + B * d) - k * r') / (q₁ * q₂)),
      {
       sorry,--ring,
      },
      rw this, clear this,
      rw← dumb9,
      have : (q₁:ℂ ) * ite ((q₁:ℤ ) ∣ r * P * (A * c + B * d) + k ∧ (q₁:ℤ ) ∣ l * rbar + (B * a + D * c) * P) 1 0 *
      e ((-(r':ℤ ) * r * P * (A * c + B * d) - k * r') / (q₁ * q₂))=
       ite ((q₁:ℤ ) ∣ r * P * (A * c + B * d) + k ∧ (q₁:ℤ ) ∣ l * rbar + (B * a + D * c) * P) q₁ 0 *
      e ((-(r':ℤ ) * r * P * (A * c + B * d) - k * r') / (q₁ * q₂)),
      {
        sorry,--field_simp,
      },
      rw this,clear this,
      congr' 1,
      clear this, clear this,
      have: -(r':ℝ ) * r * P * (A * c + B * d) - k * r'
      =-(r':ℝ ) * (r * P * (A * c + B * d) + k),
      {
        sorry,--ring,
      },
        rw this, clear this,
      simp at div2,
      simp,
      have : e (-((r':ℝ ) * (r * P * (A * c + B * d) + k)) / (q₁ * q₂))
      =e (-((r':ℝ ) * (r * P * (A * c + B * d) + k)) / (q₁ * q₂) -
      q₂*q'*(r * P * (A * c + B * d) + k)/(q₁*q₂)+
      q₂*q'*(r * P * (A * c + B * d) + k)/(q₁*q₂)),
      {
        congr' 1,
        ring,
      },
      rw this, clear this,
      rw e_add,

      have : e ((q₂:ℝ ) * q' * (r * P * (A * c + B * d) + k) / (q₁ * q₂)) =(1:ℂ ),
      {
        sorry,
        /-  cases div2 with z div2,
        have div3: (r:ℝ ) * P * (A * c + B * d) + k = q₁ * z := by norm_cast; exact div2,
        rw div3,
        have : (q₂:ℝ ) * q' * (q₁ * z) / (q₁ * q₂)=q' *  z,
        {
          field_simp,ring,

        },
        rw this, clear this,
        have :e (q' * z)= e (↑(q' * z)),
        {
          congr' 1,
          norm_cast,
        },
        rw this, clear this,
        apply e_int,  -/


      },

      rw this, clear this, rw mul_one,
      congr' 1,
      field_simp,
      have : -((r':ℝ ) * (r * P * (A * c + B * d) + k) * (q₁ * q₂)) -
  q₁ * q₂ * (q₂ * q' * (r * P * (A * c + B * d) + k))=
  -((q₂ * q'+r') * (r * P * (A * c + B * d) + k) * (q₁ * q₂)),
  {
    sorry,--ring,
  },
  rw this, clear this,
  have : (Ebar:ℝ ) * (l * rbar + (B * a + D * c) * P) / q₁ = q₂ * q' + r',
  {
    sorry,
    /- field_simp,
    norm_cast,
    rw← div,
    field_simp,
    ring,
    rw int.mul_div_cancel',
    ring,
    simp at div3,
    have:= div3.linear_comb (_: (q₁:ℤ )∣ 0) Ebar 0,
    simp at this, exact this, simp, -/

  },

  rw ← this, clear this,field_simp, ring,
  exact (0:ℤ ),exact (q₁:ℤ ), refl, exact ge0Z, simp,
  { intros x xhyp,
    rw finset.mem_Ioc at ⊢ xhyp,
    split,
    { have := int.mul_le_mul_of_nonneg_left (dumb10 _ xhyp.1) (int.le_of_lt q₂0),
      rw mul_one at this,
      linarith, },
    { have : (q₂ : ℤ) * x ≤ q₂ * q₁ := mul_le_mul_of_nonneg_left xhyp.2 (int.le_of_lt q₂0),
      rw mul_comm at q_is, rw ← q_is at this, linarith, }, },
  norm_cast at qC,

end
