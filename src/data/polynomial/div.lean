/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import data.polynomial.monic
import ring_theory.multiplicity

/-!
# Division of univariate polynomials

The main defs are `div_by_monic` and `mod_by_monic`.
The compatibility between these is given by `mod_by_monic_add_div`.
We also define `root_multiplicity`.
-/

noncomputable theory
open_locale classical big_operators

open finset
namespace polynomial
universes u v w z
variables {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

section comm_semiring
variables [comm_semiring R]

theorem X_dvd_iff {α : Type u} [comm_semiring α] {f : polynomial α} : X ∣ f ↔ f.coeff 0 = 0 :=
⟨λ ⟨g, hfg⟩, by rw [hfg, mul_comm, coeff_mul_X_zero],
λ hf, ⟨f.div_X, by rw [mul_comm, ← add_zero (f.div_X * X), ← C_0, ← hf, div_X_mul_X_add]⟩⟩

end comm_semiring


section comm_semiring

variables [comm_semiring R] {p q : polynomial R}

lemma multiplicity_finite_of_degree_pos_of_monic (hp : (0 : with_bot ℕ) < degree p)
  (hmp : monic p) (hq : q ≠ 0) : multiplicity.finite p q :=
have zn0 : (0 : R) ≠ 1, from λ h, by haveI := subsingleton_of_zero_eq_one h;
  exact hq (subsingleton.elim _ _),
⟨nat_degree q, λ ⟨r, hr⟩,
  have hp0 : p ≠ 0, from λ hp0, by simp [hp0] at hp; contradiction,
  have hr0 : r ≠ 0, from λ hr0, by simp * at *,
  have hpn1 : leading_coeff p ^ (nat_degree q + 1) = 1,
    by simp [show _ = _, from hmp],
  have hpn0' : leading_coeff p ^ (nat_degree q + 1) ≠ 0,
    from hpn1.symm ▸ zn0.symm,
  have hpnr0 : leading_coeff (p ^ (nat_degree q + 1)) * leading_coeff r ≠ 0,
    by simp only [leading_coeff_pow' hpn0', leading_coeff_eq_zero, hpn1,
      one_pow, one_mul, ne.def, hr0]; simp,
  have hnp : 0 < nat_degree p,
    by rw [← with_bot.coe_lt_coe, ← degree_eq_nat_degree hp0];
    exact hp,
  begin
    have := congr_arg nat_degree hr,
    rw [nat_degree_mul' hpnr0,  nat_degree_pow' hpn0', add_mul, add_assoc] at this,
    exact ne_of_lt (lt_add_of_le_of_pos (le_mul_of_one_le_right (nat.zero_le _) hnp)
      (add_pos_of_pos_of_nonneg (by rwa one_mul) (nat.zero_le _))) this
  end⟩

end comm_semiring


section ring
variables [ring R] {p q : polynomial R}


lemma div_wf_lemma (h : degree q ≤ degree p ∧ p ≠ 0) (hq : monic q) :
  degree (p - C (leading_coeff p) * X ^ (nat_degree p - nat_degree q) * q) < degree p :=
have hp : leading_coeff p ≠ 0 := mt leading_coeff_eq_zero.1 h.2,
if h0 : p - C (leading_coeff p) * X ^ (nat_degree p - nat_degree q) * q = 0
then h0.symm ▸ (lt_of_not_ge $ mt le_bot_iff.1 (mt degree_eq_bot.1 h.2))
else
  have hq0 : q ≠ 0 := hq.ne_zero_of_polynomial_ne h.2,
  have hlt : nat_degree q ≤ nat_degree p := with_bot.coe_le_coe.1
    (by rw [← degree_eq_nat_degree h.2, ← degree_eq_nat_degree hq0];
    exact h.1),
  degree_sub_lt
  (by rw [hq.degree_mul, degree_C_mul_X_pow _ hp, degree_eq_nat_degree h.2,
      degree_eq_nat_degree hq0, ← with_bot.coe_add, nat.sub_add_cancel hlt])
  h.2
  (by rw [leading_coeff_mul_monic hq, leading_coeff_mul_X_pow, leading_coeff_C])

/-- See `div_by_monic`. -/
noncomputable def div_mod_by_monic_aux : Π (p : polynomial R) {q : polynomial R},
  monic q → polynomial R × polynomial R
| p := λ q hq, if h : degree q ≤ degree p ∧ p ≠ 0 then
  let z := C (leading_coeff p) * X^(nat_degree p - nat_degree q)  in
  have wf : _ := div_wf_lemma h hq,
  let dm := div_mod_by_monic_aux (p - z * q) hq in
  ⟨z + dm.1, dm.2⟩
  else ⟨0, p⟩
using_well_founded {dec_tac := tactic.assumption}

/-- `div_by_monic` gives the quotient of `p` by a monic polynomial `q`. -/
def div_by_monic (p q : polynomial R) : polynomial R :=
if hq : monic q then (div_mod_by_monic_aux p hq).1 else 0

/-- `mod_by_monic` gives the remainder of `p` by a monic polynomial `q`. -/
def mod_by_monic (p q : polynomial R) : polynomial R :=
if hq : monic q then (div_mod_by_monic_aux p hq).2 else p

infixl  ` /ₘ ` : 70 := div_by_monic

infixl ` %ₘ ` : 70 := mod_by_monic

lemma degree_mod_by_monic_lt [nontrivial R] : ∀ (p : polynomial R) {q : polynomial R}
  (hq : monic q), degree (p %ₘ q) < degree q
| p := λ q hq,
if h : degree q ≤ degree p ∧ p ≠ 0 then
  have wf : _ := div_wf_lemma ⟨h.1, h.2⟩ hq,
  have degree ((p - C (leading_coeff p) * X ^ (nat_degree p - nat_degree q) * q) %ₘ q) < degree q :=
      degree_mod_by_monic_lt (p - C (leading_coeff p) * X ^ (nat_degree p - nat_degree q) * q)
      hq,
  begin
    unfold mod_by_monic at this ⊢,
    unfold div_mod_by_monic_aux,
    rw dif_pos hq at this ⊢,
    rw if_pos h,
    exact this
  end
else
  or.cases_on (not_and_distrib.1 h) begin
    unfold mod_by_monic div_mod_by_monic_aux,
    rw [dif_pos hq, if_neg h],
    exact lt_of_not_ge,
  end
  begin
    assume hp,
    unfold mod_by_monic div_mod_by_monic_aux,
    rw [dif_pos hq, if_neg h, not_not.1 hp],
    exact lt_of_le_of_ne bot_le
      (ne.symm (mt degree_eq_bot.1 hq.ne_zero)),
  end
using_well_founded {dec_tac := tactic.assumption}

@[simp] lemma zero_mod_by_monic (p : polynomial R) : 0 %ₘ p = 0 :=
begin
  unfold mod_by_monic div_mod_by_monic_aux,
  by_cases hp : monic p,
  { rw [dif_pos hp, if_neg (mt and.right (not_not_intro rfl))] },
  { rw [dif_neg hp] }
end

@[simp] lemma zero_div_by_monic (p : polynomial R) : 0 /ₘ p = 0 :=
begin
  unfold div_by_monic div_mod_by_monic_aux,
  by_cases hp : monic p,
  { rw [dif_pos hp, if_neg (mt and.right (not_not_intro rfl))] },
  { rw [dif_neg hp] }
end

@[simp] lemma mod_by_monic_zero (p : polynomial R) : p %ₘ 0 = p :=
if h : monic (0 : polynomial R) then (subsingleton_of_monic_zero h).1 _ _ else
by unfold mod_by_monic div_mod_by_monic_aux; rw dif_neg h

@[simp] lemma div_by_monic_zero (p : polynomial R) : p /ₘ 0 = 0 :=
if h : monic (0 : polynomial R) then (subsingleton_of_monic_zero h).1 _ _ else
by unfold div_by_monic div_mod_by_monic_aux; rw dif_neg h

lemma div_by_monic_eq_of_not_monic (p : polynomial R) (hq : ¬monic q) : p /ₘ q = 0 := dif_neg hq

lemma mod_by_monic_eq_of_not_monic (p : polynomial R) (hq : ¬monic q) : p %ₘ q = p := dif_neg hq

lemma mod_by_monic_eq_self_iff [nontrivial R] (hq : monic q) : p %ₘ q = p ↔ degree p < degree q :=
⟨λ h, h ▸ degree_mod_by_monic_lt _ hq,
λ h, have ¬ degree q ≤ degree p := not_le_of_gt h,
  by unfold mod_by_monic div_mod_by_monic_aux; rw [dif_pos hq, if_neg (mt and.left this)]⟩

theorem degree_mod_by_monic_le (p : polynomial R) {q : polynomial R}
  (hq : monic q) : degree (p %ₘ q) ≤ degree q :=
by { nontriviality R, exact (degree_mod_by_monic_lt _ hq).le }

end ring

section comm_ring
variables [comm_ring R] {p q : polynomial R}

lemma mod_by_monic_eq_sub_mul_div : ∀ (p : polynomial R) {q : polynomial R} (hq : monic q),
  p %ₘ q = p - q * (p /ₘ q)
| p := λ q hq,
  if h : degree q ≤ degree p ∧ p ≠ 0 then
    have wf : _ := div_wf_lemma h hq,
    have ih : _ := mod_by_monic_eq_sub_mul_div
      (p - C (leading_coeff p) * X ^ (nat_degree p - nat_degree q) * q) hq,
    begin
      unfold mod_by_monic div_by_monic div_mod_by_monic_aux,
      rw [dif_pos hq, if_pos h],
      rw [mod_by_monic, dif_pos hq] at ih,
      refine ih.trans _,
      unfold div_by_monic,
      rw [dif_pos hq, dif_pos hq, if_pos h, mul_add, sub_add_eq_sub_sub, mul_comm]
    end
  else
    begin
      unfold mod_by_monic div_by_monic div_mod_by_monic_aux,
      rw [dif_pos hq, if_neg h, dif_pos hq, if_neg h, mul_zero, sub_zero]
    end
using_well_founded {dec_tac := tactic.assumption}

lemma mod_by_monic_add_div (p : polynomial R) {q : polynomial R} (hq : monic q) :
  p %ₘ q + q * (p /ₘ q) = p := eq_sub_iff_add_eq.1 (mod_by_monic_eq_sub_mul_div p hq)

lemma div_by_monic_eq_zero_iff [nontrivial R] (hq : monic q) : p /ₘ q = 0 ↔ degree p < degree q :=
⟨λ h, by have := mod_by_monic_add_div p hq;
  rwa [h, mul_zero, add_zero, mod_by_monic_eq_self_iff hq] at this,
λ h, have ¬ degree q ≤ degree p := not_le_of_gt h,
  by unfold div_by_monic div_mod_by_monic_aux; rw [dif_pos hq, if_neg (mt and.left this)]⟩

lemma degree_add_div_by_monic (hq : monic q) (h : degree q ≤ degree p) :
  degree q + degree (p /ₘ q) = degree p :=
begin
  nontriviality R,
  have hdiv0 : p /ₘ q ≠ 0 := by rwa [(≠), div_by_monic_eq_zero_iff hq, not_lt],
  have hlc : leading_coeff q * leading_coeff (p /ₘ q) ≠ 0 :=
    by rwa [monic.def.1 hq, one_mul, (≠), leading_coeff_eq_zero],
  have hmod : degree (p %ₘ q) < degree (q * (p /ₘ q)) :=
    calc degree (p %ₘ q) < degree q : degree_mod_by_monic_lt _ hq
    ... ≤ _ : by rw [degree_mul' hlc, degree_eq_nat_degree hq.ne_zero,
        degree_eq_nat_degree hdiv0, ← with_bot.coe_add, with_bot.coe_le_coe];
      exact nat.le_add_right _ _,
  calc degree q + degree (p /ₘ q) = degree (q * (p /ₘ q)) : eq.symm (degree_mul' hlc)
  ... = degree (p %ₘ q + q * (p /ₘ q)) : (degree_add_eq_right_of_degree_lt hmod).symm
  ... = _ : congr_arg _ (mod_by_monic_add_div _ hq)
end

lemma degree_div_by_monic_le (p q : polynomial R) : degree (p /ₘ q) ≤ degree p :=
if hp0 : p = 0 then by simp only [hp0, zero_div_by_monic, le_refl]
else if hq : monic q then
  if h : degree q ≤ degree p
  then by haveI := nontrivial.of_polynomial_ne hp0;
    rw [← degree_add_div_by_monic hq h, degree_eq_nat_degree hq.ne_zero,
      degree_eq_nat_degree (mt (div_by_monic_eq_zero_iff hq).1 (not_lt.2 h))];
    exact with_bot.coe_le_coe.2 (nat.le_add_left _ _)
  else
    by unfold div_by_monic div_mod_by_monic_aux;
      simp only [dif_pos hq, h, false_and, if_false, degree_zero, bot_le]
else (div_by_monic_eq_of_not_monic p hq).symm ▸ bot_le

lemma degree_div_by_monic_lt (p : polynomial R) {q : polynomial R} (hq : monic q)
  (hp0 : p ≠ 0) (h0q : 0 < degree q) : degree (p /ₘ q) < degree p :=
if hpq : degree p < degree q
then begin
  haveI := nontrivial.of_polynomial_ne hp0,
  rw [(div_by_monic_eq_zero_iff hq).2 hpq, degree_eq_nat_degree hp0],
  exact with_bot.bot_lt_coe _
end
else begin
  haveI := nontrivial.of_polynomial_ne hp0,
  rw [← degree_add_div_by_monic hq (not_lt.1 hpq), degree_eq_nat_degree hq.ne_zero,
        degree_eq_nat_degree (mt (div_by_monic_eq_zero_iff hq).1 hpq)],
  exact with_bot.coe_lt_coe.2 (nat.lt_add_of_pos_left
    (with_bot.coe_lt_coe.1 $ (degree_eq_nat_degree hq.ne_zero) ▸ h0q))
end

theorem nat_degree_div_by_monic {R : Type u} [comm_ring R] (f : polynomial R) {g : polynomial R}
  (hg : g.monic) : nat_degree (f /ₘ g) = nat_degree f - nat_degree g :=
begin
  by_cases h01 : (0 : R) = 1,
  { haveI := subsingleton_of_zero_eq_one h01,
    rw [subsingleton.elim (f /ₘ g) 0, subsingleton.elim f 0, subsingleton.elim g 0,
        nat_degree_zero] },
  haveI : nontrivial R := ⟨⟨0, 1, h01⟩⟩,
  by_cases hfg : f /ₘ g = 0,
  { rw [hfg, nat_degree_zero], rw div_by_monic_eq_zero_iff hg at hfg,
    rw nat.sub_eq_zero_of_le (nat_degree_le_nat_degree $ le_of_lt hfg) },
  have hgf := hfg, rw div_by_monic_eq_zero_iff hg at hgf, push_neg at hgf,
  have := degree_add_div_by_monic hg hgf,
  have hf : f ≠ 0, { intro hf, apply hfg, rw [hf, zero_div_by_monic] },
  rw [degree_eq_nat_degree hf, degree_eq_nat_degree hg.ne_zero, degree_eq_nat_degree hfg,
      ← with_bot.coe_add, with_bot.coe_eq_coe] at this,
  rw [← this, nat.add_sub_cancel_left]
end

lemma div_mod_by_monic_unique {f g} (q r : polynomial R) (hg : monic g)
  (h : r + g * q = f ∧ degree r < degree g) : f /ₘ g = q ∧ f %ₘ g = r :=
begin
  nontriviality R,
  have h₁ : r - f %ₘ g = -g * (q - f /ₘ g),
    from eq_of_sub_eq_zero
      (by rw [← sub_eq_zero_of_eq (h.1.trans (mod_by_monic_add_div f hg).symm)];
        simp [mul_add, mul_comm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]),
  have h₂ : degree (r - f %ₘ g) = degree (g * (q - f /ₘ g)),
    by simp [h₁],
  have h₄ : degree (r - f %ₘ g) < degree g,
    from calc degree (r - f %ₘ g) ≤ max (degree r) (degree (f %ₘ g)) :
      degree_sub_le _ _
    ... < degree g : max_lt_iff.2 ⟨h.2, degree_mod_by_monic_lt _ hg⟩,
  have h₅ : q - (f /ₘ g) = 0,
    from by_contradiction
      (λ hqf, not_le_of_gt h₄ $
        calc degree g ≤ degree g + degree (q - f /ₘ g) :
          by erw [degree_eq_nat_degree hg.ne_zero, degree_eq_nat_degree hqf,
              with_bot.coe_le_coe];
            exact nat.le_add_right _ _
        ... = degree (r - f %ₘ g) :
          by rw [h₂, degree_mul']; simpa [monic.def.1 hg]),
  exact ⟨eq.symm $ eq_of_sub_eq_zero h₅,
    eq.symm $ eq_of_sub_eq_zero $ by simpa [h₅] using h₁⟩
end

lemma map_mod_div_by_monic [comm_ring S] (f : R →+* S) (hq : monic q) :
  (p /ₘ q).map f = p.map f /ₘ q.map f ∧ (p %ₘ q).map f = p.map f %ₘ q.map f :=
begin
  nontriviality S,
  haveI : nontrivial R := f.domain_nontrivial,
  have : map f p /ₘ map f q = map f (p /ₘ q) ∧ map f p %ₘ map f q = map f (p %ₘ q),
  { exact (div_mod_by_monic_unique ((p /ₘ q).map f) _ (monic_map f hq)
      ⟨eq.symm $ by rw [← map_mul, ← map_add, mod_by_monic_add_div _ hq],
      calc _ ≤ degree (p %ₘ q) : degree_map_le _ _
      ... < degree q : degree_mod_by_monic_lt _ hq
      ... = _ : eq.symm $ degree_map_eq_of_leading_coeff_ne_zero _
        (by rw [monic.def.1 hq, f.map_one]; exact one_ne_zero)⟩) },
  exact ⟨this.1.symm, this.2.symm⟩
end

lemma map_div_by_monic [comm_ring S] (f : R →+* S) (hq : monic q) :
  (p /ₘ q).map f = p.map f /ₘ q.map f :=
(map_mod_div_by_monic f hq).1

lemma map_mod_by_monic [comm_ring S] (f : R →+* S) (hq : monic q) :
  (p %ₘ q).map f = p.map f %ₘ q.map f :=
(map_mod_div_by_monic f hq).2

lemma dvd_iff_mod_by_monic_eq_zero (hq : monic q) : p %ₘ q = 0 ↔ q ∣ p :=
⟨λ h, by rw [← mod_by_monic_add_div p hq, h, zero_add];
  exact dvd_mul_right _ _,
λ h, begin
  nontriviality R,
  obtain ⟨r, hr⟩ := exists_eq_mul_right_of_dvd h,
  by_contradiction hpq0,
  have hmod : p %ₘ q = q * (r - p /ₘ q),
  { rw [mod_by_monic_eq_sub_mul_div _ hq, mul_sub, ← hr] },
  have : degree (q * (r - p /ₘ q)) < degree q :=
    hmod ▸ degree_mod_by_monic_lt _ hq,
  have hrpq0 : leading_coeff (r - p /ₘ q) ≠ 0 :=
    λ h, hpq0 $ leading_coeff_eq_zero.1
      (by rw [hmod, leading_coeff_eq_zero.1 h, mul_zero, leading_coeff_zero]),
  have hlc : leading_coeff q * leading_coeff (r - p /ₘ q) ≠ 0 :=
    by rwa [monic.def.1 hq, one_mul],
  rw [degree_mul' hlc, degree_eq_nat_degree hq.ne_zero,
      degree_eq_nat_degree (mt leading_coeff_eq_zero.2 hrpq0)] at this,
    exact not_lt_of_ge (nat.le_add_right _ _) (with_bot.some_lt_some.1 this)
end⟩

theorem map_dvd_map [comm_ring S] (f : R →+* S) (hf : function.injective f) {x y : polynomial R}
  (hx : x.monic) : x.map f ∣ y.map f ↔ x ∣ y :=
begin
  rw [← dvd_iff_mod_by_monic_eq_zero hx, ← dvd_iff_mod_by_monic_eq_zero (monic_map f hx),
    ← map_mod_by_monic f hx],
  exact ⟨λ H, map_injective f hf $ by rw [H, map_zero],
  λ H, by rw [H, map_zero]⟩
end

@[simp] lemma mod_by_monic_one (p : polynomial R) : p %ₘ 1 = 0 :=
(dvd_iff_mod_by_monic_eq_zero (by convert monic_one)).2 (one_dvd _)

@[simp] lemma div_by_monic_one (p : polynomial R) : p /ₘ 1 = p :=
by conv_rhs { rw [← mod_by_monic_add_div p monic_one] }; simp

@[simp] lemma mod_by_monic_X_sub_C_eq_C_eval (p : polynomial R) (a : R) :
  p %ₘ (X - C a) = C (p.eval a) :=
begin
  nontriviality R,
  have h : (p %ₘ (X - C a)).eval a = p.eval a,
  { rw [mod_by_monic_eq_sub_mul_div _ (monic_X_sub_C a), eval_sub, eval_mul,
        eval_sub, eval_X, eval_C, sub_self, zero_mul, sub_zero] },
  have : degree (p %ₘ (X - C a)) < 1 :=
    degree_X_sub_C a ▸ degree_mod_by_monic_lt p (monic_X_sub_C a),
  have : degree (p %ₘ (X - C a)) ≤ 0,
  { cases (degree (p %ₘ (X - C a))),
    { exact bot_le },
    { exact with_bot.some_le_some.2 (nat.le_of_lt_succ (with_bot.some_lt_some.1 this)) } },
  rw [eq_C_of_degree_le_zero this, eval_C] at h,
  rw [eq_C_of_degree_le_zero this, h]
end

lemma mul_div_by_monic_eq_iff_is_root : (X - C a) * (p /ₘ (X - C a)) = p ↔ is_root p a :=
⟨λ h, by rw [← h, is_root.def, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul],
λ h : p.eval a = 0,
  by conv {to_rhs, rw ← mod_by_monic_add_div p (monic_X_sub_C a)};
    rw [mod_by_monic_X_sub_C_eq_C_eval, h, C_0, zero_add]⟩

lemma dvd_iff_is_root : (X - C a) ∣ p ↔ is_root p a :=
⟨λ h, by rwa [← dvd_iff_mod_by_monic_eq_zero (monic_X_sub_C _),
    mod_by_monic_X_sub_C_eq_C_eval, ← C_0, C_inj] at h,
  λ h, ⟨(p /ₘ (X - C a)), by rw mul_div_by_monic_eq_iff_is_root.2 h⟩⟩

lemma mod_by_monic_X (p : polynomial R) : p %ₘ X = C (p.eval 0) :=
by rw [← mod_by_monic_X_sub_C_eq_C_eval, C_0, sub_zero]

lemma eval₂_mod_by_monic_eq_self_of_root [comm_ring S] {f : R →+* S}
  {p q : polynomial R} (hq : q.monic) {x : S} (hx : q.eval₂ f x = 0) :
  (p %ₘ q).eval₂ f x = p.eval₂ f x :=
by rw [mod_by_monic_eq_sub_mul_div p hq, eval₂_sub, eval₂_mul, hx, zero_mul, sub_zero]

section multiplicity
/-- An algorithm for deciding polynomial divisibility.
The algorithm is "compute `p %ₘ q` and compare to `0`". `
See `polynomial.mod_by_monic` for the algorithm that computes `%ₘ`.
 -/
def decidable_dvd_monic (p : polynomial R) (hq : monic q) : decidable (q ∣ p) :=
decidable_of_iff (p %ₘ q = 0) (dvd_iff_mod_by_monic_eq_zero hq)

open_locale classical

lemma multiplicity_X_sub_C_finite (a : R) (h0 : p ≠ 0) :
  multiplicity.finite (X - C a) p :=
multiplicity_finite_of_degree_pos_of_monic
  (have (0 : R) ≠ 1, from (λ h, by haveI := subsingleton_of_zero_eq_one h;
      exact h0 (subsingleton.elim _ _)),
    by haveI : nontrivial R := ⟨⟨0, 1, this⟩⟩; rw degree_X_sub_C; exact dec_trivial)
    (monic_X_sub_C _) h0
/-- The largest power of `X - C a` which divides `p`.
This is computable via the divisibility algorithm `decidable_dvd_monic`. -/
def root_multiplicity (a : R) (p : polynomial R) : ℕ :=
if h0 : p = 0 then 0
else let I : decidable_pred (λ n : ℕ, ¬(X - C a) ^ (n + 1) ∣ p) :=
  λ n, @not.decidable _ (decidable_dvd_monic p (monic_pow (monic_X_sub_C a) (n + 1))) in
by exactI nat.find (multiplicity_X_sub_C_finite a h0)

lemma root_multiplicity_eq_multiplicity (p : polynomial R) (a : R) :
  root_multiplicity a p = if h0 : p = 0 then 0 else
  (multiplicity (X - C a) p).get (multiplicity_X_sub_C_finite a h0) :=
by simp [multiplicity, root_multiplicity, part.dom];
  congr; funext; congr

lemma pow_root_multiplicity_dvd (p : polynomial R) (a : R) :
  (X - C a) ^ root_multiplicity a p ∣ p :=
if h : p = 0 then by simp [h]
else by rw [root_multiplicity_eq_multiplicity, dif_neg h];
  exact multiplicity.pow_multiplicity_dvd _

lemma div_by_monic_mul_pow_root_multiplicity_eq
  (p : polynomial R) (a : R) :
  p /ₘ ((X - C a) ^ root_multiplicity a p) *
  (X - C a) ^ root_multiplicity a p = p :=
have monic ((X - C a) ^ root_multiplicity a p),
  from monic_pow (monic_X_sub_C _) _,
by conv_rhs { rw [← mod_by_monic_add_div p this,
    (dvd_iff_mod_by_monic_eq_zero this).2 (pow_root_multiplicity_dvd _ _)] };
  simp [mul_comm]

lemma eval_div_by_monic_pow_root_multiplicity_ne_zero
  {p : polynomial R} (a : R) (hp : p ≠ 0) :
  eval a (p /ₘ ((X - C a) ^ root_multiplicity a p)) ≠ 0 :=
begin
  haveI : nontrivial R := nontrivial.of_polynomial_ne hp,
  rw [ne.def, ← is_root.def, ← dvd_iff_is_root],
  rintros ⟨q, hq⟩,
  have := div_by_monic_mul_pow_root_multiplicity_eq p a,
  rw [mul_comm, hq, ← mul_assoc, ← pow_succ',
    root_multiplicity_eq_multiplicity, dif_neg hp] at this,
  exact multiplicity.is_greatest'
    (multiplicity_finite_of_degree_pos_of_monic
    (show (0 : with_bot ℕ) < degree (X - C a),
      by rw degree_X_sub_C; exact dec_trivial) (monic_X_sub_C _) hp)
    (nat.lt_succ_self _) (dvd_of_mul_right_eq _ this)
end

end multiplicity
end comm_ring

end polynomial
