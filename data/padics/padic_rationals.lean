/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis

Define the p-adic numbers (rationals) ℚ_p as the completion of ℚ wrt the p-adic norm.
Show that the p-adic norm extends to ℚ_p, that ℚ is embedded in ℚ_p, and that ℚ_p is complete
-/

import data.real.cau_seq_completion data.padics.padic_norm algebra.archimedean analysis.normed_space
noncomputable theory
local attribute [instance] classical.prop_decidable

open nat padic_val padic_norm cau_seq cau_seq.completion

@[reducible] def padic_seq {p : ℕ} (hp : prime p) := cau_seq _ (padic_norm hp)

namespace padic_seq

section
variables {p : ℕ} {hp : prime p}

lemma stationary {f : cau_seq ℚ (padic_norm hp)} (hf : ¬ f ≈ 0) :
      ∃ N, ∀ m n, m ≥ N → n ≥ N → padic_norm hp (f n) = padic_norm hp (f m) :=
have ∃ ε > 0, ∃ N1, ∀ j ≥ N1, ε ≤ padic_norm hp (f j),
  from cau_seq.abv_pos_of_not_lim_zero $ not_lim_zero_of_not_congr_zero hf,
let ⟨ε, hε, N1, hN1⟩ := this,
    ⟨N2, hN2⟩ := cau_seq.cauchy₂ f hε in
⟨ max N1 N2,
  λ n m hn hm,
  have padic_norm hp (f n - f m) < ε, from hN2 _ _ (max_le_iff.1 hn).2 (max_le_iff.1 hm).2,
  have padic_norm hp (f n - f m) < padic_norm hp (f n),
    from lt_of_lt_of_le this $ hN1 _ (max_le_iff.1 hn).1,
  have  padic_norm hp (f n - f m) < max (padic_norm hp (f n)) (padic_norm hp (f m)),
    from lt_max_iff.2 (or.inl this),
  begin
    by_contradiction hne,
    rw ←padic_norm.neg hp (f m) at hne,
    have hnam := add_eq_max_of_ne hp hne,
    rw [padic_norm.neg, max_comm] at hnam,
    rw ←hnam at this,
    apply _root_.lt_irrefl _ (by simp at this; exact this)
  end ⟩

def stationary_point {f : padic_seq hp} (hf : ¬ f ≈ 0) : ℕ :=
classical.some $ stationary hf

lemma stationary_point_spec {f : padic_seq hp} (hf : ¬ f ≈ 0) :
      ∀ {m n}, m ≥ stationary_point hf → n ≥ stationary_point hf →
                 padic_norm hp (f n) = padic_norm hp (f m) :=
classical.some_spec $ stationary hf

def norm (f : padic_seq hp) : ℚ :=
if hf : f ≈ 0 then 0
else padic_norm hp (f (stationary_point hf))

lemma norm_zero_iff (f : padic_seq hp) : f.norm = 0 ↔ f ≈ 0 :=
begin
  constructor,
  { intro h,
    by_contradiction hf,
    unfold norm at h, split_ifs at h,
    apply hf,
    intros ε hε,
    existsi stationary_point hf,
    intros j hj,
    have heq := stationary_point_spec hf (le_refl _) hj,
    simpa [h, heq] },
  { intro h,
    simp [norm, h] }
end

end

section embedding
open cau_seq
variables {p : ℕ} {hp : prime p}

lemma equiv_zero_of_val_eq_of_equiv_zero {f g : padic_seq hp}
      (h : ∀ k, padic_norm hp (f k) = padic_norm hp (g k)) (hf : f ≈ 0) : g ≈ 0 :=
λ ε hε, let ⟨i, hi⟩ := hf _ hε in
⟨i, λ j hj, by simpa [h] using hi _ hj⟩

lemma norm_nonzero_of_not_equiv_zero {f : padic_seq hp} (hf : ¬ f ≈ 0) :
      f.norm ≠ 0 :=
hf ∘ f.norm_zero_iff.1

lemma norm_eq_norm_app_of_nonzero {f : padic_seq hp} (hf : ¬ f ≈ 0) :
      ∃ k, f.norm = padic_norm hp k ∧ k ≠ 0 :=
have heq : f.norm = padic_norm hp (f $ stationary_point hf), by simp [norm, hf],
⟨f $ stationary_point hf, heq,
  λ h, norm_nonzero_of_not_equiv_zero hf (by simpa [h] using heq)⟩

lemma not_lim_zero_const_of_nonzero {q : ℚ} (hq : q ≠ 0) : ¬ lim_zero (const (padic_norm hp) q) :=
λ h', hq $ const_lim_zero.1 h'

lemma not_equiv_zero_const_of_nonzero {q : ℚ} (hq : q ≠ 0) : ¬ (const (padic_norm hp) q) ≈ 0 :=
λ h : lim_zero (const (padic_norm hp) q - 0), not_lim_zero_const_of_nonzero hq $ by simpa using h

lemma norm_nonneg (f : padic_seq hp) : f.norm ≥ 0 :=
if hf : f ≈ 0 then by simp [hf, norm]
else by simp [norm, hf, padic_norm.nonneg]

lemma norm_mul (f g : padic_seq hp) : (f * g).norm = f.norm * g.norm :=
if hf : f ≈ 0 then
  have hg : f * g ≈ 0, from mul_equiv_zero' _ hf,
  by simp [hf, hg, norm]
else if hg : g ≈ 0 then
  have hf : f * g ≈ 0, from mul_equiv_zero _ hg,
  by simp [hf, hg, norm]
else
  have hfg : ¬ f * g ≈ 0, by apply mul_not_equiv_zero; assumption,
  let i := max (stationary_point hfg) (max (stationary_point hf) (stationary_point hg)) in
  have hpnfg : padic_norm hp ((f * g) (stationary_point hfg)) = padic_norm hp ((f * g) i),
  { apply stationary_point_spec hfg,
    apply le_max_left,
    apply le_refl },
  have hpnf : padic_norm hp (f (stationary_point hf)) = padic_norm hp (f i),
  { apply stationary_point_spec hf,
    apply ge_trans,
    apply le_max_right,
    apply le_max_left,
    apply le_refl },
  have hpng : padic_norm hp (g (stationary_point hg)) = padic_norm hp (g i),
  { apply stationary_point_spec hg,
    apply ge_trans,
    apply le_max_right,
    apply le_max_right,
    apply le_refl },
  begin
    unfold norm,
    split_ifs,
    rw [hpnfg, hpnf, hpng],
    apply padic_norm.mul hp
  end

lemma eq_zero_iff_equiv_zero (f : padic_seq hp) : mk f = 0 ↔ f ≈ 0 :=
mk_eq

lemma ne_zero_iff_nequiv_zero (f : padic_seq hp) : mk f ≠ 0 ↔ ¬ f ≈ 0 :=
not_iff_not.2 (eq_zero_iff_equiv_zero _)

lemma norm_const (q : ℚ) : norm (const (padic_norm hp) q) = padic_norm hp q :=
if hq : q = 0 then
  have (const (padic_norm hp) q) ≈ 0,
    by simp [hq]; apply setoid.refl (const (padic_norm hp) 0),
  by subst hq; simp [norm, this]
else
  have ¬ (const (padic_norm hp) q) ≈ 0, from not_equiv_zero_const_of_nonzero hq,
  by simp [norm, this]

lemma norm_image (a : padic_seq hp) (ha : ¬ a ≈ 0) :
      (∃ (n : ℤ), a.norm = fpow ↑p (-n)) :=
let ⟨k, hk, hk'⟩ := norm_eq_norm_app_of_nonzero ha in
by simpa [hk] using padic_norm.image hp hk'

lemma norm_one : norm (1 : padic_seq hp) = 1 :=
have h1 : ¬ (1 : padic_seq hp) ≈ 0, from one_not_equiv_zero _,
by simp [h1, norm, hp.gt_one]

private lemma norm_eq_of_equiv_aux {f g : padic_seq hp} (hf : ¬ f ≈ 0) (hg : ¬ g ≈ 0) (hfg : f ≈ g)
        (h : padic_norm hp (f (stationary_point hf)) ≠ padic_norm hp (g (stationary_point hg)))
        (hgt : padic_norm hp (f (stationary_point hf)) > padic_norm hp (g (stationary_point hg))) :
        false :=
begin
  have hpn : padic_norm hp (f (stationary_point hf)) - padic_norm hp (g (stationary_point hg)) > 0,
    from sub_pos_of_lt hgt,
  cases hfg _ hpn with N hN,
  let i := max N (max (stationary_point hf) (stationary_point hg)),
  have hfi : padic_norm hp (f (stationary_point hf)) = padic_norm hp (f i),
  { apply stationary_point_spec hf,
    { apply le_trans,
      apply le_max_left,
      tactic.rotate_left 1,
      apply le_max_right },
    { apply le_refl } },
  have hgi : padic_norm hp (g (stationary_point hg)) = padic_norm hp (g i),
  { apply stationary_point_spec hg,
    { apply le_trans,
      apply le_max_right,
      tactic.rotate_left 1,
      apply le_max_right },
    { apply le_refl } },
  have hi : i ≥ N, from le_max_left _ _,
  have hN' := hN _ hi,
  simp only [hfi, hgi] at hN',
  have hpne : padic_norm hp (f i) ≠ padic_norm hp (-(g i)),
    by rwa [hfi, hgi, ←padic_norm.neg hp (g i)] at h,
  let hpnem := add_eq_max_of_ne hp hpne,
  have hpeq : padic_norm hp ((f - g) i) = max (padic_norm hp (f i)) (padic_norm hp (g i)),
  { rwa padic_norm.neg at hpnem },
  have hfigi : padic_norm hp (g i) < padic_norm hp (f i),
  { rwa [hfi, hgi] at hgt },
  rw [hpeq, max_eq_left_of_lt hfigi] at hN',
  have : padic_norm hp (f i) < padic_norm hp (f i),
  { apply lt_of_lt_of_le hN', apply sub_le_self, apply padic_norm.nonneg },
  exact lt_irrefl _ this
end

private lemma norm_eq_of_equiv {f g : padic_seq hp} (hf : ¬ f ≈ 0) (hg : ¬ g ≈ 0) (hfg : f ≈ g) :
      padic_norm hp (f (stationary_point hf)) = padic_norm hp (g (stationary_point hg)) :=
begin
  by_contradiction h,
  cases (decidable.em (padic_norm hp (f (stationary_point hf)) >
          padic_norm hp (g (stationary_point hg))))
      with hgt hngt,
  { exact norm_eq_of_equiv_aux hf hg hfg h hgt },
  { apply norm_eq_of_equiv_aux hg hf (setoid.symm hfg) (ne.symm h),
    apply lt_of_le_of_ne,
    apply le_of_not_gt hngt,
    apply h }
end

theorem norm_equiv {f g : padic_seq hp} (hfg : f ≈ g) : f.norm = g.norm :=
if hf : f ≈ 0 then
  have hg : g ≈ 0, from setoid.trans (setoid.symm hfg) hf,
  by simp [norm, hf, hg]
else have hg : ¬ g ≈ 0, from hf ∘ setoid.trans hfg,
by unfold norm; split_ifs; exact norm_eq_of_equiv hf hg hfg

private lemma norm_nonarchimedean_aux {f g : padic_seq hp}
        (hfg : ¬ f + g ≈ 0) (hf : ¬ f ≈ 0) (hg : ¬ g ≈ 0) :
        (f + g).norm ≤ max (f.norm) (g.norm) :=
let i := max (stationary_point hfg) (max (stationary_point hf) (stationary_point hg)) in
have hpnfg : padic_norm hp ((f + g) (stationary_point hfg)) = padic_norm hp ((f + g) i),
{ apply stationary_point_spec hfg,
  apply le_max_left,
  apply le_refl },
have hpnf : padic_norm hp (f (stationary_point hf)) = padic_norm hp (f i),
{ apply stationary_point_spec hf,
  apply ge_trans,
  apply le_max_right,
  apply le_max_left,
  apply le_refl },
have hpng : padic_norm hp (g (stationary_point hg)) = padic_norm hp (g i),
{ apply stationary_point_spec hg,
  apply ge_trans,
  apply le_max_right,
  apply le_max_right,
  apply le_refl },
begin
  unfold norm, split_ifs,
  rw [hpnfg, hpnf, hpng],
  apply padic_norm.nonarchimedean
end

theorem norm_nonarchimedean (f g : padic_seq hp) :
      (f + g).norm ≤ max (f.norm) (g.norm) :=
if hfg : f + g ≈ 0 then
  have 0 ≤ max (f.norm) (g.norm), from le_max_left_of_le (norm_nonneg _),
  by simpa [hfg, norm]
else if hf : f ≈ 0 then
  have hfg' : f + g ≈ g,
  { change lim_zero (f - 0) at hf,
    show lim_zero (f + g - g), by simpa using hf },
  have hcfg : (f + g).norm = g.norm, from norm_equiv hfg',
  have hcl : f.norm = 0, from (norm_zero_iff f).2 hf,
  have max (f.norm) (g.norm) = g.norm,
    by rw hcl; exact max_eq_right (norm_nonneg _),
  by rw [this, hcfg]
else if hg : g ≈ 0 then
  have hfg' : f + g ≈ f,
  { change lim_zero (g - 0) at hg,
    show lim_zero (f + g - f), by  simpa [add_sub_cancel'] using hg },
  have hcfg : (f + g).norm = f.norm, from norm_equiv hfg',
  have hcl : g.norm = 0, from (norm_zero_iff g).2 hg,
  have max (f.norm) (g.norm) = f.norm,
    by rw hcl; exact max_eq_left (norm_nonneg _),
  by rw [this, hcfg]
else norm_nonarchimedean_aux hfg hf hg

lemma norm_eq {f g : padic_seq hp} (h : ∀ k, padic_norm hp (f k) = padic_norm hp (g k)) :
      f.norm = g.norm :=
if hf : f ≈ 0 then
  have hg : g ≈ 0, from equiv_zero_of_val_eq_of_equiv_zero h hf,
  by simp [hf, hg, norm]
else
  have hg : ¬ g ≈ 0, from λ hg, hf $ equiv_zero_of_val_eq_of_equiv_zero (by simp [h]) hg,
  begin
    simp [hg, hf, norm],
    let i := max (stationary_point hf) (stationary_point hg),
    have hpf : padic_norm hp (f (stationary_point hf)) = padic_norm hp (f i),
    { apply stationary_point_spec, apply le_max_left, apply le_refl },
    have hpg : padic_norm hp (g (stationary_point hg)) = padic_norm hp (g i),
    { apply stationary_point_spec, apply le_max_right, apply le_refl },
    rw [hpf, hpg, h]
  end

lemma norm_neg (a : padic_seq hp) : (-a).norm = a.norm :=
norm_eq $ by simp

end embedding
end padic_seq

def padic {p : ℕ} (hp : prime p) := @cau_seq.completion.Cauchy _ _ _ _ (padic_norm hp) _
notation `ℚ_[` hp `]` := padic hp

namespace padic

section completion
variables {p : ℕ} {hp : prime p}

instance discrete_field : discrete_field (padic hp) :=
cau_seq.completion.discrete_field

def mk : padic_seq hp → ℚ_[hp] := quotient.mk
end completion

section completion
variables {p : ℕ} (hp : prime p)

lemma mk_eq {f g : padic_seq hp} : mk f = mk g ↔ f ≈ g := quotient.eq

def of_rat : ℚ → ℚ_[hp] := cau_seq.completion.of_rat

@[simp] lemma of_rat_add : ∀ (x y : ℚ), of_rat hp (x + y) = of_rat hp x + of_rat hp y :=
cau_seq.completion.of_rat_add

@[simp] lemma of_rat_neg : ∀ (x : ℚ), of_rat hp (-x) = -of_rat hp x :=
cau_seq.completion.of_rat_neg

@[simp] lemma of_rat_mul : ∀ (x y : ℚ), of_rat hp (x * y) = of_rat hp x * of_rat hp y :=
cau_seq.completion.of_rat_mul

@[simp] lemma of_rat_sub : ∀ (x y : ℚ), of_rat hp (x - y) = of_rat hp x - of_rat hp y :=
cau_seq.completion.of_rat_sub

@[simp] lemma of_rat_div : ∀ (x y : ℚ), of_rat hp (x / y) = of_rat hp x / of_rat hp y :=
cau_seq.completion.of_rat_div

@[simp] lemma of_rat_one : of_rat hp 1 = 1 := rfl

@[simp] lemma of_rat_zero : of_rat hp 0 = 0 := rfl

@[simp] lemma cast_eq_of_rat_of_nat (n : ℕ) : (↑n : ℚ_[hp]) = of_rat hp n :=
begin
  induction n with n ih,
  { refl },
  { simp, ring, congr, apply ih }
end

@[simp] lemma cast_eq_of_rat_of_int (n : ℤ) : (↑n : ℚ_[hp]) = of_rat hp n :=
by induction n; simp

lemma cast_eq_of_rat : ∀ (q : ℚ), (↑q : ℚ_[hp]) = of_rat hp q
| ⟨n, d, h1, h2⟩ :=
  show ↑n / ↑d = _, from
    have (⟨n, d, h1, h2⟩ : ℚ) = rat.mk n d, from rat.num_denom _,
    by simp [this, rat.mk_eq_div, of_rat_div]

lemma const_equiv {q r : ℚ} : const (padic_norm hp) q ≈ const (padic_norm hp) r ↔ q = r :=
⟨ λ heq : lim_zero (const (padic_norm hp) (q - r)),
    eq_of_sub_eq_zero $ const_lim_zero.1 heq,
  λ heq, by rw heq; apply setoid.refl _ ⟩

lemma of_rat_eq {q r : ℚ} : of_rat hp q = of_rat hp r ↔ q = r :=
⟨(const_equiv hp).1 ∘ quotient.eq.1, λ h, by rw h⟩

instance : char_zero ℚ_[hp] :=
⟨ λ m n, suffices of_rat hp ↑m = of_rat hp ↑n ↔ m = n, by simpa using this,
    by simp [of_rat_eq] ⟩

end completion
end padic

def padic_norm_e {p : ℕ} {hp : prime p} : ℚ_[hp] → ℚ :=
quotient.lift padic_seq.norm $ @padic_seq.norm_equiv _ _

namespace padic_norm_e
section embedding
open padic_seq
variables {p : ℕ} {hp : prime p}

lemma defn (f : padic_seq hp) {ε : ℚ} (hε : ε > 0) :
      ∃ N, ∀ i ≥ N, padic_norm_e (⟦f⟧ - f i) < ε :=
begin
  simp only [padic.cast_eq_of_rat],
  change ∃ N, ∀ i ≥ N, (f - const _ (f i)).norm < ε,
  by_contradiction h,
  cases cauchy₂ f hε with N hN,
  have : ∀ N, ∃ i ≥ N, (f - const _ (f i)).norm ≥ ε,
    by simpa [not_forall] using h,
  rcases this N with ⟨i, hi, hge⟩,
  have hne : ¬ (f - const (padic_norm hp) (f i)) ≈ 0,
  { intro h, unfold padic_seq.norm at hge; split_ifs at hge, exact not_lt_of_ge hge hε },
  unfold padic_seq.norm at hge; split_ifs at hge,
  apply not_le_of_gt _ hge,
  cases decidable.em ((stationary_point hne) ≥ N) with hgen hngen,
  { apply hN; assumption },
  { have := stationary_point_spec hne (le_refl _) (le_of_not_le hngen),
    rw ←this,
    apply hN,
    apply le_refl, assumption }
end

protected lemma nonneg (q : ℚ_[hp]) : padic_norm_e q ≥ 0 :=
quotient.induction_on q $ norm_nonneg

lemma zero_def : (0 : ℚ_[hp]) = ⟦0⟧ := rfl

lemma zero_iff (q : ℚ_[hp]) : padic_norm_e q = 0 ↔ q = 0 :=
quotient.induction_on q $
  by simpa only [zero_def, quotient.eq] using norm_zero_iff

@[simp] protected lemma zero : padic_norm_e (0 : ℚ_[hp]) = 0 :=
(zero_iff _).2 rfl

@[simp] protected lemma one' : padic_norm_e (1 : ℚ_[hp]) = 1 :=
norm_one

@[simp] protected lemma neg (q : ℚ_[hp]) : padic_norm_e (-q) = padic_norm_e q :=
quotient.induction_on q $ norm_neg

theorem nonarchimedean' (q r : ℚ_[hp]) :
      padic_norm_e (q + r) ≤ max (padic_norm_e q) (padic_norm_e r) :=
quotient.induction_on₂ q r $ norm_nonarchimedean

lemma triangle_ineq (x y z : ℚ_[hp]) :
  padic_norm_e (x - z) ≤ padic_norm_e (x - y) + padic_norm_e (y - z) :=
calc padic_norm_e (x - z) = padic_norm_e ((x - y) + (y - z)) : by rw sub_add_sub_cancel
  ... ≤ max (padic_norm_e (x - y)) (padic_norm_e (y - z)) : padic_norm_e.nonarchimedean' _ _
  ... ≤ padic_norm_e (x - y) + padic_norm_e (y - z) :
    max_le_add_of_nonneg (padic_norm_e.nonneg _) (padic_norm_e.nonneg _)

protected lemma add (q r : ℚ_[hp]) :
      padic_norm_e (q + r) ≤ (padic_norm_e q) + (padic_norm_e r) :=
calc
  padic_norm_e (q + r) ≤ max (padic_norm_e q) (padic_norm_e r) : nonarchimedean' _ _
                      ... ≤ (padic_norm_e q) + (padic_norm_e r) :
                              max_le_add_of_nonneg (padic_norm_e.nonneg _) (padic_norm_e.nonneg _)

protected lemma mul' (q r : ℚ_[hp]) :
      padic_norm_e (q * r) = (padic_norm_e q) * (padic_norm_e r) :=
quotient.induction_on₂ q r $ norm_mul

instance : is_absolute_value (@padic_norm_e _ hp) :=
{ abv_nonneg := padic_norm_e.nonneg,
  abv_eq_zero := zero_iff,
  abv_add := padic_norm_e.add,
  abv_mul := padic_norm_e.mul' }

@[simp] lemma eq_padic_norm' (q : ℚ) : padic_norm_e (padic.of_rat hp q) = padic_norm hp q :=
norm_const _

protected theorem image' {q : ℚ_[hp]} : q ≠ 0 → ∃ n : ℤ, padic_norm_e q = fpow p (-n) :=
quotient.induction_on q $ λ f hf,
  have ¬ f ≈ 0, from (ne_zero_iff_nequiv_zero f).1 hf,
  norm_image f this

lemma sub_rev (q r : ℚ_[hp]) : padic_norm_e (q - r) = padic_norm_e (r - q) :=
by rw ←(padic_norm_e.neg); simp

end embedding
end padic_norm_e

namespace padic

section complete
open padic_seq padic

theorem rat_dense' {p : ℕ} {hp : prime p} (q : ℚ_[hp]) {ε : ℚ} (hε : ε > 0) :
        ∃ r : ℚ, padic_norm_e (q - r) < ε :=
quotient.induction_on q $ λ q',
  have ∃ N, ∀ m n ≥ N, padic_norm hp (q' m - q' n) < ε, from cauchy₂ _ hε,
  let ⟨N, hN⟩ := this in
  ⟨q' N,
    begin
      simp only [padic.cast_eq_of_rat],
      change padic_seq.norm (q' - const _ (q' N)) < ε,
      cases decidable.em ((q' - const (padic_norm hp) (q' N)) ≈ 0) with heq hne',
      { simpa only [heq, padic_seq.norm, dif_pos] },
      { simp only [padic_seq.norm, dif_neg hne'],
        change padic_norm hp (q' _ - q' _) < ε,
        have := stationary_point_spec hne',
        cases decidable.em (N ≥ stationary_point hne') with hle hle,
        { have := eq.symm (this (le_refl _) hle),
          simp at this, simpa [this] },
        { apply hN,
          apply le_of_lt, apply lt_of_not_ge, apply hle, apply le_refl }}
    end⟩

variables {p : ℕ} {hp : prime p} (f : cau_seq _ (@padic_norm_e _ hp))
open classical

private lemma cast_succ_nat_pos (n : ℕ) : (↑(n + 1) : ℚ) > 0 :=
nat.cast_pos.2 $ succ_pos _

private lemma div_nat_pos (n : ℕ) : (1 / ((n + 1): ℚ)) > 0 :=
div_pos zero_lt_one (cast_succ_nat_pos _)

def lim_seq : ℕ → ℚ := λ n, classical.some (rat_dense' (f n) (div_nat_pos n))

lemma exi_rat_seq_conv :
      ∀ ε > 0, ∃ N, ∀ i ≥ N, padic_norm_e (f i - of_rat hp ((lim_seq f) i)) < ε :=
begin
  intros ε hε,
  existsi (ceil (1/ε)).nat_abs,
  intros i hi,
  let h := classical.some_spec (rat_dense' (f i) (div_nat_pos i)),
  rw ←cast_eq_of_rat,
  apply lt_of_lt_of_le,
  apply h,
  apply div_le_of_le_mul,
  apply cast_succ_nat_pos,
  have hi' := int.of_nat_le_of_nat_of_le hi,
  have : ceil (1/ε) ≥ 0, from ceil_nonneg (le_of_lt (one_div_pos_of_pos hε)),
  rw int.of_nat_nat_abs_eq_of_nonneg (this) at hi',
  have hi'' := le_mul_of_div_le hε (ceil_le.1 hi'),
  rw right_distrib,
  apply le_add_of_le_of_nonneg,
  { apply hi'' },
  { apply le_of_lt,
    simpa }
end

lemma exi_rat_seq_conv_cauchy : is_cau_seq (padic_norm hp) (lim_seq f) :=
assume ε hε,
have hε3 : ε / 3 > 0, from div_pos hε (by norm_num),
let ⟨N, hN⟩ := exi_rat_seq_conv f _ hε3,
    ⟨N2, hN2⟩ := f.cauchy₂ hε3 in
begin
  existsi max N N2,
  intros j hj,
  rw [←padic_norm_e.eq_padic_norm', padic.of_rat_sub],
  suffices : padic_norm_e ((↑(lim_seq f j) - f (max N N2)) + (f (max N N2) - lim_seq f (max N N2))) < ε,
  { ring at this ⊢, simpa only [cast_eq_of_rat] },
  { apply lt_of_le_of_lt,
    { apply padic_norm_e.add },
    { have : (3 : ℚ) ≠ 0, by norm_num,
      have : ε = ε / 3 + ε / 3 + ε / 3,
      { apply eq_of_mul_eq_mul_left this, simp [left_distrib, mul_div_cancel' _ this ], ring },
      rw this,
      apply add_lt_add,
      { suffices : padic_norm_e ((↑(lim_seq f j) - f j) + (f j - f (max N N2))) < ε / 3 + ε / 3,
          by simpa,
        apply lt_of_le_of_lt,
        { apply padic_norm_e.add },
        { apply add_lt_add,
          { rw [padic_norm_e.sub_rev, cast_eq_of_rat], apply hN, apply le_of_max_le_left hj },
          { apply hN2, apply le_of_max_le_right hj, apply le_max_right } } },
      { rw cast_eq_of_rat, apply hN, apply le_max_left }}}
end

private def lim' : padic_seq hp := ⟨_, exi_rat_seq_conv_cauchy f⟩

private def lim : ℚ_[hp] := ⟦lim' f⟧

theorem complete' :
        ∃ q : ℚ_[hp], ∀ ε > 0, ∃ N, ∀ i ≥ N, padic_norm_e (q - f i) < ε :=
⟨ lim f,
  λ ε hε,
  let ⟨N, hN⟩ := exi_rat_seq_conv f _ (show ε / 2 > 0, from div_pos hε (by norm_num)),
      ⟨N2, hN2⟩ := padic_norm_e.defn (lim' f) (show ε / 2 > 0, from div_pos hε (by norm_num)) in
  begin
    existsi max N N2,
    intros i hi,
    suffices : padic_norm_e ((lim f - lim' f i) + (lim' f i - f i)) < ε,
    { ring at this; exact this },
    { apply lt_of_le_of_lt,
      { apply padic_norm_e.add },
      { have : (2 : ℚ) ≠ 0, by norm_num,
        have : ε = ε / 2 + ε / 2, by rw ←(add_self_div_two ε); simp,
        rw this,
        apply add_lt_add,
        { apply hN2, apply le_of_max_le_right hi },
        { rw [padic_norm_e.sub_rev, cast_eq_of_rat], apply hN, apply le_of_max_le_left hi } } }
  end ⟩

end complete

section normed_space
variables {p : ℕ} (hp : p.prime)

instance : has_dist ℚ_[hp] := ⟨λ x y, padic_norm_e (x - y)⟩

instance : metric_space ℚ_[hp] :=
{ dist_self := by simp [dist],
  dist_comm := λ x y, by unfold dist; rw ←padic_norm_e.neg (x - y); simp,
  dist_triangle :=
    begin
      intros, unfold dist,
      rw ←rat.cast_add,
      apply rat.cast_le.2,
      apply padic_norm_e.triangle_ineq
    end,
  eq_of_dist_eq_zero :=
    begin
      unfold dist, intros _ _ h,
      apply eq_of_sub_eq_zero,
      apply (padic_norm_e.zero_iff _).1,
      simpa using h
    end }

instance : has_norm ℚ_[hp] := ⟨λ x, padic_norm_e x⟩

instance : normed_field ℚ_[hp] :=
{ dist_eq := λ _ _, rfl,
  norm_mul := by simp [has_norm.norm, padic_norm_e.mul'] }

instance : is_absolute_value (λ a : ℚ_[hp], ∥a∥) :=
{ abv_nonneg := norm_nonneg,
  abv_eq_zero := norm_eq_zero,
  abv_add := norm_triangle,
  abv_mul := by simp [has_norm.norm, padic_norm_e.mul'] }


theorem rat_dense {p : ℕ} {hp : prime p} (q : ℚ_[hp]) {ε : ℝ} (hε : ε > 0) :
        ∃ r : ℚ, ∥q - r∥ < ε :=
let ⟨ε', hε'l, hε'r⟩ := exists_rat_btwn hε,
    ⟨r, hr⟩ := rat_dense' q (by simpa using hε'l)  in
⟨r, lt.trans (by simpa [has_norm.norm] using hr) hε'r⟩

end normed_space
end padic

namespace padic_norm_e
section normed_space
variables {p : ℕ} {hp : p.prime}

@[simp] protected lemma mul (q r : ℚ_[hp]) : ∥q * r∥ = ∥q∥ * ∥r∥ :=
by simp [has_norm.norm, padic_norm_e.mul']

protected lemma is_norm (q : ℚ_[hp]) : ↑(padic_norm_e q) = ∥q∥ := rfl

theorem nonarchimedean (q r : ℚ_[hp]) : ∥q + r∥ ≤ max (∥q∥) (∥r∥) :=
begin
  unfold has_norm.norm, rw ←rat.cast_max, apply rat.cast_le.2, apply nonarchimedean'
end

@[simp] lemma eq_padic_norm (q : ℚ) : ∥padic.of_rat hp q∥ = padic_norm hp q :=
by unfold has_norm.norm; congr; apply padic_seq.norm_const

protected theorem image {q : ℚ_[hp]} : q ≠ 0 → ∃ n : ℤ, ∥q∥ = ↑(fpow (↑p : ℚ) (-n)) :=
quotient.induction_on q $ λ f hf,
  have ¬ f ≈ 0, from (padic_seq.ne_zero_iff_nequiv_zero f).1 hf,
  let ⟨n, hn⟩ := padic_seq.norm_image f this in
  ⟨n, congr_arg rat.cast hn⟩

protected lemma is_rat (q : ℚ_[hp]) : ∃ q' : ℚ, ∥q∥ = ↑q' :=
if h : q = 0 then ⟨0, by simp [h]⟩
else let ⟨n, hn⟩ := padic_norm_e.image h in ⟨_, hn⟩

def rat_norm (q : ℚ_[hp]) : ℚ := classical.some (padic_norm_e.is_rat q)

lemma eq_rat_norm (q : ℚ_[hp]) : ∥q∥ = rat_norm q := classical.some_spec (padic_norm_e.is_rat q)

theorem norm_rat_le_one : ∀ {q : ℚ} (hq : ¬ p ∣ q.denom), ∥(q : ℚ_[hp])∥ ≤ 1
| ⟨n, d, hn, hd⟩ := λ hq : ¬ p ∣ d,
  if hnz : n = 0 then
    have (⟨n, d, hn, hd⟩ : ℚ) = 0, from rat.zero_of_num_zero hnz,
      by simp [this, padic.cast_eq_of_rat, zero_le_one]
  else
    have hnz' : {rat . num := n, denom := d, pos := hn, cop := hd} ≠ 0,
      from mt rat.zero_iff_num_zero.1 hnz,
    have fpow (p : ℚ) (-↑(padic_val p n)) ≤ 1,
      from fpow_le_one_of_nonpos
             (show (↑p : ℚ) ≥ ↑(1: ℕ), from le_of_lt (nat.cast_lt.2 hp.gt_one))
             (neg_nonpos_of_nonneg (int.coe_nat_nonneg _)),
    have (↑(fpow (p : ℚ) (-↑(padic_val p n))) : ℝ) ≤ (1 : ℚ), from rat.cast_le.2 this,
    by simpa [padic.cast_eq_of_rat, hnz', padic_norm, padic_val_rat,
              padic_val_eq_zero_of_not_dvd' hq] using this

end normed_space
end padic_norm_e

namespace padic
variables {p : ℕ} {hp : p.prime}

protected theorem complete (f : cau_seq ℚ_[hp] (λ a, ∥a∥)):
        ∃ q : ℚ_[hp], ∀ ε > 0, ∃ N, ∀ i ≥ N, ∥q - f i∥ < ε :=
let f' : cau_seq ℚ_[hp] padic_norm_e :=
  ⟨λ n, f n, λ ε hε,
    let ⟨N, hN⟩ := is_cau f ↑ε (rat.cast_pos.2 hε) in ⟨N, λ j hj, rat.cast_lt.1 (hN _ hj)⟩⟩ in
let ⟨q, hq⟩ := padic.complete' f' in
⟨ q, λ ε hε,
  let ⟨ε', hε'l, hε'r⟩ := exists_rat_btwn hε,
      ⟨N, hN⟩ := hq _ (by simpa using hε'l) in
  ⟨N, λ i hi, lt.trans (rat.cast_lt.2 (hN _ hi)) hε'r ⟩⟩

def cau_seq_lim (f : cau_seq ℚ_[hp] (λ a, ∥a∥)) : ℚ_[hp] :=
classical.some (padic.complete f)

lemma cau_seq_lim_spec (f : cau_seq ℚ_[hp] (λ a, ∥a∥)) :
      ∀ ε > 0, ∃ N, ∀ i ≥ N, ∥(cau_seq_lim f) - f i∥ < ε :=
classical.some_spec (padic.complete f)

lemma padic_norm_e_lim_le {f : cau_seq ℚ_[hp] (λ a, ∥a∥)} {a : ℝ} (ha : a > 0)
      (hf : ∀ i, ∥f i∥ ≤ a) : ∥cau_seq_lim f∥ ≤ a :=
let ⟨N, hN⟩ := cau_seq_lim_spec f _ ha in
calc ∥cau_seq_lim f∥ = ∥cau_seq_lim f - f N + f N∥ : by simp
                ... ≤ max (∥cau_seq_lim f - f N∥) (∥f N∥) : padic_norm_e.nonarchimedean _ _
                ... ≤ a : max_le (le_of_lt (hN _ (le_refl _))) (hf _)

end padic