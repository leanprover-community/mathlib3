/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import data.complex.basic tactic.ring
open is_absolute_value

namespace real

lemma lim_const {f : ℕ → ℝ} (hf : is_cau_seq abs f) (x : ℝ) : x = lim f ↔
cau_seq.const abs x ≈ ⟨f, hf⟩ := begin
  have := real.equiv_lim ⟨f, hf⟩,split,assume h,rw h,simp at this,exact setoid.symm this,
  assume h,have := setoid.trans h this,rw cau_seq.const_equiv at this,simp at this, exact this,
end

lemma real.lim_eq_lim_iff_equiv {f g : ℕ → ℝ} (hf : is_cau_seq abs f) 
    (hg : is_cau_seq abs g) : lim f = lim g ↔ @has_equiv.equiv 
    (cau_seq ℝ abs) _ ⟨f, hf⟩ ⟨g, hg⟩ := begin
  have h₁:= lim_const hg (lim f),
  have h₂:= lim_const hf (lim g),
  split,assume h, simp * at *,
  exact setoid.trans (setoid.symm h₂) h₁,
  assume h,rw h₁,have := real.equiv_lim ⟨f, hf⟩,simp at this,
  exact setoid.trans (setoid.symm this) h,
end

-- would be useful to have is_cau_seq abs f → is_cau_seq abs g → is_cau_seq abs (λ i, f i + g i)
-- in the library, similarly for mul
lemma lim_add {f g : ℕ → ℝ} (hf : is_cau_seq abs f) 
    (hg : is_cau_seq abs g) : lim f + lim g = 
    lim (λ x, f x + g x) := begin
  have : ∀ (ε : ℝ),
    ε > 0 → (∃ (i : ℕ), ∀ (j : ℕ), j ≥ i → abs (f j + (g j + (-real.lim f + -real.lim g))) < ε),
    {assume ε ε0,
    cases equiv_lim ⟨f, hf⟩ (ε / 2) (div_pos ε0 (by norm_num)) with fi hfi,simp at hfi,
    cases equiv_lim ⟨g, hg⟩ (ε / 2) (div_pos ε0 (by norm_num)) with gi hgi,simp at hgi,
    existsi max fi gi,
    assume j hj,rw [add_left_comm (g j),←add_assoc (f j)],
    refine lt_of_le_of_lt (abs_add _ _) _,rw ←add_halves ε,
    exact add_lt_add (hfi j (le_trans (le_max_left _ _) hj)) (hgi j (le_trans (le_max_right _ _) hj))},
  have cau : is_cau_seq abs (λ (x : ℕ), f x + g x), refine cau_seq.of_near _ (cau_seq.const abs (lim f + lim g)) _,simpa,
  rw real.lim_const,refine setoid.symm _,exact cau,assume ε ε0,simp,exact this ε ε0,
end

lemma lim_mul {f g : ℕ → ℝ} (hf : is_cau_seq abs f) 
    (hg : is_cau_seq abs g) : lim f * lim g = 
    lim (λ x, f x * g x) := begin
  have : ∀ (ε : ℝ),
    ε > 0 → (∃ (i : ℕ), ∀ (j : ℕ), j ≥ i → abs (f j * g j - (lim f * lim g)) < ε),
  { assume ε ε0,
    cases cau_seq.bounded ⟨_, hg⟩ with G hG,simp at hG,
    have G0 : 0 < G := lt_of_le_of_lt (abs_nonneg _) (hG 0),
    have Gf : 0 < G + abs (lim f) := add_pos_of_pos_of_nonneg G0 (abs_nonneg _),
    have Gε : 0 < ε / (G + abs (lim f)) := div_pos ε0 Gf,
    cases equiv_lim ⟨f, hf⟩ _ Gε with fi hfi, simp at hfi,
    cases equiv_lim ⟨g, hg⟩ _ Gε with gi hgi, simp at hgi,
    existsi max fi gi,assume j ji,
    rw (by simp[mul_add,add_mul];ring : f j * g j -lim f * lim g = (f j - lim f) * g j + lim f * (g j - lim g)),
    refine lt_of_le_of_lt (abs_add _ _) _,
    rw [abs_mul],
    suffices : abs (f j - lim f) * G + abs (lim f * (g j - lim g)) < ε,
      exact lt_of_le_of_lt (add_le_add (mul_le_mul_of_nonneg_left (le_of_lt (hG j)) (abs_nonneg _)) (le_refl _)) this,
    rw abs_mul,
    have : ε = ε * G / (G + abs (lim f)) + ε * abs (lim f) / (G + abs (lim f)) := by
      {rw [←add_div,←mul_add,mul_div_cancel _ (ne_of_lt Gf).symm]},
    rw this,
    refine add_lt_add_of_lt_of_le _ _,
    {rw [mul_comm,mul_comm ε,mul_div_assoc],
    exact mul_lt_mul_of_pos_left (hfi j (le_trans (le_max_left _ _) ji)) G0},
    rw [mul_comm ε,mul_div_assoc],
    refine mul_le_mul_of_nonneg_left (le_of_lt (hgi j (le_trans (le_max_right _ _) ji))) (abs_nonneg _)},
  have cau : is_cau_seq abs (λ (x : ℕ), f x * g x), refine cau_seq.of_near _ (cau_seq.const abs (lim f * lim g)) _,simpa,
  rw lim_const, refine setoid.symm _,exact cau,assume ε ε0,simp, exact this ε ε0,
end

end real
namespace complex
lemma re_const_equiv_of_const_equiv {f : ℕ → ℂ} (hf : is_cau_seq complex.abs f) (z : ℂ) :
    cau_seq.const complex.abs z ≈ ⟨f, hf⟩ → cau_seq.const _root_.abs z.re ≈ ⟨(λ (n : ℕ), (f n).re), 
    complex.is_cau_seq_re ⟨f,hf⟩⟩ := begin
  assume h,assume ε ε0,cases h ε ε0 with i hi,existsi i,assume j ji,
  replace hi := hi j ji, simp at *, rw [←complex.neg_re,←complex.add_re],
  exact lt_of_le_of_lt (complex.abs_re_le_abs _) hi,
end
#print re_const_equiv_of_const_equiv
lemma im_const_equiv_of_const_equiv {f : ℕ → ℂ} (hf : is_cau_seq complex.abs f) (z : ℂ) :
    cau_seq.const complex.abs z ≈ ⟨f, hf⟩ → cau_seq.const _root_.abs z.im ≈ ⟨(λ (n : ℕ), (f n).im),
    complex.is_cau_seq_im ⟨f,hf⟩⟩ := begin
  assume h,assume ε ε0,cases h ε ε0 with i hi,existsi i,assume j ji,
  replace hi := hi j ji, simp at *, rw [←complex.neg_im,←complex.add_im],
  exact lt_of_le_of_lt (complex.abs_im_le_abs _) hi,
end

lemma lim_const {f : ℕ → ℂ} (hf : is_cau_seq complex.abs f) (z : ℂ) : z = complex.lim f ↔ 
    cau_seq.const complex.abs z ≈ ⟨f, hf⟩ := begin
  split,have := complex.equiv_lim ⟨f, hf⟩,simp at this,
  assume h,rw h, exact setoid.symm this,assume h,
  unfold complex.lim,cases z with zre zim,simp,
  split, have := real.equiv_lim ⟨(λ (n : ℕ), (f n).re), complex.is_cau_seq_re ⟨f,hf⟩⟩,
  rw ←cau_seq.const_equiv,simp at this,
  have hf := complex.re_const_equiv_of_const_equiv hf {re := zre, im := zim} h,simp at hf,
  exact setoid.trans hf this,
  have := real.equiv_lim ⟨(λ (n : ℕ), (f n).im), complex.is_cau_seq_im ⟨f,hf⟩⟩,
  rw ←cau_seq.const_equiv,simp at this,
  have hf := complex.im_const_equiv_of_const_equiv hf {re := zre, im := zim} h,simp at hf,
  exact setoid.trans hf this,
end

lemma lim_eq_lim_iff_equiv {f g : ℕ → ℂ} (hf : is_cau_seq complex.abs f) 
    (hg : is_cau_seq complex.abs g) : complex.lim f = complex.lim g ↔ @has_equiv.equiv 
    (cau_seq ℂ complex.abs) _ ⟨f, hf⟩ ⟨g, hg⟩ := begin
  have h₁:= complex.lim_const hg (complex.lim f),
  have h₂:= complex.lim_const hf (complex.lim g),
  split,assume h, simp * at *,
  exact setoid.trans (setoid.symm h₂) h₁,
  assume h,rw h₁,have := complex.equiv_lim ⟨f, hf⟩,simp at this,
  exact setoid.trans (setoid.symm this) h,
end
open complex
lemma lim_add {f g : ℕ → ℂ} (hf : is_cau_seq complex.abs f) 
    (hg : is_cau_seq complex.abs g) : complex.lim f + complex.lim g = 
    complex.lim (λ x, f x + g x) := begin
  have : ∀ (ε : ℝ),
    ε > 0 → (∃ (i : ℕ), ∀ (j : ℕ), j ≥ i → complex.abs (f j + (g j + (-complex.lim f + -complex.lim g))) < ε) := by
    {assume ε ε0,
    cases complex.equiv_lim ⟨f, hf⟩ (ε / 2) (div_pos ε0 (by norm_num)) with fi hfi,simp at hfi,
    cases complex.equiv_lim ⟨g, hg⟩ (ε / 2) (div_pos ε0 (by norm_num)) with gi hgi,simp at hgi,
    existsi max fi gi,
    assume j hj,rw [add_left_comm (g j),←add_assoc (f j)],
    refine lt_of_le_of_lt (complex.abs_add _ _) _,rw ←add_halves ε,
    exact add_lt_add (hfi j (le_trans (le_max_left _ _) hj)) (hgi j (le_trans (le_max_right _ _) hj))},
  have cau : is_cau_seq complex.abs (λ (x : ℕ), f x + g x), refine cau_seq.of_near _ (cau_seq.const complex.abs (lim f + lim g)) _,simpa,
  rw lim_const,refine setoid.symm _,exact cau,assume ε ε0,simp,exact this ε ε0,
end

lemma lim_mul {f g : ℕ → ℂ} (hf : is_cau_seq complex.abs f) 
    (hg : is_cau_seq complex.abs g) : lim f * lim g = lim (λ x, f x * g x) := begin
  have : ∀ (ε : ℝ),
    ε > 0 → (∃ (i : ℕ), ∀ (j : ℕ), j ≥ i → complex.abs (f j * g j - (complex.lim f * complex.lim g)) < ε),
  { assume ε ε0,
    cases cau_seq.bounded ⟨_, hg⟩ with G hG,simp at hG,
    have G0 : 0 < G := lt_of_le_of_lt (complex.abs_nonneg _) (hG 0),
    have Gf : 0 < G + complex.abs (complex.lim f) := add_pos_of_pos_of_nonneg G0 (complex.abs_nonneg _),
    have Gε : 0 < ε / (G + complex.abs (complex.lim f)) := div_pos ε0 Gf,
    cases equiv_lim ⟨f, hf⟩ _ Gε with fi hfi, simp at hfi,
    cases equiv_lim ⟨g, hg⟩ _ Gε with gi hgi, simp at hgi,
    existsi max fi gi,assume j ji,
    rw (by simp[mul_add,add_mul];ring : f j * g j -lim f * lim g = (f j - lim f) * g j + lim f * (g j - lim g)),
    refine lt_of_le_of_lt (complex.abs_add _ _) _,
    rw [complex.abs_mul],
    suffices : complex.abs (f j - lim f) * G + complex.abs (lim f * (g j - lim g)) < ε,
      exact lt_of_le_of_lt (add_le_add (mul_le_mul_of_nonneg_left (le_of_lt (hG j)) (abs_nonneg _)) (le_refl _)) this,
    rw complex.abs_mul,
    have : ε = ε * G / (G + abs (lim f)) + ε * abs (lim f) / (G + abs (lim f)) := by
      {rw [←add_div,←mul_add,mul_div_cancel _ (ne_of_lt Gf).symm]},
    rw this,
    refine add_lt_add_of_lt_of_le _ _,
    {rw [mul_comm,mul_comm ε,mul_div_assoc],
    exact mul_lt_mul_of_pos_left (hfi j (le_trans (le_max_left _ _) ji)) G0},
    rw [mul_comm ε,mul_div_assoc],
    refine mul_le_mul_of_nonneg_left (le_of_lt (hgi j (le_trans (le_max_right _ _) ji))) (abs_nonneg _)},
  have cau : is_cau_seq complex.abs (λ (x : ℕ), f x * g x), refine cau_seq.of_near _ (cau_seq.const abs (lim f * lim g)) _,simpa,
  rw lim_const, refine setoid.symm _,exact cau,assume ε ε0,simp, exact this ε ε0,
end

end complex
