import data.complex.basic

namespace cau_seq

theorem const_inv {α β : Type*} [discrete_field β] [discrete_linear_ordered_field α] {abv : β → α}
  [is_absolute_value abv] {x : β} (hx : x ≠ 0) :
  const abv (x⁻¹) = inv (const abv x) (by rwa const_lim_zero) :=
 ext (assume n, by simp[inv_apply, const_apply])

end cau_seq

namespace complex
open cau_seq

lemma re_const_equiv_of_const_equiv {f : ℕ → ℂ} (hf : is_cau_seq abs f) (z : ℂ) :
    cau_seq.const abs z ≈ ⟨f, hf⟩ → cau_seq.const _root_.abs z.re ≈ ⟨(λ (n : ℕ), (f n).re),
    complex.is_cau_seq_re ⟨f,hf⟩⟩ := begin
  assume h,assume ε ε0,cases h ε ε0 with i hi,existsi i,assume j ji,
  replace hi := hi j ji, simp at *, rw [←complex.neg_re,←complex.add_re],
  exact lt_of_le_of_lt (complex.abs_re_le_abs _) hi,
end

lemma im_const_equiv_of_const_equiv {f : ℕ → ℂ} (hf : is_cau_seq abs f) (z : ℂ) :
    cau_seq.const abs z ≈ ⟨f, hf⟩ → cau_seq.const _root_.abs z.im ≈ ⟨(λ (n : ℕ), (f n).im),
    complex.is_cau_seq_im ⟨f,hf⟩⟩ := begin
  assume h,assume ε ε0,cases h ε ε0 with i hi,existsi i,assume j ji,
  replace hi := hi j ji, simp at *, rw [←complex.neg_im,←complex.add_im],
  exact lt_of_le_of_lt (complex.abs_im_le_abs _) hi,
end

lemma eq_lim_of_const_equiv {f : cau_seq ℂ abs}  {z: ℂ} :
    cau_seq.const complex.abs z ≈ f → z = complex.lim f := begin
  assume h,
  unfold complex.lim,cases z with zre zim,simp,
  split, have := real.equiv_lim ⟨(λ (n : ℕ), (f.1 n).re), complex.is_cau_seq_re f⟩,
  rw ←cau_seq.const_equiv,simp at this,
  have hf := complex.re_const_equiv_of_const_equiv f.2 {re := zre, im := zim} h,simp at hf,
  exact setoid.trans hf this,
  have := real.equiv_lim ⟨(λ (n : ℕ), (f.1 n).im), complex.is_cau_seq_im f⟩,
  rw ←cau_seq.const_equiv,simp at this,
  have hf := complex.im_const_equiv_of_const_equiv f.2 {re := zre, im := zim} h,simp at hf,
  exact setoid.trans hf this,
end

lemma lim_eq_of_equiv_const {f : cau_seq ℂ complex.abs} {x : ℂ} (h : f ≈ cau_seq.const complex.abs x) : lim f = x :=
(eq_lim_of_const_equiv $ setoid.symm h).symm

lemma lim_eq_lim_of_equiv {f g : cau_seq ℂ complex.abs} (h : f ≈ g) : lim f = lim g :=
lim_eq_of_equiv_const $ setoid.trans h $ equiv_lim g

@[simp] lemma lim_const (x : ℂ) : lim (const abs x) = x :=
lim_eq_of_equiv_const $ setoid.refl _

lemma lim_add (f g : cau_seq ℂ complex.abs) : lim f + lim g = lim ⇑(f + g) :=
eq_lim_of_const_equiv $ show lim_zero (const complex.abs (lim ⇑f + lim ⇑g) - (f + g)),
  by rw [const_add, add_sub_comm];
  exact add_lim_zero (setoid.symm (equiv_lim f)) (setoid.symm (equiv_lim g))

lemma lim_mul_lim (f g : cau_seq ℂ complex.abs) : lim f * lim g = lim ⇑(f * g) :=
eq_lim_of_const_equiv $ show lim_zero (const complex.abs (lim ⇑f * lim ⇑g) - f * g),
  from have h : const complex.abs (lim ⇑f * lim ⇑g) - f * g = g * (const complex.abs (lim f) - f)
      + const complex.abs (lim f) * (const complex.abs (lim g) - g) :=
    by simp [mul_sub, mul_comm, const_mul, mul_add],
  by rw h; exact add_lim_zero (mul_lim_zero _ (setoid.symm (equiv_lim f)))
      (mul_lim_zero _ (setoid.symm (equiv_lim g)))

lemma lim_mul (f : cau_seq ℂ complex.abs) (x : ℂ) : lim f * x = lim ⇑(f * const complex.abs x) :=
by rw [← lim_mul_lim, lim_const]

lemma lim_neg (f : cau_seq ℂ complex.abs) : lim ⇑(-f) = -lim f :=
lim_eq_of_equiv_const (show lim_zero (-f - const complex.abs (-lim ⇑f)),
  by rw [const_neg, sub_neg_eq_add, add_comm];
  exact setoid.symm (equiv_lim f))

lemma lim_eq_zero_iff (f : cau_seq ℂ complex.abs) : lim f = 0 ↔ lim_zero f :=
⟨assume h,
  by have hf := equiv_lim f;
  rw h at hf;
  exact (lim_zero_congr hf).mpr (const_lim_zero.mpr rfl),
assume h,
  have h₁ : f = (f - const complex.abs (0 : ℂ)) := cau_seq.ext (λ n, by simp [sub_apply, const_apply]),
  by rw h₁ at h; exact lim_eq_of_equiv_const h ⟩

lemma lim_inv {f : cau_seq ℂ complex.abs} (hf : ¬ lim_zero f) : lim ⇑(inv f hf) = (lim f)⁻¹ :=
have hl : lim f ≠ 0 := by rwa ← lim_eq_zero_iff at hf,
lim_eq_of_equiv_const $ show lim_zero (inv f hf - const abs (lim ⇑f)⁻¹),
  from have h₁ : ∀ (g f : cau_seq ℂ abs) (hf : ¬ lim_zero f), lim_zero (g - f * inv f hf * g) :=
    λ g f hf, by rw [← one_mul g, ← mul_assoc, ← sub_mul, mul_one, mul_comm, mul_comm f];
    exact mul_lim_zero _ (setoid.symm (cau_seq.inv_mul_cancel _)),
  have h₂ : lim_zero ((inv f hf - const abs (lim ⇑f)⁻¹) - (const abs (lim f) - f) *
      (inv f hf * const abs (lim ⇑f)⁻¹)) :=
    by rw [sub_mul, ← sub_add, sub_sub, sub_add_eq_sub_sub, sub_right_comm, sub_add];
    exact show lim_zero (inv f hf - const abs (lim ⇑f) * (inv f hf * const abs (lim ⇑f)⁻¹)
      - (const abs (lim ⇑f)⁻¹ - f * (inv f hf * const abs (lim ⇑f)⁻¹))),
    from sub_lim_zero
      (by rw [← mul_assoc, mul_right_comm, cau_seq.const_inv hl]; exact h₁ _ _ _)
      (by rw [← mul_assoc]; exact h₁ _ _ _),
  (lim_zero_congr h₂).mpr $ by rw mul_comm; exact mul_lim_zero _ (setoid.symm (equiv_lim f))

end complex