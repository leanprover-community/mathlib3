/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp

Convex sets and functions on real vector spaces
-/

import analysis.normed_space.basic
import data.complex.basic
import data.set.intervals
import tactic.interactive
import tactic.linarith
import linear_algebra.basic
import ring_theory.algebra

local attribute [instance] classical.prop_decidable

open set

section vector_space
variables {α : Type*} {β : Type*} {ι : Sort _}
  [add_comm_group α] [vector_space ℝ α] [add_comm_group β] [vector_space ℝ β]
  (A : set α) (B : set α) (x : α)

/-- Convexity of sets -/
def convex (A : set α) :=
∀ (x y : α) (a b : ℝ), x ∈ A → y ∈ A → 0 ≤ a → 0 ≤ b → a + b = 1 →
  a • x + b • y ∈ A

/-- Alternative definition of set convexity -/
lemma convex_iff:
  convex A ↔ ∀ {x y : α} {θ : ℝ},
    x ∈ A → y ∈ A → 0 ≤ θ → θ ≤ 1 → θ • x + (1 - θ) • y ∈ A :=
⟨begin
  assume h x y θ hx hy hθ₁ hθ₂,
  have hθ₂ : 0 ≤ 1 - θ, by linarith,
  exact (h _ _ _ _ hx hy hθ₁ hθ₂ (by linarith))
end,
begin
  assume h x y a b hx hy ha hb hab,
  have ha' : a ≤ 1, by linarith,
  have hb' : b = 1 - a, by linarith,
  rw hb',
  exact h hx hy ha ha'
end⟩

/-- Another alternative definition of set convexity -/
lemma convex_iff_div:
  convex A ↔ ∀ {x y : α} {a : ℝ} {b : ℝ},
    x ∈ A → y ∈ A → 0 ≤ a → 0 ≤ b → 0 < a + b → (a/(a+b)) • x + (b/(a+b)) • y ∈ A :=
⟨begin
  assume h x y a b hx hy ha hb hab,
  apply h _ _ _ _ hx hy,
  have ha', from mul_le_mul_of_nonneg_left ha (le_of_lt (inv_pos hab)),
  rwa [mul_zero, ←div_eq_inv_mul] at ha',
  have hb', from mul_le_mul_of_nonneg_left hb (le_of_lt (inv_pos hab)),
  rwa [mul_zero, ←div_eq_inv_mul] at hb',
  rw [←add_div],
  exact div_self (ne_of_lt hab).symm
end,
begin
  assume h x y a b hx hy ha hb hab,
  have h', from h hx hy ha hb,
  rw [hab, div_one, div_one] at h',
  exact h' zero_lt_one
end⟩

local notation `I` := (Icc 0 1 : set ℝ)

/-- Segments in a vector space -/
def segment (x y : α) := {z : α | ∃ l : ℝ, l ∈ I ∧ z - x = l•(y-x)}
local notation `[`x `, ` y `]` := segment x y

lemma left_mem_segment (x y : α) : x ∈ [x, y] := ⟨0, ⟨⟨le_refl _, zero_le_one⟩, by simp⟩⟩

lemma right_mem_segment (x y : α) : y ∈ [x, y] := ⟨1, ⟨⟨zero_le_one, le_refl _⟩, by simp⟩⟩

lemma mem_segment_iff {x y z : α} : z ∈ [x, y] ↔ ∃ l ∈ I, z = x + l•(y - x) :=
by split; rintro ⟨l, l_in, H⟩; use [l, l_in]; try { rw sub_eq_iff_eq_add at H }; rw H; abel

lemma mem_segment_iff' {x y z : α} : z ∈ [x, y] ↔ ∃ l ∈ I, z = ((1:ℝ)-l)•x + l•y :=
begin
  split; rintro ⟨l, l_in, H⟩; use [l, l_in]; try { rw sub_eq_iff_eq_add at H }; rw H;
  simp only [smul_sub, sub_smul, one_smul]; abel,
end

lemma segment_symm (x y : α) : [x, y] = [y, x] :=
begin
  ext z,
  rw [mem_segment_iff', mem_segment_iff'],
  split,
  all_goals {
    rintro ⟨l, ⟨hl₀, hl₁⟩, h⟩,
    use (1-l),
    split,
    split; linarith,
    rw [h]; simp },
end

lemma segment_eq_Icc {a b : ℝ} (h : a ≤ b) : [a, b] = Icc a b :=
begin
  ext z,
  rw mem_segment_iff,
  split,
  { rintro ⟨l, ⟨hl₀, hl₁⟩, H⟩,
    rw smul_eq_mul at H,
    have hba : 0 ≤ b - a, by linarith,
    split ; rw H,
    { have := mul_le_mul (le_refl l) hba (le_refl _) hl₀,
      simpa using this, },
    { have := mul_le_mul hl₁ (le_refl (b-a)) hba zero_le_one,
      rw one_mul at this,
      apply le_trans (add_le_add (le_refl a) this),
      convert le_refl _,
      show b = a + (b-a), by ring } },
  { rintro ⟨hza, hzb⟩,
    by_cases hba : b-a = 0,
    { use [(0:ℝ), ⟨le_refl 0, zero_le_one⟩],
      rw zero_smul, linarith },
    { have : (z-a)/(b-a) ∈ I,
      { change b -a ≠ 0 at hba,
        have : 0 < b - a, from lt_of_le_of_ne (by linarith) hba.symm,
        split,
        apply div_nonneg ; linarith,
        apply (div_le_iff this).2,
        simp, convert hzb },
      use [(z-a)/(b-a), this],
      rw [smul_eq_mul, div_mul_cancel],
      ring,
      exact hba } }
end

lemma segment_translate (a b c x : α) (hx : x ∈ [b, c]) : a + x ∈ [a + b, a + c] :=
begin
  refine exists.elim hx (λθ hθ, ⟨θ, ⟨hθ.1, _⟩⟩),
  simp only [smul_sub, smul_add] at *,
  simp [smul_add, (add_eq_of_eq_sub hθ.2.symm).symm]
end

lemma segment_translate_image (a b c: α) : (λx, a + x) '' [b, c] = [a + b, a + c] :=
begin
  apply subset.antisymm,
  { intros z hz,
    apply exists.elim hz,
    intros x hx,
    convert segment_translate a b c x _,
    { exact hx.2.symm },
    { exact hx.1 } },
  { intros z hz,
    apply exists.elim hz,
    intros θ hθ,
    use z - a,
    apply and.intro,
    { convert segment_translate (-a) (a + b) (a + c) z hz; simp },
    { simp only [add_sub_cancel'_right] } }
end

lemma image_Icc_zero_one_eq_segment {x y : α} :
   (λ (t : ℝ), x + t • (y - x)) '' Icc 0 1 = segment x y :=
begin
  apply subset.antisymm,
  { intros z hz,
    apply exists.elim hz,
    intros x hx,
    use x,
    simp [hx.2.symm, hx.1] },
  { intros z hz,
    apply exists.elim hz,
    intros a ha,
    exact ⟨a, ha.1, add_eq_of_eq_sub' (eq.symm ha.2)⟩ }
end

/-- Alternative defintion of set convexity using segments -/
lemma convex_segment_iff : convex A ↔ ∀ x y ∈ A, [x, y] ⊆ A :=
begin
  apply iff.intro,
  { intros hA x y hx hy z hseg,
    apply exists.elim hseg,
    intros l hl,
    have hz : z = l • y + (1-l) • x,
    { rw sub_eq_iff_eq_add.1 hl.2,
      rw [smul_sub, sub_smul, one_smul],
      simp },
    rw hz,
    apply (convex_iff A).1 hA hy hx hl.1.1 hl.1.2 },
  { intros hA,
    rw convex_iff,
    intros x y θ hx hy hθ₀ hθ₁,
    apply hA y x hy hx,
    use θ,
    apply and.intro,
    { exact and.intro hθ₀ hθ₁ },
    { simp only [smul_sub, sub_smul, one_smul],
      simp } }
end


/- Examples of convex sets -/

lemma convex_empty : convex (∅ : set α) :=  by finish

lemma convex_singleton (a : α) : convex ({a} : set α) :=
begin
  intros x y a b hx hy ha hb hab,
  rw [set.eq_of_mem_singleton hx, set.eq_of_mem_singleton hy, ←add_smul, hab],
  simp
end

lemma convex_univ : convex (set.univ : set α) := by finish

lemma convex_inter (hA: convex A) (hB: convex B) : convex (A ∩ B) :=
λ x y a b (hx : x ∈ A ∩ B) (hy : y ∈ A ∩ B) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1),
  ⟨hA _ _ _ _ hx.left hy.left ha hb hab, hB _ _ _ _ hx.right hy.right ha hb hab⟩

lemma convex_Inter {s: ι → set α} (h: ∀ i : ι, convex (s i)) : convex (Inter s) :=
begin
  intros x y a b hx hy ha hb hab,
  apply mem_Inter.2,
  exact λi, h i _ _ _ _ (mem_Inter.1 hx i) (mem_Inter.1 hy i) ha hb hab
end

lemma convex_prod {A : set α} {B : set β} (hA : convex A) (hB : convex B) :
  convex (set.prod A B) :=
begin
  intros x y a b hx hy ha hb hab,
  apply mem_prod.2,
  exact ⟨hA _ _ _ _ (mem_prod.1 hx).1 (mem_prod.1 hy).1 ha hb hab,
        hB _ _ _ _ (mem_prod.1 hx).2 (mem_prod.1 hy).2 ha hb hab⟩
end

lemma convex_linear_image (f : α → β) (hf : is_linear_map ℝ f) (hA : convex A) : convex (image f A) :=
begin
  intros x y a b hx hy ha hb hab,
  apply exists.elim hx,
  intros x' hx',
  apply exists.elim hy,
  intros y' hy',
  use a • x' + b • y',
  split,
  { apply hA _ _ _ _ hx'.1 hy'.1 ha hb hab },
  { simp [hx',hy',hf.add,hf.smul] }
end

lemma convex_linear_image' (f : α →ₗ[ℝ] β) (hA : convex A) : convex (image f A) :=
convex_linear_image A f.to_fun (linear_map.is_linear f) hA

lemma convex_linear_preimage (A : set β) (f : α → β) (hf : is_linear_map ℝ f) (hA : convex A) :
  convex (preimage f A) :=
begin
  intros x y a b hx hy ha hb hab,
  simp [hf.add, hf.smul],
  exact hA (f x) (f y) a b hx hy ha hb hab
end

lemma convex_linear_preimage' (A : set β) (f : α →ₗ[ℝ] β) (hA : convex A) :
  convex (preimage f A) :=
convex_linear_preimage A f.to_fun (linear_map.is_linear f) hA

lemma convex_neg : convex A → convex ((λ z, -z) '' A) :=
convex_linear_image _ _ is_linear_map.is_linear_map_neg

lemma convex_neg_preimage : convex A → convex ((λ z, -z) ⁻¹' A) :=
convex_linear_preimage _ _ is_linear_map.is_linear_map_neg

lemma convex_smul (c : ℝ) : convex A → convex ((λ z, c • z) '' A) :=
convex_linear_image _ _ (is_linear_map.is_linear_map_smul c)

lemma convex_smul_preimage (c : ℝ) : convex A → convex ((λ z, c • z) ⁻¹' A) :=
convex_linear_preimage _ _ (is_linear_map.is_linear_map_smul _)

lemma convex_add (hA : convex A) (hB : convex B) :
  convex ((λx : α × α, x.1 + x.2) '' (set.prod A B)) :=
begin
  apply convex_linear_image (set.prod A B) (λx : α × α, x.1 + x.2) is_linear_map.is_linear_map_add,
  exact convex_prod hA hB
end

lemma convex_sub (hA : convex A) (hB : convex B) :
  convex ((λx : α × α, x.1 - x.2) '' (set.prod A B)) :=
begin
  apply convex_linear_image (set.prod A B) (λx : α × α, x.1 - x.2) is_linear_map.is_linear_map_sub,
  exact convex_prod hA hB
end

lemma convex_translation (z : α) (hA : convex A) : convex ((λx, z + x) '' A) :=
begin
  have h : convex ((λ (x : α × α), x.fst + x.snd) '' set.prod (insert z ∅) A),
    from convex_add {z} A (convex_singleton z) hA,
  show convex ((λx, z + x) '' A),
  { rw [@insert_prod _ _ z ∅ A, set.empty_prod, set.union_empty, ←image_comp] at h,
    simp at h,
    exact h }
end

lemma convex_affinity (z : α) (c : ℝ) (hA : convex A) : convex ((λx, z + c • x) '' A) :=
begin
  have h : convex ((λ (x : α), z + x) '' ((λ (z : α), c • z) '' A)),
    from convex_translation _ z (convex_smul A c hA),
  show convex ((λx, z + c • x) '' A),
  { rw [←image_comp] at h,
    simp at h,
    exact h }
end

lemma convex_Iio (r : ℝ) : convex (Iio r) :=
begin
  intros x y a b hx hy ha hb hab,
  wlog h : x ≤ y using [x y a b, y x b a],
  exact le_total _ _,
  calc
    a * x + b * y ≤ a * y + b * y : add_le_add_right (mul_le_mul_of_nonneg_left h ha) _
    ...           = y             : by rw [←add_mul a b y, hab, one_mul]
    ... < r                       : hy
end

lemma convex_Iic (r : ℝ) : convex (Iic r) :=
begin
  intros x y a b hx hy ha hb hab,
  wlog h : x ≤ y using [x y a b, y x b a],
  exact le_total _ _,
  calc
    a * x + b * y ≤ a * y + b * y : add_le_add_right (mul_le_mul_of_nonneg_left h ha) _
    ...           = y             : by rw [←add_mul a b y, hab, one_mul]
    ... ≤ r                       : hy
end

lemma convex_Ioi (r : ℝ) : convex (Ioi r) :=
begin
  rw [← neg_neg r],
  rw (image_neg_Iio (-r)).symm,
  unfold convex,
  intros x y a b hx hy ha hb hab,
  exact convex_linear_image _ _ is_linear_map.is_linear_map_neg (convex_Iio (-r)) _ _ _ _ hx hy ha hb hab
end

lemma convex_Ici (r : ℝ) : convex (Ici r) :=
begin
  rw [← neg_neg r],
  rw (image_neg_Iic (-r)).symm,
  unfold convex,
  intros x y a b hx hy ha hb hab,
  exact convex_linear_image _ _ is_linear_map.is_linear_map_neg (convex_Iic (-r)) _ _ _ _ hx hy ha hb hab
end

lemma convex_Ioo (r : ℝ) (s : ℝ) : convex (Ioo r s) :=
convex_inter _ _ (convex_Ioi _) (convex_Iio _)

lemma convex_Ico (r : ℝ) (s : ℝ) : convex (Ico r s) :=
convex_inter _ _ (convex_Ici _) (convex_Iio _)

lemma convex_Ioc (r : ℝ) (s : ℝ) : convex (Ioc r s) :=
convex_inter _ _ (convex_Ioi _) (convex_Iic _)

lemma convex_Icc (r : ℝ) (s : ℝ) : convex (Icc r s) :=
convex_inter _ _ (convex_Ici _) (convex_Iic _)

lemma convex_segment (a b : α) : convex [a, b] :=
begin
  have : (λ (t : ℝ), a + t • (b - a)) = (λz : α, a + z) ∘ (λt:ℝ, t • (b - a)) := rfl,
  rw [← image_Icc_zero_one_eq_segment, this, image_comp],
  apply convex_translation _ _ (convex_linear_image _ _ _ (convex_Icc _ _)),
  exact is_linear_map.is_linear_map_smul' _
end

lemma convex_halfspace_lt (f : α → ℝ) (h : is_linear_map ℝ f) (r : ℝ) :
  convex {w | f w < r} :=
begin
  assume x y a b hx hy ha hb hab,
  simp,
  rw [is_linear_map.add ℝ f,  is_linear_map.smul f a,  is_linear_map.smul f b],
  apply convex_Iio _ _ _ _ _ hx hy ha hb hab
end

lemma convex_halfspace_le (f : α → ℝ) (h : is_linear_map ℝ f) (r : ℝ) :
  convex {w | f w ≤ r} :=
begin
  assume x y a b hx hy ha hb hab,
  simp,
  rw [is_linear_map.add ℝ f,  is_linear_map.smul f a,  is_linear_map.smul f b],
  apply convex_Iic _ _ _ _ _ hx hy ha hb hab
end

lemma convex_halfspace_gt (f : α → ℝ) (h : is_linear_map ℝ f) (r : ℝ) :
  convex {w | r < f w} :=
begin
  assume x y a b hx hy ha hb hab,
  simp,
  rw [is_linear_map.add ℝ f,  is_linear_map.smul f a,  is_linear_map.smul f b],
  apply convex_Ioi _ _ _ _ _ hx hy ha hb hab
end

lemma convex_halfspace_ge (f : α → ℝ) (h : is_linear_map ℝ f) (r : ℝ) :
  convex {w | r ≤ f w} :=
begin
  assume x y a b hx hy ha hb hab,
  simp,
  rw [is_linear_map.add ℝ f,  is_linear_map.smul f a,  is_linear_map.smul f b],
  apply convex_Ici _ _ _ _ _ hx hy ha hb hab
end

lemma convex_halfplane (f : α → ℝ) (h : is_linear_map ℝ f) (r : ℝ) :
  convex {w | f w = r} :=
begin
  assume x y a b hx hy ha hb hab,
  simp at *,
  rw [is_linear_map.add ℝ f,  is_linear_map.smul f a,  is_linear_map.smul f b],
  rw [hx, hy, (add_smul a b r).symm, hab, one_smul]
end

lemma convex_halfspace_re_lt (r : ℝ) : convex {c : ℂ | c.re < r} :=
convex_halfspace_lt _ (is_linear_map.mk complex.add_re complex.smul_re) _

lemma convex_halfspace_re_le (r : ℝ) : convex {c : ℂ | c.re ≤ r} :=
convex_halfspace_le _ (is_linear_map.mk complex.add_re complex.smul_re) _

lemma convex_halfspace_re_gt (r : ℝ) : convex {c : ℂ | r < c.re } :=
convex_halfspace_gt _ (is_linear_map.mk complex.add_re complex.smul_re) _

lemma convex_halfspace_re_lge (r : ℝ) : convex {c : ℂ | r ≤ c.re} :=
convex_halfspace_ge _ (is_linear_map.mk complex.add_re complex.smul_re) _

lemma convex_halfspace_im_lt (r : ℝ) : convex {c : ℂ | c.im < r} :=
convex_halfspace_lt _ (is_linear_map.mk complex.add_im complex.smul_im) _

lemma convex_halfspace_im_le (r : ℝ) : convex {c : ℂ | c.im ≤ r} :=
convex_halfspace_le _ (is_linear_map.mk complex.add_im complex.smul_im) _

lemma convex_halfspace_im_gt (r : ℝ) : convex {c : ℂ | r < c.im } :=
convex_halfspace_gt _ (is_linear_map.mk complex.add_im complex.smul_im) _

lemma convex_halfspace_im_lge (r : ℝ) : convex {c : ℂ | r ≤ c.im} :=
convex_halfspace_ge _ (is_linear_map.mk complex.add_im complex.smul_im) _

section submodule

open submodule

lemma convex_submodule (K : submodule ℝ α) : convex (↑K : set α) :=
by { repeat {intro}, refine add_mem _ (smul_mem _ _ _) (smul_mem _ _ _); assumption }

lemma convex_subspace (K : subspace ℝ α) : convex (↑K : set α) := convex_submodule K

end submodule

lemma convex_sum {γ : Type*} (hA : convex A) (z : γ → α) (s : finset γ) :
  ∀ a : γ → ℝ, s.sum a = 1 → (∀ i ∈ s, 0 ≤ a i) → (∀ i ∈ s, z i ∈ A) → s.sum (λi, a i • z i) ∈ A :=
begin
  refine finset.induction _ _ s,
  { intros _ h_sum,
    simp at h_sum,
    exact false.elim h_sum },
  { intros k s hks ih a h_sum ha hz,
    by_cases h_cases : s.sum a = 0,
    { have hak : a k = 1,
        by rwa [finset.sum_insert hks, h_cases, add_zero] at h_sum,
      have ha': ∀ i ∈ s, 0 ≤ a i,
        from λ i hi, ha i (finset.mem_insert_of_mem hi),
      have h_a0: ∀ i ∈ s, a i = 0,
        from (finset.sum_eq_zero_iff_of_nonneg ha').1 h_cases,
      have h_az0: ∀ i ∈ s, a i • z i = 0,
      { intros i hi,
        rw h_a0 i hi,
        exact zero_smul _ (z i) },
      show finset.sum (insert k s) (λ (i : γ), a i • z i) ∈ A,
      { rw [finset.sum_insert hks, hak, finset.sum_eq_zero h_az0],
        simp,
        exact hz k (finset.mem_insert_self k s) } },
    { have h_sum_nonneg : 0 ≤ s.sum a,
      { apply finset.sum_nonneg,
        intros i hi,
        apply ha _ (finset.mem_insert_of_mem hi) },
      have h_div_in_A: s.sum (λ (i : γ), ((s.sum a)⁻¹ * a i) • z i) ∈ A,
      { apply ih,
        { rw finset.mul_sum.symm,
          exact division_ring.inv_mul_cancel h_cases },
        { intros i hi,
          exact zero_le_mul (inv_nonneg.2 h_sum_nonneg) (ha i (finset.mem_insert_of_mem hi))},
        { intros i hi,
          exact hz i (finset.mem_insert_of_mem hi) } },
      have h_sum_in_A: a k • z k
        + finset.sum s a • finset.sum s (λ (i : γ), ((finset.sum s a)⁻¹ * a i) • z i) ∈ A,
      { apply hA,
        exact hz k (finset.mem_insert_self k s),
        exact h_div_in_A,
        exact ha k (finset.mem_insert_self k s),
        exact h_sum_nonneg,
        rw (finset.sum_insert hks).symm,
        exact h_sum },
      show finset.sum (insert k s) (λ (i : γ), a i • z i) ∈ A,
      { rw finset.sum_insert hks,
        rw finset.smul_sum at h_sum_in_A,
        simp [smul_smul, (mul_assoc (s.sum a) _ _).symm] at h_sum_in_A,
        conv
        begin
          congr,
          congr,
          skip,
          congr, skip, funext,
          rw (one_mul (a _)).symm,
          rw (field.mul_inv_cancel h_cases).symm,
        end,
        exact h_sum_in_A } } }
end

lemma convex_sum_iff :
  convex A ↔
    (∀ (s : finset α) (as : α → ℝ),
      s.sum as = 1 → (∀ i ∈ s, 0 ≤ as i) → (∀ x ∈ s, x ∈ A) → s.sum (λx, as x • x) ∈ A ) :=
begin
  apply iff.intro,
  { intros hA s as h_sum has hs,
    exact convex_sum A hA id s _ h_sum has hs },
  { intros h,
    intros x y a b hx hy ha hb hab,
    by_cases h_cases: x = y,
    { rw [h_cases, ←add_smul, hab, one_smul], exact hy },
    { let s := insert x (finset.singleton y),
      have h_sum_eq_add : finset.sum s (λ z, ite (x = z) a b • z) = a • x + b • y,
      { rw [finset.sum_insert (finset.not_mem_singleton.2 h_cases),
        finset.sum_singleton],
        simp [h_cases] },
      rw h_sum_eq_add.symm,
      apply h s,
      { rw [finset.sum_insert (finset.not_mem_singleton.2 h_cases),
        finset.sum_singleton],
        simp [h_cases],
        exact hab },
      { intros k hk,
        by_cases h_cases : x = k,
        { simp [h_cases], exact ha },
        { simp [h_cases], exact hb } },
      { intros z hz,
        apply or.elim (finset.mem_insert.1 hz),
        { intros h_eq, rw h_eq, exact hx },
        { intros h_eq, rw finset.mem_singleton at h_eq, rw h_eq, exact hy } } } }
end

variables (D: set α) (D': set α) (f : α → ℝ) (g : α → ℝ)

/-- Convexity of functions -/
def convex_on (f : α → ℝ) : Prop :=
  convex D ∧
  ∀ (x y : α) (a b : ℝ), x ∈ D → y ∈ D → 0 ≤ a → 0 ≤ b → a + b = 1 →
    f (a • x + b • y) ≤ a * f x + b * f y

lemma convex_on_iff :
  convex_on D f ↔ convex D ∧ ∀ {x y : α} {θ : ℝ},
    x ∈ D → y ∈ D → 0 ≤ θ → θ ≤ 1 → f (θ • x + (1 - θ) • y) ≤ θ * f x + (1 - θ) * f y :=
⟨begin
  intro h,
  apply and.intro h.1,
  intros x y θ hx hy hθ₁ hθ₂,
  have hθ₂: 0 ≤ 1 - θ, by linarith,
  exact (h.2 _ _ _ _ hx hy hθ₁ hθ₂ (by linarith))
end,
begin
  intro h,
  apply and.intro h.1,
  assume x y a b hx hy ha hb hab,
  have ha': a ≤ 1, by linarith,
  have hb': b = 1 - a, by linarith,
  rw hb',
  exact (h.2 hx hy ha ha')
end⟩

lemma convex_on_iff_div:
  convex_on D f ↔ convex D ∧ ∀ {x y : α} {a : ℝ} {b : ℝ},
    x ∈ D → y ∈ D → 0 ≤ a → 0 ≤ b → 0 < a + b →
    f ((a/(a+b)) • x + (b/(a+b)) • y) ≤ (a/(a+b)) * f x + (b/(a+b)) * f y :=
⟨begin
  intro h,
  apply and.intro h.1,
  intros x y a b hx hy ha hb hab,
  apply h.2 _ _ _ _ hx hy,
  have ha', from mul_le_mul_of_nonneg_left ha (le_of_lt (inv_pos hab)),
  rwa [mul_zero, ←div_eq_inv_mul] at ha',
  have hb', from mul_le_mul_of_nonneg_left hb (le_of_lt (inv_pos hab)),
  rwa [mul_zero, ←div_eq_inv_mul] at hb',
  rw [←add_div],
  exact div_self (ne_of_lt hab).symm
end,
begin
  intro h,
  apply and.intro h.1,
  intros x y a b hx hy ha hb hab,
  have h', from h.2 hx hy ha hb,
  rw [hab, div_one, div_one] at h',
  exact h' zero_lt_one
end⟩

lemma convex_on_sum {γ : Type} (s : finset γ) (z : γ → α) (hs : s ≠ ∅) :
  ∀ (a : γ → ℝ), convex_on D f → (∀ i ∈ s, 0 ≤ a i) → (∀ i ∈ s, z i ∈ D) → s.sum a = 1 →
  f (s.sum (λi, a i • z i)) ≤ s.sum (λi, a i • f (z i)) :=
begin
  refine finset.induction (by simp) _ s,
  intros k s hks ih a hf ha hz h_sum,
  by_cases h_cases : s.sum a = 0,
  { have hak : a k = 1,
      by rwa [finset.sum_insert hks, h_cases, add_zero] at h_sum,
    have ha': ∀ i ∈ s, 0 ≤ a i,
      from λ i hi, ha i (finset.mem_insert_of_mem hi),
    have h_a0: ∀ i ∈ s, a i = 0,
      from (finset.sum_eq_zero_iff_of_nonneg ha').1 h_cases,
    have h_az0: ∀ i ∈ s, a i • z i = 0,
    { intros i hi,
      rw h_a0 i hi,
      exact zero_smul _ _ },
    have h_afz0: ∀ i ∈ s, a i • f (z i) = 0,
    { intros i hi,
      rw h_a0 i hi,
      exact zero_smul _ _ },
    show f (finset.sum (insert k s) (λi, a i • z i)) ≤ finset.sum (insert k s) (λi, a i • f (z i)),
    { rw [finset.sum_insert hks, hak, finset.sum_eq_zero h_az0],
      rw [finset.sum_insert hks, hak, finset.sum_eq_zero h_afz0],
      simp } },
  { have h_sum_nonneg : 0 ≤ s.sum a ,
    { apply finset.sum_nonneg,
      intros i hi,
      apply ha _ (finset.mem_insert_of_mem hi) },
    have ih_div: f (s.sum (λ (i : γ), ((s.sum a)⁻¹ * a i) • z i))
                  ≤ s.sum (λ (i : γ), ((s.sum a)⁻¹ * a i) • f (z i)),
    { apply ih _ hf,
      { intros i hi,
        exact zero_le_mul (inv_nonneg.2 h_sum_nonneg) (ha i (finset.mem_insert_of_mem hi))},
      { intros i hi,
        exact hz i (finset.mem_insert_of_mem hi) },
      { rw finset.mul_sum.symm,
        exact division_ring.inv_mul_cancel h_cases } },
    have h_div_in_D: s.sum (λ (i : γ), ((s.sum a)⁻¹ * a i) • z i) ∈ D,
    { apply convex_sum _ hf.1,
      { rw finset.mul_sum.symm,
        exact division_ring.inv_mul_cancel h_cases },
      { intros i hi,
        exact zero_le_mul (inv_nonneg.2 h_sum_nonneg) (ha i (finset.mem_insert_of_mem hi))},
      { intros i hi,
        exact hz i (finset.mem_insert_of_mem hi) } },
    have hf': f (a k • z k     + s.sum a •    s.sum (λ (i : γ), ((finset.sum s a)⁻¹ * a i) • z i))
               ≤ a k • f (z k) + s.sum a • f (s.sum (λ (i : γ), ((finset.sum s a)⁻¹ * a i) • z i)),
    { apply hf.2,
      exact hz k (finset.mem_insert_self k s),
      exact h_div_in_D,
      exact ha k (finset.mem_insert_self k s),
      exact h_sum_nonneg,
      rw (finset.sum_insert hks).symm,
      exact h_sum },
    have ih_div': f (a k • z k     + s.sum a • s.sum (λ (i : γ), ((finset.sum s a)⁻¹ * a i) • z i))
                   ≤ a k • f (z k) + s.sum a • s.sum (λ (i : γ), ((finset.sum s a)⁻¹ * a i) • f (z i)),
      from trans hf' (add_le_add_left (mul_le_mul_of_nonneg_left ih_div h_sum_nonneg) _),
    show f (finset.sum (insert k s) (λ (i : γ), a i • z i))
          ≤ finset.sum (insert k s) (λ (i : γ), a i • f (z i)),
    { simp [finset.sum_insert hks],
      simp [finset.smul_sum] at ih_div',
      simp [smul_smul, (mul_assoc (s.sum a) _ _).symm] at ih_div',
      convert ih_div',
      repeat { apply funext,
        intro i,
        rw [field.mul_inv_cancel, one_mul],
        exact h_cases } } }
end

lemma convex_on_linorder [hα : linear_order α] (f : α → ℝ) : convex_on D f ↔
  convex D ∧ ∀ (x y : α) (a b : ℝ), x ∈ D → y ∈ D → x < y → a ≥ 0 → b ≥ 0 → a + b = 1 →
    f (a • x + b • y) ≤ a * f x + b * f y :=
begin
  apply iff.intro,
  { intro h,
    apply and.intro h.1,
    intros x y a b hx hy hxy ha hb hab,
    exact h.2 x y a b hx hy ha hb hab },
  { intro h,
    apply and.intro h.1,
    intros x y a b hx hy ha hb hab,
    wlog hxy : x<=y using [x y a b, y x b a],
    exact le_total _ _,
    apply or.elim (lt_or_eq_of_le hxy),
    { intros hxy, exact h.2 x y a b hx hy hxy ha hb hab },
    { intros hxy, rw [hxy,←add_smul, hab, one_smul,←add_mul,hab,one_mul] } }
end

lemma convex_on_subset (h_convex_on : convex_on D f) (h_subset : A ⊆ D) (h_convex : convex A) :
  convex_on A f :=
begin
  apply and.intro h_convex,
  intros x y a b hx hy,
  exact h_convex_on.2 x y a b (h_subset hx) (h_subset hy),
end

lemma convex_on_add (hf : convex_on D f) (hg : convex_on D g) : convex_on D (λx, f x + g x) :=
begin
  apply and.intro hf.1,
  intros x y a b hx hy ha hb hab,
  calc
    f (a • x + b • y) + g (a • x + b • y) ≤ (a * f x + b * f y) + (a * g x + b * g y)
      : add_le_add (hf.2 x y a b hx hy ha hb hab) (hg.2 x y a b hx hy ha hb hab)
    ... = a * f x + a * g x + b * f y + b * g y : by linarith
    ... = a * (f x + g x) + b * (f y + g y) : by simp [mul_add]
end

lemma convex_on_smul (c : ℝ) (hc : 0 ≤ c) (hf : convex_on D f) : convex_on D (λx, c * f x) :=
begin
  apply and.intro hf.1,
  intros x y a b hx hy ha hb hab,
  calc
    c * f (a • x + b • y) ≤ c * (a * f x + b * f y)
      : mul_le_mul_of_nonneg_left (hf.2 x y a b hx hy ha hb hab) hc
    ... = a * (c * f x) + b * (c * f y) : by rw mul_add; ac_refl
end

lemma convex_le_of_convex_on (hf : convex_on D f) (r : ℝ) : convex {x ∈ D | f x ≤ r} :=
begin
  intros x y a b hx hy ha hb hab,
  simp at *,
  apply and.intro,
  { exact hf.1 x y a b hx.1 hy.1 ha hb hab },
  { apply le_trans (hf.2 x y a b hx.1 hy.1 ha hb hab),
    wlog h_wlog : f x ≤ f y using [x y a b, y x b a],
    apply le_total,
    calc
      a * f x + b * f y ≤ a * f y + b * f y :
        add_le_add (mul_le_mul_of_nonneg_left h_wlog ha) (le_refl _)
      ... = (a + b) * f y : (add_mul _ _ _).symm
      ... ≤ r             : by rw [hab, one_mul]; exact hy.2 }
end

lemma convex_lt_of_convex_on (hf : convex_on D f) (r : ℝ) : convex {x ∈ D | f x < r} :=
begin
  intros x y a b hx hy ha hb hab,
  simp at *,
  apply and.intro,
  { exact hf.1 x y a b hx.1 hy.1 ha hb hab },
  { apply lt_of_le_of_lt (hf.2 x y a b hx.1 hy.1 ha hb hab),
    wlog h_wlog : f x ≤ f y using [x y a b, y x b a],
    apply le_total,
    calc
      a * f x + b * f y ≤ a * f y + b * f y :
        add_le_add (mul_le_mul_of_nonneg_left h_wlog ha) (le_refl _)
      ... = (a + b) * f y     : (add_mul _ _ _).symm
      ... < r                 : by rw [hab, one_mul]; exact hy.2 }
end

lemma le_on_interval_of_convex_on (x y : α) (a b : ℝ)
  (hf : convex_on D f) (hx : x ∈ D) (hy : y ∈ D) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
  f (a • x + b • y) ≤ max (f x) (f y) :=
calc
  f (a • x + b • y) ≤ a * f x + b * f y : hf.2 x y a b hx hy ha hb hab
  ... ≤ a * max (f x) (f y) + b * max (f x) (f y) :
    add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha) (mul_le_mul_of_nonneg_left (le_max_right _ _) hb)
  ... ≤ max (f x) (f y) : by rw [←add_mul, hab, one_mul]

end vector_space

section normed_space
variables {α : Type*} [normed_group α] [normed_space ℝ α]

lemma convex_on_dist  (z : α) (D : set α) (hD : convex D) :
  convex_on D (λz', dist z' z) :=
begin
  apply and.intro hD,
  intros x y a b hx hy ha hb hab,
  calc
    dist (a • x + b • y) z = ∥ (a • x + b • y) - (a + b) • z ∥ :
      by rw [hab, one_smul, normed_group.dist_eq]
    ... = ∥a • (x - z) + b • (y - z)∥ :
      by rw [add_smul, smul_sub, smul_sub]; simp
    ... ≤ ∥a • (x - z)∥ + ∥b • (y - z)∥ :
      norm_triangle (a • (x - z)) (b • (y - z))
    ... = a * dist x z + b * dist y z :
      by simp [norm_smul, normed_group.dist_eq, real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
end

lemma convex_ball (a : α) (r : ℝ) : convex (metric.ball a r) :=
by simpa using convex_lt_of_convex_on univ (λb, dist b a) (convex_on_dist _  _ convex_univ) r

lemma convex_closed_ball (a : α) (r : ℝ) : convex (metric.closed_ball a r) :=
by simpa using convex_le_of_convex_on univ (λb, dist b a) (convex_on_dist _  _ convex_univ) r

end normed_space
