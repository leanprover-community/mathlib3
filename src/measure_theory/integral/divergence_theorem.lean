/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.box_integral.divergence_theorem
import analysis.box_integral.integrability
import measure_theory.integral.interval_integral

/-!
# Divergence theorem for Bochner integral

In this file we prove the Divergence theorem for Bochner integral on a box in
`ℝⁿ⁺¹ = fin (n + 1) → ℝ`. More precisely, we prove the following theorem.

Let `E` be a complete normed space with second countably topology. If `f : ℝⁿ⁺¹ → Eⁿ⁺¹` is
differentiable on a rectangular box `[a, b] : set ℝⁿ⁺¹`, `a ≤ b`, with derivative
`f' : ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ℝ] Eⁿ⁺¹` and the divergence `λ x, ∑ i, f' x eᵢ i` is integrable on `[a, b]`,
where `eᵢ = pi.single i 1` is the `i`-th basis vector, then its integral is equal to the sum of
integrals of `f` over the faces of `[a, b]`, taken with appropriate signs. Moreover, the same is
true if the function is not differentiable but continuous at countably many points of `[a, b]`.

Once we prove the general theorem, we deduce corollaries for functions `ℝ → E` and pairs of
functions `(ℝ × ℝ) → E`.

## Notations

We use the following local notation to make the statement more readable. Note that the documentation
website shows the actual terms, not those abbreviated using local notations.

* `ℝⁿ`, `ℝⁿ⁺¹`, `Eⁿ⁺¹`: `fin n → ℝ`, `fin (n + 1) → ℝ`, `fin (n + 1) → E`;
* `face i`: the `i`-th face of the box `[a, b]` as a closed segment in `ℝⁿ`, namely `[a ∘
  fin.succ_above i, b ∘ fin.succ_above i]`;
* `e i` : `i`-th basis vector `pi.single i 1`;
* `front_face i`, `back_face i`: embeddings `ℝⁿ → ℝⁿ⁺¹` corresponding to the front face
  `{x | x i = b i}` and back face `{x | x i = a i}` of the box `[a, b]`, respectively.
  They are given by `fin.insert_nth i (b i)` and `fin.insert_nth i (a i)`.

## TODO

* Add a version that assumes existence and integrability of partial derivatives.

## Tags

divergence theorem, Bochner integral
-/

open set finset topological_space function box_integral measure_theory filter
open_locale big_operators classical topological_space interval

universes u

namespace measure_theory

variables {E : Type u} [normed_group E] [normed_space ℝ E] [measurable_space E] [borel_space E]
  [second_countable_topology E] [complete_space E]

section
variables {n : ℕ}

local notation `ℝⁿ` := fin n → ℝ
local notation `ℝⁿ⁺¹` := fin (n + 1) → ℝ
local notation `Eⁿ⁺¹` := fin (n + 1) → E
local notation `e` i := pi.single i 1

section

variables (a b : ℝⁿ⁺¹)

local notation `face` i := set.Icc (a ∘ fin.succ_above i) (b ∘ fin.succ_above i)
local notation `front_face` i:2000 := fin.insert_nth i (b i)
local notation `back_face` i:2000 := fin.insert_nth i (a i)

lemma integral_divergence_of_has_fderiv_within_at_off_countable_aux (hlt : ∀ i, a i < b i)
  (f : ℝⁿ⁺¹ → Eⁿ⁺¹) (f' : ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ℝ] Eⁿ⁺¹) (s : set ℝⁿ⁺¹) (hs : countable s)
  (Hc : continuous_on f (Icc a b))
  (Hd : ∀ x ∈ Icc a b \ s, has_fderiv_within_at f (f' x) (Icc a b) x)
  (Hi : integrable_on (λ x, ∑ i, f' x (e i) i) (Icc a b)) :
  ∫ x in Icc a b, ∑ i, f' x (e i) i =
    ∑ i : fin (n + 1),
      ((∫ x in face i, f (front_face i x) i) - ∫ x in face i, f (back_face i x) i) :=
begin
  obtain ⟨I, rfl, rfl⟩ : ∃ I : box_integral.box (fin (n + 1)), I.lower = a ∧ I.upper = b,
    from ⟨⟨a, b, hlt⟩, rfl, rfl⟩,
  simp only [volume_pi, ← set_integral_congr_set_ae measure.univ_pi_Ioc_ae_eq_Icc],
  simp only [← box.coe_eq_pi, ← box.face_lower, ← box.face_upper],
  have A := ((Hi.mono_set box.coe_subset_Icc).has_box_integral ⊥ rfl),
  have B := has_integral_bot_divergence_of_forall_has_deriv_within_at I f f' (s ∩ I.Icc)
    (hs.mono (inter_subset_left _ _)) (λ x hx, Hc _ hx.2)
    (λ x hx, Hd _ ⟨hx.1, λ h, hx.2 ⟨h, hx.1⟩⟩),
  rw continuous_on_pi at Hc,
  refine (A.unique B).trans (sum_congr rfl $ λ i hi, _),
  refine congr_arg2 has_sub.sub _ _,
  { have := box.continuous_on_face_Icc (Hc i) (set.right_mem_Icc.2 (I.lower_le_upper i)),
    have := (this.integrable_on_compact (box.is_compact_Icc _)).mono_set box.coe_subset_Icc,
    exact (this.has_box_integral ⊥ rfl).integral_eq, apply_instance },
  { have := box.continuous_on_face_Icc (Hc i) (set.left_mem_Icc.2 (I.lower_le_upper i)),
    have := (this.integrable_on_compact (box.is_compact_Icc _)).mono_set box.coe_subset_Icc,
    exact (this.has_box_integral ⊥ rfl).integral_eq, apply_instance }
end

lemma integral_divergence_of_has_fderiv_within_at_off_countable (hle : a ≤ b) (f : ℝⁿ⁺¹ → Eⁿ⁺¹)
  (f' : ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ℝ] Eⁿ⁺¹) (s : set ℝⁿ⁺¹) (hs : countable s) (Hc : continuous_on f (Icc a b))
  (Hd : ∀ x ∈ set.pi univ (λ i, Ioo (a i) (b i)) \ s, has_fderiv_at f (f' x) x)
  (Hi : integrable_on (λ x, ∑ i, f' x (e i) i) (Icc a b)) :
  ∫ x in Icc a b, ∑ i, f' x (e i) i =
    ∑ i : fin (n + 1),
      ((∫ x in face i, f (front_face i x) i) - ∫ x in face i, f (back_face i x) i) :=
begin
  rcases em (∃ i, a i = b i) with ⟨i, hi⟩|hne,
  { /- First we sort out the trivial case `∃ i, a i = b i`. -/
    simp only [volume_pi, ← set_integral_congr_set_ae measure.univ_pi_Ioc_ae_eq_Icc],
    have hi' : Ioc (a i) (b i) = ∅ := Ioc_eq_empty hi.not_lt,
    have : pi set.univ (λ j, Ioc (a j) (b j)) = ∅, from univ_pi_eq_empty hi',
    rw [this, integral_empty, sum_eq_zero],
    rintro j -,
    rcases eq_or_ne i j with rfl|hne,
    { simp [hi] },
    { rcases fin.exists_succ_above_eq hne with ⟨i, rfl⟩,
      have : pi set.univ (λ k : fin n, Ioc (a $ j.succ_above k) (b $ j.succ_above k)) = ∅,
        from univ_pi_eq_empty hi',
      rw [this, integral_empty, integral_empty, sub_self] } },
  { have hlt : ∀ i, a i < b i, from λ i, (hle i).lt_of_ne (λ hi, hne ⟨i, hi⟩),
    -- Consider and exhaustion of the interior of the box `[a, b]` by smaller boxes.
    obtain ⟨A, hA_anti, hA_lt, hA_tendsto⟩ :
      ∃ A : ℕ → ℝⁿ⁺¹, antitone A ∧ (∀ k i, a i < A k i) ∧ tendsto A at_top (𝓝 a),
    { choose A hA_anti hA_lt hA_tendsto using λ i, exists_seq_strict_anti_tendsto (a i),
      exact ⟨flip A, λ k l hkl i, (hA_anti i).antitone hkl, λ k i, hA_lt i k,
        tendsto_pi_nhds.2 hA_tendsto⟩ },
    obtain ⟨B, hA_mono, hB_lt, hB_tendsto⟩ :
      ∃ B : ℕ → ℝⁿ⁺¹, monotone B ∧ (∀ k i, B k i < b i) ∧ tendsto B at_top (𝓝 b),
    { choose B hB_mono hB_lt hB_tendsto using λ i, exists_seq_strict_mono_tendsto (b i),
      exact ⟨flip B, λ k l hkl i, (hB_mono i).monotone hkl, λ k i, hB_lt i k,
        tendsto_pi_nhds.2 hB_tendsto⟩ },
    choose B hB_mono hB_lt hB_tendsto using λ i, exists_seq_strict_mono_tendsto (b i),
    have h₁ : tendsto (λ k, ∫ x in Icc (flip A k) (flip B k), ∑ i, f' x (e i) i) at_top
      (𝓝 (∫ x in Icc a b, ∑ i, f' x (e i) i)),
    { refine tendsto_set_integral_of_Union_ae_eq (λ k, measurable_set_Icc) _ _ Hi,
      { exact λ k l hkl, Icc_subset_Icc (λ i, (hA_anti i).antitone hkl)
          (λ i, (hB_mono i).monotone hkl) },
      { sorry } },
    have h₂ : ∀ᶠ k in at_top, (∀ i, flip A k i < flip B k i) ∧
      continuous_on f (Icc (flip A k) (flip B k)) ∧
      ∀ x ∈ 
 }
end

/-- **Divergence theorem** for a family of functions `f : fin (n + 1) → ℝⁿ⁺¹ → E`. See also
`measure_theory.integral_divergence_of_has_fderiv_within_at_off_countable'` for a version formulated
in terms of a vector-valued function `f : ℝⁿ⁺¹ → Eⁿ⁺¹`. -/
lemma integral_divergence_of_has_fderiv_within_at_off_countable' (hle : a ≤ b)
  (f : fin (n + 1) → ℝⁿ⁺¹ → E) (f' : fin (n + 1) → ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ℝ] E)
  (s : set ℝⁿ⁺¹) (hs : countable s) (Hc : ∀ (x ∈ s) i, continuous_within_at (f i) (Icc a b) x)
  (Hd : ∀ (x ∈ Icc a b \ s) i, has_fderiv_within_at (f i) (f' i x) (Icc a b) x)
  (Hi : integrable_on (λ x, ∑ i, f' i x (e i)) (Icc a b)) :
  ∫ x in Icc a b, ∑ i, f' i x (e i) =
    ∑ i : fin (n + 1),
      ((∫ x in face i, f i (front_face i x)) - ∫ x in face i, f i (back_face i x)) :=
integral_divergence_of_has_fderiv_within_at_off_countable a b hle (λ x i, f i x)
  (λ x, continuous_linear_map.pi (λ i, f' i x)) s hs
  (λ x hx, continuous_within_at_pi.2 (Hc x hx)) (λ x hx, has_fderiv_within_at_pi.2 (Hd x hx)) Hi

end

/-- An auxiliary lemma that is used to specialize the general divergence theorem to spaces that do
not have the form `fin n → ℝ`. -/
lemma integral_divergence_of_has_fderiv_within_at_off_countable_of_equiv
  {F : Type*} [normed_group F] [normed_space ℝ F] [partial_order F] [measure_space F]
  [borel_space F] (eL : F ≃L[ℝ] ℝⁿ⁺¹) (he_ord : ∀ x y, eL x ≤ eL y ↔ x ≤ y)
  (he_vol : measure_preserving eL volume volume) (f : fin (n + 1) → F → E)
  (f' : fin (n + 1) → F → F →L[ℝ] E) (s : set F) (hs : countable s)
  (a b : F) (hle : a ≤ b) (Hc : ∀ (x ∈ s) i, continuous_within_at (f i) (Icc a b) x)
  (Hd : ∀ (x ∈ Icc a b \ s) i, has_fderiv_within_at (f i) (f' i x) (Icc a b) x)
  (DF : F → E) (hDF : ∀ x, DF x = ∑ i, f' i x (eL.symm $ e i)) (Hi : integrable_on DF (Icc a b)) :
  ∫ x in Icc a b, DF x =
    ∑ i : fin (n + 1), ((∫ x in Icc (eL a ∘ i.succ_above) (eL b ∘ i.succ_above),
        f i (eL.symm $ i.insert_nth (eL b i) x)) -
      (∫ x in Icc (eL a ∘ i.succ_above) (eL b ∘ i.succ_above),
        f i (eL.symm $ i.insert_nth (eL a i) x))) :=
have he_emb : measurable_embedding eL := eL.to_homeomorph.to_measurable_equiv.measurable_embedding,
have hIcc : eL ⁻¹' (Icc (eL a) (eL b)) = Icc a b,
  by { ext1 x, simp only [set.mem_preimage, set.mem_Icc, he_ord] },
have hIcc' : Icc (eL a) (eL b) = eL.symm ⁻¹' (Icc a b),
  by rw [← hIcc, eL.symm_preimage_preimage],
calc ∫ x in Icc a b, DF x = ∫ x in Icc a b, ∑ i, f' i x (eL.symm $ e i) : by simp only [hDF]
... = ∫ x in Icc (eL a) (eL b), ∑ i, f' i (eL.symm x) (eL.symm $ e i) :
  begin
    rw [← he_vol.set_integral_preimage_emb he_emb],
    simp only [hIcc, eL.symm_apply_apply]
  end
... = ∑ i : fin (n + 1), ((∫ x in Icc (eL a ∘ i.succ_above) (eL b ∘ i.succ_above),
        f i (eL.symm $ i.insert_nth (eL b i) x)) -
      (∫ x in Icc (eL a ∘ i.succ_above) (eL b ∘ i.succ_above),
        f i (eL.symm $ i.insert_nth (eL a i) x))) :
  begin
    convert integral_divergence_of_has_fderiv_within_at_off_countable' (eL a) (eL b)
      ((he_ord _ _).2 hle) (λ i x, f i (eL.symm x))
      (λ i x, f' i (eL.symm x) ∘L (eL.symm : ℝⁿ⁺¹ →L[ℝ] F))
      (eL.symm ⁻¹' s) (hs.preimage eL.symm.injective) _ _ _,
    { intros x hx i,
      refine (Hc _ hx i).comp eL.symm.continuous_within_at _,
      rw hIcc' },
    { rintro x hx i,
      rw hIcc' at hx ⊢,
      exact (Hd _ hx i).comp x eL.symm.has_fderiv_within_at subset.rfl },
    { rw [← he_vol.integrable_on_comp_preimage he_emb, hIcc],
      simp [← hDF, (∘), Hi] }
  end

end

open_locale interval
open continuous_linear_map (smul_right)

local notation `ℝ¹` := fin 1 → ℝ
local notation `ℝ²` := fin 2 → ℝ
local notation `E¹` := fin 1 → E
local notation `E²` := fin 2 → E

/-- **Fundamental theorem of calculus, part 2**. This version assumes that `f` is differentiable off
a countable set `s`, and is continuous at the points of `s`.

See also

* `interval_integral.integral_eq_sub_of_has_deriv_right_of_le` for a version that only assumes right
differentiability of `f`;

* `measure_theory.integral_eq_of_has_deriv_within_at_off_countable` for a version that works both
  for `a ≤ b` and `b ≤ a` at the expense of using unordered intervals instead of `set.Icc`. -/
theorem integral_eq_of_has_deriv_within_at_off_countable_of_le (f f' : ℝ → E)
  {a b : ℝ} (hle : a ≤ b) {s : set ℝ} (hs : countable s)
  (Hc : ∀ x ∈ s, continuous_within_at f (Icc a b) x)
  (Hd : ∀ x ∈ Icc a b \ s, has_deriv_within_at f (f' x) (Icc a b) x)
  (Hi : interval_integrable f' volume a b) :
  ∫ x in a..b, f' x = f b - f a :=
begin
  set e : ℝ ≃L[ℝ] ℝ¹ := (continuous_linear_equiv.fun_unique (fin 1) ℝ ℝ).symm,
  have e_symm : ∀ x, e.symm x = x 0 := λ x, rfl,
  set F' : ℝ → ℝ →L[ℝ] E := λ x, smul_right (1 : ℝ →L[ℝ] ℝ) (f' x),
  have hF' : ∀ x y, F' x y = y • f' x := λ x y, rfl,
  calc ∫ x in a..b, f' x = ∫ x in Icc a b, f' x :
    by simp only [interval_integral.integral_of_le hle, set_integral_congr_set_ae Ioc_ae_eq_Icc]
  ... = ∑ i : fin 1, ((∫ x in Icc (e a ∘ i.succ_above) (e b ∘ i.succ_above),
        f (e.symm $ i.insert_nth (e b i) x)) -
      (∫ x in Icc (e a ∘ i.succ_above) (e b ∘ i.succ_above),
        f (e.symm $ i.insert_nth (e a i) x))) :
    begin
      refine integral_divergence_of_has_fderiv_within_at_off_countable_of_equiv e _ _
        (λ _, f) (λ _, F') s hs a b hle (λ x hx i, Hc x hx) (λ x hx i, Hd x hx) _ _ _,
      { exact λ x y, (order_iso.fun_unique (fin 1) ℝ).symm.le_iff_le },
      { exact (volume_preserving_fun_unique (fin 1) ℝ).symm },
      { intro x, rw [fin.sum_univ_one, hF', e_symm, pi.single_eq_same, one_smul] },
      { rw [interval_integrable_iff_integrable_Ioc_of_le hle] at Hi,
        exact Hi.congr_set_ae Ioc_ae_eq_Icc.symm }
    end
  ... = f b - f a :
    begin
      simp only [fin.sum_univ_one, e_symm],
      have : ∀ (c : ℝ), const (fin 0) c = is_empty_elim := λ c, subsingleton.elim _ _,
      simp [this, volume_pi, measure.pi_of_empty (λ _ : fin 0, volume)]
    end
end

/-- **Fundamental theorem of calculus, part 2**. This version assumes that `f` is differentiable off
a countable set `s`, and is continuous at the points of `s`.

See also `measure_theory.interval_integral.integral_eq_sub_of_has_deriv_right` for a version that
only assumes right differentiability of `f`.
-/
theorem integral_eq_of_has_deriv_within_at_off_countable (f f' : ℝ → E) {a b : ℝ} {s : set ℝ}
  (hs : countable s) (Hc : ∀ x ∈ s, continuous_within_at f [a, b] x)
  (Hd : ∀ x ∈ [a, b] \ s, has_deriv_within_at f (f' x) [a, b] x)
  (Hi : interval_integrable f' volume a b) :
  ∫ x in a..b, f' x = f b - f a :=
begin
  cases le_total a b with hab hab,
  { simp only [interval_of_le hab] at *,
    exact integral_eq_of_has_deriv_within_at_off_countable_of_le f f' hab hs Hc Hd Hi },
  { simp only [interval_of_ge hab] at *,
    rw [interval_integral.integral_symm, neg_eq_iff_neg_eq, neg_sub, eq_comm],
    exact integral_eq_of_has_deriv_within_at_off_countable_of_le f f' hab hs Hc Hd Hi.symm }
end

/-- **Divergence theorem** for functions on the plane along rectangles. It is formulated in terms of
two functions `f g : ℝ × ℝ → E` and an integral over `Icc a b = [a.1, b.1] × [a.2, b.2]`, where
`a b : ℝ × ℝ`, `a ≤ b`. When thinking of `f` and `g` as the two coordinates of a single function
`F : ℝ × ℝ → E × E` and when `E = ℝ`, this is the usual statement that the integral of the
divergence of `F` inside the rectangle equals the integral of the normal derivative of `F` along the
boundary.

See also `measure_theory.integral2_divergence_prod_of_has_fderiv_within_at_off_countable` for a
version that does not assume `a ≤ b` and uses iterated interval integral instead of the integral
over `Icc a b`. -/
lemma integral_divergence_prod_Icc_of_has_fderiv_within_at_off_countable_of_le (f g : ℝ × ℝ → E)
  (f' g' : ℝ × ℝ → ℝ × ℝ →L[ℝ] E) (a b : ℝ × ℝ) (hle : a ≤ b) (s : set (ℝ × ℝ)) (hs : countable s)
  (Hcf : ∀ x ∈ s, continuous_within_at f (Icc a b) x)
  (Hcg : ∀ x ∈ s, continuous_within_at g (Icc a b) x)
  (Hdf : ∀ x ∈ Icc a b \ s, has_fderiv_within_at f (f' x) (Icc a b) x)
  (Hdg : ∀ x ∈ Icc a b \ s, has_fderiv_within_at g (g' x) (Icc a b) x)
  (Hi : integrable_on (λ x, f' x (1, 0) + g' x (0, 1)) (Icc a b)) :
  ∫ x in Icc a b, f' x (1, 0) + g' x (0, 1) =
    (∫ x in a.1..b.1, g (x, b.2)) - (∫ x in a.1..b.1, g (x, a.2)) +
      (∫ y in a.2..b.2, f (b.1, y)) - ∫ y in a.2..b.2, f (a.1, y) :=
let e : (ℝ × ℝ) ≃L[ℝ] ℝ² := (continuous_linear_equiv.fin_two_arrow ℝ ℝ).symm in
calc ∫ x in Icc a b, f' x (1, 0) + g' x (0, 1)
    = ∑ i : fin 2, ((∫ x in Icc (e a ∘ i.succ_above) (e b ∘ i.succ_above),
        ![f, g] i (e.symm $ i.insert_nth (e b i) x)) -
      (∫ x in Icc (e a ∘ i.succ_above) (e b ∘ i.succ_above),
        ![f, g] i (e.symm $ i.insert_nth (e a i) x))) :
  begin
    refine integral_divergence_of_has_fderiv_within_at_off_countable_of_equiv e _ _
      ![f, g] ![f', g'] s hs a b hle (λ x hx, _) (λ x hx, _) _ _ Hi,
    { exact λ x y, (order_iso.fin_two_arrow_iso ℝ).symm.le_iff_le },
    { exact (volume_preserving_fin_two_arrow ℝ).symm },
    { exact fin.forall_fin_two.2 ⟨Hcf x hx, Hcg x hx⟩ },
    { exact fin.forall_fin_two.2 ⟨Hdf x hx, Hdg x hx⟩ },
    { intro x, rw fin.sum_univ_two, simp }
  end
... = (∫ y in Icc a.2 b.2, f (b.1, y)) - (∫ y in Icc a.2 b.2, f (a.1, y)) +
        ((∫ x in Icc a.1 b.1, g (x, b.2)) - ∫ x in Icc a.1 b.1, g (x, a.2)) :
  begin
    have : ∀ (a b : ℝ¹) (f : ℝ¹ → E), ∫ x in Icc a b, f x = ∫ x in Icc (a 0) (b 0), f (λ _, x),
    { intros a b f,
      convert ((volume_preserving_fun_unique (fin 1) ℝ).symm.set_integral_preimage_emb
        (measurable_equiv.measurable_embedding _) _ _).symm,
      exact ((order_iso.fun_unique (fin 1) ℝ).symm.preimage_Icc a b).symm },
    simp only [fin.sum_univ_two, this],
    refl
  end
... = (∫ x in a.1..b.1, g (x, b.2)) - (∫ x in a.1..b.1, g (x, a.2)) +
        (∫ y in a.2..b.2, f (b.1, y)) - ∫ y in a.2..b.2, f (a.1, y) :
  begin
    simp only [interval_integral.integral_of_le hle.1, interval_integral.integral_of_le hle.2,
      set_integral_congr_set_ae Ioc_ae_eq_Icc],
    abel
  end

/-- **Divergence theorem** for functions on the plane. It is formulated in terms of two functions
`f g : ℝ × ℝ → E` and iterated integral `∫ x in a₁..b₁, ∫ y in a₂..b₂, _`, where
`a₁ a₂ b₁ b₂ : ℝ`. When thinking of `f` and `g` as the two coordinates of a single function
`F : ℝ × ℝ → E × E` and when `E = ℝ`, this is the usual statement that the integral of the
divergence of `F` inside the rectangle with vertices `(aᵢ, bⱼ)`, `i, j =1,2`, equals the integral of
the normal derivative of `F` along the boundary.

See also `measure_theory.integral_divergence_prod_Icc_of_has_fderiv_within_at_off_countable_of_le`
for a version that uses an integral over `Icc a b`, where `a b : ℝ × ℝ`, `a ≤ b`. -/
lemma integral2_divergence_prod_of_has_fderiv_within_at_off_countable (f g : ℝ × ℝ → E)
  (f' g' : ℝ × ℝ → ℝ × ℝ →L[ℝ] E) (a₁ a₂ b₁ b₂ : ℝ) (s : set (ℝ × ℝ)) (hs : countable s)
  (Hcf : ∀ x ∈ s, continuous_within_at f ([a₁, b₁].prod [a₂, b₂]) x)
  (Hcg : ∀ x ∈ s, continuous_within_at g ([a₁, b₁].prod [a₂, b₂]) x)
  (Hdf : ∀ x ∈ [a₁, b₁].prod [a₂, b₂] \ s, has_fderiv_within_at f (f' x) ([a₁, b₁].prod [a₂, b₂]) x)
  (Hdg : ∀ x ∈ [a₁, b₁].prod [a₂, b₂] \ s, has_fderiv_within_at g (g' x) ([a₁, b₁].prod [a₂, b₂]) x)
  (Hi : integrable_on (λ x, f' x (1, 0) + g' x (0, 1)) ([a₁, b₁].prod [a₂, b₂])) :
  ∫ x in a₁..b₁, ∫ y in a₂..b₂, f' (x, y) (1, 0) + g' (x, y) (0, 1) =
    (∫ x in a₁..b₁, g (x, b₂)) - (∫ x in a₁..b₁, g (x, a₂)) +
      (∫ y in a₂..b₂, f (b₁, y)) - ∫ y in a₂..b₂, f (a₁, y) :=
begin
  wlog h₁ : a₁ ≤ b₁ := le_total a₁ b₁ using [a₁ b₁, b₁ a₁] tactic.skip,
  wlog h₂ : a₂ ≤ b₂ := le_total a₂ b₂ using [a₂ b₂, b₂ a₂] tactic.skip,
  { rw [interval_of_le h₁, interval_of_le h₂] at *,
    calc ∫ x in a₁..b₁, ∫ y in a₂..b₂, f' (x, y) (1, 0) + g' (x, y) (0, 1)
        = ∫ x in Icc a₁ b₁, ∫ y in Icc a₂ b₂, f' (x, y) (1, 0) + g' (x, y) (0, 1) :
      by simp only [interval_integral.integral_of_le, h₁, h₂,
        set_integral_congr_set_ae Ioc_ae_eq_Icc]
    ... = ∫ x in (Icc a₁ b₁).prod (Icc a₂ b₂), f' x (1, 0) + g' x (0, 1) :
      (set_integral_prod _ Hi).symm
    ... = (∫ x in a₁..b₁, g (x, b₂)) - (∫ x in a₁..b₁, g (x, a₂)) +
            (∫ y in a₂..b₂, f (b₁, y)) - ∫ y in a₂..b₂, f (a₁, y) :
      begin
        rw Icc_prod_Icc at *,
        apply integral_divergence_prod_Icc_of_has_fderiv_within_at_off_countable_of_le f g f' g'
          (a₁, a₂) (b₁, b₂) ⟨h₁, h₂⟩ s; assumption
      end },
  { rw interval_swap b₂ a₂ at this,
    intros Hcf Hcg Hdf Hdg Hi,
    simp only [interval_integral.integral_symm b₂ a₂, interval_integral.integral_neg],
    refine (congr_arg has_neg.neg (this Hcf Hcg Hdf Hdg Hi)).trans _, abel },
  { rw interval_swap b₁ a₁ at this,
    intros Hcf Hcg Hdf Hdg Hi,
    simp only [interval_integral.integral_symm b₁ a₁],
    refine (congr_arg has_neg.neg (this Hcf Hcg Hdf Hdg Hi)).trans _, abel }
end

end measure_theory
