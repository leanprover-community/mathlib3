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
integrals of `f` over the faces of `[a, b]`, taken with appropriat signs. Moreover, the same is true
if the function is not differentiable but continuous at countably many points of `[a, b]`.

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

* Deduce corollaries about integrals in `ℝ × ℝ` and interval integral.
* Add a version that assumes existence and integrability of partial derivatives.

## Tags

divergence theorem, Bochner integral
-/

open set finset topological_space function box_integral measure_theory
open_locale big_operators classical topological_space

namespace measure_theory

universes u
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

/-- **Divergence theorem** for Bochner integral. If `f : ℝⁿ⁺¹ → Eⁿ⁺¹` is differentiable on a
rectangular box `[a, b] : set ℝⁿ⁺¹`, `a ≤ b`, with derivative `f' : ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ℝ] Eⁿ⁺¹` and the
divergence `λ x, ∑ i, f' x eᵢ i` is integrable on `[a, b]`, where `eᵢ = pi.single i 1` is the `i`-th
basis vector, then its integral is equal to the sum of integrals of `f` over the faces of `[a, b]`,
taken with appropriat signs.

Moreover, the same is true if the function is not differentiable but continuous at countably many
points of `[a, b]`.

We represent both faces `x i = a i` and `x i = b i` as the box
`face i = [a ∘ fin.succ_above i, b ∘ fin.succ_above i]` in `ℝⁿ`, where
`fin.succ_above : fin n ↪o fin (n + 1)` is the order embedding with range `{i}ᶜ`. The restrictions
of `f : ℝⁿ⁺¹ → Eⁿ⁺¹` to these faces are given by `f ∘ back_face i` and `f ∘ front_face i`, where
`back_face i = fin.insert_nth i (a i)` and `front_face i = fin.insert_nth i (b i)` are embeddings
`ℝⁿ → ℝⁿ⁺¹` that take `y : ℝⁿ` and insert `a i` (resp., `b i`) as `i`-th coordinate. -/
lemma integral_divergence_of_has_fderiv_within_at_off_countable (hle : a ≤ b) (f : ℝⁿ⁺¹ → Eⁿ⁺¹)
  (f' : ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ℝ] Eⁿ⁺¹) (s : set ℝⁿ⁺¹) (hs : countable s)
  (Hc : ∀ x ∈ s, continuous_within_at f (Icc a b) x)
  (Hd : ∀ x ∈ Icc a b \ s, has_fderiv_within_at f (f' x) (Icc a b) x)
  (Hi : integrable_on (λ x, ∑ i, f' x (e i) i) (Icc a b)) :
  ∫ x in Icc a b, ∑ i, f' x (e i) i =
    ∑ i : fin (n + 1),
      ((∫ x in face i, f (front_face i x) i) - ∫ x in face i, f (back_face i x) i) :=
begin
  simp only [volume_pi, ← set_integral_congr_set_ae measure.univ_pi_Ioc_ae_eq_Icc],
  by_cases heq : ∃ i, a i = b i,
  { rcases heq with ⟨i, hi⟩,
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
  { push_neg at heq,
    obtain ⟨I, rfl, rfl⟩ : ∃ I : box_integral.box (fin (n + 1)), I.lower = a ∧ I.upper = b,
      from ⟨⟨a, b, λ i, (hle i).lt_of_ne (heq i)⟩, rfl, rfl⟩,
    simp only [← box.coe_eq_pi, ← box.face_lower, ← box.face_upper],
    have A := ((Hi.mono_set box.coe_subset_Icc).has_box_integral ⊥ rfl),
    have B := has_integral_bot_divergence_of_forall_has_deriv_within_at I f f' s hs Hc Hd,
    have Hc : continuous_on f I.Icc,
    { intros x hx,
      by_cases hxs : x ∈ s,
      exacts [Hc x hxs, (Hd x ⟨hx, hxs⟩).continuous_within_at] },
    rw continuous_on_pi at Hc,
    refine (A.unique B).trans (sum_congr rfl $ λ i hi, _),
    refine congr_arg2 has_sub.sub _ _,
    { have := box.continuous_on_face_Icc (Hc i) (set.right_mem_Icc.2 (hle i)),
      have := (this.integrable_on_compact (box.is_compact_Icc _)).mono_set box.coe_subset_Icc,
      exact (this.has_box_integral ⊥ rfl).integral_eq, apply_instance },
    { have := box.continuous_on_face_Icc (Hc i) (set.left_mem_Icc.2 (hle i)),
      have := (this.integrable_on_compact (box.is_compact_Icc _)).mono_set box.coe_subset_Icc,
      exact (this.has_box_integral ⊥ rfl).integral_eq, apply_instance } }
end

/-- A version of `integral_divergence_of_has_fderiv_within_at_off_countable'` that uses a family of
functions `f : fin (n + 1) → ℝⁿ⁺¹ → E` instead of a vector-valued function `f : ℝⁿ⁺¹ → Eⁿ⁺¹`. -/
lemma integral_divergence_of_has_fderiv_within_at_off_countable' (hle : a ≤ b)
  (f : fin (n + 1) → ℝⁿ⁺¹ → E) (f' : fin (n + 1) → ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ℝ] E)
  (s : set ℝⁿ⁺¹) (hs : countable s) (Hc : ∀ (x ∈ s) i, continuous_within_at (f i) (Icc a b) x)
  (Hd : ∀ (x ∈ Icc a b \ s) i, has_fderiv_within_at (f i) (f' i x) (Icc a b) x)
  (Hi : integrable_on (λ x, ∑ i, f' i x (pi.single i 1)) (Icc a b)) :
  ∫ x in Icc a b, ∑ i, f' i x (e i) =
    ∑ i : fin (n + 1),
      ((∫ x in face i, f i (front_face i x)) - ∫ x in face i, f i (back_face i x)) := integral_divergence_of_has_fderiv_within_at_off_countable a b hle (λ x i, f i x)
  (λ x, continuous_linear_map.pi (λ i, f' i x)) s hs
  (λ x hx, continuous_within_at_pi.2 (Hc x hx)) (λ x hx, has_fderiv_within_at_pi.2 (Hd x hx)) Hi

end

lemma integral_divergence_of_has_fderiv_within_at_off_countable_of_equiv
  {F : Type*} [normed_group F] [normed_space ℝ F] [partial_order F] [measure_space F]
  [borel_space F] (eL : F ≃L[ℝ] ℝⁿ⁺¹) (he_ord : ∀ x y, eL x ≤ eL y ↔ x ≤ y)
  (he_vol : measure.map eL volume = volume) (f : fin (n + 1) → F → E)
  (f' : fin (n + 1) → F → F →L[ℝ] E) (s : set F) (hs : countable s)
  (a b : F) (hle : a ≤ b) (Hc : ∀ (x ∈ s) i, continuous_within_at (f i) (Icc a b) x)
  (Hd : ∀ (x ∈ Icc a b \ s) i, has_fderiv_within_at (f i) (f' i x) (Icc a b) x)
  (DF : F → E) (hDF : ∀ x, DF x = ∑ i, f' i x (eL.symm $ e i)) (Hi : integrable_on DF (Icc a b)) :
  ∫ x in Icc a b, DF x =
    ∑ i : fin (n + 1), ((∫ x in Icc (eL a ∘ i.succ_above) (eL b ∘ i.succ_above),
        f i (eL.symm $ i.insert_nth (eL b i) x)) -
      (∫ x in Icc (eL a ∘ i.succ_above) (eL b ∘ i.succ_above),
        f i (eL.symm $ i.insert_nth (eL a i) x))) :=
have he_vol' : measure_preserving eL.to_homeomorph.to_measurable_equiv volume volume :=
  ⟨eL.continuous.measurable, he_vol⟩,
have hIcc : eL ⁻¹' (Icc (eL a) (eL b)) = Icc a b,
  by { ext1 x, simp only [set.mem_preimage, set.mem_Icc, he_ord] },
have hIcc' : Icc (eL a) (eL b) = eL.symm ⁻¹' (Icc a b),
  by rw [← hIcc, eL.symm_preimage_preimage],
calc ∫ x in Icc a b, DF x = ∫ x in Icc a b, ∑ i, f' i x (eL.symm $ e i) : by simp only [hDF]
... = ∫ x in Icc (eL a) (eL b), ∑ i, f' i (eL.symm x) (eL.symm $ e i) :
  begin
    rw [← he_vol'.map_eq, set_integral_map_equiv],
    simp only [hIcc, homeomorph.to_measurable_equiv_coe, continuous_linear_equiv.coe_to_homeomorph,
      eL.symm_apply_apply]
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
    { erw [← he_vol'.map_eq, integrable_on_map_equiv, hIcc], }
  end

end

open_locale interval
open continuous_linear_map (smul_right)

local notation `ℝ¹` := fin 1 → ℝ
local notation `ℝ²` := fin 2 → ℝ
local notation `E¹` := fin 1 → E
local notation `E²` := fin 2 → E

theorem integral_eq_of_has_deriv_within_at_off_countable_of_le (f f' : ℝ → E)
  {a b : ℝ} (hle : a ≤ b) {s : set ℝ} (hs : countable s)
  (Hc : ∀ x ∈ s, continuous_within_at f (Icc a b) x)
  (Hd : ∀ x ∈ Icc a b \ s, has_deriv_within_at f (f' x) (Icc a b) x)
  (Hi : interval_integrable f' volume a b) :
  ∫ x in a..b, f' x = f b - f a :=
begin
  set eL : ℝ¹ →L[ℝ] ℝ := continuous_linear_map.proj 0,
  set eo : ℝ¹ ≃o ℝ := order_iso.fun_unique _ _,
  set e : ℝ¹ ≃ᵐ ℝ := measurable_equiv.fun_unique _ _,
  have he : measure_preserving e volume volume, from ⟨e.measurable, measure.map_fun_unique volume⟩,
  set F : fin 1 → ℝ¹ → E := λ i x, f (x 0),
  set F' : fin 1 → ℝ¹ → ℝ¹ →L[ℝ] E := λ i x, ((1 : ℝ →L[ℝ] ℝ).smul_right (f' (x 0))) ∘L eL,
  have hF' : ∀ x, ∑ i, F' i (λ _, x) (pi.single i 1) = f' x,
  { intro x, rw [fin.sum_univ_one], simp },
  calc ∫ x in a..b, f' x
      = ∫ x : ℝ¹ in Icc (eo.symm a) (eo.symm b), ∑ i : fin 1, F' i x (pi.single i 1) :
    begin
      simp only [volume_pi, set_integral_fun_unique_pi, interval_integral.integral_of_le hle,
        set_integral_congr_set_ae Ioc_ae_eq_Icc, ← eo.preimage_Icc, hF'],
      refl
    end
  ... = ∑ i : fin 1, ((∫ x in Icc (const _ a) (const _ b), F i (i.insert_nth b x)) -
                     ∫ x in Icc (const _ a) (const _ b), F i (i.insert_nth a x)) :
    begin
      refine integral_divergence_of_has_fderiv_within_at_off_countable' (const _ a) (const _ b)
        (λ _, hle) F F' (eo.symm '' s) (hs.image _) (ball_image_iff.2 $ λ x hx i, _) _ _,
      { rw [← eo.preimage_Icc],
        refine continuous_within_at.comp _ eL.continuous.continuous_within_at subset.rfl,
        exact Hc x hx },
      { rw [eo.symm.image_eq_preimage, eo.symm_symm, ← eo.preimage_Icc, ← preimage_diff],
        intros x hx i,
        refine has_fderiv_within_at.comp x _ eL.has_fderiv_within_at subset.rfl,
        exact Hd (x 0) hx },
      { rw [← eo.preimage_Icc, ← he.symm.map_eq, integrable_on_map_equiv],
        rw [interval_integrable_iff_integrable_Ioc_of_le hle] at Hi,
        convert Hi.congr_set_ae Ioc_ae_eq_Icc.symm using 1,
        exact funext hF' }
    end
  ... = f b - f a :
    begin
      rw fin.sum_univ_one,
      have : ∀ c : ℝ, const (fin 0) c = is_empty_elim := λ c, subsingleton.elim _ _,
      simp [F, this, volume_pi, measure.pi_of_empty (λ _, volume)],
    end
end

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

end measure_theory
