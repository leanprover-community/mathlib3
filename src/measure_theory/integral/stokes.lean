/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.box_integral.stokes
import analysis.box_integral.integrability
import measure_theory.integral.interval_integral

namespace linear_equiv

def {u v} fin_two_arrow_equiv (R : Type u) (M : Type v) [semiring R] [add_comm_monoid M]
  [module R M] :
  (fin 2 → M) ≃ₗ[R] M × M :=
{ map_add' := λ f g, rfl,
  map_smul' := λ c f, rfl,
  .. fin_two_arrow_equiv M }

end linear_equiv

namespace homeomorph

def {u} fin_two_arrow_homeomorph (X : Type u) [topological_space X] :
  (fin 2 → X) ≃ₜ X × X :=
{ to_equiv := fin_two_arrow_equiv X,
  continuous_to_fun := continuous.prod_mk (continuous_apply _) (continuous_apply _),
  continuous_inv_fun := continuous_pi_iff.2 $
    fin.forall_fin_two.2 ⟨continuous_fst, continuous_snd⟩ }

end homeomorph

namespace continuous_linear_equiv

def {u v} fin_two_arrow_equiv (R : Type u) (M : Type v) [semiring R] [add_comm_monoid M]
  [module R M] [topological_space M] :
  (fin 2 → M) ≃L[R] M × M :=
{ to_linear_equiv := linear_equiv.fin_two_arrow_equiv R M,
  .. homeomorph.fin_two_arrow_homeomorph M }

@[simp] lemma {u v} fin_two_arrow_equiv_apply {R : Type u} {M : Type v} [semiring R]
  [add_comm_monoid M] [module R M] [topological_space M] (f : fin 2 → M) :
  fin_two_arrow_equiv R M f = (f 0, f 1) := rfl

@[simp] lemma {u v} fin_two_arrow_equiv_symm_apply {R : Type u} {M : Type v} [semiring R]
  [add_comm_monoid M] [module R M] [topological_space M] (x : M × M) :
  (fin_two_arrow_equiv R M).symm x = ![x.1, x.2] := rfl

@[simps apply symm_apply]
def arrow_congr {R M₁ M₂ M₃ M₄ : Type*} [semiring R] [add_comm_monoid M₁] [add_comm_monoid M₂]
  [add_comm_monoid M₃] [add_comm_monoid M₄] [module R M₁] [module R M₂] [module R M₃] [module R M₄]
  [topological_space M₁] [topological_space M₂] [topological_space M₃] [topological_space M₄]
  (e₁ : M₁ ≃L[R] M₂) (e₂ : M₃ ≃L[R] M₄) :
  (M₁ →L[R] M₃) ≃ (M₂ →L[R] M₄) :=
{ to_fun := λ f, (e₂ : M₃ →L[R] M₄).comp (f.comp e₁.symm),
  inv_fun := λ f, (e₂.symm : M₄ →L[R] M₃).comp (f.comp e₁),
  left_inv := λ f, by { ext, simp only [continuous_linear_map.coe_comp', coe_coe, (∘),
    symm_apply_apply] },
  right_inv := λ f, by { ext, simp only [continuous_linear_map.coe_comp', coe_coe, (∘),
    apply_symm_apply] } }

end continuous_linear_equiv

open set finset topological_space box_integral
open_locale big_operators classical

@[to_additive]
lemma prod_univ_fin_two {M : Type*} [comm_monoid M] (f : fin 2 → M) :
  (∏ i, f i) = f 0 * f 1 :=
by simp [fin.prod_univ_succ]

namespace measure_theory

universes u
variables {E : Type u} [normed_group E] [normed_space ℝ E] [measurable_space E] [borel_space E]
  [second_countable_topology E] [complete_space E] {n : ℕ}

local notation `ℝⁿ` := fin n → ℝ
local notation `ℝⁿ⁺¹` := fin (n + 1) → ℝ
local notation `Eⁿ⁺¹` := fin (n + 1) → E

/-- Divergence theorem for Bochner integral. If `f : ℝⁿ → Eⁿ` is differentiable on a rectangular box
`[a, b] : set ℝⁿ`, `a ≤ b`, with derivative `f' : ℝⁿ → ℝⁿ →L[ℝ] Eⁿ` and the divergence
`λ x, ∑ i, f' x (pi.single i 1) i` is integrable on `[a, b]`, then its integral is equal to the sum
of integrals of `f` over the faces of `[a, b]`, taken with appropriat signs. -/
lemma integral_divergence_of_has_deriv_within_at_off_countable (f : ℝⁿ⁺¹ → Eⁿ⁺¹)
  (f' : ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ℝ] Eⁿ⁺¹) (a b : ℝⁿ⁺¹) (hle : a ≤ b)
  (s : set ℝⁿ⁺¹) (hs : countable s) (Hc : ∀ x ∈ Icc a b ∩ s, continuous_within_at f (Icc a b) x)
  (Hd : ∀ x ∈ Icc a b \ s, has_fderiv_within_at f (f' x) (Icc a b) x)
  (Hi : integrable_on (λ x, ∑ i, f' x (pi.single i 1) i) (Icc a b)) :
  ∫ x in Icc a b, ∑ i, f' x (pi.single i 1) i =
    ∑ i : fin (n + 1),
      ((∫ x in Icc (a ∘ i.succ_above) (b ∘ i.succ_above), f (i.insert_nth (b i) x) i) -
      ∫ x in Icc (a ∘ i.succ_above) (b ∘ i.succ_above), f (i.insert_nth (a i) x) i) :=
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
      exacts [Hc x ⟨hx, hxs⟩, (Hd x ⟨hx, hxs⟩).continuous_within_at] },
    rw continuous_on_pi at Hc,
    refine (A.unique B).trans (sum_congr rfl $ λ i hi, _),
    refine congr_arg2 has_sub.sub _ _,
    { have := box.continuous_on_face_Icc (Hc i) (right_mem_Icc.2 (hle i)),
      have := (this.integrable_on_compact box.is_compact_Icc).mono_set box.coe_subset_Icc,
      exact (this.has_box_integral ⊥ rfl).integral_eq, apply_instance },
    { have := box.continuous_on_face_Icc (Hc i) (left_mem_Icc.2 (hle i)),
      have := (this.integrable_on_compact box.is_compact_Icc).mono_set box.coe_subset_Icc,
      exact (this.has_box_integral ⊥ rfl).integral_eq, apply_instance } }
end

open measure

local notation `ℝ²` := fin 2 → ℝ
local notation `E²` := fin 2 → E

lemma divergence_real_prod_eq (f' : ℝ × ℝ →L[ℝ] E × E) :
  (∑ i : fin 2, ((continuous_linear_equiv.fin_two_arrow_equiv ℝ ℝ).arrow_congr
    (continuous_linear_equiv.fin_two_arrow_equiv ℝ E)).symm f' (pi.single i 1) i) =
    (f' (1, 0)).1 + (f' (0, 1)).2 :=
by simp [sum_univ_fin_two]

lemma integral_divergence_prod_of_has_fderiv_within_at_off_countable (f : ℝ × ℝ → E × E)
  (f' : ℝ × ℝ → ℝ × ℝ →L[ℝ] E × E) {a b : ℝ × ℝ} (hle : a ≤ b) (s : set (ℝ × ℝ))
  (hs : countable s)
  (Hc : ∀ x ∈ Icc a b ∩ s, continuous_within_at f (Icc a b) x)
  (Hd : ∀ x ∈ Icc a b \ s, has_fderiv_within_at f (f' x) (Icc a b) x)
  (Hi : integrable_on (λ x, (f' x (1, 0)).1 + (f' x (0, 1)).2) (Icc a b)) :
  ∫ x in Icc a b, (f' x (1, 0)).1 + (f' x (0, 1)).2 =
    (∫ x in a.1..b.1, (f (x, b.2)).2) - (∫ x in a.1..b.1, (f (x, a.2)).2) +
      (∫ y in a.2..b.2, (f (b.1, y)).1) - ∫ y in a.2..b.2, (f (a.1, y)).1 :=
begin
  rw [add_sub_assoc, add_comm],
  simp_rw [interval_integral.integral_of_le hle.1, interval_integral.integral_of_le hle.2,
    set_integral_congr_set_ae Ioc_ae_eq_Icc, ← set_integral_fin_two_arrow'],
  simp only [← divergence_real_prod_eq, volume_eq_prod, prod_eq_map_fin_two_arrow_same,
    integrable_on_map_equiv, (∘), ← volume_pi] at Hi ⊢,
  set e : ℝ² ≃ ℝ × ℝ := fin_two_arrow_equiv ℝ,
  set eo : ℝ² ≃o ℝ × ℝ := order_iso.fin_two_arrow_iso ℝ,
  rcases ⟨eo.surjective a, eo.surjective b⟩ with ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩,
  erw [eo.preimage_Icc, e.symm_apply_apply, e.symm_apply_apply] at Hi ⊢,
  replace hle : a ≤ b := eo.le_iff_le.1 hle,
  set eL : ℝ² ≃L[ℝ] ℝ × ℝ := continuous_linear_equiv.fin_two_arrow_equiv ℝ ℝ,
  set eE : E² ≃L[ℝ] E × E := continuous_linear_equiv.fin_two_arrow_equiv ℝ E,
  set F' : ℝ² → ℝ² →L[ℝ] E² := λ x, (eL.arrow_congr eE).symm (f' (e x)),
  set F : ℝ² → E² := eE.symm ∘ f ∘ e,
  replace hs : countable (e ⁻¹' s) := hs.preimage e.injective,
  rw [← eo.image_Icc] at Hc Hd,
  replace Hc : ∀ x ∈ Icc a b ∩ e ⁻¹' s, continuous_within_at F (Icc a b) x,
  { rintro x ⟨hx, hxs : e x ∈ s⟩,
    refine eE.symm.continuous_at.comp_continuous_within_at _,
    exact (Hc (e x) ⟨mem_image_of_mem _ hx, hxs⟩).comp eL.continuous_within_at
      (maps_to_image e (Icc a b)) },
  replace Hd : ∀ x ∈ Icc a b \ e ⁻¹' s, has_fderiv_within_at F (F' x) (Icc a b) x,
  { rintro x ⟨hx, hxs : e x ∉ s⟩,
    refine eE.symm.has_fderiv_at.comp_has_fderiv_within_at x _,
    exact (Hd (e x) ⟨mem_image_of_mem _ hx, hxs⟩).comp x eL.has_fderiv_within_at
      (maps_to_image e (Icc a b)) },
  refine (integral_divergence_of_has_deriv_within_at_off_countable
    F F' a b hle _ hs Hc Hd Hi).trans ((sum_univ_fin_two _).trans _),
  simp only [set_integral_fun_unique],
  erw [(order_iso.fun_unique (fin 1) ℝ).symm.preimage_Icc,
    (order_iso.fun_unique (fin 1) ℝ).symm.preimage_Icc],
  have he : ∀ x, e.symm x = ![x.1, x.2] := λ x, rfl,
  have heo : ∀ x, eo x = (x 0, x 1) := λ x, rfl,
  have : ∀ x (g : fin 1 → ℝ),  @fin.cons 1 (λ _, ℝ) x g 1 = g 0,
  { intros x g, rw [← fin.succ_zero_eq_one, fin.cons_succ] },
  simp [F, eE, heo, fin.insert_nth_apply_below fin.zero_lt_one, this]
end

end measure_theory
