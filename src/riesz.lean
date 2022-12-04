/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import analysis.normed_space.finite_dimension

open filter metric
open_locale topological_space

/-!
# Une introduction à Lean par le théorème de Riesz

Je vais expliquer la preuve du théorème de Riesz à l'ordinateur.

Le théorème de Riesz affirme que si un espace vectoriel réel a une boule compacte, alors il est
de dimension finie.

On raisonne par contraposée : si l'espace n'est pas de dimension finie, on va construire une suite
dans la boule de rayon `2` dont tous les points sont à distance au moins `1`, ce qui contredirait
la compacité de la boule.

On construit la suite par récurrence. Supposons les `n` premiers points construits. Ils engendrent
un sous-espace `F` de dimension finie, qui est complet (par équivalence des normes) donc fermé.
Soit `x ∉ F`, et notons `d` sa distance à `F` (qui est positive par fermeture). On choisit
`y ∈ F` avec `dist x y < 2 d`. J'affirme que `d⁻¹ * (x - y)` convient pour le point suivant.
Il est bien de norme au plus `2`. De plus, comme `xᵢ ∈ F`, on a `y + d * xᵢ ∈ F`. Ainsi,
`d ≤ dist x (y + d * xᵢ)`, soit `d ≤ ‖d * (d⁻¹ * (x - y) - xᵢ)‖`,
et donc `1 ≤ ‖d⁻¹ * (x - y) - xᵢ‖` comme on le voulait.

Pour expliquer cette preuve de 10 lignes à Lean, on va la couper en plusieurs sous-lemmes.
-/

variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]

/-- Étant donné un sous-espace vectoriel fermé qui n'est pas tout l'espace, on peut trouver un point
de norme au plus `2` à distance au moins `1` de tout point du sous-espace. -/
lemma existe_point_loin_de_sousmodule
  (F : submodule ℝ E) (hF : ∃ x, x ∉ F) (hFc : is_closed (F : set E)) :
  ∃ (z : E), ‖z‖ < 2 ∧ (∀ y ∈ F, 1 ≤ ‖z - y‖) :=
begin
  obtain ⟨x, hx⟩ := hF,
  let d := inf_dist x F,
  have hFn : (F : set E).nonempty, from ⟨0, F.zero_mem⟩,
  have d_pos : 0 < d, from (is_closed.not_mem_iff_inf_dist_pos hFc hFn).1 hx,
  obtain ⟨y₀, hy₀F, hxy₀⟩ : ∃ y ∈ F, dist x y < 2 * d,
  { apply (inf_dist_lt_iff hFn).1,
    exact lt_two_mul_self d_pos },
    -- linarith },
  let z := d⁻¹ • (x - y₀),
  have Nz : ‖z‖ < 2, by simpa [z, norm_smul, abs_of_nonneg d_pos.le, ← div_eq_inv_mul,
    div_lt_iff d_pos, ← dist_eq_norm],
  have I : ∀ y ∈ F, 1 ≤ ‖z - y‖,
  { assume y hyF,
    have A : d ≤ dist x (y₀ + d • y),
    { apply inf_dist_le_dist_of_mem,
      exact F.add_mem hy₀F (F.smul_mem _ hyF), },
    have B : d⁻¹ * d = 1, by field_simp [d_pos.ne'],
    calc
      1 = d⁻¹ * d                    : B.symm
    ... ≤ d⁻¹ * dist x (y₀ + d • y)  : mul_le_mul_of_nonneg_left A (inv_nonneg.2 d_pos.le)
    ... = d⁻¹ * ‖(x - y₀) - d • y‖   : by rw [dist_eq_norm, sub_sub]
    ... = ‖d⁻¹ • ((x - y₀) - d • y)‖ : by simp [norm_smul, abs_of_nonneg d_pos.le]
    ... = ‖z - y‖                    : by simp_rw [z, smul_sub, smul_smul, B, one_smul] },
  exact ⟨z, Nz, I⟩,
end

/-- Dans un espace vectoriel normé réel de dimension infinie, étant donné un ensemble fini de points,
on peut trouver un point de norme au plus `2` à distance au moins `1` de tous ces points. -/
lemma existe_point_loin_de_fini
  (s : set E) (hs : set.finite s) (h : ¬(finite_dimensional ℝ E)) :
  ∃ (z : E), ‖z‖ < 2 ∧ (∀ y ∈ s, 1 ≤ ‖z - y‖) :=
begin
  let F := submodule.span ℝ s,
  haveI : finite_dimensional ℝ F := module.finite_def.2
    ((submodule.fg_top _).2 (submodule.fg_def.2 ⟨s, hs, rfl⟩)),
  have Fclosed : is_closed (F : set E) := submodule.closed_of_finite_dimensional _,
  have hF : ∃ x, x ∉ F,
  { contrapose! h,
    have : (⊤ : submodule ℝ E) = F, by { ext x, simp [h] },
    have : finite_dimensional ℝ (⊤ : submodule ℝ E), by rwa this,
    refine module.finite_def.2 ((submodule.fg_top _).1 (module.finite_def.1 this)) },
  obtain ⟨x, x_lt_2, hx⟩ : ∃ (x : E), ‖x‖ < 2 ∧ ∀ (y : E), y ∈ F → 1 ≤ ‖x - y‖ :=
    existe_point_loin_de_sousmodule F hF Fclosed,
  exact ⟨x, x_lt_2, λ y hy, hx _ (submodule.subset_span hy)⟩,
end

/-- Dans un espace vectoriel normé réel de dimension infinie, on peut trouver une suite de points
tous de norme au plus `2` et mutuellement distants d'au moins `1`. -/
lemma existe_suite_loin
  (h : ¬(finite_dimensional ℝ E)) :
  ∃ (u : ℕ → E), (∀ n, ‖u n‖ < 2) ∧ (∀ m n, m ≠ n → 1 ≤ ‖u n - u m‖) :=
begin
  haveI : is_symm E (λ (x y : E), 1 ≤ ‖y - x‖),
  { constructor,
    assume x y hxy,
    rw ← norm_neg,
    simpa },
  apply exists_seq_of_forall_finset_exists' (λ (x : E), ‖x‖ < 2) (λ (x : E) (y : E), 1 ≤ ‖y - x‖),
  assume s hs,
  exact existe_point_loin_de_fini (s : set E) s.finite_to_set h
end

/-- Considérons un espace vectoriel normé réel dans lequel la boule fermée de rayon `2` est
compacte. Alors cet espace est de dimension finie. -/
theorem ma_version_de_riesz (h : is_compact (metric.closed_ball (0 : E) 2)) :
  finite_dimensional ℝ E :=
begin
  by_contra hfin,
  obtain ⟨u, u_lt_two, u_far⟩ :
    ∃ (u : ℕ → E), (∀ n, ‖u n‖ < 2) ∧ (∀ m n, m ≠ n → 1 ≤ ‖u n - u m‖) :=
    existe_suite_loin hfin,
  have A : ∀ n, u n ∈ closed_ball (0 : E) 2,
  { assume n,
    simpa only [norm_smul, dist_zero_right, mem_closed_ball] using (u_lt_two n).le },
  obtain ⟨x, hx, φ, φmono, φlim⟩ : ∃ (x : E) (H : x ∈ closed_ball (0 : E) 2) (φ : ℕ → ℕ),
    strict_mono φ ∧ tendsto (u ∘ φ) at_top (𝓝 x) := h.tendsto_subseq A,
  have B : cauchy_seq (u ∘ φ) := φlim.cauchy_seq,
  obtain ⟨N, hN⟩ : ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n → dist ((u ∘ φ) n) ((u ∘ φ) N) < 1 :=
    metric.cauchy_seq_iff'.1 B 1 zero_lt_one,
  apply lt_irrefl (1 : ℝ),
  calc 1 ≤ dist (u (φ (N+1))) (u (φ N)) : begin
    simp only [dist_eq_norm, ←smul_sub, norm_smul, -mul_one],
    apply u_far,
    exact (φmono (nat.lt_succ_self N)).ne
  end
  ... < 1 : hN (N+1) (nat.le_succ N)
end

/- La preuve est finie, et prend environ 100 lignes, soit 10 fois plus que la version informelle.
C'est assez typique. -/

theorem la_vraie_version_de_riesz
  (𝕜 : Type*) [nontrivially_normed_field 𝕜] {F : Type*} [normed_add_comm_group F]
  [normed_space 𝕜 F] [complete_space 𝕜] {r : ℝ}
  (r_pos : 0 < r)  {c : F} (hc : is_compact (closed_ball c r)) :
  finite_dimensional 𝕜 F :=
finite_dimensional_of_is_compact_closed_ball 𝕜 r_pos hc
-- by library_search

/- Pour l'énoncé précédent :
  have : (0 : ℝ) < 2 := zero_lt_two,
  library_search,
-/

/- Les preuves sont vérifiées par le "noyau". Mais comment se convaincre que les définitions
sont bonnes ? Avec une mauvaise définition, on risque de pouvoir démontrer n'importe quoi. -/

def is_SG_compact {α : Type*} (s : set α) : Prop := false

theorem riesz_avec_is_SG_compact (h : is_SG_compact (closed_ball (0 : E) 2)) :
  finite_dimensional ℝ E :=
false.elim h

theorem antiriesz_avec_is_SG_compact (h : is_SG_compact (closed_ball (0 : E) 2)) :
  ¬(finite_dimensional ℝ E) :=
false.elim h

/- On peut essayer de dérouler les définitions pour voir si elles ont l'air raisonnables. -/

#check is_compact
#check finite_dimensional

/- On peut voir si les définitions permettent de démontrer des théorèmes raisonnables. -/

example (n : ℕ) : finite_dimensional ℝ (fin n → ℝ) := by apply_instance

example (n : ℕ) : is_compact (closed_ball (0 : fin n → ℝ) 1) := is_compact_closed_ball _ _

example : ¬(is_compact (set.univ : set ℝ)) := noncompact_univ ℝ

example {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [nontrivial E] :
  ¬(is_compact (set.univ : set E)) := noncompact_univ E
