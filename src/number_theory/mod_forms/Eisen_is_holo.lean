import number_theory.mod_forms.Eisenstein_series
import measure_theory.integral.uniform_lim_of_holo


universes u v w

open complex

open_locale big_operators nnreal classical filter

local notation `ℍ` := upper_half_plane

local notation `ℍ'`:=(⟨upper_half_space, upper_half_plane_is_open⟩: open_subs)
noncomputable theory

namespace Eisenstein_series

lemma badlem (z : ℍ') :  0 < z.1.2 :=
begin
simp at *,
set z':  ℍ := z,
apply upper_half_plane.im_pos z',
end

lemma eisen_square_diff_on (k : ℤ)  (hkn : k ≠ 0) (n : ℕ) :
  is_holomorphic_on (λ (z : ℍ'), eisen_square k n z) :=
begin
  rw ←  is_holomorphic_on_iff_differentiable_on,
  have h1 : extend_by_zero (λ (z : ℍ'), eisen_square k n z) =
  λ x : ℂ,  ∑ y in (Square n), (extend_by_zero (λ z : ℍ', Eise k z y)) x,
  by {simp_rw eisen_square,
  funext z,
  by_cases h : z ∈ ℍ'.1,
  simp [extend_by_zero, h] at *,
  simp [extend_by_zero, h] at *,},
  simp at *,
  rw h1,
  apply differentiable_on.sum,
  intros i hi,
  apply Eise'_has_diff_within_at k i hkn,
end

def eisen_square' (k : ℤ) (n: ℕ) : ℍ' → ℂ:=
λ (z : ℍ'), ∑ x in (finset.range n), eisen_square k x z


lemma eisen_square'_diff_on (k : ℤ)  (hkn : k ≠ 0) (n : ℕ) :
  is_holomorphic_on (eisen_square' k n ) :=
begin
rw ←  is_holomorphic_on_iff_differentiable_on,
have h1 : extend_by_zero ( eisen_square' k n) =
  λ x : ℂ,  ∑ y in (finset.range n), (extend_by_zero (λ z : ℍ', eisen_square k y z)) x,
  by{simp_rw eisen_square',
  funext z,
  by_cases h : z ∈ ℍ'.1,
  simp [extend_by_zero, h] at *,
  simp [extend_by_zero, h] at *},
rw h1,
apply differentiable_on.sum,
intros i hi,
have := eisen_square_diff_on k hkn i,
rw ←  is_holomorphic_on_iff_differentiable_on at this,
apply this,
end

lemma Eisen_partial_tends_to_uniformly_on_ball (k: ℕ) (h : 3 ≤ k) (z : ℍ') : ∃ (A B ε : ℝ),
  0 < ε ∧ metric.closed_ball z ε ⊆ (upper_half_space_slice A B)  ∧  0 < B ∧ ε < B ∧
(tendsto_uniformly_on (eisen_square' k) (Eisenstein_series_of_weight_ k)
filter.at_top (metric.closed_ball z ε)   ) :=
begin
have h1:= closed_ball_in_slice z,
obtain ⟨A, B, ε, hε, hB, hball, hA, hεB⟩ := h1,
use A,
use B,
use ε,
simp [hε, hB, hball, hεB],
have hz: z ∈ (upper_half_space_slice A B), by {apply hball, simp  [hε .le],},
have hu:= (Eisen_partial_tends_to_uniformly k h A B hA hB),
have hu2:
  tendsto_uniformly_on (Eisen_par_sum_slice k A B ) (Eisenstein_series_restrict k A B hB)
  filter.at_top (metric.closed_ball ⟨z, hz⟩ ε), by {apply hu.tendsto_uniformly_on},
clear hu,
simp_rw Eisenstein_series_restrict at *,
simp_rw metric.tendsto_uniformly_on_iff at *,
simp_rw Eisen_par_sum_slice at *,
simp_rw Eisen_square_slice at *,
simp_rw eisen_square',
simp at *,
intros δ hδ,
have hu3:= hu2 δ hδ,
clear hu2,
obtain ⟨a, ha⟩:=hu3,
use a,
intros b hb x hx,
have hxx: x ∈ upper_half_space_slice A B, by {apply hball, simp [hx],},
simp at hxx,
have hxu : 0 < x.1.2, by {apply badlem,},
have ha2:= ha b hb x hxu hxx hx,
apply ha2,
end

lemma Eisen_partial_tends_to_uniformly_on_ball' (k: ℕ) (h : 3 ≤ k) (z : ℍ') : ∃ (A B ε : ℝ),
  0 < ε ∧ metric.closed_ball z ε ⊆ (upper_half_space_slice A B)  ∧  0 < B ∧ ε < B ∧
(tendsto_uniformly_on ( λ n, extend_by_zero ( eisen_square' k n))
(extend_by_zero (Eisenstein_series_of_weight_ k))
filter.at_top (metric.closed_ball z ε)   ) :=
begin
have H := Eisen_partial_tends_to_uniformly_on_ball k h z,
obtain ⟨A, B, ε, hε, hball, hB, hεB, hunif⟩ :=H,
use A,
use B,
use ε,
simp [hε, hball, hB, hεB],
simp_rw metric.tendsto_uniformly_on_iff at *,
intros ε' hε',
have h2:= hunif ε' hε',
simp at *,
obtain ⟨a, ha⟩:= h2,
use a,
have Hba:= ball_in_upper_half z A B ε hB hε hεB hball,
intros b hb x hx,
have hxx : x ∈ ℍ'.1, by {apply Hba, simp [hx],},
have hf:= ext_by_zero_apply ℍ' (Eisenstein_series_of_weight_ k) ⟨x, hxx⟩,
let F: ℕ → ℍ' → ℂ := λ n,  eisen_square' k n,
have hFb:= ext_by_zero_apply ℍ' (F b) ⟨x, hxx⟩,
simp only [topological_space.opens.mem_coe, subtype.coe_mk, subtype.val_eq_coe] at *,
rw hf,
rw hFb,
apply ha b hb ⟨x, hxx⟩ hx,
end


lemma Eisenstein_is_holomorphic (k: ℕ) (hk : 3 ≤ k):
  is_holomorphic_on (Eisenstein_series_of_weight_ k):=
begin
  rw ←  is_holomorphic_on_iff_differentiable_on,
  apply diff_on_diff,
  intro x,
  have H:= Eisen_partial_tends_to_uniformly_on_ball' k hk x,
  obtain ⟨A, B, ε, hε, hball, hB, hεB, hunif⟩ :=H,
  use 2⁻¹*ε,
  have hball2: metric.closed_ball ↑x ε ⊆ ℍ'.1,
  by {apply ball_in_upper_half x A B ε hB hε hεB hball,},
  split,
  ring_nf,
  nlinarith,
  split,
  have hb2 := complex.half_ball_sub ε hε x,
  intros w hw,
  have hwa : w ∈ ℍ'.1,
  by { apply hball2, simp, simp at hw, apply le_trans hw.le, field_simp, linarith,},
  apply hwa,
  have hkn : (k : ℤ) ≠ 0, by {norm_cast, linarith,},
  let F: ℕ → ℂ → ℂ := λ n, extend_by_zero ( eisen_square' k n),
  have hdiff : ∀ (n : ℕ), differentiable_on ℂ (F n) (metric.closed_ball x ε),
  by {intro n,
  have := eisen_square'_diff_on k hkn n,
  rw ← is_holomorphic_on_iff_differentiable_on at this,
  simp_rw F,
  apply this.mono,
  apply hball2,},
  apply unif_of_diff_is_diff F (extend_by_zero (Eisenstein_series_of_weight_ k)) x ε hε hdiff hunif,
end

lemma Eisenstein_is_bounded (k: ℕ) (hk : 3 ≤ k) :
  (λ z : ℍ, Eisenstein_series_of_weight_ k z) ∈ is_bound_at_infinity  :=
begin
simp,
sorry,
end


end Eisenstein_series
