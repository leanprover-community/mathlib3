/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

The Fréchet derivative.

Let `E` and `F` be normed spaces, and `f : E → F`. Then

  `has_fderiv_at_within f f' x s`

says that the function `f' : E → F` is a bounded linear map and `f` has derivative `f'` at
`x`, where the domain of interest is restricted to `s`. We also have

  `has_fderiv_at f f' x := has_fderiv_at_within f f' x univ`

We may want to prove some theorems specifically for this special case, but most of the more
general theorems should apply right out of the box.

The derivative is characterized in two ways: in terms of the `tendsto` relation, and in terms of
the `littleo` relation.
-/
import topology.basic analysis.normed_space.bounded_linear_maps ..asymptotics tactic.abel
open filter asymptotics

variables {E : Type*} [normed_space ℝ E]
variables {F : Type*} [normed_space ℝ F]
variables {G : Type*} [normed_space ℝ G]

def has_fderiv_at_within (f : E → F) (f' : E → F) (x : E) (s : set E) :=
is_bounded_linear_map f' ∧
  tendsto (λ x', ∥x' - x∥⁻¹ • (f x' - f x - f' (x' - x))) (nhds_within x s) (nhds 0)

def has_fderiv_at (f : E → F) (f' : E → F) (x : E) :=
has_fderiv_at_within f f' x set.univ

theorem has_fderiv_equiv_aux (f : E → F) (f' : E → F) (x : E) (s : set E)
    (bf' : is_bounded_linear_map f') :
  tendsto (λ x', ∥x' - x∥⁻¹ • (f x' - f x - f' (x' - x))) (nhds_within x s) (nhds 0) =
  tendsto (λ x', ∥x' - x∥⁻¹ * ∥f x' - f x - f' (x' - x)∥) (nhds_within x s) (nhds 0) :=
begin
  have f'0 : f' 0 = 0 := bf'.to_linear_map.map_zero,
  rw [tendsto_iff_norm_tendsto_zero], congr,
  ext x',
  have : ∥x' + -x∥⁻¹ ≥ 0, from inv_nonneg.mpr (norm_nonneg _),
  simp [norm_smul, real.norm_eq_abs, abs_of_nonneg this]
end

theorem has_fderiv_iff_littleo {f : E → F} {f' : E → F} {x : E} {s : set E} :
  has_fderiv_at_within f f' x s ↔
    is_bounded_linear_map f' ∧
      is_littleo (λ x', f x' - f x - f' (x' - x)) (λ x', x' - x) (nhds_within x s) :=
and.congr_right_iff.mpr $
  assume bf' : is_bounded_linear_map f',
  have f'0 : f' 0 = 0 := bf'.to_linear_map.map_zero,
  have h : ∀ x', ∥x' - x∥ = 0 → ∥f x' - f x - f' (x' - x)∥ = 0, from
    assume x' hx',
    have x' = x,
      from eq_of_sub_eq_zero ((norm_eq_zero _).mp hx'),
    by rw this; simp [f'0],
  begin
    rw has_fderiv_equiv_aux _ _ _ _ bf',
    rw ←is_littleo_norm_left,
    rw ←is_littleo_norm_right,
    rw is_littleo_iff_tendsto h,
    apply iff_of_eq, congr, ext x',
    apply mul_comm
  end

def has_fderiv_at_within_mono {f : E → F} {f' : E → F} {x : E} {s t : set E}
    (h : has_fderiv_at_within f f' x t) (hst : s ⊆ t) :
  has_fderiv_at_within f f' x s :=
and.intro h.left (tendsto_nhds_within_mono_left h.right hst)

theorem has_fderiv_at_within.congr {f₀ f₁ : E → F} {f₀' f₁' : E → F}
    {x : E} {s : set E} (h : has_fderiv_at_within f₀ f₀' x s)
    (h₀ : ∀ x, f₀ x = f₁ x) (h₁ : ∀ x, f₀' x = f₁' x) :
  has_fderiv_at_within f₁ f₁' x s :=
by rw [←(funext h₀ : f₀ = f₁), ←(funext h₁ : f₀' = f₁')]; exact h

theorem has_fderiv_id (x : E) (s : set E) : has_fderiv_at_within id id x s :=
and.intro is_bounded_linear_map.id $
  (@tendsto_const_nhds _ _ _ 0 _).congr (by simp)

theorem has_fderiv_const (c : F) (x : E) (s : set E) :
  has_fderiv_at_within (λ x, c) (λ y, 0) x s :=
and.intro is_bounded_linear_map.zero $
  (@tendsto_const_nhds _ _ _ 0 _).congr (by simp)

theorem has_fderiv_smul {f : E → F} {f' : E → F} {x : E} {s : set E}
    (c : ℝ) (h : has_fderiv_at_within f f' x s) :
  has_fderiv_at_within (λ x, c • f x) (λ x, c • f' x) x s :=
and.intro (is_bounded_linear_map.smul c h.left) $
begin
  have h' := tendsto_smul_const c h.right,
  rw smul_zero at h',
  apply h'.congr, intro x, simp,
  rw [smul_smul, mul_comm c, ←smul_smul, smul_add, smul_add c, smul_neg, smul_neg]
end

theorem has_fderiv_add {f g : E → F} {f' g' : E → F} {x : E} {s : set E}
    (hf : has_fderiv_at_within f f' x s) (hg : has_fderiv_at_within g g' x s) :
  has_fderiv_at_within (λ x, f x + g x) (λ x, f' x + g' x) x s :=
and.intro (is_bounded_linear_map.add hf.left hg.left) $
begin
  have h' := tendsto_add hf.right hg.right,
  rw add_zero at h',
  apply h'.congr, intro x, simp [smul_add]
end

theorem has_fderiv_neg {f : E → F} {f' : E → F} {x : E} {s : set E}
    (h : has_fderiv_at_within f f' x s) :
  has_fderiv_at_within (λ x, - f x) (λ x, - f' x) x s :=
(has_fderiv_smul (-1 : ℝ) h).congr (by simp) (by simp)

theorem has_fderiv_sub {f g : E → F} {f' g' : E → F} {x : E} {s : set E}
    (hf : has_fderiv_at_within f f' x s) (hg : has_fderiv_at_within g g' x s) :
  has_fderiv_at_within (λ x, f x - g x) (λ x, f' x - g' x) x s :=
has_fderiv_add hf (has_fderiv_neg hg)

theorem continuous_of_has_fderiv {f : E → F} {f' : E → F} {x : E} {s : set E}
    (h : has_fderiv_at_within f f' x s) :
  continuous_at_within f x s :=
have bf : is_bounded_linear_map f' := h.left,
have f'0 : f' 0 = 0 := bf.to_linear_map.map_zero,
have h₁ : tendsto (λ x', ∥x' - x∥) (nhds_within x s) (nhds 0),
  from tendsto_iff_norm_tendsto_zero.mp (tendsto_nhds_within_of_tendsto_nhds tendsto_id),
have h₂ : tendsto (λ x', f x' - f x - f' (x' - x)) (nhds_within x s) (nhds 0),
  begin
    have := tendsto_smul h₁ h.right, rw [zero_smul] at this,
    apply this.congr, intro x', dsimp,
    cases classical.em (x = x') with h' h', { simp [h', f'0] },
    have : ∥x' + -x∥ ≠ 0, by rw [ne, norm_eq_zero, add_neg_eq_zero]; apply ne.symm h',
    rw [smul_smul, mul_inv_cancel this, one_smul]
  end,
have h₃ : tendsto (λ x', f' (x' - x)) (nhds_within x s) (nhds 0),
  begin
    have : tendsto (λ x', x' - x) (nhds x) (nhds 0),
      by rw ←sub_self x; exact tendsto_sub tendsto_id tendsto_const_nhds,
    apply tendsto.comp (tendsto_nhds_within_of_tendsto_nhds this),
    suffices : tendsto f' (nhds 0) (nhds (f' 0)), by rwa f'0 at this,
    exact continuous_iff_continuous_at.mp bf.continuous 0
  end,
have h₄ : tendsto (λ x', f x' - f x) (nhds_within x s) (nhds 0),
  begin
    have :=  tendsto_add h₂ h₃, rw add_zero at this,
    apply this.congr, intro x', simp
  end,
begin
  have := tendsto_add h₄ (tendsto_const_nhds), rw zero_add at this,
  apply this.congr, intro x', simp
end

theorem chain_rule {g g' : F → G} {f f' : E → F} {s : set E} {x : E}
    (hf : has_fderiv_at_within f f' x s)
    (hg : has_fderiv_at_within g g' (f x) (f '' s)) :
  has_fderiv_at_within (g ∘ f) (g' ∘ f') x s :=
have bf' : is_bounded_linear_map f', from hf.left,
have bg' : is_bounded_linear_map g', from hg.left,
have g'add : ∀ x y, g' (x + y) = g' x + g' y, from bg'.to_linear_map.map_add,
have g'neg : ∀ x, g' (-x) = -(g' x), from bg'.to_linear_map.map_neg,
have ctsf : continuous_at_within f x s, from continuous_of_has_fderiv hf,
have eq₁ : is_littleo (λ x', f x' - f x - f' (x' - x)) (λ x', x' - x) (nhds_within x s),
  from (has_fderiv_iff_littleo.mp hf).right,
have eq₂ : is_littleo (λ y', g y' - g (f x) - g' (y' - f x)) (λ y', y' - f x) (nhds_within (f x) (f '' s)),
  from (has_fderiv_iff_littleo.mp hg).right,
suffices is_littleo (λ x', g (f x') - g (f x) - g' (f' (x' - x))) (λ x', x' - x) (nhds_within x s),
  from has_fderiv_iff_littleo.mpr ⟨is_bounded_linear_map.comp bg' bf', this⟩,
have eq₃ : is_littleo (λ x', g (f x') - g (f x) - g' (f x' - f x)) (λ x', f x' - f x) (nhds_within x s),
  from (eq₂.comp f).mono (nhds_within_le_comap ctsf),
have eq₄ : is_bigo (λ x', f x' - f x) (λ x', x' - x) (nhds_within x s), from
  by { convert eq₁.to_is_bigo.add (bf'.is_bigo_sub _ _), ext x', simp },
have eq₅ : is_littleo (λ x', g (f x') - g (f x) - g' (f x' - f x)) (λ x', x' - x) (nhds_within x s),
  from is_littleo_of_is_littleo_of_is_bigo eq₃ eq₄,
have eq₆ : is_littleo (λ x', g' (f x' - f x - f' (x' - x))) (λ x', x' - x) (nhds_within x s),
  by { refine is_littleo_of_is_bigo_of_is_littleo _ eq₁,
       exact ((bg'.is_bigo_id ⊤).comp _).mono (le_comap_top _ _) },
by { convert eq₅.add eq₆, ext x', simp [g'add, g'neg], abel }
