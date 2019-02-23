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

The derivative is defined in terms of the `littleo` relation, but also characterized in terms of
the `tendsto` relation.
-/
import topology.basic analysis.normed_space.bounded_linear_maps ..asymptotics tactic.abel
open filter asymptotics

variables {E : Type*} [normed_space ℝ E]
variables {F : Type*} [normed_space ℝ F]
variables {G : Type*} [normed_space ℝ G]

def has_fderiv_at_within (f : E → F) (f' : E → F) (x : E) (s : set E) :=
is_bounded_linear_map f' ∧
  is_littleo (λ x', f x' - f x - f' (x' - x)) (λ x', x' - x) (nhds_within x s)

def has_fderiv_at (f : E → F) (f' : E → F) (x : E) :=
has_fderiv_at_within f f' x set.univ

theorem has_fderiv_at.is_littleo {f : E → F} {f' : E → F} {x : E} (h : has_fderiv_at f f' x) :
  is_littleo (λ x', f x' - f x - f' (x' - x)) (λ x', x' - x) (nhds x) :=
by convert h.right; rw nhds_within_univ

theorem has_fderiv_at_within_equiv_aux (f : E → F) (f' : E → F) (x : E) (s : set E)
    (bf' : is_bounded_linear_map f') :
  tendsto (λ x', ∥x' - x∥⁻¹ • (f x' - f x - f' (x' - x))) (nhds_within x s) (nhds 0) =
  tendsto (λ x', ∥x' - x∥⁻¹ * ∥f x' - f x - f' (x' - x)∥) (nhds_within x s) (nhds 0) :=
begin
  have f'0 : f' 0 = 0 := (bf'.to_linear_map _).map_zero,
  rw [tendsto_iff_norm_tendsto_zero], congr, ext x',
  have : ∥x' + -x∥⁻¹ ≥ 0, from inv_nonneg.mpr (norm_nonneg _),
  simp [norm_smul, real.norm_eq_abs, abs_of_nonneg this]
end

theorem has_fderiv_at_within_iff_tendsto {f : E → F} {f' : E → F} {x : E} {s : set E} :
  has_fderiv_at_within f f' x s ↔
    is_bounded_linear_map f' ∧
      tendsto (λ x', ∥x' - x∥⁻¹ • (f x' - f x - f' (x' - x))) (nhds_within x s) (nhds 0) :=
and.congr_right_iff.mpr $
  assume bf' : is_bounded_linear_map f',
  have f'0 : f' 0 = 0 := (bf'.to_linear_map _).map_zero,
  have h : ∀ x', ∥x' - x∥ = 0 → ∥f x' - f x - f' (x' - x)∥ = 0, from
    assume x' hx',
    have x' = x, from eq_of_sub_eq_zero ((norm_eq_zero _).mp hx'),
    by rw this; simp [f'0],
  begin
    rw has_fderiv_at_within_equiv_aux _ _ _ _ bf',
    rw [←is_littleo_norm_left, ←is_littleo_norm_right, is_littleo_iff_tendsto h],
    apply iff_of_eq, congr, ext x', apply mul_comm
  end

theorem has_fderiv_at_iff_tendsto {f : E → F} {f' : E → F} {x : E} :
  has_fderiv_at f f' x ↔
    is_bounded_linear_map f' ∧
      tendsto (λ x', ∥x' - x∥⁻¹ • (f x' - f x - f' (x' - x))) (nhds x) (nhds 0) :=
by convert has_fderiv_at_within_iff_tendsto; rw nhds_within_univ

theorem has_fderiv_at_within.mono {f : E → F} {f' : E → F} {x : E} {s t : set E}
    (hst : s ⊆ t) (h : has_fderiv_at_within f f' x t) :
  has_fderiv_at_within f f' x s :=
and.intro h.left (h.right.mono (nhds_within_mono _ hst))

theorem has_fderiv_at_within_of_has_fderiv_at {f : E → F} {f' : E → F} {x : E} {s : set E}
    (h : has_fderiv_at f f' x) :
  has_fderiv_at_within f f' x s :=
h.mono (set.subset_univ _)

theorem has_fderiv_at_within.congr {f₀ f₁ : E → F} {f₀' f₁' : E → F} {x : E} {s : set E}
    (h : has_fderiv_at_within f₀ f₀' x s)
    (h₀ : ∀ x, f₀ x = f₁ x) (h₁ : ∀ x, f₀' x = f₁' x) :
  has_fderiv_at_within f₁ f₁' x s :=
by rw [←(funext h₀ : f₀ = f₁), ←(funext h₁ : f₀' = f₁')]; exact h

theorem has_fderiv_at.congr {f₀ f₁ : E → F} {f₀' f₁' : E → F} {x : E} (h : has_fderiv_at f₀ f₀' x)
    (h₀ : ∀ x, f₀ x = f₁ x) (h₁ : ∀ x, f₀' x = f₁' x) :
  has_fderiv_at f₁ f₁' x :=
has_fderiv_at_within.congr h h₀ h₁

theorem has_fderiv_at_within_id (x : E) (s : set E) : has_fderiv_at_within id id x s :=
and.intro is_bounded_linear_map.id $ by convert is_littleo_zero _ _; simp

theorem has_fderiv_at_id (x : E) : has_fderiv_at id id x :=
has_fderiv_at_within_id x set.univ

theorem has_fderiv_at_within_const (c : F) (x : E) (s : set E) :
  has_fderiv_at_within (λ x, c) (λ y, 0) x s :=
and.intro is_bounded_linear_map.zero (by simp; apply is_littleo_zero)

theorem has_fderiv_at_const (c : F) (x : E) :
  has_fderiv_at (λ x, c) (λ y, 0) x :=
has_fderiv_at_within_const c x set.univ

theorem has_fderiv_at_within_smul {f : E → F} {f' : E → F} {x : E} {s : set E}
    (c : ℝ) (h : has_fderiv_at_within f f' x s) :
  has_fderiv_at_within (λ x, c • f x) (λ x, c • f' x) x s :=
and.intro (is_bounded_linear_map.smul c h.left) $
  by { convert is_littleo_const_smul_left h.right c, ext x, simp [smul_neg, smul_add] }

theorem has_fderiv_at_smul {f : E → F} {f' : E → F} {x : E}
    (c : ℝ) (h : has_fderiv_at f f' x) :
  has_fderiv_at (λ x, c • f x) (λ x, c • f' x) x :=
has_fderiv_at_within_smul c h

theorem has_fderiv_at_within_add {f g : E → F} {f' g' : E → F} {x : E} {s : set E}
    (hf : has_fderiv_at_within f f' x s) (hg : has_fderiv_at_within g g' x s) :
  has_fderiv_at_within (λ x, f x + g x) (λ x, f' x + g' x) x s :=
and.intro (is_bounded_linear_map.add hf.left hg.left) $
by { convert (hf.right.add hg.right), simp }

theorem has_fderiv_at_add {f g : E → F} {f' g' : E → F} {x : E}
    (hf : has_fderiv_at f f' x) (hg : has_fderiv_at g g' x) :
  has_fderiv_at (λ x, f x + g x) (λ x, f' x + g' x) x :=
has_fderiv_at_within_add hf hg

theorem has_fderiv_at_within_neg {f : E → F} {f' : E → F} {x : E} {s : set E}
    (h : has_fderiv_at_within f f' x s) :
  has_fderiv_at_within (λ x, -f x) (λ x, -f' x) x s :=
(has_fderiv_at_within_smul (-1 : ℝ) h).congr (by simp) (by simp)

theorem has_fderiv_at_neg {f : E → F} {f' : E → F} {x : E} (h : has_fderiv_at f f' x) :
  has_fderiv_at (λ x, -f x) (λ x, -f' x) x :=
has_fderiv_at_within_neg h

theorem has_fderiv_at_within_sub {f g : E → F} {f' g' : E → F} {x : E} {s : set E}
    (hf : has_fderiv_at_within f f' x s) (hg : has_fderiv_at_within g g' x s) :
  has_fderiv_at_within (λ x, f x - g x) (λ x, f' x - g' x) x s :=
has_fderiv_at_within_add hf (has_fderiv_at_within_neg hg)

theorem has_fderiv_at_sub {f g : E → F} {f' g' : E → F} {x : E}
    (hf : has_fderiv_at f f' x) (hg : has_fderiv_at g g' x) :
  has_fderiv_at (λ x, f x - g x) (λ x, f' x - g' x) x :=
has_fderiv_at_within_sub hf hg

theorem continuous_at_within_of_has_fderiv_at_within {f : E → F} {f' : E → F} {x : E} {s : set E}
    (h : has_fderiv_at_within f f' x s) :
  continuous_at_within f x s :=
have bf' : is_bounded_linear_map f' := h.left,
have eq₁ : is_littleo (λ x', f x' - f x - f' (x' - x)) (λ x', x' - x) (nhds_within x s),
  from h.right,
have eq₂ : is_bigo (λ x', f x' - f x) (λ x', x' - x) (nhds_within x s),
  by { convert eq₁.to_is_bigo.add (bf'.is_bigo_sub _ _), ext, abel },
have eq₃ : is_littleo (λ x', x' - x) (λ x, (1 : ℝ)) (nhds_within x s),
  by { rw [is_littleo_one_iff, ←sub_self x], apply tendsto_nhds_within_of_tendsto_nhds,
       exact tendsto_sub tendsto_id tendsto_const_nhds },
have eq₄ : tendsto (λ x', f x' - f x) (nhds_within x s) (nhds 0),
  by { exact is_littleo_one_iff.mp (eq₂.trans_is_littleo eq₃) },
by { have := tendsto_add eq₄ tendsto_const_nhds, rw zero_add at this,
     apply this.congr, intro x', simp }

theorem continuous_at_of_has_fderiv_at {f : E → F} {f' : E → F} {x : E} (h : has_fderiv_at f f' x) :
  continuous_at f x :=
by rw [←continuous_at_within_univ]; exact continuous_at_within_of_has_fderiv_at_within h

theorem chain_rule_at_within {g g' : F → G} {f f' : E → F} {s : set E} {x : E}
    (hf : has_fderiv_at_within f f' x s)
    (hg : has_fderiv_at_within g g' (f x) (f '' s)) :
  has_fderiv_at_within (g ∘ f) (g' ∘ f') x s :=
have bf' : is_bounded_linear_map f', from hf.left,
have bg' : is_bounded_linear_map g', from hg.left,
have g'add : ∀ x y, g' (x + y) = g' x + g' y, from (bg'.to_linear_map _).map_add,
have g'neg : ∀ x, g' (-x) = -(g' x), from (bg'.to_linear_map _).map_neg,
have ctsf : continuous_at_within f x s, from continuous_at_within_of_has_fderiv_at_within hf,
have eq₁ : is_littleo (λ x', f x' - f x - f' (x' - x)) (λ x', x' - x) (nhds_within x s),
  from hf.right,
have eq₂ : is_littleo (λ y', g y' - g (f x) - g' (y' - f x)) (λ y', y' - f x) (nhds_within (f x) (f '' s)),
  from hg.right,
suffices is_littleo (λ x', g (f x') - g (f x) - g' (f' (x' - x))) (λ x', x' - x) (nhds_within x s),
  from ⟨is_bounded_linear_map.comp bg' bf', this⟩,
have eq₃ : is_littleo (λ x', g (f x') - g (f x) - g' (f x' - f x)) (λ x', f x' - f x) (nhds_within x s),
  from (eq₂.comp f).mono (nhds_within_le_comap ctsf),
have eq₄ : is_bigo (λ x', f x' - f x) (λ x', x' - x) (nhds_within x s), from
  by { convert eq₁.to_is_bigo.add (bf'.is_bigo_sub _ _), ext x', simp },
have eq₅ : is_littleo (λ x', g (f x') - g (f x) - g' (f x' - f x)) (λ x', x' - x) (nhds_within x s),
  from eq₃.trans_is_bigo eq₄,
have eq₆ : is_littleo (λ x', g' (f x' - f x - f' (x' - x))) (λ x', x' - x) (nhds_within x s),
  by { refine is_bigo.trans_is_littleo _ eq₁,
       exact ((bg'.is_bigo_id ⊤).comp _).mono (le_comap_top _ _) },
by { convert eq₅.add eq₆, ext x', simp [g'add, g'neg], abel }

theorem chain_rule {g g' : F → G} {f f' : E → F} {x : E}
    (hf : has_fderiv_at f f' x)
    (hg : has_fderiv_at g g' (f x)) :
  has_fderiv_at (g ∘ f) (g' ∘ f') x :=
chain_rule_at_within hf (has_fderiv_at_within_of_has_fderiv_at hg)
