/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
import analysis.calculus.cont_diff_def
import analysis.calculus.mean_value
import analysis.normed_space.finite_dimension

/-!
# Higher differentiability of usual operations

We prove that the usual operations (addition, multiplication, difference, composition, and
so on) preserve `C^n` functions. We also expand the API aound `C^n` functions.

## Notations

We use the notation `E [×n]→L[𝕜] F` for the space of continuous multilinear maps on `E^n` with
values in `F`. This is the space in which the `n`-th derivative of a function from `E` to `F` lives.

In this file, we denote `⊤ : ℕ∞` with `∞`.

## Tags

derivative, differentiability, higher derivative, `C^n`, multilinear, Taylor series, formal series
-/

noncomputable theory
open_locale classical big_operators nnreal

local notation `∞` := (⊤ : ℕ∞)

universes u v w uD uE uF uG

local attribute [instance, priority 1001]
normed_add_comm_group.to_add_comm_group normed_space.to_module' add_comm_group.to_add_comm_monoid

namespace finset

/- TODO porting note: move the next two lemmas to the file `data.nat.choose.sum` -/
/-- The sum of `(n+1).choose i * f i (n+1-i)` can be split into two sums at rank `n`,
respectively of `n.choose i * f i (n+1-i)` and `n.choose i * f (i+1) (n-i)`. -/
lemma sum_choose_succ_mul {R : Type*} [semiring R] (f : ℕ → ℕ → R) (n : ℕ) :
  ∑ i in range (n+2), ((n+1).choose i : R) * f i (n + 1 - i) =
    ∑ i in range (n+1), (n.choose i : R) * f i (n + 1 - i)
      + ∑ i in range (n+1), (n.choose i : R) * f (i + 1) (n - i) :=
begin
  have A : ∑ i in range (n + 1), (n.choose (i+1) : R) * f (i + 1) (n - i) + f 0 (n + 1)
    = ∑ i in range (n+1), n.choose i * f i (n + 1 - i),
  { rw [finset.sum_range_succ, finset.sum_range_succ'],
    simp only [nat.choose_succ_self, algebra_map.coe_zero, zero_mul, add_zero,
      nat.succ_sub_succ_eq_sub, nat.choose_zero_right, algebra_map.coe_one, one_mul, tsub_zero] },
  calc
  ∑ i in finset.range (n+2), ((n+1).choose i : R) * f i (n + 1 - i)
      = ∑ i in finset.range (n+1), ((n+1).choose (i+1) : R) * f (i+1) (n + 1 - (i+1))
        + f 0 (n + 1 - 0) :
    begin
      rw finset.sum_range_succ',
      simp only [nat.choose_zero_right, algebra_map.coe_one, one_mul],
    end
  ... = ∑ i in finset.range (n+1), (n.choose i : R) * f i (n + 1 - i)
        + ∑ i in finset.range (n+1), n.choose i * f (i + 1) (n - i) :
    begin
      simp only [nat.choose_succ_succ, nat.cast_add, nat.succ_sub_succ_eq_sub, tsub_zero, add_mul],
      rw [finset.sum_add_distrib, ← A],
      abel,
    end
end

/-- The sum along the antidiagonal of `(n+1).choose i * f i j` can be split into two sums along the
antidiagonal at rank `n`, respectively of `n.choose i * f i (j+1)` and `n.choose j * f (i+1) j`. -/
lemma sum_antidiagonal_choose_succ_mul {R : Type*} [semiring R] (f : ℕ → ℕ → R) (n : ℕ) :
  ∑ ij in nat.antidiagonal (n + 1), ((n + 1).choose ij.1 : R) * f ij.1 ij.2 =
    ∑ ij in nat.antidiagonal n, (n.choose ij.1 : R) * f ij.1 (ij.2 + 1)
      + ∑ ij in nat.antidiagonal n, (n.choose ij.2 : R) * f (ij.1 + 1) ij.2 :=
begin
  convert sum_choose_succ_mul f n using 1,
  { exact nat.sum_antidiagonal_eq_sum_range_succ (λ i j, ((n+1).choose i : R) * f i j) (n+1) },
  congr' 1,
  { rw nat.sum_antidiagonal_eq_sum_range_succ (λ i j, (n.choose i : R) * f i (j + 1)) n,
    apply finset.sum_congr rfl (λ i hi, _),
    have : n + 1 - i = n - i + 1, from nat.sub_add_comm (nat.lt_succ_iff.1 (finset.mem_range.1 hi)),
    simp only [this] },
  { suffices H : ∑ ij in nat.antidiagonal n, (n.choose ij.2 : R) * f (ij.1 + 1) ij.2
      = ∑ ij in nat.antidiagonal n, (n.choose ij.1 : R) * f (ij.1 + 1) ij.2,
    by rw [H, nat.sum_antidiagonal_eq_sum_range_succ (λ i j, (n.choose i : R) * f (i + 1) j) n],
    apply finset.sum_congr rfl (λ i hi, _),
    congr' 2,
    apply nat.choose_symm_of_eq_add,
    rw [← nat.mem_antidiagonal.1 hi, add_comm] }
end

end finset

open set fin filter function
open_locale topology

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
{D : Type uD} [normed_add_comm_group D] [normed_space 𝕜 D]
{E : Type uE} [normed_add_comm_group E] [normed_space 𝕜 E]
{F : Type uF} [normed_add_comm_group F] [normed_space 𝕜 F]
{G : Type uG} [normed_add_comm_group G] [normed_space 𝕜 G]
{X : Type*} [normed_add_comm_group X] [normed_space 𝕜 X]
{s s₁ t u : set E} {f f₁ : E → F} {g : F → G} {x x₀ : E} {c : F}
{b : E × F → G} {m n : ℕ∞} {p : E → formal_multilinear_series 𝕜 E F}

/-! ### Constants -/

@[simp] lemma iterated_fderiv_zero_fun {n : ℕ} :
  iterated_fderiv 𝕜 n (λ x : E, (0 : F)) = 0 :=
begin
  induction n with n IH,
  { ext m, simp },
  { ext x m,
    rw [iterated_fderiv_succ_apply_left, IH],
    change (fderiv 𝕜 (λ (x : E), (0 : (E [×n]→L[𝕜] F))) x : E → (E [×n]→L[𝕜] F)) (m 0) (tail m) = _,
    rw fderiv_const,
    refl }
end

lemma cont_diff_zero_fun :
  cont_diff 𝕜 n (λ x : E, (0 : F)) :=
begin
  apply cont_diff_of_differentiable_iterated_fderiv (λm hm, _),
  rw iterated_fderiv_zero_fun,
  exact differentiable_const (0 : (E [×m]→L[𝕜] F))
end

/--
Constants are `C^∞`.
-/
lemma cont_diff_const {c : F} : cont_diff 𝕜 n (λx : E, c) :=
begin
  suffices h : cont_diff 𝕜 ∞ (λx : E, c), by exact h.of_le le_top,
  rw cont_diff_top_iff_fderiv,
  refine ⟨differentiable_const c, _⟩,
  rw fderiv_const,
  exact cont_diff_zero_fun
end

lemma cont_diff_on_const {c : F} {s : set E} :
  cont_diff_on 𝕜 n (λx : E, c) s :=
cont_diff_const.cont_diff_on

lemma cont_diff_at_const {c : F} :
  cont_diff_at 𝕜 n (λx : E, c) x :=
cont_diff_const.cont_diff_at

lemma cont_diff_within_at_const {c : F} :
  cont_diff_within_at 𝕜 n (λx : E, c) s x :=
cont_diff_at_const.cont_diff_within_at

@[nontriviality] lemma cont_diff_of_subsingleton [subsingleton F] :
  cont_diff 𝕜 n f :=
by { rw [subsingleton.elim f (λ _, 0)], exact cont_diff_const }

@[nontriviality] lemma cont_diff_at_of_subsingleton [subsingleton F] :
  cont_diff_at 𝕜 n f x :=
by { rw [subsingleton.elim f (λ _, 0)], exact cont_diff_at_const }

@[nontriviality] lemma cont_diff_within_at_of_subsingleton [subsingleton F] :
  cont_diff_within_at 𝕜 n f s x :=
by { rw [subsingleton.elim f (λ _, 0)], exact cont_diff_within_at_const }

@[nontriviality] lemma cont_diff_on_of_subsingleton [subsingleton F] :
  cont_diff_on 𝕜 n f s :=
by { rw [subsingleton.elim f (λ _, 0)], exact cont_diff_on_const }

/-! ### Smoothness of linear functions -/

/--
Unbundled bounded linear functions are `C^∞`.
-/
lemma is_bounded_linear_map.cont_diff (hf : is_bounded_linear_map 𝕜 f) :
  cont_diff 𝕜 n f :=
begin
  suffices h : cont_diff 𝕜 ∞ f, by exact h.of_le le_top,
  rw cont_diff_top_iff_fderiv,
  refine ⟨hf.differentiable, _⟩,
  simp_rw [hf.fderiv],
  exact cont_diff_const
end

lemma continuous_linear_map.cont_diff (f : E →L[𝕜] F) : cont_diff 𝕜 n f :=
f.is_bounded_linear_map.cont_diff

lemma continuous_linear_equiv.cont_diff (f : E ≃L[𝕜] F) : cont_diff 𝕜 n f :=
(f : E →L[𝕜] F).cont_diff

lemma linear_isometry.cont_diff (f : E →ₗᵢ[𝕜] F) : cont_diff 𝕜 n f :=
f.to_continuous_linear_map.cont_diff

lemma linear_isometry_equiv.cont_diff (f : E ≃ₗᵢ[𝕜] F) : cont_diff 𝕜 n f :=
(f : E →L[𝕜] F).cont_diff

/--
The identity is `C^∞`.
-/
lemma cont_diff_id : cont_diff 𝕜 n (id : E → E) :=
is_bounded_linear_map.id.cont_diff

lemma cont_diff_within_at_id {s x} : cont_diff_within_at 𝕜 n (id : E → E) s x :=
cont_diff_id.cont_diff_within_at

lemma cont_diff_at_id {x} : cont_diff_at 𝕜 n (id : E → E) x :=
cont_diff_id.cont_diff_at

lemma cont_diff_on_id {s} : cont_diff_on 𝕜 n (id : E → E) s :=
cont_diff_id.cont_diff_on

/--
Bilinear functions are `C^∞`.
-/
lemma is_bounded_bilinear_map.cont_diff (hb : is_bounded_bilinear_map 𝕜 b) :
  cont_diff 𝕜 n b :=
begin
  suffices h : cont_diff 𝕜 ∞ b, by exact h.of_le le_top,
  rw cont_diff_top_iff_fderiv,
  refine ⟨hb.differentiable, _⟩,
  simp [hb.fderiv],
  exact hb.is_bounded_linear_map_deriv.cont_diff
end

/-- If `f` admits a Taylor series `p` in a set `s`, and `g` is linear, then `g ∘ f` admits a Taylor
series whose `k`-th term is given by `g ∘ (p k)`. -/
lemma has_ftaylor_series_up_to_on.continuous_linear_map_comp (g : F →L[𝕜] G)
  (hf : has_ftaylor_series_up_to_on n f p s) :
  has_ftaylor_series_up_to_on n (g ∘ f) (λ x k, g.comp_continuous_multilinear_map (p x k)) s :=
begin
  set L : Π m : ℕ, (E [×m]→L[𝕜] F) →L[𝕜] (E [×m]→L[𝕜] G) :=
    λ m, continuous_linear_map.comp_continuous_multilinear_mapL 𝕜 (λ _, E) F G g,
  split,
  { exact λ x hx, congr_arg g (hf.zero_eq x hx) },
  { intros m hm x hx,
    convert (L m).has_fderiv_at.comp_has_fderiv_within_at x (hf.fderiv_within m hm x hx) },
  { intros m hm,
    convert (L m).continuous.comp_continuous_on (hf.cont m hm) }
end

/-- Composition by continuous linear maps on the left preserves `C^n` functions in a domain
at a point. -/
lemma cont_diff_within_at.continuous_linear_map_comp (g : F →L[𝕜] G)
  (hf : cont_diff_within_at 𝕜 n f s x) :
  cont_diff_within_at 𝕜 n (g ∘ f) s x :=
begin
  assume m hm,
  rcases hf m hm with ⟨u, hu, p, hp⟩,
  exact ⟨u, hu, _, hp.continuous_linear_map_comp g⟩,
end

/-- Composition by continuous linear maps on the left preserves `C^n` functions in a domain
at a point. -/
lemma cont_diff_at.continuous_linear_map_comp (g : F →L[𝕜] G) (hf : cont_diff_at 𝕜 n f x) :
  cont_diff_at 𝕜 n (g ∘ f) x :=
cont_diff_within_at.continuous_linear_map_comp g hf

/-- Composition by continuous linear maps on the left preserves `C^n` functions on domains. -/
lemma cont_diff_on.continuous_linear_map_comp (g : F →L[𝕜] G) (hf : cont_diff_on 𝕜 n f s) :
  cont_diff_on 𝕜 n (g ∘ f) s :=
λ x hx, (hf x hx).continuous_linear_map_comp g

/-- Composition by continuous linear maps on the left preserves `C^n` functions. -/
lemma cont_diff.continuous_linear_map_comp {f : E → F} (g : F →L[𝕜] G)
  (hf : cont_diff 𝕜 n f) : cont_diff 𝕜 n (λx, g (f x)) :=
cont_diff_on_univ.1 $ cont_diff_on.continuous_linear_map_comp
  _ (cont_diff_on_univ.2 hf)

/-- The iterated derivative within a set of the composition with a linear map on the left is
obtained by applying the linear map to the iterated derivative. -/
lemma continuous_linear_map.iterated_fderiv_within_comp_left
  {f : E → F} (g : F →L[𝕜] G) (hf : cont_diff_on 𝕜 n f s) (hs : unique_diff_on 𝕜 s) (hx : x ∈ s)
  {i : ℕ} (hi : (i : with_top ℕ) ≤ n) :
  iterated_fderiv_within 𝕜 i (g ∘ f) s x =
    g.comp_continuous_multilinear_map (iterated_fderiv_within 𝕜 i f s x) :=
(((hf.ftaylor_series_within hs).continuous_linear_map_comp g).eq_ftaylor_series_of_unique_diff_on
  hi hs hx).symm

/-- The iterated derivative of the composition with a linear map on the left is
obtained by applying the linear map to the iterated derivative. -/
lemma continuous_linear_map.iterated_fderiv_comp_left
  {f : E → F} (g : F →L[𝕜] G) (hf : cont_diff 𝕜 n f) (x : E) {i : ℕ} (hi : (i : with_top ℕ) ≤ n) :
  iterated_fderiv 𝕜 i (g ∘ f) x = g.comp_continuous_multilinear_map (iterated_fderiv 𝕜 i f x) :=
begin
  simp only [← iterated_fderiv_within_univ],
  exact g.iterated_fderiv_within_comp_left hf.cont_diff_on unique_diff_on_univ (mem_univ x) hi,
end

/-- The iterated derivative within a set of the composition with a linear equiv on the left is
obtained by applying the linear equiv to the iterated derivative. This is true without
differentiability assumptions. -/
lemma continuous_linear_equiv.iterated_fderiv_within_comp_left
  (g : F ≃L[𝕜] G) (f : E → F) (hs : unique_diff_on 𝕜 s) (hx : x ∈ s) (i : ℕ) :
  iterated_fderiv_within 𝕜 i (g ∘ f) s x =
    (g : F →L[𝕜] G).comp_continuous_multilinear_map (iterated_fderiv_within 𝕜 i f s x) :=
begin
  induction i with i IH generalizing x,
  { ext1 m,
    simp only [iterated_fderiv_within_zero_apply, continuous_linear_equiv.coe_coe,
      continuous_linear_map.comp_continuous_multilinear_map_coe, embedding_like.apply_eq_iff_eq] },
  { ext1 m,
    rw iterated_fderiv_within_succ_apply_left,
    have Z : fderiv_within 𝕜 (iterated_fderiv_within 𝕜 i (g ∘ f) s) s x =
      fderiv_within 𝕜 (λ y, g.comp_continuous_multilinear_mapL (λ (j : fin i), E)
        (iterated_fderiv_within 𝕜 i f s y)) s x,
      from fderiv_within_congr' (hs x hx) (λ y hy, IH hy) hx,
    simp_rw Z,
    rw (g.comp_continuous_multilinear_mapL (λ (j : fin i), E)).comp_fderiv_within (hs x hx),
    simp only [continuous_linear_map.coe_comp', continuous_linear_equiv.coe_coe, comp_app,
      continuous_linear_equiv.comp_continuous_multilinear_mapL_apply,
      continuous_linear_map.comp_continuous_multilinear_map_coe, embedding_like.apply_eq_iff_eq],
    rw iterated_fderiv_within_succ_apply_left }
end

/-- Composition with a linear isometry on the left preserves the norm of the iterated
derivative within a set. -/
lemma linear_isometry.norm_iterated_fderiv_within_comp_left
  {f : E → F} (g : F →ₗᵢ[𝕜] G) (hf : cont_diff_on 𝕜 n f s) (hs : unique_diff_on 𝕜 s) (hx : x ∈ s)
  {i : ℕ} (hi : (i : with_top ℕ) ≤ n) :
  ‖iterated_fderiv_within 𝕜 i (g ∘ f) s x‖ = ‖iterated_fderiv_within 𝕜 i f s x‖ :=
begin
  have : iterated_fderiv_within 𝕜 i (g ∘ f) s x =
    g.to_continuous_linear_map.comp_continuous_multilinear_map (iterated_fderiv_within 𝕜 i f s x),
      from g.to_continuous_linear_map.iterated_fderiv_within_comp_left hf hs hx hi,
  rw this,
  apply linear_isometry.norm_comp_continuous_multilinear_map
end

/-- Composition with a linear isometry on the left preserves the norm of the iterated
derivative. -/
lemma linear_isometry.norm_iterated_fderiv_comp_left
  {f : E → F} (g : F →ₗᵢ[𝕜] G) (hf : cont_diff 𝕜 n f) (x : E) {i : ℕ} (hi : (i : with_top ℕ) ≤ n) :
  ‖iterated_fderiv 𝕜 i (g ∘ f) x‖ = ‖iterated_fderiv 𝕜 i f x‖ :=
begin
  simp only [← iterated_fderiv_within_univ],
  exact g.norm_iterated_fderiv_within_comp_left hf.cont_diff_on unique_diff_on_univ (mem_univ x) hi
end

/-- Composition with a linear isometry equiv on the left preserves the norm of the iterated
derivative within a set. -/
lemma linear_isometry_equiv.norm_iterated_fderiv_within_comp_left
  (g : F ≃ₗᵢ[𝕜] G) (f : E → F) (hs : unique_diff_on 𝕜 s) (hx : x ∈ s) (i : ℕ) :
  ‖iterated_fderiv_within 𝕜 i (g ∘ f) s x‖ = ‖iterated_fderiv_within 𝕜 i f s x‖ :=
begin
  have : iterated_fderiv_within 𝕜 i (g ∘ f) s x =
    (g : F →L[𝕜] G).comp_continuous_multilinear_map (iterated_fderiv_within 𝕜 i f s x),
    from g.to_continuous_linear_equiv.iterated_fderiv_within_comp_left f hs hx i,
  rw this,
  apply linear_isometry.norm_comp_continuous_multilinear_map g.to_linear_isometry,
end

/-- Composition with a linear isometry equiv on the left preserves the norm of the iterated
derivative. -/
lemma linear_isometry_equiv.norm_iterated_fderiv_comp_left
  (g : F ≃ₗᵢ[𝕜] G) (f : E → F) (x : E) (i : ℕ) :
  ‖iterated_fderiv 𝕜 i (g ∘ f) x‖ = ‖iterated_fderiv 𝕜 i f x‖ :=
begin
  rw [← iterated_fderiv_within_univ, ← iterated_fderiv_within_univ],
  apply g.norm_iterated_fderiv_within_comp_left f unique_diff_on_univ (mem_univ x) i
end

/-- Composition by continuous linear equivs on the left respects higher differentiability at a
point in a domain. -/
lemma continuous_linear_equiv.comp_cont_diff_within_at_iff
  (e : F ≃L[𝕜] G) :
  cont_diff_within_at 𝕜 n (e ∘ f) s x ↔ cont_diff_within_at 𝕜 n f s x :=
⟨λ H, by simpa only [(∘), e.symm.coe_coe, e.symm_apply_apply]
  using H.continuous_linear_map_comp (e.symm : G →L[𝕜] F),
  λ H, H.continuous_linear_map_comp (e : F →L[𝕜] G)⟩

/-- Composition by continuous linear equivs on the left respects higher differentiability at a
point. -/
lemma continuous_linear_equiv.comp_cont_diff_at_iff (e : F ≃L[𝕜] G) :
  cont_diff_at 𝕜 n (e ∘ f) x ↔ cont_diff_at 𝕜 n f x :=
by simp only [← cont_diff_within_at_univ, e.comp_cont_diff_within_at_iff]

/-- Composition by continuous linear equivs on the left respects higher differentiability on
domains. -/
lemma continuous_linear_equiv.comp_cont_diff_on_iff
  (e : F ≃L[𝕜] G) :
  cont_diff_on 𝕜 n (e ∘ f) s ↔ cont_diff_on 𝕜 n f s :=
by simp [cont_diff_on, e.comp_cont_diff_within_at_iff]

/-- Composition by continuous linear equivs on the left respects higher differentiability. -/
lemma continuous_linear_equiv.comp_cont_diff_iff
  (e : F ≃L[𝕜] G) :
  cont_diff 𝕜 n (e ∘ f) ↔ cont_diff 𝕜 n f :=
by simp only [← cont_diff_on_univ, e.comp_cont_diff_on_iff]

/-- If `f` admits a Taylor series `p` in a set `s`, and `g` is linear, then `f ∘ g` admits a Taylor
series in `g ⁻¹' s`, whose `k`-th term is given by `p k (g v₁, ..., g vₖ)` . -/
lemma has_ftaylor_series_up_to_on.comp_continuous_linear_map
  (hf : has_ftaylor_series_up_to_on n f p s) (g : G →L[𝕜] E) :
  has_ftaylor_series_up_to_on n (f ∘ g)
    (λ x k, (p (g x) k).comp_continuous_linear_map (λ _, g)) (g ⁻¹' s) :=
begin
  let A : Π m : ℕ, (E [×m]→L[𝕜] F) → (G [×m]→L[𝕜] F) :=
    λ m h, h.comp_continuous_linear_map (λ _, g),
  have hA : ∀ m, is_bounded_linear_map 𝕜 (A m) :=
    λ m, is_bounded_linear_map_continuous_multilinear_map_comp_linear g,
  split,
  { assume x hx,
    simp only [(hf.zero_eq (g x) hx).symm, function.comp_app],
    change p (g x) 0 (λ (i : fin 0), g 0) = p (g x) 0 0,
    rw continuous_linear_map.map_zero,
    refl },
  { assume m hm x hx,
    convert ((hA m).has_fderiv_at).comp_has_fderiv_within_at x
      ((hf.fderiv_within m hm (g x) hx).comp x (g.has_fderiv_within_at) (subset.refl _)),
    ext y v,
    change p (g x) (nat.succ m) (g ∘ (cons y v)) = p (g x) m.succ (cons (g y) (g ∘ v)),
    rw comp_cons },
  { assume m hm,
    exact (hA m).continuous.comp_continuous_on
      ((hf.cont m hm).comp g.continuous.continuous_on (subset.refl _)) }
end

/-- Composition by continuous linear maps on the right preserves `C^n` functions at a point on
a domain. -/
lemma cont_diff_within_at.comp_continuous_linear_map {x : G}
  (g : G →L[𝕜] E) (hf : cont_diff_within_at 𝕜 n f s (g x)) :
  cont_diff_within_at 𝕜 n (f ∘ g) (g ⁻¹' s) x :=
begin
  assume m hm,
  rcases hf m hm with ⟨u, hu, p, hp⟩,
  refine ⟨g ⁻¹' u, _, _, hp.comp_continuous_linear_map g⟩,
  apply continuous_within_at.preimage_mem_nhds_within',
  { exact g.continuous.continuous_within_at },
  { apply nhds_within_mono (g x) _ hu,
    rw image_insert_eq,
    exact insert_subset_insert (image_preimage_subset g s) }
end

/-- Composition by continuous linear maps on the right preserves `C^n` functions on domains. -/
lemma cont_diff_on.comp_continuous_linear_map
  (hf : cont_diff_on 𝕜 n f s) (g : G →L[𝕜] E) :
  cont_diff_on 𝕜 n (f ∘ g) (g ⁻¹' s) :=
λ x hx, (hf (g x) hx).comp_continuous_linear_map g

/-- Composition by continuous linear maps on the right preserves `C^n` functions. -/
lemma cont_diff.comp_continuous_linear_map {f : E → F} {g : G →L[𝕜] E}
  (hf : cont_diff 𝕜 n f) : cont_diff 𝕜 n (f ∘ g) :=
cont_diff_on_univ.1 $
cont_diff_on.comp_continuous_linear_map (cont_diff_on_univ.2 hf) _

/-- The iterated derivative within a set of the composition with a linear map on the right is
obtained by composing the iterated derivative with the linear map. -/
lemma continuous_linear_map.iterated_fderiv_within_comp_right
  {f : E → F} (g : G →L[𝕜] E) (hf : cont_diff_on 𝕜 n f s)
  (hs : unique_diff_on 𝕜 s) (h's : unique_diff_on 𝕜 (g⁻¹' s)) {x : G}
  (hx : g x ∈ s) {i : ℕ} (hi : (i : with_top ℕ) ≤ n) :
  iterated_fderiv_within 𝕜 i (f ∘ g) (g ⁻¹' s) x =
    (iterated_fderiv_within 𝕜 i f s (g x)).comp_continuous_linear_map (λ _, g) :=
(((hf.ftaylor_series_within hs).comp_continuous_linear_map g).eq_ftaylor_series_of_unique_diff_on
  hi h's hx).symm

/-- The iterated derivative within a set of the composition with a linear equiv on the right is
obtained by composing the iterated derivative with the linear equiv. -/
lemma continuous_linear_equiv.iterated_fderiv_within_comp_right
  (g : G ≃L[𝕜] E) (f : E → F) (hs : unique_diff_on 𝕜 s) {x : G} (hx : g x ∈ s) (i : ℕ) :
  iterated_fderiv_within 𝕜 i (f ∘ g) (g ⁻¹' s) x =
    (iterated_fderiv_within 𝕜 i f s (g x)).comp_continuous_linear_map (λ _, g) :=
begin
  induction i with i IH generalizing x,
  { ext1 m,
    simp only [iterated_fderiv_within_zero_apply,
      continuous_multilinear_map.comp_continuous_linear_map_apply] },
  { ext1 m,
    simp only [continuous_multilinear_map.comp_continuous_linear_map_apply,
      continuous_linear_equiv.coe_coe, iterated_fderiv_within_succ_apply_left],
    have : fderiv_within 𝕜 (iterated_fderiv_within 𝕜 i (f ∘ ⇑g) (⇑g ⁻¹' s)) (⇑g ⁻¹' s) x
      = fderiv_within 𝕜 (λ y, continuous_multilinear_map.comp_continuous_linear_map_equivL _
        (λ (_x : fin i), g) (iterated_fderiv_within 𝕜 i f s (g y))) (g ⁻¹' s) x,
      from fderiv_within_congr' (g.unique_diff_on_preimage_iff.2 hs x hx) (λ y hy, IH hy) hx,
    rw [this],
    rw continuous_linear_equiv.comp_fderiv_within _ (g.unique_diff_on_preimage_iff.2 hs x hx),
    simp only [continuous_linear_map.coe_comp', continuous_linear_equiv.coe_coe, comp_app,
      continuous_multilinear_map.comp_continuous_linear_map_equivL_apply,
      continuous_multilinear_map.comp_continuous_linear_map_apply],
    rw continuous_linear_equiv.comp_right_fderiv_within _ (g.unique_diff_on_preimage_iff.2 hs x hx),
    refl }
end

/-- The iterated derivative of the composition with a linear map on the right is
obtained by composing the iterated derivative with the linear map. -/
lemma continuous_linear_map.iterated_fderiv_comp_right
  (g : G →L[𝕜] E) {f : E → F} (hf : cont_diff 𝕜 n f) (x : G) {i : ℕ} (hi : (i : with_top ℕ) ≤ n) :
  iterated_fderiv 𝕜 i (f ∘ g) x =
    (iterated_fderiv 𝕜 i f (g x)).comp_continuous_linear_map (λ _, g) :=
begin
  simp only [← iterated_fderiv_within_univ],
  apply g.iterated_fderiv_within_comp_right hf.cont_diff_on unique_diff_on_univ unique_diff_on_univ
    (mem_univ _) hi,
end

/-- Composition with a linear isometry on the right preserves the norm of the iterated derivative
within a set. -/
lemma linear_isometry_equiv.norm_iterated_fderiv_within_comp_right
  (g : G ≃ₗᵢ[𝕜] E) (f : E → F) (hs : unique_diff_on 𝕜 s) {x : G} (hx : g x ∈ s) (i : ℕ) :
  ‖iterated_fderiv_within 𝕜 i (f ∘ g) (g ⁻¹' s) x‖ = ‖iterated_fderiv_within 𝕜 i f s (g x)‖ :=
begin
  have : iterated_fderiv_within 𝕜 i (f ∘ g) (g ⁻¹' s) x =
    (iterated_fderiv_within 𝕜 i f s (g x)).comp_continuous_linear_map (λ _, g),
      from g.to_continuous_linear_equiv.iterated_fderiv_within_comp_right f hs hx i,
  rw [this, continuous_multilinear_map.norm_comp_continuous_linear_isometry_equiv]
end

/-- Composition with a linear isometry on the right preserves the norm of the iterated derivative
within a set. -/
lemma linear_isometry_equiv.norm_iterated_fderiv_comp_right
  (g : G ≃ₗᵢ[𝕜] E) (f : E → F) (x : G) (i : ℕ) :
  ‖iterated_fderiv 𝕜 i (f ∘ g) x‖ = ‖iterated_fderiv 𝕜 i f (g x)‖ :=
begin
  simp only [← iterated_fderiv_within_univ],
  apply g.norm_iterated_fderiv_within_comp_right f unique_diff_on_univ (mem_univ (g x)) i,
end

/-- Composition by continuous linear equivs on the right respects higher differentiability at a
point in a domain. -/
lemma continuous_linear_equiv.cont_diff_within_at_comp_iff (e : G ≃L[𝕜] E) :
  cont_diff_within_at 𝕜 n (f ∘ e) (e ⁻¹' s) (e.symm x) ↔
  cont_diff_within_at 𝕜 n f s x :=
begin
  split,
  { assume H,
    simpa [← preimage_comp, (∘)] using H.comp_continuous_linear_map (e.symm : E →L[𝕜] G) },
  { assume H,
    rw [← e.apply_symm_apply x, ← e.coe_coe] at H,
    exact H.comp_continuous_linear_map _ },
end

/-- Composition by continuous linear equivs on the right respects higher differentiability at a
point. -/
lemma continuous_linear_equiv.cont_diff_at_comp_iff (e : G ≃L[𝕜] E) :
  cont_diff_at 𝕜 n (f ∘ e) (e.symm x) ↔ cont_diff_at 𝕜 n f x :=
begin
  rw [← cont_diff_within_at_univ, ← cont_diff_within_at_univ, ← preimage_univ],
  exact e.cont_diff_within_at_comp_iff
end

/-- Composition by continuous linear equivs on the right respects higher differentiability on
domains. -/
lemma continuous_linear_equiv.cont_diff_on_comp_iff (e : G ≃L[𝕜] E) :
  cont_diff_on 𝕜 n (f ∘ e) (e ⁻¹' s) ↔ cont_diff_on 𝕜 n f s :=
begin
  refine ⟨λ H, _, λ H, H.comp_continuous_linear_map (e : G →L[𝕜] E)⟩,
  have A : f = (f ∘ e) ∘ e.symm,
    by { ext y, simp only [function.comp_app], rw e.apply_symm_apply y },
  have B : e.symm ⁻¹' (e ⁻¹' s) = s,
    by { rw [← preimage_comp, e.self_comp_symm], refl },
  rw [A, ← B],
  exact H.comp_continuous_linear_map (e.symm : E →L[𝕜] G)
end

/-- Composition by continuous linear equivs on the right respects higher differentiability. -/
lemma continuous_linear_equiv.cont_diff_comp_iff (e : G ≃L[𝕜] E) :
  cont_diff 𝕜 n (f ∘ e) ↔ cont_diff 𝕜 n f :=
begin
  rw [← cont_diff_on_univ, ← cont_diff_on_univ, ← preimage_univ],
  exact e.cont_diff_on_comp_iff
end

/-- If two functions `f` and `g` admit Taylor series `p` and `q` in a set `s`, then the cartesian
product of `f` and `g` admits the cartesian product of `p` and `q` as a Taylor series. -/
lemma has_ftaylor_series_up_to_on.prod (hf : has_ftaylor_series_up_to_on n f p s)
  {g : E → G} {q : E → formal_multilinear_series 𝕜 E G} (hg : has_ftaylor_series_up_to_on n g q s) :
  has_ftaylor_series_up_to_on n (λ y, (f y, g y)) (λ y k, (p y k).prod (q y k)) s :=
begin
  set L := λ m, continuous_multilinear_map.prodL 𝕜 (λ i : fin m, E) F G,
  split,
  { assume x hx, rw [← hf.zero_eq x hx, ← hg.zero_eq x hx], refl },
  { assume m hm x hx,
    convert (L m).has_fderiv_at.comp_has_fderiv_within_at x
      ((hf.fderiv_within m hm x hx).prod (hg.fderiv_within m hm x hx)) },
  { assume m hm,
    exact (L m).continuous.comp_continuous_on ((hf.cont m hm).prod (hg.cont m hm)) }
end

/-- The cartesian product of `C^n` functions at a point in a domain is `C^n`. -/
lemma cont_diff_within_at.prod {s : set E} {f : E → F} {g : E → G}
  (hf : cont_diff_within_at 𝕜 n f s x) (hg : cont_diff_within_at 𝕜 n g s x) :
  cont_diff_within_at 𝕜 n (λx:E, (f x, g x)) s x :=
begin
  assume m hm,
  rcases hf m hm with ⟨u, hu, p, hp⟩,
  rcases hg m hm with ⟨v, hv, q, hq⟩,
  exact ⟨u ∩ v, filter.inter_mem hu hv, _,
        (hp.mono (inter_subset_left u v)).prod (hq.mono (inter_subset_right u v))⟩
end

/-- The cartesian product of `C^n` functions on domains is `C^n`. -/
lemma cont_diff_on.prod {s : set E} {f : E → F} {g : E → G}
  (hf : cont_diff_on 𝕜 n f s) (hg : cont_diff_on 𝕜 n g s) :
  cont_diff_on 𝕜 n (λ x : E, (f x, g x)) s :=
λ x hx, (hf x hx).prod (hg x hx)

/-- The cartesian product of `C^n` functions at a point is `C^n`. -/
lemma cont_diff_at.prod {f : E → F} {g : E → G}
  (hf : cont_diff_at 𝕜 n f x) (hg : cont_diff_at 𝕜 n g x) :
  cont_diff_at 𝕜 n (λ x : E, (f x, g x)) x :=
cont_diff_within_at_univ.1 $ cont_diff_within_at.prod
  (cont_diff_within_at_univ.2 hf)
  (cont_diff_within_at_univ.2 hg)

/-- The cartesian product of `C^n` functions is `C^n`.-/
lemma cont_diff.prod {f : E → F} {g : E → G} (hf : cont_diff 𝕜 n f) (hg : cont_diff 𝕜 n g) :
  cont_diff 𝕜 n (λ x : E, (f x, g x)) :=
cont_diff_on_univ.1 $ cont_diff_on.prod (cont_diff_on_univ.2 hf)
  (cont_diff_on_univ.2 hg)

/-!
### Composition of `C^n` functions

We show that the composition of `C^n` functions is `C^n`. One way to prove it would be to write
the `n`-th derivative of the composition (this is Faà di Bruno's formula) and check its continuity,
but this is very painful. Instead, we go for a simple inductive proof. Assume it is done for `n`.
Then, to check it for `n+1`, one needs to check that the derivative of `g ∘ f` is `C^n`, i.e.,
that `Dg(f x) ⬝ Df(x)` is `C^n`. The term `Dg (f x)` is the composition of two `C^n` functions, so
it is `C^n` by the inductive assumption. The term `Df(x)` is also `C^n`. Then, the matrix
multiplication is the application of a bilinear map (which is `C^∞`, and therefore `C^n`) to
`x ↦ (Dg(f x), Df x)`. As the composition of two `C^n` maps, it is again `C^n`, and we are done.

There is a subtlety in this argument: we apply the inductive assumption to functions on other Banach
spaces. In maths, one would say: prove by induction over `n` that, for all `C^n` maps between all
pairs of Banach spaces, their composition is `C^n`. In Lean, this is fine as long as the spaces
stay in the same universe. This is not the case in the above argument: if `E` lives in universe `u`
and `F` lives in universe `v`, then linear maps from `E` to `F` (to which the derivative of `f`
belongs) is in universe `max u v`. If one could quantify over finitely many universes, the above
proof would work fine, but this is not the case. One could still write the proof considering spaces
in any universe in `u, v, w, max u v, max v w, max u v w`, but it would be extremely tedious and
lead to a lot of duplication. Instead, we formulate the above proof when all spaces live in the same
universe (where everything is fine), and then we deduce the general result by lifting all our spaces
to a common universe. We use the trick that any space `H` is isomorphic through a continuous linear
equiv to `continuous_multilinear_map (λ (i : fin 0), E × F × G) H` to change the universe level,
and then argue that composing with such a linear equiv does not change the fact of being `C^n`,
which we have already proved previously.
-/

/-- Auxiliary lemma proving that the composition of `C^n` functions on domains is `C^n` when all
spaces live in the same universe. Use instead `cont_diff_on.comp` which removes the universe
assumption (but is deduced from this one). -/
private lemma cont_diff_on.comp_same_univ
  {Eu : Type u} [normed_add_comm_group Eu] [normed_space 𝕜 Eu]
  {Fu : Type u} [normed_add_comm_group Fu] [normed_space 𝕜 Fu]
  {Gu : Type u} [normed_add_comm_group Gu] [normed_space 𝕜 Gu]
  {s : set Eu} {t : set Fu} {g : Fu → Gu} {f : Eu → Fu}
  (hg : cont_diff_on 𝕜 n g t) (hf : cont_diff_on 𝕜 n f s) (st : s ⊆ f ⁻¹' t) :
  cont_diff_on 𝕜 n (g ∘ f) s :=
begin
  unfreezingI { induction n using enat.nat_induction with n IH Itop generalizing Eu Fu Gu },
  { rw cont_diff_on_zero at hf hg ⊢,
    exact continuous_on.comp hg hf st },
  { rw cont_diff_on_succ_iff_has_fderiv_within_at at hg ⊢,
    assume x hx,
    rcases (cont_diff_on_succ_iff_has_fderiv_within_at.1 hf) x hx
      with ⟨u, hu, f', hf', f'_diff⟩,
    rcases hg (f x) (st hx) with ⟨v, hv, g', hg', g'_diff⟩,
    rw insert_eq_of_mem hx at hu ⊢,
    have xu : x ∈ u := mem_of_mem_nhds_within hx hu,
    let w := s ∩ (u ∩ f⁻¹' v),
    have wv : w ⊆ f ⁻¹' v := λ y hy, hy.2.2,
    have wu : w ⊆ u := λ y hy, hy.2.1,
    have ws : w ⊆ s := λ y hy, hy.1,
    refine ⟨w, _, λ y, (g' (f y)).comp (f' y), _, _⟩,
    show w ∈ 𝓝[s] x,
    { apply filter.inter_mem self_mem_nhds_within,
      apply filter.inter_mem hu,
      apply continuous_within_at.preimage_mem_nhds_within',
      { rw ← continuous_within_at_inter' hu,
        exact (hf' x xu).differentiable_within_at.continuous_within_at.mono
          (inter_subset_right _ _) },
      { apply nhds_within_mono _ _ hv,
        exact subset.trans (image_subset_iff.mpr st) (subset_insert (f x) t) } },
    show ∀ y ∈ w,
      has_fderiv_within_at (g ∘ f) ((g' (f y)).comp (f' y)) w y,
    { rintros y ⟨ys, yu, yv⟩,
      exact (hg' (f y) yv).comp y ((hf' y yu).mono wu) wv },
    show cont_diff_on 𝕜 n (λ y, (g' (f y)).comp (f' y)) w,
    { have A : cont_diff_on 𝕜 n (λ y, g' (f y)) w :=
        IH g'_diff ((hf.of_le (with_top.coe_le_coe.2 (nat.le_succ n))).mono ws) wv,
      have B : cont_diff_on 𝕜 n f' w := f'_diff.mono wu,
      have C : cont_diff_on 𝕜 n (λ y, (g' (f y), f' y)) w := A.prod B,
      have D : cont_diff_on 𝕜 n (λ p : (Fu →L[𝕜] Gu) × (Eu →L[𝕜] Fu), p.1.comp p.2) univ :=
        is_bounded_bilinear_map_comp.cont_diff.cont_diff_on,
      exact IH D C (subset_univ _) } },
  { rw cont_diff_on_top at hf hg ⊢,
    exact λ n, Itop n (hg n) (hf n) st }
end

/-- The composition of `C^n` functions on domains is `C^n`. -/
lemma cont_diff_on.comp
  {s : set E} {t : set F} {g : F → G} {f : E → F}
  (hg : cont_diff_on 𝕜 n g t) (hf : cont_diff_on 𝕜 n f s) (st : s ⊆ f ⁻¹' t) :
  cont_diff_on 𝕜 n (g ∘ f) s :=
begin
  /- we lift all the spaces to a common universe, as we have already proved the result in this
  situation. -/
  let Eu : Type (max uE uF uG) := ulift E,
  let Fu : Type (max uE uF uG) := ulift.{(max uE uG) uF} F,
  let Gu : Type (max uE uF uG) := ulift.{(max uE uF) uG} G,
  -- declare the isomorphisms
  have isoE : Eu ≃L[𝕜] E := continuous_linear_equiv.ulift,
  have isoF : Fu ≃L[𝕜] F := continuous_linear_equiv.ulift,
  have isoG : Gu ≃L[𝕜] G := continuous_linear_equiv.ulift,
  -- lift the functions to the new spaces, check smoothness there, and then go back.
  let fu : Eu → Fu := (isoF.symm ∘ f) ∘ isoE,
  have fu_diff : cont_diff_on 𝕜 n fu (isoE ⁻¹' s),
    by rwa [isoE.cont_diff_on_comp_iff, isoF.symm.comp_cont_diff_on_iff],
  let gu : Fu → Gu := (isoG.symm ∘ g) ∘ isoF,
  have gu_diff : cont_diff_on 𝕜 n gu (isoF ⁻¹' t),
    by rwa [isoF.cont_diff_on_comp_iff, isoG.symm.comp_cont_diff_on_iff],
  have main : cont_diff_on 𝕜 n (gu ∘ fu) (isoE ⁻¹' s),
  { apply cont_diff_on.comp_same_univ gu_diff fu_diff,
    assume y hy,
    simp only [fu, continuous_linear_equiv.coe_apply, function.comp_app, mem_preimage],
    rw isoF.apply_symm_apply (f (isoE y)),
    exact st hy },
  have : gu ∘ fu = (isoG.symm ∘ (g ∘ f)) ∘ isoE,
  { ext y,
    simp only [function.comp_apply, gu, fu],
    rw isoF.apply_symm_apply (f (isoE y)) },
  rwa [this, isoE.cont_diff_on_comp_iff, isoG.symm.comp_cont_diff_on_iff] at main
end

/-- The composition of `C^n` functions on domains is `C^n`. -/
lemma cont_diff_on.comp'
  {s : set E} {t : set F} {g : F → G} {f : E → F}
  (hg : cont_diff_on 𝕜 n g t) (hf : cont_diff_on 𝕜 n f s) :
  cont_diff_on 𝕜 n (g ∘ f) (s ∩ f⁻¹' t) :=
hg.comp (hf.mono (inter_subset_left _ _)) (inter_subset_right _ _)

/-- The composition of a `C^n` function on a domain with a `C^n` function is `C^n`. -/
lemma cont_diff.comp_cont_diff_on {s : set E} {g : F → G} {f : E → F}
  (hg : cont_diff 𝕜 n g) (hf : cont_diff_on 𝕜 n f s) :
  cont_diff_on 𝕜 n (g ∘ f) s :=
(cont_diff_on_univ.2 hg).comp hf subset_preimage_univ

/-- The composition of `C^n` functions is `C^n`. -/
lemma cont_diff.comp {g : F → G} {f : E → F}
  (hg : cont_diff 𝕜 n g) (hf : cont_diff 𝕜 n f) :
  cont_diff 𝕜 n (g ∘ f) :=
cont_diff_on_univ.1 $ cont_diff_on.comp (cont_diff_on_univ.2 hg)
  (cont_diff_on_univ.2 hf) (subset_univ _)

/-- The composition of `C^n` functions at points in domains is `C^n`. -/
lemma cont_diff_within_at.comp
  {s : set E} {t : set F} {g : F → G} {f : E → F} (x : E)
  (hg : cont_diff_within_at 𝕜 n g t (f x))
  (hf : cont_diff_within_at 𝕜 n f s x) (st : s ⊆ f ⁻¹' t) :
  cont_diff_within_at 𝕜 n (g ∘ f) s x :=
begin
  assume m hm,
  rcases hg.cont_diff_on hm with ⟨u, u_nhd, ut, hu⟩,
  rcases hf.cont_diff_on hm with ⟨v, v_nhd, vs, hv⟩,
  have xmem : x ∈ f ⁻¹' u ∩ v :=
    ⟨(mem_of_mem_nhds_within (mem_insert (f x) _) u_nhd : _),
    mem_of_mem_nhds_within (mem_insert x s) v_nhd⟩,
  have : f ⁻¹' u ∈ 𝓝[insert x s] x,
  { apply hf.continuous_within_at.insert_self.preimage_mem_nhds_within',
    apply nhds_within_mono _ _ u_nhd,
    rw image_insert_eq,
    exact insert_subset_insert (image_subset_iff.mpr st) },
  have Z := ((hu.comp (hv.mono (inter_subset_right (f ⁻¹' u) v)) (inter_subset_left _ _))
    .cont_diff_within_at) xmem m le_rfl,
  have : 𝓝[f ⁻¹' u ∩ v] x = 𝓝[insert x s] x,
  { have A : f ⁻¹' u ∩ v = (insert x s) ∩ (f ⁻¹' u ∩ v),
    { apply subset.antisymm _ (inter_subset_right _ _),
      rintros y ⟨hy1, hy2⟩,
      simp [hy1, hy2, vs hy2] },
    rw [A, ← nhds_within_restrict''],
    exact filter.inter_mem this v_nhd },
  rwa [insert_eq_of_mem xmem, this] at Z,
end

/-- The composition of `C^n` functions at points in domains is `C^n`,
  with a weaker condition on `s` and `t`. -/
lemma cont_diff_within_at.comp_of_mem
  {s : set E} {t : set F} {g : F → G} {f : E → F} (x : E)
  (hg : cont_diff_within_at 𝕜 n g t (f x))
  (hf : cont_diff_within_at 𝕜 n f s x) (hs : t ∈ 𝓝[f '' s] f x) :
  cont_diff_within_at 𝕜 n (g ∘ f) s x :=
(hg.mono_of_mem hs).comp x hf (subset_preimage_image f s)

/-- The composition of `C^n` functions at points in domains is `C^n`. -/
lemma cont_diff_within_at.comp' {s : set E} {t : set F} {g : F → G}
  {f : E → F} (x : E)
  (hg : cont_diff_within_at 𝕜 n g t (f x)) (hf : cont_diff_within_at 𝕜 n f s x) :
  cont_diff_within_at 𝕜 n (g ∘ f) (s ∩ f⁻¹' t) x :=
hg.comp x (hf.mono (inter_subset_left _ _)) (inter_subset_right _ _)

lemma cont_diff_at.comp_cont_diff_within_at {n} (x : E)
  (hg : cont_diff_at 𝕜 n g (f x)) (hf : cont_diff_within_at 𝕜 n f s x) :
  cont_diff_within_at 𝕜 n (g ∘ f) s x :=
hg.comp x hf (maps_to_univ _ _)

/-- The composition of `C^n` functions at points is `C^n`. -/
lemma cont_diff_at.comp (x : E)
  (hg : cont_diff_at 𝕜 n g (f x))
  (hf : cont_diff_at 𝕜 n f x) :
  cont_diff_at 𝕜 n (g ∘ f) x :=
hg.comp x hf subset_preimage_univ

lemma cont_diff.comp_cont_diff_within_at
  {g : F → G} {f : E → F} (h : cont_diff 𝕜 n g)
  (hf : cont_diff_within_at 𝕜 n f t x) :
  cont_diff_within_at 𝕜 n (g ∘ f) t x :=
begin
  have : cont_diff_within_at 𝕜 n g univ (f x) :=
    h.cont_diff_at.cont_diff_within_at,
  exact this.comp x hf (subset_univ _),
end

lemma cont_diff.comp_cont_diff_at {g : F → G} {f : E → F} (x : E)
  (hg : cont_diff 𝕜 n g) (hf : cont_diff_at 𝕜 n f x) : cont_diff_at 𝕜 n (g ∘ f) x :=
hg.comp_cont_diff_within_at hf

/-!
### Smoothness of projections
-/

/-- The first projection in a product is `C^∞`. -/
lemma cont_diff_fst : cont_diff 𝕜 n (prod.fst : E × F → E) :=
is_bounded_linear_map.cont_diff is_bounded_linear_map.fst

/-- Postcomposing `f` with `prod.fst` is `C^n` -/
lemma cont_diff.fst {f : E → F × G} (hf : cont_diff 𝕜 n f) : cont_diff 𝕜 n (λ x, (f x).1) :=
cont_diff_fst.comp hf

/-- Precomposing `f` with `prod.fst` is `C^n` -/
lemma cont_diff.fst' {f : E → G} (hf : cont_diff 𝕜 n f) : cont_diff 𝕜 n (λ x : E × F, f x.1) :=
hf.comp cont_diff_fst

/-- The first projection on a domain in a product is `C^∞`. -/
lemma cont_diff_on_fst {s : set (E × F)} : cont_diff_on 𝕜 n (prod.fst : E × F → E) s :=
cont_diff.cont_diff_on cont_diff_fst

lemma cont_diff_on.fst {f : E → F × G} {s : set E} (hf : cont_diff_on 𝕜 n f s) :
  cont_diff_on 𝕜 n (λ x, (f x).1) s :=
cont_diff_fst.comp_cont_diff_on hf

/-- The first projection at a point in a product is `C^∞`. -/
lemma cont_diff_at_fst {p : E × F} : cont_diff_at 𝕜 n (prod.fst : E × F → E) p :=
cont_diff_fst.cont_diff_at

/-- Postcomposing `f` with `prod.fst` is `C^n` at `(x, y)` -/
lemma cont_diff_at.fst {f : E → F × G} {x : E} (hf : cont_diff_at 𝕜 n f x) :
  cont_diff_at 𝕜 n (λ x, (f x).1) x :=
cont_diff_at_fst.comp x hf

/-- Precomposing `f` with `prod.fst` is `C^n` at `(x, y)` -/
lemma cont_diff_at.fst' {f : E → G} {x : E} {y : F} (hf : cont_diff_at 𝕜 n f x) :
  cont_diff_at 𝕜 n (λ x : E × F, f x.1) (x, y) :=
cont_diff_at.comp (x, y) hf cont_diff_at_fst

/-- Precomposing `f` with `prod.fst` is `C^n` at `x : E × F` -/
lemma cont_diff_at.fst'' {f : E → G} {x : E × F} (hf : cont_diff_at 𝕜 n f x.1) :
  cont_diff_at 𝕜 n (λ x : E × F, f x.1) x :=
hf.comp x cont_diff_at_fst

/-- The first projection within a domain at a point in a product is `C^∞`. -/
lemma cont_diff_within_at_fst {s : set (E × F)} {p : E × F} :
  cont_diff_within_at 𝕜 n (prod.fst : E × F → E) s p :=
cont_diff_fst.cont_diff_within_at

/-- The second projection in a product is `C^∞`. -/
lemma cont_diff_snd : cont_diff 𝕜 n (prod.snd : E × F → F) :=
is_bounded_linear_map.cont_diff is_bounded_linear_map.snd

/-- Postcomposing `f` with `prod.snd` is `C^n` -/
lemma cont_diff.snd {f : E → F × G} (hf : cont_diff 𝕜 n f) : cont_diff 𝕜 n (λ x, (f x).2) :=
cont_diff_snd.comp hf

/-- Precomposing `f` with `prod.snd` is `C^n` -/
lemma cont_diff.snd' {f : F → G} (hf : cont_diff 𝕜 n f) : cont_diff 𝕜 n (λ x : E × F, f x.2) :=
hf.comp cont_diff_snd

/-- The second projection on a domain in a product is `C^∞`. -/
lemma cont_diff_on_snd {s : set (E × F)} : cont_diff_on 𝕜 n (prod.snd : E × F → F) s :=
cont_diff.cont_diff_on cont_diff_snd

lemma cont_diff_on.snd {f : E → F × G} {s : set E} (hf : cont_diff_on 𝕜 n f s) :
  cont_diff_on 𝕜 n (λ x, (f x).2) s :=
cont_diff_snd.comp_cont_diff_on hf

/-- The second projection at a point in a product is `C^∞`. -/
lemma cont_diff_at_snd {p : E × F} : cont_diff_at 𝕜 n (prod.snd : E × F → F) p :=
cont_diff_snd.cont_diff_at

/-- Postcomposing `f` with `prod.snd` is `C^n` at `x` -/
lemma cont_diff_at.snd {f : E → F × G} {x : E} (hf : cont_diff_at 𝕜 n f x) :
  cont_diff_at 𝕜 n (λ x, (f x).2) x :=
cont_diff_at_snd.comp x hf

/-- Precomposing `f` with `prod.snd` is `C^n` at `(x, y)` -/
lemma cont_diff_at.snd' {f : F → G} {x : E} {y : F} (hf : cont_diff_at 𝕜 n f y) :
  cont_diff_at 𝕜 n (λ x : E × F, f x.2) (x, y) :=
cont_diff_at.comp (x, y) hf cont_diff_at_snd

/-- Precomposing `f` with `prod.snd` is `C^n` at `x : E × F` -/
lemma cont_diff_at.snd'' {f : F → G} {x : E × F} (hf : cont_diff_at 𝕜 n f x.2) :
  cont_diff_at 𝕜 n (λ x : E × F, f x.2) x :=
hf.comp x cont_diff_at_snd

/-- The second projection within a domain at a point in a product is `C^∞`. -/
lemma cont_diff_within_at_snd {s : set (E × F)} {p : E × F} :
  cont_diff_within_at 𝕜 n (prod.snd : E × F → F) s p :=
cont_diff_snd.cont_diff_within_at

section n_ary

variables {E₁ E₂ E₃ E₄ : Type*}
variables [normed_add_comm_group E₁] [normed_add_comm_group E₂] [normed_add_comm_group E₃]
  [normed_add_comm_group E₄] [normed_space 𝕜 E₁] [normed_space 𝕜 E₂] [normed_space 𝕜 E₃]
  [normed_space 𝕜 E₄]

lemma cont_diff.comp₂ {g : E₁ × E₂ → G} {f₁ : F → E₁} {f₂ : F → E₂}
  (hg : cont_diff 𝕜 n g) (hf₁ : cont_diff 𝕜 n f₁) (hf₂ : cont_diff 𝕜 n f₂) :
  cont_diff 𝕜 n (λ x, g (f₁ x, f₂ x)) :=
hg.comp $ hf₁.prod hf₂

lemma cont_diff.comp₃ {g : E₁ × E₂ × E₃ → G} {f₁ : F → E₁} {f₂ : F → E₂} {f₃ : F → E₃}
  (hg : cont_diff 𝕜 n g) (hf₁ : cont_diff 𝕜 n f₁) (hf₂ : cont_diff 𝕜 n f₂)
  (hf₃ : cont_diff 𝕜 n f₃) : cont_diff 𝕜 n (λ x, g (f₁ x, f₂ x, f₃ x)) :=
hg.comp₂ hf₁ $ hf₂.prod hf₃

lemma cont_diff.comp_cont_diff_on₂ {g : E₁ × E₂ → G} {f₁ : F → E₁} {f₂ : F → E₂} {s : set F}
  (hg : cont_diff 𝕜 n g) (hf₁ : cont_diff_on 𝕜 n f₁ s) (hf₂ : cont_diff_on 𝕜 n f₂ s) :
  cont_diff_on 𝕜 n (λ x, g (f₁ x, f₂ x)) s :=
hg.comp_cont_diff_on $ hf₁.prod hf₂

lemma cont_diff.comp_cont_diff_on₃ {g : E₁ × E₂ × E₃ → G} {f₁ : F → E₁} {f₂ : F → E₂} {f₃ : F → E₃}
  {s : set F} (hg : cont_diff 𝕜 n g) (hf₁ : cont_diff_on 𝕜 n f₁ s) (hf₂ : cont_diff_on 𝕜 n f₂ s)
  (hf₃ : cont_diff_on 𝕜 n f₃ s) : cont_diff_on 𝕜 n (λ x, g (f₁ x, f₂ x, f₃ x)) s :=
hg.comp_cont_diff_on₂ hf₁ $ hf₂.prod hf₃

end n_ary

section specific_bilinear_maps

lemma cont_diff.clm_comp {g : X → F →L[𝕜] G} {f : X → E →L[𝕜] F}
  (hg : cont_diff 𝕜 n g) (hf : cont_diff 𝕜 n f) :
  cont_diff 𝕜 n (λ x, (g x).comp (f x)) :=
is_bounded_bilinear_map_comp.cont_diff.comp₂ hg hf

lemma cont_diff_on.clm_comp {g : X → F →L[𝕜] G} {f : X → E →L[𝕜] F}
  {s : set X} (hg : cont_diff_on 𝕜 n g s) (hf : cont_diff_on 𝕜 n f s) :
  cont_diff_on 𝕜 n (λ x, (g x).comp (f x)) s :=
is_bounded_bilinear_map_comp.cont_diff.comp_cont_diff_on₂ hg hf

lemma cont_diff.clm_apply {f : E → F →L[𝕜] G} {g : E → F} {n : ℕ∞}
  (hf : cont_diff 𝕜 n f) (hg : cont_diff 𝕜 n g) :
  cont_diff 𝕜 n (λ x, (f x) (g x)) :=
is_bounded_bilinear_map_apply.cont_diff.comp₂ hf hg

lemma cont_diff_on.clm_apply {f : E → F →L[𝕜] G} {g : E → F} {n : ℕ∞}
  (hf : cont_diff_on 𝕜 n f s) (hg : cont_diff_on 𝕜 n g s) :
  cont_diff_on 𝕜 n (λ x, (f x) (g x)) s :=
is_bounded_bilinear_map_apply.cont_diff.comp_cont_diff_on₂ hf hg

lemma cont_diff.smul_right {f : E → F →L[𝕜] 𝕜} {g : E → G} {n : ℕ∞}
  (hf : cont_diff 𝕜 n f) (hg : cont_diff 𝕜 n g) :
  cont_diff 𝕜 n (λ x, (f x).smul_right (g x)) :=
-- giving the following implicit type arguments speeds up elaboration significantly
(@is_bounded_bilinear_map_smul_right 𝕜 _ F _ _ G _ _).cont_diff.comp₂ hf hg

end specific_bilinear_maps

/--
The natural equivalence `(E × F) × G ≃ E × (F × G)` is smooth.

Warning: if you think you need this lemma, it is likely that you can simplify your proof by
reformulating the lemma that you're applying next using the tips in
Note [continuity lemma statement]
-/
lemma cont_diff_prod_assoc : cont_diff 𝕜 ⊤ $ equiv.prod_assoc E F G :=
(linear_isometry_equiv.prod_assoc 𝕜 E F G).cont_diff

/--
The natural equivalence `E × (F × G) ≃ (E × F) × G` is smooth.

Warning: see remarks attached to `cont_diff_prod_assoc`
-/
lemma cont_diff_prod_assoc_symm : cont_diff 𝕜 ⊤ $ (equiv.prod_assoc E F G).symm :=
(linear_isometry_equiv.prod_assoc 𝕜 E F G).symm.cont_diff

/-! ### Bundled derivatives are smooth -/

/-- One direction of `cont_diff_within_at_succ_iff_has_fderiv_within_at`, but where all derivatives
	are taken within the same set. Version for partial derivatives / functions with parameters.
	If `f x` is a `C^n+1` family of functions and `g x` is a `C^n` family of points, then the
  derivative of `f x` at `g x` depends in a `C^n` way on `x`. We give a general version of this fact
  relative to sets which may not have unique derivatives, in the following form.
	If `f : E × F → G` is `C^n+1` at `(x₀, g(x₀))` in `(s ∪ {x₀}) × t ⊆ E × F` and `g : E → F` is
	`C^n` at `x₀` within some set `s ⊆ E`, then there is a function `f' : E → F →L[𝕜] G`
	that is `C^n` at `x₀` within `s` such that for all `x` sufficiently close to `x₀` within
	`s ∪ {x₀}` the function `y ↦ f x y` has derivative `f' x` at `g x` within `t ⊆ F`.
	For convenience, we return an explicit set of `x`'s where this holds that is a subset of
	`s ∪ {x₀}`.
	We need one additional condition, namely that `t` is a neighborhood of `g(x₀)` within `g '' s`.
	-/
lemma cont_diff_within_at.has_fderiv_within_at_nhds {f : E → F → G} {g : E → F}
  {t : set F} {n : ℕ} {x₀ : E}
  (hf : cont_diff_within_at 𝕜 (n+1) (uncurry f) (insert x₀ s ×ˢ t) (x₀, g x₀))
  (hg : cont_diff_within_at 𝕜 n g s x₀)
  (hgt : t ∈ 𝓝[g '' s] g x₀) :
  ∃ v ∈ 𝓝[insert x₀ s] x₀, v ⊆ insert x₀ s ∧ ∃ f' : E → F →L[𝕜] G,
    (∀ x ∈ v, has_fderiv_within_at (f x) (f' x) t (g x)) ∧
    cont_diff_within_at 𝕜 n (λ x, f' x) s x₀ :=
begin
  have hst : insert x₀ s ×ˢ t ∈ 𝓝[(λ x, (x, g x)) '' s] (x₀, g x₀),
  { refine nhds_within_mono _ _ (nhds_within_prod self_mem_nhds_within hgt),
    simp_rw [image_subset_iff, mk_preimage_prod, preimage_id', subset_inter_iff, subset_insert,
      true_and, subset_preimage_image] },
  obtain ⟨v, hv, hvs, f', hvf', hf'⟩ := cont_diff_within_at_succ_iff_has_fderiv_within_at'.mp hf,
  refine ⟨(λ z, (z, g z)) ⁻¹' v ∩ insert x₀ s, _, inter_subset_right _ _,
    λ z, (f' (z, g z)).comp (continuous_linear_map.inr 𝕜 E F), _, _⟩,
  { refine inter_mem _ self_mem_nhds_within,
    have := mem_of_mem_nhds_within (mem_insert _ _) hv,
    refine mem_nhds_within_insert.mpr ⟨this, _⟩,
    refine (continuous_within_at_id.prod hg.continuous_within_at).preimage_mem_nhds_within' _,
    rw [← nhds_within_le_iff] at hst hv ⊢,
    refine (hst.trans $ nhds_within_mono _ $ subset_insert _ _).trans hv },
  { intros z hz,
    have := hvf' (z, g z) hz.1,
    refine this.comp _ (has_fderiv_at_prod_mk_right _ _).has_fderiv_within_at _,
    exact maps_to'.mpr (image_prod_mk_subset_prod_right hz.2) },
  { exact (hf'.continuous_linear_map_comp $ (continuous_linear_map.compL 𝕜 F (E × F) G).flip
      (continuous_linear_map.inr 𝕜 E F)).comp_of_mem x₀
      (cont_diff_within_at_id.prod hg) hst },
end

/-- The most general lemma stating that `x ↦ fderiv_within 𝕜 (f x) t (g x)` is `C^n`
at a point within a set.
To show that `x ↦ D_yf(x,y)g(x)` (taken within `t`) is `C^m` at `x₀` within `s`, we require that
* `f` is `C^n` at `(x₀, g(x₀))` within `(s ∪ {x₀}) × t` for `n ≥ m+1`.
* `g` is `C^m` at `x₀` within `s`;
* Derivatives are unique at `g(x)` within `t` for `x` sufficiently close to `x₀` within `s ∪ {x₀}`;
* `t` is a neighborhood of `g(x₀)` within `g '' s`; -/
lemma cont_diff_within_at.fderiv_within'' {f : E → F → G} {g : E → F}
  {t : set F} {n : ℕ∞}
  (hf : cont_diff_within_at 𝕜 n (function.uncurry f) (insert x₀ s ×ˢ t) (x₀, g x₀))
  (hg : cont_diff_within_at 𝕜 m g s x₀)
  (ht : ∀ᶠ x in 𝓝[insert x₀ s] x₀, unique_diff_within_at 𝕜 t (g x))
  (hmn : m + 1 ≤ n)
  (hgt : t ∈ 𝓝[g '' s] g x₀) :
  cont_diff_within_at 𝕜 m (λ x, fderiv_within 𝕜 (f x) t (g x)) s x₀ :=
begin
  have : ∀ k : ℕ, (k : ℕ∞) ≤ m →
    cont_diff_within_at 𝕜 k (λ x, fderiv_within 𝕜 (f x) t (g x)) s x₀,
  { intros k hkm,
    obtain ⟨v, hv, -, f', hvf', hf'⟩ :=
      (hf.of_le $ (add_le_add_right hkm 1).trans hmn).has_fderiv_within_at_nhds (hg.of_le hkm) hgt,
    refine hf'.congr_of_eventually_eq_insert _,
    filter_upwards [hv, ht],
    exact λ y hy h2y, (hvf' y hy).fderiv_within h2y },
  induction m using with_top.rec_top_coe,
  { obtain rfl := eq_top_iff.mpr hmn,
    rw [cont_diff_within_at_top],
    exact λ m, this m le_top },
  exact this m le_rfl
end

/-- A special case of `cont_diff_within_at.fderiv_within''` where we require that `s ⊆ g⁻¹(t)`. -/
lemma cont_diff_within_at.fderiv_within' {f : E → F → G} {g : E → F}
  {t : set F} {n : ℕ∞}
  (hf : cont_diff_within_at 𝕜 n (function.uncurry f) (insert x₀ s ×ˢ t) (x₀, g x₀))
  (hg : cont_diff_within_at 𝕜 m g s x₀)
  (ht : ∀ᶠ x in 𝓝[insert x₀ s] x₀, unique_diff_within_at 𝕜 t (g x))
  (hmn : m + 1 ≤ n)
  (hst : s ⊆ g ⁻¹' t) :
  cont_diff_within_at 𝕜 m (λ x, fderiv_within 𝕜 (f x) t (g x)) s x₀ :=
hf.fderiv_within'' hg ht hmn $ mem_of_superset self_mem_nhds_within $ image_subset_iff.mpr hst

/-- A special case of `cont_diff_within_at.fderiv_within'` where we require that `x₀ ∈ s` and there
  are unique derivatives everywhere within `t`. -/
lemma cont_diff_within_at.fderiv_within {f : E → F → G} {g : E → F}
  {t : set F} {n : ℕ∞}
  (hf : cont_diff_within_at 𝕜 n (function.uncurry f) (s ×ˢ t) (x₀, g x₀))
  (hg : cont_diff_within_at 𝕜 m g s x₀)
  (ht : unique_diff_on 𝕜 t)
  (hmn : m + 1 ≤ n) (hx₀ : x₀ ∈ s)
  (hst : s ⊆ g ⁻¹' t) :
  cont_diff_within_at 𝕜 m (λ x, fderiv_within 𝕜 (f x) t (g x)) s x₀ :=
begin
  rw [← insert_eq_self.mpr hx₀] at hf,
  refine hf.fderiv_within' hg _ hmn hst,
  rw [insert_eq_self.mpr hx₀],
  exact eventually_of_mem self_mem_nhds_within (λ x hx, ht _ (hst hx))
end

/-- `x ↦ fderiv_within 𝕜 (f x) t (g x) (k x)` is smooth at a point within a set. -/
lemma cont_diff_within_at.fderiv_within_apply {f : E → F → G} {g k : E → F}
  {t : set F} {n : ℕ∞}
  (hf : cont_diff_within_at 𝕜 n (function.uncurry f) (s ×ˢ t) (x₀, g x₀))
  (hg : cont_diff_within_at 𝕜 m g s x₀)
  (hk : cont_diff_within_at 𝕜 m k s x₀)
  (ht : unique_diff_on 𝕜 t)
  (hmn : m + 1 ≤ n) (hx₀ : x₀ ∈ s)
  (hst : s ⊆ g ⁻¹' t) :
  cont_diff_within_at 𝕜 m (λ x, fderiv_within 𝕜 (f x) t (g x) (k x)) s x₀ :=
(cont_diff_fst.clm_apply cont_diff_snd).cont_diff_at.comp_cont_diff_within_at x₀
  ((hf.fderiv_within hg ht hmn hx₀ hst).prod hk)

/-- `fderiv_within 𝕜 f s` is smooth at `x₀` within `s`. -/
lemma cont_diff_within_at.fderiv_within_right
  (hf : cont_diff_within_at 𝕜 n f s x₀) (hs : unique_diff_on 𝕜 s)
  (hmn : (m + 1 : ℕ∞) ≤ n) (hx₀s : x₀ ∈ s) :
  cont_diff_within_at 𝕜 m (fderiv_within 𝕜 f s) s x₀ :=
cont_diff_within_at.fderiv_within
  (cont_diff_within_at.comp (x₀, x₀) hf cont_diff_within_at_snd $ prod_subset_preimage_snd s s)
  cont_diff_within_at_id hs hmn hx₀s (by rw [preimage_id'])

/-- `x ↦ fderiv 𝕜 (f x) (g x)` is smooth at `x₀`. -/
lemma cont_diff_at.fderiv {f : E → F → G} {g : E → F} {n : ℕ∞}
  (hf : cont_diff_at 𝕜 n (function.uncurry f) (x₀, g x₀))
  (hg : cont_diff_at 𝕜 m g x₀)
  (hmn : m + 1 ≤ n) :
  cont_diff_at 𝕜 m (λ x, fderiv 𝕜 (f x) (g x)) x₀ :=
begin
  simp_rw [← fderiv_within_univ],
  refine (cont_diff_within_at.fderiv_within hf.cont_diff_within_at hg.cont_diff_within_at
    unique_diff_on_univ hmn (mem_univ x₀) _).cont_diff_at univ_mem,
  rw [preimage_univ]
end

/-- `fderiv 𝕜 f` is smooth at `x₀`. -/
lemma cont_diff_at.fderiv_right (hf : cont_diff_at 𝕜 n f x₀) (hmn : (m + 1 : ℕ∞) ≤ n) :
  cont_diff_at 𝕜 m (fderiv 𝕜 f) x₀ :=
cont_diff_at.fderiv (cont_diff_at.comp (x₀, x₀) hf cont_diff_at_snd) cont_diff_at_id hmn

/-- `x ↦ fderiv 𝕜 (f x) (g x)` is smooth. -/
lemma cont_diff.fderiv {f : E → F → G} {g : E → F} {n m : ℕ∞}
  (hf : cont_diff 𝕜 m $ function.uncurry f) (hg : cont_diff 𝕜 n g) (hnm : n + 1 ≤ m) :
    cont_diff 𝕜 n (λ x, fderiv 𝕜 (f x) (g x)) :=
cont_diff_iff_cont_diff_at.mpr $ λ x, hf.cont_diff_at.fderiv hg.cont_diff_at hnm

/-- `fderiv 𝕜 f` is smooth. -/
lemma cont_diff.fderiv_right (hf : cont_diff 𝕜 n f) (hmn : (m + 1 : ℕ∞) ≤ n) :
  cont_diff 𝕜 m (fderiv 𝕜 f) :=
cont_diff_iff_cont_diff_at.mpr $ λ x, hf.cont_diff_at.fderiv_right hmn

/-- `x ↦ fderiv 𝕜 (f x) (g x)` is continuous. -/
lemma continuous.fderiv {f : E → F → G} {g : E → F} {n : ℕ∞}
  (hf : cont_diff 𝕜 n $ function.uncurry f) (hg : continuous g) (hn : 1 ≤ n) :
    continuous (λ x, fderiv 𝕜 (f x) (g x)) :=
(hf.fderiv (cont_diff_zero.mpr hg) hn).continuous

/-- `x ↦ fderiv 𝕜 (f x) (g x) (k x)` is smooth. -/
lemma cont_diff.fderiv_apply {f : E → F → G} {g k : E → F} {n m : ℕ∞}
  (hf : cont_diff 𝕜 m $ function.uncurry f) (hg : cont_diff 𝕜 n g) (hk : cont_diff 𝕜 n k)
  (hnm : n + 1 ≤ m) :
  cont_diff 𝕜 n (λ x, fderiv 𝕜 (f x) (g x) (k x)) :=
(hf.fderiv hg hnm).clm_apply hk

/-- The bundled derivative of a `C^{n+1}` function is `C^n`. -/
lemma cont_diff_on_fderiv_within_apply {m n : ℕ∞} {s : set E}
  {f : E → F} (hf : cont_diff_on 𝕜 n f s) (hs : unique_diff_on 𝕜 s) (hmn : m + 1 ≤ n) :
  cont_diff_on 𝕜 m (λp : E × E, (fderiv_within 𝕜 f s p.1 : E →L[𝕜] F) p.2) (s ×ˢ univ) :=
((hf.fderiv_within hs hmn).comp cont_diff_on_fst (prod_subset_preimage_fst _ _)).clm_apply
  cont_diff_on_snd

/-- If a function is at least `C^1`, its bundled derivative (mapping `(x, v)` to `Df(x) v`) is
continuous. -/
lemma cont_diff_on.continuous_on_fderiv_within_apply
  (hf : cont_diff_on 𝕜 n f s) (hs : unique_diff_on 𝕜 s) (hn : 1 ≤ n) :
  continuous_on (λp : E × E, (fderiv_within 𝕜 f s p.1 : E → F) p.2) (s ×ˢ univ) :=
(cont_diff_on_fderiv_within_apply hf hs $ by rwa [zero_add]).continuous_on

/-- The bundled derivative of a `C^{n+1}` function is `C^n`. -/
lemma cont_diff.cont_diff_fderiv_apply {f : E → F}
  (hf : cont_diff 𝕜 n f) (hmn : m + 1 ≤ n) :
  cont_diff 𝕜 m (λp : E × E, (fderiv 𝕜 f p.1 : E →L[𝕜] F) p.2) :=
begin
  rw ← cont_diff_on_univ at ⊢ hf,
  rw [← fderiv_within_univ, ← univ_prod_univ],
  exact cont_diff_on_fderiv_within_apply hf unique_diff_on_univ hmn
end

/-!
### Smoothness of functions `f : E → Π i, F' i`
-/

section pi

variables {ι ι' : Type*} [fintype ι] [fintype ι'] {F' : ι → Type*}
  [Π i, normed_add_comm_group (F' i)] [Π i, normed_space 𝕜 (F' i)] {φ : Π i, E → F' i}
  {p' : Π i, E → formal_multilinear_series 𝕜 E (F' i)}
  {Φ : E → Π i, F' i} {P' : E → formal_multilinear_series 𝕜 E (Π i, F' i)}

lemma has_ftaylor_series_up_to_on_pi :
  has_ftaylor_series_up_to_on n (λ x i, φ i x)
    (λ x m, continuous_multilinear_map.pi (λ i, p' i x m)) s ↔
    ∀ i, has_ftaylor_series_up_to_on n (φ i) (p' i) s :=
begin
  set pr := @continuous_linear_map.proj 𝕜 _ ι F' _ _ _,
  letI : Π (m : ℕ) (i : ι), normed_space 𝕜 (E [×m]→L[𝕜] (F' i)) := λ m i, infer_instance,
  set L : Π m : ℕ, (Π i, E [×m]→L[𝕜] (F' i)) ≃ₗᵢ[𝕜] (E [×m]→L[𝕜] (Π i, F' i)) :=
    λ m, continuous_multilinear_map.piₗᵢ _ _,
  refine ⟨λ h i, _, λ h, ⟨λ x hx, _, _, _⟩⟩,
  { convert h.continuous_linear_map_comp (pr i),
    ext, refl },
  { ext1 i,
    exact (h i).zero_eq x hx },
  { intros m hm x hx,
    have := has_fderiv_within_at_pi.2 (λ i, (h i).fderiv_within m hm x hx),
    convert (L m).has_fderiv_at.comp_has_fderiv_within_at x this },
  { intros m hm,
    have := continuous_on_pi.2 (λ i, (h i).cont m hm),
    convert (L m).continuous.comp_continuous_on this }
end

@[simp] lemma has_ftaylor_series_up_to_on_pi' :
  has_ftaylor_series_up_to_on n Φ P' s ↔
    ∀ i, has_ftaylor_series_up_to_on n (λ x, Φ x i)
      (λ x m, (@continuous_linear_map.proj 𝕜 _ ι F' _ _ _ i).comp_continuous_multilinear_map
        (P' x m)) s :=
by { convert has_ftaylor_series_up_to_on_pi, ext, refl }

lemma cont_diff_within_at_pi :
  cont_diff_within_at 𝕜 n Φ s x ↔
    ∀ i, cont_diff_within_at 𝕜 n (λ x, Φ x i) s x :=
begin
  set pr := @continuous_linear_map.proj 𝕜 _ ι F' _ _ _,
  refine ⟨λ h i, h.continuous_linear_map_comp (pr i), λ h m hm, _⟩,
  choose u hux p hp using λ i, h i m hm,
  exact ⟨⋂ i, u i, filter.Inter_mem.2 hux, _,
    has_ftaylor_series_up_to_on_pi.2 (λ i, (hp i).mono $ Inter_subset _ _)⟩,
end

lemma cont_diff_on_pi :
  cont_diff_on 𝕜 n Φ s ↔ ∀ i, cont_diff_on 𝕜 n (λ x, Φ x i) s :=
⟨λ h i x hx, cont_diff_within_at_pi.1 (h x hx) _,
  λ h x hx, cont_diff_within_at_pi.2 (λ i, h i x hx)⟩

lemma cont_diff_at_pi :
  cont_diff_at 𝕜 n Φ x ↔ ∀ i, cont_diff_at 𝕜 n (λ x, Φ x i) x :=
cont_diff_within_at_pi

lemma cont_diff_pi :
  cont_diff 𝕜 n Φ ↔ ∀ i, cont_diff 𝕜 n (λ x, Φ x i) :=
by simp only [← cont_diff_on_univ, cont_diff_on_pi]

variables (𝕜 E)
lemma cont_diff_apply (i : ι) : cont_diff 𝕜 n (λ (f : ι → E), f i) :=
cont_diff_pi.mp cont_diff_id i

lemma cont_diff_apply_apply (i : ι) (j : ι') : cont_diff 𝕜 n (λ (f : ι → ι' → E), f i j) :=
cont_diff_pi.mp (cont_diff_apply 𝕜 (ι' → E) i) j

variables {𝕜 E}

end pi

/-! ### Sum of two functions -/

section add

/- The sum is smooth. -/
lemma cont_diff_add : cont_diff 𝕜 n (λp : F × F, p.1 + p.2) :=
(is_bounded_linear_map.fst.add is_bounded_linear_map.snd).cont_diff

/-- The sum of two `C^n` functions within a set at a point is `C^n` within this set
at this point. -/
lemma cont_diff_within_at.add {s : set E} {f g : E → F}
  (hf : cont_diff_within_at 𝕜 n f s x) (hg : cont_diff_within_at 𝕜 n g s x) :
  cont_diff_within_at 𝕜 n (λx, f x + g x) s x :=
cont_diff_add.cont_diff_within_at.comp x (hf.prod hg) subset_preimage_univ

/-- The sum of two `C^n` functions at a point is `C^n` at this point. -/
lemma cont_diff_at.add {f g : E → F} (hf : cont_diff_at 𝕜 n f x) (hg : cont_diff_at 𝕜 n g x) :
  cont_diff_at 𝕜 n (λx, f x + g x) x :=
by rw [← cont_diff_within_at_univ] at *; exact hf.add hg

/-- The sum of two `C^n`functions is `C^n`. -/
lemma cont_diff.add {f g : E → F} (hf : cont_diff 𝕜 n f) (hg : cont_diff 𝕜 n g) :
  cont_diff 𝕜 n (λx, f x + g x) :=
cont_diff_add.comp (hf.prod hg)

/-- The sum of two `C^n` functions on a domain is `C^n`. -/
lemma cont_diff_on.add {s : set E} {f g : E → F}
  (hf : cont_diff_on 𝕜 n f s) (hg : cont_diff_on 𝕜 n g s) :
  cont_diff_on 𝕜 n (λx, f x + g x) s :=
λ x hx, (hf x hx).add (hg x hx)

variables {i : ℕ}

/-- The iterated derivative of the sum of two functions is the sum of the iterated derivatives.
See also `iterated_fderiv_within_add_apply'`, which uses the spelling `(λ x, f x + g x)`
instead of `f + g`. -/
lemma iterated_fderiv_within_add_apply {f g : E → F}
  (hf : cont_diff_on 𝕜 i f s) (hg : cont_diff_on 𝕜 i g s) (hu : unique_diff_on 𝕜 s)
  (hx : x ∈ s) :
iterated_fderiv_within 𝕜 i (f + g) s x =
  iterated_fderiv_within 𝕜 i f s x + iterated_fderiv_within 𝕜 i g s x :=
begin
  induction i with i hi generalizing x,
  { ext h, simp },
  { ext h,
    have hi' : (i : ℕ∞) < i+1 :=
      with_top.coe_lt_coe.mpr (nat.lt_succ_self _),
    have hdf : differentiable_on 𝕜 (iterated_fderiv_within 𝕜 i f s) s :=
      hf.differentiable_on_iterated_fderiv_within hi' hu,
    have hdg : differentiable_on 𝕜 (iterated_fderiv_within 𝕜 i g s) s :=
      hg.differentiable_on_iterated_fderiv_within hi' hu,
    have hcdf : cont_diff_on 𝕜 i f s := hf.of_le hi'.le,
    have hcdg : cont_diff_on 𝕜 i g s := hg.of_le hi'.le,
    calc iterated_fderiv_within 𝕜 (i+1) (f + g) s x h
        = fderiv_within 𝕜 (iterated_fderiv_within 𝕜 i (f + g) s) s x (h 0) (fin.tail h) : rfl
    ... = fderiv_within 𝕜 (iterated_fderiv_within 𝕜 i f s + iterated_fderiv_within 𝕜 i g s) s x
              (h 0) (fin.tail h) :
            begin
              congr' 2,
              exact fderiv_within_congr (hu x hx) (λ _, hi hcdf hcdg) (hi hcdf hcdg hx),
            end
    ... = (fderiv_within 𝕜 (iterated_fderiv_within 𝕜 i f s) s +
            fderiv_within 𝕜 (iterated_fderiv_within 𝕜 i g s) s)
              x (h 0) (fin.tail h) :
            by rw [pi.add_def, fderiv_within_add (hu x hx) (hdf x hx) (hdg x hx)]; refl
    ... = (iterated_fderiv_within 𝕜 (i+1) f s + iterated_fderiv_within 𝕜 (i+1) g s) x h : rfl }
end

/-- The iterated derivative of the sum of two functions is the sum of the iterated derivatives.
This is the same as `iterated_fderiv_within_add_apply`, but using the spelling `(λ x, f x + g x)`
instead of `f + g`, which can be handy for some rewrites.
TODO: use one form consistently. -/
lemma iterated_fderiv_within_add_apply' {f g : E → F}
  (hf : cont_diff_on 𝕜 i f s) (hg : cont_diff_on 𝕜 i g s) (hu : unique_diff_on 𝕜 s)
  (hx : x ∈ s) :
iterated_fderiv_within 𝕜 i (λ x, f x + g x) s x =
  iterated_fderiv_within 𝕜 i f s x + iterated_fderiv_within 𝕜 i g s x :=
iterated_fderiv_within_add_apply hf hg hu hx

lemma iterated_fderiv_add_apply {i : ℕ} {f g : E → F} (hf : cont_diff 𝕜 i f)
  (hg : cont_diff 𝕜 i g) :
  iterated_fderiv 𝕜 i (f + g) x = iterated_fderiv 𝕜 i f x + iterated_fderiv 𝕜 i g x :=
begin
  simp_rw [←cont_diff_on_univ, ←iterated_fderiv_within_univ] at hf hg ⊢,
  exact iterated_fderiv_within_add_apply hf hg unique_diff_on_univ (set.mem_univ _),
end

lemma iterated_fderiv_add_apply' {i : ℕ} {f g : E → F} (hf : cont_diff 𝕜 i f)
  (hg : cont_diff 𝕜 i g) :
  iterated_fderiv 𝕜 i (λ x, f x + g x) x = iterated_fderiv 𝕜 i f x + iterated_fderiv 𝕜 i g x :=
iterated_fderiv_add_apply hf hg

end add

/-! ### Negative -/

section neg

/- The negative is smooth. -/
lemma cont_diff_neg : cont_diff 𝕜 n (λp : F, -p) :=
is_bounded_linear_map.id.neg.cont_diff

/-- The negative of a `C^n` function within a domain at a point is `C^n` within this domain at
this point. -/
lemma cont_diff_within_at.neg {s : set E} {f : E → F}
  (hf : cont_diff_within_at 𝕜 n f s x) : cont_diff_within_at 𝕜 n (λx, -f x) s x :=
cont_diff_neg.cont_diff_within_at.comp x hf subset_preimage_univ

/-- The negative of a `C^n` function at a point is `C^n` at this point. -/
lemma cont_diff_at.neg {f : E → F}
  (hf : cont_diff_at 𝕜 n f x) : cont_diff_at 𝕜 n (λx, -f x) x :=
by rw ← cont_diff_within_at_univ at *; exact hf.neg

/-- The negative of a `C^n`function is `C^n`. -/
lemma cont_diff.neg {f : E → F} (hf : cont_diff 𝕜 n f) : cont_diff 𝕜 n (λx, -f x) :=
cont_diff_neg.comp hf

/-- The negative of a `C^n` function on a domain is `C^n`. -/
lemma cont_diff_on.neg {s : set E} {f : E → F}
  (hf : cont_diff_on 𝕜 n f s) : cont_diff_on 𝕜 n (λx, -f x) s :=
λ x hx, (hf x hx).neg

variables {i : ℕ}

lemma iterated_fderiv_within_neg_apply {f : E → F} (hu : unique_diff_on 𝕜 s) (hx : x ∈ s) :
  iterated_fderiv_within 𝕜 i (-f) s x = -iterated_fderiv_within 𝕜 i f s x :=
begin
  induction i with i hi generalizing x,
  { ext h, simp },
  { ext h,
    have hi' : (i : ℕ∞) < i+1 :=
      with_top.coe_lt_coe.mpr (nat.lt_succ_self _),
    calc iterated_fderiv_within 𝕜 (i+1) (-f) s x h
        = fderiv_within 𝕜 (iterated_fderiv_within 𝕜 i (-f) s) s x (h 0) (fin.tail h) : rfl
    ... = fderiv_within 𝕜 (-iterated_fderiv_within 𝕜 i f s) s x
              (h 0) (fin.tail h) :
            begin
              congr' 2,
              exact fderiv_within_congr (hu x hx) (λ _, hi) (hi hx),
            end
    ... = -(fderiv_within 𝕜 (iterated_fderiv_within 𝕜 i f s) s) x (h 0) (fin.tail h) :
            by rw [pi.neg_def, fderiv_within_neg (hu x hx)]; refl
    ... = - (iterated_fderiv_within 𝕜 (i+1) f s) x h : rfl }
end

lemma iterated_fderiv_neg_apply {i : ℕ} {f : E → F} :
  iterated_fderiv 𝕜 i (-f) x = -iterated_fderiv 𝕜 i f x :=
begin
  simp_rw [←iterated_fderiv_within_univ],
  exact iterated_fderiv_within_neg_apply unique_diff_on_univ (set.mem_univ _),
end

end neg

/-! ### Subtraction -/

/-- The difference of two `C^n` functions within a set at a point is `C^n` within this set
at this point. -/
lemma cont_diff_within_at.sub {s : set E} {f g : E → F}
  (hf : cont_diff_within_at 𝕜 n f s x) (hg : cont_diff_within_at 𝕜 n g s x) :
  cont_diff_within_at 𝕜 n (λx, f x - g x) s x :=
by simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- The difference of two `C^n` functions at a point is `C^n` at this point. -/
lemma cont_diff_at.sub {f g : E → F}
  (hf : cont_diff_at 𝕜 n f x) (hg : cont_diff_at 𝕜 n g x) :
  cont_diff_at 𝕜 n (λx, f x - g x) x :=
by simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- The difference of two `C^n` functions on a domain is `C^n`. -/
lemma cont_diff_on.sub {s : set E} {f g : E → F}
  (hf : cont_diff_on 𝕜 n f s) (hg : cont_diff_on 𝕜 n g s) :
  cont_diff_on 𝕜 n (λx, f x - g x) s :=
by simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- The difference of two `C^n` functions is `C^n`. -/
lemma cont_diff.sub {f g : E → F}
  (hf : cont_diff 𝕜 n f) (hg : cont_diff 𝕜 n g) : cont_diff 𝕜 n (λx, f x - g x) :=
by simpa only [sub_eq_add_neg] using hf.add hg.neg

/-! ### Sum of finitely many functions -/

lemma cont_diff_within_at.sum
  {ι : Type*} {f : ι → E → F} {s : finset ι} {t : set E} {x : E}
  (h : ∀ i ∈ s, cont_diff_within_at 𝕜 n (λ x, f i x) t x) :
  cont_diff_within_at 𝕜 n (λ x, (∑ i in s, f i x)) t x :=
begin
  classical,
  induction s using finset.induction_on with i s is IH,
  { simp [cont_diff_within_at_const] },
  { simp only [is, finset.sum_insert, not_false_iff],
    exact (h _ (finset.mem_insert_self i s)).add (IH (λ j hj, h _ (finset.mem_insert_of_mem hj))) }
end

lemma cont_diff_at.sum
  {ι : Type*} {f : ι → E → F} {s : finset ι} {x : E}
  (h : ∀ i ∈ s, cont_diff_at 𝕜 n (λ x, f i x) x) :
  cont_diff_at 𝕜 n (λ x, (∑ i in s, f i x)) x :=
by rw [← cont_diff_within_at_univ] at *; exact cont_diff_within_at.sum h

lemma cont_diff_on.sum
  {ι : Type*} {f : ι → E → F} {s : finset ι} {t : set E}
  (h : ∀ i ∈ s, cont_diff_on 𝕜 n (λ x, f i x) t) :
  cont_diff_on 𝕜 n (λ x, (∑ i in s, f i x)) t :=
λ x hx, cont_diff_within_at.sum (λ i hi, h i hi x hx)

lemma cont_diff.sum
  {ι : Type*} {f : ι → E → F} {s : finset ι}
  (h : ∀ i ∈ s, cont_diff 𝕜 n (λ x, f i x)) :
  cont_diff 𝕜 n (λ x, (∑ i in s, f i x)) :=
by simp only [← cont_diff_on_univ] at *; exact cont_diff_on.sum h

/-! ### Product of two functions -/

section mul_prod

variables {𝔸 𝔸' ι 𝕜' : Type*} [normed_ring 𝔸] [normed_algebra 𝕜 𝔸]
  [normed_comm_ring 𝔸'] [normed_algebra 𝕜 𝔸'] [normed_field 𝕜'] [normed_algebra 𝕜 𝕜']

/- The product is smooth. -/
lemma cont_diff_mul : cont_diff 𝕜 n (λ p : 𝔸 × 𝔸, p.1 * p.2) :=
(continuous_linear_map.mul 𝕜 𝔸).is_bounded_bilinear_map.cont_diff

/-- The product of two `C^n` functions within a set at a point is `C^n` within this set
at this point. -/
lemma cont_diff_within_at.mul {s : set E} {f g : E → 𝔸}
  (hf : cont_diff_within_at 𝕜 n f s x) (hg : cont_diff_within_at 𝕜 n g s x) :
  cont_diff_within_at 𝕜 n (λ x, f x * g x) s x :=
cont_diff_mul.comp_cont_diff_within_at (hf.prod hg)

/-- The product of two `C^n` functions at a point is `C^n` at this point. -/
lemma cont_diff_at.mul {f g : E → 𝔸} (hf : cont_diff_at 𝕜 n f x) (hg : cont_diff_at 𝕜 n g x) :
  cont_diff_at 𝕜 n (λ x, f x * g x) x :=
hf.mul hg

/-- The product of two `C^n` functions on a domain is `C^n`. -/
lemma cont_diff_on.mul {f g : E → 𝔸} (hf : cont_diff_on 𝕜 n f s) (hg : cont_diff_on 𝕜 n g s) :
  cont_diff_on 𝕜 n (λ x, f x * g x) s :=
λ x hx, (hf x hx).mul (hg x hx)

/-- The product of two `C^n`functions is `C^n`. -/
lemma cont_diff.mul {f g : E → 𝔸} (hf : cont_diff 𝕜 n f) (hg : cont_diff 𝕜 n g) :
  cont_diff 𝕜 n (λ x, f x * g x) :=
cont_diff_mul.comp (hf.prod hg)

lemma cont_diff_within_at_prod' {t : finset ι} {f : ι → E → 𝔸'}
  (h : ∀ i ∈ t, cont_diff_within_at 𝕜 n (f i) s x) :
  cont_diff_within_at 𝕜 n (∏ i in t, f i) s x :=
finset.prod_induction f (λ f, cont_diff_within_at 𝕜 n f s x) (λ _ _, cont_diff_within_at.mul)
  (@cont_diff_within_at_const _ _ _ _ _ _ _ _ _ _ _ 1) h

lemma cont_diff_within_at_prod {t : finset ι} {f : ι → E → 𝔸'}
  (h : ∀ i ∈ t, cont_diff_within_at 𝕜 n (f i) s x) :
  cont_diff_within_at 𝕜 n (λ y, ∏ i in t, f i y) s x :=
by simpa only [← finset.prod_apply] using cont_diff_within_at_prod' h

lemma cont_diff_at_prod' {t : finset ι} {f : ι → E → 𝔸'} (h : ∀ i ∈ t, cont_diff_at 𝕜 n (f i) x) :
  cont_diff_at 𝕜 n (∏ i in t, f i) x :=
cont_diff_within_at_prod' h

lemma cont_diff_at_prod {t : finset ι} {f : ι → E → 𝔸'} (h : ∀ i ∈ t, cont_diff_at 𝕜 n (f i) x) :
  cont_diff_at 𝕜 n (λ y, ∏ i in t, f i y) x :=
cont_diff_within_at_prod h

lemma cont_diff_on_prod' {t : finset ι} {f : ι → E → 𝔸'} (h : ∀ i ∈ t, cont_diff_on 𝕜 n (f i) s) :
  cont_diff_on 𝕜 n (∏ i in t, f i) s :=
λ x hx, cont_diff_within_at_prod' (λ i hi, h i hi x hx)

lemma cont_diff_on_prod {t : finset ι} {f : ι → E → 𝔸'} (h : ∀ i ∈ t, cont_diff_on 𝕜 n (f i) s) :
  cont_diff_on 𝕜 n (λ y, ∏ i in t, f i y) s :=
λ x hx, cont_diff_within_at_prod (λ i hi, h i hi x hx)

lemma cont_diff_prod' {t : finset ι} {f : ι → E → 𝔸'} (h : ∀ i ∈ t, cont_diff 𝕜 n (f i)) :
  cont_diff 𝕜 n (∏ i in t, f i) :=
cont_diff_iff_cont_diff_at.mpr $ λ x, cont_diff_at_prod' $ λ i hi, (h i hi).cont_diff_at

lemma cont_diff_prod {t : finset ι} {f : ι → E → 𝔸'} (h : ∀ i ∈ t, cont_diff 𝕜 n (f i)) :
  cont_diff 𝕜 n (λ y, ∏ i in t, f i y) :=
cont_diff_iff_cont_diff_at.mpr $ λ x, cont_diff_at_prod $ λ i hi, (h i hi).cont_diff_at

lemma cont_diff.pow {f : E → 𝔸} (hf : cont_diff 𝕜 n f) :
  ∀ m : ℕ, cont_diff 𝕜 n (λ x, (f x) ^ m)
| 0       := by simpa using cont_diff_const
| (m + 1) := by simpa [pow_succ] using hf.mul (cont_diff.pow m)

lemma cont_diff_within_at.pow {f : E → 𝔸} (hf : cont_diff_within_at 𝕜 n f s x) (m : ℕ) :
  cont_diff_within_at 𝕜 n (λ y, f y ^ m) s x :=
(cont_diff_id.pow m).comp_cont_diff_within_at hf

lemma cont_diff_at.pow {f : E → 𝔸} (hf : cont_diff_at 𝕜 n f x) (m : ℕ) :
  cont_diff_at 𝕜 n (λ y, f y ^ m) x :=
hf.pow m

lemma cont_diff_on.pow {f : E → 𝔸} (hf : cont_diff_on 𝕜 n f s) (m : ℕ) :
  cont_diff_on 𝕜 n (λ y, f y ^ m) s :=
λ y hy, (hf y hy).pow m

lemma cont_diff_within_at.div_const {f : E → 𝕜'} {n}
  (hf : cont_diff_within_at 𝕜 n f s x) (c : 𝕜') :
  cont_diff_within_at 𝕜 n (λ x, f x / c) s x :=
by simpa only [div_eq_mul_inv] using hf.mul cont_diff_within_at_const

lemma cont_diff_at.div_const {f : E → 𝕜'} {n} (hf : cont_diff_at 𝕜 n f x) (c : 𝕜') :
  cont_diff_at 𝕜 n (λ x, f x / c) x :=
hf.div_const c

lemma cont_diff_on.div_const {f : E → 𝕜'} {n} (hf : cont_diff_on 𝕜 n f s) (c : 𝕜') :
  cont_diff_on 𝕜 n (λ x, f x / c) s :=
λ x hx, (hf x hx).div_const c

lemma cont_diff.div_const {f : E → 𝕜'} {n} (hf : cont_diff 𝕜 n f) (c : 𝕜') :
  cont_diff 𝕜 n (λ x, f x / c) :=
by simpa only [div_eq_mul_inv] using hf.mul cont_diff_const

end mul_prod

/-! ### Scalar multiplication -/

section smul

/- The scalar multiplication is smooth. -/
lemma cont_diff_smul : cont_diff 𝕜 n (λ p : 𝕜 × F, p.1 • p.2) :=
is_bounded_bilinear_map_smul.cont_diff

/-- The scalar multiplication of two `C^n` functions within a set at a point is `C^n` within this
set at this point. -/
lemma cont_diff_within_at.smul {s : set E} {f : E → 𝕜} {g : E → F}
  (hf : cont_diff_within_at 𝕜 n f s x) (hg : cont_diff_within_at 𝕜 n g s x) :
  cont_diff_within_at 𝕜 n (λ x, f x • g x) s x :=
cont_diff_smul.cont_diff_within_at.comp x (hf.prod hg) subset_preimage_univ

/-- The scalar multiplication of two `C^n` functions at a point is `C^n` at this point. -/
lemma cont_diff_at.smul {f : E → 𝕜} {g : E → F}
  (hf : cont_diff_at 𝕜 n f x) (hg : cont_diff_at 𝕜 n g x) :
  cont_diff_at 𝕜 n (λ x, f x • g x) x :=
by rw [← cont_diff_within_at_univ] at *; exact hf.smul hg

/-- The scalar multiplication of two `C^n` functions is `C^n`. -/
lemma cont_diff.smul {f : E → 𝕜} {g : E → F} (hf : cont_diff 𝕜 n f) (hg : cont_diff 𝕜 n g) :
  cont_diff 𝕜 n (λ x, f x • g x) :=
cont_diff_smul.comp (hf.prod hg)

/-- The scalar multiplication of two `C^n` functions on a domain is `C^n`. -/
lemma cont_diff_on.smul {s : set E} {f : E → 𝕜} {g : E → F}
  (hf : cont_diff_on 𝕜 n f s) (hg : cont_diff_on 𝕜 n g s) :
  cont_diff_on 𝕜 n (λ x, f x • g x) s :=
λ x hx, (hf x hx).smul (hg x hx)

end smul

/-! ### Constant scalar multiplication -/

section const_smul

variables {R : Type*} [semiring R] [module R F] [smul_comm_class 𝕜 R F]
variables [has_continuous_const_smul R F]

/- The scalar multiplication with a constant is smooth. -/
lemma cont_diff_const_smul (c : R) : cont_diff 𝕜 n (λ p : F, c • p) :=
(c • continuous_linear_map.id 𝕜 F).cont_diff

/-- The scalar multiplication of a constant and a `C^n` function within a set at a point is `C^n`
within this set at this point. -/
lemma cont_diff_within_at.const_smul {s : set E} {f : E → F} {x : E} (c : R)
  (hf : cont_diff_within_at 𝕜 n f s x) : cont_diff_within_at 𝕜 n (λ y, c • f y) s x :=
(cont_diff_const_smul c).cont_diff_at.comp_cont_diff_within_at x hf

/-- The scalar multiplication of a constant and a `C^n` function at a point is `C^n` at this
point. -/
lemma cont_diff_at.const_smul {f : E → F} {x : E} (c : R)
  (hf : cont_diff_at 𝕜 n f x) : cont_diff_at 𝕜 n (λ y, c • f y) x :=
by rw [←cont_diff_within_at_univ] at *; exact hf.const_smul c

/-- The scalar multiplication of a constant and a `C^n` function is `C^n`. -/
lemma cont_diff.const_smul {f : E → F} (c : R)
  (hf : cont_diff 𝕜 n f) : cont_diff 𝕜 n (λ y, c • f y) :=
(cont_diff_const_smul c).comp hf

/-- The scalar multiplication of a constant and a `C^n` on a domain is `C^n`. -/
lemma cont_diff_on.const_smul {s : set E} {f : E → F} (c : R)
  (hf : cont_diff_on 𝕜 n f s) : cont_diff_on 𝕜 n (λ y, c • f y) s :=
λ x hx, (hf x hx).const_smul c

variables {i : ℕ} {a : R}

lemma iterated_fderiv_within_const_smul_apply (hf : cont_diff_on 𝕜 i f s)
  (hu : unique_diff_on 𝕜 s) (hx : x ∈ s) :
iterated_fderiv_within 𝕜 i (a • f) s x = a • (iterated_fderiv_within 𝕜 i f s x) :=
begin
  induction i with i hi generalizing x,
  { ext, simp },
  { ext h,
    have hi' : (i : ℕ∞) < i+1 :=
      with_top.coe_lt_coe.mpr (nat.lt_succ_self _),
    have hdf : differentiable_on 𝕜 (iterated_fderiv_within 𝕜 i f s) s :=
      hf.differentiable_on_iterated_fderiv_within hi' hu,
    have hcdf : cont_diff_on 𝕜 i f s := hf.of_le hi'.le,
    calc iterated_fderiv_within 𝕜 (i+1) (a • f) s x h
        = fderiv_within 𝕜 (iterated_fderiv_within 𝕜 i (a • f) s) s x (h 0) (fin.tail h) : rfl
    ... = fderiv_within 𝕜 (a • iterated_fderiv_within 𝕜 i f s) s x (h 0) (fin.tail h) :
            begin
              congr' 2,
              exact fderiv_within_congr (hu x hx) (λ _, hi hcdf) (hi hcdf hx),
            end
    ... = (a • fderiv_within 𝕜 (iterated_fderiv_within 𝕜 i f s)) s x (h 0) (fin.tail h) :
            by rw [pi.smul_def, fderiv_within_const_smul (hu x hx) (hdf x hx)]; refl
    ... = a • iterated_fderiv_within 𝕜 (i+1) f s x h : rfl }
end

lemma iterated_fderiv_const_smul_apply {x : E} (hf : cont_diff 𝕜 i f) :
  iterated_fderiv 𝕜 i (a • f) x = a • iterated_fderiv 𝕜 i f x :=
begin
  simp_rw [←cont_diff_on_univ, ←iterated_fderiv_within_univ] at *,
  refine iterated_fderiv_within_const_smul_apply hf unique_diff_on_univ (set.mem_univ _),
end

end const_smul

/-! ### Cartesian product of two functions -/

section prod_map
variables {E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
variables {F' : Type*} [normed_add_comm_group F'] [normed_space 𝕜 F']

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
lemma cont_diff_within_at.prod_map'
  {s : set E} {t : set E'} {f : E → F} {g : E' → F'} {p : E × E'}
  (hf : cont_diff_within_at 𝕜 n f s p.1) (hg : cont_diff_within_at 𝕜 n g t p.2) :
  cont_diff_within_at 𝕜 n (prod.map f g) (s ×ˢ t) p :=
(hf.comp p cont_diff_within_at_fst (prod_subset_preimage_fst _ _)).prod
  (hg.comp p cont_diff_within_at_snd (prod_subset_preimage_snd _ _))

lemma cont_diff_within_at.prod_map
  {s : set E} {t : set E'} {f : E → F} {g : E' → F'} {x : E} {y : E'}
  (hf : cont_diff_within_at 𝕜 n f s x) (hg : cont_diff_within_at 𝕜 n g t y) :
  cont_diff_within_at 𝕜 n (prod.map f g) (s ×ˢ t) (x, y) :=
cont_diff_within_at.prod_map' hf hg

/-- The product map of two `C^n` functions on a set is `C^n` on the product set. -/
lemma cont_diff_on.prod_map {E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
  {F' : Type*} [normed_add_comm_group F'] [normed_space 𝕜 F']
  {s : set E} {t : set E'} {f : E → F} {g : E' → F'}
  (hf : cont_diff_on 𝕜 n f s) (hg : cont_diff_on 𝕜 n g t) :
  cont_diff_on 𝕜 n (prod.map f g) (s ×ˢ t) :=
(hf.comp cont_diff_on_fst (prod_subset_preimage_fst _ _)).prod
  (hg.comp (cont_diff_on_snd) (prod_subset_preimage_snd _ _))

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
lemma cont_diff_at.prod_map {f : E → F} {g : E' → F'} {x : E} {y : E'}
  (hf : cont_diff_at 𝕜 n f x) (hg : cont_diff_at 𝕜 n g y) :
  cont_diff_at 𝕜 n (prod.map f g) (x, y) :=
begin
  rw cont_diff_at at *,
  convert hf.prod_map hg,
  simp only [univ_prod_univ]
end

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
lemma cont_diff_at.prod_map' {f : E → F} {g : E' → F'} {p : E × E'}
  (hf : cont_diff_at 𝕜 n f p.1) (hg : cont_diff_at 𝕜 n g p.2) :
  cont_diff_at 𝕜 n (prod.map f g) p :=
begin
  rcases p,
  exact cont_diff_at.prod_map hf hg
end

/-- The product map of two `C^n` functions is `C^n`. -/
lemma cont_diff.prod_map {f : E → F} {g : E' → F'}
  (hf : cont_diff 𝕜 n f) (hg : cont_diff 𝕜 n g) :
  cont_diff 𝕜 n (prod.map f g) :=
begin
  rw cont_diff_iff_cont_diff_at at *,
  exact λ ⟨x, y⟩, (hf x).prod_map (hg y)
end

lemma cont_diff_prod_mk_left (f₀ : F) : cont_diff 𝕜 n (λ e : E, (e, f₀)) :=
cont_diff_id.prod cont_diff_const

lemma cont_diff_prod_mk_right (e₀ : E) : cont_diff 𝕜 n (λ f : F, (e₀, f)) :=
cont_diff_const.prod cont_diff_id

end prod_map

/-! ### Inversion in a complete normed algebra -/

section algebra_inverse
variables (𝕜) {R : Type*} [normed_ring R] [normed_algebra 𝕜 R]
open normed_ring continuous_linear_map ring

/-- In a complete normed algebra, the operation of inversion is `C^n`, for all `n`, at each
invertible element.  The proof is by induction, bootstrapping using an identity expressing the
derivative of inversion as a bilinear map of inversion itself. -/
lemma cont_diff_at_ring_inverse [complete_space R] (x : Rˣ) :
  cont_diff_at 𝕜 n ring.inverse (x : R) :=
begin
  induction n using enat.nat_induction with n IH Itop,
  { intros m hm,
    refine ⟨{y : R | is_unit y}, _, _⟩,
    { simp [nhds_within_univ],
      exact x.nhds },
    { use (ftaylor_series_within 𝕜 inverse univ),
      rw [le_antisymm hm bot_le, has_ftaylor_series_up_to_on_zero_iff],
      split,
      { rintros _ ⟨x', rfl⟩,
        exact (inverse_continuous_at x').continuous_within_at },
      { simp [ftaylor_series_within] } } },
  { apply cont_diff_at_succ_iff_has_fderiv_at.mpr,
    refine ⟨λ (x : R), - mul_left_right 𝕜 R (inverse x) (inverse x), _, _⟩,
    { refine ⟨{y : R | is_unit y}, x.nhds, _⟩,
      rintros _ ⟨y, rfl⟩,
      rw [inverse_unit],
      exact has_fderiv_at_ring_inverse y },
    { convert (mul_left_right_is_bounded_bilinear 𝕜 R).cont_diff.neg.comp_cont_diff_at
        (x : R) (IH.prod IH) } },
  { exact cont_diff_at_top.mpr Itop }
end

variables (𝕜) {𝕜' : Type*} [normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] [complete_space 𝕜']

lemma cont_diff_at_inv {x : 𝕜'} (hx : x ≠ 0) {n} :
  cont_diff_at 𝕜 n has_inv.inv x :=
by simpa only [ring.inverse_eq_inv'] using cont_diff_at_ring_inverse 𝕜 (units.mk0 x hx)

lemma cont_diff_on_inv {n} : cont_diff_on 𝕜 n (has_inv.inv : 𝕜' → 𝕜') {0}ᶜ :=
λ x hx, (cont_diff_at_inv 𝕜 hx).cont_diff_within_at

variable {𝕜}

-- TODO: the next few lemmas don't need `𝕜` or `𝕜'` to be complete
-- A good way to show this is to generalize `cont_diff_at_ring_inverse` to the setting
-- of a function `f` such that `∀ᶠ x in 𝓝 a, x * f x = 1`.

lemma cont_diff_within_at.inv {f : E → 𝕜'} {n} (hf : cont_diff_within_at 𝕜 n f s x)
  (hx : f x ≠ 0) :
  cont_diff_within_at 𝕜 n (λ x, (f x)⁻¹) s x :=
(cont_diff_at_inv 𝕜 hx).comp_cont_diff_within_at x hf

lemma cont_diff_on.inv {f : E → 𝕜'} {n} (hf : cont_diff_on 𝕜 n f s)
  (h : ∀ x ∈ s, f x ≠ 0) :
  cont_diff_on 𝕜 n (λ x, (f x)⁻¹) s :=
λ x hx, (hf.cont_diff_within_at hx).inv (h x hx)

lemma cont_diff_at.inv {f : E → 𝕜'} {n} (hf : cont_diff_at 𝕜 n f x) (hx : f x ≠ 0) :
  cont_diff_at 𝕜 n (λ x, (f x)⁻¹) x :=
hf.inv hx

lemma cont_diff.inv {f : E → 𝕜'} {n} (hf : cont_diff 𝕜 n f) (h : ∀ x, f x ≠ 0) :
  cont_diff 𝕜 n (λ x, (f x)⁻¹) :=
by { rw cont_diff_iff_cont_diff_at, exact λ x, hf.cont_diff_at.inv (h x) }

-- TODO: generalize to `f g : E → 𝕜'`
lemma cont_diff_within_at.div [complete_space 𝕜] {f g : E → 𝕜} {n}
  (hf : cont_diff_within_at 𝕜 n f s x) (hg : cont_diff_within_at 𝕜 n g s x)
  (hx : g x ≠ 0) :
  cont_diff_within_at 𝕜 n (λ x, f x / g x) s x :=
by simpa only [div_eq_mul_inv] using hf.mul (hg.inv hx)

lemma cont_diff_on.div [complete_space 𝕜] {f g : E → 𝕜} {n}
  (hf : cont_diff_on 𝕜 n f s) (hg : cont_diff_on 𝕜 n g s) (h₀ : ∀ x ∈ s, g x ≠ 0) :
  cont_diff_on 𝕜 n (f / g) s :=
λ x hx, (hf x hx).div (hg x hx) (h₀ x hx)

lemma cont_diff_at.div [complete_space 𝕜] {f g : E → 𝕜} {n}
  (hf : cont_diff_at 𝕜 n f x) (hg : cont_diff_at 𝕜 n g x)
  (hx : g x ≠ 0) :
  cont_diff_at 𝕜 n (λ x, f x / g x) x :=
hf.div hg hx

lemma cont_diff.div [complete_space 𝕜] {f g : E → 𝕜} {n}
  (hf : cont_diff 𝕜 n f) (hg : cont_diff 𝕜 n g)
  (h0 : ∀ x, g x ≠ 0) :
  cont_diff 𝕜 n (λ x, f x / g x) :=
begin
  simp only [cont_diff_iff_cont_diff_at] at *,
  exact λ x, (hf x).div (hg x) (h0 x)
end

end algebra_inverse

/-! ### Inversion of continuous linear maps between Banach spaces -/

section map_inverse
open continuous_linear_map

/-- At a continuous linear equivalence `e : E ≃L[𝕜] F` between Banach spaces, the operation of
inversion is `C^n`, for all `n`. -/
lemma cont_diff_at_map_inverse [complete_space E] (e : E ≃L[𝕜] F) :
  cont_diff_at 𝕜 n inverse (e : E →L[𝕜] F) :=
begin
  nontriviality E,
  -- first, we use the lemma `to_ring_inverse` to rewrite in terms of `ring.inverse` in the ring
  -- `E →L[𝕜] E`
  let O₁ : (E →L[𝕜] E) → (F →L[𝕜] E) := λ f, f.comp (e.symm : (F →L[𝕜] E)),
  let O₂ : (E →L[𝕜] F) → (E →L[𝕜] E) := λ f, (e.symm : (F →L[𝕜] E)).comp f,
  have : continuous_linear_map.inverse = O₁ ∘ ring.inverse ∘ O₂ :=
    funext (to_ring_inverse e),
  rw this,
  -- `O₁` and `O₂` are `cont_diff`,
  -- so we reduce to proving that `ring.inverse` is `cont_diff`
  have h₁ : cont_diff 𝕜 n O₁ := cont_diff_id.clm_comp cont_diff_const,
  have h₂ : cont_diff 𝕜 n O₂ := cont_diff_const.clm_comp cont_diff_id,
  refine h₁.cont_diff_at.comp _ (cont_diff_at.comp _ _ h₂.cont_diff_at),
  convert cont_diff_at_ring_inverse 𝕜 (1 : (E →L[𝕜] E)ˣ),
  simp [O₂, one_def]
end

end map_inverse

section function_inverse
open continuous_linear_map

/-- If `f` is a local homeomorphism and the point `a` is in its target,
and if `f` is `n` times continuously differentiable at `f.symm a`,
and if the derivative at `f.symm a` is a continuous linear equivalence,
then `f.symm` is `n` times continuously differentiable at the point `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem local_homeomorph.cont_diff_at_symm [complete_space E]
  (f : local_homeomorph E F) {f₀' : E ≃L[𝕜] F} {a : F} (ha : a ∈ f.target)
  (hf₀' : has_fderiv_at f (f₀' : E →L[𝕜] F) (f.symm a)) (hf : cont_diff_at 𝕜 n f (f.symm a)) :
  cont_diff_at 𝕜 n f.symm a :=
begin
  -- We prove this by induction on `n`
  induction n using enat.nat_induction with n IH Itop,
  { rw cont_diff_at_zero,
    exact ⟨f.target, is_open.mem_nhds f.open_target ha, f.continuous_inv_fun⟩ },
  { obtain ⟨f', ⟨u, hu, hff'⟩, hf'⟩ := cont_diff_at_succ_iff_has_fderiv_at.mp hf,
    apply cont_diff_at_succ_iff_has_fderiv_at.mpr,
    -- For showing `n.succ` times continuous differentiability (the main inductive step), it
    -- suffices to produce the derivative and show that it is `n` times continuously differentiable
    have eq_f₀' : f' (f.symm a) = f₀',
    { exact (hff' (f.symm a) (mem_of_mem_nhds hu)).unique hf₀' },
    -- This follows by a bootstrapping formula expressing the derivative as a function of `f` itself
    refine ⟨inverse ∘ f' ∘ f.symm, _, _⟩,
    { -- We first check that the derivative of `f` is that formula
      have h_nhds : {y : E | ∃ (e : E ≃L[𝕜] F), ↑e = f' y} ∈ 𝓝 ((f.symm) a),
      { have hf₀' := f₀'.nhds,
        rw ← eq_f₀' at hf₀',
        exact hf'.continuous_at.preimage_mem_nhds hf₀' },
      obtain ⟨t, htu, ht, htf⟩ := mem_nhds_iff.mp (filter.inter_mem hu h_nhds),
      use f.target ∩ (f.symm) ⁻¹' t,
      refine ⟨is_open.mem_nhds _ _, _⟩,
      { exact f.preimage_open_of_open_symm ht },
      { exact mem_inter ha (mem_preimage.mpr htf) },
      intros x hx,
      obtain ⟨hxu, e, he⟩ := htu hx.2,
      have h_deriv : has_fderiv_at f ↑e ((f.symm) x),
      { rw he,
        exact hff' (f.symm x) hxu },
      convert f.has_fderiv_at_symm hx.1 h_deriv,
      simp [← he] },
    { -- Then we check that the formula, being a composition of `cont_diff` pieces, is
      -- itself `cont_diff`
      have h_deriv₁ : cont_diff_at 𝕜 n inverse (f' (f.symm a)),
      { rw eq_f₀',
        exact cont_diff_at_map_inverse _ },
      have h_deriv₂ : cont_diff_at 𝕜 n f.symm a,
      { refine IH (hf.of_le _),
        norm_cast,
        exact nat.le_succ n },
      exact (h_deriv₁.comp _ hf').comp _ h_deriv₂ } },
  { refine cont_diff_at_top.mpr _,
    intros n,
    exact Itop n (cont_diff_at_top.mp hf n) }
end

/-- If `f` is an `n` times continuously differentiable homeomorphism,
and if the derivative of `f` at each point is a continuous linear equivalence,
then `f.symm` is `n` times continuously differentiable.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem homeomorph.cont_diff_symm [complete_space E] (f : E ≃ₜ F) {f₀' : E → E ≃L[𝕜] F}
  (hf₀' : ∀ a, has_fderiv_at f (f₀' a : E →L[𝕜] F) a) (hf : cont_diff 𝕜 n (f : E → F)) :
  cont_diff 𝕜 n (f.symm : F → E) :=
cont_diff_iff_cont_diff_at.2 $ λ x,
  f.to_local_homeomorph.cont_diff_at_symm (mem_univ x) (hf₀' _) hf.cont_diff_at

/-- Let `f` be a local homeomorphism of a nontrivially normed field, let `a` be a point in its
target. if `f` is `n` times continuously differentiable at `f.symm a`, and if the derivative at
`f.symm a` is nonzero, then `f.symm` is `n` times continuously differentiable at the point `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem local_homeomorph.cont_diff_at_symm_deriv [complete_space 𝕜]
  (f : local_homeomorph 𝕜 𝕜) {f₀' a : 𝕜} (h₀ : f₀' ≠ 0) (ha : a ∈ f.target)
  (hf₀' : has_deriv_at f f₀' (f.symm a)) (hf : cont_diff_at 𝕜 n f (f.symm a)) :
  cont_diff_at 𝕜 n f.symm a :=
f.cont_diff_at_symm ha (hf₀'.has_fderiv_at_equiv h₀) hf

/-- Let `f` be an `n` times continuously differentiable homeomorphism of a nontrivially normed
field.  Suppose that the derivative of `f` is never equal to zero. Then `f.symm` is `n` times
continuously differentiable.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem homeomorph.cont_diff_symm_deriv [complete_space 𝕜] (f : 𝕜 ≃ₜ 𝕜) {f' : 𝕜 → 𝕜}
  (h₀ : ∀ x, f' x ≠ 0) (hf' : ∀ x, has_deriv_at f (f' x) x) (hf : cont_diff 𝕜 n (f : 𝕜 → 𝕜)) :
  cont_diff 𝕜 n (f.symm : 𝕜 → 𝕜) :=
cont_diff_iff_cont_diff_at.2 $ λ x,
  f.to_local_homeomorph.cont_diff_at_symm_deriv (h₀ _) (mem_univ x) (hf' _) hf.cont_diff_at

end function_inverse


/-! ### Finite dimensional results -/
section finite_dimensional

open function finite_dimensional
variables [complete_space 𝕜]

/-- A family of continuous linear maps is `C^n` on `s` if all its applications are. -/
lemma cont_diff_on_clm_apply {n : ℕ∞} {f : E → F →L[𝕜] G}
  {s : set E} [finite_dimensional 𝕜 F] :
  cont_diff_on 𝕜 n f s ↔ ∀ y, cont_diff_on 𝕜 n (λ x, f x y) s :=
begin
  refine ⟨λ h y, h.clm_apply cont_diff_on_const, λ h, _⟩,
  let d := finrank 𝕜 F,
  have hd : d = finrank 𝕜 (fin d → 𝕜) := (finrank_fin_fun 𝕜).symm,
  let e₁ := continuous_linear_equiv.of_finrank_eq hd,
  let e₂ := (e₁.arrow_congr (1 : G ≃L[𝕜] G)).trans (continuous_linear_equiv.pi_ring (fin d)),
  rw [← comp.left_id f, ← e₂.symm_comp_self],
  exact e₂.symm.cont_diff.comp_cont_diff_on (cont_diff_on_pi.mpr (λ i, h _))
end

lemma cont_diff_clm_apply_iff {n : ℕ∞} {f : E → F →L[𝕜] G} [finite_dimensional 𝕜 F] :
  cont_diff 𝕜 n f ↔ ∀ y, cont_diff 𝕜 n (λ x, f x y) :=
by simp_rw [← cont_diff_on_univ, cont_diff_on_clm_apply]

/-- This is a useful lemma to prove that a certain operation preserves functions being `C^n`.
When you do induction on `n`, this gives a useful characterization of a function being `C^(n+1)`,
assuming you have already computed the derivative. The advantage of this version over
`cont_diff_succ_iff_fderiv` is that both occurences of `cont_diff` are for functions with the same
domain and codomain (`E` and `F`). This is not the case for `cont_diff_succ_iff_fderiv`, which
often requires an inconvenient need to generalize `F`, which results in universe issues
(see the discussion in the section of `cont_diff.comp`).

This lemma avoids these universe issues, but only applies for finite dimensional `E`. -/
lemma cont_diff_succ_iff_fderiv_apply [finite_dimensional 𝕜 E] {n : ℕ} {f : E → F} :
  cont_diff 𝕜 ((n + 1) : ℕ) f ↔
  differentiable 𝕜 f ∧ ∀ y, cont_diff 𝕜 n (λ x, fderiv 𝕜 f x y) :=
by rw [cont_diff_succ_iff_fderiv, cont_diff_clm_apply_iff]

lemma cont_diff_on_succ_of_fderiv_apply [finite_dimensional 𝕜 E] {n : ℕ} {f : E → F}
  {s : set E} (hf : differentiable_on 𝕜 f s)
  (h : ∀ y, cont_diff_on 𝕜 n (λ x, fderiv_within 𝕜 f s x y) s) :
  cont_diff_on 𝕜 ((n + 1) : ℕ) f s :=
cont_diff_on_succ_of_fderiv_within hf $ cont_diff_on_clm_apply.mpr h

lemma cont_diff_on_succ_iff_fderiv_apply [finite_dimensional 𝕜 E] {n : ℕ} {f : E → F}
  {s : set E} (hs : unique_diff_on 𝕜 s) : cont_diff_on 𝕜 ((n + 1) : ℕ) f s ↔
  differentiable_on 𝕜 f s ∧ ∀ y, cont_diff_on 𝕜 n (λ x, fderiv_within 𝕜 f s x y) s :=
by rw [cont_diff_on_succ_iff_fderiv_within hs, cont_diff_on_clm_apply]

end finite_dimensional


section real
/-!
### Results over `ℝ` or `ℂ`
  The results in this section rely on the Mean Value Theorem, and therefore hold only over `ℝ` (and
  its extension fields such as `ℂ`).
-/

variables
{𝕂 : Type*} [is_R_or_C 𝕂]
{E' : Type*} [normed_add_comm_group E'] [normed_space 𝕂 E']
{F' : Type*} [normed_add_comm_group F'] [normed_space 𝕂 F']

/-- If a function has a Taylor series at order at least 1, then at points in the interior of the
    domain of definition, the term of order 1 of this series is a strict derivative of `f`. -/
lemma has_ftaylor_series_up_to_on.has_strict_fderiv_at
  {s : set E'} {f : E' → F'} {x : E'} {p : E' → formal_multilinear_series 𝕂 E' F'}
  (hf : has_ftaylor_series_up_to_on n f p s) (hn : 1 ≤ n) (hs : s ∈ 𝓝 x) :
  has_strict_fderiv_at f ((continuous_multilinear_curry_fin1 𝕂 E' F') (p x 1)) x :=
has_strict_fderiv_at_of_has_fderiv_at_of_continuous_at (hf.eventually_has_fderiv_at hn hs) $
  (continuous_multilinear_curry_fin1 𝕂 E' F').continuous_at.comp $
    (hf.cont 1 hn).continuous_at hs

/-- If a function is `C^n` with `1 ≤ n` around a point, and its derivative at that point is given to
us as `f'`, then `f'` is also a strict derivative. -/
lemma cont_diff_at.has_strict_fderiv_at'
  {f : E' → F'} {f' : E' →L[𝕂] F'} {x : E'}
  (hf : cont_diff_at 𝕂 n f x) (hf' : has_fderiv_at f f' x) (hn : 1 ≤ n) :
  has_strict_fderiv_at f f' x :=
begin
  rcases hf 1 hn with ⟨u, H, p, hp⟩,
  simp only [nhds_within_univ, mem_univ, insert_eq_of_mem] at H,
  have := hp.has_strict_fderiv_at le_rfl H,
  rwa hf'.unique this.has_fderiv_at
end

/-- If a function is `C^n` with `1 ≤ n` around a point, and its derivative at that point is given to
us as `f'`, then `f'` is also a strict derivative. -/
lemma cont_diff_at.has_strict_deriv_at' {f : 𝕂 → F'} {f' : F'} {x : 𝕂}
  (hf : cont_diff_at 𝕂 n f x) (hf' : has_deriv_at f f' x) (hn : 1 ≤ n) :
  has_strict_deriv_at f f' x :=
hf.has_strict_fderiv_at' hf' hn

/-- If a function is `C^n` with `1 ≤ n` around a point, then the derivative of `f` at this point
is also a strict derivative. -/
lemma cont_diff_at.has_strict_fderiv_at {f : E' → F'} {x : E'}
  (hf : cont_diff_at 𝕂 n f x) (hn : 1 ≤ n) :
  has_strict_fderiv_at f (fderiv 𝕂 f x) x :=
hf.has_strict_fderiv_at' (hf.differentiable_at hn).has_fderiv_at hn

/-- If a function is `C^n` with `1 ≤ n` around a point, then the derivative of `f` at this point
is also a strict derivative. -/
lemma cont_diff_at.has_strict_deriv_at {f : 𝕂 → F'} {x : 𝕂}
  (hf : cont_diff_at 𝕂 n f x) (hn : 1 ≤ n) :
  has_strict_deriv_at f (deriv f x) x :=
(hf.has_strict_fderiv_at hn).has_strict_deriv_at

/-- If a function is `C^n` with `1 ≤ n`, then the derivative of `f` is also a strict derivative. -/
lemma cont_diff.has_strict_fderiv_at
  {f : E' → F'} {x : E'} (hf : cont_diff 𝕂 n f) (hn : 1 ≤ n) :
  has_strict_fderiv_at f (fderiv 𝕂 f x) x :=
hf.cont_diff_at.has_strict_fderiv_at hn

/-- If a function is `C^n` with `1 ≤ n`, then the derivative of `f` is also a strict derivative. -/
lemma cont_diff.has_strict_deriv_at
  {f : 𝕂 → F'} {x : 𝕂} (hf : cont_diff 𝕂 n f) (hn : 1 ≤ n) :
  has_strict_deriv_at f (deriv f x) x :=
hf.cont_diff_at.has_strict_deriv_at hn

/-- If `f` has a formal Taylor series `p` up to order `1` on `{x} ∪ s`, where `s` is a convex set,
and `‖p x 1‖₊ < K`, then `f` is `K`-Lipschitz in a neighborhood of `x` within `s`. -/
lemma has_ftaylor_series_up_to_on.exists_lipschitz_on_with_of_nnnorm_lt {E F : Type*}
  [normed_add_comm_group E] [normed_space ℝ E] [normed_add_comm_group F] [normed_space ℝ F]
  {f : E → F} {p : E → formal_multilinear_series ℝ E F} {s : set E} {x : E}
  (hf : has_ftaylor_series_up_to_on 1 f p (insert x s)) (hs : convex ℝ s) (K : ℝ≥0)
  (hK : ‖p x 1‖₊ < K) :
  ∃ t ∈ 𝓝[s] x, lipschitz_on_with K f t :=
begin
  set f' := λ y, continuous_multilinear_curry_fin1 ℝ E F (p y 1),
  have hder : ∀ y ∈ s, has_fderiv_within_at f (f' y) s y,
    from λ y hy, (hf.has_fderiv_within_at le_rfl (subset_insert x s hy)).mono (subset_insert x s),
  have hcont : continuous_within_at f' s x,
    from (continuous_multilinear_curry_fin1 ℝ E F).continuous_at.comp_continuous_within_at
      ((hf.cont _ le_rfl _ (mem_insert _ _)).mono (subset_insert x s)),
  replace hK : ‖f' x‖₊ < K, by simpa only [linear_isometry_equiv.nnnorm_map],
  exact hs.exists_nhds_within_lipschitz_on_with_of_has_fderiv_within_at_of_nnnorm_lt
    (eventually_nhds_within_iff.2 $ eventually_of_forall hder) hcont K hK
end

/-- If `f` has a formal Taylor series `p` up to order `1` on `{x} ∪ s`, where `s` is a convex set,
then `f` is Lipschitz in a neighborhood of `x` within `s`. -/
lemma has_ftaylor_series_up_to_on.exists_lipschitz_on_with {E F : Type*} [normed_add_comm_group E]
  [normed_space ℝ E] [normed_add_comm_group F] [normed_space ℝ F] {f : E → F}
  {p : E → formal_multilinear_series ℝ E F} {s : set E} {x : E}
  (hf : has_ftaylor_series_up_to_on 1 f p (insert x s)) (hs : convex ℝ s) :
  ∃ K (t ∈ 𝓝[s] x), lipschitz_on_with K f t :=
(exists_gt _).imp $ hf.exists_lipschitz_on_with_of_nnnorm_lt hs

/-- If `f` is `C^1` within a conves set `s` at `x`, then it is Lipschitz on a neighborhood of `x`
within `s`. -/
lemma cont_diff_within_at.exists_lipschitz_on_with {E F : Type*} [normed_add_comm_group E]
  [normed_space ℝ E] [normed_add_comm_group F] [normed_space ℝ F] {f : E → F} {s : set E}
  {x : E} (hf : cont_diff_within_at ℝ 1 f s x) (hs : convex ℝ s) :
  ∃ (K : ℝ≥0) (t ∈ 𝓝[s] x), lipschitz_on_with K f t :=
begin
  rcases hf 1 le_rfl with ⟨t, hst, p, hp⟩,
  rcases metric.mem_nhds_within_iff.mp hst with ⟨ε, ε0, hε⟩,
  replace hp : has_ftaylor_series_up_to_on 1 f p (metric.ball x ε ∩ insert x s) := hp.mono hε,
  clear hst hε t,
  rw [← insert_eq_of_mem (metric.mem_ball_self ε0), ← insert_inter_distrib] at hp,
  rcases hp.exists_lipschitz_on_with ((convex_ball _ _).inter hs) with ⟨K, t, hst, hft⟩,
  rw [inter_comm, ← nhds_within_restrict' _ (metric.ball_mem_nhds _ ε0)] at hst,
  exact ⟨K, t, hst, hft⟩
end

/-- If `f` is `C^1` at `x` and `K > ‖fderiv 𝕂 f x‖`, then `f` is `K`-Lipschitz in a neighborhood of
`x`. -/
lemma cont_diff_at.exists_lipschitz_on_with_of_nnnorm_lt {f : E' → F'} {x : E'}
  (hf : cont_diff_at 𝕂 1 f x) (K : ℝ≥0) (hK : ‖fderiv 𝕂 f x‖₊ < K) :
  ∃ t ∈ 𝓝 x, lipschitz_on_with K f t :=
(hf.has_strict_fderiv_at le_rfl).exists_lipschitz_on_with_of_nnnorm_lt K hK

/-- If `f` is `C^1` at `x`, then `f` is Lipschitz in a neighborhood of `x`. -/
lemma cont_diff_at.exists_lipschitz_on_with {f : E' → F'} {x : E'}
  (hf : cont_diff_at 𝕂 1 f x) :
  ∃ K (t ∈ 𝓝 x), lipschitz_on_with K f t :=
(hf.has_strict_fderiv_at le_rfl).exists_lipschitz_on_with

end real

section deriv
/-!
### One dimension

All results up to now have been expressed in terms of the general Fréchet derivative `fderiv`. For
maps defined on the field, the one-dimensional derivative `deriv` is often easier to use. In this
paragraph, we reformulate some higher smoothness results in terms of `deriv`.
-/

variables {f₂ : 𝕜 → F} {s₂ : set 𝕜}
open continuous_linear_map (smul_right)

/-- A function is `C^(n + 1)` on a domain with unique derivatives if and only if it is
differentiable there, and its derivative (formulated with `deriv_within`) is `C^n`. -/
theorem cont_diff_on_succ_iff_deriv_within {n : ℕ} (hs : unique_diff_on 𝕜 s₂) :
  cont_diff_on 𝕜 ((n + 1) : ℕ) f₂ s₂ ↔
  differentiable_on 𝕜 f₂ s₂ ∧ cont_diff_on 𝕜 n (deriv_within f₂ s₂) s₂ :=
begin
  rw cont_diff_on_succ_iff_fderiv_within hs,
  congr' 2,
  apply le_antisymm,
  { assume h,
    have : deriv_within f₂ s₂ = (λ u : 𝕜 →L[𝕜] F, u 1) ∘ (fderiv_within 𝕜 f₂ s₂),
      by { ext x, refl },
    simp only [this],
    apply cont_diff.comp_cont_diff_on _ h,
    exact (is_bounded_bilinear_map_apply.is_bounded_linear_map_left _).cont_diff },
  { assume h,
    have : fderiv_within 𝕜 f₂ s₂ = smul_right (1 : 𝕜 →L[𝕜] 𝕜) ∘ deriv_within f₂ s₂,
      by { ext x, simp [deriv_within] },
    simp only [this],
    apply cont_diff.comp_cont_diff_on _ h,
    have : is_bounded_bilinear_map 𝕜 (λ _ : (𝕜 →L[𝕜] 𝕜) × F, _) :=
      is_bounded_bilinear_map_smul_right,
    exact (this.is_bounded_linear_map_right _).cont_diff }
end

/-- A function is `C^(n + 1)` on an open domain if and only if it is
differentiable there, and its derivative (formulated with `deriv`) is `C^n`. -/
theorem cont_diff_on_succ_iff_deriv_of_open {n : ℕ} (hs : is_open s₂) :
  cont_diff_on 𝕜 ((n + 1) : ℕ) f₂ s₂ ↔
  differentiable_on 𝕜 f₂ s₂ ∧ cont_diff_on 𝕜 n (deriv f₂) s₂ :=
begin
  rw cont_diff_on_succ_iff_deriv_within hs.unique_diff_on,
  congrm _ ∧ _,
  exact cont_diff_on_congr (λ _, deriv_within_of_open hs)
end

/-- A function is `C^∞` on a domain with unique derivatives if and only if it is differentiable
there, and its derivative (formulated with `deriv_within`) is `C^∞`. -/
theorem cont_diff_on_top_iff_deriv_within (hs : unique_diff_on 𝕜 s₂) :
  cont_diff_on 𝕜 ∞ f₂ s₂ ↔
  differentiable_on 𝕜 f₂ s₂ ∧ cont_diff_on 𝕜 ∞ (deriv_within f₂ s₂) s₂ :=
begin
  split,
  { assume h,
    refine ⟨h.differentiable_on le_top, _⟩,
    apply cont_diff_on_top.2 (λ n, ((cont_diff_on_succ_iff_deriv_within hs).1 _).2),
    exact h.of_le le_top },
  { assume h,
    refine cont_diff_on_top.2 (λ n, _),
    have A : (n : ℕ∞) ≤ ∞ := le_top,
    apply ((cont_diff_on_succ_iff_deriv_within hs).2 ⟨h.1, h.2.of_le A⟩).of_le,
    exact with_top.coe_le_coe.2 (nat.le_succ n) }
end

/-- A function is `C^∞` on an open domain if and only if it is differentiable
there, and its derivative (formulated with `deriv`) is `C^∞`. -/
theorem cont_diff_on_top_iff_deriv_of_open (hs : is_open s₂) :
  cont_diff_on 𝕜 ∞ f₂ s₂ ↔
  differentiable_on 𝕜 f₂ s₂ ∧ cont_diff_on 𝕜 ∞ (deriv f₂) s₂ :=
begin
  rw cont_diff_on_top_iff_deriv_within hs.unique_diff_on,
  congrm _ ∧ _,
  exact cont_diff_on_congr (λ _, deriv_within_of_open hs)
end

lemma cont_diff_on.deriv_within
  (hf : cont_diff_on 𝕜 n f₂ s₂) (hs : unique_diff_on 𝕜 s₂) (hmn : m + 1 ≤ n) :
  cont_diff_on 𝕜 m (deriv_within f₂ s₂) s₂ :=
begin
  cases m,
  { change ∞ + 1 ≤ n at hmn,
    have : n = ∞, by simpa using hmn,
    rw this at hf,
    exact ((cont_diff_on_top_iff_deriv_within hs).1 hf).2 },
  { change (m.succ : ℕ∞) ≤ n at hmn,
    exact ((cont_diff_on_succ_iff_deriv_within hs).1 (hf.of_le hmn)).2 }
end

lemma cont_diff_on.deriv_of_open
  (hf : cont_diff_on 𝕜 n f₂ s₂) (hs : is_open s₂) (hmn : m + 1 ≤ n) :
  cont_diff_on 𝕜 m (deriv f₂) s₂ :=
(hf.deriv_within hs.unique_diff_on hmn).congr (λ x hx, (deriv_within_of_open hs hx).symm)

lemma cont_diff_on.continuous_on_deriv_within
  (h : cont_diff_on 𝕜 n f₂ s₂) (hs : unique_diff_on 𝕜 s₂) (hn : 1 ≤ n) :
  continuous_on (deriv_within f₂ s₂) s₂ :=
((cont_diff_on_succ_iff_deriv_within hs).1 (h.of_le hn)).2.continuous_on

lemma cont_diff_on.continuous_on_deriv_of_open
  (h : cont_diff_on 𝕜 n f₂ s₂) (hs : is_open s₂) (hn : 1 ≤ n) :
  continuous_on (deriv f₂) s₂ :=
((cont_diff_on_succ_iff_deriv_of_open hs).1 (h.of_le hn)).2.continuous_on

/-- A function is `C^(n + 1)` if and only if it is differentiable,
  and its derivative (formulated in terms of `deriv`) is `C^n`. -/
theorem cont_diff_succ_iff_deriv {n : ℕ} :
  cont_diff 𝕜 ((n + 1) : ℕ) f₂ ↔
    differentiable 𝕜 f₂ ∧ cont_diff 𝕜 n (deriv f₂) :=
by simp only [← cont_diff_on_univ, cont_diff_on_succ_iff_deriv_of_open, is_open_univ,
  differentiable_on_univ]

theorem cont_diff_one_iff_deriv :
  cont_diff 𝕜 1 f₂ ↔ differentiable 𝕜 f₂ ∧ continuous (deriv f₂) :=
cont_diff_succ_iff_deriv.trans $ iff.rfl.and cont_diff_zero

/-- A function is `C^∞` if and only if it is differentiable,
and its derivative (formulated in terms of `deriv`) is `C^∞`. -/
theorem cont_diff_top_iff_deriv :
  cont_diff 𝕜 ∞ f₂ ↔
  differentiable 𝕜 f₂ ∧ cont_diff 𝕜 ∞ (deriv f₂) :=
begin
  simp only [← cont_diff_on_univ, ← differentiable_on_univ, ← deriv_within_univ],
  rw cont_diff_on_top_iff_deriv_within unique_diff_on_univ,
end

lemma cont_diff.continuous_deriv (h : cont_diff 𝕜 n f₂) (hn : 1 ≤ n) :
  continuous (deriv f₂) :=
(cont_diff_succ_iff_deriv.mp (h.of_le hn)).2.continuous

end deriv

section restrict_scalars
/-!
### Restricting from `ℂ` to `ℝ`, or generally from `𝕜'` to `𝕜`

If a function is `n` times continuously differentiable over `ℂ`, then it is `n` times continuously
differentiable over `ℝ`. In this paragraph, we give variants of this statement, in the general
situation where `ℂ` and `ℝ` are replaced respectively by `𝕜'` and `𝕜` where `𝕜'` is a normed algebra
over `𝕜`.
-/

variables (𝕜) {𝕜' : Type*} [nontrivially_normed_field 𝕜'] [normed_algebra 𝕜 𝕜']
variables [normed_space 𝕜' E] [is_scalar_tower 𝕜 𝕜' E]
variables [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F]
variables {p' : E → formal_multilinear_series 𝕜' E F}

lemma has_ftaylor_series_up_to_on.restrict_scalars
  (h : has_ftaylor_series_up_to_on n f p' s) :
  has_ftaylor_series_up_to_on n f (λ x, (p' x).restrict_scalars 𝕜) s :=
{ zero_eq := λ x hx, h.zero_eq x hx,
  fderiv_within :=
    begin
      intros m hm x hx,
      convert ((continuous_multilinear_map.restrict_scalars_linear 𝕜).has_fderiv_at)
        .comp_has_fderiv_within_at _ ((h.fderiv_within m hm x hx).restrict_scalars 𝕜),
    end,
  cont := λ m hm, continuous_multilinear_map.continuous_restrict_scalars.comp_continuous_on
    (h.cont m hm) }

lemma cont_diff_within_at.restrict_scalars (h : cont_diff_within_at 𝕜' n f s x) :
  cont_diff_within_at 𝕜 n f s x :=
begin
  intros m hm,
  rcases h m hm with ⟨u, u_mem, p', hp'⟩,
  exact ⟨u, u_mem, _, hp'.restrict_scalars _⟩
end

lemma cont_diff_on.restrict_scalars (h : cont_diff_on 𝕜' n f s) :
  cont_diff_on 𝕜 n f s :=
λ x hx, (h x hx).restrict_scalars _

lemma cont_diff_at.restrict_scalars (h : cont_diff_at 𝕜' n f x) :
  cont_diff_at 𝕜 n f x :=
cont_diff_within_at_univ.1 $ h.cont_diff_within_at.restrict_scalars _

lemma cont_diff.restrict_scalars (h : cont_diff 𝕜' n f) :
  cont_diff 𝕜 n f :=
cont_diff_iff_cont_diff_at.2 $ λ x, h.cont_diff_at.restrict_scalars _

end restrict_scalars

/-!## Quantitative bounds -/

/-- Bounding the norm of the iterated derivative of `B (f x) (g x)` within a set in terms of the
iterated derivatives of `f` and `g` when `B` is bilinear. This lemma is an auxiliary version
assuming all spaces live in the same universe, to enable an induction. Use instead
`continuous_linear_map.norm_iterated_fderiv_within_le_of_bilinear` that removes this assumption. -/
lemma continuous_linear_map.norm_iterated_fderiv_within_le_of_bilinear_aux
  {Du Eu Fu Gu : Type u}
  [normed_add_comm_group Du] [normed_space 𝕜 Du]
  [normed_add_comm_group Eu] [normed_space 𝕜 Eu]
  [normed_add_comm_group Fu] [normed_space 𝕜 Fu]
  [normed_add_comm_group Gu] [normed_space 𝕜 Gu]
  (B : Eu →L[𝕜] Fu →L[𝕜] Gu) {f : Du → Eu} {g : Du → Fu} {n : ℕ} {s : set Du} {x : Du}
  (hf : cont_diff_on 𝕜 n f s) (hg : cont_diff_on 𝕜 n g s) (hs : unique_diff_on 𝕜 s) (hx : x ∈ s) :
  ‖iterated_fderiv_within 𝕜 n (λ y, B (f y) (g y)) s x‖
    ≤ ‖B‖ * ∑ i in finset.range (n+1), (n.choose i : ℝ)
      * ‖iterated_fderiv_within 𝕜 i f s x‖ * ‖iterated_fderiv_within 𝕜 (n-i) g s x‖ :=
begin
  /- We argue by induction on `n`. The bound is trivial for `n = 0`. For `n + 1`, we write
  the `(n+1)`-th derivative as the `n`-th derivative of the derivative `B f g' + B f' g`, and apply
  the inductive assumption to each of those two terms. For this induction to make sense,
  the spaces of linear maps that appear in the induction should be in the same universe as the
  original spaces, which explains why we assume in the lemma that all spaces live in the same
  universe. -/
  unfreezingI { induction n with n IH generalizing Eu Fu Gu},
  { simp only [←mul_assoc, norm_iterated_fderiv_within_zero, finset.range_one, finset.sum_singleton,
      nat.choose_self, algebra_map.coe_one, one_mul],
    apply ((B (f x)).le_op_norm (g x)).trans,
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _),
    exact B.le_op_norm (f x) },
  { have In : (n : with_top ℕ) + 1 ≤ n.succ, by simp only [nat.cast_succ, le_refl],
    have I1 :
      ‖iterated_fderiv_within 𝕜 n (λ (y : Du), B.precompR Du (f y) (fderiv_within 𝕜 g s y)) s x‖ ≤
      ‖B‖ * ∑ (i : ℕ) in finset.range (n + 1), n.choose i *
        ‖iterated_fderiv_within 𝕜 i f s x‖ * ‖iterated_fderiv_within 𝕜 (n + 1 - i) g s x‖ := calc
      ‖iterated_fderiv_within 𝕜 n (λ (y : Du), B.precompR Du (f y) (fderiv_within 𝕜 g s y)) s x‖
          ≤ ‖B.precompR Du‖ * ∑ (i : ℕ) in finset.range (n + 1), n.choose i
            * ‖iterated_fderiv_within 𝕜 i f s x‖
            * ‖iterated_fderiv_within 𝕜 (n - i) (fderiv_within 𝕜 g s) s x‖ :
        IH _ (hf.of_le (nat.cast_le.2 (nat.le_succ n))) (hg.fderiv_within hs In)
      ... ≤ ‖B‖ * ∑ (i : ℕ) in finset.range (n + 1), n.choose i
            * ‖iterated_fderiv_within 𝕜 i f s x‖
            * ‖iterated_fderiv_within 𝕜 (n - i) (fderiv_within 𝕜 g s) s x‖ :
        mul_le_mul_of_nonneg_right (B.norm_precompR_le Du) (finset.sum_nonneg' (λ i, by positivity))
      ... = _ :
        begin
          congr' 1,
          apply finset.sum_congr rfl (λ i hi, _ ),
          rw [nat.succ_sub (nat.lt_succ_iff.1 (finset.mem_range.1 hi)),
            iterated_fderiv_within_succ_eq_comp_right hs hx, linear_isometry_equiv.norm_map],
        end,
    have I2 :
      ‖iterated_fderiv_within 𝕜 n (λ (y : Du), B.precompL Du (fderiv_within 𝕜 f s y) (g y)) s x‖ ≤
      ‖B‖ * ∑ (i : ℕ) in finset.range (n + 1), n.choose i *
        ‖iterated_fderiv_within 𝕜 (i + 1) f s x‖ * ‖iterated_fderiv_within 𝕜 (n - i) g s x‖ := calc
      ‖iterated_fderiv_within 𝕜 n (λ (y : Du), B.precompL Du (fderiv_within 𝕜 f s y) (g y)) s x‖
          ≤ ‖B.precompL Du‖ * ∑ (i : ℕ) in finset.range (n + 1), n.choose i
            * ‖iterated_fderiv_within 𝕜 i (fderiv_within 𝕜 f s) s x‖
            * ‖iterated_fderiv_within 𝕜 (n - i) g s x‖ :
        IH _ (hf.fderiv_within hs In) (hg.of_le (nat.cast_le.2 (nat.le_succ n)))
      ... ≤ ‖B‖ * ∑ (i : ℕ) in finset.range (n + 1), n.choose i
            * ‖iterated_fderiv_within 𝕜 i (fderiv_within 𝕜 f s) s x‖
            * ‖iterated_fderiv_within 𝕜 (n - i) g s x‖ :
        mul_le_mul_of_nonneg_right (B.norm_precompL_le Du) (finset.sum_nonneg' (λ i, by positivity))
      ... = _ :
        begin
          congr' 1,
          apply finset.sum_congr rfl (λ i hi, _ ),
          rw [iterated_fderiv_within_succ_eq_comp_right hs hx, linear_isometry_equiv.norm_map],
        end,
    have J : iterated_fderiv_within 𝕜 n
      (λ (y : Du), fderiv_within 𝕜 (λ (y : Du), B (f y) (g y)) s y) s x
      = iterated_fderiv_within 𝕜 n (λ y, B.precompR Du (f y) (fderiv_within 𝕜 g s y)
        + B.precompL Du (fderiv_within 𝕜 f s y) (g y)) s x,
    { apply iterated_fderiv_within_congr hs (λ y hy, _) hx,
      have L : (1 : with_top ℕ) ≤ n.succ,
        by simpa only [enat.coe_one, nat.one_le_cast] using nat.succ_pos n,
      exact B.fderiv_within_of_bilinear (hf.differentiable_on L y hy)
        (hg.differentiable_on L y hy) (hs y hy) },
    rw [iterated_fderiv_within_succ_eq_comp_right hs hx, linear_isometry_equiv.norm_map, J],
    have A : cont_diff_on 𝕜 n (λ y, B.precompR Du (f y) (fderiv_within 𝕜 g s y)) s,
      from (B.precompR Du).is_bounded_bilinear_map.cont_diff.comp_cont_diff_on₂
        (hf.of_le (nat.cast_le.2 (nat.le_succ n))) (hg.fderiv_within hs In),
    have A' : cont_diff_on 𝕜 n (λ y, B.precompL Du (fderiv_within 𝕜 f s y) (g y)) s,
      from (B.precompL Du).is_bounded_bilinear_map.cont_diff.comp_cont_diff_on₂
        (hf.fderiv_within hs In) (hg.of_le (nat.cast_le.2 (nat.le_succ n))),
    rw iterated_fderiv_within_add_apply' A A' hs hx,
    apply (norm_add_le _ _).trans ((add_le_add I1 I2).trans (le_of_eq _)),
    simp_rw [← mul_add, mul_assoc],
    congr' 1,
    exact (finset.sum_choose_succ_mul (λ i j, ‖iterated_fderiv_within 𝕜 i f s x‖ *
      ‖iterated_fderiv_within 𝕜 j g s x‖) n).symm }
end

/-- Bounding the norm of the iterated derivative of `B (f x) (g x)` within a set in terms of the
iterated derivatives of `f` and `g` when `B` is bilinear:
`‖D^n (x ↦ B (f x) (g x))‖ ≤ ‖B‖ ∑_{k ≤ n} n.choose k ‖D^k f‖ ‖D^{n-k} g‖` -/
lemma continuous_linear_map.norm_iterated_fderiv_within_le_of_bilinear
  (B : E →L[𝕜] F →L[𝕜] G) {f : D → E} {g : D → F} {N : with_top ℕ} {s : set D} {x : D}
  (hf : cont_diff_on 𝕜 N f s) (hg : cont_diff_on 𝕜 N g s) (hs : unique_diff_on 𝕜 s) (hx : x ∈ s)
  {n : ℕ} (hn : (n : with_top ℕ) ≤ N) :
  ‖iterated_fderiv_within 𝕜 n (λ y, B (f y) (g y)) s x‖
    ≤ ‖B‖ * ∑ i in finset.range (n+1), (n.choose i : ℝ)
      * ‖iterated_fderiv_within 𝕜 i f s x‖ * ‖iterated_fderiv_within 𝕜 (n-i) g s x‖ :=
begin
  /- We reduce the bound to the case where all spaces live in the same universe (in which we
  already have proved the result), by using linear isometries between the spaces and their `ulift`
  to a common universe. These linear isometries preserve the norm of the iterated derivative. -/
  let Du : Type (max uD uE uF uG) := ulift.{(max uE uF uG) uD} D,
  let Eu : Type (max uD uE uF uG) := ulift.{(max uD uF uG) uE} E,
  let Fu : Type (max uD uE uF uG) := ulift.{(max uD uE uG) uF} F,
  let Gu : Type (max uD uE uF uG) := ulift.{(max uD uE uF) uG} G,
  have isoD : Du ≃ₗᵢ[𝕜] D := linear_isometry_equiv.ulift 𝕜 D,
  have isoE : Eu ≃ₗᵢ[𝕜] E := linear_isometry_equiv.ulift 𝕜 E,
  have isoF : Fu ≃ₗᵢ[𝕜] F := linear_isometry_equiv.ulift 𝕜 F,
  have isoG : Gu ≃ₗᵢ[𝕜] G := linear_isometry_equiv.ulift 𝕜 G,
  -- lift `f` and `g` to versions `fu` and `gu` on the lifted spaces.
  let fu : Du → Eu := isoE.symm ∘ f ∘ isoD,
  let gu : Du → Fu := isoF.symm ∘ g ∘ isoD,
  -- lift the bilinear map `B` to a bilinear map `Bu` on the lifted spaces.
  let Bu₀ : Eu →L[𝕜] Fu →L[𝕜] G,
    from ((B.comp (isoE : Eu →L[𝕜] E)).flip.comp (isoF : Fu →L[𝕜] F)).flip,
  let Bu : Eu →L[𝕜] Fu →L[𝕜] Gu, from continuous_linear_map.compL 𝕜 Eu (Fu →L[𝕜] G) (Fu →L[𝕜] Gu)
    (continuous_linear_map.compL 𝕜 Fu G Gu (isoG.symm : G →L[𝕜] Gu)) Bu₀,
  have Bu_eq : (λ y, Bu (fu y) (gu y)) = isoG.symm ∘ (λ y, B (f y) (g y)) ∘ isoD,
  { ext1 y,
    simp only [Bu, continuous_linear_map.compL_apply, function.comp_app,
      continuous_linear_map.coe_comp', linear_isometry_equiv.coe_coe'',
      continuous_linear_map.flip_apply, linear_isometry_equiv.apply_symm_apply] },
  -- All norms are preserved by the lifting process.
  have Bu_le : ‖Bu‖ ≤ ‖B‖,
  { refine continuous_linear_map.op_norm_le_bound _ (norm_nonneg _) (λ y, _),
    refine continuous_linear_map.op_norm_le_bound _ (by positivity) (λ x, _ ),
    simp only [Bu, continuous_linear_map.compL_apply, continuous_linear_map.coe_comp',
      function.comp_app, linear_isometry_equiv.coe_coe'', continuous_linear_map.flip_apply,
      linear_isometry_equiv.norm_map],
    calc ‖B (isoE y) (isoF x)‖
        ≤ ‖B (isoE y)‖ * ‖isoF x‖ : continuous_linear_map.le_op_norm _ _
    ... ≤ ‖B‖ * ‖isoE y‖ * ‖isoF x‖ :
      mul_le_mul_of_nonneg_right (continuous_linear_map.le_op_norm _ _) (norm_nonneg _)
    ... = ‖B‖ * ‖y‖ * ‖x‖ : by simp only [linear_isometry_equiv.norm_map] },
  let su := isoD ⁻¹' s,
  have hsu : unique_diff_on 𝕜 su,
    from isoD.to_continuous_linear_equiv.unique_diff_on_preimage_iff.2 hs,
  let xu := isoD.symm x,
  have hxu : xu ∈ su,
    by simpa only [set.mem_preimage, linear_isometry_equiv.apply_symm_apply] using hx,
  have xu_x : isoD xu = x, by simp only [linear_isometry_equiv.apply_symm_apply],
  have hfu : cont_diff_on 𝕜 n fu su, from isoE.symm.cont_diff.comp_cont_diff_on
    ((hf.of_le hn).comp_continuous_linear_map (isoD : Du →L[𝕜] D)),
  have hgu : cont_diff_on 𝕜 n gu su, from isoF.symm.cont_diff.comp_cont_diff_on
    ((hg.of_le hn).comp_continuous_linear_map (isoD : Du →L[𝕜] D)),
  have Nfu : ∀ i, ‖iterated_fderiv_within 𝕜 i fu su xu‖ = ‖iterated_fderiv_within 𝕜 i f s x‖,
  { assume i,
    rw linear_isometry_equiv.norm_iterated_fderiv_within_comp_left _ _ hsu hxu,
    rw [linear_isometry_equiv.norm_iterated_fderiv_within_comp_right _ _ hs, xu_x],
    rwa ← xu_x at hx },
  have Ngu : ∀ i, ‖iterated_fderiv_within 𝕜 i gu su xu‖ = ‖iterated_fderiv_within 𝕜 i g s x‖,
  { assume i,
    rw linear_isometry_equiv.norm_iterated_fderiv_within_comp_left _ _ hsu hxu,
    rw [linear_isometry_equiv.norm_iterated_fderiv_within_comp_right _ _ hs, xu_x],
    rwa ← xu_x at hx },
  have NBu : ‖iterated_fderiv_within 𝕜 n (λ y, Bu (fu y) (gu y)) su xu‖ =
    ‖iterated_fderiv_within 𝕜 n (λ y, B (f y) (g y)) s x‖,
  { rw Bu_eq,
    rw linear_isometry_equiv.norm_iterated_fderiv_within_comp_left _ _ hsu hxu,
    rw [linear_isometry_equiv.norm_iterated_fderiv_within_comp_right _ _ hs, xu_x],
    rwa ← xu_x at hx },
  -- state the bound for the lifted objects, and deduce the original bound from it.
  have : ‖iterated_fderiv_within 𝕜 n (λ y, Bu (fu y) (gu y)) su xu‖
    ≤ ‖Bu‖ * ∑ i in finset.range (n+1), (n.choose i : ℝ)
      * ‖iterated_fderiv_within 𝕜 i fu su xu‖ * ‖iterated_fderiv_within 𝕜 (n-i) gu su xu‖,
    from Bu.norm_iterated_fderiv_within_le_of_bilinear_aux hfu hgu hsu hxu,
  simp only [Nfu, Ngu, NBu] at this,
  apply this.trans (mul_le_mul_of_nonneg_right Bu_le _),
  exact finset.sum_nonneg' (λ i, by positivity),
end

/-- Bounding the norm of the iterated derivative of `B (f x) (g x)` in terms of the
iterated derivatives of `f` and `g` when `B` is bilinear:
`‖D^n (x ↦ B (f x) (g x))‖ ≤ ‖B‖ ∑_{k ≤ n} n.choose k ‖D^k f‖ ‖D^{n-k} g‖` -/
lemma continuous_linear_map.norm_iterated_fderiv_le_of_bilinear
  (B : E →L[𝕜] F →L[𝕜] G) {f : D → E} {g : D → F} {N : with_top ℕ}
  (hf : cont_diff 𝕜 N f) (hg : cont_diff 𝕜 N g) (x : D)
  {n : ℕ} (hn : (n : with_top ℕ) ≤ N) :
  ‖iterated_fderiv 𝕜 n (λ y, B (f y) (g y)) x‖
    ≤ ‖B‖ * ∑ i in finset.range (n+1), (n.choose i : ℝ)
      * ‖iterated_fderiv 𝕜 i f x‖ * ‖iterated_fderiv 𝕜 (n-i) g x‖ :=
begin
  simp_rw [← iterated_fderiv_within_univ],
  exact B.norm_iterated_fderiv_within_le_of_bilinear hf.cont_diff_on hg.cont_diff_on
    unique_diff_on_univ (mem_univ x) hn,
end

/-- Bounding the norm of the iterated derivative of `B (f x) (g x)` within a set in terms of the
iterated derivatives of `f` and `g` when `B` is bilinear of norm at most `1`:
`‖D^n (x ↦ B (f x) (g x))‖ ≤ ∑_{k ≤ n} n.choose k ‖D^k f‖ ‖D^{n-k} g‖` -/
lemma continuous_linear_map.norm_iterated_fderiv_within_le_of_bilinear_of_le_one
  (B : E →L[𝕜] F →L[𝕜] G) {f : D → E} {g : D → F} {N : with_top ℕ} {s : set D} {x : D}
  (hf : cont_diff_on 𝕜 N f s) (hg : cont_diff_on 𝕜 N g s) (hs : unique_diff_on 𝕜 s) (hx : x ∈ s)
  {n : ℕ} (hn : (n : with_top ℕ) ≤ N) (hB : ‖B‖ ≤ 1) :
  ‖iterated_fderiv_within 𝕜 n (λ y, B (f y) (g y)) s x‖
    ≤ ∑ i in finset.range (n+1), (n.choose i : ℝ)
      * ‖iterated_fderiv_within 𝕜 i f s x‖ * ‖iterated_fderiv_within 𝕜 (n-i) g s x‖ :=
begin
  apply (B.norm_iterated_fderiv_within_le_of_bilinear hf hg hs hx hn).trans,
  apply mul_le_of_le_one_left (finset.sum_nonneg' (λ i, _)) hB,
  positivity
end

/-- Bounding the norm of the iterated derivative of `B (f x) (g x)` in terms of the
iterated derivatives of `f` and `g` when `B` is bilinear of norm at most `1`:
`‖D^n (x ↦ B (f x) (g x))‖ ≤ ∑_{k ≤ n} n.choose k ‖D^k f‖ ‖D^{n-k} g‖` -/
lemma continuous_linear_map.norm_iterated_fderiv_le_of_bilinear_of_le_one
  (B : E →L[𝕜] F →L[𝕜] G) {f : D → E} {g : D → F} {N : with_top ℕ}
  (hf : cont_diff 𝕜 N f) (hg : cont_diff 𝕜 N g) (x : D)
  {n : ℕ} (hn : (n : with_top ℕ) ≤ N) (hB : ‖B‖ ≤ 1) :
  ‖iterated_fderiv 𝕜 n (λ y, B (f y) (g y)) x‖
    ≤ ∑ i in finset.range (n+1), (n.choose i : ℝ)
      * ‖iterated_fderiv 𝕜 i f x‖ * ‖iterated_fderiv 𝕜 (n-i) g x‖ :=
begin
  simp_rw [← iterated_fderiv_within_univ],
  exact B.norm_iterated_fderiv_within_le_of_bilinear_of_le_one hf.cont_diff_on hg.cont_diff_on
    unique_diff_on_univ (mem_univ x) hn hB,
end

section

variables {𝕜' : Type*} [normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] [normed_space 𝕜' F]
  [is_scalar_tower 𝕜 𝕜' F]

lemma norm_iterated_fderiv_within_smul_le
  {f : E → 𝕜'} {g : E → F} {N : with_top ℕ} (hf : cont_diff_on 𝕜 N f s) (hg : cont_diff_on 𝕜 N g s)
  (hs : unique_diff_on 𝕜 s) {x : E} (hx : x ∈ s) {n : ℕ} (hn : (n : with_top ℕ) ≤ N) :
  ‖iterated_fderiv_within 𝕜 n (λ y, f y • g y) s x‖
    ≤ ∑ i in finset.range (n+1), (n.choose i : ℝ)
      * ‖iterated_fderiv_within 𝕜 i f s x‖ * ‖iterated_fderiv_within 𝕜 (n-i) g s x‖ :=
(continuous_linear_map.lsmul 𝕜 𝕜' : 𝕜' →L[𝕜] F →L[𝕜] F)
  .norm_iterated_fderiv_within_le_of_bilinear_of_le_one hf hg hs hx hn
  continuous_linear_map.op_norm_lsmul_le

lemma norm_iterated_fderiv_smul_le
  {f : E → 𝕜'} {g : E → F} {N : with_top ℕ} (hf : cont_diff 𝕜 N f) (hg : cont_diff 𝕜 N g)
  (x : E) {n : ℕ} (hn : (n : with_top ℕ) ≤ N) :
  ‖iterated_fderiv 𝕜 n (λ y, f y • g y) x‖
    ≤ ∑ i in finset.range (n+1), (n.choose i : ℝ)
      * ‖iterated_fderiv 𝕜 i f x‖ * ‖iterated_fderiv 𝕜 (n-i) g x‖ :=
(continuous_linear_map.lsmul 𝕜 𝕜' : 𝕜' →L[𝕜] F →L[𝕜] F)
  .norm_iterated_fderiv_le_of_bilinear_of_le_one hf hg x hn
  continuous_linear_map.op_norm_lsmul_le

end

section
variables {A : Type*} [normed_ring A] [normed_algebra 𝕜 A]

lemma norm_iterated_fderiv_within_mul_le
  {f : E → A} {g : E → A} {N : with_top ℕ} (hf : cont_diff_on 𝕜 N f s) (hg : cont_diff_on 𝕜 N g s)
  (hs : unique_diff_on 𝕜 s) {x : E} (hx : x ∈ s) {n : ℕ} (hn : (n : with_top ℕ) ≤ N) :
  ‖iterated_fderiv_within 𝕜 n (λ y, f y * g y) s x‖
    ≤ ∑ i in finset.range (n+1), (n.choose i : ℝ)
      * ‖iterated_fderiv_within 𝕜 i f s x‖ * ‖iterated_fderiv_within 𝕜 (n-i) g s x‖ :=
(continuous_linear_map.mul 𝕜 A : A →L[𝕜] A →L[𝕜] A)
  .norm_iterated_fderiv_within_le_of_bilinear_of_le_one hf hg hs hx hn
  (continuous_linear_map.op_norm_mul_le _ _)

lemma norm_iterated_fderiv_mul_le
  {f : E → A} {g : E → A} {N : with_top ℕ} (hf : cont_diff 𝕜 N f) (hg : cont_diff 𝕜 N g)
  (x : E) {n : ℕ} (hn : (n : with_top ℕ) ≤ N) :
  ‖iterated_fderiv 𝕜 n (λ y, f y * g y) x‖
    ≤ ∑ i in finset.range (n+1), (n.choose i : ℝ)
      * ‖iterated_fderiv 𝕜 i f x‖ * ‖iterated_fderiv 𝕜 (n-i) g x‖ :=
begin
  simp_rw [← iterated_fderiv_within_univ],
  exact norm_iterated_fderiv_within_mul_le hf.cont_diff_on
    hg.cont_diff_on unique_diff_on_univ (mem_univ x) hn,
end

end
