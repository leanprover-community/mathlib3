/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl

Continuous linear functions -- functions between normed vector spaces which are bounded and linear.
-/
import analysis.normed_space.multilinear

noncomputable theory
open_locale classical big_operators topological_space

open filter (tendsto)
open metric

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
variables {E : Type*} [normed_group E] [normed_space 𝕜 E]
variables {F : Type*} [normed_group F] [normed_space 𝕜 F]
variables {G : Type*} [normed_group G] [normed_space 𝕜 G]

section
variables {ι : Type*} [decidable_eq ι] [fintype ι]

/-- Taking the cartesian product of two continuous multilinear maps is a bounded linear operation. -/
lemma is_bounded_linear_map_prod_multilinear
  {E : ι → Type*} [∀i, normed_group (E i)] [∀i, normed_space 𝕜 (E i)] :
  is_bounded_linear_map 𝕜
  (λ p : (continuous_multilinear_map 𝕜 E F) × (continuous_multilinear_map 𝕜 E G), p.1.prod p.2) :=
{ map_add := λ p₁ p₂, by { ext1 m, refl },
  map_smul := λ c p, by { ext1 m, refl },
  bound := ⟨1, zero_lt_one, λ p, begin
    rw one_mul,
    apply continuous_multilinear_map.op_norm_le_bound _ (norm_nonneg _) (λ m, _),
    rw [continuous_multilinear_map.prod_apply, norm_prod_le_iff],
    split,
    { exact le_trans (p.1.le_op_norm m)
        (mul_le_mul_of_nonneg_right (norm_fst_le p) (finset.prod_nonneg (λ i hi, norm_nonneg _))) },
    { exact le_trans (p.2.le_op_norm m)
        (mul_le_mul_of_nonneg_right (norm_snd_le p) (finset.prod_nonneg (λ i hi, norm_nonneg _))) },
  end⟩ }

/-- Given a fixed continuous linear map `g`, associating to a continuous multilinear map `f` the
continuous multilinear map `f (g m₁, ..., g mₙ)` is a bounded linear operation. -/
lemma is_bounded_linear_map_continuous_multilinear_map_comp_linear (g : G →L[𝕜] E) :
  is_bounded_linear_map 𝕜 (λ f : continuous_multilinear_map 𝕜 (λ (i : ι), E) F,
    f.comp_continuous_linear_map (λ _, g)) :=
begin
  refine is_linear_map.with_bound ⟨λ f₁ f₂, by { ext m, refl }, λ c f, by { ext m, refl }⟩
    (∥g∥ ^ (fintype.card ι)) (λ f, _),
  apply continuous_multilinear_map.op_norm_le_bound _ _ (λ m, _),
  { apply_rules [mul_nonneg, pow_nonneg, norm_nonneg] },
  calc ∥f (g ∘ m)∥ ≤
    ∥f∥ * ∏ i, ∥g (m i)∥ : f.le_op_norm _
    ... ≤ ∥f∥ * ∏ i, (∥g∥ * ∥m i∥) : begin
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _),
      exact finset.prod_le_prod (λ i hi, norm_nonneg _) (λ i hi, g.le_op_norm _)
    end
    ... = ∥g∥ ^ fintype.card ι * ∥f∥ * ∏ i, ∥m i∥ :
      by { simp [finset.prod_mul_distrib, finset.card_univ], ring }
end

end

section bilinear_map

variable (𝕜)

/-- A map `f : E × F → G` satisfies `is_bounded_bilinear_map 𝕜 f` if it is bilinear and
continuous. -/
structure is_bounded_bilinear_map (f : E × F → G) : Prop :=
(add_left   : ∀(x₁ x₂ : E) (y : F), f (x₁ + x₂, y) = f (x₁, y) + f (x₂, y))
(smul_left  : ∀(c : 𝕜) (x : E) (y : F), f (c • x, y) = c • f (x,y))
(add_right  : ∀(x : E) (y₁ y₂ : F), f (x, y₁ + y₂) = f (x, y₁) + f (x, y₂))
(smul_right : ∀(c : 𝕜) (x : E) (y : F), f (x, c • y) = c • f (x,y))
(bound      : ∃C>0, ∀(x : E) (y : F), ∥f (x, y)∥ ≤ C * ∥x∥ * ∥y∥)

variable {𝕜}
variable {f : E × F → G}

protected lemma is_bounded_bilinear_map.is_O (h : is_bounded_bilinear_map 𝕜 f) :
  asymptotics.is_O f (λ p : E × F, ∥p.1∥ * ∥p.2∥) ⊤ :=
let ⟨C, Cpos, hC⟩ := h.bound in asymptotics.is_O.of_bound _ $
filter.eventually_of_forall $ λ ⟨x, y⟩, by simpa [mul_assoc] using hC x y

lemma is_bounded_bilinear_map.is_O_comp {α : Type*} (H : is_bounded_bilinear_map 𝕜 f)
  {g : α → E} {h : α → F} {l : filter α} :
  asymptotics.is_O (λ x, f (g x, h x)) (λ x, ∥g x∥ * ∥h x∥) l :=
H.is_O.comp_tendsto le_top

protected lemma is_bounded_bilinear_map.is_O' (h : is_bounded_bilinear_map 𝕜 f) :
  asymptotics.is_O f (λ p : E × F, ∥p∥ * ∥p∥) ⊤ :=
h.is_O.trans (asymptotics.is_O_fst_prod'.norm_norm.mul asymptotics.is_O_snd_prod'.norm_norm)

/-- The composition of a continuous linear map with a continuous multilinear map is a bounded
bilinear operation. -/
lemma is_bounded_bilinear_map_comp_multilinear {ι : Type*} {E : ι → Type*}
[decidable_eq ι] [fintype ι] [∀i, normed_group (E i)] [∀i, normed_space 𝕜 (E i)] :
  is_bounded_bilinear_map 𝕜 (λ p : (F →L[𝕜] G) × (continuous_multilinear_map 𝕜 E F),
    p.1.comp_continuous_multilinear_map p.2) :=
{ add_left   := λ g₁ g₂ f, by { ext m, refl },
  smul_left  := λ c g f, by { ext m, refl },
  add_right  := λ g f₁ f₂, by { ext m, simp },
  smul_right := λ c g f, by { ext m, simp },
  bound      := ⟨1, zero_lt_one, λ g f, begin
    apply continuous_multilinear_map.op_norm_le_bound _ _ (λm, _),
    { apply_rules [mul_nonneg, zero_le_one, norm_nonneg] },
    calc ∥g (f m)∥ ≤ ∥g∥ * ∥f m∥ : g.le_op_norm _
    ... ≤ ∥g∥ * (∥f∥ * ∏ i, ∥m i∥) :
      mul_le_mul_of_nonneg_left (f.le_op_norm _) (norm_nonneg _)
    ... = 1 * ∥g∥ * ∥f∥ * ∏ i, ∥m i∥ : by ring
    end⟩ }

/-- Definition of the derivative of a bilinear map `f`, given at a point `p` by
`q ↦ f(p.1, q.2) + f(q.1, p.2)` as in the standard formula for the derivative of a product.
We define this function here a bounded linear map from `E × F` to `G`. The fact that this
is indeed the derivative of `f` is proved in `is_bounded_bilinear_map.has_fderiv_at` in
`fderiv.lean`-/
def is_bounded_bilinear_map.linear_deriv (h : is_bounded_bilinear_map 𝕜 f) (p : E × F) :
  (E × F) →ₗ[𝕜] G :=
{ to_fun := λq, f (p.1, q.2) + f (q.1, p.2),
  map_add' := λq₁ q₂, begin
    change f (p.1, q₁.2 + q₂.2) + f (q₁.1 + q₂.1, p.2) =
      f (p.1, q₁.2) + f (q₁.1, p.2) + (f (p.1, q₂.2) + f (q₂.1, p.2)),
    simp [h.add_left, h.add_right], abel
  end,
  map_smul' := λc q, begin
    change f (p.1, c • q.2) + f (c • q.1, p.2) = c • (f (p.1, q.2) + f (q.1, p.2)),
    simp [h.smul_left, h.smul_right, smul_add]
  end }

/-- The derivative of a bounded bilinear map at a point `p : E × F`, as a continuous linear map
from `E × F` to `G`. -/
def is_bounded_bilinear_map.deriv (h : is_bounded_bilinear_map 𝕜 f) (p : E × F) : (E × F) →L[𝕜] G :=
(h.linear_deriv p).mk_continuous_of_exists_bound $ begin
  rcases h.bound with ⟨C, Cpos, hC⟩,
  refine ⟨C * ∥p.1∥ + C * ∥p.2∥, λq, _⟩,
  calc ∥f (p.1, q.2) + f (q.1, p.2)∥
    ≤ C * ∥p.1∥ * ∥q.2∥ + C * ∥q.1∥ * ∥p.2∥ : norm_add_le_of_le (hC _ _) (hC _ _)
  ... ≤ C * ∥p.1∥ * ∥q∥ + C * ∥q∥ * ∥p.2∥ : begin
      apply add_le_add,
      exact mul_le_mul_of_nonneg_left (le_max_right _ _) (mul_nonneg (le_of_lt Cpos) (norm_nonneg _)),
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _),
      exact mul_le_mul_of_nonneg_left (le_max_left _ _) (le_of_lt Cpos),
  end
  ... = (C * ∥p.1∥ + C * ∥p.2∥) * ∥q∥ : by ring
end

@[simp] lemma is_bounded_bilinear_map_deriv_coe (h : is_bounded_bilinear_map 𝕜 f) (p q : E × F) :
  h.deriv p q = f (p.1, q.2) + f (q.1, p.2) := rfl

variables (𝕜)

/-- The function `lmul_left_right : 𝕜' × 𝕜' → (𝕜' →L[𝕜] 𝕜')` is a bounded bilinear map. -/
lemma continuous_linear_map.lmul_left_right_is_bounded_bilinear
  (𝕜' : Type*) [normed_ring 𝕜'] [normed_algebra 𝕜 𝕜'] :
  is_bounded_bilinear_map 𝕜 (continuous_linear_map.lmul_left_right 𝕜 𝕜') :=
{ add_left := λ v₁ v₂ w, by {ext t, simp [add_comm, add_mul]},
  smul_left := λ c v w, by {ext, simp },
  add_right := λ v w₁ w₂, by {ext t, simp [add_comm, mul_add]},
  smul_right := λ c v w, by {ext, simp },
  bound := begin
    refine ⟨1, by linarith, _⟩,
    intros v w,
    rw one_mul,
    apply continuous_linear_map.lmul_left_right_norm_le,
  end }

variables {𝕜}

/-- Given a bounded bilinear map `f`, the map associating to a point `p` the derivative of `f` at
`p` is itself a bounded linear map. -/
lemma is_bounded_bilinear_map.is_bounded_linear_map_deriv (h : is_bounded_bilinear_map 𝕜 f) :
  is_bounded_linear_map 𝕜 (λp : E × F, h.deriv p) :=
begin
  rcases h.bound with ⟨C, Cpos, hC⟩,
  refine is_linear_map.with_bound ⟨λp₁ p₂, _, λc p, _⟩ (C + C) (λp, _),
  { ext q,
    simp [h.add_left, h.add_right], abel },
  { ext q,
    simp [h.smul_left, h.smul_right, smul_add] },
  { refine continuous_linear_map.op_norm_le_bound _
      (mul_nonneg (add_nonneg (le_of_lt Cpos) (le_of_lt Cpos)) (norm_nonneg _)) (λq, _),
    calc ∥f (p.1, q.2) + f (q.1, p.2)∥
      ≤ C * ∥p.1∥ * ∥q.2∥ + C * ∥q.1∥ * ∥p.2∥ : norm_add_le_of_le (hC _ _) (hC _ _)
    ... ≤ C * ∥p∥ * ∥q∥ + C * ∥q∥ * ∥p∥ : by apply_rules [add_le_add, mul_le_mul, norm_nonneg,
      le_of_lt Cpos, le_refl, le_max_left, le_max_right, mul_nonneg]
    ... = (C + C) * ∥p∥ * ∥q∥ : by ring },
end

end bilinear_map

/-- A linear isometry preserves the norm. -/
lemma linear_map.norm_apply_of_isometry (f : E →ₗ[𝕜] F) {x : E} (hf : isometry f) : ∥f x∥ = ∥x∥ :=
by { simp_rw [←dist_zero_right, ←f.map_zero], exact isometry.dist_eq hf _ _ }

/-- Construct a continuous linear equiv from a linear map that is also an isometry with full range. -/
def continuous_linear_equiv.of_isometry (f : E →ₗ[𝕜] F) (hf : isometry f) (hfr : f.range = ⊤) :
  E ≃L[𝕜] F :=
continuous_linear_equiv.of_homothety 𝕜
(linear_equiv.of_bijective f (linear_map.ker_eq_bot.mpr (isometry.injective hf)) hfr)
1 zero_lt_one (λ _, by simp [one_mul, f.norm_apply_of_isometry hf])
