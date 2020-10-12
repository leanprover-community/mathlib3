/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Frédéric Dupuis
-/
import analysis.normed_space.hahn_banach
import analysis.normed_space.banach
import analysis.normed_space.inner_product
import analysis.normed_space.operator_norm

/-!
# The topological dual of a normed space

In this file we define the topological dual of a normed space, and the bounded linear map from
a normed space into its double dual.

We also prove that, for base field such as the real or the complex numbers, this map is an isometry.
More generically, this is proved for any field in the class `has_exists_extension_norm_eq`, i.e.,
satisfying the Hahn-Banach theorem.

In the case of inner product spaces, we define `to_dual` which maps an element x of the space
to `λ y, ⟪x, y⟫`. We also give the Fréchet-Riesz representation, which states that every element
of the dual of a Hilbert space `E` has the form `λ u, ⟪x, u⟫` for some `x : E`.

## References

* [M. Einsiedler and T. Ward, *Functional Analysis, Spectral Theory, and Applications*][EinsiedlerWard2017]

## Tags

dual, Fréchet-Riesz
-/

noncomputable theory
universes u v

namespace normed_space

section general
variables (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
variables (E : Type*) [normed_group E] [normed_space 𝕜 E]

/-- The topological dual of a normed space `E`. -/
@[derive [has_coe_to_fun, normed_group, normed_space 𝕜]] def dual := E →L[𝕜] 𝕜

instance : inhabited (dual 𝕜 E) := ⟨0⟩

/-- The inclusion of a normed space in its double (topological) dual. -/
def inclusion_in_double_dual' (x : E) : (dual 𝕜 (dual 𝕜 E)) :=
linear_map.mk_continuous
  { to_fun := λ f, f x,
    map_add'    := by simp,
    map_smul'   := by simp }
  ∥x∥
  (λ f, by { rw mul_comm, exact f.le_op_norm x } )

@[simp] lemma dual_def (x : E) (f : dual 𝕜 E) :
  ((inclusion_in_double_dual' 𝕜 E) x) f = f x := rfl

lemma double_dual_bound (x : E) : ∥(inclusion_in_double_dual' 𝕜 E) x∥ ≤ ∥x∥ :=
begin
  apply continuous_linear_map.op_norm_le_bound,
  { simp },
  { intros f, rw mul_comm, exact f.le_op_norm x, }
end

/-- The inclusion of a normed space in its double (topological) dual, considered
   as a bounded linear map. -/
def inclusion_in_double_dual : E →L[𝕜] (dual 𝕜 (dual 𝕜 E)) :=
linear_map.mk_continuous
  { to_fun := λ (x : E), (inclusion_in_double_dual' 𝕜 E) x,
    map_add'    := λ x y, by { ext, simp },
    map_smul'   := λ (c : 𝕜) x, by { ext, simp } }
  1
  (λ x, by { convert double_dual_bound _ _ _, simp } )

instance [complete_space 𝕜] : complete_space (dual 𝕜 E) := continuous_linear_map.complete_space

end general

section bidual_isometry

variables {𝕜 : Type v} [nondiscrete_normed_field 𝕜] [normed_algebra ℝ 𝕜]
[has_exists_extension_norm_eq.{u} 𝕜]
{E : Type u} [normed_group E] [normed_space 𝕜 E]

/-- If one controls the norm of every `f x`, then one controls the norm of `x`.
    Compare `continuous_linear_map.op_norm_le_bound`. -/
lemma norm_le_dual_bound (x : E) {M : ℝ} (hMp: 0 ≤ M) (hM : ∀ (f : dual 𝕜 E), ∥f x∥ ≤ M * ∥f∥) :
  ∥x∥ ≤ M :=
begin
  classical,
  by_cases h : x = 0,
  { simp only [h, hMp, norm_zero] },
  { obtain ⟨f, hf⟩ : ∃ g : E →L[𝕜] 𝕜, _ := exists_dual_vector x h,
    calc ∥x∥ = ∥norm' 𝕜 x∥ : (norm_norm' _ _ _).symm
    ... = ∥f x∥ : by rw hf.2
    ... ≤ M * ∥f∥ : hM f
    ... = M : by rw [hf.1, mul_one] }
end

/-- The inclusion of a real normed space in its double dual is an isometry onto its image.-/
lemma inclusion_in_double_dual_isometry (x : E) : ∥inclusion_in_double_dual 𝕜 E x∥ = ∥x∥ :=
begin
  apply le_antisymm,
  { exact double_dual_bound 𝕜 E x },
  { rw continuous_linear_map.norm_def,
    apply real.lb_le_Inf _ continuous_linear_map.bounds_nonempty,
    rintros c ⟨hc1, hc2⟩,
    exact norm_le_dual_bound x hc1 hc2 },
end

end bidual_isometry

end normed_space

namespace inner_product_space
open is_R_or_C continuous_linear_map

variables (𝕜 : Type*)
variables {E : Type*} [is_R_or_C 𝕜] [inner_product_space 𝕜 E]
variables {F : Type*} [inner_product_space ℝ F]
local notation `⟪`x`, `y`⟫` := @inner 𝕜 E _ x y
local postfix `†`:90 := @is_R_or_C.conj 𝕜 _

/--
Given some x in an inner product space, we can define its dual as the continuous linear map
λ y, ⟪x, y⟫.
-/
def to_dual_fn (x : E) : normed_space.dual 𝕜 E :=
linear_map.mk_continuous
{ to_fun := λ y, ⟪x, y⟫,
  map_add' := λ _ _, inner_add_right,
  map_smul' := λ _ _, inner_smul_right }
∥x∥
(λ y, by { rw [is_R_or_C.norm_eq_abs], exact abs_inner_le_norm _ _ })

@[simp] lemma to_dual_fn_def {x y : E} : to_dual_fn 𝕜 x y = ⟪x, y⟫ := rfl

variables {𝕜}

@[simp] lemma to_dual_fn_zero : to_dual_fn 𝕜 (0 : E) = 0 :=
by { ext, simp [to_dual_fn] }

lemma to_dual_fn_add {x y : E} : to_dual_fn 𝕜 (x + y) = to_dual_fn 𝕜 x + to_dual_fn 𝕜 y :=
by { ext, simp [inner_add_left] }

/--
Fréchet-Riesz representation: any ℓ in the dual of a Hilbert space E is of the form
λ u, ⟪y, u⟫ for some y in E.
-/
lemma exists_elem_of_mem_dual [complete_space E] (ℓ : normed_space.dual 𝕜 E) :
  ∃ y : E, ℓ = to_dual_fn 𝕜 y :=
begin
  set Y := ker ℓ with hY,
  by_cases htriv : Y = ⊤,
  { have hℓ : ℓ = 0,
    { have h' := linear_map.ker_eq_top.mp htriv,
      rw [←coe_zero] at h',
      apply coe_injective,
      exact h' },
    exact ⟨0, by simp [hℓ]⟩ },
  { have Ycomplete := is_complete_ker ℓ,
    rw [submodule.eq_top_iff_orthogonal_eq_bot Ycomplete, ←hY] at htriv,
    change Y.orthogonal ≠ ⊥ at htriv,
    rw [submodule.ne_bot_iff] at htriv,
    obtain ⟨z : E, hz : z ∈ Y.orthogonal, z_ne_0 : z ≠ 0⟩ := htriv,
    refine ⟨((ℓ z)† / ⟪z, z⟫) • z, _⟩,
    ext x,
    have h₁ : (ℓ z) • x - (ℓ x) • z ∈ Y,
    { rw [mem_ker, map_sub, map_smul, map_smul, algebra.id.smul_eq_mul, algebra.id.smul_eq_mul,
          mul_comm],
      exact sub_self (ℓ x * ℓ z) },
    have h₂ : (ℓ z) * ⟪z, x⟫ = (ℓ x) * ⟪z, z⟫,
    { have h₃ := calc
        0    = ⟪z, (ℓ z) • x - (ℓ x) • z⟫       : by { rw [(Y.mem_orthogonal' z).mp hz], exact h₁ }
         ... = ⟪z, (ℓ z) • x⟫ - ⟪z, (ℓ x) • z⟫  : by rw [inner_sub_right]
         ... = (ℓ z) * ⟪z, x⟫ - (ℓ x) * ⟪z, z⟫  : by simp [inner_smul_right],
      exact sub_eq_zero.mp (eq.symm h₃) },
    have h₄ := calc
      ⟪((ℓ z)† / ⟪z, z⟫) • z, x⟫ = (ℓ z) / ⟪z, z⟫ * ⟪z, x⟫
            : by simp [inner_smul_left, conj_div, conj_conj]
                            ... = (ℓ z) * ⟪z, x⟫ / ⟪z, z⟫
            : by rw [←div_mul_eq_mul_div]
                            ... = (ℓ x) * ⟪z, z⟫ / ⟪z, z⟫
            : by rw [h₂]
                            ... = ℓ x
            : begin
                have : ⟪z, z⟫ ≠ 0,
                { change z = 0 → false at z_ne_0,
                  rwa ←inner_self_eq_zero at z_ne_0 },
                field_simp [this]
              end,
    exact h₄.symm }
end

variables (𝕜)

@[simp] lemma to_dual_fn_eq_iff_eq {x y : E} : to_dual_fn 𝕜 x = to_dual_fn 𝕜 y ↔ x = y :=
begin
  classical,
  refine ⟨_, by {rintro rfl, refl}⟩,
  intro h,
  rw [continuous_linear_map.ext_iff] at h,
  change ∀ z, ⟪x, z⟫ = ⟪y, z⟫ at h,
  have h₁ : ∀ z, ⟪x - y, z⟫ = 0 := λ z, by { rw [inner_sub_left, h z], exact sub_self ⟪y, z⟫ },
  by_contradiction,
  exact (sub_ne_zero.mpr a) (inner_self_eq_zero.mp (h₁ (x - y)))
end

variables {𝕜}

def to_primal [complete_space E] (x : normed_space.dual 𝕜 E) : E :=
  classical.some (exists_elem_of_mem_dual x)

lemma to_primal_eq_iff_eq [complete_space E] {x y : normed_space.dual 𝕜 E} :
  to_primal x = to_primal y ↔ x = y :=
begin
  refine ⟨_, by { rintro rfl, refl }⟩,
  intro h,
  have hx := classical.some_spec (exists_elem_of_mem_dual x),
  have hy := classical.some_spec (exists_elem_of_mem_dual y),
  rw [hx, hy],
  simpa [to_primal, function.right_inverse, function.left_inverse] using h,
end

lemma primal_dual [complete_space E] {x : E} : to_primal (to_dual_fn 𝕜 x) = x :=
begin
  have h := (classical.some_spec (exists_elem_of_mem_dual (to_dual_fn 𝕜 x))).symm,
  rwa [to_dual_fn_eq_iff_eq] at h,
end

lemma dual_primal [complete_space E] {ℓ : normed_space.dual 𝕜 E} : to_dual_fn 𝕜 (to_primal ℓ) = ℓ :=
begin
  let x := classical.some (exists_elem_of_mem_dual ℓ),
  have hx := classical.some_spec (exists_elem_of_mem_dual ℓ),
  rw [hx],
  apply (to_dual_fn_eq_iff_eq 𝕜).mpr,
  exact primal_dual,
end

lemma dual_apply [complete_space E] {ℓ : normed_space.dual 𝕜 E} {x : E} : ℓ x = ⟪to_primal ℓ, x⟫ :=
begin
  obtain ⟨ℓ', hℓ⟩ := exists_elem_of_mem_dual ℓ,
  rw [hℓ, primal_dual, to_dual_fn],
  simp,
end

lemma to_primal_zero [complete_space E] : to_primal (0 : normed_space.dual 𝕜 E) = 0 :=
begin
  have : 0 = to_primal (to_dual_fn 𝕜 (0 : E)) := primal_dual.symm,
  rw [this],
  simp only [to_dual_fn_zero],
end

lemma to_primal_smul [complete_space E] {r : 𝕜} {ℓ : normed_space.dual 𝕜 E} :
  to_primal (r • ℓ) = r† • to_primal ℓ :=
begin
  rw [←to_dual_fn_eq_iff_eq 𝕜, dual_primal],
  ext,
  simp only [algebra.id.smul_eq_mul, smul_apply, to_dual_fn_def, inner_smul_left, conj_conj, ←dual_apply],
end

lemma to_primal_add [complete_space E] {x y : normed_space.dual 𝕜 E} :
  to_primal (x + y) = to_primal x + to_primal y :=
by rw [←to_dual_fn_eq_iff_eq 𝕜, to_dual_fn_add, dual_primal, dual_primal, dual_primal]

lemma dual_norm_eq_primal_norm [complete_space E] {ℓ : normed_space.dual 𝕜 E} : ∥ℓ∥ = ∥to_primal ℓ∥ :=
begin
  have h₁ : ∀ x, ∥ℓ x∥ ≤ ∥to_primal ℓ∥ * ∥x∥,
  { intro x,
    simp [dual_apply, norm_eq_abs, abs_inner_le_norm] },
  apply le_antisymm (cInf_le bounds_bdd_below ⟨norm_nonneg _, h₁⟩),
  have h₂ : ∥to_primal ℓ∥ ∈ {c : ℝ | 0 ≤ c ∧ ∀ (x : E), ∥ℓ x∥ ≤ c * ∥x∥} := ⟨norm_nonneg _, h₁⟩,
  refine le_cInf (set.nonempty_of_mem h₂) _,
  rintro b ⟨hb0, hb⟩,
  have hb' := hb (to_primal ℓ),
  rw [dual_apply, norm_eq_abs, ←inner_self_re_abs, inner_self_eq_norm_square] at hb',
  by_cases hℓ : ℓ = 0,
  { rw [hℓ, to_primal_zero],
    convert hb0,
    exact norm_zero },
  { change ℓ ≠ 0 at hℓ,
    have hℓ0 : 0 < ∥to_primal ℓ∥,
    { have : to_primal ℓ ≠ 0,
      { rw [←to_primal_zero],
        intro H,
        rw [to_primal_eq_iff_eq] at H,
        exact hℓ H },
      exact norm_pos_iff.mpr this },
    exact (mul_le_mul_right hℓ0).mp hb' }
end

lemma inner_eq_to_dual_apply {x y : E} : ⟪x, y⟫ = (to_dual_fn 𝕜 x) y := by simp only [to_dual_fn_def]

instance [complete_space E] : has_inner 𝕜 (normed_space.dual 𝕜 E) :=
{ inner := λ x y, ⟪to_primal y, to_primal x⟫ }

instance [complete_space E] : inner_product_space 𝕜 (normed_space.dual 𝕜 E) :=
{ norm_sq_eq_inner := assume ℓ,
  begin
    change ∥ℓ∥ ^ 2 = re ⟪to_primal ℓ, to_primal ℓ⟫,
    rw [dual_norm_eq_primal_norm, inner_self_eq_norm_square, pow_two],
  end,
  conj_sym := λ x y, inner_conj_sym _ _,
  nonneg_im := λ x, inner_self_im_zero,
  add_left := assume x y z,
  begin
    change ⟪to_primal z, to_primal (x + y)⟫ = ⟪to_primal z, to_primal x⟫ + ⟪to_primal z, to_primal y⟫,
    rw [to_primal_add],
    simp [inner_add_right],
  end,
  smul_left := assume x y r,
  begin
    change ⟪to_primal y, to_primal (r • x)⟫ = conj r * ⟪to_primal y, to_primal x⟫,
    rw [to_primal_smul, inner_smul_right],
  end }

def to_dual_real [complete_space F] : F ≃L[ℝ] (normed_space.dual ℝ F) :=
{
  to_linear_equiv :=
  { to_fun := λ x, to_dual_fn ℝ x,
    map_add' := λ x y, by { ext z, simp [inner_add_left] },
    map_smul' := λ c x, by { ext z, simp [inner_smul_left] },
    inv_fun := λ ℓ, to_primal ℓ,
    left_inv := assume z,
    begin
      have h₁ := (classical.some_spec (exists_elem_of_mem_dual (to_dual_fn ℝ z))).symm,
      rwa [to_dual_fn_eq_iff_eq] at h₁
    end,
    right_inv := assume z,
    begin
      obtain ⟨y, hy⟩ := exists_elem_of_mem_dual z,
      conv_rhs { rw [hy] },
      have h := (classical.some_spec (exists_elem_of_mem_dual z)).symm,
      simpa [to_primal, function.right_inverse, function.left_inverse, h],
    end },
  continuous_to_fun := begin

  end,
  continuous_inv_fun := sorry,
}


end inner_product_space
