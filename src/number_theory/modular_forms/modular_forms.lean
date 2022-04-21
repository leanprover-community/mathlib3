/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import algebra.module.submodule
import analysis.complex.upper_half_plane
import linear_algebra.general_linear_group
import linear_algebra.special_linear_group
import algebra.direct_sum.ring
import number_theory.modular
import geometry.manifold.mfderiv
universes u v

open complex

open_locale topological_space manifold upper_half_plane

noncomputable theory

local notation `ℍ'`:=(⟨upper_half_plane.upper_half_space ,
 upper_half_plane.upper_half_plane_is_open⟩: topological_space.opens ℂ)

local prefix `↑ₘ`:1024 := @coe _ (matrix (fin 2) (fin 2) _) _

local notation `GL(` n `, ` R `)`⁺:= matrix.GL_pos (fin n) R

local notation `SL(` n `, ` R `)`:= matrix.special_linear_group (fin n) R

variable (M : GL(2, ℝ)⁺)

def slash_k : ℤ → GL(2, ℝ)⁺ → (ℍ → ℂ) → (ℍ → ℂ) := λ k γ f,
  (λ (x : ℍ), f (γ • x) * ( ((↑ₘ γ).det ) : ℝ)^(k-1) * (((↑ₘ γ 1 0 : ℝ) * x +(↑ₘ γ 1 1 : ℝ))^k)⁻¹)

namespace modular_forms

variables (Γ : subgroup SL(2,ℤ)) (C : GL(2, ℝ)⁺) (k: ℤ) (f : (ℍ → ℂ))

localized "notation  f  ` ∣[`:100 k `]`:0 γ :100 := slash_k k γ f" in modular_form

lemma slash_k_right_action (k : ℤ) (A B : GL(2, ℝ)⁺) (f : ℍ → ℂ ) :
  (f ∣[k] A) ∣[k] B = f ∣[k] (A * B):=
begin
  simp_rw slash_k,
  simp  [upper_half_plane.num, upper_half_plane.denom, monoid_hom.map_mul, of_real_mul,
  subgroup.coe_mul,matrix.general_linear_group.coe_det_apply, subtype.val_eq_coe, coe_coe,
  upper_half_plane.coe_smul, units.coe_mul],
  ext1,
  have e1:= upper_half_plane.denom_cocycle A B x,
  simp  [upper_half_plane.denom, upper_half_plane.smul_aux,  upper_half_plane.smul_aux',
  matrix.general_linear_group.coe_mul, coe_fn_coe_base, subgroup.coe_mul,
  matrix.general_linear_group.coe_fn_eq_coe] at e1,
  rw e1,
  dsimp only,
  have e2 := upper_half_plane.mul_smul' A B x,
  have e3 : (A * B) • x = A • B • x , by {convert e2,} ,
  rw e3,
  ring_nf,
  have aux1 : ∀  (a b c d e: ℂ) (k : ℤ), (e^k)⁻¹*a^(k-1) * (b^k)⁻¹ * c^(k -1) * d =
  ( (b * e)^ k)⁻¹ * (c * a)^(k-1) * d, by
  {intros a b c d e k,
  have : (b^k)⁻¹ * ((e)^ k)⁻¹ * (c)^(k-1) * (a)^(k-1) * d = ( (b * e)^ k)⁻¹ * (c * a)^(k-1) * d ,
  by  {ring_exp,
  rw ← mul_assoc,
  have :  (b * e)^ k = b^k * e^k, by {exact mul_zpow₀ b e k,},
  simp_rw [mul_zpow₀, mul_inv₀],
  ring,},
  rw ←this,
  ring,},
  simp_rw aux1,
  end

lemma slash_k_add (k : ℤ) (A : GL(2, ℝ)⁺) (f g : ℍ → ℂ) :
  (f + g) ∣[k] A = (f ∣[k] A) + (g ∣[k] A) :=
begin
  simp only [slash_k, pi.add_apply, matrix.general_linear_group.coe_det_apply, subtype.val_eq_coe,
  coe_coe],
  ext1,
  simp only [pi.add_apply],
  ring,
end

lemma slash_k_mul_one (k : ℤ) (f : ℍ → ℂ) : (f ∣[k] 1) = f :=
begin
 simp_rw slash_k,
 ext1,
 simp,
end

lemma smul_slash_k (k : ℤ) (A : GL(2, ℝ)⁺) (f : ℍ → ℂ ) (c  : ℂ) : (c • f) ∣[k] A = c • (f ∣[k] A):=
begin
  ext1,
  simp_rw slash_k,
  simp only [algebra.id.smul_eq_mul, matrix.general_linear_group.coe_det_apply, pi.smul_apply,
  subtype.val_eq_coe, coe_coe],
  ring,
end

lemma slash_k_mul (k1 k2 : ℤ) (A : GL(2, ℝ)⁺) (f g : ℍ → ℂ) :
  (f * g) ∣[k1+k2] A = (((↑ₘ A).det) : ℝ) • (f ∣[k1] A) * (g ∣[k2] A) :=
begin
  ext1,
  simp [slash_k, matrix.general_linear_group.coe_det_apply, subtype.val_eq_coe, coe_coe,
  ←mul_assoc],
  rw  pi.mul_apply,
  have h1 : ((((↑ₘ A).det) : ℝ)^(k1+k2-1) : ℂ) =
  (((↑ₘ A).det) : ℝ) * (((↑ₘ A).det) : ℝ)^(k1-1) * (((↑ₘ A).det) : ℝ)^(k2-1),
  by {simp only [mul_assoc, matrix.general_linear_group.coe_det_apply, subtype.val_eq_coe, coe_coe],
  rw [←zpow_add₀, ←zpow_one_add₀],
  ring_exp,
  all_goals{ have hd:= (matrix.mem_GL_pos _).1 A.2,
  simp only [subtype.val_eq_coe, matrix.general_linear_group.coe_det_apply] at hd,
  norm_cast,
  apply ne_of_gt hd,},},
  simp only [matrix.general_linear_group.coe_det_apply, subtype.val_eq_coe, coe_coe] at h1,
  rw h1,
  have h2 : ((((↑ₘA 1 0 : ℝ) : ℂ) * (x : ℂ) + ((↑ₘA 1 1 : ℝ)))^(k1 + k2))⁻¹ =
  ((((↑ₘA 1 0 : ℝ) : ℂ) * (x : ℂ) + ((↑ₘA 1 1 : ℝ)))^k1)⁻¹ *
  ((((↑ₘA 1 0 : ℝ) : ℂ) * (x : ℂ) + ((↑ₘA 1 1 : ℝ)))^k2)⁻¹,
  by {simp_rw ← mul_inv₀,
  simp only [coe_coe, inv_inj],
  apply zpow_add₀ (upper_half_plane.denom_ne_zero A x),},
  simp only [coe_coe] at h2,
  rw h2,
  ring,
end

/--The  space of functions that are modular-/
def weakly_modular_submodule (k : ℤ)  (Γ : subgroup SL(2,ℤ)): submodule ℂ (ℍ  → ℂ) := {
  carrier := {f : (ℍ → ℂ) | ∀ (γ : Γ),  (f ∣[k] (γ : GL(2, ℝ)⁺)) = f },
  zero_mem' := by {simp only [set.mem_set_of_eq, coe_coe],
  simp_rw slash_k,
  simp only [forall_const, zero_mul, pi.zero_apply],
  refl, },
  add_mem' := by {intros f g hf hg,
  intro γ,
  rw [slash_k_add k γ f g, hf γ, hg γ], },
  smul_mem' := by {intros c f hf,
  intro γ,
  have : (c • f) ∣[k] γ = c • (f  ∣[k] γ ),
  by {apply smul_slash_k},
  rw (hf γ) at this,
  apply this,}}

lemma wmodular_mem (k : ℤ) (Γ : subgroup SL(2,ℤ)) (f : ℍ → ℂ) :
  f ∈ (weakly_modular_submodule k Γ) ↔  ∀ (γ : Γ), (f ∣[k] (γ : GL(2, ℝ)⁺)) = f := iff.rfl

lemma slash_k_mul_subgroup (k1 k2 : ℤ) (Γ : subgroup SL(2,ℤ)) (A : Γ) (f g : ℍ → ℂ) :
  (f * g) ∣[k1+k2] A = (f ∣[k1] A) * (g ∣[k2] A) :=
begin
  have : (((↑ₘ(A : GL(2,ℝ)⁺)).det): ℝ) = 1,
  by {simp only [coe_coe,matrix.special_linear_group.coe_GL_pos_coe_GL_coe_matrix,
  matrix.special_linear_group.det_coe],},
  simp_rw [slash_k_mul, this , one_smul],
end

/--A function `f : ℍ → ℂ` is modular, of level `Γ` and weight `k ∈ ℤ`, if for every matrix in
 `γ ∈  Γ` we have `f(γ  • z)= (c*z+d)^k f(z)` where `γ= ![![a, b], ![c, d]]`,
 and it acts on `ℍ` via Moebius trainsformations. -/
@[simp]
lemma wmodular_mem' (k : ℤ) (Γ : subgroup SL(2,ℤ)) (f : ℍ → ℂ) :
  f ∈ (weakly_modular_submodule k Γ) ↔  ∀ γ : Γ, ∀ z : ℍ,
  f (γ • z) = ((↑ₘγ 1 0 : ℝ) * z +(↑ₘγ 1 1 : ℝ))^k * f z :=
begin
  simp only [wmodular_mem],
  split,
  {intros h1 γ z,
  have h3 : (f ∣[k] γ) z = f z , by {simp_rw (h1 γ)},
  rw [←h3, slash_k, mul_comm],
  have h55 := inv_mul_cancel (zpow_ne_zero k (upper_half_plane.denom_ne_zero (γ : GL(2, ℝ)⁺) z)),
  simp only [upper_half_plane.denom, upper_half_plane.subgroup_to_sl_moeb, upper_half_plane.sl_moeb,
  coe_coe, matrix.special_linear_group.coe_GL_pos_coe_GL_coe_matrix,
  matrix.special_linear_group.coe_matrix_coe, int.coe_cast_ring_hom, matrix.map_apply,
  of_real_int_cast] at *,
  rw [mul_assoc, h55,←int.coe_cast_ring_hom, ←matrix.special_linear_group.coe_matrix_coe,
  matrix.special_linear_group.det_coe ((γ : SL(2, ℤ) ) : SL(2, ℝ))],
  simp only [of_real_one, one_zpow₀, mul_one]},
  {intros hf γ,
  simp_rw slash_k,
  ext1,
  rw [←upper_half_plane.subgroup_moeb, (hf γ x), mul_comm],
  have h55 := inv_mul_cancel (zpow_ne_zero k (upper_half_plane.denom_ne_zero (γ : GL(2, ℝ)⁺) x)),
  simp_rw upper_half_plane.denom at *,
  simp only [matrix.special_linear_group.coe_GL_pos_coe_GL_coe_matrix, coe_coe,
  matrix.special_linear_group.coe_matrix_coe, int.coe_cast_ring_hom, matrix.map_apply,
  of_real_int_cast] at h55,
  simp only [coe_coe, matrix.special_linear_group.coe_GL_pos_coe_GL_coe_matrix,
  matrix.map_apply, of_real_int_cast],
  rw (matrix.special_linear_group.det_coe ((γ : SL(2, ℤ) ) : SL(2, ℝ))),
  simp only [matrix.special_linear_group.coe_matrix_coe, int.coe_cast_ring_hom, matrix.map_apply,
  of_real_int_cast, of_real_one, one_zpow₀, mul_one],
  simp_rw [← mul_assoc,h55],
  simp},
end

lemma mul_modular  (k_1 k_2 : ℤ) (Γ : subgroup SL(2,ℤ)) (f g : ℍ → ℂ)
  (hf : f ∈  weakly_modular_submodule k_1 Γ)  (hg : g ∈ weakly_modular_submodule k_2 Γ) :
  f * g  ∈  weakly_modular_submodule (k_1 + k_2) Γ :=
begin
  simp only [wmodular_mem', pi.mul_apply, coe_coe] at *,
  intros γ z,
  rw [(hf γ z),(hg γ z)],
  have pown := zpow_add₀ (upper_half_plane.denom_ne_zero (γ : GL(2, ℝ)⁺) z) k_1 k_2,
  simp only [upper_half_plane.denom, coe_fn_coe_base, ne.def,
  matrix.general_linear_group.coe_fn_eq_coe, coe_coe] at pown,
  rw pown,
  ring,
end

/--A function ` f : ℍ → ℂ` is bounded at infinity if there exist real numbers `M,A` such that
for all `z ∈ ℍ` with `im z ≥ A` we have `abs(f (z)) ≤ M`,
 i.e. the function is bounded as you approach `i∞`.  -/
def is_bound_at_infinity := { f : ℍ → ℂ | ∃ (M A : ℝ), ∀ z : ℍ, A ≤ im z → abs (f z) ≤ M }

/--A function ` f : ℍ → ℂ` is zero at infinity if for any `ε > 0` there exist a real
number `A` such that for all `z ∈ ℍ` with `im z ≥ A` we have `abs(f (z)) ≤ ε`,
 i.e. the function tends to zero as you approach `i∞`.  -/
def is_zero_at_infinity :=
  { f : ℍ → ℂ | ∀ ε : ℝ, 0 < ε  → ∃ A : ℝ, ∀ z : ℍ, A ≤ im z  → abs (f z) ≤ ε }

@[simp]lemma bound_mem (f : ℍ → ℂ):
  (f ∈  is_bound_at_infinity ) ↔ ∃ (M A : ℝ), ∀ z : ℍ, A ≤ im z  → abs (f z) ≤ M := iff.rfl

@[simp]lemma zero_at_inf_mem (f : ℍ → ℂ) :
  (f ∈  is_zero_at_infinity  ) ↔
  ∀ ε : ℝ, 0 < ε  → ∃ A : ℝ, ∀ z : ℍ, A ≤ im z  → abs (f z) ≤ ε := iff.rfl

lemma zero_form_is_zero_at_inf : (0 : (ℍ → ℂ)) ∈  is_zero_at_infinity:=
begin
  simp only [ zero_at_inf_mem, gt_iff_lt, ge_iff_le,
  set_coe.forall, subtype.coe_mk],
  intros ε he,
  refine ⟨0,_⟩,
  intros x  h1,
  simp only [complex.abs_zero, pi.zero_apply, he.le],
end

lemma is_zero_at_inf_is_bound (f : ℍ → ℂ): (f ∈ is_zero_at_infinity) → (f ∈ is_bound_at_infinity):=
begin
  simp only [ zero_at_inf_mem, gt_iff_lt, bound_mem, ge_iff_le, set_coe.forall,
  subtype.coe_mk],
  intro H,
  refine ⟨1, by {apply H, linarith}⟩,
end

lemma zero_form_is_bound : (0 : (ℍ → ℂ)) ∈  is_bound_at_infinity:=
begin
 apply is_zero_at_inf_is_bound,
 apply zero_form_is_zero_at_inf,
end

/--This is the submodule of functions that are bounded at infinity-/
def bounded_at_infty_submodule: submodule (ℂ) (ℍ  → ℂ):={
  carrier :={ f : ℍ → ℂ | ∃ (M A : ℝ), ∀ z : ℍ, A ≤ im z → abs (f z) ≤ M },
  zero_mem' :=by {simp only [pi.zero_apply, complex.abs_zero, subtype.forall,
  upper_half_plane.coe_im, set.mem_set_of_eq],
  refine ⟨1 ,0 ,_⟩,
  intros x  h1,
  simp only [zero_le_one, pi.zero_apply, complex.abs_zero, implies_true_iff], },
  add_mem' := by  {intros f g hf hg, begin
  cases hf with Mf hMf,
  cases hg with Mg hMg,
  cases hMf with Af hAMf,
  cases hMg with Ag hAMg,
  existsi (Mf + Mg),
  existsi (max Af Ag),
  intros z hz,
  simp only [pi.add_apply],
  apply le_trans (complex.abs_add _ _),
  apply add_le_add,
  { refine hAMf z _,
  exact le_trans (le_max_left _ _) hz },
  { refine hAMg z _,
  exact le_trans (le_max_right _ _) hz }
  end},
  smul_mem' := by {intros c f hyp,
  begin
  cases hyp with M hM,
  cases hM with A hAM,
  existsi (complex.abs c * M),
  existsi A,
  intros z hz,
  simp only [algebra.id.smul_eq_mul, pi.smul_apply],
  convert (mul_le_mul_of_nonneg_left (hAM z hz) (complex.abs_nonneg c)),
  apply complex.abs_mul,
  end  },}


 /--The submodule of functions that are zero at infinity-/
def zero_at_infty_submodule : submodule (ℂ) (ℍ  → ℂ) := {
  carrier := { f : ℍ → ℂ | ∀ ε : ℝ, 0 < ε  → ∃ A : ℝ, ∀ z : ℍ, A ≤ im z  → abs (f z) ≤ ε },
  zero_mem' := by {simp only [pi.zero_apply, complex.abs_zero, subtype.forall,
  upper_half_plane.coe_im,
  set.mem_set_of_eq],
  intros ε he,
  refine ⟨(-1: ℝ ), _⟩,
  intros x  h1,
  apply he.le,},
  add_mem' := by  {intros f g hf hg ε hε, begin
  cases hf (ε/2) (half_pos hε) with Af hAf,
  cases hg (ε/2) (half_pos hε) with Ag hAg,
  existsi (max Af Ag),
  intros z hz,
  simp only [pi.add_apply],
  apply le_trans (complex.abs_add _ _),
  rw show ε = ε / 2 + ε / 2, by simp only [add_halves'],
  apply add_le_add,
  { refine hAf z (le_trans (le_max_left _ _) hz)},
  { refine hAg z (le_trans (le_max_right _ _) hz)}
  end,},
  smul_mem' := by {intros c f hyp ε hε,
  begin
  by_cases hc : (c = 0),
  { existsi (0 : ℝ ), intros, simp only [hc, pi.zero_apply, complex.abs_zero, zero_smul],
  exact le_of_lt hε },
  have habsinv: 0 < (complex.abs c)⁻¹ :=
  by {simp only [gt_iff_lt, complex.abs_pos, ne.def, inv_pos], exact hc,},
  have hcc: 0 <  (ε / complex.abs c)  :=
  by { rw div_eq_mul_inv, apply mul_pos hε habsinv,},
  {cases hyp (ε / complex.abs c) (hcc) with A hA,
  existsi A,
  intros z hz,
  simp only [complex.abs_mul,algebra.id.smul_eq_mul, pi.smul_apply],
  rw show ε = complex.abs c * (ε / complex.abs c),
  begin
  rw [mul_comm],
  refine (div_mul_cancel _ _).symm,
  simp only [hc, complex.abs_eq_zero, ne.def, not_false_iff]
  end,
  apply mul_le_mul_of_nonneg_left (hA z hz) (complex.abs_nonneg c), }
  end },}

/-- The product of two bounded-at-infinity functions is bounded-at-infinty --/
lemma prod_of_bound_is_bound (f g : ℍ → ℂ) :
  (f ∈ is_bound_at_infinity) ∧ (g ∈ is_bound_at_infinity) → ((f * g) ∈ is_bound_at_infinity) :=
begin
  intro h,
  cases h with hf hg,
  simp [is_bound_at_infinity] at *,
  obtain ⟨Mf, Af, hMAf⟩:= hf,
  obtain ⟨Mg, Ag, hMAg⟩:= hg,
  refine ⟨Mf * Mg, max Af Ag, _⟩,
  intros z hAfg,
  simp only [max_le_iff] at *,
  apply mul_le_mul ( hMAf z hAfg.1) (hMAg z hAfg.2) (complex.abs_nonneg _)
  (le_trans (complex.abs_nonneg (f(z))) (hMAf z hAfg.1 )),
end

/--The extension of a function from `ℍ` to `ℍ'`-/
def hol_extn (f : ℍ → ℂ) : ℍ' → ℂ := λ (z : ℍ'), (f (z : ℍ) )

instance : has_coe (ℍ → ℂ) (ℍ' → ℂ) :=
⟨λ f, hol_extn f ⟩

/-- A function `f : ℍ → ℂ` is a modular form of level `Γ` and weight `k ∈ ℤ` if it is holomorphic,
 Petersson and bounded at infinity -/

  structure is_modular_form_of_lvl_and_weight (Γ : subgroup SL(2,ℤ)) (k : ℤ) (f : ℍ → ℂ) : Prop :=
  (hol      : mdifferentiable 𝓘(ℂ) 𝓘(ℂ) (↑f : ℍ' → ℂ))
  (transf   : f ∈ weakly_modular_submodule k Γ )
  (infinity : ∀ (A : (⊤ : subgroup SL(2,ℤ))), (f ∣[k] A) ∈ is_bound_at_infinity )

lemma mk (Γ : subgroup SL(2,ℤ)) (k : ℤ) (f : ℍ → ℂ)
  (h : mdifferentiable 𝓘(ℂ) 𝓘(ℂ) (↑f : ℍ' → ℂ) )
  (h2: f ∈ weakly_modular_submodule k Γ )
  (h3 : ∀ (A : (⊤ : subgroup SL(2,ℤ))), (f ∣[k] A) ∈ is_bound_at_infinity ) :
  is_modular_form_of_lvl_and_weight Γ k f :={
  hol := h,
  transf := h2,
  infinity := h3,}

lemma mod_mem (Γ : subgroup SL(2,ℤ)) (k : ℤ) (f : ℍ → ℂ) :
  is_modular_form_of_lvl_and_weight Γ k f ↔ mdifferentiable 𝓘(ℂ) 𝓘(ℂ) (↑f : ℍ' → ℂ) ∧
  f ∈ weakly_modular_submodule k Γ  ∧
  (∀ (A : (⊤ : subgroup SL(2,ℤ))), (f ∣[k] A) ∈ is_bound_at_infinity) :=
begin
  split,
  intro hf,
  simp only [hf.hol, hf.transf, true_and, subtype.forall, upper_half_plane.coe_im, coe_coe],
  apply hf.infinity,
  intros h,
  apply mk Γ k f h.1 h.2.1 h.2.2,
end

/-- A function `f : ℍ → ℂ` is a cusp form of level one and weight `k ∈ ℤ` if it is holomorphic,
 Petersson and zero at infinity -/
structure is_cusp_form_of_lvl_and_weight (Γ : subgroup SL(2,ℤ)) (k : ℤ) (f : ℍ → ℂ) : Prop :=
  (hol      : mdifferentiable 𝓘(ℂ) 𝓘(ℂ) (↑f : ℍ' → ℂ))
  (transf   : f ∈ weakly_modular_submodule k Γ)
  (infinity : ∀ (A : (⊤ : subgroup SL(2,ℤ))), (f ∣[k] A) ∈ is_zero_at_infinity )

lemma is_cuspform_mk (Γ : subgroup SL(2,ℤ)) (k : ℤ) (f : ℍ → ℂ)
  (h : mdifferentiable 𝓘(ℂ) 𝓘(ℂ) (↑f : ℍ' → ℂ) )
  (h2 : f ∈ weakly_modular_submodule k Γ)
  (h3 :  ∀ (A : (⊤ : subgroup SL(2,ℤ))), (f ∣[k] A) ∈ is_zero_at_infinity ) :
  is_cusp_form_of_lvl_and_weight Γ k f :={
  hol := h,
  transf := h2,
  infinity := h3}

lemma cusp_mem (Γ : subgroup SL(2,ℤ)) (k : ℤ) (f : ℍ → ℂ): is_cusp_form_of_lvl_and_weight Γ k f ↔
  mdifferentiable 𝓘(ℂ) 𝓘(ℂ) (↑f : ℍ' → ℂ) ∧
  f ∈ weakly_modular_submodule k Γ ∧
  ( ∀ (A : (⊤ : subgroup SL(2,ℤ))), (f ∣[k] A) ∈ is_zero_at_infinity) :=
begin
  split,
  intro hf,
  simp only [hf.hol, hf.transf, true_and, subtype.forall, upper_half_plane.coe_im, coe_coe],
  apply hf.infinity,
  intro h,
  apply is_cuspform_mk Γ k f h.1 h.2.1 h.2.2,
end


/-- The zero modular form is a cusp form-/
lemma zero_cusp_form :  (is_cusp_form_of_lvl_and_weight Γ k) (0 : (ℍ → ℂ)) :=
  { hol := by {apply mdifferentiable_zero,},
  transf := (weakly_modular_submodule k Γ).zero_mem',
  infinity := by {simp only [zero_at_inf_mem, gt_iff_lt, ge_iff_le],
  intros A ε he,
  use (-1: ℝ ),
  intros x  h1,
  simp only [slash_k, complex.abs_zero, zero_mul, pi.zero_apply, complex.abs_mul],
  linarith}}

lemma is_modular_form_of_lvl_and_weight_of_is_cusp_form_of_lvl_and_weight (f : ℍ → ℂ)
  (h : is_cusp_form_of_lvl_and_weight Γ k f) : is_modular_form_of_lvl_and_weight Γ k f :={
  hol := h.1,
  transf := h.2,
  infinity := by {intro A, have h3:=  h.3 A, apply  is_zero_at_inf_is_bound _ h3,}}

 /-- The zero modular form is a modular form-/
lemma zero_mod_form :  (is_modular_form_of_lvl_and_weight Γ (k : ℤ) ) (0 : (ℍ → ℂ)):=
begin
  apply_rules [is_modular_form_of_lvl_and_weight_of_is_cusp_form_of_lvl_and_weight, zero_cusp_form],
end

/-- This is the space of modular forms of level `Γ` and weight `k`-/
def space_of_mod_forms_of_weight_and_level (Γ : subgroup SL(2,ℤ)) (k : ℤ) : submodule ℂ (ℍ → ℂ) :={
  carrier:={ f : ℍ → ℂ | is_modular_form_of_lvl_and_weight Γ k f},
  zero_mem':=by {simp only [set.mem_set_of_eq], apply zero_mod_form, },
  add_mem' :=by {simp only [set.mem_set_of_eq], intros a b ha hb,
  refine ⟨mdifferentiable_add _ _ ha.hol hb.hol,
  (weakly_modular_submodule  k Γ).add_mem' ha.transf hb.transf, by{intro A,
  rw slash_k_add, apply (bounded_at_infty_submodule.add_mem' (ha.infinity A) (hb.infinity A))}⟩, },
  smul_mem' := by {intros c f hf,
  refine ⟨mdifferentiable_smul _ _ hf.hol, (weakly_modular_submodule  k Γ).smul_mem' _ hf.transf,
  by {intro A, rw smul_slash_k, apply (bounded_at_infty_submodule.smul_mem' c (hf.infinity A))}⟩,},}

localized "notation `M(`k`, `Γ`)`:= space_of_mod_forms_of_weight_and_level Γ k" in modular_forms

/-- This is the space of cuspforms of level `Γ` and weigth `k`-/
def space_of_cusp_forms_of_weight_and_level (Γ : subgroup SL(2,ℤ)) (k : ℤ): submodule ℂ (ℍ → ℂ) :={
  carrier := { f : ℍ → ℂ | is_cusp_form_of_lvl_and_weight Γ k f},
  zero_mem' := by {simp only [set.mem_set_of_eq], apply zero_cusp_form, },
  add_mem' := by {simp only [set.mem_set_of_eq], intros a b ha hb,
  refine ⟨mdifferentiable_add _ _ ha.hol hb.hol,
  (weakly_modular_submodule  k Γ).add_mem' ha.transf hb.transf, by{intro A,
  rw slash_k_add, apply (zero_at_infty_submodule.add_mem' (ha.infinity A) (hb.infinity A))}⟩, },
  smul_mem' := by {intros c f hf,
  refine ⟨mdifferentiable_smul _ _ hf.hol, (weakly_modular_submodule  k Γ).smul_mem' _ hf.transf,
  by {intro A, rw smul_slash_k, apply (zero_at_infty_submodule.smul_mem' c (hf.infinity A))}⟩,},}

localized "notation `S(`k`, `Γ`)`:= space_of_cusp_forms_of_weight_and_level Γ k" in modular_forms

lemma mul_modform (k_1 k_2 : ℤ) (Γ : subgroup SL(2,ℤ)) (f g : ℍ → ℂ)
  (hf : f ∈ M(k_1, Γ)) (hg : g ∈ M(k_2, Γ)) : f * g  ∈  M(k_1+k_2, Γ) :=
begin
  refine ⟨mdifferentiable_mul _ _ hf.1 hg.1, mul_modular  _ _ _ _ _ hf.2 hg.2 ,
  by {intro A, rw slash_k_mul_subgroup k_1 k_2 ⊤ A f g,
  apply prod_of_bound_is_bound _ _ ⟨(hf.3 A), (hg.3 A)⟩}⟩,
end

end modular_forms
