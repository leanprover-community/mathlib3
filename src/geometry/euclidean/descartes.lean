/-
Copyright (c) 2022 Archana .... . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import geometry.euclidean.triangle
import linear_algebra.general_linear_group
import data.real.basic
import linear_algebra.matrix.bilinear_form
import analysis.normed_space.pi_Lp
--import tactic.polyrith
--import analysis.inner_product_space.pi_L2

/-!
# Spheres

This file proves

## Main theorems

* `mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi`: Intersecting Chords Theorem (Freek No. 55).

-/

open_locale big_operators real_inner_product_space

open finite_dimensional

noncomputable theory

----------------------------AREA FOR MESSING AROUND -----------------
/-
-

universe u

variables (E₁ E₂ : Type u) [inner_product_space ℝ E₁] [inner_product_space ℝ E₂]

@[derive [add_comm_group, module ℝ]]def new_space := E₁ × E₂

instance : inner_product_space ℝ (new_space E₁ E₂) :=
begin
  have := pi_Lp 2 (![E₁, E₂] : (fin 2) → (Type u)),
  let E : (fin 2) → (Type*) := ![E₁, E₂],
end

def new_inner : new_space E₁ E₂ →ₗ[ℝ] new_space E₁ E₂ →ₗ[ℝ] ℝ := linear_map.mk₂ ℝ
  (λ ⟨x₁, z₁⟩ ⟨x₂, z₂⟩, ⟪x₁, x₂⟫ + ⟪z₁, z₂⟫)
  -- (λ ⟨x₁, z₁⟩ ⟨x₂, z₂⟩ ⟨x₃, z₃⟩, by dsimp [new_inner._match_2, new_inner._match_1];
  --   rw inner_add_left; ring)
  begin
  end
  (λ r ⟨x₁, z₁⟩ ⟨x₂, z₂⟩, by dsimp [new_inner._match_2, new_inner._match_1]; rw inner_smul_left;
    simp only [is_R_or_C.conj_to_real]; ring)
  (λ ⟨x₁, z₁⟩ ⟨x₂, z₂⟩ ⟨x₃, z₃⟩, by dsimp [new_inner._match_2, new_inner._match_1];
    rw inner_add_right; ring)
  (λ r ⟨x₁, z₁⟩ ⟨x₂, z₂⟩, by dsimp [new_inner._match_2, new_inner._match_1]; rw inner_smul_right;
    simp only [is_R_or_C.conj_to_real]; ring)



example (E : Type*) {n : ℕ} [inner_product_space ℝ E] [finite_dimensional ℝ E]
  [fact (finrank ℝ E = n)] [fact (n ≠ 0)] (vs : fin n → E) (Q : E →ₗ[ℝ] E →ₗ[ℝ] ℝ )
  (G : matrix (fin n) (fin n) ℝ) (hG : invertible G) (h : ∀ i j, Q (vs i) (vs j) = G i j) :
  linear_independent ℝ vs
:= begin
  sorry,
end

#exit

-
-/

variables (E : Type*) {n : ℕ} [inner_product_space ℝ E] [finite_dimensional ℝ E]
[fact (finrank ℝ E = n)] [fact (n ≠ 0)]

/-- A (positively oriented, n-1) `sphere` in dimension `n` has a `n`-dimensional center, and
  positive radius -/
structure sphere :=
(center : E)
(radius : ℝ)
(rad_pos : 0 < radius)

/-- The inversive coordinate system attached to a sphere `S` is given by the `n+2`-tuple:
  `(bend, bend*center, cobend)`. -/
@[derive [add_comm_group, module ℝ]]def inv_coord_space := ((fin 2) → ℝ) × E

variables {E}

/-- The `bend` is the reciprocal of the radius -/
def bend (S : sphere E) : ℝ := 1 / S.radius

/-- The `bend` is nonzero -/
lemma bend_nonzero (S : sphere E) : bend S ≠ 0 := one_div_ne_zero S.rad_pos.ne.symm

/-- The square norm in Euclidean space -/
def norm_sq (z : E) := ⟪z,z⟫

/-- The `cobend` is the reciprocal of the coradius; the latter is the radius of the inversion of
  the sphere through the unit sphere -/
def cobend (S : sphere E) : ℝ := (norm_sq (S.center) - S.radius ^ 2) * (bend S)

/-- Two spheres are `tangent` if the (square of) the distance between their centers is the
 (square of) the sum of their radii -/
def tangent (S₁ S₂ : sphere E) : Prop :=
  ∥S₁.center - S₂.center∥ = S₁.radius + S₂.radius

lemma tangent_iff (S₁ S₂ : sphere E) : tangent S₁ S₂ ↔
  norm_sq (S₁.center - S₂.center) = (S₁.radius + S₂.radius)^2 :=
begin
  convert (sq_eq_sq (norm_nonneg _) _).symm,
  { convert (norm_sq_eq_inner (S₁.center - S₂.center)).symm,
    simp [norm_sq], },
  have := S₁.rad_pos,
  have := S₂.rad_pos,
  linarith,
end

/-- The inversive coordinate system attached to a sphere `S` is given by the `n+2`-tuple:
  `(bend, cobend, bend*center)`. -/
def inv_coords (S : sphere E) : inv_coord_space E := ⟨![bend S, cobend S], (bend S) • S.center⟩

def inv_prod : (inv_coord_space E) →ₗ[ℝ] (inv_coord_space E) →ₗ[ℝ] ℝ := linear_map.mk₂ ℝ
  (λ ⟨x₁, z₁⟩ ⟨x₂, z₂⟩, (x₁ 0) * (x₂ 1) + (x₁ 1) * (x₂ 0) - 2 * ⟪z₁, z₂⟫)
  (λ ⟨x₁, z₁⟩ ⟨x₂, z₂⟩ ⟨x₃, z₃⟩, by dsimp [inv_prod._match_2, inv_prod._match_1];
    rw inner_add_left; ring)
  (λ r ⟨x₁, z₁⟩ ⟨x₂, z₂⟩, by dsimp [inv_prod._match_2, inv_prod._match_1]; rw inner_smul_left;
    simp only [is_R_or_C.conj_to_real]; ring)
  (λ ⟨x₁, z₁⟩ ⟨x₂, z₂⟩ ⟨x₃, z₃⟩, by dsimp [inv_prod._match_2, inv_prod._match_1];
    rw inner_add_right; ring)
  (λ r ⟨x₁, z₁⟩ ⟨x₂, z₂⟩, by dsimp [inv_prod._match_2, inv_prod._match_1]; rw inner_smul_right;
    simp only [is_R_or_C.conj_to_real]; ring)

lemma inv_prod_self (S : sphere E) : inv_prod (inv_coords S) (inv_coords S) = -2 :=
begin
  have := S.rad_pos.ne',
  simp only [inv_prod, inv_coords, cobend, norm_sq, inner_smul_left, inner_smul_right, bend,
    one_div, linear_map.mk₂_apply, matrix.cons_val_one, matrix.head_cons, is_R_or_C.conj_to_real,
    matrix.cons_vec_bit0_eq_alt0, matrix.cons_append, matrix.empty_append, matrix.cons_vec_alt0],
  field_simp,
  ring,
end

lemma inv_prod_tangent (S₁ S₂ : sphere E) (h : tangent S₁ S₂) :
  inv_prod (inv_coords S₁) (inv_coords S₂) = 2 :=
begin
  have := S₁.rad_pos.ne',
  have := S₂.rad_pos.ne',
  simp only [inv_prod, inv_coords, cobend, inner_smul_left, inner_smul_right, norm_sq, bend,
    one_div, linear_map.mk₂_apply, matrix.cons_val_one, matrix.head_cons, is_R_or_C.conj_to_real,
    matrix.cons_vec_bit0_eq_alt0, matrix.cons_append, matrix.empty_append, matrix.cons_vec_alt0],
  simp only [tangent_iff, norm_sq, inner_sub_left, inner_sub_right, real_inner_comm] at h,
  field_simp,
  linear_combination S₂.radius * S₁.radius * h,
end

def inv_prod_aux (vs : basis (fin (n+2)) ℝ (inv_coord_space E))
  (G : matrix (fin (n+2)) (fin (n+2)) ℝ) : (inv_coord_space E) →ₗ[ℝ] (inv_coord_space E) →ₗ[ℝ] ℝ :=
begin
 refine linear_map.mk₂ ℝ (λ w₁ w₂, ∑ i, ∑ j, inv_prod w₁ (vs i) * inv_prod w₂ (vs j) * (G⁻¹ i j))
  _ _ _ _,
  repeat {sorry},
end

lemma inv_prod_aux_apply (vs : basis (fin (n+2)) ℝ (inv_coord_space E))
  (G : matrix (fin (n+2)) (fin (n+2)) ℝ) (w₁ w₂ : (inv_coord_space E)) :
  inv_prod_aux vs G w₁ w₂ = ∑ i, ∑ j, inv_prod w₁ (vs i) * inv_prod w₂ (vs j) * (G⁻¹ i j)
:= rfl

lemma inv_prod_apply (vs : basis (fin (n+2)) ℝ (inv_coord_space E))
  (G : matrix (fin (n+2)) (fin (n+2)) ℝ) (hG : invertible G)
  (hvG : ∀ i j, G i j = inv_prod (vs i) (vs j)) :
  inv_prod.flip = inv_prod_aux vs G :=
begin
  refine linear_map.ext_basis vs vs _,
  intros i j,
  rw linear_map.flip_apply,
  rw ←hvG j i,
  rw inv_prod_aux_apply,
  simp_rw [←hvG],
  simp_rw mul_comm (G i _),
  simp_rw mul_assoc,
  rw finset.sum_comm,
  simp_rw ←finset.mul_sum,
  simp_rw ←matrix.mul_apply,
  simp_rw matrix.mul_inv_of_invertible,
  simp_rw matrix.one_apply,
  simp,
end

/-- The covector which gives the bend when paired with an inversive coordinate -/
def bend_covector : inv_coord_space E := (![0,1],0)

@[simp] lemma finset.filter_eq_univ {α : Type*} [fintype α] [decidable_eq α] (i : α) :
  finset.univ.filter (eq i) = {i} :=
by ext; simp [eq_comm]

@[simp] lemma finset.filter_eq_univ' {α : Type*} [fintype α] [decidable_eq α] (i : α) :
  finset.univ.filter (λ x, x = i) = {i} :=
by ext; simp [eq_comm]

@[simp] lemma finset.filter_ne_univ {α : Type*} [fintype α] [decidable_eq α] (i : α) :
  finset.univ.filter (λ x, x ≠ i) = finset.univ \ {i} :=
by ext; simp [eq_comm]

@[simp] lemma finset.filter_ne_univ' {α : Type*} [fintype α] [decidable_eq α] (i : α) :
  finset.univ.filter (λ x, i ≠ x) = finset.univ \ {i} :=
by ext; simp [eq_comm]

@[simp] lemma finset.filter_eq_singleton {α : Type*} [fintype α] [decidable_eq α] (i k : α) :
  finset.filter (eq i) {k} = if i = k then {i} else ∅ :=
by split_ifs; ext; simp [h] {contextual := tt}

@[simp] lemma finset.filter_eq_singleton' {α : Type*} [fintype α] [decidable_eq α] (i k : α) :
  finset.filter (λ x, x = i) {k} = if i = k then {i} else ∅ :=
by split_ifs; ext; simp [h, eq_comm] {contextual := tt}

@[simp] lemma finset.filter_ne_singleton {α : Type*} [fintype α] [decidable_eq α] (i k : α) :
  finset.filter (ne i) {k} = if i = k then ∅ else {k} :=
by split_ifs; ext; simp [h] {contextual := tt}

@[simp] lemma finset.filter_ne_singleton' {α : Type*} [fintype α] [decidable_eq α] (i k : α) :
  finset.filter (λ x, x ≠ i) {k} = if i = k then ∅ else {k} :=
by split_ifs; ext; simp [h, eq_comm] {contextual := tt}

@[simp] lemma finset.filter_eq_univ_erase {α : Type*} [fintype α] [decidable_eq α] (i k : α) :
  finset.filter (eq i) (finset.univ \ {k}) = if i = k then ∅ else {i} :=
by { split_ifs; ext; simp [h, eq_comm] {contextual := tt}; rintro rfl; simp [ne.symm h]  }

@[simp] lemma finset.filter_eq_univ_erase' {α : Type*} [fintype α] [decidable_eq α] (i k : α) :
  finset.filter (λ x, x =  i) (finset.univ \ {k}) = if i = k then ∅ else {i} :=
by split_ifs; ext; simp [h, eq_comm] {contextual := tt}

@[simp] lemma finset.filter_ne_univ_erase {α : Type*} [fintype α] [decidable_eq α] (i k : α) :
  finset.filter (ne i) (finset.univ \ {k}) = finset.univ \ {i, k} :=
by ext; simp [not_or_distrib, eq_comm, and.comm]

@[simp] lemma finset.filter_ne_univ_erase' {α : Type*} [fintype α] [decidable_eq α] (i k : α) :
  finset.filter (λ x, x ≠ i) (finset.univ \ {k}) = finset.univ \ {i, k} :=
by ext; simp [not_or_distrib, eq_comm, and.comm]

lemma G_inv_mul_G (n : ℕ) (hn : 3 ≤ (n:ℝ)) (G : matrix (fin n) (fin n) ℝ)
  (hG : ∀ i j, G i j = ite (i=j) (-2) 2) (Ginv : matrix (fin n) (fin n) ℝ)
  (hGinv : ∀ i j, Ginv i j = if (i = j) then (-((-3 + n) / (4 * (-2 + n))))
    else (1 / (4 * (-2 + n)))) :
  Ginv.mul G = 1 :=
begin
  have : -2 + (n : ℝ) ≠ 0 := by linarith,
  ext i j,
  by_cases hh : i = j,
  { simp only [matrix.mul, matrix.dot_product, hGinv, hG, hh, one_div, mul_inv_rev, mul_ite,
      mul_neg, mul_one, matrix.one_apply_eq],
    suffices : ((-(3 : ℝ) + n) / (4 * (-2 + n)) * 2 +
      (n * ((-2 + n)⁻¹ * 4⁻¹ * 2) - (-2 + n)⁻¹ * 4⁻¹ * 2) = 1),
    { simp [this, finset.sum_ite], },
    field_simp,
    ring, },
  { simp only [matrix.mul, matrix.dot_product, hGinv, hG, hh, one_div, mul_inv_rev, mul_ite,
      mul_neg, mul_one, matrix.one_apply_ne, ne.def, not_false_iff],
    suffices : (-((-(2 : ℝ) + n)⁻¹ * 4⁻¹ * 2) + (-((-3 + n) / (4 * (-2 + n)) * 2) +
      (n * ((-2 + n)⁻¹ * 4⁻¹ * 2) - 2 * ((-2 + n)⁻¹ * 4⁻¹ * 2))) = 0),
    { simp [finset.sum_ite, hh, this], },
    field_simp,
    ring, },
end

/-- move to `matrix.basic` ??? -/
lemma matrix.range_to_lin' {R} [comm_semiring R] {m n} [fintype n] [decidable_eq n]
  (G : matrix m n R) : G.to_lin'.range = submodule.span R (set.range G.transpose) :=
begin
  rw [linear_map.range_eq_map, ← linear_map.supr_range_std_basis],
  simp_rw [submodule.map_supr, linear_map.range_eq_map, ← ideal.span_one, ideal.span,
    submodule.map_span, set.image_image],
  dsimp only [set.has_one, has_one.one],
  simp_rw set.image_singleton,
  apply le_antisymm,
  { refine supr_le (λ i, submodule.span_mono _),
    rintro _ ⟨_, rfl⟩,
    exact ⟨i, (G.mul_vec_std_basis_apply i).symm⟩ },
  { rw submodule.span_le,
    rintro _ ⟨i, rfl⟩,
    apply submodule.mem_supr_of_mem i,
    exact submodule.subset_span (G.mul_vec_std_basis_apply i).symm },
end

--- exists in mathlib
noncomputable def matrix.rank {m: Type*} {n : Type*} {K : Type*} [fintype n] [decidable_eq n]
  [field K] (A : matrix m n K) : ℕ := finrank K A.to_lin'.range

--- exists in mathlib
theorem matrix.rank_of_is_unit {n : Type*} {K : Type*} [fintype n] [decidable_eq n] [field K]
  (A : matrix n n K) (h : is_unit A) : matrix.rank A = fintype.card n := sorry

/-- move to `quadratic space` ??? -/
lemma linear_independent_of_invertible_gram (E : Type*) {n : ℕ} [add_comm_group E] [module ℝ E]
  [finite_dimensional ℝ E] (vs : fin n → E) (Q : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (G : matrix (fin n) (fin n) ℝ)
  (hG : invertible G) (h : ∀ i j, Q (vs i) (vs j) = G i j) : linear_independent ℝ vs :=
begin
  apply linear_independent.of_comp Q.flip,
  rw linear_independent_iff_card_eq_finrank_span,
  apply le_antisymm,
  { rw ← G.rank_of_is_unit (is_unit_of_invertible G),
    unfold set.finrank matrix.rank,
    rw G.range_to_lin',
    let f : (E →ₗ[ℝ] ℝ) →ₗ[ℝ] fin n → ℝ := linear_map.pi (λ i, linear_map.applyₗ $ vs i),
    rw (by { ext j i, exact (h i j).symm } : G.transpose = f ∘ (Q.flip ∘ vs)),
    rw [set.range_comp, ← submodule.map_span],
    apply finite_dimensional.finrank_map_le },
  { apply (finrank_span_le_card _).trans,
    { classical, rw set.to_finset_range, exact finset.card_image_le },
    { apply set.fintype_range } },
end

lemma spanning_of_invertible_gram (E : Type*) {n : ℕ} [add_comm_group E] [module ℝ E]
  [finite_dimensional ℝ E] (hr : finite_dimensional.finrank ℝ E = n) (vs : fin n → E)
  (Q : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (G : matrix (fin n) (fin n) ℝ) (hG : invertible G)
  (h : ∀ i j, Q (vs i) (vs j) = G i j) : submodule.span ℝ (set.range vs) = ⊤ :=
begin
  sorry,
end

-- Descartes / Soddy-Gossett Theorem
theorem descartes_soddy_gossett (Ss : (fin (n+2)) → (sphere E))
  (h : ∀ (i j : fin (n+2)), i ≠ j → tangent (Ss i) (Ss j)) :
--(h : pairwise tangent Ss) :
(∑ (i : fin (n+2)), (bend (Ss i))) ^ 2 - n * ∑ (i : fin (n+2)), (bend (Ss i)) ^ 2 = 0
:= begin
  let G : matrix (fin (n+2)) (fin (n+2)) ℝ := λ i j, inv_prod (inv_coords (Ss i)) (inv_coords (Ss j)),
  have Gis : ∀ i j, G i j = ite (i = j) (-2) 2,
  { intros i j,
    by_cases hh : i = j,
    { simp only [hh, eq_self_iff_true, if_true],
      convert inv_prod_self (Ss j), },
    { simp [hh],
      apply inv_prod_tangent (Ss i) (Ss j) (h i j hh), }, },
  let Ginv : matrix (fin (n+2)) (fin (n+2)) ℝ := λ i j, if (i = j) then (-((n - 1) / (4 * n)))
    else (1 / (4 * n)),
  have GinvG : Ginv.mul G = 1,
  { have n_ne_zero : n ≠ 0 := fact.out _,
    have : (n : ℝ) ≠ 0 := by exact_mod_cast n_ne_zero,
    have : 1 ≤ n := nat.one_le_iff_ne_zero.mpr n_ne_zero,
    have : (3 : ℝ) ≤ n+2 := by norm_cast; linarith,
    refine G_inv_mul_G (n+2) (by exact_mod_cast this) G Gis Ginv (λ i j, _),
    dsimp [Ginv],
    by_cases hh : i = j,
    { simp only [hh, eq_self_iff_true, if_true, neg_inj],
      rw (by ring : -2 + ((n:ℝ) + 1 + 1) = n),
      field_simp,
      ring, },
    { simp only [hh, one_div, mul_inv_rev, if_false, mul_eq_mul_right_iff, inv_inj, inv_eq_zero,
        bit0_eq_zero, one_ne_zero, or_false],
      ring, }, },
  have invble_G := matrix.invertible_of_left_inverse G Ginv GinvG,
  have finrank_inv_coord_space : finrank ℝ (inv_coord_space E) = n + 2,
  { rw add_comm,
    have : finrank ℝ E = n := fact.out _,
    letI : module.finite ℝ (fin 2 → ℝ) := module.finite.pi,
    convert module.free.finrank_prod ℝ _ _,
    { simp, },
    { exact this.symm, },
    { exact module.free.pi ℝ, },
    { exact _inst, },
    { exact module.free.of_division_ring ℝ E, },
    { exact _inst_2, }, },
  haveI : finite_dimensional ℝ (inv_coord_space E) := sorry,
  let vs := inv_coords ∘ Ss,
  have lin_indep_vs := linear_independent_of_invertible_gram
    (inv_coord_space E) vs inv_prod G invble_G (λ i j, by simp [G, vs]),

  have span_vs := spanning_of_invertible_gram (inv_coord_space E) finrank_inv_coord_space vs
    inv_prod G invble_G (λ i j, by simp [G, vs]),

  let vs_basis := basis.mk lin_indep_vs span_vs,
  convert congr_arg (λ (f : (inv_coord_space E) →ₗ[ℝ] (inv_coord_space E) →ₗ[ℝ] ℝ),
    f bend_covector bend_covector) ((inv_prod_apply vs_basis G
    invble_G _).symm),
  {
    rw inv_prod_aux_apply,
    rw (_ : G⁻¹ = Ginv),
    simp [Ginv, inv_prod, bend_covector, vs, inv_coords],
    repeat {sorry},
  },
  { simp [inv_prod, bend_covector], },
  {
    sorry,
  },
  {
    intros i j,
    sorry,
  },
end
--  is_basis_iff_det

#exit































/-
@[simp] lemma finset.filter_eq_univ {α : Type*} [fintype α] [decidable_eq α] (i : α) :
  finset.univ.filter (eq i) = {i} :=
by ext; simp [eq_comm]

@[simp] lemma finset.filter_eq_univ' {α : Type*} [fintype α] [decidable_eq α] (i : α) :
  finset.univ.filter (λ x, x = i) = {i} :=
by ext; simp [eq_comm]

@[simp] lemma finset.filter_ne_univ {α : Type*} [fintype α] [decidable_eq α] (i : α) :
  finset.univ.filter (λ x, x ≠ i) = finset.univ \ {i} :=
by ext; simp [eq_comm]

@[simp] lemma finset.filter_ne_univ' {α : Type*} [fintype α] [decidable_eq α] (i : α) :
  finset.univ.filter (λ x, i ≠ x) = finset.univ \ {i} :=
by ext; simp [eq_comm]

@[simp] lemma finset.filter_eq_empty {α : Type*} [fintype α] (i : α)
  [decidable_pred (λ (x : α), ¬i = x)] : finset.filter (λ x, ¬ i = x) {i} = ∅ :=
by ext; simp [eq_comm]

@[simp] lemma finset.filter_eq_single {α : Type*} [fintype α] (i j : α) (h : i ≠ j)
  [decidable_pred (λ (x : α), ¬i = x)] : finset.filter (λ x, ¬ i = x) {j} = {j} :=
by ext; simp [eq_comm, h]

@[simp] lemma finset.filter_eq_empty' {α : Type*} [fintype α] (i : α) [decidable_eq α] :
  finset.filter (eq i) (finset.univ \ {i}) = ∅ :=
by ext; simp [eq_comm]

@[simp] lemma finset.filter_eq_empty'' {α : Type*} [fintype α] (i j : α) [decidable_eq α]
  (h : i ≠ j) : finset.filter (eq i) {j} = ∅ :=
by ext; simp only [eq_comm, finset.mem_filter, finset.mem_singleton, finset.not_mem_empty,
  iff_false, not_and]; intros h₂ h₃; rw ← h₂ at h₃; exact h h₃

@[simp] lemma finset.filter_eq_all_but_one {n : ℕ} (i : fin n) :
  finset.filter (λ (x : fin n), ¬i = x) ((finset.univ : finset (fin n)) \ {i})
  = ((finset.univ : finset (fin n)) \ {i}) := by ext; simp [eq_comm]

@[simp] lemma finset.filter_eq_all_but_one' {n : ℕ} (i j : fin n) (h : i ≠ j) :
  finset.filter (eq i) ((finset.univ : finset (fin n)) \ {j}) = {i} :=
by ext; simp only [eq_comm, finset.mem_filter, finset.mem_sdiff, finset.mem_univ,
  finset.mem_singleton, true_and, and_iff_right_iff_imp]; intros h₂ h₃; rw ← h₃ at h₂; exact h h₂

@[simp] lemma finset.filter_ne_univ_erase' {α : Type*} [fintype α] [decidable_eq α] (i k : α) :
  finset.filter (λ x, ¬ i = x) (finset.univ \ {k}) = finset.univ \ {i, k} :=
by ext; simp [not_or_distrib, eq_comm, and.comm]
-/
--------------- USING `SESQUILINEAR` FORMS -----------------
/-- The ℝ^2 bilinear form `Q(x,y)=xy` -/ ----------- NO LONGER NEEDED? --------
def r2_to_r2 : ((fin 2) → ℝ) →ₗ[ℝ] ((fin 2) → ℝ) →ₗ[ℝ] ℝ :=
{ to_fun := λ x,
 { to_fun := λ y, ((x 1)*(y 2)+(x 2)*(y 1))/2,
  map_add' := λ y z, by field_simp; ring,
  map_smul' := λ r y, by field_simp; ring, },
  map_add' := λ x y, by congr; ext; simp only [pi.add_apply, linear_map.coe_mk]; field_simp;
    ring,
  map_smul' := λ r x, by congr; ext; simp only [pi.smul_apply, algebra.id.smul_eq_mul,
    ring_hom.id_apply, linear_map.coe_mk]; field_simp; ring, }

/-- The bilinear form on `inv_coord_space`
def inv_prod : (inv_coord_space E) →ₗ[ℝ] (inv_coord_space E) →ₗ[ℝ] ℝ :=
{ to_fun := λ ⟨x₁, z₁⟩, { to_fun := λ ⟨x₂, z₂⟩,
    (x₁ 1) * (x₂ 2) + (x₁ 2) * (x₂ 1) - 2 * ⟪z₁, z₂⟫,
  map_add' := λ ⟨x₂, z₂⟩ ⟨x₃, z₃⟩, by dsimp [inv_prod._match_1]; rw inner_add_right; ring,
  map_smul' := λ r ⟨x₂, z₂⟩, by dsimp [inv_prod._match_1]; rw inner_smul_right; ring, },
  map_add' := begin
    rintros ⟨x₂, z₂⟩ ⟨x₃, z₃⟩,
    dsimp [inv_prod._match_5],
    congr,
    simp only [linear_map.coe_mk],
    sorry,
    --dsimp [inv_prod._match_1],
  end,
  map_smul' := begin
    rintros r ⟨x₂,z₂⟩,
    dsimp [inv_prod._match_5],
    congr,
    simp only [linear_map.coe_mk],
    sorry,
    --dsimp [inv_prod._match_1],
  end }
  -/


--------------- USING BILINEAR FORMS -----------------
/-- The ℝ^2 bilinear form `Q(x,y)=xy` -/
def r2_to_r2' : bilin_form ℝ ((fin 2) → ℝ) := matrix.to_bilin' ![![0, (1:ℝ) / 2], ![(1:ℝ) / 2, 0]]
/-- The bilinear form on `inv_coord_space` -/
def inv_prod' : bilin_form ℝ (inv_coord_space E) :=
  r2_to_r2'.comp (linear_map.fst ℝ ((fin 2) → ℝ) E) (linear_map.fst ℝ ((fin 2) → ℝ) E) -
  bilin_form_of_real_inner.comp (linear_map.snd ℝ ((fin 2) → ℝ) E)
    (linear_map.snd ℝ ((fin 2) → ℝ) E)
lemma inv_prod_self' (S : sphere E) : inv_prod' (inv_coords S) (inv_coords S) = -1 :=
begin
  have := S.rad_pos.ne',
  simp only [inv_prod', r2_to_r2', inv_coords, matrix.to_bilin'_apply, fin.sum_univ_succ, cobend,
    bend, inner_smul_left, inner_smul_right, norm_sq, one_div, bilin_form.sub_apply,
    bilin_form.comp_apply, linear_map.fst_apply, matrix.cons_val_zero,
    fintype.univ_of_subsingleton, matrix.cons_val_succ, matrix.cons_val_fin_one, mul_zero,
    zero_mul, zero_add, add_zero, finset.sum_const, finset.card_singleton, nsmul_eq_mul,
    nat.cast_one, one_mul, linear_map.snd_apply, bilin_form_of_real_inner_apply,
    is_R_or_C.conj_to_real],
  field_simp,
  ring,
end
lemma inv_prod_tangent' (S₁ S₂ : sphere E) (h : tangent S₁ S₂) :
  inv_prod' (inv_coords S₁) (inv_coords S₂) = 1 :=
begin
  have := S₁.rad_pos.ne',
  have := S₂.rad_pos.ne',
  simp only [inv_prod', r2_to_r2', inv_coords, matrix.to_bilin'_apply, fin.sum_univ_succ, cobend,
    inner_smul_left, inner_smul_right, norm_sq, bend, one_div, bilin_form.sub_apply,
    bilin_form.comp_apply, linear_map.fst_apply, matrix.cons_val_zero,
    fintype.univ_of_subsingleton, matrix.cons_val_succ, matrix.cons_val_fin_one, mul_zero,
    zero_mul, zero_add, add_zero, finset.sum_const, finset.card_singleton, nsmul_eq_mul,
    nat.cast_one, one_mul, linear_map.snd_apply, bilin_form_of_real_inner_apply,
    is_R_or_C.conj_to_real],
  simp only [tangent_iff, norm_sq, inner_sub_left, inner_sub_right, real_inner_comm] at h,
  field_simp,
  linear_combination S₂.radius * S₁.radius * h,
end
lemma linear_algebra_thing' {F : Type*} [add_comm_group F] [module ℝ F]
--(Q : bilin_form ℝ F)
(Q : F →ₗ[ℝ] F →ₗ[ℝ] ℝ)
{n : ℕ} (hdim : finrank ℝ F = n) (vs : basis (fin n) ℝ F) (G : matrix (fin n) (fin n) ℝ) (hG : invertible G)
(hvG : ∀ i j, G i j = Q (vs i) (vs j)) (w₁ w₂ : F) :
Q w₁ w₂ = ∑ i, ∑ j, Q w₁ (vs i) * Q w₂ (vs j) * (G⁻¹ i j) :=
begin
  sorry,
end































































-- move to `data.nat.basic`
/-- If `n ≤ m` and `n ≠ 0`, then `n - 1 < m`. -/
lemma nat.pred_lt_of_le_ne {n m : ℕ} (h : n ≤ m) (hh : n ≠ 0) : n - 1 < m :=
begin
  obtain ⟨c, hc⟩ := nat.exists_eq_succ_of_ne_zero hh,
  rw hc at ⊢ h,
  exact nat.succ_le_iff.mp h,
end


-- Descartes / Soddy-Gossett Theorem
theorem descartes_soddy_gossett {n : ℕ} (Ss : (fin (n+2)) → (sphere E))
  (h : ∀ (i : fin (n+2)), ∀ (j : fin (n+2)), i ≠ j → tangent (Ss i) (Ss j)) :
(∑ (i : fin (n+2)), (bend (Ss i))) ^ 2 - n * ∑ (i : fin (n+2)), (bend (Ss i)) ^ 2 = 0
:= begin
  let V : matrix (fin (n+2)) (fin (n+2)) ℝ := λ i, (inv_coords (Ss i)) 0,
  let G := (V.mul inv_prod_mat).mul V.transpose,
  have G_eval : G = λ i j, ite (i=j) (-1) 1,
  { ext i j,
    dsimp [G, V],
    by_cases hij : i = j,
    { rw hij,
      simp only [eq_self_iff_true, if_true],
      convert inv_prod_self (Ss j) using 1, },
    { simp only [hij, if_false],
      convert (tangent_iff_inv_prod (Ss i) (Ss j)).mp (h i j hij) using 1, }, },
  have G_det_ne_zero : G.det ≠ 0,
  { rw [G_eval, matrix.det_apply],
    simp [fin.sum_univ_succ],
    sorry,
  },
  have V_det_ne_zero : V.det ≠ 0,
  { intros Vdet,
    have : G.det = (V.mul inv_prod_mat).det * V.transpose.det :=
      matrix.det_mul (V.mul inv_prod_mat) V.transpose,
    rw [matrix.det_transpose, Vdet, mul_zero] at this,
    exact G_det_ne_zero this, },
  have inv_prod_mat_det : inv_prod_mat.det ≠ 0,
  {
    rw matrix.det_apply,
    sorry,
  },
  let G_inv := (matrix.general_linear_group.mk_of_det_ne_zero G G_det_ne_zero)⁻¹,
/-  have G_inv_is : (G_inv : matrix (fin 4) (fin 4) ℝ) = ![], -- Archana homework
  {
    sorry, -- Archana homework
  },
  -/
  let inv_prod_mat_inv :=
    (matrix.general_linear_group.mk_of_det_ne_zero inv_prod_mat inv_prod_mat_det)⁻¹,
/-  have inv_prod_mat_inv_is : (inv_prod_mat_inv : matrix (fin 4) (fin 4) ℝ) = ![], -- Archana homework
  {
    sorry, -- Archana homework
  },
-/
  have : (inv_prod_mat_inv : matrix (fin (n+2)) (fin (n+2)) ℝ) = (V.transpose.mul G_inv).mul V,
  {
    sorry,
  },

  repeat {sorry},
end




/-- Tangency is a symmetric condition -/
lemma tangent_symm (S₁ S₂ : sphere E) (h : tangent S₁ S₂) : tangent S₂ S₁ :=
begin
  dsimp [tangent] at *,
  convert h using 1,
  rw ←  norm_neg,
  congr,
  ring,
  ring,
  rw (λ z, by simp [norm_sq, norm_neg] : ∀ (z : E), norm_sq z = norm_sq (-z) ) _,
  convert h using 2; ring,
end

#exit


/-- Tangency is a symmetric condition -/
lemma tangent_symm' (S₁ S₂ : sphere E) (h : tangent S₁ S₂) : tangent S₂ S₁ :=
begin
  dsimp [tangent] at *,
  rw (λ z, by simp [norm_sq, norm_neg] : ∀ (z : E), norm_sq z = norm_sq (-z) ) _,
  convert h using 2; ring,
end

/-- `inv_prod_mat` gives the matrix representing the inversive inner product, which looks like:
![![0, 0, 0, 1/2],
  ![0, -1, 0, 0],
  ![0, 0, -1, 0],
  ![1/2, 0, 0, 0]] -/
def inv_prod_mat {n : ℕ} : matrix (fin (n+2)) (fin (n+2)) ℝ :=
λ i j, ite (i = 0) (ite (j = n + 1) (1/2) 0)
  (ite (i = n + 1) (ite (j = 0) (1/2) 0)
  (ite (i = j) (-1) 0))

/-- `inv_prod_mat` gives the matrix representing the inversive inner product, which looks like:
![![0, 0, 0, 1/2],
  ![0, -1, 0, 0],
  ![0, 0, -1, 0],
  ![1/2, 0, 0, 0]] -/
def inv_prod_mat' {n : ℕ} : matrix (fin (n+2)) (fin (n+2)) ℝ :=
λ i j, ite (i = 0) (ite (j = n + 1) (1/2) 0)
  (ite (i = n + 1) (ite (j = 0) (1/2) 0)
  (ite (i = j) (-1) 0))

/-- The inversive product (with respect to `inv_prod_mat`) of two vectors is `inv_prod`. -/
def inv_prod {n : ℕ} (v₁ v₂ : (fin (n+2)) → ℝ) : ℝ :=
  (((matrix.row v₂).mul inv_prod_mat).mul (matrix.col v₁)) 0 0

/-- As a bilinear form, `inv_prod` is `inv_prod_form` -/
def inv_prod_form {n : ℕ} : (fin (n+2) → ℝ) → (fin (n+2) → ℝ) → ℝ :=
λ f g, 1/2 * (f 0) * (g (n+1))
  + ((∑ (i : fin n), (-(f (i+1)) * (g (i+1)))) + 1/2 * (f (n+1)) * (g 0))

/-- The inversive product `inv_prod` is exactly the bilinear form `inv_prod_form` -/
lemma inv_prod_eq_form {n : ℕ} (v₁ v₂ : (fin (n+2)) → ℝ) :
  inv_prod v₁ v₂ = inv_prod_form v₁ v₂ := -- sorry
/- -- Most of this proof is ok-ish, needs cleaning and finishing -/
begin
  dsimp [inv_prod_form, inv_prod],
  rw [matrix.mul_apply, fin.sum_univ_succ],
  have zero_ne_nP1 : (0 : fin (n+2)) ≠ n + 1 := sorry,
  have nP1_ne_zero : (fin.last (n + 1) : fin (n+2)) ≠ 0 := sorry,
  have last_eq : (fin.last (n + 1) : fin (n+2)) = n + 1 := sorry,
  have all_nonzero : ∀ (i : fin (n+1)), i.succ ≠ 0 := sorry,
  congr' 1,
  { dsimp [inv_prod_mat],
    rw [matrix.mul_apply, fin.sum_univ_cast_succ],
    simp only [zero_ne_nP1, last_eq, matrix.row_apply, fin.cast_succ_eq_zero_iff, one_div,
      if_false, eq_self_iff_true, if_true, mul_ite, mul_zero, mul_neg, mul_one],
    rw fin.sum_univ_succ,
    simp only [zero_ne_nP1.symm, eq_self_iff_true, if_true, zero_add, if_false],
    have : ∑ (i : fin n), ite (i.succ = 0) 0 (ite (fin.cast_succ i.succ = n + 1)
      (v₂ (fin.cast_succ i.succ) * 2⁻¹) (ite (i.succ = 0) (-v₂ (fin.cast_succ i.succ)) 0)) = 0,
    { rw (by simp : (0 : ℝ) = ∑ (i : fin n), 0),
      congr' 1,
      ext i,
      simp only [finset.sum_const_zero, ite_eq_left_iff],
      intros h,
      have : (fin.cast_succ i.succ : fin (n+2)) ≠ n + 1,
      { obtain ⟨ii, hi⟩ := i,
        intros hhh,
        norm_cast at hhh,
        have := congr_arg (coe : fin (n+2) → ℕ) hhh,
        simp at this,
        have : ii+1 = n+1,
        {
          sorry,
          --exact_mod_cast this,
        },
        linarith, },
      simp only [this, if_false, ite_eq_right_iff, neg_eq_zero],
      intros hh,
      exfalso,
      exact h hh, },
    rw this,
    ring, },
  { rw [fin.sum_univ_cast_succ],
    congr' 1,
    {
      apply finset.sum_congr rfl,
      intros i hi,
      dsimp [inv_prod_mat],
      simp only [one_div, neg_mul],
      sorry,
    },
    {
      sorry,
    rw ← matrix.row_mul_col_apply,
    simp, }, },
end
/-
#exit
-/


/-- This is the inversive product of the inversive coordinate systems of two spheres -/
def inv_prod_form_sph {n : ℕ} : (sphere n) → (sphere n) → ℝ :=
λ S₁ S₂, (1 / 2) * (bend S₁) * (cobend S₂)
  + ((matrix.dot_product S₁.center S₂.center) * ( - (bend S₁) * (bend S₂))
  + (1 / 2) * (cobend S₁) * (bend S₂))

/-- The inversive product -/
lemma inv_prod_eq_form_sph {n : ℕ} (S₁ S₂ : sphere n) :
  inv_prod (inv_coords S₁) (inv_coords S₂) = inv_prod_form_sph S₁ S₂ :=
begin
  rw inv_prod_eq_form,
  dsimp [inv_prod_form, inv_prod_form_sph],
  congr' 1,
  {
    sorry,
  },
  congr' 1,
  {
    dsimp [matrix.dot_product],
    rw finset.sum_div ,
    apply finset.sum_congr rfl,
    intros x hx,
    dsimp [inv_coords],

    sorry,
  },
  dsimp [inv_coords],
  simp,
  sorry
end



lemma tangent_iff_inv_prod {n : ℕ} (S₁ S₂ : sphere n) (hS₁ : general_position S₁)
  (hS₂ : general_position S₂) : tangent S₁ S₂ ↔ inv_prod (inv_coords S₁) (inv_coords S₂) = 1 :=
begin
  rw inv_prod_eq_form_sph,
  have := S₁.rad_pos.ne,
  have := S₂.rad_pos.ne,
  have := (coradius_non_zero_iff_general_position S₁).mpr hS₁,
  have := (coradius_non_zero_iff_general_position S₂).mpr hS₂,
  dsimp [tangent, inv_prod_form_sph, norm_sq, coradius],
  have : 2 * S₁.radius * S₂.radius ≠ 0 := sorry,
  split; intros h; field_simp at *,
  {

    sorry,
    --linear_combination 2 * h,
  },

  sorry,

  field_simp at h,
  simp,



  dsimp [tangent, inv_coords, inv_prod_form, norm_sq, matrix.dot_product],
  split; intros h,
  {
    have nonZ1 : (((n : fin (n+2)) + 1) : ℕ) ≠ 0 := sorry,
    simp [nonZ1, finset.sum_dite_of_false],
  },

  simp only [one_div, dif_pos, neg_mul, finset.sum_neg_distrib],
  field_simp,
  dsimp [tangent, inv_prod, inv_coords, inv_prod_mat, diff_sq, norm_sq, origin],
  rw [matrix.mul_apply, fin.sum_univ_cast_succ, fin.sum_univ_succ],
--  simp [matrix.mul, matrix.dot_product, fin.sum_univ_succ],
--  split; intros h; field_simp at *,
  { sorry }, --linear_combination 2 * S₁.radius ^3 * S₂.radius ^3 * h, },
  {
  -- AK homework
    sorry,
  },
end

#exit

-- not needed?
lemma inv_prod_eval {n : ℕ} {hn : n ≠ 0} (S₁ S₂ : sphere n) :
  inv_prod S₁ S₂ = 1/(2 * S₁.radius * (coradius S₂))
    + ∑ (i : fin n), (-(S₁.center i)*(S₂.center i)) + 1/(2 * S₂.radius * (coradius S₁)) :=
begin
  dsimp [inv_prod, inv_coords, inv_prod_mat],
  rw [matrix.mul_apply, fin.sum_univ_cast_succ, fin.sum_univ_succ],
  congr' 1,
  {
    congr' 1,
    {
      have : (0 : fin (n+2)) ≠ n + 1 := sorry,
      have hn' : (n : fin (n+2)) ≠ 0 := sorry,
      have hx : ∀ (x : fin n), x.succ.succ ≠ 0 := sorry,
      simp only [matrix.mul, matrix.dot_product, fin.sum_univ_succ, this, hn', hx, fin.coe_succ,
        nat.succ_ne_zero, not_false_iff, nat.add_succ_sub_one, add_zero, one_div,
        fin.cast_succ_zero, if_false, eq_self_iff_true, if_true, mul_ite, mul_zero, fin.coe_zero,
        dif_pos, dif_neg, fin.succ_zero_eq_one, fin.one_eq_zero_iff, zero_add, self_eq_add_left,
        matrix.transpose_apply, mul_inv_rev],
      have := S₂.rad_pos,
      --rw fin.sum_univ_succ,
      sorry,
    },
    {
      sorry,
    },
  },
  simp only [matrix.mul, matrix.dot_product, fin.coe_last, nat.succ_ne_zero, not_false_iff, nat.succ_sub_succ_eq_sub, tsub_zero,
  one_div, eq_self_iff_true, if_true, mul_ite, mul_zero, mul_neg, mul_one, fin.coe_zero, matrix.transpose_apply,
  dif_pos, fin.coe_succ, fin.coe_cast_succ, fin.eta, dite_eq_ite, if_false, fin.succ_last, dif_neg, mul_inv_rev],
  sorry,
end


--- needed?
lemma inv_prod_apply {n : ℕ} (S₁ S₂ : sphere n) :
  inv_prod S₁ S₂ = (((inv_coords S₁).mul inv_prod_mat).mul (inv_coords S₂).transpose) 0 0 := rfl


-- TESTING
def zeros_pad (n : ℕ) : fin (n+2) → ℝ := λ i, dite (i=0) (λ h, 0) (λ h, dite (i = n+1) (λ hh, 0) (λ hh, i))

example (n : ℕ) : ∑ (i : fin (n+2)), (zeros_pad n i) = n * (n-1) / 2 :=
begin
  have := fin.sum_univ_succ,
  simp [fin.sum_univ_succ],
end

example {n : ℕ} (f : fin (n + 1) → ℝ) :
finset.univ.sum (λ (i : fin (n + 1)), f i) = finset.univ.sum (λ (i : fin n), f i) + f n :=
begin
  rw fin.sum_univ_cast_succ,
  congr',
  {
    ext i,
    congr' ,
    simp only [fin.coe_eq_cast_succ],
  },
  simp,
end
--------
def inv_coords {n : ℕ} (S : sphere E) : (fin (n+2)) → ℝ :=
  λ i, dite (i.val = 0) (λ hi, bend S)
      (λ hi, (dite (i.val ≤ n)
        (λ h, ((S.center (fin.mk (i.val - 1) (nat.pred_lt_of_le_ne h hi))) * (bend S)))
        (λ h, cobend S)))

---------------

lemma inv_prod_self {n : ℕ} (S : sphere n) : inv_prod S S = -1 :=
begin
  dsimp [inv_prod, inv_coords, inv_prod_mat],
  sorry, -- ???
  /-
--  dsimp [tangent, inv_prod, inv_coords, inv_prod_mat, coradius, norm_sq, diff_sq, origin],
  simp [matrix.mul, matrix.dot_product, fin.sum_univ_succ],
  have : S.radius ≠ 0:= S.rad_pos.ne.symm,
  field_simp,
  ring,
  -/
end

-- Descartes / Soddy-Gossett Theorem
theorem descartes_soddy_gossett {n : ℕ} (Ss : (fin (n+2)) → (sphere n))
  (h : ∀ (i : fin (n+2)), ∀ (j : fin (n+2)), i ≠ j → tangent (Ss i) (Ss j)) :
(∑ (i : fin (n+2)), (1 / (Ss i).radius)) ^ 2 - n * ∑ (i : fin (n+2)), (1 / (Ss i).radius) ^ 2 = 0
:= begin
  let V : matrix (fin (n+2)) (fin (n+2)) ℝ := λ i, (inv_coords (Ss i)) 0,
  let G := (V.mul inv_prod_mat).mul V.transpose,
  have G_eval : G = λ i j, ite (i=j) (-1) 1,
  { ext i j,
    dsimp [G, V],
    by_cases hij : i = j,
    { rw hij,
      simp only [eq_self_iff_true, if_true],
      convert inv_prod_self (Ss j) using 1, },
    { simp only [hij, if_false],
      convert (tangent_iff_inv_prod (Ss i) (Ss j)).mp (h i j hij) using 1, }, },
  have G_det_ne_zero : G.det ≠ 0,
  { rw [G_eval, matrix.det_apply],
    simp [fin.sum_univ_succ],
    sorry,
  },
  have V_det_ne_zero : V.det ≠ 0,
  { intros Vdet,
    have : G.det = (V.mul inv_prod_mat).det * V.transpose.det :=
      matrix.det_mul (V.mul inv_prod_mat) V.transpose,
    rw [matrix.det_transpose, Vdet, mul_zero] at this,
    exact G_det_ne_zero this, },
  have inv_prod_mat_det : inv_prod_mat.det ≠ 0,
  {
    rw matrix.det_apply,
    sorry,
  },
  let G_inv := (matrix.general_linear_group.mk_of_det_ne_zero G G_det_ne_zero)⁻¹,
/-  have G_inv_is : (G_inv : matrix (fin 4) (fin 4) ℝ) = ![], -- Archana homework
  {
    sorry, -- Archana homework
  },
  -/
  let inv_prod_mat_inv :=
    (matrix.general_linear_group.mk_of_det_ne_zero inv_prod_mat inv_prod_mat_det)⁻¹,
/-  have inv_prod_mat_inv_is : (inv_prod_mat_inv : matrix (fin 4) (fin 4) ℝ) = ![], -- Archana homework
  {
    sorry, -- Archana homework
  },
-/
  have : (inv_prod_mat_inv : matrix (fin (n+2)) (fin (n+2)) ℝ) = (V.transpose.mul G_inv).mul V,
  {
    sorry,
  },

  repeat {sorry},
end
