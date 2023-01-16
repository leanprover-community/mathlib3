/-
Copyright (c) 2022 Alex Kontorovich, Heather Macbeth, and Archana Mohandas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth, and Archana Mohandas
-/
import geometry.euclidean.triangle
import linear_algebra.general_linear_group
import data.real.basic
import linear_algebra.matrix.bilinear_form
import analysis.normed_space.pi_Lp
import data.matrix.rank

/-!
# Spheres

This file proves

## Main theorems

*

-/

open_locale big_operators real_inner_product_space matrix

open finite_dimensional

noncomputable theory

variables (E : Type*) {n : ℕ} [inner_product_space ℝ E] [finite_dimensional ℝ E]
[fact (finrank ℝ E = n)] [fact (n ≠ 0)]

/-- A (positively oriented, n-1) `sphere` in dimension `n` has a `n`-dimensional center, and
  positive radius. -/
structure sphere :=
(center : E)
(radius : ℝ)
(rad_pos : 0 < radius)

/-- The inversive coordinate system attached to a sphere `S` is given by the `n+2`-tuple:
  `(bend, cobend, bend*center)`. -/
@[derive [add_comm_group, module ℝ]]def inv_coord_space := ((fin 2) → ℝ) × E

variables {E}

/-- The `bend` of a `sphere` is the reciprocal of the radius. -/
def bend (S : sphere E) : ℝ := 1 / S.radius

/-- The `bend` of a `sphere` is nonzero. -/
lemma bend_nonzero (S : sphere E) : bend S ≠ 0 := one_div_ne_zero S.rad_pos.ne.symm

/-- The square norm in Euclidean space. -/
def norm_sq (z : E) := ⟪z,z⟫

/-- The `cobend` is the reciprocal of the coradius; the latter is the radius of the inversion of
  the sphere through the unit sphere. -/
def cobend (S : sphere E) : ℝ := (norm_sq (S.center) - S.radius ^ 2) * (bend S)

/-- Two spheres are defined to be `tangent` if the distance between their centers is the the sum
  of their radii. -/
def tangent (S₁ S₂ : sphere E) : Prop :=
  ∥S₁.center - S₂.center∥ = S₁.radius + S₂.radius

/-- Two spheres are `tangent` if and only if the norm squared of their centers is the square of the
  sum of the radii. -/
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

/-- The inversive product is a map taking
  `(bend₁, cobend₁, bendCenter₁) × (bend₂, cobend₂, bendCenter₂) ↦ `
  ` bend₁ * cobend₂ + bend₂ * cobend₁ - 2 bendCenter₁ ⬝ bendCenter₂`. -/
def inv_prod : (inv_coord_space E) →ₗ[ℝ] (inv_coord_space E) →ₗ[ℝ] ℝ := linear_map.mk₂ ℝ
  (λ p₁ p₂, (p₁.1 0) * (p₂.1 1) + (p₁.1 1) * (p₂.1 0) - 2 * ⟪p₁.2, p₂.2⟫)
  (λ ⟨x₁, z₁⟩ ⟨x₂, z₂⟩ ⟨x₃, z₃⟩, by dsimp; rw inner_add_left; ring)
  (λ r ⟨x₁, z₁⟩ ⟨x₂, z₂⟩, by dsimp; rw inner_smul_left;
    simp only [is_R_or_C.conj_to_real]; ring)
  (λ ⟨x₁, z₁⟩ ⟨x₂, z₂⟩ ⟨x₃, z₃⟩, by dsimp;
    rw inner_add_right; ring)
  (λ r ⟨x₁, z₁⟩ ⟨x₂, z₂⟩, by dsimp; rw inner_smul_right;
    simp only [is_R_or_C.conj_to_real]; ring)

/-- The `inv_prod` of a `sphere` with itself is `-2`. -/
lemma inv_prod_self (S : sphere E) : inv_prod (inv_coords S) (inv_coords S) = -2 :=
begin
  have := S.rad_pos.ne',
  simp only [inv_prod, inv_coords, cobend, norm_sq, inner_smul_left, inner_smul_right, bend,
    one_div, linear_map.mk₂_apply, matrix.cons_val_one, matrix.head_cons, is_R_or_C.conj_to_real,
    matrix.cons_vec_bit0_eq_alt0, matrix.cons_append, matrix.empty_append, matrix.cons_vec_alt0],
  field_simp,
  ring,
end

/-- The `inv_prod` of two tangent `sphere`s is `+2`. -/
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

/-- Given a basis `vs` for `inv_coord_space E` and an `(n+2)×(n+2)` matrix `G`, we define an
  auxiliary inner product `inv_prod_aux`. -/
def inv_prod_aux (vs : basis (fin (n+2)) ℝ (inv_coord_space E))
  (G : matrix (fin (n+2)) (fin (n+2)) ℝ) : (inv_coord_space E) →ₗ[ℝ] (inv_coord_space E) →ₗ[ℝ] ℝ :=
begin
 refine linear_map.mk₂ ℝ (λ w₁ w₂, ∑ i, ∑ j, inv_prod w₁ (vs i) * inv_prod w₂ (vs j) * (G⁻¹ i j))
  _ _ _ _,
  repeat {sorry},
end

/-- Unfold the definition of `inv_prod_aux`. -/
lemma inv_prod_aux_apply (vs : basis (fin (n+2)) ℝ (inv_coord_space E))
  (G : matrix (fin (n+2)) (fin (n+2)) ℝ) (w₁ w₂ : (inv_coord_space E)) :
  inv_prod_aux vs G w₁ w₂ = ∑ i, ∑ j, inv_prod w₁ (vs i) * inv_prod w₂ (vs j) * (G⁻¹ i j)
:= rfl

/-- When `G` is the matrix of `inv_prod`'s of a basis `vs`, then `inv_prod_aux` agrees with
  `inv_prod.flip`. -/
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
  (h : ∀ i j, Q (vs i) (vs j) = G i j) : ⊤ ≤ submodule.span ℝ (set.range vs) :=
begin
  by_cases h_n : n = 0,
  {
    simp [h_n] at *,
    sorry, -- ask on Zulip! -- include finite dimensional; otherwise finrank could be 0...
--    haveI : unique E

  },
  haveI : nonempty (fin n),
  {
  have : 0 < n := sorry,
  exact fin.pos_iff_nonempty.mp this,
  },
  rw top_le_iff,
  apply span_eq_top_of_linear_independent_of_card_eq_finrank,
  {
    -- linear indepence
    sorry,
  },
  convert hr.symm,
  simp,
end

lemma open_square {α : Type*} {β : Type*} [ring β]
  (s : finset α) (f : α → β) :
(∑ i in s, f i)^2 = ∑ i in s, ∑ j in s, (f i) * (f j) :=
begin
  rw pow_two (∑ i in s, f i),
  rw finset.sum_mul_sum s s f f,
  exact finset.sum_product,
end

def matrix.const (n m : Type*) {R : Type*} [fintype n] [fintype m] (c : R) : matrix n m R :=
  λ i j, c

@[simp] lemma matrix.const_apply {n m : Type*} {R : Type*} [fintype n] [fintype m] (c : R) (i : n)
  (j : m) : (matrix.const n m c) i j = c := rfl

@[simp] lemma matrix.smul_const {n m : Type*} {R : Type*} [fintype n] [fintype m] [has_mul R]
  (c₁ c₂ : R) : c₂ • (matrix.const n m c₁) = matrix.const n m (c₂ * c₁) := rfl

lemma matrix.const.add {n m : Type*} {R : Type*} [fintype n] [fintype m] [has_add R]
  (c₁ c₂ : R) : (matrix.const n m c₁) + (matrix.const n m c₂)  = matrix.const n m (c₁ + c₂) := rfl

lemma matrix.const.sub {n m : Type*} {R : Type*} [fintype n] [fintype m] [has_sub R]
  (c₁ c₂ : R) : (matrix.const n m c₁) - (matrix.const n m c₂)  = matrix.const n m (c₁ - c₂) := rfl

lemma matrix.const.zero {n : Type*} {R : Type*} [fintype n] [ring R]
  (c : R) (h : c = 0) : matrix.const n n c = 0 := by rw h; refl


lemma matrix.const_mul_const {n m k : Type*} {R : Type*} [fintype n] [fintype m] [fintype k]
  [semiring R] {c₁ c₂: R} :
  (matrix.const n m c₁) ⬝ (matrix.const m k c₂) = matrix.const n k ((fintype.card m) • c₁* c₂) :=
begin
  ext i j,
  simp only [matrix.const, matrix.mul, matrix.dot_product, finset.sum_const, ← smul_mul_assoc],
  refl,
end

--set_option trace.simplify.rewrite true

-- Descartes / Soddy-Gossett Theorem
theorem descartes_soddy_gossett (Ss : (fin (n+2)) → (sphere E))
  (h : ∀ (i j : fin (n+2)), i ≠ j → tangent (Ss i) (Ss j)) :
--(h : pairwise tangent Ss) :
(∑ (i : fin (n+2)), (bend (Ss i))) ^ 2 - n * ∑ (i : fin (n+2)), (bend (Ss i)) ^ 2 = 0
:= begin
  have n_ne_zero : (n : ℝ) ≠ 0 := by exact_mod_cast (fact.out _ : n ≠ 0),
  suffices : (∑ (i : fin (n+2)), (bend (Ss i))) ^ 2 / (4 * n)
    - n * (∑ (i : fin (n+2)), (bend (Ss i)) ^ 2) / (4 * n) = 0,
  {
    sorry,
    /-
    rw ← sub_div at this,
    cases (div_eq_zero_iff.mp this) with hhh hhh,
    { exact hhh, },
    exfalso,
    rw mul_eq_zero at hhh,
    simp only [bit0_eq_zero, one_ne_zero, nat.cast_eq_zero, false_or] at hhh,
    have : n ≠ 0 := fact.out _,
    exact this hhh,
    -/ },
  let G : matrix (fin (n+2)) (fin (n+2)) ℝ :=
    λ i j, inv_prod (inv_coords (Ss i)) (inv_coords (Ss j)),
  have Gis : G = matrix.const (fin (n+2)) (fin (n+2)) (2:ℝ) - 4,
  {
    sorry,
    /-
    ext i j,
    by_cases hh : i = j,
    { simp only [hh, matrix.const_apply, G, pi.sub_apply, pi.bit0_apply, matrix.one_apply_eq],
      convert inv_prod_self (Ss j),
      norm_num, },
    { simp only [hh, matrix.const_apply, G, pi.sub_apply, pi.bit0_apply, matrix.one_apply_ne,
        ne.def, not_false_iff, bit0_zero, tsub_zero],
      apply inv_prod_tangent (Ss i) (Ss j) (h i j hh), },
      -/ },
  let Ginv := (matrix.const (fin (n+2)) (fin (n+2)) ((1 : ℝ) / (4 * n))) - ((n : ℝ) / (4 * n)) • 1,
  have GinvG : Ginv * G = 1,
  {
    simp [matrix.mul_eq_mul, Gis, Ginv, matrix.const_mul_const, sub_mul, mul_add, add_mul,
      mul_sub],
    rw ← sub_add,
    transitivity (0 : matrix (fin (n+2)) (fin (n+2)) ℝ) + 1,
    {  congr,
      {
        simp [bit0, matrix.const.sub, matrix.const.add, add_mul, mul_add, sub_mul, mul_sub,
          ← matrix.mul_eq_mul],
        apply matrix.const.zero,
        ring_nf,
        field_simp,
        ring,
      },
      { rw [div_mul_left n_ne_zero],
        norm_num,
        sorry,
      },
    },
    simp,
},
  have invble_G := matrix.invertible_of_left_inverse G Ginv GinvG,
  have Ginv_is : G⁻¹ = Ginv := matrix.inv_eq_left_inv GinvG,
  have finrank_inv_coord_space : finrank ℝ (inv_coord_space E) = n + 2 := sorry,
/-  { rw add_comm,
    have : finrank ℝ E = n := fact.out _,
    letI : module.finite ℝ (fin 2 → ℝ) := module.finite.pi,
    convert module.free.finrank_prod ℝ _ _,
    { simp, },
    { exact this.symm, },
    { exact @module.free.pi (fin 2) ℝ _ (λ _, ℝ) _ _ _ _, },
    { exact _inst, },
    { exact module.free.of_division_ring ℝ E, },
    { exact _inst_2, }, },-/
  haveI : finite_dimensional ℝ (inv_coord_space E) := sorry,
--    finite_dimensional.finite_dimensional_of_finrank (by linarith),

  let vs := inv_coords ∘ Ss,
  have lin_indep_vs : linear_independent ℝ vs := sorry,
  -- linear_independent_of_invertible_gram
    --(inv_coord_space E) vs inv_prod G invble_G (λ i j, by simp [G, vs]),

  have span_vs : ⊤ ≤ submodule.span ℝ (set.range vs) := sorry,
  --spanning_of_invertible_gram (inv_coord_space E) finrank_inv_coord_space vs
    --inv_prod G invble_G (λ i j, by simp [G, vs]),

  let vs_basis := basis.mk lin_indep_vs span_vs,
  convert congr_arg (λ (f : (inv_coord_space E) →ₗ[ℝ] (inv_coord_space E) →ₗ[ℝ] ℝ),
    f bend_covector bend_covector) ((inv_prod_apply vs_basis G
    invble_G _).symm),
  { rw [inv_prod_aux_apply, Ginv_is, open_square],
    -- make all these rw and four simps into single simp???


    simp only [Ginv, matrix.const, inv_prod, bend_covector, vs, inv_coords, basis.coe_mk, zero_mul,
      function.comp_app, linear_map.mk₂_apply, matrix.cons_val_zero, matrix.cons_val_one, zero_add,
      matrix.head_cons, one_mul, inner_zero_left, mul_zero, tsub_zero, neg_smul, mul_inv_rev,
      pi.smul_const, algebra.id.smul_eq_mul, mul_one, pi.add_apply, pi.neg_apply, pi.smul_apply,
      function.const_apply,  mul_add, mul_neg, mul_sub, finset.sum_add_distrib, one_div,
      finset.sum_neg_distrib, mul_ite, finset.sum_ite_eq, pi.sub_apply, matrix.one_apply,
      algebra.id.smul_eq_mul, mul_boole, finset.sum_sub_distrib],
    simp only [finset.mem_univ, if_true],
    simp only [finset.mul_sum, finset.sum_div],
    congrm (∑ i j, _) -(∑ i, _) ,
    { field_simp [-mul_ne_zero],
      ring_nf, },
    { ring, },
  },
  { simp [inv_prod, bend_covector], },
  {
    sorry, -- trivial, definition of G
  },

end
