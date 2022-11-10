/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux, Jon Bannon
-/

import algebra.star.star_alg_hom
import analysis.normed_space.star.basic
import analysis.normed_space.operator_norm
import analysis.special_functions.pow

/-!
# Multiplier Algebra of a C⋆-algebra

Define the multiplier algebra of a C⋆-algebra as the algebra (over `𝕜`) of double centralizers,
for which we provide the localized notation `𝓜(𝕜, A)`.  A double centralizer is a pair of
continuous linear maps `L R : A →L[𝕜] A` satisfying the intertwining condition `R x * y = x * L y`.

There is a natural embedding `A → 𝓜(𝕜, A)` which sends `a : A` to the continuous linear maps
`L R : A →L[𝕜] A` given by left and right multiplication by `a`, and we provide this map as a
coercion.

The multiplier algebra corresponds to a non-commutative Stone–Čech compactification in the sense
that when the algebra `A` is commutative, it can be identified with `C₀(X, ℂ)` for some locally
compact Hausdorff space `X`, and in that case `𝓜(𝕜, A)` can be identified with `C(β X, ℂ)`.

## Implementation notes

## TODO

+ define a type synonym for `𝓜(𝕜, A)` which is equipped with the strict uniform space structure
  and show it is complete
+ show that the image of `A` in `𝓜(𝕜, A)` is an essential ideal
+ prove the universal property of `𝓜(𝕜, A)`
* Construct a double centralizer from a pair of maps `L : A → A`, `R : A → A` satisfying the
  centrality condition `∀ x y, R x * y = x * L y`.
-/

noncomputable theory

open_locale nnreal ennreal
open nnreal continuous_linear_map

universes u v

/-- The type of *double centralizers*, also known as the *multiplier algebra* and denoted by
`𝓜(𝕜, A)`, of a non-unital normed algebra. -/
@[ext]
structure double_centralizer (𝕜 : Type u) (A : Type v) [nontrivially_normed_field 𝕜]
  [non_unital_normed_ring A] [normed_space 𝕜 A] [smul_comm_class 𝕜 A A] [is_scalar_tower 𝕜 A A] :=
(left : A →L[𝕜] A)
(right : A →L[𝕜] A)
(central : ∀ x y : A, right x * y = x * left y)

localized "notation `𝓜(` 𝕜 `, ` A `)` := double_centralizer 𝕜 A" in multiplier_algebra

namespace double_centralizer

section nontrivially_normed

variables (𝕜 A : Type*) [nontrivially_normed_field 𝕜] [non_unital_normed_ring A]
variables [normed_space 𝕜 A] [smul_comm_class 𝕜 A A] [is_scalar_tower 𝕜 A A]

instance : inhabited 𝓜(𝕜, A) :=
{ default := ⟨1, 1, by simp only [one_apply, eq_self_iff_true, forall_const]⟩ }

/-!
### Normed space structure

Because the multiplier algebra is defined as the algebra of double centralizers, there is a natural
map `double_centralizer.prod_mk := λ a, (a.left, a.right) : 𝓜(𝕜, A) → (A →L[𝕜] A) × (A →L[𝕜] A)`.
We use this map to pull back the normed space structure from `(A →L[𝕜] A) × (A →L[𝕜] A)` to
`𝓜(𝕜, A)`, which provides a definitional isometric embedding. Consequently, completeness of
`𝓜(𝕜, A)` is obtained by proving that the range of this map is closed.
-/

/-- the canonical map of `𝓜(𝕜, A)` into `(A →L[𝕜] A) × (A →L[𝕜] A)`. -/
@[simp] def prod_mk (a : 𝓜(𝕜, A)) : (A →L[𝕜] A) × (A →L[𝕜] A) := (a.left, a.right)

variables {𝕜 A}

lemma injective_prod_mk : function.injective (prod_mk 𝕜 A) :=
λ a b h, ext a b (prod.ext_iff.mp h).1 (prod.ext_iff.mp h).2

lemma range_prod_mk : set.range (prod_mk 𝕜 A) = {lr | ∀ x y, lr.2 x * y = x * lr.1 y} :=
set.ext $ λ x, ⟨by {rintro ⟨a, rfl⟩, exact a.central}, λ hx, ⟨⟨x.1, x.2, hx⟩, by simp⟩⟩

instance : has_add 𝓜(𝕜, A) :=
{ add := λ a b,
  { left := a.left + b.left,
    right := a.right + b.right,
    central := λ x y, by simp only [continuous_linear_map.add_apply, add_mul, mul_add, central] } }

instance : has_zero 𝓜(𝕜, A) :=
{ zero :=
  { left := 0,
    right := 0,
    central := λ x y, by simp only [continuous_linear_map.zero_apply, zero_mul, mul_zero] } }

instance : has_neg 𝓜(𝕜, A) :=
{ neg := λ a,
  { left := -(a.left),
    right := -(a.right),
    central := λ x y, by simp only [continuous_linear_map.neg_apply, neg_mul,
                      mul_neg, neg_inj, central]}}

instance : has_sub 𝓜(𝕜, A) :=
{ sub := λ a b,
  { left := a.left - b.left,
    right := a.right - b.right,
    central := λ x y, by simp only [continuous_linear_map.coe_sub', pi.sub_apply, sub_mul,
      mul_sub, central] } }

section scalars

variables {S : Type*} [monoid S] [distrib_mul_action S A] [smul_comm_class 𝕜 S A]
  [has_continuous_const_smul S A] [is_scalar_tower S A A] [smul_comm_class S A A]

instance : has_smul S 𝓜(𝕜, A) :=
{ smul := λ s a,
  { left := s • a.left,
    right := s • a.right,
    central := λ x y, by simp only [continuous_linear_map.coe_smul', pi.smul_apply, mul_smul_comm,
      smul_mul_assoc, central] } }

@[simp] lemma smul_left (k : 𝕜) (a : 𝓜(𝕜, A)) : (k • a).left = k • a.left := rfl
@[simp] lemma smul_right (k : 𝕜) (a : 𝓜(𝕜, A)) : (k • a).right = k • a.right := rfl

end scalars

@[simp] lemma add_left (a b : 𝓜(𝕜, A)) : (a + b).left = a.left + b.left := rfl
@[simp] lemma add_right (a b : 𝓜(𝕜, A)) : (a + b).right = a.right + b.right := rfl
@[simp] lemma zero_left : (0 : 𝓜(𝕜, A)).left = 0 := rfl
@[simp] lemma zero_right : (0 : 𝓜(𝕜, A)).right = 0 := rfl
@[simp] lemma neg_left (a : 𝓜(𝕜, A)) : (-a).left = -a.left := rfl
@[simp] lemma neg_right (a : 𝓜(𝕜, A)) : (-a).right = -a.right := rfl
@[simp] lemma sub_left (a b : 𝓜(𝕜, A)) : (a - b).left = a.left - b.left := rfl
@[simp] lemma sub_right (a b : 𝓜(𝕜, A)) : (a - b).right = a.right - b.right := rfl

/-- The module structure is inherited as the pullback under the injective map
`double_centralizer.prod_mk : 𝓜(𝕜, A) → (A →L[𝕜] A) × (A →L[𝕜] A)` -/
instance : add_comm_group 𝓜(𝕜, A) :=
function.injective.add_comm_group (prod_mk 𝕜 A) injective_prod_mk rfl (λ x y, rfl) (λ x, rfl)
  (λ x y, rfl) (λ x n, rfl) (λ x n, rfl)

/-- The canonical map `double_centralizer.prod_mk` as an additive group homomorphism. -/
def add_group_hom_prod_mk : 𝓜(𝕜, A) →+ (A →L[𝕜] A) × (A →L[𝕜] A) :=
{ to_fun := prod_mk 𝕜 A,
  map_zero' := rfl,
  map_add' := λ x y, rfl }

/-- The module structure is inherited as the pullback under the additive group monomoprhism
`double_centralizer.prod_mk : 𝓜(𝕜, A) →+ (A →L[𝕜] A) × (A →L[𝕜] A)` -/
instance : module 𝕜 𝓜(𝕜, A) :=
function.injective.module 𝕜 add_group_hom_prod_mk injective_prod_mk (λ x y, rfl)

/-- The normed group structure is inherited as the pullback under the additive group monomoprhism
`double_centralizer.prod_mk : 𝓜(𝕜, A) →+ (A →L[𝕜] A) × (A →L[𝕜] A)` -/
instance : normed_add_comm_group 𝓜(𝕜, A) :=
normed_add_comm_group.induced _ _ (add_group_hom_prod_mk : 𝓜(𝕜, A) →+ (A →L[𝕜] A) × (A →L[𝕜] A))
  injective_prod_mk

@[simp] lemma norm_eq (a : 𝓜(𝕜, A)) : ∥a∥ = max (∥a.left∥) (∥a.right∥) := rfl

instance : normed_space 𝕜 𝓜(𝕜, A) :=
{ norm_smul_le := λ k a, show max (∥k • a.left∥) (∥k • a.right∥) ≤ ∥k∥ * max (∥a.left∥) (∥a.right∥),
    by simp only [mul_max_of_nonneg _ _ (norm_nonneg k), norm_smul],
  .. double_centralizer.module }

lemma uniform_embedding_prod_mk : uniform_embedding (prod_mk 𝕜 A) :=
uniform_embedding_comap injective_prod_mk

instance [complete_space A] : complete_space 𝓜(𝕜, A) :=
begin
  rw complete_space_iff_is_complete_range uniform_embedding_prod_mk.to_uniform_inducing,
  apply is_closed.is_complete,
  simp only [range_prod_mk, set.set_of_forall],
  refine is_closed_Inter (λ x, is_closed_Inter $ λ y, is_closed_eq _ _),
  { exact ((continuous_mul_right y).comp (continuous_linear_map.apply 𝕜 A x).continuous).comp
      continuous_snd },
  { exact ((continuous_mul_left x).comp (continuous_linear_map.apply 𝕜 A y).continuous).comp
      continuous_fst }
end

/-!
### Multiplicative structure
-/

instance : ring 𝓜(𝕜, A) :=
{ one := ⟨1, 1, λ x y, rfl⟩,
  mul := λ x y,
  { left := x.left.comp y.left,
    right := y.right.comp x.right,
    central := λ x y, by simp only [continuous_linear_map.coe_comp', function.comp_app, central] },
  mul_assoc := λ a b c, ext _ _ (mul_assoc _ _ _) (mul_assoc _ _ _),
  one_mul := λ a, ext _ _ (one_mul _) (one_mul _),
  mul_one := λ a, ext _ _ (mul_one _) (mul_one _),
  left_distrib := λ a b c, ext _ _ (mul_add _ _ _) (add_mul _ _ _),
  right_distrib := λ a b c, ext _ _ (add_mul _ _ _) (mul_add _ _ _),
  nat_cast := λ n, ⟨n, n, λ x y,
    by simp only [←nat.smul_one_eq_coe, smul_apply n 1, one_apply, mul_smul_comm, smul_mul_assoc]⟩,
  int_cast := λ n, ⟨n, n, λ x y,
    by simp only [←int.smul_one_eq_coe, smul_apply n 1, one_apply, mul_smul_comm, smul_mul_assoc]⟩,
  npow := λ n a, ⟨a.left ^ n, a.right ^ n, λ x y,
  begin
    induction n with k hk generalizing x y,
    refl,
    rw [pow_succ, mul_apply, a.central, hk, pow_succ', mul_apply],
  end⟩,
  npow_succ' := λ n a, nat.rec_on n (ext _ _ rfl rfl) (λ k hk, ext _ _
    (by { change _ = a.left * _, simp only [congr_arg left hk, pow_succ] })
    (by { change _ = _ * a.right, simp only [congr_arg right hk, pow_succ'] })),
  .. double_centralizer.add_comm_group }

@[simp] lemma one_left : (1 : 𝓜(𝕜, A)).left = 1 := rfl
@[simp] lemma one_right : (1 : 𝓜(𝕜, A)).right = 1 := rfl
@[simp] lemma mul_left (a b : 𝓜(𝕜, A)) : (a * b).left = a.left * b.left := rfl
@[simp] lemma mul_right (a b : 𝓜(𝕜, A)) : (a * b).right = b.right * a.right := rfl
@[simp] lemma nat_cast_left (n : ℕ) : (n : 𝓜(𝕜 , A)).left = n := rfl
@[simp] lemma nat_cast_right (n : ℕ) : (n : 𝓜(𝕜 , A)).right = n := rfl
@[simp] lemma int_cast_left (n : ℤ) : (n : 𝓜(𝕜 , A)).left = n := rfl
@[simp] lemma int_cast_right (n : ℤ) : (n : 𝓜(𝕜 , A)).right = n := rfl
@[simp] lemma pow_left (n : ℕ) (a : 𝓜(𝕜, A)) : (a ^ n).left = a.left ^ n := rfl
@[simp] lemma pow_right (n : ℕ) (a : 𝓜(𝕜, A)) : (a ^ n).right = a.right ^ n := rfl


noncomputable instance : algebra 𝕜 𝓜(𝕜, A) :=
algebra.of_module
  (λ k a b, by {ext; simp only [mul_left, smul_left, mul_right, smul_right, coe_smul',pi.smul_apply,
    continuous_linear_map.coe_mul, function.comp_app, continuous_linear_map.map_smul]})
  (λ k a b, by {ext; simp only [mul_left, smul_left, mul_right, smul_right, algebra.mul_smul_comm,
    coe_smul', continuous_linear_map.coe_mul, pi.smul_apply, function.comp_app]})

/-!
### Star structure
-/

section star

variables [star_ring 𝕜] [star_ring A] [star_module 𝕜 A] [normed_star_group A]

instance : has_star 𝓜(𝕜, A) :=
{ star := λ a,
  { left := (((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A →L⋆[𝕜] A).comp a.right).comp
      ((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A →L⋆[𝕜] A),
    right := (((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A →L⋆[𝕜] A).comp a.left).comp
      ((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A →L⋆[𝕜] A),
    central := λ x y, by simpa only [star_mul, star_star]
      using (congr_arg star (a.central (star y) (star x))).symm } }

@[simp] lemma star_left (a : 𝓜(𝕜, A)) (b : A) : (star a).left b = star (a.right (star b)) := rfl
@[simp] lemma star_right (a : 𝓜(𝕜, A)) (b : A) : (star a).right b = star (a.left (star b)) := rfl

instance : star_add_monoid 𝓜(𝕜, A) :=
{ star_involutive := λ x, by {ext; simp only [star_left, star_right, star_star]},
  star_add := λ x y, by {ext; simp only [star_left, star_right, add_left, add_right,
    continuous_linear_map.add_apply, star_add]},
  .. double_centralizer.has_star }

instance : star_ring 𝓜(𝕜, A) :=
{ star_mul := λ a b, by {ext; simp only [star_left, star_right, mul_left, mul_right, star_star,
    continuous_linear_map.coe_mul, function.comp_app]},
  .. double_centralizer.star_add_monoid }

instance : star_module 𝕜 𝓜(𝕜, A) :=
{ star_smul := λ k a, by {ext; exact star_smul _ _},
  .. double_centralizer.star_add_monoid }

end star

/-!
### Coercion from an algebra into its multiplier algebra
-/

noncomputable instance : has_coe_t A 𝓜(𝕜, A) :=
{ coe := λ a,
  { left := continuous_linear_map.mul 𝕜 A a,
    right := (continuous_linear_map.mul 𝕜 A).flip a,
    central := λ x y, mul_assoc _ _ _ } }

@[simp, norm_cast]
lemma coe_left (a : A) : (a : 𝓜(𝕜, A)).left = continuous_linear_map.mul 𝕜 A a := rfl
@[simp, norm_cast]
lemma coe_right (a : A) : (a : 𝓜(𝕜, A)).right = (continuous_linear_map.mul 𝕜 A).flip a := rfl

section
variables [star_ring 𝕜] [star_ring A] [star_module 𝕜 A] [normed_star_group A]
/-- The coercion of an algebra into its multiplier algebra as a non-unital star algebra
homomorphism. -/
def non_unital_star_algebra_hom_coe : A →⋆ₙₐ[𝕜] 𝓜(𝕜, A) :=
{ to_fun := λ a, a,
  map_smul' := λ k a, by {ext1; simp only [coe_left, coe_right, continuous_linear_map.map_smul,
    smul_left, smul_right]},
  map_zero' := by {ext1; simp only [coe_left, coe_right, map_zero, zero_left, zero_right]},
  map_add' := λ a b, by {ext1; simp only [coe_left, coe_right, map_add, add_left, add_right]},
  map_mul' := λ a b, by {ext; simp only [coe_left, coe_right, mul_apply',
    flip_apply, mul_left, mul_right, continuous_linear_map.coe_mul,
    function.comp_app, mul_assoc]},
  map_star' := λ a, by {ext; simp only [coe_left, mul_apply', star_left, star_right, coe_right,
    flip_apply, star_mul, star_star]} }
end

/-!
### Norm structures
-/

noncomputable instance : normed_ring 𝓜(𝕜, A) :=
{ norm_mul := λ a b,
    begin
      refine max_le ((norm_mul_le _ _).trans _) ((norm_mul_le _ _).trans _),
      exact mul_le_mul (le_max_left _ _) (le_max_left _ _) (norm_nonneg _)
        ((norm_nonneg _).trans $ le_max_left _ _),
      exact mul_comm (∥a.right∥) (∥b.right∥) ▸ mul_le_mul (le_max_right _ _) (le_max_right _ _)
        (norm_nonneg _) ((norm_nonneg _).trans $ le_max_right _ _),
    end,
  .. double_centralizer.ring,
  .. double_centralizer.normed_add_comm_group }

noncomputable instance : normed_algebra 𝕜 𝓜(𝕜, A) :=
{ ..double_centralizer.algebra, ..double_centralizer.normed_space }

variables [star_ring A] [cstar_ring A]

/-- For `a : 𝓜(𝕜, A)`, the norms of `a.left` and `a.right` coincide, and hence these
also coincide with `∥a∥` which is `max (∥a.left∥) (∥a.right∥)`. -/
lemma norm_left_eq_right (a : 𝓜(𝕜, A)) : ∥a.left∥ = ∥a.right∥ :=
begin
  -- a handy lemma for this proof
  have h0 : ∀ f : A →L[𝕜] A, ∀ C : ℝ≥0, (∀ b : A, ∥f b∥₊ ^ 2 ≤ C * ∥f b∥₊ * ∥b∥₊) → ∥f∥₊ ≤ C,
  { intros f C h,
    have h1 : ∀ b, C * ∥f b∥₊ * ∥b∥₊ ≤ C * ∥f∥₊ * ∥b∥₊ ^ 2,
    { intros b,
      convert mul_le_mul_right' (mul_le_mul_left' (f.le_op_nnnorm b) C) (∥b∥₊) using 1,
      ring, },
    have := div_le_of_le_mul (f.op_nnnorm_le_bound _ (by simpa only [sqrt_sq, sqrt_mul]
      using (λ b, sqrt_le_sqrt_iff.mpr ((h b).trans (h1 b))))),
    convert rpow_le_rpow this (by exact_mod_cast zero_le (2 : ℕ) : 0 ≤ (2 : ℝ)),
    { simp only [rpow_two, div_pow, sq_sqrt], simp only [sq, mul_self_div_self] },
    { simp only [rpow_two, sq_sqrt] } },
  have h1 : ∀ b, ∥ a.left b ∥₊ ^ 2 ≤  ∥ a.right ∥₊ * ∥ a.left b ∥₊ * ∥ b ∥₊,
  { intros b,
    calc ∥ a.left b ∥₊ ^ 2
        = ∥ star (a.left b) * (a.left b) ∥₊
        : by simpa only [←sq] using (cstar_ring.nnnorm_star_mul_self).symm
    ... ≤ ∥ a.right (star (a.left b))∥₊ * ∥ b ∥₊ : a.central (star (a.left b)) b ▸ nnnorm_mul_le _ _
    ... ≤ ∥ a.right ∥₊ * ∥ a.left b ∥₊ * ∥ b ∥₊
        : nnnorm_star (a.left b) ▸ mul_le_mul_right' (a.right.le_op_nnnorm _) _},
  have h2 : ∀ b, ∥ a.right b ∥₊ ^ 2 ≤  ∥ a.left ∥₊ * ∥ a.right b ∥₊ * ∥ b ∥₊,
  { intros b,
    calc ∥ a.right b ∥₊ ^ 2
        = ∥ a.right b * star (a.right b) ∥₊
        : by simpa only [←sq] using (cstar_ring.nnnorm_self_mul_star).symm
    ... ≤ ∥ b ∥₊ * ∥ a.left (star (a.right b))∥₊
        : (a.central b (star (a.right b))).symm ▸ nnnorm_mul_le _ _
    ... = ∥ a.left (star (a.right b))∥₊ * ∥b∥₊ : mul_comm _ _
    ... ≤ ∥ a.left ∥₊ * ∥ a.right b ∥₊ * ∥ b ∥₊
        : nnnorm_star (a.right b) ▸ mul_le_mul_right' (a.left.le_op_nnnorm _) _  },
  exact le_antisymm (h0 _ _ h1) (h0 _ _ h2),
end

lemma norm_left (a : 𝓜(𝕜, A)) : ∥a∥ = ∥a.left∥ :=
by simp only [norm_eq, norm_left_eq_right, max_eq_right, eq_self_iff_true]
lemma norm_right (a : 𝓜(𝕜, A)) : ∥a∥ = ∥a.right∥ := by rw [norm_left, norm_left_eq_right]
lemma nnnorm_left (a : 𝓜(𝕜, A)) : ∥a∥₊ = ∥a.left∥₊ := subtype.ext (norm_left a)
lemma nnnorm_right (a : 𝓜(𝕜, A)) : ∥a∥₊ = ∥a.right∥₊ := subtype.ext (norm_right a)

end nontrivially_normed

section densely_normed

variables {𝕜 A : Type*} [densely_normed_field 𝕜] [star_ring 𝕜]
variables [non_unital_normed_ring A] [star_ring A] [cstar_ring A]
variables [normed_space 𝕜 A] [smul_comm_class 𝕜 A A] [is_scalar_tower 𝕜 A A] [star_module 𝕜 A]

instance : cstar_ring 𝓜(𝕜, A) :=
{ norm_star_mul_self := λ a, congr_arg (coe : ℝ≥0 → ℝ) $ show ∥star a * a∥₊ = ∥a∥₊ * ∥a∥₊, from
  begin
    have hball : (metric.closed_ball (0 : A) 1).nonempty :=
      metric.nonempty_closed_ball.2 (zero_le_one),
    have key : ∀ x y, ∥x∥₊ ≤ 1 → ∥y∥₊ ≤ 1 → ∥a.right (star (a.left (star x))) * y∥₊ ≤ ∥a∥₊ * ∥a∥₊,
    { intros x y hx hy,
      rw [a.central],
      calc ∥star (a.left (star x)) * a.left y∥₊ ≤ ∥a.left (star x)∥₊ * ∥a.left y∥₊
          : nnnorm_star (a.left (star x)) ▸ nnnorm_mul_le _ _
      ... ≤ (∥a.left∥₊ * 1) * (∥a.left∥₊ * 1)
          : mul_le_mul' (a.left.le_op_norm_of_le ((nnnorm_star x).trans_le hx))
              (a.left.le_op_norm_of_le hy)
      ... ≤ ∥a∥₊ * ∥a∥₊ : by simp only [mul_one, nnnorm_left] },
    rw nnnorm_right,
    simp only [mul_right, ←Sup_closed_unit_ball_eq_nnnorm, star_right, mul_apply],
      simp only [←@op_nnnorm_mul 𝕜 A],
      simp only [←Sup_closed_unit_ball_eq_nnnorm, mul_apply'],
    refine cSup_eq_of_forall_le_of_forall_lt_exists_gt (hball.image _) _ (λ r hr, _),
    { rintro - ⟨x, hx, rfl⟩,
      refine cSup_le (hball.image _) _,
      rintro - ⟨y, hy, rfl⟩,
      exact key x y (mem_closed_ball_zero_iff.1 hx) (mem_closed_ball_zero_iff.1 hy) },
    { simp only [set.mem_image, set.mem_set_of_eq, exists_prop, exists_exists_and_eq_and],
      have hr' : r.sqrt < ∥a∥₊ := (∥a∥₊).sqrt_mul_self ▸ nnreal.sqrt_lt_sqrt_iff.2 hr,
      simp_rw [nnnorm_left, ←Sup_closed_unit_ball_eq_nnnorm] at hr',
      obtain ⟨_, ⟨x, hx, rfl⟩, hxr⟩ := exists_lt_of_lt_cSup (hball.image _) hr',
      have hx' : ∥x∥₊ ≤ 1 := mem_closed_ball_zero_iff.1 hx,
      refine ⟨star x, mem_closed_ball_zero_iff.2 ((nnnorm_star x).trans_le hx'), _⟩,
      refine lt_cSup_of_lt _ ⟨x, hx, rfl⟩ _,
      { refine ⟨∥a∥₊ * ∥a∥₊, _⟩,
        rintros - ⟨y, hy, rfl⟩,
        exact key (star x) y ((nnnorm_star x).trans_le hx') (mem_closed_ball_zero_iff.1 hy) },
      { simpa only [a.central, star_star, cstar_ring.nnnorm_star_mul_self, nnreal.sq_sqrt, ←sq]
          using pow_lt_pow_of_lt_left hxr zero_le' two_pos } }
  end }

end densely_normed

end double_centralizer
