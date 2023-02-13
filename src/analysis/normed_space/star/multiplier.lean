/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux, Jon Bannon
-/

import algebra.star.star_alg_hom
import analysis.normed_space.star.basic
import analysis.normed_space.operator_norm
import analysis.special_functions.pow
import analysis.normed_space.star.mul

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

We make the hypotheses on `𝕜` as weak as possible so that, in particular, this construction works
for both `𝕜 = ℝ` and `𝕜 = ℂ`. The reader familiar with C⋆-algebra theory may recognize that one
only needs `L` and `R` to be functions instead of continuous linear maps, at least when `A` is a
C⋆-algebra. Our intention is simply to eventually provide a constructor for this situation.

## TODO

+ define a type synonym for `𝓜(𝕜, A)` which is equipped with the strict uniform space structure
  and show it is complete
+ show that the image of `A` in `𝓜(𝕜, A)` is an essential ideal
+ prove the universal property of `𝓜(𝕜, A)`
* Construct a double centralizer from a pair of maps (not necessarily linear or continuous)
  `L : A → A`, `R : A → A` satisfying the centrality condition `∀ x y, R x * y = x * L y`.
-/

noncomputable theory

open_locale nnreal ennreal
open nnreal continuous_linear_map

universes u v

/-- The type of *double centralizers*, also known as the *multiplier algebra* and denoted by
`𝓜(𝕜, A)`, of a non-unital normed algebra. -/
@[ext]
structure double_centralizer (𝕜 : Type u) (A : Type v) [nontrivially_normed_field 𝕜]
  [non_unital_normed_ring A] [normed_space 𝕜 A] [smul_comm_class 𝕜 A A] [is_scalar_tower 𝕜 A A]
  extends (A →L[𝕜] A) × (A →L[𝕜] A) :=
(central : ∀ x y : A, snd x * y = x * fst y)

localized "notation `𝓜(` 𝕜 `, ` A `)` := double_centralizer 𝕜 A" in multiplier_algebra

namespace double_centralizer

section nontrivially_normed

variables (𝕜 A : Type*) [nontrivially_normed_field 𝕜] [non_unital_normed_ring A]
variables [normed_space 𝕜 A] [smul_comm_class 𝕜 A A] [is_scalar_tower 𝕜 A A]

instance : inhabited 𝓜(𝕜, A) :=
{ default := ⟨1, λ x y, rfl⟩ }

/-!
### Algebraic structure

Because the multiplier algebra is defined as the algebra of double centralizers, there is a natural
injection `double_centralizer.to_prod_mop : 𝓜(𝕜, A) → (A →L[𝕜] A) × (A →L[𝕜] A)ᵐᵒᵖ` defined by
`λ a, (a.fst, mul_opposite.op a.snd)`. We use this map to pull back the the ring, module and
algebra structure from `(A →L[𝕜] A) × (A →L[𝕜] A)ᵐᵒᵖ` to `𝓜(𝕜, A)`. -/

variables {𝕜 A}

lemma range_to_prod : set.range to_prod = {lr : (A →L[𝕜] A) × _ | ∀ x y, lr.2 x * y = x * lr.1 y} :=
set.ext $ λ x, ⟨by {rintro ⟨a, rfl⟩, exact a.central}, λ hx, ⟨⟨x, hx⟩, rfl⟩⟩

instance : has_add 𝓜(𝕜, A) :=
{ add := λ a b,
  { to_prod := a.to_prod + b.to_prod,
    central := λ x y, show (a.snd + b.snd) x * y = x * (a.fst + b.fst) y,
      by simp only [continuous_linear_map.add_apply, mul_add, add_mul, central] } }

instance : has_zero 𝓜(𝕜, A) :=
{ zero :=
  { to_prod := 0,
    central := λ x y, (zero_mul y).trans (mul_zero x).symm } }

instance : has_neg 𝓜(𝕜, A) :=
{ neg := λ a,
  { to_prod := -a.to_prod,
    central := λ x y, show -a.snd x * y = x * -a.fst y,
      by simp only [continuous_linear_map.neg_apply, neg_mul, mul_neg, central] } }

instance : has_sub 𝓜(𝕜, A) :=
{ sub := λ a b,
  { to_prod := a.to_prod - b.to_prod,
    central := λ x y, show (a.snd - b.snd) x * y = x * (a.fst - b.fst) y,
      by simp only [continuous_linear_map.sub_apply, sub_mul, mul_sub, central] } }

section scalars

variables {S : Type*} [monoid S] [distrib_mul_action S A] [smul_comm_class 𝕜 S A]
  [has_continuous_const_smul S A] [is_scalar_tower S A A] [smul_comm_class S A A]

instance : has_smul S 𝓜(𝕜, A) :=
{ smul := λ s a,
  { to_prod := s • a.to_prod,
    central := λ x y, show (s • a.snd) x * y = x * (s • a.fst) y,
      by simp only [continuous_linear_map.smul_apply, mul_smul_comm, smul_mul_assoc, central] } }

@[simp] lemma smul_fst (k : 𝕜) (a : 𝓜(𝕜, A)) : (k • a).fst = k • a.fst := rfl
@[simp] lemma smul_snd (k : 𝕜) (a : 𝓜(𝕜, A)) : (k • a).snd = k • a.snd := rfl

end scalars

instance : has_one 𝓜(𝕜, A) := ⟨⟨1, λ x y, rfl⟩⟩

instance : has_mul 𝓜(𝕜, A) :=
{ mul := λ a b,
  { to_prod := (a.fst.comp b.fst, b.snd.comp a.snd),
    central := λ x y, show b.snd (a.snd x) * y = x * (a.fst (b.fst y)),
      by simp only [central] } }

instance : has_nat_cast 𝓜(𝕜, A) :=
  { nat_cast := λ n, ⟨n, λ x y, by simp only [←nat.smul_one_eq_coe, prod.smul_fst, prod.smul_snd,
      prod.fst_one, prod.snd_one, smul_apply n 1, one_apply, mul_smul_comm, smul_mul_assoc]⟩ }

instance : has_int_cast 𝓜(𝕜, A) :=
  { int_cast := λ n, ⟨n, λ x y, by simp only [←int.smul_one_eq_coe, prod.smul_fst, prod.smul_snd,
      prod.fst_one, prod.snd_one, smul_apply n 1, one_apply, mul_smul_comm, smul_mul_assoc]⟩ }

instance : has_pow 𝓜(𝕜, A) ℕ :=
  { pow := λ a n, ⟨a.to_prod ^ n, λ x y,
    begin
      induction n with k hk generalizing x y,
      refl,
      rw [prod.pow_snd, prod.pow_fst] at hk ⊢,
      rw [pow_succ a.snd, mul_apply, a.central, hk, pow_succ' a.fst, mul_apply],
    end⟩, }

@[simp] lemma add_fst (a b : 𝓜(𝕜, A)) : (a + b).fst = a.fst + b.fst := rfl
@[simp] lemma add_snd (a b : 𝓜(𝕜, A)) : (a + b).snd = a.snd + b.snd := rfl
@[simp] lemma zero_fst : (0 : 𝓜(𝕜, A)).fst = 0 := rfl
@[simp] lemma zero_snd : (0 : 𝓜(𝕜, A)).snd = 0 := rfl
@[simp] lemma neg_fst (a : 𝓜(𝕜, A)) : (-a).fst = -a.fst := rfl
@[simp] lemma neg_snd (a : 𝓜(𝕜, A)) : (-a).snd = -a.snd := rfl
@[simp] lemma sub_fst (a b : 𝓜(𝕜, A)) : (a - b).fst = a.fst - b.fst := rfl
@[simp] lemma sub_snd (a b : 𝓜(𝕜, A)) : (a - b).snd = a.snd - b.snd := rfl
@[simp] lemma one_fst : (1 : 𝓜(𝕜, A)).fst = 1 := rfl
@[simp] lemma one_snd : (1 : 𝓜(𝕜, A)).snd = 1 := rfl
@[simp] lemma mul_fst (a b : 𝓜(𝕜, A)) : (a * b).fst = a.fst * b.fst := rfl
@[simp] lemma mul_snd (a b : 𝓜(𝕜, A)) : (a * b).snd = b.snd * a.snd := rfl
@[simp] lemma nat_cast_fst (n : ℕ) : (n : 𝓜(𝕜 , A)).fst = n := rfl
@[simp] lemma nat_cast_snd (n : ℕ) : (n : 𝓜(𝕜 , A)).snd = n := rfl
@[simp] lemma int_cast_fst (n : ℤ) : (n : 𝓜(𝕜 , A)).fst = n := rfl
@[simp] lemma int_cast_snd (n : ℤ) : (n : 𝓜(𝕜 , A)).snd = n := rfl
@[simp] lemma pow_fst (n : ℕ) (a : 𝓜(𝕜, A)) : (a ^ n).fst = a.fst ^ n := rfl
@[simp] lemma pow_snd (n : ℕ) (a : 𝓜(𝕜, A)) : (a ^ n).snd = a.snd ^ n := rfl

/-- The natural injection from `double_centralizer.to_prod` except the second coordinate inherits
`mul_opposite.op`. The ring structure on `𝓜(𝕜, A)` is the pullback under this map. -/
def to_prod_mop : 𝓜(𝕜, A) → ((A →L[𝕜] A) × (A →L[𝕜] A)ᵐᵒᵖ) :=
λ a, (a.fst, mul_opposite.op a.snd)

/-- The ring structure is inherited as the pullback under the injective map
`double_centralizer.to_prod_mop : 𝓜(𝕜, A) → (A →L[𝕜] A) × (A →L[𝕜] A)ᵐᵒᵖ` -/
instance : ring 𝓜(𝕜, A) :=
function.injective.ring to_prod_mop
  (λ a b h, let h' := prod.ext_iff.mp h in ext _ _ $ prod.ext h'.1 $ mul_opposite.op_injective h'.2)
  rfl rfl (λ _ _, rfl) (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl)
  (λ x n, by simpa only [to_prod_mop, to_prod, prod.smul_fst, prod.smul_snd, mul_opposite.op_smul])
  (λ x n, by simpa only [to_prod_mop, to_prod, prod.smul_fst, prod.smul_snd, mul_opposite.op_smul])
  (λ x n, by simpa only [to_prod_mop, to_prod, prod.pow_fst, prod.pow_fst, mul_opposite.op_pow])
  (λ _, rfl) (λ _, rfl)

/-- The canonical map `double_centralizer.to_prod` as an additive group homomorphism. -/
def add_group_hom_to_prod : 𝓜(𝕜, A) →+ (A →L[𝕜] A) × (A →L[𝕜] A) :=
{ to_fun := to_prod,
  map_zero' := rfl,
  map_add' := λ x y, rfl }

/-- The module structure is inherited as the pullback under the additive group monomoprhism
`double_centralizer.to_prod : 𝓜(𝕜, A) →+ (A →L[𝕜] A) × (A →L[𝕜] A)` -/
instance : module 𝕜 𝓜(𝕜, A) :=
function.injective.module 𝕜 add_group_hom_to_prod ext (λ x y, rfl)

noncomputable instance : algebra 𝕜 𝓜(𝕜, A) :=
algebra.of_module
  (λ k a b, by {ext; simp only [mul_fst, smul_fst, mul_snd, smul_snd, coe_smul',pi.smul_apply,
    continuous_linear_map.coe_mul, function.comp_app, continuous_linear_map.map_smul]})
  (λ k a b, by {ext; simp only [mul_fst, smul_fst, mul_snd, smul_snd, algebra.mul_smul_comm,
    coe_smul', continuous_linear_map.coe_mul, pi.smul_apply, function.comp_app]})

/-!
### Star structure
-/

section star

variables [star_ring 𝕜] [star_ring A] [star_module 𝕜 A] [normed_star_group A]

/-- The star operation on `a : 𝓜(𝕜, A)` is given by
`(star a).to_prod = (star ∘ a.snd ∘ star, star ∘ a.fst ∘ star)`. -/
instance : has_star 𝓜(𝕜, A) :=
{ star := λ a,
  { fst := (((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A →L⋆[𝕜] A).comp a.snd).comp
      ((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A →L⋆[𝕜] A),
    snd := (((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A →L⋆[𝕜] A).comp a.fst).comp
      ((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A →L⋆[𝕜] A),
    central := λ x y, by simpa only [star_mul, star_star]
      using (congr_arg star (a.central (star y) (star x))).symm } }

@[simp] lemma star_fst (a : 𝓜(𝕜, A)) (b : A) : (star a).fst b = star (a.snd (star b)) := rfl
@[simp] lemma star_snd (a : 𝓜(𝕜, A)) (b : A) : (star a).snd b = star (a.fst (star b)) := rfl

instance : star_add_monoid 𝓜(𝕜, A) :=
{ star_involutive := λ x, by {ext; simp only [star_fst, star_snd, star_star]},
  star_add := λ x y, by {ext; simp only [star_fst, star_snd, add_fst, add_snd,
    continuous_linear_map.add_apply, star_add]},
  .. double_centralizer.has_star }

instance : star_ring 𝓜(𝕜, A) :=
{ star_mul := λ a b, by {ext; simp only [star_fst, star_snd, mul_fst, mul_snd, star_star,
    continuous_linear_map.coe_mul, function.comp_app]},
  .. double_centralizer.star_add_monoid }

instance : star_module 𝕜 𝓜(𝕜, A) :=
{ star_smul := λ k a, by {ext; exact star_smul _ _},
  .. double_centralizer.star_add_monoid }

end star

/-!
### Coercion from an algebra into its multiplier algebra
-/

section
variables [star_ring 𝕜] [star_ring A] [star_module 𝕜 A] [normed_star_group A]

/-- The coercion of an algebra into its multiplier algebra as a non-unital star algebra
homomorphism. -/
def coe_hom : A →⋆ₙₐ[𝕜] 𝓜(𝕜, A) :=
{ to_fun := λ a,
  { fst := continuous_linear_map.mul 𝕜 A a,
    snd := (continuous_linear_map.mul 𝕜 A).flip a,
    central := λ x y, mul_assoc _ _ _ },
  map_smul' := λ k a, by {ext; simp only [continuous_linear_map.map_smul, smul_fst, smul_snd]},
  map_zero' := by {ext; simp only [map_zero, zero_fst, zero_snd]},
  map_add' := λ a b, by {ext; simp only [map_add, add_fst, add_snd]},
  map_mul' := λ a b, by {ext; simp only [mul_apply', flip_apply, mul_fst, mul_snd,
    continuous_linear_map.coe_mul, function.comp_app, mul_assoc]},
  map_star' := λ a, by {ext; simp only [mul_apply', star_fst, star_snd, flip_apply,
    star_mul, star_star]} }
end

noncomputable instance [star_ring 𝕜] [star_ring A] [star_module 𝕜 A] [normed_star_group A] :
  has_coe_t A 𝓜(𝕜, A) :=
{ coe := (double_centralizer.coe_hom : A → 𝓜(𝕜, A)) }

@[simp, norm_cast]
lemma coe_fst [star_ring 𝕜] [star_ring A] [star_module 𝕜 A] [normed_star_group A] (a : A) :
  (a : 𝓜(𝕜, A)).fst = continuous_linear_map.mul 𝕜 A a := rfl
@[simp, norm_cast]
lemma coe_snd [star_ring 𝕜] [star_ring A] [star_module 𝕜 A] [normed_star_group A] (a : A) :
  (a : 𝓜(𝕜, A)).snd = (continuous_linear_map.mul 𝕜 A).flip a := rfl

/-!
### Norm structures
We define the norm structure on `𝓜(𝕜, A)` as the pullback under
`double_centralizer.add_group_hom_to_prod : 𝓜(𝕜, A) →+ (A →L[𝕜] A) × (A →L[𝕜] A)`, which provides
a definitional isometric embedding. Consequently, completeness of `𝓜(𝕜, A)` is obtained by proving
that the range of this map is closed.

In addition, we prove that `𝓜(𝕜, A)` is a normed algebra, and, when `A` is a C⋆-algebra, we show
that `𝓜(𝕜, A)` is also a C⋆-algebra. Moreover, in this case, for `a : 𝓜(𝕜, A)`,
`‖a‖ = ‖a.fst‖ = ‖a.snd‖`. -/

/-- The normed group structure is inherited as the pullback under the additive group monomoprhism
`double_centralizer.to_prod : 𝓜(𝕜, A) →+ (A →L[𝕜] A) × (A →L[𝕜] A)` -/
instance : normed_add_comm_group 𝓜(𝕜, A) :=
normed_add_comm_group.induced _ _ (add_group_hom_to_prod : 𝓜(𝕜, A) →+ (A →L[𝕜] A) × (A →L[𝕜] A))
  ext

@[simp] lemma norm_eq (a : 𝓜(𝕜, A)) : ‖a‖ = max (‖a.fst‖) (‖a.snd‖) := rfl

instance : normed_space 𝕜 𝓜(𝕜, A) :=
{ norm_smul_le := λ k a, show max (‖k • a.fst‖) (‖k • a.snd‖) ≤‖k‖ * max (‖a.fst‖) (‖a.snd‖),
    by simp only [mul_max_of_nonneg _ _ (norm_nonneg k), norm_smul],
  .. double_centralizer.module }

lemma uniform_embedding_to_prod : uniform_embedding (@to_prod 𝕜 A _ _ _ _ _) :=
uniform_embedding_comap ext

instance [complete_space A] : complete_space 𝓜(𝕜, A) :=
begin
  rw complete_space_iff_is_complete_range uniform_embedding_to_prod.to_uniform_inducing,
  apply is_closed.is_complete,
  simp only [range_to_prod, set.set_of_forall],
  refine is_closed_Inter (λ x, is_closed_Inter $ λ y, is_closed_eq _ _),
  exacts [((continuous_linear_map.apply 𝕜 A _).continuous.comp continuous_snd).mul continuous_const,
    continuous_const.mul ((continuous_linear_map.apply 𝕜 A _).continuous.comp continuous_fst)],
end

noncomputable instance : normed_ring 𝓜(𝕜, A) :=
{ norm_mul := λ a b,
    begin
      refine max_le ((norm_mul_le _ _).trans _) ((norm_mul_le _ _).trans _),
      exact mul_le_mul (le_max_left _ _) (le_max_left _ _) (norm_nonneg _)
        ((norm_nonneg _).trans $ le_max_left _ _),
      exact mul_comm (‖a.snd‖) (‖b.snd‖) ▸ mul_le_mul (le_max_right _ _) (le_max_right _ _)
        (norm_nonneg _) ((norm_nonneg _).trans $ le_max_right _ _),
    end,
  .. double_centralizer.ring,
  .. double_centralizer.normed_add_comm_group }

noncomputable instance : normed_algebra 𝕜 𝓜(𝕜, A) :=
{ ..double_centralizer.algebra, ..double_centralizer.normed_space }

variables [star_ring A] [cstar_ring A]

/-- For `a : 𝓜(𝕜, A)`, the norms of `a.fst` and `a.snd` coincide, and hence these
also coincide with `‖a‖` which is `max (‖a.fst‖) (‖a.snd‖)`. -/
lemma norm_fst_eq_snd (a : 𝓜(𝕜, A)) : ‖a.fst‖ = ‖a.snd‖ :=
begin
  -- a handy lemma for this proof
  have h0 : ∀ f : A →L[𝕜] A, ∀ C : ℝ≥0, (∀ b : A, ‖f b‖₊ ^ 2 ≤ C * ‖f b‖₊ * ‖b‖₊) → ‖f‖₊ ≤ C,
  { intros f C h,
    have h1 : ∀ b, C * ‖f b‖₊ * ‖b‖₊ ≤ C * ‖f‖₊ * ‖b‖₊ ^ 2,
    { intros b,
      convert mul_le_mul_right' (mul_le_mul_left' (f.le_op_nnnorm b) C) (‖b‖₊) using 1,
      ring, },
    have := div_le_of_le_mul (f.op_nnnorm_le_bound _ (by simpa only [sqrt_sq, sqrt_mul]
      using (λ b, sqrt_le_sqrt_iff.mpr ((h b).trans (h1 b))))),
    convert rpow_le_rpow this two_pos.le,
    { simp only [rpow_two, div_pow, sq_sqrt], simp only [sq, mul_self_div_self] },
    { simp only [rpow_two, sq_sqrt] } },
  have h1 : ∀ b, ‖a.fst b‖₊ ^ 2 ≤ ‖a.snd‖₊ * ‖a.fst b‖₊ * ‖b‖₊,
  { intros b,
    calc ‖a.fst b‖₊ ^ 2
        = ‖star (a.fst b) * (a.fst b)‖₊
        : by simpa only [←sq] using (cstar_ring.nnnorm_star_mul_self).symm
    ... ≤ ‖a.snd (star (a.fst b))‖₊ * ‖b‖₊ : a.central (star (a.fst b)) b ▸ nnnorm_mul_le _ _
    ... ≤ ‖a.snd‖₊ * ‖a.fst b‖₊ * ‖b‖₊
        : nnnorm_star (a.fst b) ▸ mul_le_mul_right' (a.snd.le_op_nnnorm _) _},
  have h2 : ∀ b, ‖a.snd b‖₊ ^ 2 ≤ ‖a.fst‖₊ * ‖a.snd b‖₊ * ‖b‖₊,
  { intros b,
    calc ‖a.snd b‖₊ ^ 2
        = ‖a.snd b * star (a.snd b)‖₊
        : by simpa only [←sq] using (cstar_ring.nnnorm_self_mul_star).symm
    ... ≤ ‖b‖₊ * ‖a.fst (star (a.snd b))‖₊
        : (a.central b (star (a.snd b))).symm ▸ nnnorm_mul_le _ _
    ... = ‖a.fst (star (a.snd b))‖₊ * ‖b‖₊ : mul_comm _ _
    ... ≤ ‖a.fst‖₊ * ‖a.snd b‖₊ * ‖b‖₊
        : nnnorm_star (a.snd b) ▸ mul_le_mul_right' (a.fst.le_op_nnnorm _) _  },
  exact le_antisymm (h0 _ _ h1) (h0 _ _ h2),
end

lemma norm_fst (a : 𝓜(𝕜, A)) : ‖a‖ = ‖a.fst‖ :=
  by simp only [norm_eq, norm_fst_eq_snd, max_eq_right, eq_self_iff_true]
lemma norm_snd (a : 𝓜(𝕜, A)) : ‖a‖ = ‖a.snd‖ := by rw [norm_fst, norm_fst_eq_snd]
lemma nnnorm_fst (a : 𝓜(𝕜, A)) : ‖a‖₊ = ‖a.fst‖₊ := subtype.ext (norm_fst a)
lemma nnnorm_snd (a : 𝓜(𝕜, A)) : ‖a‖₊ = ‖a.snd‖₊ := subtype.ext (norm_snd a)

end nontrivially_normed

section densely_normed

variables {𝕜 A : Type*} [densely_normed_field 𝕜] [star_ring 𝕜]
variables [non_unital_normed_ring A] [star_ring A] [cstar_ring A]
variables [normed_space 𝕜 A] [smul_comm_class 𝕜 A A] [is_scalar_tower 𝕜 A A] [star_module 𝕜 A]

instance : cstar_ring 𝓜(𝕜, A) :=
{ norm_star_mul_self := λ a, congr_arg (coe : ℝ≥0 → ℝ) $ show ‖star a * a‖₊ = ‖a‖₊ * ‖a‖₊, from
  begin
    /- The essence of the argument is this: let `a = (L,R)` and recall `‖a‖ = ‖L‖`.
    `star a = (star ∘ R ∘ star, star ∘ L ∘ star)`. Then for any `x y : A`, we have
    `‖star a * a‖ = ‖(star a * a).snd‖ = ‖R (star (L (star x))) * y‖ = ‖star (L (star x)) * L y‖`
    Now, on the one hand,
    `‖star (L (star x)) * L y‖ ≤ ‖star (L (star x))‖ * ‖L y‖ = ‖L (star x)‖ * ‖L y‖ ≤ ‖L‖ ^ 2`
    whenever `‖x‖, ‖y‖ ≤ 1`, so the supremum over all such `x, y` is at most `‖L‖ ^ 2`.
    On the other hand, for any `‖z‖ ≤ 1`, we may choose `x := star z` and `y := z` to get:
    `‖star (L (star x)) * L y‖ = ‖star (L z) * (L z)‖ = ‖L z‖ ^ 2`, and taking the supremum over
    all such `z` yields that the supremum is at least `‖L‖ ^ 2`. It is the latter part of the
    argument where `densely_normed_field 𝕜` is required (for `Sup_closed_unit_ball_eq_nnnorm`). -/
    have hball : (metric.closed_ball (0 : A) 1).nonempty :=
      metric.nonempty_closed_ball.2 (zero_le_one),
    have key : ∀ x y, ‖x‖₊ ≤ 1 → ‖y‖₊ ≤ 1 → ‖a.snd (star (a.fst (star x))) * y‖₊ ≤ ‖a‖₊ * ‖a‖₊,
    { intros x y hx hy,
      rw [a.central],
      calc ‖star (a.fst (star x)) * a.fst y‖₊ ≤ ‖a.fst (star x)‖₊ * ‖a.fst y‖₊
          : nnnorm_star (a.fst (star x)) ▸ nnnorm_mul_le _ _
      ... ≤ (‖a.fst‖₊ * 1) * (‖a.fst‖₊ * 1)
          : mul_le_mul' (a.fst.le_op_norm_of_le ((nnnorm_star x).trans_le hx))
              (a.fst.le_op_norm_of_le hy)
      ... ≤ ‖a‖₊ * ‖a‖₊ : by simp only [mul_one, nnnorm_fst] },
    rw nnnorm_snd,
    simp only [mul_snd, ←Sup_closed_unit_ball_eq_nnnorm, star_snd, mul_apply],
    simp only [←@op_nnnorm_mul 𝕜 A],
    simp only [←Sup_closed_unit_ball_eq_nnnorm, mul_apply'],
    refine cSup_eq_of_forall_le_of_forall_lt_exists_gt (hball.image _) _ (λ r hr, _),
    { rintro - ⟨x, hx, rfl⟩,
      refine cSup_le (hball.image _) _,
      rintro - ⟨y, hy, rfl⟩,
      exact key x y (mem_closed_ball_zero_iff.1 hx) (mem_closed_ball_zero_iff.1 hy) },
    { simp only [set.mem_image, set.mem_set_of_eq, exists_prop, exists_exists_and_eq_and],
      have hr' : r.sqrt < ‖a‖₊ := (‖a‖₊).sqrt_mul_self ▸ nnreal.sqrt_lt_sqrt_iff.2 hr,
      simp_rw [nnnorm_fst, ←Sup_closed_unit_ball_eq_nnnorm] at hr',
      obtain ⟨_, ⟨x, hx, rfl⟩, hxr⟩ := exists_lt_of_lt_cSup (hball.image _) hr',
      have hx' : ‖x‖₊ ≤ 1 := mem_closed_ball_zero_iff.1 hx,
      refine ⟨star x, mem_closed_ball_zero_iff.2 ((nnnorm_star x).trans_le hx'), _⟩,
      refine lt_cSup_of_lt _ ⟨x, hx, rfl⟩ _,
      { refine ⟨‖a‖₊ * ‖a‖₊, _⟩,
        rintros - ⟨y, hy, rfl⟩,
        exact key (star x) y ((nnnorm_star x).trans_le hx') (mem_closed_ball_zero_iff.1 hy) },
      { simpa only [a.central, star_star, cstar_ring.nnnorm_star_mul_self, nnreal.sq_sqrt, ←sq]
          using pow_lt_pow_of_lt_left hxr zero_le' two_pos } }
  end }

end densely_normed

end double_centralizer
