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
for both `𝕜 = ℝ` and `𝕜 = ℂ`.

The reader familiar with C⋆-algebra theory may recognize that one
only needs `L` and `R` to be functions instead of continuous linear maps, at least when `A` is a
C⋆-algebra. Our intention is simply to eventually provide a constructor for this situation.

We pull back the `normed_algebra` structure (and everything contained therein) through the
ring (even algebra) homomorphism
`double_centralizer.to_prod_mul_opposite_hom : 𝓜(𝕜, A) →+* (A →L[𝕜] A) × (A →L[𝕜] A)ᵐᵒᵖ` which
sends `a : 𝓜(𝕜, A)` to `(a.fst, mul_opposite.op a.snd)`. The star structure is provided
separately.

## References

* https://en.wikipedia.org/wiki/Multiplier_algebra

## TODO

+ Define a type synonym for `𝓜(𝕜, A)` which is equipped with the strict uniform space structure
  and show it is complete
+ Show that the image of `A` in `𝓜(𝕜, A)` is an essential ideal
+ Prove the universal property of `𝓜(𝕜, A)`
+ Construct a double centralizer from a pair of maps (not necessarily linear or continuous)
  `L : A → A`, `R : A → A` satisfying the centrality condition `∀ x y, R x * y = x * L y`.
+ Show that if `A` is unital, then `A ≃⋆ₐ[𝕜] 𝓜(𝕜, A)`.
-/

open_locale nnreal ennreal
open nnreal continuous_linear_map mul_opposite

universes u v

/-- The type of *double centralizers*, also known as the *multiplier algebra* and denoted by
`𝓜(𝕜, A)`, of a non-unital normed algebra.

If `x : 𝓜(𝕜, A)`, then `x.fst` and `x.snd` are what is usually referred to as $L$ and $R$. -/
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

/-!
### Algebraic structure

Because the multiplier algebra is defined as the algebra of double centralizers, there is a natural
injection `double_centralizer.to_prod_mul_opposite : 𝓜(𝕜, A) → (A →L[𝕜] A) × (A →L[𝕜] A)ᵐᵒᵖ`
defined by `λ a, (a.fst, mul_opposite.op a.snd)`. We use this map to pull back the ring, module and
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

@[simp] lemma smul_to_prod (s : S) (a : 𝓜(𝕜, A)) : (s • a).to_prod = s • a.to_prod := rfl
lemma smul_fst (s : S) (a : 𝓜(𝕜, A)) : (s • a).fst = s • a.fst := rfl
lemma smul_snd (s : S) (a : 𝓜(𝕜, A)) : (s • a).snd = s • a.snd := rfl

variables {T : Type*} [monoid T] [distrib_mul_action T A] [smul_comm_class 𝕜 T A]
  [has_continuous_const_smul T A] [is_scalar_tower T A A] [smul_comm_class T A A]

instance [has_smul S T] [is_scalar_tower S T A] : is_scalar_tower S T 𝓜(𝕜, A) :=
{ smul_assoc := λ _ _ a, ext _ _ $ smul_assoc _ _ a.to_prod }

instance [smul_comm_class S T A] : smul_comm_class S T 𝓜(𝕜, A) :=
{ smul_comm := λ _ _ a, ext _ _ $ smul_comm _ _ a.to_prod }

instance {R : Type*} [semiring R] [module R A] [smul_comm_class 𝕜 R A]
  [has_continuous_const_smul R A] [is_scalar_tower R A A] [smul_comm_class R A A]
  [module Rᵐᵒᵖ A] [is_central_scalar R A] : is_central_scalar R 𝓜(𝕜, A) :=
{ op_smul_eq_smul := λ _ a, ext _ _ $ op_smul_eq_smul _ a.to_prod }

end scalars

instance : has_one 𝓜(𝕜, A) := ⟨⟨1, λ x y, rfl⟩⟩

instance : has_mul 𝓜(𝕜, A) :=
{ mul := λ a b,
  { to_prod := (a.fst.comp b.fst, b.snd.comp a.snd),
    central := λ x y, show b.snd (a.snd x) * y = x * a.fst (b.fst y),
      by simp only [central] } }

instance : has_nat_cast 𝓜(𝕜, A) :=
{ nat_cast := λ n, ⟨n, λ x y,
  begin
    rw [prod.snd_nat_cast, prod.fst_nat_cast],
    simp only [←nat.smul_one_eq_coe, smul_apply, one_apply, mul_smul_comm, smul_mul_assoc],
  end⟩ }

instance : has_int_cast 𝓜(𝕜, A) :=
{ int_cast := λ n, ⟨n, λ x y,
  begin
    rw [prod.snd_int_cast, prod.fst_int_cast],
    simp only [←int.smul_one_eq_coe, smul_apply, one_apply, mul_smul_comm, smul_mul_assoc],
  end⟩ }

instance : has_pow 𝓜(𝕜, A) ℕ :=
{ pow := λ a n, ⟨a.to_prod ^ n, λ x y,
  begin
    induction n with k hk generalizing x y,
    { refl },
    { rw [prod.pow_snd, prod.pow_fst] at hk ⊢,
      rw [pow_succ a.snd, mul_apply, a.central, hk, pow_succ' a.fst, mul_apply] },
  end⟩ }

instance : inhabited 𝓜(𝕜, A) := ⟨0⟩

@[simp] lemma add_to_prod (a b : 𝓜(𝕜, A)) : (a + b).to_prod = a.to_prod + b.to_prod := rfl
@[simp] lemma zero_to_prod : (0 : 𝓜(𝕜, A)).to_prod = 0 := rfl
@[simp] lemma neg_to_prod (a : 𝓜(𝕜, A)) : (-a).to_prod = -a.to_prod := rfl
@[simp] lemma sub_to_prod (a b : 𝓜(𝕜, A)) : (a - b).to_prod = a.to_prod - b.to_prod := rfl
@[simp] lemma one_to_prod : (1 : 𝓜(𝕜, A)).to_prod = 1 := rfl
@[simp] lemma nat_cast_to_prod (n : ℕ) : (n : 𝓜(𝕜 , A)).to_prod = n := rfl
@[simp] lemma int_cast_to_prod (n : ℤ) : (n : 𝓜(𝕜 , A)).to_prod = n := rfl
@[simp] lemma pow_to_prod (n : ℕ) (a : 𝓜(𝕜, A)) : (a ^ n).to_prod = a.to_prod ^ n := rfl

lemma add_fst (a b : 𝓜(𝕜, A)) : (a + b).fst = a.fst + b.fst := rfl
lemma add_snd (a b : 𝓜(𝕜, A)) : (a + b).snd = a.snd + b.snd := rfl
lemma zero_fst : (0 : 𝓜(𝕜, A)).fst = 0 := rfl
lemma zero_snd : (0 : 𝓜(𝕜, A)).snd = 0 := rfl
lemma neg_fst (a : 𝓜(𝕜, A)) : (-a).fst = -a.fst := rfl
lemma neg_snd (a : 𝓜(𝕜, A)) : (-a).snd = -a.snd := rfl
lemma sub_fst (a b : 𝓜(𝕜, A)) : (a - b).fst = a.fst - b.fst := rfl
lemma sub_snd (a b : 𝓜(𝕜, A)) : (a - b).snd = a.snd - b.snd := rfl
lemma one_fst : (1 : 𝓜(𝕜, A)).fst = 1 := rfl
lemma one_snd : (1 : 𝓜(𝕜, A)).snd = 1 := rfl
@[simp] lemma mul_fst (a b : 𝓜(𝕜, A)) : (a * b).fst = a.fst * b.fst := rfl
@[simp] lemma mul_snd (a b : 𝓜(𝕜, A)) : (a * b).snd = b.snd * a.snd := rfl
lemma nat_cast_fst (n : ℕ) : (n : 𝓜(𝕜 , A)).fst = n := rfl
lemma nat_cast_snd (n : ℕ) : (n : 𝓜(𝕜 , A)).snd = n := rfl
lemma int_cast_fst (n : ℤ) : (n : 𝓜(𝕜 , A)).fst = n := rfl
lemma int_cast_snd (n : ℤ) : (n : 𝓜(𝕜 , A)).snd = n := rfl
lemma pow_fst (n : ℕ) (a : 𝓜(𝕜, A)) : (a ^ n).fst = a.fst ^ n := rfl
lemma pow_snd (n : ℕ) (a : 𝓜(𝕜, A)) : (a ^ n).snd = a.snd ^ n := rfl

/-- The natural injection from `double_centralizer.to_prod` except the second coordinate inherits
`mul_opposite.op`. The ring structure on `𝓜(𝕜, A)` is the pullback under this map. -/
def to_prod_mul_opposite : 𝓜(𝕜, A) → (A →L[𝕜] A) × (A →L[𝕜] A)ᵐᵒᵖ :=
λ a, (a.fst, mul_opposite.op a.snd)

lemma to_prod_mul_opposite_injective :
  function.injective (to_prod_mul_opposite : 𝓜(𝕜, A) → (A →L[𝕜] A) × (A →L[𝕜] A)ᵐᵒᵖ) :=
λ a b h, let h' := prod.ext_iff.mp h in ext _ _ $ prod.ext h'.1 $ mul_opposite.op_injective h'.2

lemma range_to_prod_mul_opposite :
  set.range to_prod_mul_opposite = {lr : (A →L[𝕜] A) × _ | ∀ x y, unop lr.2 x * y = x * lr.1 y} :=
set.ext $ λ x,
  ⟨by {rintro ⟨a, rfl⟩, exact a.central}, λ hx, ⟨⟨(x.1, unop x.2), hx⟩, prod.ext rfl rfl⟩⟩

/-- The ring structure is inherited as the pullback under the injective map
`double_centralizer.to_prod_mul_opposite : 𝓜(𝕜, A) → (A →L[𝕜] A) × (A →L[𝕜] A)ᵐᵒᵖ` -/
instance : ring 𝓜(𝕜, A) :=
to_prod_mul_opposite_injective.ring _
  rfl rfl (λ _ _, rfl) (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl)
  (λ x n, prod.ext rfl $ mul_opposite.op_smul _ _)
  (λ x n, prod.ext rfl $ mul_opposite.op_smul _ _)
  (λ x n, prod.ext rfl $ mul_opposite.op_pow _ _)
  (λ _, rfl) (λ _, rfl)

/-- The canonical map `double_centralizer.to_prod` as an additive group homomorphism. -/
@[simps]
def to_prod_hom : 𝓜(𝕜, A) →+ (A →L[𝕜] A) × (A →L[𝕜] A) :=
{ to_fun := to_prod,
  map_zero' := rfl,
  map_add' := λ x y, rfl }

/-- The canonical map `double_centralizer.to_prod_mul_opposite` as a ring homomorphism. -/
@[simps]
def to_prod_mul_opposite_hom : 𝓜(𝕜, A) →+* (A →L[𝕜] A) × (A →L[𝕜] A)ᵐᵒᵖ :=
{ to_fun := to_prod_mul_opposite,
  map_zero' := rfl,
  map_one' := rfl,
  map_add' := λ x y, rfl,
  map_mul' := λ x y, rfl }

/-- The module structure is inherited as the pullback under the additive group monomorphism
`double_centralizer.to_prod : 𝓜(𝕜, A) →+ (A →L[𝕜] A) × (A →L[𝕜] A)` -/
instance {S : Type*} [semiring S] [module S A] [smul_comm_class 𝕜 S A]
  [has_continuous_const_smul S A] [is_scalar_tower S A A] [smul_comm_class S A A] :
  module S 𝓜(𝕜, A) :=
function.injective.module S to_prod_hom ext (λ x y, rfl)

-- TODO: generalize to `algebra S 𝓜(𝕜, A)` once `continuous_linear_map.algebra` is generalized.
instance : algebra 𝕜 𝓜(𝕜, A) :=
{ to_fun := λ k,
  { to_prod := algebra_map 𝕜 ((A →L[𝕜] A) × (A →L[𝕜] A)) k,
    central := λ x y, by simp_rw [prod.algebra_map_apply, algebra.algebra_map_eq_smul_one,
      smul_apply, one_apply, mul_smul_comm, smul_mul_assoc] },
  map_one' := ext _ _ $ map_one $ algebra_map 𝕜 ((A →L[𝕜] A) × (A →L[𝕜] A)),
  map_mul' := λ k₁ k₂, ext _ _ $ prod.ext (map_mul (algebra_map 𝕜 (A →L[𝕜] A)) _ _)
    ((map_mul (algebra_map 𝕜 (A →L[𝕜] A)) _ _).trans (algebra.commutes _ _)),
  map_zero' := ext _ _ $ map_zero $ algebra_map 𝕜 ((A →L[𝕜] A) × (A →L[𝕜] A)),
  map_add' := λ _ _, ext _ _ $ map_add (algebra_map 𝕜 ((A →L[𝕜] A) × (A →L[𝕜] A))) _ _,
  commutes' := λ _ _, ext _ _ $ prod.ext (algebra.commutes _ _) (algebra.commutes _ _).symm,
  smul_def' := λ _ _, ext _ _ $ prod.ext (algebra.smul_def _ _)
    ((algebra.smul_def _ _).trans $ algebra.commutes _ _) }

@[simp] lemma algebra_map_to_prod (k : 𝕜) :
  (algebra_map 𝕜 𝓜(𝕜, A) k).to_prod = algebra_map 𝕜 _ k := rfl
lemma algebra_map_fst (k : 𝕜) : (algebra_map 𝕜 𝓜(𝕜, A) k).fst = algebra_map 𝕜 _ k := rfl
lemma algebra_map_snd (k : 𝕜) : (algebra_map 𝕜 𝓜(𝕜, A) k).snd = algebra_map 𝕜 _ k := rfl

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

/-- The natural coercion of `A` into `𝓜(𝕜, A)` given by sending `a : A` to the pair of linear
maps `Lₐ Rₐ : A →L[𝕜] A` given by left- and right-multiplication by `a`, respectively.

Warning: if `A = 𝕜`, then this is a coercion which is not definitionally equal to the
`algebra_map 𝕜 𝓜(𝕜, 𝕜)` coercion, but these are propositionally equal. See
`double_centralizer.coe_eq_algebra_map` below. -/
noncomputable instance : has_coe_t A 𝓜(𝕜, A) :=
{ coe := λ a,
  { fst := continuous_linear_map.mul 𝕜 A a,
    snd := (continuous_linear_map.mul 𝕜 A).flip a,
    central := λ x y, mul_assoc _ _ _ } }

@[simp, norm_cast]
lemma coe_fst (a : A) : (a : 𝓜(𝕜, A)).fst = continuous_linear_map.mul 𝕜 A a := rfl
@[simp, norm_cast]
lemma coe_snd (a : A) : (a : 𝓜(𝕜, A)).snd = (continuous_linear_map.mul 𝕜 A).flip a := rfl

lemma coe_eq_algebra_map : (coe : 𝕜 → 𝓜(𝕜, 𝕜)) = algebra_map 𝕜 𝓜(𝕜, 𝕜) :=
begin
  ext;
  simp only [coe_fst, mul_apply', mul_one, algebra_map_to_prod, prod.algebra_map_apply, coe_snd,
    flip_apply, one_mul];
  simp only [algebra.algebra_map_eq_smul_one, smul_apply, one_apply, smul_eq_mul, mul_one],
end

/-- The coercion of an algebra into its multiplier algebra as a non-unital star algebra
homomorphism. -/
@[simps]
noncomputable def coe_hom [star_ring 𝕜] [star_ring A] [star_module 𝕜 A] [normed_star_group A] :
  A →⋆ₙₐ[𝕜] 𝓜(𝕜, A) :=
{ to_fun := λ a, a,
  map_smul' := λ k a, by ext; simp only [coe_fst, coe_snd, continuous_linear_map.map_smul,
    smul_fst, smul_snd],
  map_zero' := by ext; simp only [coe_fst, coe_snd, map_zero, zero_fst, zero_snd],
  map_add' := λ a b, by ext; simp only [coe_fst, coe_snd, map_add, add_fst, add_snd],
  map_mul' := λ a b, by ext; simp only [coe_fst, coe_snd, mul_apply', flip_apply, mul_fst, mul_snd,
    continuous_linear_map.coe_mul, function.comp_app, mul_assoc],
  map_star' := λ a, by ext; simp only [coe_fst, coe_snd, mul_apply', star_fst, star_snd,
    flip_apply, star_mul, star_star] }

/-!
### Norm structures
We define the norm structure on `𝓜(𝕜, A)` as the pullback under
`double_centralizer.to_prod_mul_opposite_hom : 𝓜(𝕜, A) →+* (A →L[𝕜] A) × (A →L[𝕜] A)ᵐᵒᵖ`, which
provides a definitional isometric embedding. Consequently, completeness of `𝓜(𝕜, A)` is obtained
by proving that the range of this map is closed.

In addition, we prove that `𝓜(𝕜, A)` is a normed algebra, and, when `A` is a C⋆-algebra, we show
that `𝓜(𝕜, A)` is also a C⋆-algebra. Moreover, in this case, for `a : 𝓜(𝕜, A)`,
`‖a‖ = ‖a.fst‖ = ‖a.snd‖`. -/

/-- The normed group structure is inherited as the pullback under the ring monomoprhism
`double_centralizer.to_prod_mul_opposite_hom : 𝓜(𝕜, A) →+* (A →L[𝕜] A) × (A →L[𝕜] A)ᵐᵒᵖ`. -/
noncomputable instance : normed_ring 𝓜(𝕜, A) :=
normed_ring.induced _ _ (to_prod_mul_opposite_hom : 𝓜(𝕜, A) →+* (A →L[𝕜] A) × (A →L[𝕜] A)ᵐᵒᵖ)
  to_prod_mul_opposite_injective

-- even though the definition is actually in terms of `double_centralizer.to_prod_mul_opposite`, we
-- choose to see through that here to avoid `mul_opposite.op` appearing.
lemma norm_def (a : 𝓜(𝕜, A)) : ‖a‖ = ‖a.to_prod_hom‖ := rfl
lemma nnnorm_def (a : 𝓜(𝕜, A)) : ‖a‖₊ = ‖a.to_prod_hom‖₊ := rfl

lemma norm_def' (a : 𝓜(𝕜, A)) : ‖a‖ = ‖a.to_prod_mul_opposite_hom‖ := rfl
lemma nnnorm_def' (a : 𝓜(𝕜, A)) : ‖a‖₊ = ‖a.to_prod_mul_opposite_hom‖₊ := rfl

instance : normed_space 𝕜 𝓜(𝕜, A) :=
{ norm_smul_le := λ k a, (norm_smul k a.to_prod_mul_opposite).le,
  .. double_centralizer.module }

instance : normed_algebra 𝕜 𝓜(𝕜, A) :=
{ ..double_centralizer.algebra, ..double_centralizer.normed_space }

lemma uniform_embedding_to_prod_mul_opposite :
  uniform_embedding (@to_prod_mul_opposite 𝕜 A _ _ _ _ _) :=
uniform_embedding_comap to_prod_mul_opposite_injective

instance [complete_space A] : complete_space 𝓜(𝕜, A) :=
begin
  rw complete_space_iff_is_complete_range
    uniform_embedding_to_prod_mul_opposite.to_uniform_inducing,
  apply is_closed.is_complete,
  simp only [range_to_prod_mul_opposite, set.set_of_forall],
  refine is_closed_Inter (λ x, is_closed_Inter $ λ y, is_closed_eq _ _),
  exact ((continuous_linear_map.apply 𝕜 A _).continuous.comp $
    continuous_unop.comp continuous_snd).mul continuous_const,
  exact continuous_const.mul ((continuous_linear_map.apply 𝕜 A _).continuous.comp continuous_fst),
end

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

lemma nnnorm_fst_eq_snd (a : 𝓜(𝕜, A)) : ‖a.fst‖₊ = ‖a.snd‖₊ := subtype.ext $ norm_fst_eq_snd a
@[simp] lemma norm_fst (a : 𝓜(𝕜, A)) : ‖a.fst‖ = ‖a‖ :=
  by simp only [norm_def, to_prod_hom_apply, prod.norm_def, norm_fst_eq_snd, max_eq_right,
    eq_self_iff_true]
@[simp] lemma norm_snd (a : 𝓜(𝕜, A)) : ‖a.snd‖ = ‖a‖ := by rw [←norm_fst, norm_fst_eq_snd]
@[simp] lemma nnnorm_fst (a : 𝓜(𝕜, A)) : ‖a.fst‖₊ = ‖a‖₊ := subtype.ext (norm_fst a)
@[simp] lemma nnnorm_snd (a : 𝓜(𝕜, A)) : ‖a.snd‖₊ = ‖a‖₊ := subtype.ext (norm_snd a)

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
    rw ←nnnorm_snd,
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
      simp_rw [←nnnorm_fst, ←Sup_closed_unit_ball_eq_nnnorm] at hr',
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
