/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.direct_sum.module
import algebra.lie.of_associative
import algebra.lie.submodule
import algebra.lie.basic

/-!
# Direct sums of Lie algebras and Lie modules

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Direct sums of Lie algebras and Lie modules carry natural algebra and module structures.

## Tags

lie algebra, lie module, direct sum
-/

universes u v w w₁

namespace direct_sum
open dfinsupp
open_locale direct_sum

variables {R : Type u} {ι : Type v} [comm_ring R]

section modules

/-! The direct sum of Lie modules over a fixed Lie algebra carries a natural Lie module
structure. -/

variables {L : Type w₁} {M : ι → Type w}
variables [lie_ring L] [lie_algebra R L]
variables [Π i, add_comm_group (M i)] [Π i, module R (M i)]
variables [Π i, lie_ring_module L (M i)] [Π i, lie_module R L (M i)]

instance : lie_ring_module L (⨁ i, M i) :=
{ bracket     := λ x m, m.map_range (λ i m', ⁅x, m'⁆) (λ i, lie_zero x),
  add_lie     := λ x y m, by { ext, simp only [map_range_apply, add_apply, add_lie], },
  lie_add     := λ x m n, by { ext, simp only [map_range_apply, add_apply, lie_add], },
  leibniz_lie := λ x y m, by { ext, simp only [map_range_apply, lie_lie, add_apply,
    sub_add_cancel], }, }

@[simp] lemma lie_module_bracket_apply (x : L) (m : ⨁ i, M i) (i : ι) :
  ⁅x, m⁆ i = ⁅x, m i⁆ := map_range_apply _ _ m i

instance : lie_module R L (⨁ i, M i) :=
{ smul_lie := λ t x m, by { ext i, simp only [smul_lie, lie_module_bracket_apply, smul_apply], },
  lie_smul := λ t x m, by { ext i, simp only [lie_smul, lie_module_bracket_apply, smul_apply], }, }

variables (R ι L M)

/-- The inclusion of each component into a direct sum as a morphism of Lie modules. -/
def lie_module_of [decidable_eq ι] (j : ι) : M j →ₗ⁅R,L⁆ ⨁ i, M i :=
{ map_lie' := λ x m,
    begin
      ext i, by_cases h : j = i,
      { rw ← h, simp, },
      { simp [lof, single_eq_of_ne h], },
    end,
  ..lof R ι M j }

/-- The projection map onto one component, as a morphism of Lie modules. -/
def lie_module_component (j : ι) : (⨁ i, M i) →ₗ⁅R,L⁆ M j :=
{ map_lie' := λ x m,
    by simp only [component, lapply_apply, lie_module_bracket_apply, linear_map.to_fun_eq_coe],
  ..component R ι M j }

end modules

section algebras

/-! The direct sum of Lie algebras carries a natural Lie algebra structure. -/

variables (L : ι → Type w)
variables [Π i, lie_ring (L i)] [Π i, lie_algebra R (L i)]

instance lie_ring : lie_ring (⨁ i, L i) :=
{ bracket     := zip_with (λ i, λ x y, ⁅x, y⁆) (λ i, lie_zero 0),
  add_lie     := λ x y z, by { ext, simp only [zip_with_apply, add_apply, add_lie], },
  lie_add     := λ x y z, by { ext, simp only [zip_with_apply, add_apply, lie_add], },
  lie_self    := λ x, by { ext, simp only [zip_with_apply, add_apply, lie_self, zero_apply], },
  leibniz_lie := λ x y z, by { ext, simp only [sub_apply,
    zip_with_apply, add_apply, zero_apply], apply leibniz_lie, },
  ..(infer_instance : add_comm_group _) }

@[simp] lemma bracket_apply (x y : ⨁ i, L i) (i : ι) :
  ⁅x, y⁆ i = ⁅x i, y i⁆ := zip_with_apply _ _ x y i

instance lie_algebra : lie_algebra R (⨁ i, L i) :=
{ lie_smul := λ c x y, by { ext, simp only [
    zip_with_apply, smul_apply, bracket_apply, lie_smul] },
  ..(infer_instance : module R _) }

variables (R ι L)

/-- The inclusion of each component into the direct sum as morphism of Lie algebras. -/
@[simps] def lie_algebra_of [decidable_eq ι] (j : ι) : L j →ₗ⁅R⁆ ⨁ i, L i :=
{ to_fun   := of L j,
  map_lie' := λ x y, by
  { ext i, by_cases h : j = i,
    { rw ← h, simp [of], },
    { simp [of, single_eq_of_ne h], }, },
  ..lof R ι L j, }

/-- The projection map onto one component, as a morphism of Lie algebras. -/
@[simps] def lie_algebra_component (j : ι) : (⨁ i, L i) →ₗ⁅R⁆ L j :=
{ to_fun   := component R ι L j,
  map_lie' := λ x y,
    by simp only [component, bracket_apply, lapply_apply, linear_map.to_fun_eq_coe],
  ..component R ι L j }

@[ext] lemma lie_algebra_ext {x y : ⨁ i, L i}
  (h : ∀ i, lie_algebra_component R ι L i x = lie_algebra_component R ι L i y) : x = y :=
dfinsupp.ext h

include R

lemma lie_of_of_ne [decidable_eq ι] {i j : ι} (hij : j ≠ i) (x : L i) (y : L j) :
  ⁅of L i x, of L j y⁆ = 0 :=
begin
  apply lie_algebra_ext R ι L, intros k,
  rw lie_hom.map_lie,
  simp only [component, of, lapply_apply, single_add_hom_apply, lie_algebra_component_apply,
    single_apply, zero_apply],
  by_cases hik : i = k,
  { simp only [dif_neg, not_false_iff, lie_zero, hik.symm, hij], },
  { simp only [dif_neg, not_false_iff, zero_lie, hik], },
end

lemma lie_of_of_eq [decidable_eq ι] {i j : ι} (hij : j = i) (x : L i) (y : L j) :
  ⁅of L i x, of L j y⁆ = of L i ⁅x, hij.rec_on y⁆ :=
begin
  have : of L j y = of L i (hij.rec_on y), { exact eq.drec (eq.refl _) hij, },
  rw [this, ← lie_algebra_of_apply R ι L i ⁅x, hij.rec_on y⁆, lie_hom.map_lie,
    lie_algebra_of_apply, lie_algebra_of_apply],
end

@[simp] lemma lie_of [decidable_eq ι] {i j : ι} (x : L i) (y : L j) :
  ⁅of L i x, of L j y⁆ =
  if hij : j = i then lie_algebra_of R ι L i ⁅x, hij.rec_on y⁆ else 0 :=
begin
  by_cases hij : j = i,
  { simp only [lie_of_of_eq R ι L hij x y, hij, dif_pos, not_false_iff, lie_algebra_of_apply], },
  { simp only [lie_of_of_ne R ι L hij x y, hij, dif_neg, not_false_iff], },
end

variables {R L ι}

/-- Given a family of Lie algebras `L i`, together with a family of morphisms of Lie algebras
`f i : L i →ₗ⁅R⁆ L'` into a fixed Lie algebra `L'`, we have a natural linear map:
`(⨁ i, L i) →ₗ[R] L'`. If in addition `⁅f i x, f j y⁆ = 0` for any `x ∈ L i` and `y ∈ L j` (`i ≠ j`)
then this map is a morphism of Lie algebras. -/
@[simps] def to_lie_algebra [decidable_eq ι] (L' : Type w₁) [lie_ring L'] [lie_algebra R L']
  (f : Π i, L i →ₗ⁅R⁆ L') (hf : ∀ (i j : ι), i ≠ j → ∀ (x : L i) (y : L j), ⁅f i x, f j y⁆ = 0) :
  (⨁ i, L i) →ₗ⁅R⁆ L' :=
{ to_fun   := to_module R ι L' (λ i, (f i : L i →ₗ[R] L')),
  map_lie' := λ x y,
    begin
      let f' := λ i, (f i : L i →ₗ[R] L'),
      /- The goal is linear in `y`. We can use this to reduce to the case that `y` has only one
        non-zero component. -/
      suffices : ∀ (i : ι) (y : L i), to_module R ι L' f' ⁅x, of L i y⁆ =
        ⁅to_module R ι L' f' x, to_module R ι L' f' (of L i y)⁆,
      { simp only [← lie_algebra.ad_apply R],
        rw [← linear_map.comp_apply, ← linear_map.comp_apply],
        congr, clear y, ext i y, exact this i y, },
      /- Similarly, we can reduce to the case that `x` has only one non-zero component. -/
      suffices : ∀ i j (y : L i) (x : L j), to_module R ι L' f' ⁅of L j x, of L i y⁆ =
        ⁅to_module R ι L' f' (of L j x), to_module R ι L' f' (of L i y)⁆,
      { intros i y,
        rw [← lie_skew x, ← lie_skew (to_module R ι L' f' x)],
        simp only [linear_map.map_neg, neg_inj, ← lie_algebra.ad_apply R],
        rw [← linear_map.comp_apply, ← linear_map.comp_apply],
        congr, clear x, ext j x, exact this j i x y, },
      /- Tidy up and use `lie_of`. -/
      intros i j y x,
      simp only [lie_of R, lie_algebra_of_apply, lie_hom.coe_to_linear_map, to_add_monoid_of,
        coe_to_module_eq_coe_to_add_monoid, linear_map.to_add_monoid_hom_coe],
      /- And finish with trivial case analysis. -/
      rcases eq_or_ne i j with h | h,
      { have h' : f j (h.rec_on y) = f i y, { exact eq.drec (eq.refl _) h, },
        simp only [h, h', lie_hom.coe_to_linear_map, dif_pos, lie_hom.map_lie, to_add_monoid_of,
          linear_map.to_add_monoid_hom_coe], },
      { simp only [h, hf j i h.symm x y, dif_neg, not_false_iff, add_monoid_hom.map_zero], },
    end,
.. to_module R ι L' (λ i, (f i : L i →ₗ[R] L')) }

end algebras

section ideals

variables {L : Type w} [lie_ring L] [lie_algebra R L] (I : ι → lie_ideal R L)

/-- The fact that this instance is necessary seems to be a bug in typeclass inference. See
[this Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/
Typeclass.20resolution.20under.20binders/near/245151099). -/
instance lie_ring_of_ideals : lie_ring (⨁ i, I i) := direct_sum.lie_ring (λ i, ↥(I i))

/-- See `direct_sum.lie_ring_of_ideals` comment. -/
instance lie_algebra_of_ideals : lie_algebra R (⨁ i, I i) := direct_sum.lie_algebra (λ i, ↥(I i))

end ideals

end direct_sum
