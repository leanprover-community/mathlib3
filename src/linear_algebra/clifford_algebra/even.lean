/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.clifford_algebra.fold
import linear_algebra.clifford_algebra.grading

/-!
# The universal property of the even subalgebra

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

* `clifford_algebra.even Q`: The even subalgebra of `clifford_algebra Q`.
* `clifford_algebra.even_hom`: The type of bilinear maps that satisfy the universal property of the
  even subalgebra
* `clifford_algebra.even.lift`: The universal property of the even subalgebra, which states
  that every bilinear map `f` with `f v v = Q v` and `f u v * f v w = Q v • f u w` is in unique
  correspondence with an algebra morphism from `clifford_algebra.even Q`.

## Implementation notes

The approach here is outlined in "Computing with the universal properties of the Clifford algebra
and the even subalgebra" (to appear).

The broad summary is that we have two tricks available to us for implementing complex recursors on
top of `clifford_algebra.lift`: the first is to use morphisms as the output type, such as
`A = module.End R N` which is how we obtained `clifford_algebra.foldr`; and the second is to use
`N = (N', S)` where `N'` is the value we wish to compute, and `S` is some auxiliary state passed
between one recursor invocation and the next.
For the universal property of the even subalgebra, we apply a variant of the first trick again by
choosing `S` to itself be a submodule of morphisms.
-/

namespace clifford_algebra

variables {R M : Type*} [comm_ring R] [add_comm_group M] [module R M]
variables {Q : quadratic_form R M}
-- put this after `Q` since we want to talk about morphisms from `clifford_algebra Q` to `A` and
-- that order is more natural
variables {A B : Type*} [ring A] [ring B] [algebra R A] [algebra R B]

open_locale direct_sum

variables (Q)

/-- The even submodule `clifford_algebra.even_odd Q 0` is also a subalgebra. -/
def even : subalgebra R (clifford_algebra Q) :=
(even_odd Q 0).to_subalgebra
  set_like.graded_monoid.one_mem
  (λ x y hx hy, add_zero (0 : zmod 2) ▸ set_like.graded_monoid.mul_mem hx hy)

@[simp] lemma even_to_submodule : (even Q).to_submodule = even_odd Q 0 :=
rfl

variables (A)

/-- The type of bilinear maps which are accepted by `clifford_algebra.even.lift`. -/
@[ext]
structure even_hom : Type (max u_2 u_3) :=
(bilin : M →ₗ[R] M →ₗ[R] A)
(contract (m : M) : bilin m m = algebra_map R A (Q m))
(contract_mid (m₁ m₂ m₃ : M) : bilin m₁ m₂ * bilin m₂ m₃ = Q m₂ • bilin m₁ m₃)

variables {A Q}

/-- Compose an `even_hom` with an `alg_hom` on the output. -/
@[simps]
def even_hom.compr₂ (g : even_hom Q A) (f : A →ₐ[R] B) : even_hom Q B :=
{ bilin := g.bilin.compr₂ f.to_linear_map,
  contract := λ m, (f.congr_arg $ g.contract _).trans $ f.commutes _,
  contract_mid := λ m₁ m₂ m₃, (f.map_mul _ _).symm.trans $
    (f.congr_arg $ g.contract_mid _ _ _).trans $ f.map_smul _ _ }

variables (Q)

/-- The embedding of pairs of vectors into the even subalgebra, as a bilinear map. -/
@[simps bilin_apply_apply_coe]
def even.ι : even_hom Q (even Q) :=
{ bilin := linear_map.mk₂ R (λ m₁ m₂, ⟨ι Q m₁ * ι Q m₂, ι_mul_ι_mem_even_odd_zero _ _ _⟩)
             (λ _ _ _, by { simp only [linear_map.map_add, add_mul], refl })
             (λ _ _ _, by { simp only [linear_map.map_smul, smul_mul_assoc], refl })
             (λ _ _ _, by { simp only [linear_map.map_add, mul_add], refl })
             (λ _ _ _, by { simp only [linear_map.map_smul, mul_smul_comm], refl }),
  contract := λ m, subtype.ext $ ι_sq_scalar Q m,
  contract_mid := λ m₁ m₂ m₃, subtype.ext $
    calc  ι Q m₁ * ι Q m₂ * (ι Q m₂ * ι Q m₃)
        = ι Q m₁ * ((ι Q m₂ * ι Q m₂) * ι Q m₃) : by simp only [mul_assoc]
    ... = Q m₂ • (ι Q m₁ * ι Q m₃) : by rw [algebra.smul_def, ι_sq_scalar, algebra.left_comm] }

instance : inhabited (even_hom Q (even Q)) := ⟨even.ι Q⟩

variables (f : even_hom Q A)

/-- Two algebra morphisms from the even subalgebra are equal if they agree on pairs of generators.

See note [partially-applied ext lemmas]. -/
@[ext]
lemma even.alg_hom_ext ⦃f g : even Q →ₐ[R] A⦄
  (h : (even.ι Q).compr₂ f = (even.ι Q).compr₂ g) :
  f = g :=
begin
  rw even_hom.ext_iff at h,
  ext ⟨x, hx⟩,
  refine even_induction _ _ _ _ _ hx,
  { intro r,
    exact (f.commutes r).trans (g.commutes r).symm },
  { intros x y hx hy ihx ihy,
    have := congr_arg2 (+) ihx ihy,
    exact (f.map_add _ _).trans (this.trans $ (g.map_add _ _).symm) },
  { intros m₁ m₂ x hx ih,
    have := congr_arg2 (*) (linear_map.congr_fun (linear_map.congr_fun h m₁) m₂) ih,
    exact (f.map_mul _ _).trans (this.trans $ (g.map_mul _ _).symm) },
end

variables {Q}

namespace even.lift

/-- An auxiliary submodule used to store the half-applied values of `f`.
This is the span of elements `f'` such that `∃ x m₂, ∀ m₁, f' m₁ = f m₁ m₂ * x`.  -/
private def S : submodule R (M →ₗ[R] A) :=
submodule.span R
  {f' | ∃ x m₂, f' = linear_map.lcomp R _ (f.bilin.flip m₂) (linear_map.mul_right R x)}

/-- An auxiliary bilinear map that is later passed into `clifford_algebra.fold`. Our desired result
is stored in the `A` part of the accumulator, while auxiliary recursion state is stored in the `S f`
part. -/
private def f_fold : M →ₗ[R] (A × S f) →ₗ[R] (A × S f) :=
linear_map.mk₂ R (λ m acc,
  /- We could write this `snd` term in a point-free style as follows, but it wouldn't help as we
  don't have any prod or subtype combinators to deal with n-linear maps of this degree.
  ```lean
  (linear_map.lcomp R _ (algebra.lmul R A).to_linear_map.flip).comp $
    (linear_map.llcomp R M A A).flip.comp f.flip : M →ₗ[R] A →ₗ[R] M →ₗ[R] A)
  ```
  -/
  (acc.2 m, ⟨(linear_map.mul_right R acc.1).comp (f.bilin.flip m),
    submodule.subset_span $ ⟨_, _, rfl⟩⟩))
  (λ m₁ m₂ a, prod.ext
    (linear_map.map_add _ m₁ m₂)
    (subtype.ext $ linear_map.ext $ λ m₃,
      show f.bilin m₃ (m₁ + m₂) * a.1 = f.bilin m₃ m₁ * a.1 + f.bilin m₃ m₂ * a.1,
      by rw [map_add, add_mul]))
  (λ c m a, prod.ext
    (linear_map.map_smul _ c m)
    (subtype.ext $ linear_map.ext $ λ m₃,
      show f.bilin m₃ (c • m) * a.1 = c • (f.bilin m₃ m * a.1),
      by rw [linear_map.map_smul, smul_mul_assoc]))
  (λ m a₁ a₂, prod.ext rfl (subtype.ext $ linear_map.ext $ λ m₃, mul_add _ _ _))
  (λ c m a, prod.ext rfl (subtype.ext $ linear_map.ext $ λ m₃, mul_smul_comm _ _ _))

@[simp] private lemma fst_f_fold_f_fold (m₁ m₂ : M) (x : A × S f) :
  (f_fold f m₁ (f_fold f m₂ x)).fst = f.bilin m₁ m₂ * x.fst := rfl

@[simp] private lemma snd_f_fold_f_fold (m₁ m₂ m₃ : M) (x : A × S f) :
  ((f_fold f m₁ (f_fold f m₂ x)).snd : M →ₗ[R] A) m₃ = f.bilin m₃ m₁ * (x.snd : M →ₗ[R] A) m₂ := rfl

private lemma f_fold_f_fold (m : M) (x : A × S f) :
  f_fold f m (f_fold f m x) = Q m • x :=
begin
  obtain ⟨a, ⟨g, hg⟩⟩ := x,
  ext : 2,
  { change f.bilin m m * a = Q m • a,
    rw [algebra.smul_def, f.contract] },
  { ext m₁,
    change f.bilin _ _ * g m = Q m • g m₁,
    apply submodule.span_induction' _ _ _ _ hg,
    { rintros _ ⟨b, m₃, rfl⟩,
      change f.bilin _ _ * (f.bilin _ _ * b) = Q m • (f.bilin _ _ * b),
      rw [←smul_mul_assoc, ←mul_assoc, f.contract_mid] },
    { change f.bilin m₁ m * 0 = Q m • 0,
      rw [mul_zero, smul_zero] },
    { rintros x hx y hy ihx ihy,
      rw [linear_map.add_apply, linear_map.add_apply, mul_add, smul_add, ihx, ihy] },
    { rintros x hx c ihx,
      rw [linear_map.smul_apply, linear_map.smul_apply, mul_smul_comm, ihx, smul_comm] } },
end

/-- The final auxiliary construction for `clifford_algebra.even.lift`. This map is the forwards
direction of that equivalence, but not in the fully-bundled form. -/
@[simps apply {attrs := []}] def aux (f : even_hom Q A) : clifford_algebra.even Q →ₗ[R] A :=
begin
  refine _ ∘ₗ (even Q).val.to_linear_map,
  exact linear_map.fst _ _ _ ∘ₗ foldr Q (f_fold f) (f_fold_f_fold f) (1, 0),
end

@[simp] lemma aux_one : aux f 1 = 1 :=
(congr_arg prod.fst (foldr_one _ _ _ _))

@[simp] lemma aux_ι (m₁ m₂ : M) : aux f ((even.ι Q).bilin m₁ m₂) = f.bilin m₁ m₂ :=
(congr_arg prod.fst (foldr_mul _ _ _ _ _ _)).trans begin
  rw [foldr_ι, foldr_ι],
  exact mul_one _,
end

@[simp] lemma aux_algebra_map (r) (hr) :
  aux f ⟨algebra_map R _ r, hr⟩ = algebra_map R _ r :=
(congr_arg prod.fst (foldr_algebra_map _ _ _ _ _)).trans (algebra.algebra_map_eq_smul_one r).symm

@[simp] lemma aux_mul (x y : even Q) :
  aux f (x * y) = aux f x * aux f y :=
begin
  cases x,
  cases y,
  refine (congr_arg prod.fst (foldr_mul _ _ _ _ _ _)).trans _,
  dsimp only,
  refine even_induction Q _ _ _ _ x_property,
  { intros r,
    rw [foldr_algebra_map, aux_algebra_map],
    exact (algebra.smul_def r _), },
  { intros x y hx hy ihx ihy,
    rw [linear_map.map_add, prod.fst_add, ihx, ihy, ←add_mul, ←linear_map.map_add],
    refl, },
  { rintros m₁ m₂ x (hx : x ∈ even Q) ih,
    rw [aux_apply, foldr_mul, foldr_mul, foldr_ι, foldr_ι, fst_f_fold_f_fold, ih,
      ←mul_assoc, subtype.coe_mk, foldr_mul, foldr_mul, foldr_ι, foldr_ι, fst_f_fold_f_fold],
      refl }
end

end even.lift

open even.lift

variables (Q) {A}

/-- Every algebra morphism from the even subalgebra is in one-to-one correspondence with a
bilinear map that sends duplicate arguments to the quadratic form, and contracts across
multiplication. -/
@[simps symm_apply_bilin]
def even.lift : even_hom Q A ≃ (clifford_algebra.even Q →ₐ[R] A) :=
{ to_fun := λ f, alg_hom.of_linear_map (aux f) (aux_one f) (aux_mul f),
  inv_fun := λ F, (even.ι Q).compr₂ F,
  left_inv := λ f, even_hom.ext _ _ $ linear_map.ext₂ $ even.lift.aux_ι f,
  right_inv := λ F, even.alg_hom_ext Q $ even_hom.ext _ _ $ linear_map.ext₂ $ even.lift.aux_ι _ }

@[simp] lemma even.lift_ι (f : even_hom Q A) (m₁ m₂ : M) :
  even.lift Q f ((even.ι Q).bilin m₁ m₂) = f.bilin m₁ m₂ :=
even.lift.aux_ι _ _ _

end clifford_algebra
