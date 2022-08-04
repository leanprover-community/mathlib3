/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import algebra.algebra.subalgebra.basic
import algebra.algebra.bilinear

/-!
# Towers of algebras

In this file we prove basic facts about towers of algebra.

An algebra tower A/S/R is expressed by having instances of `algebra A S`,
`algebra R S`, `algebra R A` and `is_scalar_tower R S A`, the later asserting the
compatibility condition `(r • s) • a = r • (s • a)`.

An important definition is `to_alg_hom R S A`, the canonical `R`-algebra homomorphism `S →ₐ[R] A`.

-/

open_locale pointwise
universes u v w u₁ v₁

variables (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

namespace algebra

variables [comm_semiring R] [semiring A] [algebra R A]
variables [add_comm_monoid M] [module R M] [module A M] [is_scalar_tower R A M]

variables {A}

/-- The `R`-algebra morphism `A → End (M)` corresponding to the representation of the algebra `A`
on the `R`-module `M`.

This is a stronger version of `distrib_mul_action.to_linear_map`, and could also have been
called `algebra.to_module_End`. -/
def lsmul : A →ₐ[R] module.End R M :=
{ to_fun := distrib_mul_action.to_linear_map R M,
  map_one' := linear_map.ext $ λ _, one_smul A _,
  map_mul' := λ a b, linear_map.ext $ smul_assoc a b,
  map_zero' := linear_map.ext $ λ _, zero_smul A _,
  map_add' := λ a b, linear_map.ext $ λ _, add_smul _ _ _,
  commutes' := λ r, linear_map.ext $ algebra_map_smul A r, }

@[simp] lemma lsmul_coe (a : A) : (lsmul R M a : M → M) = (•) a := rfl

lemma lmul_algebra_map (x : R) :
  algebra.lmul R A (algebra_map R A x) = algebra.lsmul R A x :=
eq.symm $ linear_map.ext $ smul_def x

end algebra

namespace is_scalar_tower

section module

variables [comm_semiring R] [semiring A] [algebra R A]
variables [has_smul R M] [mul_action A M] [is_scalar_tower R A M]

variables {R} (A) {M}
theorem algebra_map_smul (r : R) (x : M) : algebra_map R A r • x = r • x :=
by rw [algebra.algebra_map_eq_smul_one, smul_assoc, one_smul]

end module

section semiring
variables [comm_semiring R] [comm_semiring S] [semiring A] [semiring B]
variables [algebra R S] [algebra S A] [algebra S B]

variables {R S A}
theorem of_algebra_map_eq [algebra R A]
  (h : ∀ x, algebra_map R A x = algebra_map S A (algebra_map R S x)) :
  is_scalar_tower R S A :=
⟨λ x y z, by simp_rw [algebra.smul_def, ring_hom.map_mul, mul_assoc, h]⟩

/-- See note [partially-applied ext lemmas]. -/
theorem of_algebra_map_eq' [algebra R A]
  (h : algebra_map R A = (algebra_map S A).comp (algebra_map R S)) :
  is_scalar_tower R S A :=
of_algebra_map_eq $ ring_hom.ext_iff.1 h

variables (R S A)

instance subalgebra (S₀ : subalgebra R S) : is_scalar_tower S₀ S A :=
of_algebra_map_eq $ λ x, rfl

variables [algebra R A] [algebra R B]
variables [is_scalar_tower R S A] [is_scalar_tower R S B]

theorem algebra_map_eq :
  algebra_map R A = (algebra_map S A).comp (algebra_map R S) :=
ring_hom.ext $ λ x, by simp_rw [ring_hom.comp_apply, algebra.algebra_map_eq_smul_one,
    smul_assoc, one_smul]

theorem algebra_map_apply (x : R) : algebra_map R A x = algebra_map S A (algebra_map R S x) :=
by rw [algebra_map_eq R S A, ring_hom.comp_apply]

instance subalgebra' (S₀ : subalgebra R S) : is_scalar_tower R S₀ A :=
@is_scalar_tower.of_algebra_map_eq R S₀ A _ _ _ _ _ _ $ λ _,
(is_scalar_tower.algebra_map_apply R S A _ : _)

@[ext] lemma algebra.ext {S : Type u} {A : Type v} [comm_semiring S] [semiring A]
  (h1 h2 : algebra S A) (h : ∀ (r : S) (x : A), (by haveI := h1; exact r • x) = r • x) : h1 = h2 :=
algebra.algebra_ext _ _ $ λ r, by
  simpa only [@algebra.smul_def _ _ _ _ h1, @algebra.smul_def _ _ _ _ h2, mul_one] using h r 1

/-- In a tower, the canonical map from the middle element to the top element is an
algebra homomorphism over the bottom element. -/
def to_alg_hom : S →ₐ[R] A :=
{ commutes' := λ _, (algebra_map_apply _ _ _ _).symm,
  .. algebra_map S A }

lemma to_alg_hom_apply (y : S) : to_alg_hom R S A y = algebra_map S A y := rfl

@[simp] lemma coe_to_alg_hom : ↑(to_alg_hom R S A) = algebra_map S A :=
ring_hom.ext $ λ _, rfl

@[simp] lemma coe_to_alg_hom' : (to_alg_hom R S A : S → A) = algebra_map S A :=
rfl

variables {R S A B}

@[simp, priority 900] lemma _root_.alg_hom.map_algebra_map (f : A →ₐ[S] B) (r : R) :
  f (algebra_map R A r) = algebra_map R B r :=
by rw [algebra_map_apply R S A r, f.commutes, ← algebra_map_apply R S B]

variables (R)

@[simp, priority 900] lemma _root_.alg_hom.comp_algebra_map_of_tower (f : A →ₐ[S] B) :
  (f : A →+* B).comp (algebra_map R A) = algebra_map R B :=
ring_hom.ext f.map_algebra_map

variables (R) {S A B}

-- conflicts with is_scalar_tower.subalgebra
@[priority 999] instance subsemiring (U : subsemiring S) : is_scalar_tower U S A :=
of_algebra_map_eq $ λ x, rfl

@[nolint instance_priority]
instance of_ring_hom {R A B : Type*} [comm_semiring R] [comm_semiring A] [comm_semiring B]
  [algebra R A] [algebra R B] (f : A →ₐ[R] B) :
  @is_scalar_tower R A B _ (f.to_ring_hom.to_algebra.to_has_smul) _ :=
by { letI := (f : A →+* B).to_algebra, exact of_algebra_map_eq (λ x, (f.commutes x).symm) }

end semiring

end is_scalar_tower

section homs

variables [comm_semiring R] [comm_semiring S] [semiring A] [semiring B]
variables [algebra R S] [algebra S A] [algebra S B]
variables [algebra R A] [algebra R B]
variables [is_scalar_tower R S A] [is_scalar_tower R S B]

variables (R) {A S B}

open is_scalar_tower

namespace alg_hom

/-- R ⟶ S induces S-Alg ⥤ R-Alg -/
def restrict_scalars (f : A →ₐ[S] B) : A →ₐ[R] B :=
{ commutes' := λ r, by { rw [algebra_map_apply R S A, algebra_map_apply R S B],
    exact f.commutes (algebra_map R S r) },
  .. (f : A →+* B) }

lemma restrict_scalars_apply (f : A →ₐ[S] B) (x : A) : f.restrict_scalars R x = f x := rfl

@[simp] lemma coe_restrict_scalars (f : A →ₐ[S] B) : (f.restrict_scalars R : A →+* B) = f := rfl

@[simp] lemma coe_restrict_scalars' (f : A →ₐ[S] B) : (restrict_scalars R f : A → B) = f := rfl

lemma restrict_scalars_injective :
  function.injective (restrict_scalars R : (A →ₐ[S] B) → (A →ₐ[R] B)) :=
λ f g h, alg_hom.ext (alg_hom.congr_fun h : _)

end alg_hom

namespace alg_equiv

/-- R ⟶ S induces S-Alg ⥤ R-Alg -/
def restrict_scalars (f : A ≃ₐ[S] B) : A ≃ₐ[R] B :=
{ commutes' := λ r, by { rw [algebra_map_apply R S A, algebra_map_apply R S B],
    exact f.commutes (algebra_map R S r) },
  .. (f : A ≃+* B) }

lemma restrict_scalars_apply (f : A ≃ₐ[S] B) (x : A) : f.restrict_scalars R x = f x := rfl

@[simp] lemma coe_restrict_scalars (f : A ≃ₐ[S] B) : (f.restrict_scalars R : A ≃+* B) = f := rfl

@[simp] lemma coe_restrict_scalars' (f : A ≃ₐ[S] B) : (restrict_scalars R f : A → B) = f := rfl

lemma restrict_scalars_injective :
  function.injective (restrict_scalars R : (A ≃ₐ[S] B) → (A ≃ₐ[R] B)) :=
λ f g h, alg_equiv.ext (alg_equiv.congr_fun h : _)

end alg_equiv

end homs

namespace subalgebra

open is_scalar_tower

section semiring

variables (R) {S A B} [comm_semiring R] [comm_semiring S] [semiring A] [semiring B]
variables [algebra R S] [algebra S A] [algebra R A] [algebra S B] [algebra R B]
variables [is_scalar_tower R S A] [is_scalar_tower R S B]

/-- Given a tower `A / ↥U / S / R` of algebras, where `U` is an `S`-subalgebra of `A`, reinterpret
`U` as an `R`-subalgebra of `A`. -/
def restrict_scalars (U : subalgebra S A) : subalgebra R A :=
{ algebra_map_mem' := λ x, by { rw algebra_map_apply R S A, exact U.algebra_map_mem _ },
  .. U }

@[simp] lemma coe_restrict_scalars {U : subalgebra S A} :
  (restrict_scalars R U : set A) = (U : set A) := rfl

@[simp] lemma restrict_scalars_top : restrict_scalars R (⊤ : subalgebra S A) = ⊤ :=
set_like.coe_injective rfl

@[simp] lemma restrict_scalars_to_submodule {U : subalgebra S A} :
  (U.restrict_scalars R).to_submodule = U.to_submodule.restrict_scalars R :=
set_like.coe_injective rfl

@[simp] lemma mem_restrict_scalars {U : subalgebra S A} {x : A} :
  x ∈ restrict_scalars R U ↔ x ∈ U := iff.rfl

lemma restrict_scalars_injective :
  function.injective (restrict_scalars R : subalgebra S A → subalgebra R A) :=
λ U V H, ext $ λ x, by rw [← mem_restrict_scalars R, H, mem_restrict_scalars]

/-- Produces an `R`-algebra map from `U.restrict_scalars R` given an `S`-algebra map from `U`.

This is a special case of `alg_hom.restrict_scalars` that can be helpful in elaboration. -/
@[simp]
def of_restrict_scalars (U : subalgebra S A) (f : U →ₐ[S] B) : U.restrict_scalars R →ₐ[R] B :=
f.restrict_scalars R

end semiring

end subalgebra

namespace algebra

variables {R A} [comm_semiring R] [semiring A] [algebra R A]
variables {M} [add_comm_monoid M] [module A M] [module R M] [is_scalar_tower R A M]

lemma span_restrict_scalars_eq_span_of_surjective
  (h : function.surjective (algebra_map R A)) (s : set M) :
  (submodule.span A s).restrict_scalars R = submodule.span R s :=
begin
  refine le_antisymm (λ x hx, _) (submodule.span_subset_span _ _ _),
  refine submodule.span_induction hx _ _ _ _,
  { exact λ x hx, submodule.subset_span hx },
  { exact submodule.zero_mem _ },
  { exact λ x y, submodule.add_mem _ },
  { intros c x hx,
    obtain ⟨c', rfl⟩ := h c,
    rw is_scalar_tower.algebra_map_smul,
    exact submodule.smul_mem _ _ hx },
end

lemma coe_span_eq_span_of_surjective
  (h : function.surjective (algebra_map R A)) (s : set M) :
  (submodule.span A s : set M) = submodule.span R s :=
congr_arg coe (algebra.span_restrict_scalars_eq_span_of_surjective h s)

end algebra

namespace is_scalar_tower

open subalgebra

variables [comm_semiring R] [comm_semiring S] [comm_semiring A]
variables [algebra R S] [algebra S A] [algebra R A] [is_scalar_tower R S A]

theorem adjoin_range_to_alg_hom (t : set A) :
  (algebra.adjoin (to_alg_hom R S A).range t).restrict_scalars R =
    (algebra.adjoin S t).restrict_scalars R :=
subalgebra.ext $ λ z,
show z ∈ subsemiring.closure (set.range (algebra_map (to_alg_hom R S A).range A) ∪ t : set A) ↔
  z ∈ subsemiring.closure (set.range (algebra_map S A) ∪ t : set A),
from suffices set.range (algebra_map (to_alg_hom R S A).range A) = set.range (algebra_map S A),
  by rw this,
by { ext z, exact ⟨λ ⟨⟨x, y, h1⟩, h2⟩, ⟨y, h2 ▸ h1⟩, λ ⟨y, hy⟩, ⟨⟨z, y, hy⟩, rfl⟩⟩ }

end is_scalar_tower

section semiring

variables {R S A}

namespace submodule

section module

variables [semiring R] [semiring S] [add_comm_monoid A]
variables [module R S] [module S A] [module R A] [is_scalar_tower R S A]

open is_scalar_tower

theorem smul_mem_span_smul_of_mem {s : set S} {t : set A} {k : S} (hks : k ∈ span R s)
  {x : A} (hx : x ∈ t) : k • x ∈ span R (s • t) :=
span_induction hks (λ c hc, subset_span $ set.mem_smul.2 ⟨c, x, hc, hx, rfl⟩)
  (by { rw zero_smul, exact zero_mem _ })
  (λ c₁ c₂ ih₁ ih₂, by { rw add_smul, exact add_mem ih₁ ih₂ })
  (λ b c hc, by { rw is_scalar_tower.smul_assoc, exact smul_mem _ _ hc })

variables [smul_comm_class R S A]

theorem smul_mem_span_smul {s : set S} (hs : span R s = ⊤) {t : set A} {k : S}
  {x : A} (hx : x ∈ span R t) :
  k • x ∈ span R (s • t) :=
span_induction hx (λ x hx, smul_mem_span_smul_of_mem (hs.symm ▸ mem_top) hx)
  (by { rw smul_zero, exact zero_mem _ })
  (λ x y ihx ihy, by { rw smul_add, exact add_mem ihx ihy })
  (λ c x hx, smul_comm c k x ▸ smul_mem _ _ hx)

theorem smul_mem_span_smul' {s : set S} (hs : span R s = ⊤) {t : set A} {k : S}
  {x : A} (hx : x ∈ span R (s • t)) :
  k • x ∈ span R (s • t) :=
span_induction hx (λ x hx, let ⟨p, q, hp, hq, hpq⟩ := set.mem_smul.1 hx in
    by { rw [← hpq, smul_smul], exact smul_mem_span_smul_of_mem (hs.symm ▸ mem_top) hq })
  (by { rw smul_zero, exact zero_mem _ })
  (λ x y ihx ihy, by { rw smul_add, exact add_mem ihx ihy })
  (λ c x hx, smul_comm c k x ▸ smul_mem _ _ hx)

theorem span_smul {s : set S} (hs : span R s = ⊤) (t : set A) :
  span R (s • t) = (span S t).restrict_scalars R :=
le_antisymm (span_le.2 $ λ x hx, let ⟨p, q, hps, hqt, hpqx⟩ := set.mem_smul.1 hx in
  hpqx ▸ (span S t).smul_mem p (subset_span hqt)) $
λ p hp, span_induction hp (λ x hx, one_smul S x ▸ smul_mem_span_smul hs (subset_span hx))
  (zero_mem _)
  (λ _ _, add_mem)
  (λ k x hx, smul_mem_span_smul' hs hx)

end module

section algebra

variables [comm_semiring R] [semiring S] [add_comm_monoid A]
variables [algebra R S] [module S A] [module R A] [is_scalar_tower R S A]

/-- A variant of `submodule.span_image` for `algebra_map`. -/
lemma span_algebra_map_image (a : set R) :
  submodule.span R (algebra_map R S '' a) =
    (submodule.span R a).map (algebra.linear_map R S) :=
(submodule.span_image $ algebra.linear_map R S).trans rfl

lemma span_algebra_map_image_of_tower {S T : Type*} [comm_semiring S] [semiring T]
  [module R S] [is_scalar_tower R S S] [algebra R T] [algebra S T] [is_scalar_tower R S T]
  (a : set S) :
  submodule.span R (algebra_map S T '' a) =
    (submodule.span R a).map ((algebra.linear_map S T).restrict_scalars R) :=
(submodule.span_image $ (algebra.linear_map S T).restrict_scalars R).trans rfl

lemma map_mem_span_algebra_map_image {S T : Type*} [comm_semiring S] [semiring T]
  [algebra R S] [algebra R T] [algebra S T] [is_scalar_tower R S T]
  (x : S) (a : set S) (hx : x ∈ submodule.span R a) :
  algebra_map S T x ∈ submodule.span R (algebra_map S T '' a) :=
by { rw [span_algebra_map_image_of_tower, mem_map], exact ⟨x, hx, rfl⟩ }

end algebra

end submodule

end semiring

section ring

namespace algebra

variables [comm_semiring R] [semiring A] [algebra R A]
variables [add_comm_group M] [module A M] [module R M] [is_scalar_tower R A M]

lemma lsmul_injective [no_zero_smul_divisors A M] {x : A} (hx : x ≠ 0) :
  function.injective (lsmul R M x) :=
smul_right_injective _ hx

end algebra

end ring

namespace linear_map

variables {R₁ R₂ R₃ M₁ M₂ : Type*}
variables [semiring R₁] [comm_semiring R₂] [semiring R₃]
variables [add_comm_monoid M₁] [add_comm_monoid M₂]
variables [module R₁ M₁] [module R₂ M₂] [module R₃ M₂] [algebra R₂ R₃] [is_scalar_tower R₂ R₃ M₂]
variables {σ₁₂ : R₁ →+* R₂}

/--
A heterobasic version of `linear_map.cod_restrict`, restricting the codomain of a linear map.
-/
@[simps]
def cod_restrict_of_tower
  (p : submodule R₃ M₂) (f : M₁ →ₛₗ[σ₁₂] M₂) (h : ∀c, f c ∈ p) : M₁ →ₛₗ[σ₁₂] p :=
by refine {to_fun := λc, ⟨f c, h c⟩, ..}; intros; apply set_coe.ext; simp

end linear_map
