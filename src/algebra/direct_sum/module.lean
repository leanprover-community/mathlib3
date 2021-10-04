/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import algebra.direct_sum.basic
import linear_algebra.dfinsupp

/-!
# Direct sum of modules over commutative rings, indexed by a discrete type.

This file provides constructors for finite direct sums of modules.
It provides a construction of the direct sum using the universal property and proves
its uniqueness.

## Implementation notes

All of this file assumes that
* `R` is a commutative ring,
* `ι` is a discrete type,
* `S` is a finite set in `ι`,
* `M` is a family of `R` modules indexed over `ι`.
-/

universes u v w u₁

variables (R : Type u) [semiring R]
variables (ι : Type v) [dec_ι : decidable_eq ι] (M : ι → Type w)
variables [Π i, add_comm_monoid (M i)] [Π i, module R (M i)]
include R

namespace direct_sum
open_locale direct_sum

variables {R ι M}

instance : module R (⨁ i, M i) := dfinsupp.module
instance {S : Type*} [semiring S] [Π i, module S (M i)] [Π i, smul_comm_class R S (M i)] :
  smul_comm_class R S (⨁ i, M i) := dfinsupp.smul_comm_class
instance {S : Type*} [semiring S] [has_scalar R S] [Π i, module S (M i)]
  [Π i, is_scalar_tower R S (M i)] :
  is_scalar_tower R S (⨁ i, M i) := dfinsupp.is_scalar_tower

lemma smul_apply (b : R) (v : ⨁ i, M i) (i : ι) :
  (b • v) i = b • (v i) := dfinsupp.smul_apply _ _ _

include dec_ι

variables R ι M
/-- Create the direct sum given a family `M` of `R` modules indexed over `ι`. -/
def lmk : Π s : finset ι, (Π i : (↑s : set ι), M i.val) →ₗ[R] (⨁ i, M i) :=
dfinsupp.lmk

/-- Inclusion of each component into the direct sum. -/
def lof : Π i : ι, M i →ₗ[R] (⨁ i, M i) :=
dfinsupp.lsingle

lemma lof_eq_of (i : ι) (b : M i) : lof R ι M i b = of M i b := rfl

variables {ι M}

lemma single_eq_lof (i : ι) (b : M i) :
  dfinsupp.single i b = lof R ι M i b := rfl

/-- Scalar multiplication commutes with direct sums. -/
theorem mk_smul (s : finset ι) (c : R) (x) : mk M s (c • x) = c • mk M s x :=
(lmk R ι M s).map_smul c x

/-- Scalar multiplication commutes with the inclusion of each component into the direct sum. -/
theorem of_smul (i : ι) (c : R) (x) : of M i (c • x) = c • of M i x :=
(lof R ι M i).map_smul c x

variables {R}
lemma support_smul [Π (i : ι) (x : M i), decidable (x ≠ 0)]
  (c : R) (v : ⨁ i, M i) : (c • v).support ⊆ v.support := dfinsupp.support_smul _ _

variables {N : Type u₁} [add_comm_monoid N] [module R N]
variables (φ : Π i, M i →ₗ[R] N)

variables (R ι N φ)
/-- The linear map constructed using the universal property of the coproduct. -/
def to_module : (⨁ i, M i) →ₗ[R] N :=
dfinsupp.lsum ℕ φ

/-- Coproducts in the categories of modules and additive monoids commute with the forgetful functor
from modules to additive monoids. -/
lemma coe_to_module_eq_coe_to_add_monoid :
  (to_module R ι N φ : (⨁ i, M i) → N) = to_add_monoid (λ i, (φ i).to_add_monoid_hom) :=
rfl

variables {ι N φ}

/-- The map constructed using the universal property gives back the original maps when
restricted to each component. -/
@[simp] lemma to_module_lof (i) (x : M i) : to_module R ι N φ (lof R ι M i x) = φ i x :=
to_add_monoid_of (λ i, (φ i).to_add_monoid_hom) i x

variables (ψ : (⨁ i, M i) →ₗ[R] N)

/-- Every linear map from a direct sum agrees with the one obtained by applying
the universal property to each of its components. -/
theorem to_module.unique (f : ⨁ i, M i) : ψ f = to_module R ι N (λ i, ψ.comp $ lof R ι M i) f :=
to_add_monoid.unique ψ.to_add_monoid_hom f

variables {ψ} {ψ' : (⨁ i, M i) →ₗ[R] N}

/-- Two `linear_map`s out of a direct sum are equal if they agree on the generators.

See note [partially-applied ext lemmas]. -/
@[ext]
theorem linear_map_ext ⦃ψ ψ' : (⨁ i, M i) →ₗ[R] N⦄
  (H : ∀ i, ψ.comp (lof R ι M i) = ψ'.comp (lof R ι M i)) : ψ = ψ' :=
dfinsupp.lhom_ext' H

/--
The inclusion of a subset of the direct summands
into a larger subset of the direct summands, as a linear map.
-/
def lset_to_set (S T : set ι) (H : S ⊆ T) :
  (⨁ (i : S), M i) →ₗ[R] (⨁ (i : T), M i) :=
to_module R _ _ $ λ i, lof R T (λ (i : subtype T), M i) ⟨i, H i.prop⟩

omit dec_ι

/-- The natural linear equivalence between `⨁ _ : ι, M` and `M` when `unique ι`. -/
protected def lid (M : Type v) (ι : Type* := punit) [add_comm_monoid M] [module R M]
  [unique ι] :
  (⨁ (_ : ι), M) ≃ₗ[R] M :=
{ .. direct_sum.id M ι,
  .. to_module R ι M (λ i, linear_map.id) }

variables (ι M)
/-- The projection map onto one component, as a linear map. -/
def component (i : ι) : (⨁ i, M i) →ₗ[R] M i :=
dfinsupp.lapply i

variables {ι M}

lemma apply_eq_component (f : ⨁ i, M i) (i : ι) :
  f i = component R ι M i f := rfl

@[ext] lemma ext {f g : ⨁ i, M i}
  (h : ∀ i, component R ι M i f = component R ι M i g) : f = g :=
dfinsupp.ext h

lemma ext_iff {f g : ⨁ i, M i} : f = g ↔
  ∀ i, component R ι M i f = component R ι M i g :=
⟨λ h _, by rw h, ext R⟩

include dec_ι

@[simp] lemma lof_apply (i : ι) (b : M i) : ((lof R ι M i) b) i = b :=
dfinsupp.single_eq_same

@[simp] lemma component.lof_self (i : ι) (b : M i) :
  component R ι M i ((lof R ι M i) b) = b :=
lof_apply R i b

lemma component.of (i j : ι) (b : M j) :
  component R ι M i ((lof R ι M j) b) =
  if h : j = i then eq.rec_on h b else 0 :=
dfinsupp.single_apply

/-- The `direct_sum` formed by a collection of `submodule`s of `M` is said to be internal if the
canonical map `(⨁ i, A i) →ₗ[R] M` is bijective.

For the alternate statement in terms of independence and spanning, see
`direct_sum.submodule_is_internal_iff_independent_and_supr_eq_top`. -/
def submodule_is_internal {R M : Type*}
  [semiring R] [add_comm_monoid M] [module R M]
  (A : ι → submodule R M) : Prop :=
function.bijective (to_module R ι M (λ i, (A i).subtype))

lemma submodule_is_internal.to_add_submonoid {R M : Type*}
  [semiring R] [add_comm_monoid M] [module R M] (A : ι → submodule R M) :
  submodule_is_internal A ↔ add_submonoid_is_internal (λ i, (A i).to_add_submonoid) :=
iff.rfl

lemma submodule_is_internal.to_add_subgroup {R M : Type*}
  [ring R] [add_comm_group M] [module R M] (A : ι → submodule R M) :
  submodule_is_internal A ↔ add_subgroup_is_internal (λ i, (A i).to_add_subgroup) :=
iff.rfl

/-- If a direct sum of submodules is internal then the submodules span the module. -/
lemma submodule_is_internal.supr_eq_top {R M : Type*}
  [semiring R] [add_comm_monoid M] [module R M] {A : ι → submodule R M}
  (h : submodule_is_internal A) : supr A = ⊤ :=
begin
  rw [submodule.supr_eq_range_dfinsupp_lsum, linear_map.range_eq_top],
  exact function.bijective.surjective h,
end

/-- If a direct sum of submodules is internal then the submodules are independent. -/
lemma submodule_is_internal.independent {R M : Type*}
  [semiring R] [add_comm_monoid M] [module R M] {A : ι → submodule R M}
  (h : submodule_is_internal A) : complete_lattice.independent A :=
complete_lattice.independent_of_dfinsupp_lsum_injective _ h.injective

/-- Note that this is not generally true for `[semiring R]`; see
`complete_lattice.independent.dfinsupp_lsum_injective` for details. -/
lemma submodule_is_internal_of_independent_of_supr_eq_top {R M : Type*}
  [ring R] [add_comm_group M] [module R M] {A : ι → submodule R M}
  (hi : complete_lattice.independent A) (hs : supr A = ⊤) : submodule_is_internal A :=
⟨hi.dfinsupp_lsum_injective, linear_map.range_eq_top.1 $
  (submodule.supr_eq_range_dfinsupp_lsum _).symm.trans hs⟩

/-- `iff` version of `direct_sum.submodule_is_internal_of_independent_of_supr_eq_top`,
`direct_sum.submodule_is_internal.independent`, and `direct_sum.submodule_is_internal.supr_eq_top`.
-/
lemma submodule_is_internal_iff_independent_and_supr_eq_top {R M : Type*}
  [ring R] [add_comm_group M] [module R M] (A : ι → submodule R M) :
    submodule_is_internal A ↔ complete_lattice.independent A ∧ supr A = ⊤ :=
⟨λ i, ⟨i.independent, i.supr_eq_top⟩,
 and.rec submodule_is_internal_of_independent_of_supr_eq_top⟩

end direct_sum
