/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl, Kenny Lau
-/
import data.dfinsupp
import linear_algebra.basic

/-!
# Properties of the semimodule `Π₀ i, M i`

Given an indexed collection of `R`-semimodules `M i`, the `R`-semimodule structure on `Π₀ i, M i`
is defined in `data.dfinsupp`.

In this file we define `linear_map` versions of various maps:

* `dfinsupp.lsingle a : M →ₗ[R] Π₀ i, M i`: `dfinsupp.single a` as a linear map;

* `dfinsupp.lmk s : (Π i : (↑s : set ι), M i) →ₗ[R] Π₀ i, M i`: `dfinsupp.single a` as a linear map;

* `dfinsupp.lapply i : (Π₀ i, M i) →ₗ[R] M`: the map `λ f, f i` as a linear map;

* `dfinsupp.lsum`: `dfinsupp.sum` or `dfinsupp.lift_add_hom` as a `linear_map`;

## Implementation notes

This file should try to mirror `linear_algebra.finsupp` where possible. The API of `finsupp` is
much more developed, but many lemmas in that file should be eligible to copy over.

## Tags

function with finite support, semimodule, linear algebra
-/

variables {ι : Type*} {R : Type*} {M : ι → Type*} {N : Type*}

variables [dec_ι : decidable_eq ι]
variables [semiring R] [Π i, add_comm_monoid (M i)] [Π i, semimodule R (M i)]
variables [add_comm_monoid N] [semimodule R N]

namespace dfinsupp

include dec_ι

/-- `dfinsupp.mk` as a `linear_map`. -/
def lmk (s : finset ι) : (Π i : (↑s : set ι), M i) →ₗ[R] Π₀ i, M i :=
⟨mk s, λ _ _, mk_add, λ c x, by rw [mk_smul R x]⟩

/-- `dfinsupp.single` as a `linear_map` -/
def lsingle (i) : M i →ₗ[R] Π₀ i, M i :=
⟨single i, λ _ _, single_add, λ _ _, single_smul _⟩

/-- Two `R`-linear maps from `Π₀ i, M i` which agree on each `single i x` agree everywhere. -/
lemma lhom_ext ⦃φ ψ : (Π₀ i, M i) →ₗ[R] N⦄
  (h : ∀ i x, φ (single i x) = ψ (single i x)) :
  φ = ψ :=
linear_map.to_add_monoid_hom_injective $ add_hom_ext h

/-- Two `R`-linear maps from `Π₀ i, M i` which agree on each `single i x` agree everywhere.

We formulate this fact using equality of linear maps `φ.comp (lsingle a)` and `ψ.comp (lsingle a)`
so that the `ext` tactic can apply a type-specific extensionality lemma to prove equality of these
maps. E.g., if `M = R`, then it suffices to verify `φ (single a 1) = ψ (single a 1)`. -/
@[ext] lemma lhom_ext' ⦃φ ψ : (Π₀ i, M i) →ₗ[R] N⦄
  (h : ∀ i, φ.comp (lsingle i) = ψ.comp (lsingle i)) :
  φ = ψ :=
lhom_ext $ λ i, linear_map.congr_fun (h i)

omit dec_ι

/-- Interpret `λ (f : Π₀ i, M i), f i` as a linear map. -/
def lapply (i : ι) : (Π₀ i, M i) →ₗ[R] M i :=
{ to_fun := λ f, f i,
  map_add' := λ f g, add_apply f g i,
  map_smul' := λ c f, smul_apply c f i}

include dec_ι

@[simp] lemma lmk_apply (s : finset ι) (x) : (lmk s : _ →ₗ[R] Π₀ i, M i) x = mk s x := rfl

@[simp] lemma lsingle_apply (i : ι) (x : M i) : (lsingle i : _ →ₗ[R] _) x = single i x := rfl

omit dec_ι

@[simp] lemma lapply_apply (i : ι) (f : Π₀ i, M i) : (lapply i : _ →ₗ[R] _) f = f i := rfl

include dec_ι

/-- The `dfinsupp` version of `finsupp.lsum`. -/
@[simps apply symm_apply]
def lsum : (Π i, M i →ₗ[R] N) ≃+ ((Π₀ i, M i) →ₗ[R] N) :=
{ to_fun := λ F, {
    to_fun := sum_add_hom (λ i, (F i).to_add_monoid_hom),
    map_add' := (lift_add_hom (λ i, (F i).to_add_monoid_hom)).map_add,
    map_smul' := λ c f, by {
      apply dfinsupp.induction f,
      { rw [smul_zero, add_monoid_hom.map_zero, smul_zero] },
      { intros a b f ha hb hf,
        rw [smul_add, add_monoid_hom.map_add, add_monoid_hom.map_add, smul_add, hf, ←single_smul,
          sum_add_hom_single, sum_add_hom_single, linear_map.to_add_monoid_hom_coe,
          linear_map.map_smul], } } },
  inv_fun := λ F i, F.comp (lsingle i),
  left_inv := λ F, by { ext x y, simp },
  right_inv := λ F, by { ext x y, simp },
  map_add' := λ F G, by { ext x y, simp } }

end dfinsupp
