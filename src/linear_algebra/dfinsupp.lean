/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau
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

variables {ι : Type*} {R : Type*} {S : Type*} {M : ι → Type*} {N : Type*}

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

See note [partially-applied ext lemmas].
After apply this lemma, if `M = R` then it suffices to verify `φ (single a 1) = ψ (single a 1)`. -/
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

section lsum

/-- Typeclass inference can't find `dfinsupp.add_comm_monoid` without help for this case.
This instance allows it to be found where it is needed on the LHS of the colon in
`dfinsupp.semimodule_of_linear_map`. -/
instance add_comm_monoid_of_linear_map : add_comm_monoid (Π₀ (i : ι), M i →ₗ[R] N) :=
@dfinsupp.add_comm_monoid _ (λ i, M i →ₗ[R] N) _

/-- Typeclass inference can't find `dfinsupp.semimodule` without help for this case.
This is needed to define `dfinsupp.lsum` below.

The cause seems to be an inability to unify the `Π i, add_comm_monoid (M i →ₗ[R] N)` instance that
we have with the `Π i, has_zero (M i →ₗ[R] N)` instance which appears as a parameter to the
`dfinsupp` type. -/
instance semimodule_of_linear_map [semiring S] [semimodule S N] [smul_comm_class R S N] :
  semimodule S (Π₀ (i : ι), M i →ₗ[R] N) :=
@dfinsupp.semimodule _ (λ i, M i →ₗ[R] N) _ _ _ _

variables (S)

include dec_ι

/-- The `dfinsupp` version of `finsupp.lsum`.

See note [bundled maps over different rings] for why separate `R` and `S` semirings are used. -/
@[simps apply symm_apply]
def lsum [semiring S] [semimodule S N] [smul_comm_class R S N] :
  (Π i, M i →ₗ[R] N) ≃ₗ[S] ((Π₀ i, M i) →ₗ[R] N) :=
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
  map_add' := λ F G, by { ext x y, simp },
  map_smul' := λ c F, by { ext, simp } }

end lsum

/-! ### Bundled versions of `dfinsupp.map_range`

The names should match the equivalent bundled `finsupp.map_range` definitions.
-/

section map_range

variables {β β₁ β₂: ι → Type*}
variables [Π i, add_comm_monoid (β i)] [Π i, add_comm_monoid (β₁ i)] [Π i, add_comm_monoid (β₂ i)]
variables [Π i, semimodule R (β i)] [Π i, semimodule R (β₁ i)] [Π i, semimodule R (β₂ i)]

lemma map_range_smul (f : Π i, β₁ i → β₂ i) (hf : ∀ i, f i 0 = 0)
  (hf' : ∀ i r x, f i (r • x) = r • f i y) (r : R) (g : Π₀ i, β₁ i):
  map_range f hf (r • g) = r • map_range f hf g :=
begin
  ext,
  simp only [map_range_apply f, coe_smul, pi.smul_apply, hf']
end

/-- `dfinsupp.map_range` as an `linear_map`. -/
@[simps apply]
def map_range.linear_map (f : Π i, β₁ i →ₗ[R] β₂ i) : (Π₀ i, β₁ i) →ₗ[R] (Π₀ i, β₂ i) :=
{ to_fun := map_range (λ i x, f i x) (λ i, (f i).map_zero),
  map_smul' := map_range_smul _ _ (λ i, (f i).map_smul),
  .. map_range.linear_map (λ i, (f i).to_add_monoid_hom) }

@[simp]
lemma map_range.linear_map_id :
  map_range.linear_map (λ i, linear_map.id (β₂ i)) = linear_map.id _ :=
linear_map.ext map_range_id

lemma map_range.linear_map_comp (f : Π i, β₁ i →ₗ[R] β₂ i) (f₂ : Π i, β i →ₗ[R] β₁ i):
  map_range.linear_map (λ i, (f i).comp (f₂ i)) =
    (map_range.linear_map f).comp (map_range.linear_map f₂) :=
linear_map.ext $ map_range_comp (λ i x, f i x) (λ i x, f₂ i x) _ _ _

/-- `dfinsupp.map_range.linear_map` as an `linear_equiv`. -/
@[simps apply]
def map_range.linear_equiv (e : Π i, β₁ i ≃ₗ[R] β₂ i) : (Π₀ i, β₁ i) ≃ₗ[R] (Π₀ i, β₂ i) :=
{ to_fun := map_range (λ i x, e i x) (λ i, (e i).map_zero),
  inv_fun := map_range (λ i x, (e i).symm x) (λ i, (e i).symm.map_zero),
  left_inv := λ x, by rw ←map_range_comp; { simp_rw linear_equiv.symm_comp_self, simp },
  right_inv := λ x, by rw ←map_range_comp; { simp_rw linear_equiv.self_comp_symm, simp },
  .. map_range.linear_map (λ i, (e i).to_linear_map) }

@[simp]
lemma map_range.linear_equiv_refl :
  (map_range.linear_equiv $ λ i, linear_equiv.refl (β₁ i)) = linear_equiv.refl _ :=
linear_equiv.ext map_range_id

lemma map_range.linear_equiv_trans (f : Π i, β i ≃ₗ[R] β₁ i) (f₂ : Π i, β₁ i ≃ₗ[R] β₂ i):
  map_range.linear_equiv (λ i, (f i).trans (f₂ i)) =
    (map_range.linear_equiv f).trans (map_range.linear_equiv f₂) :=
linear_equiv.ext $ map_range_comp (λ i x, f₂ i x) (λ i x, f i x) _ _ _

@[simp]
lemma map_range.linear_equiv_symm (e : Π i, β₁ i ≃ₗ[R] β₂ i) :
  (map_range.linear_equiv e).symm = map_range.linear_equiv (λ i, (e i).symm) := rfl

end map_range

end dfinsupp
