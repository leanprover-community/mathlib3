/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.direct_sum_graded
import linear_algebra.direct_sum_module

/-! # Additively-graded algebra structures on `⨁ i, A i`

## Main definitions

* `direct_sum.galgebra R A`, the typeclass
* `direct_sum.galgebra.of_submodules`, for creating the above instance from a collection of
  submodules.
* `direct_sum.to_algebra` extends `direct_sum.to_semiring` to produce an `alg_hom`.

-/

namespace direct_sum
open_locale direct_sum

universes uι uR uA uB

variables {ι : Type uι} (R : Type uR) (A : ι → Type uA) {B : Type uB} [decidable_eq ι]

variables [comm_semiring R] [Π i, add_comm_monoid (A i)] [Π i, module R (A i)]
variables [add_monoid ι] [gmonoid A]

section

local attribute [instance] ghas_one.to_sigma_has_one
local attribute [instance] ghas_mul.to_sigma_has_mul

/-- A graded version of `algebra`. An instance of `direct_sum.galgebra R A` endows `(⨁ i, A i)`
with an `R`-algebra structure. -/
class galgebra :=
(to_fun : R →+ A 0)
(map_one : to_fun 1 = ghas_one.one)
(map_mul : ∀ r s, (⟨_, to_fun (r * s)⟩ : Σ i, A i) = ⟨_, ghas_mul.mul (to_fun r) (to_fun s)⟩)
(commutes : ∀ r x, (⟨_, to_fun (r)⟩ : Σ i, A i) * x = x * ⟨_, to_fun (r)⟩)
(smul_def : ∀ r (x : Σ i, A i), (⟨x.1, r • x.2⟩ : Σ i, A i) = ⟨_, to_fun (r)⟩ * x)

end

variables [semiring B] [galgebra R A] [algebra R B]

instance : algebra R (⨁ i, A i) :=
{ to_fun := (direct_sum.of A 0).comp galgebra.to_fun,
  map_zero' := add_monoid_hom.map_zero _,
  map_add' := add_monoid_hom.map_add _,
  map_one' := (direct_sum.of A 0).congr_arg galgebra.map_one,
  map_mul' := λ a b, begin
    simp only [add_monoid_hom.comp_apply],
    rw of_mul_of,
    apply dfinsupp.single_eq_of_sigma_eq (galgebra.map_mul a b),
  end,
  commutes' := λ r x, begin
    change add_monoid_hom.mul (direct_sum.of _ _ _) x =
      add_monoid_hom.mul.flip (direct_sum.of _ _ _) x,
    apply add_monoid_hom.congr_fun _ x,
    ext i xi : 2,
    dsimp only [add_monoid_hom.comp_apply, add_monoid_hom.mul_apply, add_monoid_hom.flip_apply],
    rw direct_sum.of_mul_of,
    rw direct_sum.of_mul_of,
    apply dfinsupp.single_eq_of_sigma_eq (galgebra.commutes r ⟨i, xi⟩),
  end,
  smul_def' := λ r x, begin
    change const_smul_hom _ r x = add_monoid_hom.mul (direct_sum.of _ _ _) x,
    apply add_monoid_hom.congr_fun _ x,
    ext i xi : 2,
    dsimp only [add_monoid_hom.comp_apply, const_smul_hom_apply, add_monoid_hom.mul_apply],
    rw direct_sum.of_mul_of,
    rw ←direct_sum.of_smul,
    apply dfinsupp.single_eq_of_sigma_eq (galgebra.smul_def r ⟨i, xi⟩),
  end }

#check 1

/-- Build a `galgebra` instance for a collection of `submodule`s. -/
def galgebra.of_submodules
  (carriers : ι → submodule R B)
  (one_mem : (1 : B) ∈ carriers 0)
  (mul_mem : ∀ ⦃i j⦄ (gi : carriers i) (gj : carriers j), (gi * gj : B) ∈ carriers (i + j)) :
  by haveI : gmonoid (λ i, carriers i) := gmonoid.of_submodules carriers one_mem mul_mem; exact
  galgebra R (λ i, carriers i) :=
by exact {
  to_fun := begin
    refine ((algebra.linear_map R B).cod_restrict (carriers 0) $ λ r, _).to_add_monoid_hom,
    exact submodule.one_le.mpr one_mem (submodule.algebra_map_mem _),
  end,
  map_one := subtype.ext $ by exact (algebra_map R B).map_one,
  map_mul := λ x y, sigma.subtype_ext (add_zero 0).symm $ (algebra_map R B).map_mul _ _,
  commutes := λ r ⟨i, xi⟩, sigma.subtype_ext ((zero_add i).trans (add_zero i).symm) $ algebra.commutes _ _,
  smul_def := λ r ⟨i, xi⟩, sigma.subtype_ext (zero_add i).symm $ algebra.smul_def _ _ }

-- `@[simps]` doesn't generate this well
lemma galgebra.of_submodules_algebra_map
  (carriers : ι → submodule R B)
  (one_mem : (1 : B) ∈ carriers 0)
  (mul_mem : ∀ ⦃i j⦄ (gi : carriers i) (gj : carriers j), (gi * gj : B) ∈ carriers (i + j))
  (r : R) :
  by letI x : gmonoid (λ i, carriers i) := gmonoid.of_submodules carriers one_mem mul_mem;exact
  @galgebra.to_fun _ _ _ _ _ _ _ _ _ (galgebra.of_submodules R carriers one_mem mul_mem) r =
    ⟨algebra_map R B r, submodule.one_le.mpr one_mem (submodule.algebra_map_mem _) ⟩ := rfl

/-- A family of `linear_map`s preserving `direct_sum.ghas_one.one` and `direct_sum.ghas_mul.mul`
describes an `alg_hom` on `⨁ i, A i`. This is a stronger version of `direct_sum.to_semiring`.

Of particular interest is the case when `A i` are bundled subojects, `f` is the family of
coercions such as `submodule.subtype (A i)`, and the `[gmonoid A]` structure originates from
`direct_sum.gmonoid.of_add_submodules`, in which case the proofs about `ghas_one` and `ghas_mul`
can be discharged by `rfl`. -/
@[simps]
def to_algebra [galgebra R A] [semiring B] [algebra R B]
  (f : Π i, A i →ₗ[R] B) (hone : f _ (ghas_one.one) = 1)
  (hmul : ∀ {i j} (ai : A i) (aj : A j), f _ (ghas_mul.mul ai aj) = f _ ai * f _ aj)
  (hcommutes : ∀ r, (f 0) (galgebra.to_fun r) = (algebra_map R B) r) :
  (⨁ i, A i) →ₐ[R] B :=
{ to_fun := to_semiring (λ i, (f i).to_add_monoid_hom) hone (λ i j ai aj, hmul ai aj),
  commutes' := λ r, (direct_sum.to_semiring_of _ _ _ _ _).trans (hcommutes r),
  .. to_semiring (λ i, (f i).to_add_monoid_hom) hone (λ i j ai aj, hmul ai aj)}

end direct_sum
