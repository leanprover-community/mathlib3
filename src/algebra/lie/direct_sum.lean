/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.lie.basic
import linear_algebra.direct_sum.finsupp

/-!
# Direct sums of Lie algebras and Lie modules

Direct sums of Lie algebras and Lie modules carry natural algbebra and module structures.

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

variables {L : ι → Type w}
variables [Π i, lie_ring (L i)] [Π i, lie_algebra R (L i)]

instance : lie_ring (⨁ i, L i) :=
{ bracket     := zip_with (λ i, λ x y, ⁅x, y⁆) (λ i, lie_zero 0),
  add_lie     := λ x y z, by { ext, simp only [zip_with_apply, add_apply, add_lie], },
  lie_add     := λ x y z, by { ext, simp only [zip_with_apply, add_apply, lie_add], },
  lie_self    := λ x, by { ext, simp only [zip_with_apply, add_apply, lie_self, zero_apply], },
  leibniz_lie := λ x y z, by { ext, simp only [sub_apply,
    zip_with_apply, add_apply, zero_apply], apply leibniz_lie, },
  ..(infer_instance : add_comm_group _) }

@[simp] lemma bracket_apply (x y : ⨁ i, L i) (i : ι) :
  ⁅x, y⁆ i = ⁅x i, y i⁆ := zip_with_apply _ _ x y i

instance : lie_algebra R (⨁ i, L i) :=
{ lie_smul := λ c x y, by { ext, simp only [
    zip_with_apply, smul_apply, bracket_apply, lie_smul] },
  ..(infer_instance : module R _) }

variables (R ι L)

/-- The inclusion of each component into the direct sum as morphism of Lie algebras. -/
def lie_algebra_of [decidable_eq ι] (j : ι) : L j →ₗ⁅R⁆ ⨁ i, L i :=
{ map_lie' := λ x y, by
  { ext i, by_cases h : j = i,
    { rw ← h, simp, },
    { simp [lof, single_eq_of_ne h], }, },
  ..lof R ι L j, }

/-- The projection map onto one component, as a morphism of Lie algebras. -/
def lie_algebra_component (j : ι) : (⨁ i, L i) →ₗ⁅R⁆ L j :=
{ map_lie' := λ x y,
    by simp only [component, bracket_apply, lapply_apply, linear_map.to_fun_eq_coe],
  ..component R ι L j }

end algebras

end direct_sum
