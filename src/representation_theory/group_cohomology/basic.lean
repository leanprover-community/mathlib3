/-
Copyright (c) 2023 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/

import algebra.homology.opposite
import representation_theory.group_cohomology.resolution

/-!
# The group cohomology of a `k`-linear `G`-representation

This file defines group cohomology of `A : Rep k G` to be the cohomology of the complex
`0 → Fun(G⁰, A) → Fun(G¹, A) → Fun(G², A) → ...`, with differential `dⁿ` sending `f: Gⁿ → A` to
the function sending `(g₀, ..., gₙ) ↦ A.ρ(g₀)(f(g₁, ..., gₙ))`
`+ ∑ (-1)^(i + 1)⬝f(g₀, ..., gᵢgᵢ₊₁, ..., gₙ) + (-1)ⁿ⁺¹⬝f(g₀, ..., gₙ₋₁)` (where the sum ranges from
`i = 0` to `i = n - 1`).

We have `Fun(Gⁿ, A) ≅ Hom(k[Gⁿ⁺¹], A)` as `k`-modules, where the representation on `k[Gⁿ⁺¹]` is
induced by the diagonal action of `G`. Thus we show that our differential agrees with the
differential induced by this isomorphism and the differential in `Hom(P, A)`, where `P` is the
standard resolution of `k` as a trivial `k`-linear `G`-representation.

This gives us for free a proof that our `dⁿ` squares to zero. It also gives us an isomorphism
`Hⁿ(G, A) ≅ Extⁿ(k, A).`

## Main definitions

* `group_cohomology.linear_yoneda_obj_resolution`
* `group_cohomology.inhomogeneous_cochains`
* `group_cohomology`
* `group_cohomology_iso_Ext`

## Implementation notes

Group cohomology is typically stated for `G`-modules, or equivalently modules over the group ring
`ℤ[G].` However, `ℤ` can be generalized to any commutative ring `k`, which is what we use.
Moreover, we express `k[G]`-module structures on a module `k`-module `A` using the `Rep`
definition. We avoid using instances `module (monoid_algebra k G) A` so that we do not run into
possible scalar action diamonds.
-/

noncomputable theory
universes u

variables {k G : Type u} [comm_ring k] {n : ℕ}

open category_theory
namespace group_cohomology
variables [monoid G]

/-- The complex `Hom(P, A)`, where `P` is the standard resolution of `k` as a trivial `k`-linear
`G`-representation. -/
abbreviation linear_yoneda_obj_resolution (A : Rep k G) : cochain_complex (Module.{u} k) ℕ :=
homological_complex.unop
  ((((linear_yoneda k (Rep k G)).obj A).right_op.map_homological_complex _).obj (resolution k G))

lemma linear_yoneda_obj_resolution_d_apply {A : Rep k G} (i j : ℕ) (x : (resolution k G).X i ⟶ A) :
  (linear_yoneda_obj_resolution A).d i j x = (resolution k G).d j i ≫ x :=
rfl

end group_cohomology
namespace inhomogeneous_cochains
open Rep group_cohomology

/-- The differential in the complex of inhomogeneous cochains used to
calculate group cohomology. -/
@[simps] def d [monoid G] (n : ℕ) (A : Rep k G) :
  ((fin n → G) → A) →ₗ[k] (fin (n + 1) → G) → A :=
{ to_fun := λ f g, A.ρ (g 0) (f (λ i, g (fin.add_nat 1 i)))
    + (finset.range (n + 1)).sum (λ j, (-1 : k) ^ (j + 1) • f (fin.mul_nth j g)),
  map_add' := λ f g,
  begin
    ext x,
    simp only [pi.add_apply, map_add, smul_add, finset.sum_add_distrib, add_add_add_comm],
  end,
  map_smul' := λ r f,
  begin
    ext x,
    simp only [pi.smul_apply, ring_hom.id_apply, map_smul, smul_add, finset.smul_sum,
      ←smul_assoc, smul_eq_mul, mul_comm r],
  end }

variables [group G] (n) (A : Rep k G)

lemma d_eq :
  d n A = ((diagonal_hom_equiv n A).to_Module_iso.inv
    ≫ (linear_yoneda_obj_resolution A).d n (n + 1)
    ≫ (diagonal_hom_equiv (n + 1) A).to_Module_iso.hom) :=
begin
  ext f g,
  simp only [Module.coe_comp, linear_equiv.coe_coe, function.comp_app,
    linear_equiv.to_Module_iso_inv, linear_yoneda_obj_resolution_d_apply,
    linear_equiv.to_Module_iso_hom, diagonal_hom_equiv_apply, Action.comp_hom],
  rw [resolution.d_eq, resolution.d_of, linear_map.map_sum],
  simp only [←finsupp.smul_single_one _ ((-1 : k) ^ _), map_smul, d_apply],
  rw [fin.sum_univ_succ, fin.coe_zero, pow_zero, one_smul, fin.succ_above_zero,
    diagonal_hom_equiv_symm_apply],
  simp only [function.comp_app, fin.succ_above_zero, fin.partial_prod_succ,
    fin.cast_succ_zero, fin.partial_prod_zero, one_mul],
  congr' 1,
  { congr,
    ext,
    have := fin.partial_prod_right_inv (1 : G) g (fin.cast_succ x),
    simp only [fin.add_nat_one, mul_inv_rev, fin.coe_eq_cast_succ, one_smul,
      fin.cast_succ_fin_succ] at *,
    rw [mul_assoc, ←mul_assoc _ _ (g x.succ), this, inv_mul_cancel_left] },
  { refine @finset.sum_bij _ ℕ (fin (n + 1)) _ (finset.range (n + 1)) finset.univ
      _ _ (λ a ha, a) (λ a ha, finset.mem_univ _) (λ a ha, _) (λ a b ha hb hab,
      by rw [←fin.coe_coe_of_lt (finset.mem_range.1 ha), ←fin.coe_coe_of_lt
      (finset.mem_range.1 hb)]; congr' 1) (λ a ha, ⟨(a : ℕ), finset.mem_range.2 a.2,
      by ext; simp only [fin.coe_coe_eq_self]⟩),
    rw [diagonal_hom_equiv_symm_partial_prod_succ, fin.coe_succ,
      fin.coe_coe_of_lt (finset.mem_range.1 ha)] }
end

end inhomogeneous_cochains
namespace group_cohomology
variables [group G] (n) (A : Rep k G)

open inhomogeneous_cochains

/-- Given a `k`-linear `G`-representation `A`, this is the complex of inhomogeneous cochains
which calculates the group cohomology of `A`. -/
noncomputable def inhomogeneous_cochains : cochain_complex (Module k) ℕ :=
cochain_complex.of (λ n, Module.of k ((fin n → G) → A))
(λ n, inhomogeneous_cochains.d n A) (λ n,
begin
  ext x y,
  simp only [Module.coe_comp, function.comp_app, linear_map.zero_apply, pi.zero_apply,
    d_eq, linear_equiv.to_Module_iso_hom, linear_equiv.to_Module_iso_inv,
    linear_equiv.coe_coe, linear_equiv.symm_apply_apply],
  have := linear_map.ext_iff.1 ((linear_yoneda_obj_resolution A).d_comp_d n (n + 1) (n + 2)),
  simp only [Module.coe_comp, function.comp_app] at this,
  simp only [this, linear_map.zero_apply, map_zero, pi.zero_apply],
end)

@[simp] lemma inhomogeneous_cochains.d_def (n : ℕ) :
  (inhomogeneous_cochains A).d n (n + 1) = inhomogeneous_cochains.d n A :=
cochain_complex.of_d _ _ _ _

/-- Given a `k`-linear `G`-representation `A`, the complex of inhomogeneous cochains is isomorphic
to `Hom(P, A)`, where `P` is the standard resolution of `k` as a trivial `G`-representation. -/
def inhomogeneous_cochains_iso :
  inhomogeneous_cochains A ≅ linear_yoneda_obj_resolution A :=
homological_complex.hom.iso_of_components
  (λ i, (Rep.diagonal_hom_equiv i A).to_Module_iso.symm) $
begin
  rintros i j ⟨rfl⟩,
  dsimp [inhomogeneous_cochains],
  erw cochain_complex.of_d,
  simp only [d_eq, category.assoc],
  erw [iso.hom_inv_id, category.comp_id],
  refl,
end

end group_cohomology
open group_cohomology

/-- The group cohomology of a `k`-linear `G`-representation `A`, as the cohomology of its complex
of inhomogeneous cochains. -/
def group_cohomology [group G] (A : Rep k G) (n : ℕ) := (inhomogeneous_cochains A).homology n

/-- The `n`th group cohomology of a `k`-linear `G`-representation `A` is isomorphic to
`Extⁿ(k, A)`, where `k` is a trivial `k`-linear `G`-representation. -/
def group_cohomology_iso_Ext [group G] (A : Rep k G) (n : ℕ) :
  group_cohomology A n ≅ ((Ext k (Rep k G) n).obj
    (opposite.op $ Rep.of representation.trivial)).obj A :=
(homology_obj_iso_of_homotopy_equiv (homotopy_equiv.of_iso (inhomogeneous_cochains_iso _)) _)
  ≪≫ (homological_complex.homology_unop _ _) ≪≫ (Ext_iso k G A n).symm
