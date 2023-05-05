/-
Copyright (c) 2023 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/

import algebra.homology.opposite
import representation_theory.group_cohomology.resolution

/-!
# The group cohomology of a `k`-linear `G`-representation

Let `k` be a commutative ring and `G` a group. This file defines the group cohomology of
`A : Rep k G` to be the cohomology of the complex
$$0 \to \mathrm{Fun}(G^0, A) \to \mathrm{Fun}(G^1, A) \to \mathrm{Fun}(G^2, A) \to \dots$$
with differential $d^n$ sending $f: G^n \to A$ to the function mapping $(g_0, \dots, g_n)$ to
$$\rho(g_0)(f(g_1, \dots, g_n))
+ \sum_{i = 0}^{n - 1} (-1)^{i + 1}\cdot f(g_0, \dots, g_ig_{i + 1}, \dots, g_n)$$
$$+ (-1)^{n + 1}\cdot f(g_0, \dots, g_{n - 1})$$ (where `ρ` is the representation attached to `A`).

We have a `k`-linear isomorphism $\mathrm{Fun}(G^n, A) \cong \mathrm{Hom}(k[G^{n + 1}], A)$, where
the righthand side is morphisms in `Rep k G`, and the representation on $k[G^{n + 1}]$
is induced by the diagonal action of `G`. If we conjugate the $n$th differential in
$\mathrm{Hom}(P, A)$ by this isomorphism, where `P` is the standard resolution of `k` as a trivial
`k`-linear `G`-representation, then the resulting map agrees with the differential $d^n$ defined
above, a fact we prove.

This gives us for free a proof that our $d^n$ squares to zero. It also gives us an isomorphism
$\mathrm{H}^n(G, A) \cong \mathrm{Ext}^n(k, A),$ where $\mathrm{Ext}$ is taken in the category
`Rep k G`.

## Main definitions

* `group_cohomology.linear_yoneda_obj_resolution A`: a complex whose objects are the representation
morphisms $\mathrm{Hom}(k[G^{n + 1}], A)$ and whose cohomology is the group cohomology
$\mathrm{H}^n(G, A)$.
* `group_cohomology.inhomogeneous_cochains A`: a complex whose objects are
$\mathrm{Fun}(G^n, A)$ and whose cohomology is the group cohomology $\mathrm{H}^n(G, A).$
* `group_cohomology.inhomogeneous_cochains_iso A`: an isomorphism between the above two complexes.
* `group_cohomology A n`: this is $\mathrm{H}^n(G, A),$ defined as the $n$th cohomology of the
second complex, `inhomogeneous_cochains A`.
* `group_cohomology_iso_Ext A n`: an isomorphism $\mathrm{H}^n(G, A) \cong \mathrm{Ext}^n(k, A)$
(where $\mathrm{Ext}$ is taken in the category `Rep k G`) induced by `inhomogeneous_cochains_iso A`.

## Implementation notes

Group cohomology is typically stated for `G`-modules, or equivalently modules over the group ring
`ℤ[G].` However, `ℤ` can be generalized to any commutative ring `k`, which is what we use.
Moreover, we express `k[G]`-module structures on a module `k`-module `A` using the `Rep`
definition. We avoid using instances `module (monoid_algebra k G) A` so that we do not run into
possible scalar action diamonds.

## TODO

* API for cohomology in low degree: $\mathrm{H}^0, \mathrm{H}^1$ and $\mathrm{H}^2.$ For example,
the inflation-restriction exact sequence.
* The long exact sequence in cohomology attached to a short exact sequence of representations.
* Upgrading `group_cohomology_iso_Ext` to an isomorphism of derived functors.
* Profinite cohomology.

Longer term:
* The Hochschild-Serre spectral sequence (this is perhaps a good toy example for the theory of
spectral sequences in general).
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
{ to_fun := λ f g, A.ρ (g 0) (f (λ i, g i.succ))
    + finset.univ.sum (λ j : fin (n + 1), (-1 : k) ^ ((j : ℕ) + 1) • f (fin.contract_nth j (*) g)),
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

/-- The theorem that our isomorphism `Fun(Gⁿ, A) ≅ Hom(k[Gⁿ⁺¹], A)` (where the righthand side is
morphisms in `Rep k G`) commutes with the differentials in the complex of inhomogeneous cochains
and the homogeneous `linear_yoneda_obj_resolution`. -/
lemma d_eq :
  d n A = ((diagonal_hom_equiv n A).to_Module_iso.inv
    ≫ (linear_yoneda_obj_resolution A).d n (n + 1)
    ≫ (diagonal_hom_equiv (n + 1) A).to_Module_iso.hom) :=
begin
  ext f g,
  simp only [Module.coe_comp, linear_equiv.coe_coe, function.comp_app,
    linear_equiv.to_Module_iso_inv, linear_yoneda_obj_resolution_d_apply,
    linear_equiv.to_Module_iso_hom, diagonal_hom_equiv_apply, Action.comp_hom,
    resolution.d_eq k G n, resolution.d_of (fin.partial_prod g), linear_map.map_sum,
    ←finsupp.smul_single_one _ ((-1 : k) ^ _), map_smul, d_apply],
  simp only [@fin.sum_univ_succ _ _ (n + 1), fin.coe_zero, pow_zero, one_smul, fin.succ_above_zero,
    diagonal_hom_equiv_symm_apply f (fin.partial_prod g ∘ @fin.succ (n + 1)), function.comp_app,
    fin.partial_prod_succ, fin.cast_succ_zero, fin.partial_prod_zero, one_mul],
  congr' 1,
  { congr,
    ext,
    have := fin.partial_prod_right_inv g (fin.cast_succ x),
    simp only [fin.cast_succ_fin_succ] at *,
    rw [mul_assoc, ←mul_assoc _ _ (g x.succ), this, inv_mul_cancel_left] },
  { exact finset.sum_congr rfl (λ j hj,
      by rw [diagonal_hom_equiv_symm_partial_prod_succ, fin.coe_succ]) }
end

end inhomogeneous_cochains
namespace group_cohomology
variables [group G] (n) (A : Rep k G)

open inhomogeneous_cochains

/-- Given a `k`-linear `G`-representation `A`, this is the complex of inhomogeneous cochains
$$0 \to \mathrm{Fun}(G^0, A) \to \mathrm{Fun}(G^1, A) \to \mathrm{Fun}(G^2, A) \to \dots$$
which calculates the group cohomology of `A`. -/
noncomputable abbreviation inhomogeneous_cochains : cochain_complex (Module k) ℕ :=
cochain_complex.of (λ n, Module.of k ((fin n → G) → A))
(λ n, inhomogeneous_cochains.d n A) (λ n,
begin
  ext x y,
  have := linear_map.ext_iff.1 ((linear_yoneda_obj_resolution A).d_comp_d n (n + 1) (n + 2)),
  simp only [Module.coe_comp, function.comp_app] at this,
  simp only [Module.coe_comp, function.comp_app, d_eq, linear_equiv.to_Module_iso_hom,
    linear_equiv.to_Module_iso_inv, linear_equiv.coe_coe, linear_equiv.symm_apply_apply,
    this, linear_map.zero_apply, map_zero, pi.zero_apply],
end)

/-- Given a `k`-linear `G`-representation `A`, the complex of inhomogeneous cochains is isomorphic
to `Hom(P, A)`, where `P` is the standard resolution of `k` as a trivial `G`-representation. -/
def inhomogeneous_cochains_iso :
  inhomogeneous_cochains A ≅ linear_yoneda_obj_resolution A :=
homological_complex.hom.iso_of_components
  (λ i, (Rep.diagonal_hom_equiv i A).to_Module_iso.symm) $
begin
  rintros i j (h : i + 1 = j),
  subst h,
  simp only [cochain_complex.of_d, d_eq, category.assoc, iso.symm_hom,
    iso.hom_inv_id, category.comp_id],
end

end group_cohomology
open group_cohomology

/-- The group cohomology of a `k`-linear `G`-representation `A`, as the cohomology of its complex
of inhomogeneous cochains. -/
def group_cohomology [group G] (A : Rep k G) (n : ℕ) : Module k :=
(inhomogeneous_cochains A).homology n

/-- The `n`th group cohomology of a `k`-linear `G`-representation `A` is isomorphic to
`Extⁿ(k, A)` (taken in `Rep k G`), where `k` is a trivial `k`-linear `G`-representation. -/
def group_cohomology_iso_Ext [group G] (A : Rep k G) (n : ℕ) :
  group_cohomology A n ≅ ((Ext k (Rep k G) n).obj
    (opposite.op $ Rep.trivial k G k)).obj A :=
(homology_obj_iso_of_homotopy_equiv (homotopy_equiv.of_iso (inhomogeneous_cochains_iso _)) _)
  ≪≫ (homological_complex.homology_unop _ _) ≪≫ (Ext_iso k G A n).symm
