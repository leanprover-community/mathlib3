/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.lie.submodule
import algebra.lie.of_associative
import linear_algebra.isomorphisms

/-!
# Quotients of Lie algebras and Lie modules

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Given a Lie submodule of a Lie module, the quotient carries a natural Lie module structure. In the
special case that the Lie module is the Lie algebra itself via the adjoint action, the submodule
is a Lie ideal and the quotient carries a natural Lie algebra structure.

We define these quotient structures here. A notable omission at the time of writing (February 2021)
is a statement and proof of the universal property of these quotients.

## Main definitions

  * `lie_submodule.quotient.lie_quotient_lie_module`
  * `lie_submodule.quotient.lie_quotient_lie_algebra`

## Tags

lie algebra, quotient
-/

universes u v w w₁ w₂

namespace lie_submodule

variables {R : Type u} {L : Type v} {M : Type w}
variables [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M]
variables [lie_ring_module L M] [lie_module R L M]
variables (N N' : lie_submodule R L M) (I J : lie_ideal R L)

/-- The quotient of a Lie module by a Lie submodule. It is a Lie module. -/
instance : has_quotient M (lie_submodule R L M) :=
⟨λ N, M ⧸ N.to_submodule⟩

namespace quotient

variables {N I}

instance add_comm_group : add_comm_group (M ⧸ N) := submodule.quotient.add_comm_group _
instance module' {S : Type*} [semiring S] [has_smul S R] [module S M] [is_scalar_tower S R M] :
  module S (M ⧸ N) := submodule.quotient.module' _
instance module : module R (M ⧸ N) := submodule.quotient.module _
instance is_central_scalar {S : Type*} [semiring S]
  [has_smul S R] [module S M] [is_scalar_tower S R M]
  [has_smul Sᵐᵒᵖ R] [module Sᵐᵒᵖ M] [is_scalar_tower Sᵐᵒᵖ R M]
  [is_central_scalar S M] : is_central_scalar S (M ⧸ N) :=
submodule.quotient.is_central_scalar _
instance inhabited : inhabited (M ⧸ N) := ⟨0⟩

/-- Map sending an element of `M` to the corresponding element of `M/N`, when `N` is a
lie_submodule of the lie_module `N`. -/
abbreviation mk : M → M ⧸ N := submodule.quotient.mk

lemma is_quotient_mk (m : M) : quotient.mk' m = (mk m : M ⧸ N) := rfl

/-- Given a Lie module `M` over a Lie algebra `L`, together with a Lie submodule `N ⊆ M`, there
is a natural linear map from `L` to the endomorphisms of `M` leaving `N` invariant. -/
def lie_submodule_invariant : L →ₗ[R] submodule.compatible_maps N.to_submodule N.to_submodule :=
linear_map.cod_restrict _ (lie_module.to_endomorphism R L M) $ λ _ _, N.lie_mem

variables (N)

/-- Given a Lie module `M` over a Lie algebra `L`, together with a Lie submodule `N ⊆ M`, there
is a natural Lie algebra morphism from `L` to the linear endomorphism of the quotient `M/N`. -/
def action_as_endo_map : L →ₗ⁅R⁆ module.End R (M ⧸ N) :=
{ map_lie' := λ x y, submodule.linear_map_qext _ $ linear_map.ext $ λ m,
    congr_arg mk $ lie_lie _ _ _,
  ..linear_map.comp (submodule.mapq_linear (N : submodule R M) ↑N) lie_submodule_invariant }

/-- Given a Lie module `M` over a Lie algebra `L`, together with a Lie submodule `N ⊆ M`, there is
a natural bracket action of `L` on the quotient `M/N`. -/
instance action_as_endo_map_bracket : has_bracket L (M ⧸ N) := ⟨λ x n, action_as_endo_map N x n⟩

instance lie_quotient_lie_ring_module : lie_ring_module L (M ⧸ N) :=
{ bracket := has_bracket.bracket,
  ..lie_ring_module.comp_lie_hom _ (action_as_endo_map N) }

/-- The quotient of a Lie module by a Lie submodule, is a Lie module. -/
instance lie_quotient_lie_module : lie_module R L (M ⧸ N) :=
lie_module.comp_lie_hom _ (action_as_endo_map N)

instance lie_quotient_has_bracket : has_bracket (L ⧸ I) (L ⧸ I) :=
⟨begin
  intros x y,
  apply quotient.lift_on₂' x y (λ x' y', mk ⁅x', y'⁆),
  intros x₁ x₂ y₁ y₂ h₁ h₂,
  apply (submodule.quotient.eq I.to_submodule).2,
  rw submodule.quotient_rel_r_def at h₁ h₂,
  have h : ⁅x₁, x₂⁆ - ⁅y₁, y₂⁆ = ⁅x₁, x₂ - y₂⁆ + ⁅x₁ - y₁, y₂⁆,
    by simp [-lie_skew, sub_eq_add_neg, add_assoc],
  rw h,
  apply submodule.add_mem,
  { apply lie_mem_right R L I x₁ (x₂ - y₂) h₂, },
  { apply lie_mem_left R L I (x₁ - y₁) y₂ h₁, },
end⟩

@[simp] lemma mk_bracket (x y : L) :
  mk ⁅x, y⁆ = ⁅(mk x : L ⧸ I), (mk y : L ⧸ I)⁆ := rfl

instance lie_quotient_lie_ring : lie_ring (L ⧸ I) :=
{ add_lie  := by { intros x' y' z', apply quotient.induction_on₃' x' y' z', intros x y z,
                   repeat { rw is_quotient_mk <|>
                            rw ←mk_bracket <|>
                            rw ←submodule.quotient.mk_add, },
                   apply congr_arg, apply add_lie, },
  lie_add  := by { intros x' y' z', apply quotient.induction_on₃' x' y' z', intros x y z,
                   repeat { rw is_quotient_mk <|>
                            rw ←mk_bracket <|>
                            rw ←submodule.quotient.mk_add, },
                   apply congr_arg, apply lie_add, },
  lie_self := by { intros x', apply quotient.induction_on' x', intros x,
                   rw [is_quotient_mk, ←mk_bracket],
                   apply congr_arg, apply lie_self, },
  leibniz_lie := by { intros x' y' z', apply quotient.induction_on₃' x' y' z', intros x y z,
                   repeat { rw is_quotient_mk <|>
                            rw ←mk_bracket <|>
                            rw ←submodule.quotient.mk_add, },
                   apply congr_arg, apply leibniz_lie, } }

instance lie_quotient_lie_algebra : lie_algebra R (L ⧸ I) :=
{ lie_smul := by { intros t x' y', apply quotient.induction_on₂' x' y', intros x y,
                   repeat { rw is_quotient_mk <|>
                            rw ←mk_bracket <|>
                            rw ←submodule.quotient.mk_smul, },
                   apply congr_arg, apply lie_smul, } }

/-- `lie_submodule.quotient.mk` as a `lie_module_hom`. -/
@[simps]
def mk' : M →ₗ⁅R,L⁆ M ⧸ N :=
{ to_fun := mk, map_lie' := λ r m, rfl, ..N.to_submodule.mkq}

@[simp] lemma mk_eq_zero {m : M} : mk' N m = 0 ↔ m ∈ N :=
submodule.quotient.mk_eq_zero N.to_submodule

@[simp] lemma mk'_ker : (mk' N).ker = N :=
by { ext, simp, }

@[simp] lemma map_mk'_eq_bot_le : map (mk' N) N' = ⊥ ↔ N' ≤ N :=
by rw [← lie_module_hom.le_ker_iff_map, mk'_ker]

/-- Two `lie_module_hom`s from a quotient lie module are equal if their compositions with
`lie_submodule.quotient.mk'` are equal.

See note [partially-applied ext lemmas]. -/
@[ext]
lemma lie_module_hom_ext ⦃f g : M ⧸ N →ₗ⁅R,L⁆ M⦄ (h : f.comp (mk' N) = g.comp (mk' N)) :
  f = g :=
lie_module_hom.ext $ λ x, quotient.induction_on' x $ lie_module_hom.congr_fun h

end quotient

end lie_submodule

namespace lie_hom

variables {R L L' : Type*}
variables [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L']
variables (f : L →ₗ⁅R⁆ L')

/-- The first isomorphism theorem for morphisms of Lie algebras. -/
@[simps] noncomputable def quot_ker_equiv_range : L ⧸ f.ker ≃ₗ⁅R⁆ f.range :=
{ to_fun := (f : L →ₗ[R] L').quot_ker_equiv_range,
  map_lie' :=
  begin
    rintros ⟨x⟩ ⟨y⟩,
    rw [← set_like.coe_eq_coe, lie_subalgebra.coe_bracket],
    simp only [submodule.quotient.quot_mk_eq_mk, linear_map.quot_ker_equiv_range_apply_mk,
      ← lie_submodule.quotient.mk_bracket, coe_to_linear_map, map_lie],
  end,
  .. (f : L →ₗ[R] L').quot_ker_equiv_range, }

end lie_hom
