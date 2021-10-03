/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.lie.submodule
import algebra.lie.of_associative

/-!
# Quotients of Lie algebras and Lie modules

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
abbreviation quotient := N.to_submodule.quotient

namespace quotient

variables {N I}

/-- Map sending an element of `M` to the corresponding element of `M/N`, when `N` is a
lie_submodule of the lie_module `N`. -/
abbreviation mk : M → N.quotient := submodule.quotient.mk

lemma is_quotient_mk (m : M) :
  quotient.mk' m = (mk m : N.quotient) := rfl

/-- Given a Lie module `M` over a Lie algebra `L`, together with a Lie submodule `N ⊆ M`, there
is a natural linear map from `L` to the endomorphisms of `M` leaving `N` invariant. -/
def lie_submodule_invariant : L →ₗ[R] submodule.compatible_maps N.to_submodule N.to_submodule :=
  linear_map.cod_restrict _ (lie_module.to_endomorphism R L M) N.lie_mem

variables (N)

/-- Given a Lie module `M` over a Lie algebra `L`, together with a Lie submodule `N ⊆ M`, there
is a natural Lie algebra morphism from `L` to the linear endomorphism of the quotient `M/N`. -/
def action_as_endo_map : L →ₗ⁅R⁆ module.End R N.quotient :=
{ map_lie' := λ x y, by { ext m,
                          change mk ⁅⁅x, y⁆, m⁆ = mk (⁅x, ⁅y, m⁆⁆ - ⁅y, ⁅x, m⁆⁆),
                          congr, apply lie_lie, },
  ..linear_map.comp (submodule.mapq_linear (N : submodule R M) ↑N) lie_submodule_invariant }

/-- Given a Lie module `M` over a Lie algebra `L`, together with a Lie submodule `N ⊆ M`, there is
a natural bracket action of `L` on the quotient `M/N`. -/
def action_as_endo_map_bracket : has_bracket L N.quotient := ⟨λ x n, action_as_endo_map N x n⟩

instance lie_quotient_lie_ring_module : lie_ring_module L N.quotient :=
{ bracket     := λ x n, (action_as_endo_map N : L →ₗ[R] module.End R N.quotient) x n,
  add_lie     := λ x y n, by { simp only [linear_map.map_add, linear_map.add_apply], },
  lie_add     := λ x m n, by { simp only [linear_map.map_add, linear_map.add_apply], },
  leibniz_lie := λ x y m, show action_as_endo_map _ _ _ = _,
  { simp only [lie_hom.map_lie, lie_ring.of_associative_ring_bracket, sub_add_cancel,
      lie_hom.coe_to_linear_map, linear_map.mul_apply, linear_map.sub_apply], } }

/-- The quotient of a Lie module by a Lie submodule, is a Lie module. -/
instance lie_quotient_lie_module : lie_module R L N.quotient :=
{ smul_lie := λ t x m, show (_ : L →ₗ[R] module.End R N.quotient) _ _ = _,
  { simp only [linear_map.map_smul], refl, },
  lie_smul := λ x t m, show (_ : L →ₗ[R] module.End R N.quotient) _ _ = _,
  { simp only [linear_map.map_smul], refl, }, }

instance lie_quotient_has_bracket : has_bracket (quotient I) (quotient I) :=
⟨begin
  intros x y,
  apply quotient.lift_on₂' x y (λ x' y', mk ⁅x', y'⁆),
  intros x₁ x₂ y₁ y₂ h₁ h₂,
  apply (submodule.quotient.eq I.to_submodule).2,
  have h : ⁅x₁, x₂⁆ - ⁅y₁, y₂⁆ = ⁅x₁, x₂ - y₂⁆ + ⁅x₁ - y₁, y₂⁆,
    by simp [-lie_skew, sub_eq_add_neg, add_assoc],
  rw h,
  apply submodule.add_mem,
  { apply lie_mem_right R L I x₁ (x₂ - y₂) h₂, },
  { apply lie_mem_left R L I (x₁ - y₁) y₂ h₁, },
end⟩

@[simp] lemma mk_bracket (x y : L) :
  mk ⁅x, y⁆ = ⁅(mk x : quotient I), (mk y : quotient I)⁆ := rfl

instance lie_quotient_lie_ring : lie_ring (quotient I) :=
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

instance lie_quotient_lie_algebra : lie_algebra R (quotient I) :=
{ lie_smul := by { intros t x' y', apply quotient.induction_on₂' x' y', intros x y,
                   repeat { rw is_quotient_mk <|>
                            rw ←mk_bracket <|>
                            rw ←submodule.quotient.mk_smul, },
                   apply congr_arg, apply lie_smul, } }

/-- `lie_submodule.quotient.mk` as a `lie_module_hom`. -/
@[simps]
def mk' : M →ₗ⁅R,L⁆ quotient N :=
{ to_fun := mk, map_lie' := λ r m, rfl, ..N.to_submodule.mkq}

/-- Two `lie_module_hom`s from a quotient lie module are equal if their compositions with
`lie_submodule.quotient.mk'` are equal.

See note [partially-applied ext lemmas]. -/
@[ext]
lemma lie_module_hom_ext ⦃f g : quotient N →ₗ⁅R,L⁆ M⦄ (h : f.comp (mk' N) = g.comp (mk' N)) :
  f = g :=
lie_module_hom.ext $ λ x, quotient.induction_on' x $ lie_module_hom.congr_fun h

end quotient

end lie_submodule
