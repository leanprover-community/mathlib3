/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
import algebra.module
import linear_algebra.quotient
import ring_theory.ideal.quotient

/-!
# Torsion submodules

## Main definitions

* `torsion R M a` : the `a`-torsion submodule, containing all elements `x` of `M` such that
  `a • x = 0`.
* `torsion' R M` : the torsion submoule, containing all elements `x` of `M` such that  `a • x = 0`
  for some non-zero `a` in `R`.

## Main statements

* `torsion' R M` is a submodule when `R` is a domain.
* `torsion R M a` can be viewed as a `(R ⧸ R·a)`-module.
* `quot_torsion_is_torsion_free` : `(M ⧸ torsion' R M)` is a torsion-free module, that is, there is
  no non-zero `a`, `x` such that `a • x = 0`.

## Notation

* The notions are defined for a `comm_semiring R` and a `module R M`. Some additional hypotheses on
  `R` and `M`are required by some lemmas.
* The letters `a`, `b`, ... are used for scalars (in `R`), while `x`, `y`, ... are used for vectors
  (in `M`).

## Tags

Torsion, submodule, module, quotient
-/


section defs
variables (R M : Type*) [comm_semiring R] [add_comm_monoid M] [module R M] (a : R)

/-- The `a`-torsion submodule, for `a` in `R` -/
def torsion : submodule R M := (distrib_mul_action.to_linear_map _ _ a).ker

/-- The torsion submodule, only defined when `R` is a domain. -/
def torsion' [no_zero_divisors R] [nontrivial R] : submodule R M :=
{ carrier := { x | ∃ a : R, a • x = 0 ∧ a ≠ 0 },
  zero_mem' := ⟨1, smul_zero _, one_ne_zero⟩,
  add_mem' := λ x y ⟨a, hx, ha⟩ ⟨b, hy, hb⟩,
    ⟨b * a,
      by rw [smul_add, ← smul_smul, mul_comm, ← smul_smul, hx, hy, smul_zero, smul_zero, add_zero],
      mul_ne_zero hb ha⟩,
  smul_mem' := λ a x ⟨b, h, hb⟩, ⟨b, by rw [smul_smul, mul_comm, ← smul_smul, h, smul_zero], hb⟩ }
end defs

section
variables {R M : Type*}

section torsion
variables [comm_semiring R] [add_comm_monoid M] [module R M] (a : R)

@[simp] lemma smul_torsion (x : torsion R M a) : a • x = 0 := subtype.ext x.prop

end torsion

section quotient
variables [comm_ring R] [add_comm_group M] [module R M] (a : R)
open ideal.quotient

instance : has_scalar (R ⧸ ideal.span ({a} : set R)) (torsion R M a) :=
{ smul := λ b x, quotient.lift_on' b (• x) $ λ b₁ b₂ (h : b₁ - b₂ ∈ _), begin
    show b₁ • x = b₂ • x,
    obtain ⟨c, h⟩ := ideal.mem_span_singleton'.mp h,
    rw [← sub_eq_zero, ← sub_smul, ←h, mul_smul, smul_torsion, smul_zero],
  end }

@[simp] lemma torsion.mk_smul (b : R) (x : torsion R M a) :
  mk (ideal.span ({a} : set R)) b • x = b • x := rfl

/-- The `a`-torsion submodule as a `(R ⧸ R·a)`-module. -/
instance : module (R ⧸ ideal.span ({a} : set R)) (torsion R M a) :=
function.surjective.module_left (mk _) mk_surjective (torsion.mk_smul _)

instance {S : Type*} [has_scalar S R] [has_scalar S M]
  [is_scalar_tower S R M] [is_scalar_tower S R R] :
  is_scalar_tower S (R ⧸ ideal.span ({a} : set R)) (torsion R M a) :=
{ smul_assoc := λ b d x, quotient.induction_on' d $ λ c, (smul_assoc b c x : _) }

end quotient

section torsion'
variables [comm_semiring R] [add_comm_monoid M] [no_zero_divisors R] [nontrivial R] [module R M]

/-- A module is torsion-free (`no_zero_smul_divisors`) iff its `torsion'` submodule is trivial. -/
lemma no_zero_smul_divisors_iff_torsion'_bot :
  no_zero_smul_divisors R M ↔ torsion' R M = ⊥ :=
begin
  split; intro h,
  { haveI : no_zero_smul_divisors R M := h,
    ext, split; intro hx,
    { cases hx with a hax,
      cases eq_zero_or_eq_zero_of_smul_eq_zero (hax.left) with h0 h0,
      { exfalso, exact hax.right h0 }, { exact h0 } },
    { have hx : x = 0 := hx, rw hx, exact (torsion' R M).zero_mem } },
  { exact { eq_zero_or_eq_zero_of_smul_eq_zero := λ a x hax, begin
      by_cases ha : a = 0,
      { left, exact ha },
      { right, rw [← submodule.mem_bot _, ← h], exact ⟨a, hax, ha⟩ }
    end } }
end
end torsion'

section torsion'_quotient
variables [comm_ring R] [is_domain R] [add_comm_group M] [module R M]
open submodule.quotient

/-- Quotienting by the `torsion'` submodule gives a torsion-free module. -/
instance quotient_torsion.no_zero_smul_divisors :
  no_zero_smul_divisors R (M ⧸ torsion' R M) :=
{ eq_zero_or_eq_zero_of_smul_eq_zero := λ a, (mk_surjective (torsion' R M)).forall.mpr $
  λ x h, begin
    rw [← mk_smul, mk_eq_zero] at h,
    rw [mk_eq_zero, or_iff_not_imp_left], intro a0,
    cases h with b h,
    exact ⟨b * a, (smul_smul _ _ _).symm.trans h.left, mul_ne_zero h.right a0⟩
  end }

end torsion'_quotient
end
