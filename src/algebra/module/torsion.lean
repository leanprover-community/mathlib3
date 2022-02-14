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

* The notions are defined for a `comm_ring R` and a `module R M`. We further require `R` to be a
  domain when talking about `torsion' R M` (otherwise it may not be a submodule), and for `M` to be
  an `add_comm_group` when it's needed.
* The letters `a`, `b`, ... are used for scalars (in `R`), while `x`, `y`, ... are used for vectors
  (in `M`).

## Tags

Torsion, submodule, module, quotient
-/


section defs
variables (R M : Type*) [comm_ring R] [add_comm_monoid M] [module R M] (a : R)
open is_linear_map

/-- The `a`-torsion submodule, for `a` in `R` -/
def torsion : submodule R M := (mk' (λ z, a • z) (is_linear_map_smul a)).ker

/-- The torsion submodule, only defined when `R` is a domain. -/
def torsion' [is_domain R] : submodule R M :=
{ carrier := { x | ∃ a : R, a • x = 0 ∧ a ≠ 0 },
  zero_mem' := ⟨1, smul_zero _, one_ne_zero⟩,
  add_mem' := λ x y hx hy, begin
    cases hx with a hx,
    cases hy with b hy,
    exact ⟨b * a,
      by rw [smul_add, ← smul_smul, mul_comm, ← smul_smul, hx.left, hy.left,
             smul_zero, smul_zero, add_zero],
      mul_ne_zero hy.right hx.right⟩
  end,
  smul_mem' := λ a x h, begin
    cases h with b h,
    exact ⟨b, by rw [smul_smul, mul_comm, ← smul_smul, h.left, smul_zero], h.right⟩
  end }
end defs

section
variables {R M : Type*} [comm_ring R] [add_comm_monoid M] [module R M] (a : R)

lemma smul_torsion (x : torsion R M a) : a • x = 0 := begin
  cases x with x h, ext, exact h
end

/-- A module is torsion-free (`no_zero_smul_divisors`) iff its torsion submodule is trivial. -/
lemma no_zero_smul_divisors_iff_torsion_bot [is_domain R] :
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
end

section quotient
open ideal.quotient
open submodule.quotient
variables {R M : Type*} [comm_ring R] [add_comm_group M] [module R M] (a : R)

noncomputable instance : has_scalar (R ⧸ ideal.span ({a} : set R)) (torsion R M a) :=
  { smul := λ b x, classical.some (mk_surjective _ b) • x }
/-- The `a`-torsion submodule as a `(R ⧸ R·a)`-module. -/
noncomputable instance : module (R ⧸ ideal.span ({a} : set R)) (torsion R M a) :=
function.surjective.module_left (mk _) (mk_surjective _) $
λ b x, begin
  change classical.some _ • x = b • x,
  rw [← sub_eq_zero, ← sub_smul],
  have := (submodule.quotient.eq _).mp (classical.some_spec (mk_surjective _ $ mk _ b)),
  cases ideal.mem_span_singleton'.mp this with c h,
  rw [← h, ← smul_smul, smul_torsion, smul_zero]
end

/-- Quotienting by the torsion submodule gives a torsion-free module. -/
lemma quot_torsion_is_torsion_free [is_domain R] : no_zero_smul_divisors R (M ⧸ torsion' R M) :=
{ eq_zero_or_eq_zero_of_smul_eq_zero := λ a, (mk_surjective (torsion' R M)).forall.mpr $
  λ x h, begin
    rw [← mk_smul, mk_eq_zero] at h,
    rw [mk_eq_zero, or_iff_not_imp_left], intro a0,
    cases h with b h,
    exact ⟨b * a, (smul_smul _ _ _).symm.trans h.left, mul_ne_zero h.right a0⟩
  end }
end quotient
