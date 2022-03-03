/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
import algebra.module
import linear_algebra.quotient
import ring_theory.ideal.quotient
import ring_theory.non_zero_divisors

/-!
# Torsion submodules

## Main definitions

* `torsion R M a` : the `a`-torsion submodule, containing all elements `x` of `M` such that
  `a • x = 0`.
* `torsion'' R M S`: the `S`-torsion submodule, containing all elements `x` of `M` such that
  `a • x = 0` for some `a` in `S`.
* `torsion' R M` : the torsion submoule, containing all elements `x` of `M` such that  `a • x = 0`
  for some non-zero-divisor `a` in `R`.

## Main statements

* `torsion' R M` is a submodule.
* `torsion R M a` can be viewed as a `(R ⧸ R∙a)`-module.
* `torsion_torsion_eq_top` : the `a`-torsion submodule of the `a`-torsion submodule (viewed as a
  module) is the full `a`-torsion module. Similar lemmas for `torsion''` and `torsion'`.
* `no_zero_smul_divisors_iff_torsion'_bot` : a module over a domain has `no_zero_smul_divisors`
  (that is, there is no non-zero `a`, `x` such that `a • x = 0` )iff its `torsion'` submodule is
  trivial.
* `quotient_torsion.torsion'_eq_bot` : quotienting by the `tosion'` submodule makes the `torsion'`
  submodule of the new module trivial. If `R` is a domain, we can derive an instance
  `quotient_torsion.no_zero_smul_divisors : no_zero_smul_divisors R (M ⧸ torsion' R M)`.

## Notation

* The notions are defined for a `comm_semiring R` and a `module R M`. Some additional hypotheses on
  `R` and `M` are required by some lemmas.
* The letters `a`, `b`, ... are used for scalars (in `R`), while `x`, `y`, ... are used for vectors
  (in `M`).

## Tags

Torsion, submodule, module, quotient
-/

namespace submodule
open_locale non_zero_divisors
section defs
variables (R M : Type*) [comm_semiring R] [add_comm_monoid M] [module R M]

/-- The `a`-torsion submodule for `a` in `R`, containing all elements `x` of `M` such that
  `a • x = 0`. -/
@[simps] def torsion (a : R) : submodule R M := (distrib_mul_action.to_linear_map _ _ a).ker

/-- The `S`-torsion submodule, containing all elements `x` of `M` such that `a • x = 0` for some
`a` in `S`. -/
@[simps] def torsion'' (S : Type*)
  [comm_monoid S] [distrib_mul_action S M] [smul_comm_class S R M] :
  submodule R M :=
{ carrier := { x | ∃ a : S, a • x = 0 },
  zero_mem' := ⟨1, smul_zero _⟩,
  add_mem' := λ x y ⟨a, hx⟩ ⟨b, hy⟩,
    ⟨b * a,
      by rw [smul_add, mul_smul, mul_comm, mul_smul, hx, hy, smul_zero, smul_zero, add_zero]⟩,
  smul_mem' := λ a x ⟨b, h⟩, ⟨b, by rw [smul_comm, h, smul_zero]⟩ }

/-- The torsion submoule, containing all elements `x` of `M` such that  `a • x = 0` for some
  non-zero-divisor `a` in `R`. -/
@[simps] def torsion' := torsion'' R M R⁰

end defs

section
variables {R M : Type*}

section torsion
variables [comm_semiring R] [add_comm_monoid M] [module R M] (a : R)

@[simp] lemma smul_torsion (x : torsion R M a) : a • x = 0 := subtype.ext x.prop
@[simp] lemma smul'_torsion (x : torsion R M a) : a • (x:M) = 0 := x.prop
@[simp] lemma mem_torsion_iff (x : M) : x ∈ torsion R M a ↔ a • x = 0 := iff.rfl

/-- The `a`-torsion submodule of the `a`-torsion submodule (viewed as a module) is the full
`a`-torsion module. -/
lemma torsion_torsion_eq_top : torsion R (torsion R M a) a = ⊤ :=
begin
  ext,
  exact ⟨λ _, trivial, λ _, smul_torsion a x⟩
end

end torsion

section quotient
variables [comm_ring R] [add_comm_group M] [module R M] (a : R)

instance : has_scalar (R ⧸ R ∙ a) (torsion R M a) :=
{ smul := λ b x, quotient.lift_on' b (• x) $ λ b₁ b₂ (h : b₁ - b₂ ∈ _), begin
    show b₁ • x = b₂ • x,
    obtain ⟨c, h⟩ := ideal.mem_span_singleton'.mp h,
    rw [← sub_eq_zero, ← sub_smul, ←h, mul_smul, smul_torsion, smul_zero],
  end }

@[simp] lemma torsion.mk_smul (b : R) (x : torsion R M a) :
  ideal.quotient.mk (R ∙ a) b • x = b • x := rfl

/-- The `a`-torsion submodule as a `(R ⧸ R∙a)`-module. -/
instance : module (R ⧸ R ∙ a) (torsion R M a) :=
ideal.quotient.mk_surjective.module_left _ (torsion.mk_smul _)

instance {S : Type*} [has_scalar S R] [has_scalar S M]
  [is_scalar_tower S R M] [is_scalar_tower S R R] :
  is_scalar_tower S (R ⧸ R ∙ a) (torsion R M a) :=
{ smul_assoc := λ b d x, quotient.induction_on' d $ λ c, (smul_assoc b c x : _) }

end quotient

section torsion''
variables [comm_semiring R] [add_comm_monoid M] [module R M]
variables (S : Type*) [comm_monoid S] [distrib_mul_action S M] [smul_comm_class S R M]

@[simp] lemma mem_torsion''_iff (x : M) : x ∈ torsion'' R M S ↔ ∃ a : S, a • x = 0 := iff.rfl
@[simp] lemma mem_torsion'_iff (x : M) : x ∈ torsion' R M ↔ ∃ a : R⁰, a • x = 0 := iff.rfl

instance i : has_scalar S (torsion'' R M S) := ⟨λ s x, ⟨s • x, begin
  obtain ⟨x, a, h⟩ := x, use a, dsimp, rw [smul_comm, h, smul_zero] end⟩⟩
instance : distrib_mul_action S (torsion'' R M S) := subtype.coe_injective.distrib_mul_action
  ((torsion'' R M S).subtype).to_add_monoid_hom (λ (c : S) x, rfl)
instance : smul_comm_class S R (torsion'' R M S) := ⟨λ s a x, begin ext, exact smul_comm _ _ _ end⟩

/-- The `S`-torsion submodule of the `S`-torsion submodule (viewed as a module) is the full
`S`-torsion module. -/
lemma torsion''_torsion''_eq_top : torsion'' R (torsion'' R M S) S = ⊤ :=
begin
  ext, refine ⟨λ _, trivial, λ _, _⟩,
  obtain ⟨x, a, ha⟩ := x, use a, ext, exact ha
end
/-- The `torsion'` submodule of the `torsion'` submodule (viewed as a module) is the full
`torsion'` module. -/
lemma torsion'_torsion'_eq_top : torsion' R (torsion' R M) = ⊤ := torsion''_torsion''_eq_top R⁰

end torsion''

section torsion'
variables [comm_semiring R] [add_comm_monoid M] [no_zero_divisors R] [nontrivial R] [module R M]

/-- A module over a domain has `no_zero_smul_divisors` iff its `torsion'` submodule is trivial. -/
lemma no_zero_smul_divisors_iff_torsion'_bot :
  no_zero_smul_divisors R M ↔ torsion' R M = ⊥ :=
begin
  split; intro h,
  { haveI : no_zero_smul_divisors R M := h,
    ext, split; intro hx,
    { cases hx with a hax,
      have hax : (a : R) • x = 0 := hax,
      cases eq_zero_or_eq_zero_of_smul_eq_zero hax with h0 h0,
      { exfalso, exact non_zero_divisors.coe_ne_zero a h0 }, { exact h0 } },
    { have hx : x = 0 := hx, rw hx, exact (torsion' R M).zero_mem } },
  { exact { eq_zero_or_eq_zero_of_smul_eq_zero := λ a x hax, begin
      by_cases ha : a = 0,
      { left, exact ha },
      { right, rw [← submodule.mem_bot _, ← h],
        exact ⟨⟨a, mem_non_zero_divisors_of_ne_zero ha⟩, hax⟩ }
    end } }
end
end torsion'

section torsion'_quotient
variables [comm_ring R] [add_comm_group M] [module R M]

/-- Quotienting by the `torsion'` submodule gives a torsion-free module. -/
lemma quotient_torsion.torsion'_eq_bot : torsion' R (M ⧸ torsion' R M) = ⊥ :=
begin
  ext z, split,
  { exact quotient.induction_on' z (λ x hx, begin
      cases hx with a hax,
      rw [quotient.mk'_eq_mk, ← quotient.mk_smul, quotient.mk_eq_zero] at hax,
      change quotient.mk x = 0, rw quotient.mk_eq_zero,
      cases hax with b h,
      exact ⟨b * a, (mul_smul _ _ _).trans h⟩
    end) },
  { intro hz, have hz : z = 0 := hz, rw hz, exact zero_mem _ }
end

instance quotient_torsion.no_zero_smul_divisors [is_domain R] :
  no_zero_smul_divisors R (M ⧸ torsion' R M) :=
no_zero_smul_divisors_iff_torsion'_bot.mpr quotient_torsion.torsion'_eq_bot

end torsion'_quotient
end
end submodule
