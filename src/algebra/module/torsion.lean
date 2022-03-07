/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
import algebra.module
import linear_algebra.quotient
import ring_theory.ideal.quotient
import ring_theory.non_zero_divisors
import group_theory.torsion

/-!
# Torsion submodules

## Main definitions

* `torsion_by R M a` : the `a`-torsion submodule, containing all elements `x` of `M` such that
  `a • x = 0`.
* `torsion' R M S`: the `S`-torsion submodule, containing all elements `x` of `M` such that
  `a • x = 0` for some `a` in `S`.
* `torsion R M` : the torsion submoule, containing all elements `x` of `M` such that  `a • x = 0`
  for some non-zero-divisor `a` in `R`.

## Main statements

* `torsion' R M S` and `torsion R M` are submodules.
* `torsion_by R M a` can be viewed as a `(R ⧸ R∙a)`-module.
* `torsion_by_torsion_by_eq_top` : the `a`-torsion submodule of the `a`-torsion submodule (viewed as
  a module) is the full `a`-torsion module. Similar lemmas for `torsion'` and `torsion`.
* `no_zero_smul_divisors_iff_torsion_bot` : a module over a domain has `no_zero_smul_divisors`
  (that is, there is no non-zero `a`, `x` such that `a • x = 0` )iff its torsion submodule is
  trivial.
* `quotient_torsion.torsion_eq_bot` : quotienting by the torsion submodule makes the torsion
  submodule of the new module trivial. If `R` is a domain, we can derive an instance
  `quotient_torsion.no_zero_smul_divisors : no_zero_smul_divisors R (M ⧸ torsion R M)`.

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
@[simps] def torsion_by (a : R) : submodule R M := (distrib_mul_action.to_linear_map _ _ a).ker

/-- The `S`-torsion submodule, containing all elements `x` of `M` such that `a • x = 0` for some
`a` in `S`. -/
@[simps] def torsion' (S : Type*)
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
@[reducible] def torsion := torsion' R M R⁰

end defs

section
variables {R M : Type*}

section torsion_by
variables [comm_semiring R] [add_comm_monoid M] [module R M] (a : R)

@[simp] lemma smul_torsion_by (x : torsion_by R M a) : a • x = 0 := subtype.ext x.prop
@[simp] lemma smul'_torsion_by (x : torsion_by R M a) : a • (x:M) = 0 := x.prop
@[simp] lemma mem_torsion_by_iff (x : M) : x ∈ torsion_by R M a ↔ a • x = 0 := iff.rfl

/-- The `a`-torsion submodule of the `a`-torsion submodule (viewed as a module) is the full
`a`-torsion module. -/
lemma torsion_by_torsion_by_eq_top : torsion_by R (torsion_by R M a) a = ⊤ :=
begin
  ext,
  exact ⟨λ _, trivial, λ _, smul_torsion_by a x⟩
end

end torsion_by

section quotient
variables [comm_ring R] [add_comm_group M] [module R M] (a : R)

instance : has_scalar (R ⧸ R ∙ a) (torsion_by R M a) :=
{ smul := λ b x, quotient.lift_on' b (• x) $ λ b₁ b₂ (h : b₁ - b₂ ∈ _), begin
    show b₁ • x = b₂ • x,
    obtain ⟨c, h⟩ := ideal.mem_span_singleton'.mp h,
    rw [← sub_eq_zero, ← sub_smul, ←h, mul_smul, smul_torsion_by, smul_zero],
  end }

@[simp] lemma torsion_by.mk_smul (b : R) (x : torsion_by R M a) :
  ideal.quotient.mk (R ∙ a) b • x = b • x := rfl

/-- The `a`-torsion submodule as a `(R ⧸ R∙a)`-module. -/
instance : module (R ⧸ R ∙ a) (torsion_by R M a) :=
ideal.quotient.mk_surjective.module_left _ (torsion_by.mk_smul _)

instance {S : Type*} [has_scalar S R] [has_scalar S M]
  [is_scalar_tower S R M] [is_scalar_tower S R R] :
  is_scalar_tower S (R ⧸ R ∙ a) (torsion_by R M a) :=
{ smul_assoc := λ b d x, quotient.induction_on' d $ λ c, (smul_assoc b c x : _) }

end quotient

section torsion'
variables [comm_semiring R] [add_comm_monoid M] [module R M]
variables (S : Type*) [comm_monoid S] [distrib_mul_action S M] [smul_comm_class S R M]

@[simp] lemma mem_torsion'_iff (x : M) : x ∈ torsion' R M S ↔ ∃ a : S, a • x = 0 := iff.rfl
@[simp] lemma mem_torsion_iff (x : M) : x ∈ torsion R M ↔ ∃ a : R⁰, a • x = 0 := iff.rfl

instance i : has_scalar S (torsion' R M S) := ⟨λ s x, ⟨s • x, begin
  obtain ⟨x, a, h⟩ := x, use a, dsimp, rw [smul_comm, h, smul_zero] end⟩⟩
instance : distrib_mul_action S (torsion' R M S) := subtype.coe_injective.distrib_mul_action
  ((torsion' R M S).subtype).to_add_monoid_hom (λ (c : S) x, rfl)
instance : smul_comm_class S R (torsion' R M S) := ⟨λ s a x, begin ext, exact smul_comm _ _ _ end⟩

/-- The `S`-torsion submodule of the `S`-torsion submodule (viewed as a module) is the full
`S`-torsion module. -/
lemma torsion'_torsion'_eq_top : torsion' R (torsion' R M S) S = ⊤ :=
begin
  ext, refine ⟨λ _, trivial, λ _, _⟩,
  obtain ⟨x, a, ha⟩ := x, use a, ext, exact ha
end
/-- The torsion submodule of the torsion submodule (viewed as a module) is the full
torsion module. -/
lemma torsion_torsion_eq_top : torsion R (torsion R M) = ⊤ := torsion'_torsion'_eq_top R⁰

end torsion'

section torsion
variables [comm_semiring R] [add_comm_monoid M] [no_zero_divisors R] [nontrivial R] [module R M]

example (a : R⁰) (x : M) : a • x = (a : R) • x := submonoid.smul_def a x

lemma coe_torsion_eq_annihilator_ne_bot :
  (torsion R M : set M) = { x : M | (R ∙ x).annihilator ≠ ⊥ } :=
begin
  ext x, simp_rw [submodule.ne_bot_iff, mem_annihilator, mem_span_singleton],
  exact ⟨λ ⟨a, hax⟩, ⟨a, λ _ ⟨b, hb⟩, by rw [← hb, smul_comm, ← submonoid.smul_def, hax, smul_zero],
    non_zero_divisors.coe_ne_zero _⟩,
    λ ⟨a, hax, ha⟩, ⟨⟨_, mem_non_zero_divisors_of_ne_zero ha⟩, hax x ⟨1, one_smul _ _⟩⟩⟩
end

/-- A module over a domain has `no_zero_smul_divisors` iff its torsion submodule is trivial. -/
lemma no_zero_smul_divisors_iff_torsion_eq_bot :
  no_zero_smul_divisors R M ↔ torsion R M = ⊥ :=
begin
  split; intro h,
  { haveI : no_zero_smul_divisors R M := h,
    ext, split; intro hx,
    { cases hx with a hax,
      have hax : (a : R) • x = 0 := hax,
      cases eq_zero_or_eq_zero_of_smul_eq_zero hax with h0 h0,
      { exfalso, exact non_zero_divisors.coe_ne_zero a h0 }, { exact h0 } },
    { have hx : x = 0 := hx, rw hx, exact (torsion R M).zero_mem } },
  { exact { eq_zero_or_eq_zero_of_smul_eq_zero := λ a x hax, begin
      by_cases ha : a = 0,
      { left, exact ha },
      { right, rw [← submodule.mem_bot _, ← h],
        exact ⟨⟨a, mem_non_zero_divisors_of_ne_zero ha⟩, hax⟩ }
    end } }
end
end torsion

namespace quotient_torsion
variables [comm_ring R] [add_comm_group M] [module R M]

/-- Quotienting by the torsion submodule gives a torsion-free module. -/
lemma torsion_eq_bot : torsion R (M ⧸ torsion R M) = ⊥ :=
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

instance no_zero_smul_divisors [is_domain R] : no_zero_smul_divisors R (M ⧸ torsion R M) :=
no_zero_smul_divisors_iff_torsion_eq_bot.mpr torsion_eq_bot

end quotient_torsion
end
end submodule

section ℕ_torsion
variables {M : Type*} [add_comm_monoid M]

theorem is_torsion_iff_torsion_eq_top : add_monoid.is_torsion M ↔ submodule.torsion ℕ M = ⊤ :=
begin
  refine ⟨λ h, submodule.ext (λ x, ⟨λ _, trivial, λ _, _⟩), λ h x, _⟩,
  { obtain ⟨n, h0, hn⟩ := (is_of_fin_add_order_iff_nsmul_eq_zero x).mp (h x),
    exact ⟨⟨n, mem_non_zero_divisors_of_ne_zero (ne_of_gt h0)⟩, hn⟩ },
  { rw is_of_fin_add_order_iff_nsmul_eq_zero,
    have : x ∈ (⊤ : submodule ℕ M) := trivial, rw ← h at this,
    obtain ⟨⟨n, h0⟩, hn⟩ := this,
    refine ⟨n, nat.pos_of_ne_zero _, hn⟩,
    rw mem_non_zero_divisors_iff at h0, exact λ hn0, one_ne_zero (h0 _ $ by rw [hn0, mul_zero]), }
end
end ℕ_torsion
