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

* `submodule.torsion_by R M a` : the `a`-torsion submodule, containing all elements `x` of `M` such
  that `a • x = 0`.
* `submodule.torsion' R M S` : the `S`-torsion submodule, containing all elements `x` of `M` such
  that `a • x = 0` for some `a` in `S`.
* `submodule.torsion R M` : the torsion submoule, containing all elements `x` of `M` such that
  `a • x = 0` for some non-zero-divisor `a` in `R`.
* `module.is_torsion_by R M a` : the property that defines a `a`-torsion module. Similarly,
  `is_torsion'` and `is_torsion`.

## Main statements

* `torsion' R M S` and `torsion R M` are submodules.
* `torsion_by R M a` can be viewed as a `(R ⧸ R∙a)`-module.
* `submodule.torsion_by_is_torsion_by` : the `a`-torsion submodule is a `a`-torsion module.
  Similar lemmas for `torsion'` and `torsion`.
* `submodule.no_zero_smul_divisors_iff_torsion_bot` : a module over a domain has
  `no_zero_smul_divisors` (that is, there is no non-zero `a`, `x` such that `a • x = 0`)
  iff its torsion submodule is trivial.
* `submodule.quotient_torsion.torsion_eq_bot` : quotienting by the torsion submodule makes the
  torsion submodule of the new module trivial. If `R` is a domain, we can derive an instance
  `submodule.quotient_torsion.no_zero_smul_divisors : no_zero_smul_divisors R (M ⧸ torsion R M)`.

## Notation

* The notions are defined for a `comm_semiring R` and a `module R M`. Some additional hypotheses on
  `R` and `M` are required by some lemmas.
* The letters `a`, `b`, ... are used for scalars (in `R`), while `x`, `y`, ... are used for vectors
  (in `M`).

## Tags

Torsion, submodule, module, quotient
-/

open_locale non_zero_divisors

section defs

variables (R M : Type*) [comm_semiring R] [add_comm_monoid M] [module R M]

namespace submodule

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

/-- The torsion submodule, containing all elements `x` of `M` such that  `a • x = 0` for some
  non-zero-divisor `a` in `R`. -/
@[reducible] def torsion := torsion' R M R⁰
end submodule

namespace module

/-- A `a`-torsion module is a module where every element is `a`-torsion. -/
@[reducible] def is_torsion_by (a : R) := ∀ ⦃x : M⦄, a • x = 0

/-- A `S`-torsion module is a module where every element is `a`-torsion for some `a` in `S`. -/
@[reducible] def is_torsion' (S : Type*) [has_scalar S M] := ∀ ⦃x : M⦄, ∃ a : S, a • x = 0

/-- A torsion module is a module where every element is `a`-torsion for some non-zero-divisor `a`.
-/
@[reducible] def is_torsion := ∀ ⦃x : M⦄, ∃ a : R⁰, a • x = 0

end module

end defs

namespace submodule

open module

variables {R M : Type*}

section torsion_by

variables [comm_semiring R] [add_comm_monoid M] [module R M] (a : R)

@[simp] lemma smul_torsion_by (x : torsion_by R M a) : a • x = 0 := subtype.ext x.prop
@[simp] lemma smul_coe_torsion_by (x : torsion_by R M a) : a • (x : M) = 0 := x.prop
@[simp] lemma mem_torsion_by_iff (x : M) : x ∈ torsion_by R M a ↔ a • x = 0 := iff.rfl

/-- A `a`-torsion module is a module whose `a`-torsion submodule is the full space. -/
lemma is_torsion_by_iff_torsion_by_eq_top : is_torsion_by R M a ↔ torsion_by R M a = ⊤ :=
⟨λ h, eq_top_iff.mpr (λ _ _, @h _), λ h x, by { rw [← mem_torsion_by_iff, h], trivial }⟩

/-- The `a`-torsion submodule is a `a`-torsion module. -/
lemma torsion_by_is_torsion_by : is_torsion_by R (torsion_by R M a) a := λ _, smul_torsion_by _ _

@[simp] lemma torsion_by_torsion_by_eq_top : torsion_by R (torsion_by R M a) a = ⊤ :=
(is_torsion_by_iff_torsion_by_eq_top a).mp $ torsion_by_is_torsion_by a

end torsion_by

section quotient

variables [comm_ring R] [add_comm_group M] [module R M] (a : R)

instance : has_scalar (R ⧸ R ∙ a) (torsion_by R M a) :=
{ smul := λ b x, quotient.lift_on' b (• x) $ λ b₁ b₂ (h : b₁ - b₂ ∈ _), begin
    show b₁ • x = b₂ • x,
    obtain ⟨c, h⟩ := ideal.mem_span_singleton'.mp h,
    rw [← sub_eq_zero, ← sub_smul, ← h, mul_smul, smul_torsion_by, smul_zero],
  end }

@[simp] lemma torsion_by.mk_smul (b : R) (x : torsion_by R M a) :
  ideal.quotient.mk (R ∙ a) b • x = b • x := rfl

/-- The `a`-torsion submodule as a `(R ⧸ R∙a)`-module. -/
instance : module (R ⧸ R ∙ a) (torsion_by R M a) :=
@function.surjective.module_left _ _ (torsion_by R M a) _ _ _ _ _ (ideal.quotient.mk $ R ∙ a)
  ideal.quotient.mk_surjective (torsion_by.mk_smul _)

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

@[simps] instance : has_scalar S (torsion' R M S) :=
⟨λ s x, ⟨s • x, by { obtain ⟨x, a, h⟩ := x, use a, dsimp, rw [smul_comm, h, smul_zero] }⟩⟩
instance : distrib_mul_action S (torsion' R M S) := subtype.coe_injective.distrib_mul_action
  ((torsion' R M S).subtype).to_add_monoid_hom (λ (c : S) x, rfl)
instance : smul_comm_class S R (torsion' R M S) := ⟨λ s a x, subtype.ext $ smul_comm _ _ _⟩

/-- A `S`-torsion module is a module whose `S`-torsion submodule is the full space. -/
lemma is_torsion'_iff_torsion'_eq_top : is_torsion' M S ↔ torsion' R M S = ⊤ :=
⟨λ h, eq_top_iff.mpr (λ _ _, @h _), λ h x, by { rw [← @mem_torsion'_iff R, h], trivial }⟩

/-- The `S`-torsion submodule is a `S`-torsion module. -/
lemma torsion'_is_torsion' : is_torsion' (torsion' R M S) S := λ ⟨x, ⟨a, h⟩⟩, ⟨a, subtype.ext h⟩

@[simp] lemma torsion'_torsion'_eq_top : torsion' R (torsion' R M S) S = ⊤ :=
(is_torsion'_iff_torsion'_eq_top S).mp $ torsion'_is_torsion' S

/-- The torsion submodule of the torsion submodule (viewed as a module) is the full
torsion module. -/
@[simp] lemma torsion_torsion_eq_top : torsion R (torsion R M) = ⊤ := torsion'_torsion'_eq_top R⁰

/-- The torsion submodule is always a torsion module. -/
lemma torsion_is_torsion : module.is_torsion R (torsion R M) := torsion'_is_torsion' R⁰

end torsion'

section torsion
variables [comm_semiring R] [add_comm_monoid M] [module R M] [no_zero_divisors R] [nontrivial R]

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
    rw eq_bot_iff, rintro x ⟨a, hax⟩,
    change (a : R) • x = 0 at hax,
    cases eq_zero_or_eq_zero_of_smul_eq_zero hax with h0 h0,
    { exfalso, exact non_zero_divisors.coe_ne_zero a h0 }, { exact h0 } },
  { exact { eq_zero_or_eq_zero_of_smul_eq_zero := λ a x hax, begin
      by_cases ha : a = 0,
      { left, exact ha },
      { right, rw [← mem_bot _, ← h],
        exact ⟨⟨a, mem_non_zero_divisors_of_ne_zero ha⟩, hax⟩ }
    end } }
end
end torsion

namespace quotient_torsion

variables [comm_ring R] [add_comm_group M] [module R M]

/-- Quotienting by the torsion submodule gives a torsion-free module. -/
@[simp] lemma torsion_eq_bot : torsion R (M ⧸ torsion R M) = ⊥ :=
eq_bot_iff.mpr $ λ z, quotient.induction_on' z $ λ x ⟨a, hax⟩,
begin
  rw [quotient.mk'_eq_mk, ← quotient.mk_smul, quotient.mk_eq_zero] at hax,
  rw [mem_bot, quotient.mk'_eq_mk, quotient.mk_eq_zero],
  cases hax with b h,
  exact ⟨b * a, (mul_smul _ _ _).trans h⟩
end

instance no_zero_smul_divisors [is_domain R] : no_zero_smul_divisors R (M ⧸ torsion R M) :=
no_zero_smul_divisors_iff_torsion_eq_bot.mpr torsion_eq_bot

end quotient_torsion

end submodule

namespace add_monoid

variables {M : Type*}

theorem is_torsion_iff_is_torsion_nat [add_comm_monoid M] :
  add_monoid.is_torsion M ↔ module.is_torsion ℕ M :=
begin
  refine ⟨λ h x, _, λ h x, _⟩,
  { obtain ⟨n, h0, hn⟩ := (is_of_fin_add_order_iff_nsmul_eq_zero x).mp (h x),
    exact ⟨⟨n, mem_non_zero_divisors_of_ne_zero $ ne_of_gt h0⟩, hn⟩ },
  { rw is_of_fin_add_order_iff_nsmul_eq_zero,
    obtain ⟨n, hn⟩ := @h x,
    refine ⟨n, nat.pos_of_ne_zero (non_zero_divisors.coe_ne_zero _), hn⟩ }
end

theorem is_torsion_iff_is_torsion_int [add_comm_group M] :
  add_monoid.is_torsion M ↔ module.is_torsion ℤ M :=
begin
  refine ⟨λ h x, _, λ h x, _⟩,
  { obtain ⟨n, h0, hn⟩ := (is_of_fin_add_order_iff_nsmul_eq_zero x).mp (h x),
    exact ⟨⟨n, mem_non_zero_divisors_of_ne_zero $ ne_of_gt $ int.coe_nat_pos.mpr h0⟩,
      (coe_nat_zsmul _ _).trans hn⟩ },
  { rw is_of_fin_add_order_iff_nsmul_eq_zero,
    obtain ⟨n, hn⟩ := @h x,
    exact exists_nsmul_eq_zero_of_zsmul_eq_zero (non_zero_divisors.coe_ne_zero n) hn }
end

end add_monoid
