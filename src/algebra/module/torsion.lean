/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
import algebra.module
import linear_algebra.quotient
import ring_theory.ideal.quotient
import ring_theory.non_zero_divisors
import algebra.direct_sum.module
import group_theory.torsion
import linear_algebra.isomorphisms
import group_theory.torsion

/-!
# Torsion submodules

## Main definitions

* `torsion_of R M x` : the torsion ideal of `x`, containing all `a` such that `a • x = 0`.
* `submodule.torsion_by R M a` : the `a`-torsion submodule, containing all elements `x` of `M` such
  that `a • x = 0`.
* `submodule.torsion' R M S` : the `S`-torsion submodule, containing all elements `x` of `M` such
  that `a • x = 0` for some `a` in `S`.
* `submodule.torsion R M` : the torsion submoule, containing all elements `x` of `M` such that
  `a • x = 0` for some non-zero-divisor `a` in `R`.
* `module.is_torsion_by R M a` : the property that defines a `a`-torsion module. Similarly,
  `is_torsion'` and `is_torsion`.

## Main statements

* `quot_torsion_of_equiv_span_singleton` : isomorphism between the span of an element of `M` and
  the quotient by its torsion ideal.
* `torsion' R M S` and `torsion R M` are submodules.
* `torsion_by R M a` can be viewed as a `(R ⧸ R∙a)`-module.
* `submodule.torsion_by_is_torsion_by` : the `a`-torsion submodule is a `a`-torsion module.
  Similar lemmas for `torsion'` and `torsion`.
* `submodule.tosion_is_internal` : a `∏ i, p i`-torsion module is the internal direct sum of its
  `p i`-torsion submodules when the `p i` are pairwise coprime.
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

section
variables (R M : Type*) [semiring R] [add_comm_monoid M] [module R M]
/--The torsion ideal of `x`, containing all `a` such that `a • x = 0`.-/
@[simps] def torsion_of (x : M) : ideal R := (linear_map.to_span_singleton R M x).ker
variables {R M}
@[simp] lemma mem_torsion_of_iff (x : M) (a : R) : a ∈ torsion_of R M x ↔ a • x = 0 := iff.rfl
end

section
variables (R M : Type*) [ring R] [add_comm_group M] [module R M]
/--The span of `x` in `M` is isomorphic to `R` quotiented by the torsion ideal of `x`.-/
noncomputable def quot_torsion_of_equiv_span_singleton (x : M) :
  (R ⧸ torsion_of R M x) ≃ₗ[R] (R ∙ x) :=
(linear_map.to_span_singleton R M x).quot_ker_equiv_range.trans $
linear_equiv.of_eq _ _ (linear_map.span_singleton_eq_range R M x).symm

@[simp] lemma quot_torsion_of_equiv_span_singleton_apply_mk (x : M) (a : R) :
  quot_torsion_of_equiv_span_singleton R M x (submodule.quotient.mk a) =
    a • ⟨x, submodule.mem_span_singleton_self x⟩ := rfl
end

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

lemma torsion_by_le_torsion_by_of_dvd (a b : R) (dvd : a ∣ b) :
  torsion_by R M a ≤ torsion_by R M b :=
λ x hx, begin
  cases dvd with c h,
  change _ • _ = _, change _ • _ = _ at hx,
  rw [h, mul_comm, mul_smul, hx, smul_zero]
end

@[simp] lemma torsion_by_one : torsion_by R M 1 = ⊥ :=
eq_bot_iff.mpr (λ _ h, by { rw [mem_torsion_by_iff, one_smul] at h, exact h })

section coprime
open_locale big_operators
open dfinsupp
variables {ι : Type*} {p : ι → R} {S : finset ι} (hp : pairwise (is_coprime on λ s : S, p s))
include hp

lemma supr_torsion_by_eq_torsion_by_prod :
  (⨆ i : S, torsion_by R M (p i)) = torsion_by R M (∏ i in S, p i) :=
begin
  cases S.eq_empty_or_nonempty with h h,
  { rw [h, finset.prod_empty, torsion_by_one],
    convert supr_of_empty _, exact subtype.is_empty_false },
  apply le_antisymm,
  { apply supr_le _, rintro ⟨i, is⟩,
    exact torsion_by_le_torsion_by_of_dvd _ _ (finset.dvd_prod_of_mem p is) },
  { intros x hx, classical, rw mem_supr_iff_exists_dfinsupp',
    cases (exists_sum_eq_one_iff_pairwise_coprime h).mpr hp with f hf,
    use equiv_fun_on_fintype.inv_fun (λ i, ⟨(f i * ∏ j in S \ {i}, p j) • x, begin
      obtain ⟨i, is⟩ := i,
      change p i • (f i * ∏ j in S \ {i}, _) • _ = _, change _ • _ = _ at hx,
      rw [smul_smul, mul_comm, mul_assoc, mul_smul, ← finset.prod_eq_prod_diff_singleton_mul is,
        hx, smul_zero]
    end⟩),
    simp only [equiv.inv_fun_as_coe, sum_eq_sum_fintype, coe_eq_zero, eq_self_iff_true,
      implies_true_iff, finset.univ_eq_attach, equiv_fun_on_fintype_apply],
    change ∑ i : S, ((f i * ∏ j in S \ {i}, p j) • x) = x,
    have : ∑ i : S, _ = _ := S.sum_finset_coe (λ i, f i * ∏ j in S \ {i}, p j),
    rw [← finset.sum_smul, this, hf, one_smul] }
end

lemma torsion_by_independent : complete_lattice.independent (λ i : S, torsion_by R M (p i)) :=
λ i, begin
  classical,
  dsimp, rw [disjoint_iff, eq_bot_iff], intros x hx,
  rw submodule.mem_inf at hx, obtain ⟨hxi, hxj⟩ := hx,
  have hxi : p i • x = 0 := hxi,
  rw mem_supr_iff_exists_dfinsupp' at hxj, cases hxj with f hf,
  obtain ⟨b, c, h1⟩ := pairwise_coprime_iff_coprime_prod.mp hp i i.2,
  rw [mem_bot, ← one_smul _ x, ← h1, add_smul],
  convert (zero_add (0:M)),
  { rw [mul_smul, hxi, smul_zero] },
  { rw [← hf, smul_sum, sum_eq_zero],
    intro j, by_cases ji : j = i,
    { convert smul_zero _,
      rw ← mem_bot _, convert coe_mem (f j),
      symmetry, rw supr_eq_bot, intro hj',
      exfalso, exact hj' ji },
    { have hj' : ↑j ∈ S \ {i},
      { rw finset.mem_sdiff, refine ⟨j.2, λ hj', ji _⟩, ext, rw ← finset.mem_singleton, exact hj' },
      rw [finset.prod_eq_prod_diff_singleton_mul hj', ← mul_assoc, mul_smul],
      have : (⨆ (H : ¬j = i), torsion_by R M (p j)) ≤ torsion_by R M (p j) := supr_const_le,
      have : _ • _ = _ := this (coe_mem _),
      rw [this, smul_zero] } }
end
end coprime
end torsion_by

section needs_group
variables [comm_ring R] [add_comm_group M] [module R M] (a : R)

section
open_locale big_operators
variables {ι : Type*} {p : ι → R} {S : finset ι} (hp : pairwise (is_coprime on λ s : S, p s))
include hp

/--If the `p i` are pairwise coprime, a `∏ i, p i`-torsion module is the internal direct sum of
its `p i`-torsion submodules.-/
lemma torsion_is_internal [decidable_eq ι] (hM : torsion_by R M (∏ i in S, p i) = ⊤) :
  direct_sum.submodule_is_internal (λ i : S, torsion_by R M (p i)) :=
direct_sum.submodule_is_internal_of_independent_of_supr_eq_top
  (torsion_by_independent hp) (by { rw ← hM, exact supr_torsion_by_eq_torsion_by_prod hp})
end

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

end needs_group

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

lemma is_torsion'_powers_iff (p : R) :
  is_torsion' M (submonoid.powers p) ↔ ∀ x : M, ∃ n : ℕ, p ^ n • x = 0 :=
⟨λ h x, let ⟨⟨a, ⟨n, rfl⟩⟩, hx⟩ := @h x in ⟨n, hx⟩,
λ h x, let ⟨n, hn⟩ := h x in ⟨⟨_, ⟨n, rfl⟩⟩, hn⟩⟩

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

namespace ideal.quotient

open submodule

lemma torsion_by_eq_span_singleton {R : Type*} [comm_ring R] (a b : R) (ha : a ∈ R⁰) :
  torsion_by R (R ⧸ R ∙ a * b) a = R ∙ (mk _ b) :=
begin
  ext x, rw [mem_torsion_by_iff, mem_span_singleton],
  obtain ⟨x, rfl⟩ := mk_surjective x, split; intro h,
  { rw [← mk_eq_mk, ← quotient.mk_smul, quotient.mk_eq_zero, mem_span_singleton] at h,
    obtain ⟨c, h⟩ := h, rw [smul_eq_mul, smul_eq_mul, mul_comm, mul_assoc,
      mul_cancel_left_mem_non_zero_divisor ha, mul_comm] at h,
    use c, rw [← h, ← mk_eq_mk, ← quotient.mk_smul, smul_eq_mul, mk_eq_mk] },
  { obtain ⟨c, h⟩ := h,
    rw [← h, smul_comm, ← mk_eq_mk, ← quotient.mk_smul,
      (quotient.mk_eq_zero _).mpr $ mem_span_singleton_self _, smul_zero] }
end
end ideal.quotient

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
