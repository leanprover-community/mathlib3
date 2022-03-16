/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
import algebra.module
import linear_algebra.quotient
import ring_theory.ideal.quotient
import ring_theory.non_zero_divisors
import ring_theory.coprime.pairwise
import algebra.direct_sum.module
import group_theory.torsion
import linear_algebra.isomorphisms

/-!
# Torsion submodules

## Main definitions

* `submodule.torsion_by R M a` : the `a`-torsion submodule, containing all elements `x` of `M` such
  that `a • x = 0`.
* `submodule.torsion' R M S` : the `S`-torsion submodule, containing all elements `x` of `M` such
  that `a • x = 0` for some `a` in `S`.
* `submodule.torsion R M` : the torsion submoule, containing all elements `x` of `M` such that
  `a • x = 0` for some non-zero-divisor `a` in `R`.
* `module.is_torsion R M` : the property that defines a torsion module.

## Main statements

* `torsion' R M S` and `torsion R M` are submodules.
* `torsion_by R M a` can be viewed as a `(R ⧸ R∙a)`-module.
* `submodule.torsion_by_torsion_by_eq_top` : the `a`-torsion submodule of the `a`-torsion submodule
  (viewed as a module) is the full `a`-torsion module. Similar lemmas for `torsion'` and `torsion`.
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

namespace dfinsupp /- to move to linear_algebra.basic -/

variables {α : Type*} {β : α → Type*} {R : Type*} {M : Type*}
  [∀ i : α, has_zero (β i)] [monoid R] [add_comm_monoid M] [distrib_mul_action R M]
  {v : Π₀ (i : α), β i} {c : R} {h : Π (i : α), β i → M}
variables [decidable_eq α] [Π (i : α) (x : β i), decidable (x ≠ 0)]

lemma smul_sum : c • (v.sum h) = v.sum (λa b, c • h a b) := finset.smul_sum

lemma sum_eq_zero (hyp : ∀ i : α, h i (v i) = 0) : v.sum h = 0 := finset.sum_eq_zero $ λ i hi, hyp i

end dfinsupp

section
variables (R M : Type*) [semiring R] [add_comm_monoid M] [module R M]
@[simps] def torsion_of (x : M) : ideal R := (linear_map.to_span_singleton R M x).ker
variables {R M}
@[simp] lemma mem_torsion_of_iff (x : M) (a : R) : a ∈ torsion_of R M x ↔ a • x = 0 := iff.rfl
end
section
variables {R M : Type*} [ring R] [add_comm_group M] [module R M]
noncomputable def quot_torsion_of_equiv_span_singleton (x : M) :
(R ⧸ torsion_of R M x) ≃ₗ[R] (R ∙ x) :=
by { convert (linear_map.to_span_singleton R M x).quot_ker_equiv_range,
     repeat { exact linear_map.span_singleton_eq_range R M x } }
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

/-- A torsion module is a module whose torsion submodule is the full space. -/
@[reducible] def module.is_torsion := submodule.torsion R M = ⊤
end defs

namespace submodule
variables {R M : Type*}
section torsion_by
variables [comm_semiring R] [add_comm_monoid M] [module R M]

@[simp] lemma smul_torsion_by (a : R) (x : torsion_by R M a) : a • x = 0 := subtype.ext x.prop
@[simp] lemma smul'_torsion_by (a : R) (x : torsion_by R M a) : a • (x:M) = 0 := x.prop
@[simp] lemma mem_torsion_by_iff (a : R) (x : M) : x ∈ torsion_by R M a ↔ a • x = 0 := iff.rfl
@[simp] lemma torsion_by_one : torsion_by R M 1 = ⊥ :=
eq_bot_iff.mpr (λ _ (h : _ • _ = _), by { rw one_smul at h, exact h })

/-- The `a`-torsion submodule of the `a`-torsion submodule (viewed as a module) is the full
`a`-torsion module. -/
@[simp] lemma torsion_by_torsion_by_eq_top (a : R) : torsion_by R (torsion_by R M a) a = ⊤ :=
eq_top_iff.mpr (λ _ _, smul_torsion_by _ _)

lemma torsion_le_torsion_of_dvd (a b : R) (dvd : a ∣ b) : torsion_by R M a ≤ torsion_by R M b :=
λ x hx, begin
  cases dvd with c h,
  change _ • _ = _, change _ • _ = _ at hx,
  rw [h, mul_comm, mul_smul, hx, smul_zero]
end

section coprime
open_locale big_operators
open dfinsupp
variables {ι : Type*} {p : ι → R} {S : finset ι} (hp : pairwise (is_coprime on λ s : S, p s))
include hp
lemma supr_torsion_by_eq_torsion_by_prod :
  (⨆ i : S, torsion_by R M (p i)) = torsion_by R M (∏ i in S, p i) :=
begin
  cases S.eq_empty_or_nonempty,
  { rw [h, finset.prod_empty, torsion_by_one],
    convert supr_of_empty _, exact subtype.is_empty_false },
  apply le_antisymm,
  { apply supr_le _, rintro ⟨i, is⟩,
    exact torsion_le_torsion_of_dvd _ _ (finset.dvd_prod_of_mem p is) },
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
      have : (f j : M) ∈ torsion_by R M (p j) := this (coe_mem _),
      have : _ • _ = _ := this,
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
ideal.quotient.mk_surjective.module_left _ (torsion_by.mk_smul _)

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

instance : has_scalar S (torsion' R M S) :=
⟨λ s x, ⟨s • x, by { obtain ⟨x, a, h⟩ := x, use a, dsimp, rw [smul_comm, h, smul_zero] }⟩⟩
instance : distrib_mul_action S (torsion' R M S) := subtype.coe_injective.distrib_mul_action
  ((torsion' R M S).subtype).to_add_monoid_hom (λ (c : S) x, rfl)
instance : smul_comm_class S R (torsion' R M S) := ⟨λ s a x, subtype.ext $ smul_comm _ _ _⟩

/-- The `S`-torsion submodule of the `S`-torsion submodule (viewed as a module) is the full
`S`-torsion module. -/
@[simp] lemma torsion'_torsion'_eq_top : torsion' R (torsion' R M S) S = ⊤ :=
eq_top_iff.mpr (λ ⟨x, ⟨a, h⟩⟩ _, ⟨a, subtype.ext h⟩)
/-- The torsion submodule of the torsion submodule (viewed as a module) is the full
torsion module. -/
@[simp] lemma torsion_torsion_eq_top : torsion R (torsion R M) = ⊤ := torsion'_torsion'_eq_top R⁰
/-- The torsion submodule is always a torsion module. -/
lemma torsion_is_torsion : module.is_torsion R (torsion R M) := torsion_torsion_eq_top

end torsion'

section torsion
variables [comm_semiring R] [add_comm_monoid M] [module R M]
lemma mem_torsion_of_is_torsion (h : module.is_torsion R M) (x : M) : x ∈ torsion R M :=
by convert mem_top

variables [no_zero_divisors R] [nontrivial R]

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

section ℕ_torsion
variables {M : Type*} [add_comm_monoid M]

theorem is_torsion_iff_torsion_eq_top : add_monoid.is_torsion M ↔ module.is_torsion ℕ M :=
begin
  refine ⟨λ h, eq_top_iff.mpr $ λ x _, _, λ h x, _⟩,
  { obtain ⟨n, h0, hn⟩ := (is_of_fin_add_order_iff_nsmul_eq_zero x).mp (h x),
    exact ⟨⟨n, mem_non_zero_divisors_of_ne_zero (ne_of_gt h0)⟩, hn⟩ },
  { rw is_of_fin_add_order_iff_nsmul_eq_zero,
    obtain ⟨n, hn⟩ := submodule.mem_torsion_of_is_torsion h x,
    refine ⟨n, nat.pos_of_ne_zero (non_zero_divisors.coe_ne_zero _), hn⟩ }
end
end ℕ_torsion
