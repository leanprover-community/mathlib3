/-
Copyright (c) 2020 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/

import ring_theory.principal_ideal_domain
import order.conditionally_complete_lattice
import ring_theory.multiplicity
import ring_theory.valuation.basic
import ring_theory.ideal.over
import ring_theory.fractional_ideal

/-!
# Discrete valuation rings

This file defines discrete valuation rings (DVRs) and develops a basic interface
for them.

## Important definitions

There are various definitions of a DVR in the literature; we define a DVR to be a local PID
which is not a field (the first definition in Wikipedia) and prove that this is equivalent
to being a PID with a unique non-zero prime ideal (the definition in Serre's
book "Local Fields").

Let R be an integral domain, assumed to be a principal ideal ring and a local ring.

* `discrete_valuation_ring R` : a predicate expressing that R is a DVR

### Definitions

* `add_val R : R → ℕ` : the additive valuation on a DVR (sending 0 to 0 rather than the
     mathematically correct +∞).
TODO -- the multiplicative valuation, taking values in something
  like `with_zero (multiplicative ℤ)`?

## Implementation notes

It's a theorem that an element of a DVR is a uniformizer if and only if it's irreducible.
We do not hence define `uniformizer` at all, because we can use `irreducible` instead.

## Tags

discrete valuation ring
-/

open_locale classical

universe u

open ideal local_ring

/-- An integral domain is a *discrete valuation ring* (DVR) if it's a local PID which
  is not a field. -/
class discrete_valuation_ring (R : Type u) [integral_domain R]
  extends is_principal_ideal_ring R, local_ring R : Prop :=
(not_a_field' : maximal_ideal R ≠ ⊥)

namespace discrete_valuation_ring

variables (R : Type u) [integral_domain R] [discrete_valuation_ring R]

lemma not_a_field : maximal_ideal R ≠ ⊥ := not_a_field'

variable {R}

open principal_ideal_ring

/-- An element of a DVR is irreducible iff it is a uniformizer, that is, generates the
  maximal ideal of R -/
theorem irreducible_iff_uniformizer (ϖ : R) :
  irreducible ϖ ↔ maximal_ideal R = ideal.span {ϖ} :=
⟨λ hϖ, (eq_maximal_ideal (is_maximal_of_irreducible hϖ)).symm,
begin
  intro h,
  have h2 : ¬(is_unit ϖ) := show ϖ ∈ maximal_ideal R,
    from h.symm ▸ submodule.mem_span_singleton_self ϖ,
  refine ⟨h2, _⟩,
  intros a b hab,
  by_contra h,
  push_neg at h,
  obtain ⟨ha : a ∈ maximal_ideal R, hb : b ∈ maximal_ideal R⟩ := h,
  rw h at ha hb,
  rw mem_span_singleton' at ha hb,
  rcases ha with ⟨a, rfl⟩,
  rcases hb with ⟨b, rfl⟩,
  rw (show a * ϖ * (b * ϖ) = ϖ * (ϖ * (a * b)), by ring) at hab,
  have h3 := eq_zero_of_mul_eq_self_right _ hab.symm,
  { apply not_a_field R,
    simp [h, h3] },
  { intro hh, apply h2,
    refine is_unit_of_dvd_one ϖ _,
    use a * b, exact hh.symm }
end⟩

variable (R)

/-- Uniformisers exist in a DVR -/
theorem exists_irreducible : ∃ ϖ : R, irreducible ϖ :=
by {simp_rw [irreducible_iff_uniformizer],
    exact (is_principal_ideal_ring.principal $ maximal_ideal R).principal}

/-- an integral domain is a DVR iff it's a PID with a unique non-zero prime ideal -/
theorem iff_pid_with_one_nonzero_prime (R : Type u) [integral_domain R] :
  discrete_valuation_ring R ↔ is_principal_ideal_ring R ∧ ∃! P : ideal R, P ≠ ⊥ ∧ is_prime P :=
begin
  split,
  { intro RDVR,
    rcases id RDVR with ⟨RPID, Rlocal, Rnotafield⟩,
    split, assumption,
    resetI,
    use local_ring.maximal_ideal R,
    split, split,
    { assumption },
    { apply_instance } ,
    { rintro Q ⟨hQ1, hQ2⟩,
      obtain ⟨q, rfl⟩ := (is_principal_ideal_ring.principal Q).1,
      have hq : q ≠ 0,
      { rintro rfl,
        apply hQ1,
        simp },
      erw span_singleton_prime hq at hQ2,
      replace hQ2 := irreducible_of_prime hQ2,
      rw irreducible_iff_uniformizer at hQ2,
      exact hQ2.symm } },
  { rintro ⟨RPID, Punique⟩,
    haveI : local_ring R := local_of_unique_nonzero_prime R Punique,
    refine {not_a_field' := _},
    rcases Punique with ⟨P, ⟨hP1, hP2⟩, hP3⟩,
    have hPM : P ≤ maximal_ideal R := le_maximal_ideal (hP2.1),
    intro h, rw [h, le_bot_iff] at hPM, exact hP1 hPM }
end

lemma associated_of_irreducible {a b : R} (ha : irreducible a) (hb : irreducible b) :
  associated a b :=
begin
  rw irreducible_iff_uniformizer at ha hb,
  rw [←span_singleton_eq_span_singleton, ←ha, hb],
end

end discrete_valuation_ring

namespace discrete_valuation_ring

variable (R : Type*)

/-- Alternative characterisation of discrete valuation rings. -/
def has_unit_mul_pow_irreducible_factorization [integral_domain R] : Prop :=
∃ p : R, irreducible p ∧ ∀ {x : R}, x ≠ 0 → ∃ (n : ℕ), associated (p ^ n) x

namespace has_unit_mul_pow_irreducible_factorization

variables {R} [integral_domain R] (hR : has_unit_mul_pow_irreducible_factorization R)
include hR

lemma unique_irreducible ⦃p q : R⦄ (hp : irreducible p) (hq : irreducible q) :
  associated p q :=
begin
  rcases hR with ⟨ϖ, hϖ, hR⟩,
  suffices : ∀ {p : R} (hp : irreducible p), associated p ϖ,
  { apply associated.trans (this hp) (this hq).symm, },
  clear hp hq p q,
  intros p hp,
  obtain ⟨n, hn⟩ := hR hp.ne_zero,
  have : irreducible (ϖ ^ n) := irreducible_of_associated hn.symm hp,
  rcases lt_trichotomy n 1 with (H|rfl|H),
  { obtain rfl : n = 0, { clear hn this, revert H n, exact dec_trivial },
    simpa only [not_irreducible_one, pow_zero] using this, },
  { simpa only [pow_one] using hn.symm, },
  { obtain ⟨n, rfl⟩ : ∃ k, n = 1 + k + 1 := nat.exists_eq_add_of_lt H,
    rw pow_succ at this,
    rcases this.2 _ _ rfl with H0|H0,
    { exact (hϖ.not_unit H0).elim, },
    { rw [add_comm, pow_succ] at H0,
      exact (hϖ.not_unit (is_unit_of_mul_is_unit_left H0)).elim } }
end

/-- An integral domain in which there is an irreducible element `p`
such that every nonzero element is associated to a power of `p` is a unique factorization domain.
See `discrete_valuation_ring.of_has_unit_mul_pow_irreducible_factorization`. -/
theorem to_unique_factorization_monoid : unique_factorization_monoid R :=
let p := classical.some hR in
let spec := classical.some_spec hR in
unique_factorization_monoid.of_exists_prime_factors $ λ x hx,
begin
  use multiset.repeat p (classical.some (spec.2 hx)),
  split,
  { intros q hq,
    have hpq := multiset.eq_of_mem_repeat hq,
    rw hpq,
    refine ⟨spec.1.ne_zero, spec.1.not_unit, _⟩,
    intros a b h,
    by_cases ha : a = 0,
    { rw ha, simp only [true_or, dvd_zero], },
    by_cases hb : b = 0,
    { rw hb, simp only [or_true, dvd_zero], },
    obtain ⟨m, u, rfl⟩ := spec.2 ha,
    rw [mul_assoc, mul_left_comm, is_unit.dvd_mul_left _ _ _ (is_unit_unit _)] at h,
    rw is_unit.dvd_mul_right (is_unit_unit _),
    by_cases hm : m = 0,
    { simp only [hm, one_mul, pow_zero] at h ⊢, right, exact h },
    left,
    obtain ⟨m, rfl⟩ := nat.exists_eq_succ_of_ne_zero hm,
    apply dvd_mul_of_dvd_left (dvd_refl _) _ },
  { rw [multiset.prod_repeat], exact (classical.some_spec (spec.2 hx)), }
end

omit hR

lemma of_ufd_of_unique_irreducible [unique_factorization_monoid R]
  (h₁ : ∃ p : R, irreducible p)
  (h₂ : ∀ ⦃p q : R⦄, irreducible p → irreducible q → associated p q) :
  has_unit_mul_pow_irreducible_factorization R :=
begin
  obtain ⟨p, hp⟩ := h₁,
  refine ⟨p, hp, _⟩,
  intros x hx,
  cases wf_dvd_monoid.exists_factors x hx with fx hfx,
  refine ⟨fx.card, _⟩,
  have H := hfx.2,
  rw ← associates.mk_eq_mk_iff_associated at H ⊢,
  rw [← H, ← associates.prod_mk, associates.mk_pow, ← multiset.prod_repeat],
  congr' 1,
  symmetry,
  rw multiset.eq_repeat,
  simp only [true_and, and_imp, multiset.card_map, eq_self_iff_true,
    multiset.mem_map, exists_imp_distrib],
  rintros _ q hq rfl,
  rw associates.mk_eq_mk_iff_associated,
  apply h₂ (hfx.1 _ hq) hp,
end

end has_unit_mul_pow_irreducible_factorization

lemma aux_pid_of_ufd_of_unique_irreducible
  (R : Type u) [integral_domain R] [unique_factorization_monoid R]
  (h₁ : ∃ p : R, irreducible p)
  (h₂ : ∀ ⦃p q : R⦄, irreducible p → irreducible q → associated p q) :
  is_principal_ideal_ring R :=
begin
  constructor,
  intro I,
  by_cases I0 : I = ⊥, { rw I0, use 0, simp only [set.singleton_zero, submodule.span_zero], },
  obtain ⟨x, hxI, hx0⟩ : ∃ x ∈ I, x ≠ (0:R) := I.ne_bot_iff.mp I0,
  obtain ⟨p, hp, H⟩ :=
    has_unit_mul_pow_irreducible_factorization.of_ufd_of_unique_irreducible h₁ h₂,
  have ex : ∃ n : ℕ, p ^ n ∈ I,
  { obtain ⟨n, u, rfl⟩ := H hx0,
    refine ⟨n, _⟩,
    simpa only [units.mul_inv_cancel_right] using @ideal.mul_mem_right _ _ I _ ↑u⁻¹ hxI, },
  constructor,
  use p ^ (nat.find ex),
  show I = ideal.span _,
  apply le_antisymm,
  { intros r hr,
    by_cases hr0 : r = 0,
    { simp only [hr0, submodule.zero_mem], },
    obtain ⟨n, u, rfl⟩ := H hr0,
    simp only [mem_span_singleton, is_unit_unit, is_unit.dvd_mul_right],
    apply pow_dvd_pow,
    apply nat.find_min',
    simpa only [units.mul_inv_cancel_right] using @ideal.mul_mem_right _ _ I _ ↑u⁻¹ hr, },
  { erw submodule.span_singleton_le_iff_mem,
    exact nat.find_spec ex, },
end

/--
A unique factorization domain with at least one irreducible element
in which all irreducible elements are associated
is a discrete valuation ring.
-/
lemma of_ufd_of_unique_irreducible {R : Type u} [integral_domain R] [unique_factorization_monoid R]
  (h₁ : ∃ p : R, irreducible p)
  (h₂ : ∀ ⦃p q : R⦄, irreducible p → irreducible q → associated p q) :
  discrete_valuation_ring R :=
begin
  rw iff_pid_with_one_nonzero_prime,
  haveI PID : is_principal_ideal_ring R := aux_pid_of_ufd_of_unique_irreducible R h₁ h₂,
  obtain ⟨p, hp⟩ := h₁,
  refine ⟨PID, ⟨ideal.span {p}, ⟨_, _⟩, _⟩⟩,
  { rw submodule.ne_bot_iff,
    refine ⟨p, ideal.mem_span_singleton.mpr (dvd_refl p), hp.ne_zero⟩, },
  { rwa [ideal.span_singleton_prime hp.ne_zero,
        ← unique_factorization_monoid.irreducible_iff_prime], },
  { intro I,
    rw ← submodule.is_principal.span_singleton_generator I,
    rintro ⟨I0, hI⟩,
    apply span_singleton_eq_span_singleton.mpr,
    apply h₂ _ hp,
    erw [ne.def, span_singleton_eq_bot] at I0,
    rwa [unique_factorization_monoid.irreducible_iff_prime, ← ideal.span_singleton_prime I0], },
end

/--
An integral domain in which there is an irreducible element `p`
such that every nonzero element is associated to a power of `p`
is a discrete valuation ring.
-/
lemma of_has_unit_mul_pow_irreducible_factorization {R : Type u} [integral_domain R]
  (hR : has_unit_mul_pow_irreducible_factorization R) :
  discrete_valuation_ring R :=
begin
  letI : unique_factorization_monoid R := hR.to_unique_factorization_monoid,
  apply of_ufd_of_unique_irreducible _ hR.unique_irreducible,
  unfreezingI { obtain ⟨p, hp, H⟩ := hR, exact ⟨p, hp⟩, },
end



lemma aux_prime_of_principal_prime_ideal {R : Type u} [comm_ring R] {I : ideal R} {p : R}
  (Hprime : I.is_prime) (Hnon_zero : I ≠ ⊥) (Hprincipal : I = ideal.span {p}) : prime p :=
begin
  let Hproper := Hprime.1,
  let Hprod := Hprime.2,
  split,
  {
  intro hpzero,
  apply Hnon_zero,
  rw Hprincipal,
  rw hpzero,
  rw span_singleton_eq_bot,
  }, split,
  {
    intro hpunit,
    apply Hproper,
    rw Hprincipal,
    rw span_singleton_eq_top,
    exact hpunit,
  },{
    intros a b,
    rw <- mem_span_singleton,
    rw <- mem_span_singleton,
    rw <- mem_span_singleton,
    rw <- Hprincipal,
    exact Hprod,
  }
end

/--
A local noetherian integral domain `R` such that the maximal ideal of `R` is principal
and the unique non-zero prime ideal (i.e. `R` has Krull dimension 1)
is a discrete valuation ring.
-/
lemma of_principal_unique_prime_ideal {R : Type u}
  [integral_domain R] [local_ring R] [Inoetherian : is_noetherian_ring R]
  (Hprincipal : ∃ p: R, maximal_ideal R = ideal.span {p})
  (Hunique : ∀ I ≠ (⊥ : ideal R), I.is_prime → I = maximal_ideal R)
  (Hnon_zero : maximal_ideal R ≠ ⊥) :
  discrete_valuation_ring R :=
begin
  let m := maximal_ideal R,
  apply of_has_unit_mul_pow_irreducible_factorization,
  cases Hprincipal with p Hprincipal,
  use p,
  split,
  apply irreducible_of_prime,
  have hmprime : is_prime m,
  apply is_maximal.is_prime,
  exact maximal_ideal.is_maximal R,
  exact aux_prime_of_principal_prime_ideal hmprime Hnon_zero Hprincipal,

  intros x hxnon_zero,
  let S : set (ideal R) := {I : ideal R | ∃ y : R, I = ideal.span {y} ∧ ∃ n : ℕ, associated (y * p^n) x},
  have hmax : ∃ J ∈ S, ∀ I ∈ S, J ≤ I → I = J,
  {
  apply set_has_maximal_iff_noetherian.2,
  exact Inoetherian,
  use (ideal.span {x}),
  split,
  split,
  trivial,
  use 0,
  simp,
  },

  have hpprime : prime p,
  have hmprime : is_prime m,
  apply is_maximal.is_prime,
  exact maximal_ideal.is_maximal R,
  exact aux_prime_of_principal_prime_ideal hmprime Hnon_zero Hprincipal,

  cases hmax with J hJmax,
  cases hJmax with HJS H,
  have hJtop : J = ⊤,
  {
    by_contradiction hnJtop,
    cases exists_le_maximal J hnJtop with m' hm',
    have h4 : m' = m,
    cases (maximal_ideal_unique R) with m'' h,
    rw (h.2 m' hm'.1),
    rw (h.2 m),
    exact maximal_ideal.is_maximal R,
    cases HJS with y1 hy1,
    have hdiv : ∃ y2 : R, y2 * p = y1,
    {
      rw <- mem_span_singleton',
      rw <- Hprincipal,
      have h5 : maximal_ideal R = m, trivial,
      rw h5,
      rw <- h4,
      apply hm'.2,
      rw hy1.1,
      apply subset_span,
      simp, -- y1 in {y1}
    },
    cases hdiv with y2 hy2,
    let J2 : ideal R := ideal.span {y2},
    have hJ2S : J2 ∈ S,
    {
      use y2,
      split,
      trivial,
      cases hy1.2 with n hn,
      use n + 1,
      rw <- hy2 at hn,
      rw pow_succ,
      rw <- mul_assoc,
      exact hn,
    },
    have hJineq : J ≤ J2,
    rw hy1.1,
    intros t ht,
    rw mem_span_singleton at ht,
    rw <- hy2 at ht,
    rw mem_span_singleton,
    apply dvd_of_mul_right_dvd,
    exact ht,
    have Heq : span {y2} = span {y1},
    rw <- hy1.1,
    exact H J2 hJ2S hJineq,
    rw span_singleton_eq_span_singleton at Heq,
    rw <- hy2 at Heq,
    have h7 : associated (y2*1) (y2*p), simp, exact Heq,
    have h8 : associated 1 p,
    apply associated_mul_left_cancel h7, trivial,
    cases hy1.2 with n hn,
    have h10 : y1*p^n ≠ 0,
    rw ne_zero_iff_of_associated hn,
    exact hxnon_zero,
    have hy1ne_zero : y1 ≠ 0,
    intro hzero,
    apply h10,
    rw hzero,
    simp,
    intro hy2zero,
    apply hy1ne_zero,
    rw <- hy2,
    rw hy2zero,
    simp,

    apply hpprime.2.1,
    rw <- is_unit_iff_of_associated h8,
    simp,
  },
  cases HJS with y hy,
  cases hy.2 with n hn,
  use n,
  have hn' : associated (y * p^n) (1 * x), simp, exact hn,
  apply associated_mul_left_cancel hn',
  rw <- span_singleton_eq_span_singleton,
  rw <- hy.1,
  rw hJtop,
  rw <- span_singleton_one,
  trivial,
  have h9 : y*p^n ≠ 0,
  rw ne_zero_iff_of_associated hn,
  exact hxnon_zero,
  intro hzero,
  apply h9,
  rw hzero,
  simp,
end

lemma aux_nakayama_ideals_noetherian_local_ring {R : Type u}
  [comm_ring R] [local_ring R] [is_noetherian_ring R]
  {I : ideal R} (H : I ≤ (maximal_ideal R)*I) : I = ⊥ :=
begin
  have H1 : ∃ r : R, r - 1 ∈ maximal_ideal R ∧ ∀ x ∈ I, r * x = (0 : R),
  apply submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul,
  exactI is_noetherian.noetherian I,
  exact H,
  cases H1 with r hr,
  have hunit : is_unit r,
  cases is_unit_or_is_unit_one_sub_self r with htrivial hneg,
  exact htrivial,
  by_contradiction,
  have hmtop : maximal_ideal R = ⊤,
  apply eq_top_of_is_unit_mem (maximal_ideal R) hr.1,
  have hassoc : associated (r - 1) (1 - r),
  use (-1),
  simp,
  rw is_unit_iff_of_associated hassoc,
  exact hneg,
  apply (maximal_ideal.is_maximal R).1,
  exact hmtop,
  rw <- submodule.annihilator_eq_top_iff,
  have hannihilate : r ∈ submodule.annihilator I,
  rw submodule.mem_annihilator,
  exact hr.2,
  apply eq_top_of_is_unit_mem (submodule.annihilator I) hannihilate,
  exact hunit,
end

lemma aux_mem_pow {R : Type u} [comm_ring R] {I : ideal R} {a : R}
  (H : a ∈ I) (n : ℕ) : a^n ∈ I^n :=
begin
  induction n,
  simp,
  rw pow_succ,
  rw pow_succ,
  apply mul_mem_mul,
  exact H,
  exact n_ih,
end


lemma aux_noetherian_radical_pow {R : Type u} [comm_ring R] [is_noetherian_ring R]
  (I : ideal R) : ∃ n : ℕ, (radical I)^n ≤ I :=
begin
  sorry,
end

lemma aux_mem_of_ideal_ne_zero {R : Type u} [comm_ring R] {I : ideal R} (H : I ≠ ⊥)
  : ∃ a : R, a ∈ I ∧ a ≠ (0 : R) :=
begin
    by_contradiction,
    apply H,
    rw not_exists at h,
    ext x,
    rw mem_bot,
    split,
    have H1 := not_and.1 (h x),
    rw not_not at H1,
    exact H1,
    intro hx,
    rw hx,
    exact ideal.zero_mem I,
end

lemma aux_integral_domain_not_nilpotent {R : Type u} [integral_domain R]
  {I : ideal R} (H : I ≠ ⊥) : ∀ n : ℕ, I^n ≠ ⊥ :=
begin
    intros n hn,
    cases (aux_mem_of_ideal_ne_zero H) with a ha,
    apply ha.2,
    rw <- mem_bot,
    apply is_prime.mem_of_pow_mem bot_prime n,
    rw <- hn,
    apply aux_mem_pow,
    exact ha.1,
end

lemma aux_noetherian_local_dim_one_min_pow_maximal_ideal {R : Type u} [integral_domain R] [local_ring R]
  [Inoetherian : is_noetherian_ring R] {a : R}
  (Hne_zero : a ≠ 0) (Hin_max : a ∈ maximal_ideal R)
  (Hprime_unique : ∀ p ≠ (⊥ : ideal R), p.is_prime → p = maximal_ideal R)
  (Hprime_ne_zero : maximal_ideal R ≠ ⊥)
  : ∃ k : ℕ, (maximal_ideal R)^(k+1) ≤ ideal.span {a} ∧ ¬ ((maximal_ideal R)^k ≤ ideal.span {a}) :=
begin
  let m:= maximal_ideal R,

  have hmelement := aux_mem_of_ideal_ne_zero Hprime_ne_zero,
  have hnonilpotent := aux_integral_domain_not_nilpotent Hprime_ne_zero,

  have hnak : ∀ n : ℕ, m^n ≠ m^(n+1),
  {
    intros n h,
    apply hnonilpotent n,
    rw pow_succ at h,
    apply aux_nakayama_ideals_noetherian_local_ring,
    exact le_of_eq h,
  },

  have hradical : radical (ideal.span {a}) = m,
  {
    rw radical_eq_Inf,
    have h : {m} = {J : ideal R | span {a} ≤ J ∧ J.is_prime},
    ext J,
    rw set.mem_singleton_iff,
    split,
    intro hJ,
    rw hJ,
    split,
    rw span_le,
    rw set.singleton_subset_iff,
    exact Hin_max,
    apply is_maximal.is_prime,
    exact maximal_ideal.is_maximal R,
    intro hJ,
    apply Hprime_unique,
    intro Jbot,
    apply Hne_zero,
    rw <- mem_bot,
    rw <- Jbot,
    have h := hJ.1,
    rw span_le at h,
    rw set.singleton_subset_iff at h,
    exact h,
    exact hJ.2,
    rw <- h,
    exact Inf_singleton,
  },

  have Hpowle : ∃ k : ℕ, m^k ≤ ideal.span {a},
  rw <- hradical,
  exact aux_noetherian_radical_pow (ideal.span {a}),
  let S := {J : ideal R | ∃ k : ℕ, J = m^k ∧ m^k ≤ ideal.span {a}},
    have Hnoeth : ∀ a : set $ ideal R, a.nonempty → ∃ M' ∈ a, ∀ I ∈ a, M' ≤ I → I = M',
    rw set_has_maximal_iff_noetherian,
    exact Inoetherian,
    have hnonempty : S.nonempty,
    cases Hpowle with k hk,
    use m^k,
    use k,
    split,
    refl,
    exact hk,
    cases Hnoeth S hnonempty with J hJ,
    cases hJ with hJin hJ,
    cases hJin with k hk,
    have hkne_zero : k ≠ 0,
    {
      intro hkzero,
      rw hkzero at hk,
      apply (maximal_ideal.is_maximal R).1,
      rw eq_top_iff,
      have h3 : m^0 = ⊤, simp,
      rw <- h3,
      refine le_trans hk.2 _,
      rw span_le,
      rw set.singleton_subset_iff,
      exact Hin_max,
    },

    have hkpos : 1 ≤ k,
    rw <- nat.lt_iff_add_one_le,
    rw nat.pos_iff_ne_zero,
    exact hkne_zero,

    rw le_iff_exists_add at hkpos,
    cases hkpos with l hl,
    use l,
    rw add_comm,
    rw <- hl,
    split,
    exact hk.2,
    intro h,
    apply hnak l,
    rw add_comm,
    rw <- hl,
    rw <- hk.1,
    apply hJ,
    use l,
    split,
    refl,
    exact h,
    rw hk.1,
    rw hl,
    rw add_comm,
    rw pow_succ,
    generalize : m^l = I,
    rw ideal.mul_le,
    intros r hr s hs,
    exact ideal.mul_mem_left I hs,
end

/--
A local noetherian integral domain `R` which is integrally closed in its field of fractions
and such that the maximal ideal of `R` is the unique non-zero prime ideal
(i.e. `R` has Krull dimension 1) is a discrete valuation ring.
-/
lemma of_integrally_closed_local_noetherian_unique_prime {R : Type u}
  [integral_domain R] [local_ring R] [Inoetherian : is_noetherian_ring R]
  (Hintegrally_closed : integral_closure R (fraction_ring R) = ⊥)
  (Hprime_unique : ∀ p ≠ (⊥ : ideal R), p.is_prime → p = maximal_ideal R)
  (Hprime_ne_zero : maximal_ideal R ≠ ⊥) :
  discrete_valuation_ring R :=
begin
  refine of_principal_unique_prime_ideal _ Hprime_unique Hprime_ne_zero,

  let m := maximal_ideal R,
  cases (aux_mem_of_ideal_ne_zero Hprime_ne_zero) with a ha,

  have Hminimalk : ∃ k : ℕ, m^(k+1) ≤ ideal.span {a} ∧ ¬ (m^k ≤ ideal.span {a}) :=
    aux_noetherian_local_dim_one_min_pow_maximal_ideal ha.2 ha.1 Hprime_unique Hprime_ne_zero,

  have Hlemax : ideal.span {a} ≤ m,
  rw span_le,
  rw set.singleton_subset_iff,
  exact ha.1,

  cases Hminimalk with k hk,
  have Helement : ∃ b : R, b ∈ m^k ∧ ¬ (b ∈ ideal.span {a}),
  have Hnonempty : ((m^k).carrier \ (ideal.span {a}).carrier).nonempty,
  rw set.nonempty_diff,
  exact hk.2,
  cases Hnonempty with b hb,
  use b,
  rw set.diff_eq at hb,
  rw set.mem_inter_iff at hb,
  rw submodule.mem_carrier at hb,
  rw set.mem_compl_iff at hb,
  rw submodule.mem_carrier at hb,
  rw submodule.mem_coe at hb,
  rw submodule.mem_coe at hb,
  exact hb,

  cases Helement with b hb,
  let K := fraction_ring R,
  let φ : fraction_map R K := fraction_ring.of R,
  let f := localization_map.to_map φ,
  let x : K := (f a)/(f b),
  let m_frac : ring.fractional_ideal φ := m,
  let Hx_inv_span_is_fractional : ring.is_fractional φ (submodule.span R {1/x}),
  exact ring.fractional_ideal.is_fractional_span_singleton (1/x),
  let x_inv_span : ring.fractional_ideal φ := subtype.mk (submodule.span R {1/x}) Hx_inv_span_is_fractional,

  have Hnotle : ¬ (x_inv_span * m_frac ≤ m_frac),
  rw ring.fractional_ideal.le_iff_mem,
  intro Hle,
  apply hb.2,
  -- show that x^-1 is integral over R using the fact that x^-1 acts via an
  -- endomorphism of m which is finitely generated then show that m = x
  sorry,

  have Hxm_le_one : x_inv_span * m_frac ≤ subtype.mk (submodule.span R {1}) (ring.fractional_ideal.is_fractional_span_singleton 1),
  rw ring.fractional_ideal.le_iff_mem,
  intros y hy,
  sorry,
  sorry,
end

section

variables [integral_domain R] [discrete_valuation_ring R]

variable {R}

lemma associated_pow_irreducible {x : R} (hx : x ≠ 0) {ϖ : R} (hirr : irreducible ϖ) :
  ∃ (n : ℕ), associated x (ϖ ^ n) :=
begin
  have : wf_dvd_monoid R := is_noetherian_ring.wf_dvd_monoid,
  cases wf_dvd_monoid.exists_factors x hx with fx hfx,
  unfreezingI { use fx.card },
  have H := hfx.2,
  rw ← associates.mk_eq_mk_iff_associated at H ⊢,
  rw [← H, ← associates.prod_mk, associates.mk_pow, ← multiset.prod_repeat],
  congr' 1,
  rw multiset.eq_repeat,
  simp only [true_and, and_imp, multiset.card_map, eq_self_iff_true,
             multiset.mem_map, exists_imp_distrib],
  rintros _ _ _ rfl,
  rw associates.mk_eq_mk_iff_associated,
  refine associated_of_irreducible _ _ hirr,
  apply hfx.1,
  assumption
end

lemma eq_unit_mul_pow_irreducible {x : R} (hx : x ≠ 0) {ϖ : R} (hirr : irreducible ϖ) :
  ∃ (n : ℕ) (u : units R), x = u * ϖ ^ n :=
begin
  obtain ⟨n, hn⟩ := associated_pow_irreducible hx hirr,
  obtain ⟨u, rfl⟩ := hn.symm,
  use [n, u],
  apply mul_comm,
end

open submodule.is_principal

lemma ideal_eq_span_pow_irreducible {s : ideal R} (hs : s ≠ ⊥) {ϖ : R} (hirr : irreducible ϖ) :
  ∃ n : ℕ, s = ideal.span {ϖ ^ n} :=
begin
  have gen_ne_zero : generator s ≠ 0,
  { rw [ne.def, ← eq_bot_iff_generator_eq_zero], assumption },
  rcases associated_pow_irreducible gen_ne_zero hirr with ⟨n, u, hnu⟩,
  use n,
  have : span _ = _ := span_singleton_generator s,
  rw [← this, ← hnu, span_singleton_eq_span_singleton],
  use u
end

lemma unit_mul_pow_congr_pow {p q : R} (hp : irreducible p) (hq : irreducible q)
  (u v : units R) (m n : ℕ) (h : ↑u * p ^ m = v * q ^ n) :
  m = n :=
begin
  have key : associated (multiset.repeat p m).prod (multiset.repeat q n).prod,
  { rw [multiset.prod_repeat, multiset.prod_repeat, associated],
    refine ⟨u * v⁻¹, _⟩,
    simp only [units.coe_mul],
    rw [mul_left_comm, ← mul_assoc, h, mul_right_comm, units.mul_inv, one_mul], },
  have := multiset.card_eq_card_of_rel (unique_factorization_monoid.factors_unique _ _ key),
  { simpa only [multiset.card_repeat] },
  all_goals
  { intros x hx, replace hx := multiset.eq_of_mem_repeat hx,
    unfreezingI { subst hx, assumption } },
end

lemma unit_mul_pow_congr_unit {ϖ : R} (hirr : irreducible ϖ) (u v : units R) (m n : ℕ)
  (h : ↑u * ϖ ^ m = v * ϖ ^ n) :
  u = v :=
begin
  obtain rfl : m = n := unit_mul_pow_congr_pow hirr hirr u v m n h,
  rw ← sub_eq_zero at h,
  rw [← sub_mul, mul_eq_zero] at h,
  cases h,
  { rw sub_eq_zero at h, exact_mod_cast h },
  { apply (hirr.ne_zero (pow_eq_zero h)).elim, }
end

/-!
## The additive valuation on a DVR
-/

/-- The `ℕ`-valued additive valuation on a DVR (returns junk at `0` rather than `+∞`) -/
noncomputable def add_val (R : Type u) [integral_domain R] [discrete_valuation_ring R] : R → ℕ :=
λ r, if hr : r = 0 then 0 else
  classical.some (associated_pow_irreducible hr (classical.some_spec $ exists_irreducible R))

theorem add_val_spec {r : R} (hr : r ≠ 0) :
  let ϖ := classical.some (exists_irreducible R) in
  let n := classical.some
    (associated_pow_irreducible hr (classical.some_spec (exists_irreducible R))) in
  associated r (ϖ ^ n) :=
classical.some_spec (associated_pow_irreducible hr (classical.some_spec $ exists_irreducible R))

lemma add_val_def (r : R) (u : units R) {ϖ : R} (hϖ : irreducible ϖ) (n : ℕ) (hr : r = u * ϖ ^ n) :
  add_val R r = n :=
begin
  subst hr,
  let ϖ₀ := classical.some (exists_irreducible R),
  have hϖ₀ : irreducible ϖ₀ := classical.some_spec (exists_irreducible R),
  have h0 : (u : R) * ϖ ^ n ≠ 0,
  { simp only [units.mul_right_eq_zero, ne.def, pow_ne_zero n hϖ.ne_zero, not_false_iff] },
  unfold add_val,
  rw dif_neg h0,
  obtain ⟨v, hv⟩ := (add_val_spec h0).symm,
  rw mul_comm at hv,
  refine unit_mul_pow_congr_pow hϖ₀ hϖ _ u _ _ hv,
end

lemma add_val_def' (u : units R) {ϖ : R} (hϖ : irreducible ϖ) (n : ℕ) :
  add_val R ((u : R) * ϖ ^ n) = n :=
add_val_def _ u hϖ n rfl

@[simp] lemma add_val_zero : add_val R 0 = 0 :=
dif_pos rfl

@[simp] lemma add_val_one : add_val R 1 = 0 :=
add_val_def 1 1 (classical.some_spec $ exists_irreducible R) 0 (by simp)

@[simp] lemma add_val_uniformizer {ϖ : R} (hϖ : irreducible ϖ) : add_val R ϖ = 1 :=
add_val_def ϖ 1 hϖ 1 (by simp)

@[simp] lemma add_val_mul {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) :
  add_val R (a * b) = add_val R a + add_val R b :=
begin
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R,
  obtain ⟨m, u, rfl⟩ := eq_unit_mul_pow_irreducible ha hϖ,
  obtain ⟨n, v, rfl⟩ := eq_unit_mul_pow_irreducible hb hϖ,
  rw mul_mul_mul_comm,
  simp only [hϖ, add_val_def', ← pow_add, ← units.coe_mul],
end

lemma add_val_pow (a : R) (n : ℕ) : add_val R (a ^ n) = n * add_val R a :=
begin
  by_cases ha : a = 0,
  { cases nat.eq_zero_or_pos n with hn hn,
    { simp [ha, hn] },
    { simp [ha, zero_pow hn] } },
  induction n with d hd,
  { simp [ha] },
  { rw [pow_succ, add_val_mul ha (pow_ne_zero _ ha), hd], ring}
end

lemma add_val_le_iff_dvd {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) : add_val R a ≤ add_val R b ↔ a ∣ b :=
begin
  split,
  { obtain ⟨ϖ, hϖ⟩ := exists_irreducible R,
    obtain ⟨m, u, rfl⟩ := eq_unit_mul_pow_irreducible ha hϖ,
    obtain ⟨n, v, rfl⟩ := eq_unit_mul_pow_irreducible hb hϖ,
    rw [add_val_def' _ hϖ, add_val_def' _ hϖ, le_iff_exists_add],
    rintro ⟨q, rfl⟩,
    use ((v * u⁻¹ : units R) : R) * ϖ ^ q,
    rw [mul_mul_mul_comm, pow_add, units.coe_mul, mul_left_comm ↑u, units.mul_inv, mul_one] },
  { rintro ⟨c, rfl⟩,
    rw add_val_mul ha (right_ne_zero_of_mul hb),
    simp only [zero_le, le_add_iff_nonneg_right] }
end

lemma add_val_add {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0) :
  min (add_val R a) (add_val R b) ≤ add_val R (a + b) :=
begin
  -- wlog is slow but I'm grateful it works.
  wlog h : add_val R a ≤ add_val R b := le_total (add_val R a) (add_val R b) using [a b, b a],
  rw [min_eq_left h, add_val_le_iff_dvd ha hab],
  rw add_val_le_iff_dvd ha hb at h,
  exact dvd_add_self_left.mpr h,
end

end

end discrete_valuation_ring
