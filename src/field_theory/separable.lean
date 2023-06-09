/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import algebra.squarefree
import data.polynomial.expand
import data.polynomial.splits
import field_theory.minpoly.field
import ring_theory.power_basis

/-!

# Separable polynomials

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define a polynomial to be separable if it is coprime with its derivative. We prove basic
properties about separable polynomials here.

## Main definitions

* `polynomial.separable f`: a polynomial `f` is separable iff it is coprime with its derivative.

-/

universes u v w
open_locale classical big_operators polynomial
open finset

namespace polynomial

section comm_semiring

variables {R : Type u} [comm_semiring R] {S : Type v} [comm_semiring S]

/-- A polynomial is separable iff it is coprime with its derivative. -/
def separable (f : R[X]) : Prop :=
is_coprime f f.derivative

lemma separable_def (f : R[X]) :
  f.separable ↔ is_coprime f f.derivative :=
iff.rfl

lemma separable_def' (f : R[X]) :
  f.separable ↔ ∃ a b : R[X], a * f + b * f.derivative = 1 :=
iff.rfl

lemma not_separable_zero [nontrivial R] : ¬ separable (0 : R[X]) :=
begin
  rintro ⟨x, y, h⟩,
  simpa only [derivative_zero, mul_zero, add_zero, zero_ne_one] using h,
end

lemma separable_one : (1 : R[X]).separable :=
is_coprime_one_left

@[nontriviality] lemma separable_of_subsingleton [subsingleton R] (f : R[X]) :
  f.separable := by simp [separable]

lemma separable_X_add_C (a : R) : (X + C a).separable :=
by { rw [separable_def, derivative_add, derivative_X, derivative_C, add_zero],
  exact is_coprime_one_right }

lemma separable_X : (X : R[X]).separable :=
by { rw [separable_def, derivative_X], exact is_coprime_one_right }

lemma separable_C (r : R) : (C r).separable ↔ is_unit r :=
by rw [separable_def, derivative_C, is_coprime_zero_right, is_unit_C]

lemma separable.of_mul_left {f g : R[X]} (h : (f * g).separable) : f.separable :=
begin
  have := h.of_mul_left_left, rw derivative_mul at this,
  exact is_coprime.of_mul_right_left (is_coprime.of_add_mul_left_right this)
end

lemma separable.of_mul_right {f g : R[X]} (h : (f * g).separable) : g.separable :=
by { rw mul_comm at h, exact h.of_mul_left }

lemma separable.of_dvd {f g : R[X]} (hf : f.separable) (hfg : g ∣ f) : g.separable :=
by { rcases hfg with ⟨f', rfl⟩, exact separable.of_mul_left hf }

lemma separable_gcd_left {F : Type*} [field F] {f : F[X]}
  (hf : f.separable) (g : F[X]) : (euclidean_domain.gcd f g).separable :=
separable.of_dvd hf (euclidean_domain.gcd_dvd_left f g)

lemma separable_gcd_right {F : Type*} [field F] {g : F[X]}
  (f : F[X]) (hg : g.separable) : (euclidean_domain.gcd f g).separable :=
separable.of_dvd hg (euclidean_domain.gcd_dvd_right f g)

lemma separable.is_coprime {f g : R[X]} (h : (f * g).separable) : is_coprime f g :=
begin
  have := h.of_mul_left_left, rw derivative_mul at this,
  exact is_coprime.of_mul_right_right (is_coprime.of_add_mul_left_right this)
end

theorem separable.of_pow' {f : R[X]} :
  ∀ {n : ℕ} (h : (f ^ n).separable), is_unit f ∨ (f.separable ∧ n = 1) ∨ n = 0
| 0     := λ h, or.inr $ or.inr rfl
| 1     := λ h, or.inr $ or.inl ⟨pow_one f ▸ h, rfl⟩
| (n+2) := λ h, by { rw [pow_succ, pow_succ] at h,
    exact or.inl (is_coprime_self.1 h.is_coprime.of_mul_right_left) }

theorem separable.of_pow {f : R[X]} (hf : ¬is_unit f) {n : ℕ} (hn : n ≠ 0)
  (hfs : (f ^ n).separable) : f.separable ∧ n = 1 :=
(hfs.of_pow'.resolve_left hf).resolve_right hn

theorem separable.map {p : R[X]} (h : p.separable) {f : R →+* S} : (p.map f).separable :=
let ⟨a, b, H⟩ := h in ⟨a.map f, b.map f,
by rw [derivative_map, ← polynomial.map_mul, ← polynomial.map_mul, ← polynomial.map_add, H,
       polynomial.map_one]⟩

variables (p q : ℕ)

lemma is_unit_of_self_mul_dvd_separable {p q : R[X]}
  (hp : p.separable) (hq : q * q ∣ p) : is_unit q :=
begin
  obtain ⟨p, rfl⟩ := hq,
  apply is_coprime_self.mp,
  have : is_coprime (q * (q * p)) (q * (q.derivative * p + q.derivative * p + q * p.derivative)),
  { simp only [← mul_assoc, mul_add],
    convert hp,
    rw [derivative_mul, derivative_mul],
    ring },
  exact is_coprime.of_mul_right_left (is_coprime.of_mul_left_left this)
end

lemma multiplicity_le_one_of_separable {p q : R[X]} (hq : ¬ is_unit q)
  (hsep : separable p) : multiplicity q p ≤ 1 :=
begin
  contrapose! hq,
  apply is_unit_of_self_mul_dvd_separable hsep,
  rw ← sq,
  apply multiplicity.pow_dvd_of_le_multiplicity,
  simpa only [nat.cast_one, nat.cast_bit0] using part_enat.add_one_le_of_lt hq
end

lemma separable.squarefree {p : R[X]} (hsep : separable p) : squarefree p :=
begin
  rw multiplicity.squarefree_iff_multiplicity_le_one p,
  intro f,
  by_cases hunit : is_unit f,
  { exact or.inr hunit },
  exact or.inl (multiplicity_le_one_of_separable hunit hsep)
end

end comm_semiring

section comm_ring

variables {R : Type u} [comm_ring R]

lemma separable_X_sub_C {x : R} : separable (X - C x) :=
by simpa only [sub_eq_add_neg, C_neg] using separable_X_add_C (-x)

lemma separable.mul {f g : R[X]} (hf : f.separable) (hg : g.separable)
  (h : is_coprime f g) : (f * g).separable :=
by { rw [separable_def, derivative_mul], exact ((hf.mul_right h).add_mul_left_right _).mul_left
  ((h.symm.mul_right hg).mul_add_right_right _) }

lemma separable_prod' {ι : Sort*} {f : ι → R[X]} {s : finset ι} :
  (∀x∈s, ∀y∈s, x ≠ y → is_coprime (f x) (f y)) → (∀x∈s, (f x).separable) →
  (∏ x in s, f x).separable :=
finset.induction_on s (λ _ _, separable_one) $ λ a s has ih h1 h2, begin
  simp_rw [finset.forall_mem_insert, forall_and_distrib] at h1 h2, rw prod_insert has,
  exact h2.1.mul (ih h1.2.2 h2.2) (is_coprime.prod_right $ λ i his, h1.1.2 i his $
    ne.symm $ ne_of_mem_of_not_mem his has)
end

lemma separable_prod {ι : Sort*} [fintype ι] {f : ι → R[X]}
  (h1 : pairwise (is_coprime on f)) (h2 : ∀ x, (f x).separable) : (∏ x, f x).separable :=
separable_prod' (λ x hx y hy hxy, h1 hxy) (λ x hx, h2 x)

lemma separable.inj_of_prod_X_sub_C [nontrivial R] {ι : Sort*} {f : ι → R} {s : finset ι}
  (hfs : (∏ i in s, (X - C (f i))).separable)
  {x y : ι} (hx : x ∈ s) (hy : y ∈ s) (hfxy : f x = f y) : x = y :=
begin
  by_contra hxy,
  rw [← insert_erase hx, prod_insert (not_mem_erase _ _),
      ← insert_erase (mem_erase_of_ne_of_mem (ne.symm hxy) hy),
      prod_insert (not_mem_erase _ _), ← mul_assoc, hfxy, ← sq] at hfs,
  cases (hfs.of_mul_left.of_pow (by exact not_is_unit_X_sub_C _) two_ne_zero).2
end

lemma separable.injective_of_prod_X_sub_C [nontrivial R] {ι : Sort*} [fintype ι] {f : ι → R}
  (hfs : (∏ i, (X - C (f i))).separable) : function.injective f :=
λ x y hfxy, hfs.inj_of_prod_X_sub_C (mem_univ _) (mem_univ _) hfxy

lemma nodup_of_separable_prod [nontrivial R] {s : multiset R}
  (hs : separable (multiset.map (λ a, X - C a) s).prod) : s.nodup :=
begin
  rw multiset.nodup_iff_ne_cons_cons,
  rintros a t rfl,
  refine not_is_unit_X_sub_C a (is_unit_of_self_mul_dvd_separable hs _),
  simpa only [multiset.map_cons, multiset.prod_cons] using mul_dvd_mul_left _ (dvd_mul_right _ _)
end

/--If `is_unit n` in a `comm_ring R`, then `X ^ n - u` is separable for any unit `u`. -/
lemma separable_X_pow_sub_C_unit {n : ℕ} (u : Rˣ) (hn : is_unit (n : R)) :
  separable (X ^ n - C (u : R)) :=
begin
  nontriviality R,
  rcases n.eq_zero_or_pos with rfl | hpos,
  { simpa using hn },
  apply (separable_def' (X ^ n - C (u : R))).2,
  obtain ⟨n', hn'⟩ := hn.exists_left_inv,
  refine ⟨-C ↑u⁻¹, C ↑u⁻¹ * C n' * X, _⟩,
  rw [derivative_sub, derivative_C, sub_zero, derivative_pow X n, derivative_X, mul_one],
  calc  - C ↑u⁻¹ * (X ^ n - C ↑u) + C ↑u⁻¹ * C n' * X * (↑n * X ^ (n - 1))
      = C (↑u⁻¹ * ↑ u) - C ↑u⁻¹ * X^n + C ↑ u ⁻¹ * C (n' * ↑n) * (X * X ^ (n - 1)) :
    by { simp only [C.map_mul, C_eq_nat_cast], ring }
  ... = 1 : by simp only [units.inv_mul, hn', C.map_one, mul_one, ← pow_succ,
              nat.sub_add_cancel (show 1 ≤ n, from hpos), sub_add_cancel]
end

lemma root_multiplicity_le_one_of_separable [nontrivial R] {p : R[X]}
  (hsep : separable p) (x : R) : root_multiplicity x p ≤ 1 :=
begin
  by_cases hp : p = 0,
  { simp [hp], },
  rw [root_multiplicity_eq_multiplicity, dif_neg hp, ← part_enat.coe_le_coe, part_enat.coe_get,
    nat.cast_one],
  exact multiplicity_le_one_of_separable (not_is_unit_X_sub_C _) hsep
end

end comm_ring

section is_domain

variables {R : Type u} [comm_ring R] [is_domain R]

lemma count_roots_le_one {p : R[X]} (hsep : separable p) (x : R) :
  p.roots.count x ≤ 1 :=
begin
  rw count_roots p,
  exact root_multiplicity_le_one_of_separable hsep x
end

lemma nodup_roots {p : R[X]} (hsep : separable p) : p.roots.nodup :=
multiset.nodup_iff_count_le_one.mpr (count_roots_le_one hsep)

end is_domain

section field

variables {F : Type u} [field F] {K : Type v} [field K]

theorem separable_iff_derivative_ne_zero {f : F[X]} (hf : irreducible f) :
  f.separable ↔ f.derivative ≠ 0 :=
⟨λ h1 h2, hf.not_unit $ is_coprime_zero_right.1 $ h2 ▸ h1,
  λ h, euclidean_domain.is_coprime_of_dvd (mt and.right h) $ λ g hg1 hg2 ⟨p, hg3⟩ hg4,
let ⟨u, hu⟩ := (hf.is_unit_or_is_unit hg3).resolve_left hg1 in
  have f ∣ f.derivative, by { conv_lhs { rw [hg3, ← hu] }, rwa units.mul_right_dvd },
  not_lt_of_le (nat_degree_le_of_dvd this h) $
  nat_degree_derivative_lt $ mt derivative_of_nat_degree_zero h⟩

theorem separable_map (f : F →+* K) {p : F[X]} : (p.map f).separable ↔ p.separable :=
by simp_rw [separable_def, derivative_map, is_coprime_map]

lemma separable_prod_X_sub_C_iff' {ι : Sort*} {f : ι → F} {s : finset ι} :
  (∏ i in s, (X - C (f i))).separable ↔ (∀ (x ∈ s) (y ∈ s), f x = f y → x = y) :=
⟨λ hfs x hx y hy hfxy, hfs.inj_of_prod_X_sub_C hx hy hfxy,
λ H, by { rw ← prod_attach, exact separable_prod' (λ x hx y hy hxy,
    @pairwise_coprime_X_sub_C _ _ { x // x ∈ s } (λ x, f x)
      (λ x y hxy, subtype.eq $ H x.1 x.2 y.1 y.2 hxy) _ _ hxy)
  (λ _ _, separable_X_sub_C) }⟩

lemma separable_prod_X_sub_C_iff {ι : Sort*} [fintype ι] {f : ι → F} :
  (∏ i, (X - C (f i))).separable ↔ function.injective f :=
separable_prod_X_sub_C_iff'.trans $ by simp_rw [mem_univ, true_implies_iff, function.injective]

section char_p

variables (p : ℕ) [HF : char_p F p]
include HF

theorem separable_or {f : F[X]} (hf : irreducible f) : f.separable ∨
  ¬f.separable ∧ ∃ g : F[X], irreducible g ∧ expand F p g = f :=
if H : f.derivative = 0 then
begin
  unfreezingI { rcases p.eq_zero_or_pos with rfl | hp },
  { haveI := char_p.char_p_to_char_zero F,
    have := nat_degree_eq_zero_of_derivative_eq_zero H,
    have := (nat_degree_pos_iff_degree_pos.mpr $ degree_pos_of_irreducible hf).ne',
    contradiction },
  haveI := is_local_ring_hom_expand F hp,
  exact or.inr
        ⟨by rw [separable_iff_derivative_ne_zero hf, not_not, H],
        contract p f,
        of_irreducible_map ↑(expand F p) (by rwa ← expand_contract p H hp.ne' at hf),
        expand_contract p H hp.ne'⟩
end
else or.inl $ (separable_iff_derivative_ne_zero hf).2 H

theorem exists_separable_of_irreducible {f : F[X]} (hf : irreducible f) (hp : p ≠ 0) :
  ∃ (n : ℕ) (g : F[X]), g.separable ∧ expand F (p ^ n) g = f :=
begin
  replace hp : p.prime := (char_p.char_is_prime_or_zero F p).resolve_right hp,
  unfreezingI
  { induction hn : f.nat_degree using nat.strong_induction_on with N ih generalizing f },
  rcases separable_or p hf with h | ⟨h1, g, hg, hgf⟩,
  { refine ⟨0, f, h, _⟩, rw [pow_zero, expand_one] },
  { cases N with N,
    { rw [nat_degree_eq_zero_iff_degree_le_zero, degree_le_zero_iff] at hn,
      rw [hn, separable_C, is_unit_iff_ne_zero, not_not] at h1,
      have hf0 : f ≠ 0 := hf.ne_zero,
      rw [h1, C_0] at hn, exact absurd hn hf0 },
    have hg1 : g.nat_degree * p = N.succ,
    { rwa [← nat_degree_expand, hgf] },
    have hg2 : g.nat_degree ≠ 0,
    { intro this, rw [this, zero_mul] at hg1, cases hg1 },
    have hg3 : g.nat_degree < N.succ,
    { rw [← mul_one g.nat_degree, ← hg1],
      exact nat.mul_lt_mul_of_pos_left hp.one_lt hg2.bot_lt },
    rcases ih _ hg3 hg rfl with ⟨n, g, hg4, rfl⟩, refine ⟨n+1, g, hg4, _⟩,
    rw [← hgf, expand_expand, pow_succ] }
end

theorem is_unit_or_eq_zero_of_separable_expand {f : F[X]} (n : ℕ) (hp : 0 < p)
  (hf : (expand F (p ^ n) f).separable) : is_unit f ∨ n = 0 :=
begin
  rw or_iff_not_imp_right,
  rintro hn : n ≠ 0,
  have hf2 : (expand F (p ^ n) f).derivative = 0,
  { rw [derivative_expand, nat.cast_pow, char_p.cast_eq_zero,
      zero_pow hn.bot_lt, zero_mul, mul_zero] },
  rw [separable_def, hf2, is_coprime_zero_right, is_unit_iff] at hf,
  rcases hf with ⟨r, hr, hrf⟩,
  rw [eq_comm, expand_eq_C (pow_pos hp _)] at hrf,
  rwa [hrf, is_unit_C]
end

theorem unique_separable_of_irreducible {f : F[X]} (hf : irreducible f) (hp : 0 < p)
  (n₁ : ℕ) (g₁ : F[X]) (hg₁ : g₁.separable) (hgf₁ : expand F (p ^ n₁) g₁ = f)
  (n₂ : ℕ) (g₂ : F[X]) (hg₂ : g₂.separable) (hgf₂ : expand F (p ^ n₂) g₂ = f) :
  n₁ = n₂ ∧ g₁ = g₂ :=
begin
  revert g₁ g₂,
  wlog hn : n₁ ≤ n₂,
  { intros g₁ g₂ hg₁ Hg₁ hg₂ Hg₂,
    simpa only [eq_comm] using this hf hp n₂ n₁ (le_of_not_le hn) g₂ g₁ hg₂ Hg₂ hg₁ Hg₁ },
  have hf0 : f ≠ 0 := hf.ne_zero,
  unfreezingI { intros, rw le_iff_exists_add at hn, rcases hn with ⟨k, rfl⟩,
    rw [← hgf₁, pow_add, expand_mul, expand_inj (pow_pos hp n₁)] at hgf₂, subst hgf₂,
    subst hgf₁,
    rcases is_unit_or_eq_zero_of_separable_expand p k hp hg₁ with h | rfl,
    { rw is_unit_iff at h, rcases h with ⟨r, hr, rfl⟩,
      simp_rw expand_C at hf, exact absurd (is_unit_C.2 hr) hf.1 },
    { rw [add_zero, pow_zero, expand_one], split; refl } },
end

end char_p

/--If `n ≠ 0` in `F`, then ` X ^ n - a` is separable for any `a ≠ 0`. -/
lemma separable_X_pow_sub_C {n : ℕ} (a : F) (hn : (n : F) ≠ 0) (ha : a ≠ 0) :
  separable (X ^ n - C a) :=
separable_X_pow_sub_C_unit (units.mk0 a ha) (is_unit.mk0 n hn)

-- this can possibly be strengthened to making `separable_X_pow_sub_C_unit` a
-- bi-implication, but it is nontrivial!
/-- In a field `F`, `X ^ n - 1` is separable iff `↑n ≠ 0`. -/
lemma X_pow_sub_one_separable_iff {n : ℕ} :
  (X ^ n - 1 : F[X]).separable ↔ (n : F) ≠ 0 :=
begin
  refine ⟨_, λ h, separable_X_pow_sub_C_unit 1 (is_unit.mk0 ↑n h)⟩,
  rw [separable_def', derivative_sub, derivative_X_pow, derivative_one, sub_zero],
  -- Suppose `(n : F) = 0`, then the derivative is `0`, so `X ^ n - 1` is a unit, contradiction.
  rintro (h : is_coprime _ _) hn',
  rw [hn', C_0, zero_mul, is_coprime_zero_right] at h,
  exact not_is_unit_X_pow_sub_one F n h
end

section splits

lemma card_root_set_eq_nat_degree [algebra F K] {p : F[X]} (hsep : p.separable)
  (hsplit : splits (algebra_map F K) p) : fintype.card (p.root_set K) = p.nat_degree :=
begin
  simp_rw [root_set_def, finset.coe_sort_coe, fintype.card_coe],
  rw [multiset.to_finset_card_of_nodup, ←nat_degree_eq_card_roots hsplit],
  exact nodup_roots hsep.map,
end

variable {i : F →+* K}

lemma eq_X_sub_C_of_separable_of_root_eq {x : F} {h : F[X]}
  (h_sep : h.separable) (h_root : h.eval x = 0) (h_splits : splits i h)
  (h_roots : ∀ y ∈ (h.map i).roots, y = i x) : h = (C (leading_coeff h)) * (X - C x) :=
begin
  have h_ne_zero : h ≠ 0 := by { rintro rfl, exact not_separable_zero h_sep },
  apply polynomial.eq_X_sub_C_of_splits_of_single_root i h_splits,
  apply finset.mk.inj,
  { change _ = {i x},
    rw finset.eq_singleton_iff_unique_mem,
    split,
    { apply finset.mem_mk.mpr,
      rw mem_roots (show h.map i ≠ 0, by exact map_ne_zero h_ne_zero),
      rw [is_root.def,←eval₂_eq_eval_map,eval₂_hom,h_root],
      exact ring_hom.map_zero i },
    { exact h_roots } },
  { exact nodup_roots (separable.map h_sep) },
end

lemma exists_finset_of_splits
  (i : F →+* K) {f : F[X]} (sep : separable f) (sp : splits i f) :
  ∃ (s : finset K), f.map i = C (i f.leading_coeff) * (s.prod (λ a : K, X - C a)) :=
begin
  obtain ⟨s, h⟩ := (splits_iff_exists_multiset _).1 sp,
  use s.to_finset,
  rw [h, finset.prod_eq_multiset_prod, ←multiset.to_finset_eq],
  apply nodup_of_separable_prod,
  apply separable.of_mul_right,
  rw ←h,
  exact sep.map,
end

end splits

theorem _root_.irreducible.separable [char_zero F] {f : F[X]}
  (hf : irreducible f) : f.separable :=
begin
  rw [separable_iff_derivative_ne_zero hf, ne, ← degree_eq_bot, degree_derivative_eq],
  { rintro ⟨⟩ },
  rw [pos_iff_ne_zero, ne, nat_degree_eq_zero_iff_degree_le_zero, degree_le_zero_iff],
  refine λ hf1, hf.not_unit _,
  rw [hf1, is_unit_C, is_unit_iff_ne_zero],
  intro hf2,
  rw [hf2, C_0] at hf1,
  exact absurd hf1 hf.ne_zero
end

end field

end polynomial

open polynomial

section comm_ring

variables (F K : Type*) [comm_ring F] [ring K] [algebra F K]

-- TODO: refactor to allow transcendental extensions?
-- See: https://en.wikipedia.org/wiki/Separable_extension#Separability_of_transcendental_extensions
-- Note that right now a Galois extension (class `is_galois`) is defined to be an extension which
-- is separable and normal, so if the definition of separable changes here at some point
-- to allow non-algebraic extensions, then the definition of `is_galois` must also be changed.

/-- Typeclass for separable field extension: `K` is a separable field extension of `F` iff
the minimal polynomial of every `x : K` is separable.

We define this for general (commutative) rings and only assume `F` and `K` are fields if this
is needed for a proof.
-/
class is_separable : Prop :=
(is_integral' (x : K) : is_integral F x)
(separable' (x : K) : (minpoly F x).separable)

variables (F) {K}

theorem is_separable.is_integral [is_separable F K] :
  ∀ x : K, is_integral F x := is_separable.is_integral'

theorem is_separable.separable [is_separable F K] :
  ∀ x : K, (minpoly F x).separable := is_separable.separable'

variables {F K}

theorem is_separable_iff : is_separable F K ↔ ∀ x : K, is_integral F x ∧ (minpoly F x).separable :=
⟨λ h x, ⟨@@is_separable.is_integral F _ _ _ h x, @@is_separable.separable F _ _ _ h x⟩,
 λ h, ⟨λ x, (h x).1, λ x, (h x).2⟩⟩

end comm_ring

instance is_separable_self (F : Type*) [field F] : is_separable F F :=
⟨λ x, is_integral_algebra_map, λ x, by { rw minpoly.eq_X_sub_C', exact separable_X_sub_C }⟩

/-- A finite field extension in characteristic 0 is separable. -/
@[priority 100] -- See note [lower instance priority]
instance is_separable.of_finite (F K : Type*) [field F] [field K] [algebra F K]
  [finite_dimensional F K] [char_zero F] : is_separable F K :=
have ∀ (x : K), is_integral F x,
from λ x, algebra.is_integral_of_finite _ _ _,
⟨this, λ x, (minpoly.irreducible (this x)).separable⟩

section is_separable_tower
variables (F K E : Type*) [field F] [field K] [field E] [algebra F K] [algebra F E]
  [algebra K E] [is_scalar_tower F K E]

lemma is_separable_tower_top_of_is_separable [is_separable F E] : is_separable K E :=
⟨λ x, is_integral_of_is_scalar_tower (is_separable.is_integral F x),
 λ x, (is_separable.separable F x).map.of_dvd (minpoly.dvd_map_of_is_scalar_tower _ _ _)⟩

lemma is_separable_tower_bot_of_is_separable [h : is_separable F E] : is_separable F K :=
is_separable_iff.2 $ λ x, begin
  refine (is_separable_iff.1 h (algebra_map K E x)).imp
    is_integral_tower_bot_of_is_integral_field (λ hs, _),
  obtain ⟨q, hq⟩ := minpoly.dvd F x
    ((aeval_algebra_map_eq_zero_iff _ _ _).mp (minpoly.aeval F ((algebra_map K E) x))),
  rw hq at hs,
  exact hs.of_mul_left
end

variables {E}

lemma is_separable.of_alg_hom (E' : Type*) [field E'] [algebra F E']
  (f : E →ₐ[F] E') [is_separable F E'] : is_separable F E :=
begin
  letI : algebra E E' := ring_hom.to_algebra f.to_ring_hom,
  haveI : is_scalar_tower F E E' := is_scalar_tower.of_algebra_map_eq (λ x, (f.commutes x).symm),
  exact is_separable_tower_bot_of_is_separable F E E',
end

end is_separable_tower

section card_alg_hom

variables {R S T : Type*} [comm_ring S]
variables {K L F : Type*} [field K] [field L] [field F]
variables [algebra K S] [algebra K L]

lemma alg_hom.card_of_power_basis (pb : power_basis K S) (h_sep : (minpoly K pb.gen).separable)
  (h_splits : (minpoly K pb.gen).splits (algebra_map K L)) :
  @fintype.card (S →ₐ[K] L) (power_basis.alg_hom.fintype pb) = pb.dim :=
begin
  let s := ((minpoly K pb.gen).map (algebra_map K L)).roots.to_finset,
  have H := λ x, multiset.mem_to_finset,
  rw [fintype.card_congr pb.lift_equiv', fintype.card_of_subtype s H,
      ← pb.nat_degree_minpoly, nat_degree_eq_card_roots h_splits, multiset.to_finset_card_of_nodup],
  exact nodup_roots ((separable_map (algebra_map K L)).mpr h_sep)
end

end card_alg_hom
