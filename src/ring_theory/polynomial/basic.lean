/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import algebra.char_p.basic
import algebra.geom_sum
import data.mv_polynomial.comm_ring
import data.mv_polynomial.equiv
import ring_theory.polynomial.content
import ring_theory.unique_factorization_domain

/-!
# Ring-theoretic supplement of data.polynomial.

## Main results
* `mv_polynomial.is_domain`:
  If a ring is an integral domain, then so is its polynomial ring over finitely many variables.
* `polynomial.is_noetherian_ring`:
  Hilbert basis theorem, that if a ring is noetherian then so is its polynomial ring.
* `polynomial.wf_dvd_monoid`:
  If an integral domain is a `wf_dvd_monoid`, then so is its polynomial ring.
* `polynomial.unique_factorization_monoid`, `mv_polynomial.unique_factorization_monoid`:
  If an integral domain is a `unique_factorization_monoid`, then so is its polynomial ring (of any
  number of variables).
-/

noncomputable theory
open_locale classical big_operators polynomial
open finset

universes u v w
variables {R : Type u} {S : Type*}

namespace polynomial

section semiring
variables [semiring R]

instance (p : ℕ) [h : char_p R p] : char_p R[X] p :=
let ⟨h⟩ := h in ⟨λ n, by rw [← map_nat_cast C, ← C_0, C_inj, h]⟩

variables (R)

/-- The `R`-submodule of `R[X]` consisting of polynomials of degree ≤ `n`. -/
def degree_le (n : with_bot ℕ) : submodule R R[X] :=
⨅ k : ℕ, ⨅ h : ↑k > n, (lcoeff R k).ker

/-- The `R`-submodule of `R[X]` consisting of polynomials of degree < `n`. -/
def degree_lt (n : ℕ) : submodule R R[X] :=
⨅ k : ℕ, ⨅ h : k ≥ n, (lcoeff R k).ker

variable {R}

theorem mem_degree_le {n : with_bot ℕ} {f : R[X]} :
  f ∈ degree_le R n ↔ degree f ≤ n :=
by simp only [degree_le, submodule.mem_infi, degree_le_iff_coeff_zero, linear_map.mem_ker]; refl

@[mono] theorem degree_le_mono {m n : with_bot ℕ} (H : m ≤ n) :
  degree_le R m ≤ degree_le R n :=
λ f hf, mem_degree_le.2 (le_trans (mem_degree_le.1 hf) H)

theorem degree_le_eq_span_X_pow {n : ℕ} :
  degree_le R n = submodule.span R ↑((finset.range (n+1)).image (λ n, (X : R[X])^n)) :=
begin
  apply le_antisymm,
  { intros p hp, replace hp := mem_degree_le.1 hp,
    rw [← polynomial.sum_monomial_eq p, polynomial.sum],
    refine submodule.sum_mem _ (λ k hk, _),
    show monomial _ _ ∈ _,
    have := with_bot.coe_le_coe.1 (finset.sup_le_iff.1 hp k hk),
    rw [← C_mul_X_pow_eq_monomial, C_mul'],
    refine submodule.smul_mem _ _ (submodule.subset_span $ finset.mem_coe.2 $
      finset.mem_image.2 ⟨_, finset.mem_range.2 (nat.lt_succ_of_le this), rfl⟩) },
  rw [submodule.span_le, finset.coe_image, set.image_subset_iff],
  intros k hk, apply mem_degree_le.2,
  exact (degree_X_pow_le _).trans
    (with_bot.coe_le_coe.2 $ nat.le_of_lt_succ $ finset.mem_range.1 hk)
end

theorem mem_degree_lt {n : ℕ} {f : R[X]} :
  f ∈ degree_lt R n ↔ degree f < n :=
by { simp_rw [degree_lt, submodule.mem_infi, linear_map.mem_ker, degree, finset.max_eq_sup_coe,
    finset.sup_lt_iff (with_bot.bot_lt_coe n), mem_support_iff,
    with_bot.coe_lt_coe, lt_iff_not_le, ne, not_imp_not], refl }

@[mono] theorem degree_lt_mono {m n : ℕ} (H : m ≤ n) :
  degree_lt R m ≤ degree_lt R n :=
λ f hf, mem_degree_lt.2 (lt_of_lt_of_le (mem_degree_lt.1 hf) $ with_bot.coe_le_coe.2 H)

theorem degree_lt_eq_span_X_pow {n : ℕ} :
  degree_lt R n = submodule.span R ↑((finset.range n).image (λ n, X^n) : finset R[X]) :=
begin
  apply le_antisymm,
  { intros p hp, replace hp := mem_degree_lt.1 hp,
    rw [← polynomial.sum_monomial_eq p, polynomial.sum],
    refine submodule.sum_mem _ (λ k hk, _),
    show monomial _ _ ∈ _,
    have := with_bot.coe_lt_coe.1 ((finset.sup_lt_iff $ with_bot.bot_lt_coe n).1 hp k hk),
    rw [← C_mul_X_pow_eq_monomial, C_mul'],
    refine submodule.smul_mem _ _ (submodule.subset_span $ finset.mem_coe.2 $
      finset.mem_image.2 ⟨_, finset.mem_range.2 this, rfl⟩) },
  rw [submodule.span_le, finset.coe_image, set.image_subset_iff],
  intros k hk, apply mem_degree_lt.2,
  exact lt_of_le_of_lt (degree_X_pow_le _) (with_bot.coe_lt_coe.2 $ finset.mem_range.1 hk)
end

/-- The first `n` coefficients on `degree_lt n` form a linear equivalence with `fin n → R`. -/
def degree_lt_equiv (R) [semiring R] (n : ℕ) : degree_lt R n ≃ₗ[R] (fin n → R) :=
{ to_fun := λ p n, (↑p : R[X]).coeff n,
  inv_fun := λ f, ⟨∑ i : fin n, monomial i (f i),
    (degree_lt R n).sum_mem (λ i _, mem_degree_lt.mpr (lt_of_le_of_lt
      (degree_monomial_le i (f i)) (with_bot.coe_lt_coe.mpr i.is_lt)))⟩,
  map_add' := λ p q, by { ext, rw [submodule.coe_add, coeff_add], refl },
  map_smul' := λ x p, by { ext, rw [submodule.coe_smul, coeff_smul], refl },
  left_inv :=
  begin
    rintro ⟨p, hp⟩, ext1,
    simp only [submodule.coe_mk],
    by_cases hp0 : p = 0,
    { subst hp0, simp only [coeff_zero, linear_map.map_zero, finset.sum_const_zero] },
    rw [mem_degree_lt, degree_eq_nat_degree hp0, with_bot.coe_lt_coe] at hp,
    conv_rhs { rw [p.as_sum_range' n hp, ← fin.sum_univ_eq_sum_range] },
  end,
  right_inv :=
  begin
    intro f, ext i,
    simp only [finset_sum_coeff, submodule.coe_mk],
    rw [finset.sum_eq_single i, coeff_monomial, if_pos rfl],
    { rintro j - hji, rw [coeff_monomial, if_neg], rwa [← fin.ext_iff] },
    { intro h, exact (h (finset.mem_univ _)).elim }
  end }

@[simp] theorem degree_lt_equiv_eq_zero_iff_eq_zero {n : ℕ} {p : R[X]} (hp : p ∈ degree_lt R n) :
  degree_lt_equiv _ _ ⟨p, hp⟩ = 0 ↔ p = 0 :=
by rw [linear_equiv.map_eq_zero_iff, submodule.mk_eq_zero]

theorem eval_eq_sum_degree_lt_equiv {n : ℕ} {p : R[X]} (hp : p ∈ degree_lt R n) (x : R) :
  p.eval x = ∑ i, degree_lt_equiv _ _ ⟨p, hp⟩ i * (x ^ (i : ℕ)) :=
begin
  simp_rw [eval_eq_sum],
  exact (sum_fin _ (by simp_rw [zero_mul, forall_const]) (mem_degree_lt.mp hp)).symm
end

/-- The finset of nonzero coefficients of a polynomial. -/
def frange (p : R[X]) : finset R :=
finset.image (λ n, p.coeff n) p.support

lemma frange_zero : frange (0 : R[X]) = ∅ :=
rfl

lemma mem_frange_iff {p : R[X]} {c : R} :
  c ∈ p.frange ↔ ∃ n ∈ p.support, c = p.coeff n :=
by simp [frange, eq_comm]

lemma frange_one : frange (1 : R[X]) ⊆ {1} :=
begin
  simp [frange, finset.image_subset_iff],
  simp only [← C_1, coeff_C],
  assume n hn,
  simp only [exists_prop, ite_eq_right_iff, not_forall] at hn,
  simp [hn],
end

lemma coeff_mem_frange (p : R[X]) (n : ℕ) (h : p.coeff n ≠ 0) :
  p.coeff n ∈ p.frange :=
begin
  simp only [frange, exists_prop, mem_support_iff, finset.mem_image, ne.def],
  exact ⟨n, h, rfl⟩,
end

lemma geom_sum_X_comp_X_add_one_eq_sum (n : ℕ) :
  (∑ i in range n, (X : R[X]) ^ i).comp (X + 1) =
  (finset.range n).sum (λ (i : ℕ), (n.choose (i + 1) : R[X]) * X ^ i) :=
begin
  ext i,
  transitivity (n.choose (i + 1) : R), swap,
  { simp only [finset_sum_coeff, ← C_eq_nat_cast, coeff_C_mul_X_pow],
    rw [finset.sum_eq_single i, if_pos rfl],
    { simp only [@eq_comm _ i, if_false, eq_self_iff_true, implies_true_iff] {contextual := tt}, },
    { simp only [nat.lt_add_one_iff, nat.choose_eq_zero_of_lt, nat.cast_zero, finset.mem_range,
        not_lt, eq_self_iff_true, if_true, implies_true_iff] {contextual := tt}, } },
  induction n with n ih generalizing i,
  { simp only [geom_sum_zero, zero_comp, coeff_zero, nat.choose_zero_succ, nat.cast_zero], },
  simp only [geom_sum_succ', ih, add_comp, X_pow_comp, coeff_add, nat.choose_succ_succ,
    nat.cast_add, coeff_X_add_one_pow],
end

lemma monic.geom_sum {P : R[X]}
  (hP : P.monic) (hdeg : 0 < P.nat_degree) {n : ℕ} (hn : n ≠ 0) : (∑ i in range n, P ^ i).monic :=
begin
  nontriviality R,
  cases n, { exact (hn rfl).elim },
  rw [geom_sum_succ'],
  refine (hP.pow _).add_of_left _,
  refine lt_of_le_of_lt (degree_sum_le _ _) _,
  rw [finset.sup_lt_iff],
  { simp only [finset.mem_range, degree_eq_nat_degree (hP.pow _).ne_zero,
      with_bot.coe_lt_coe, hP.nat_degree_pow],
    intro k, exact nsmul_lt_nsmul hdeg },
  { rw [bot_lt_iff_ne_bot, ne.def, degree_eq_bot],
    exact (hP.pow _).ne_zero }
end

lemma monic.geom_sum' {P : R[X]}
  (hP : P.monic) (hdeg : 0 < P.degree) {n : ℕ} (hn : n ≠ 0) : (∑ i in range n, P ^ i).monic :=
hP.geom_sum (nat_degree_pos_iff_degree_pos.2 hdeg) hn

lemma monic_geom_sum_X {n : ℕ} (hn : n ≠ 0) :
  (∑ i in range n, (X : R[X]) ^ i).monic :=
begin
  nontriviality R,
  apply monic_X.geom_sum _ hn,
  simpa only [nat_degree_X] using zero_lt_one
end

end semiring

section ring
variables [ring R]

/-- Given a polynomial, return the polynomial whose coefficients are in
the ring closure of the original coefficients. -/
def restriction (p : R[X]) : polynomial (subring.closure (↑p.frange : set R)) :=
∑ i in p.support, monomial i (⟨p.coeff i,
  if H : p.coeff i = 0 then H.symm ▸ (subring.closure _).zero_mem
  else subring.subset_closure (p.coeff_mem_frange _ H)⟩ : (subring.closure (↑p.frange : set R)))

@[simp] theorem coeff_restriction {p : R[X]} {n : ℕ} :
  ↑(coeff (restriction p) n) = coeff p n :=
begin
  simp only [restriction, coeff_monomial, finset_sum_coeff, mem_support_iff, finset.sum_ite_eq',
    ne.def, ite_not],
  split_ifs,
  { rw h, refl },
  { refl }
end

@[simp] theorem coeff_restriction' {p : R[X]} {n : ℕ} :
  (coeff (restriction p) n).1 = coeff p n :=
coeff_restriction

@[simp] lemma support_restriction (p : R[X]) :
  support (restriction p) = support p :=
begin
  ext i,
  simp only [mem_support_iff, not_iff_not, ne.def],
  conv_rhs { rw [← coeff_restriction] },
  exact ⟨λ H, by { rw H, refl }, λ H, subtype.coe_injective H⟩
end

@[simp] theorem map_restriction {R : Type u} [comm_ring R]
  (p : R[X]) : p.restriction.map (algebra_map _ _) = p :=
ext $ λ n, by rw [coeff_map, algebra.algebra_map_of_subring_apply, coeff_restriction]

@[simp] theorem degree_restriction {p : R[X]} : (restriction p).degree = p.degree :=
by simp [degree]

@[simp] theorem nat_degree_restriction {p : R[X]} :
  (restriction p).nat_degree = p.nat_degree :=
by simp [nat_degree]

@[simp] theorem monic_restriction {p : R[X]} : monic (restriction p) ↔ monic p :=
begin
  simp only [monic, leading_coeff, nat_degree_restriction],
  rw [←@coeff_restriction _ _ p],
  exact ⟨λ H, by { rw H, refl }, λ H, subtype.coe_injective H⟩
end

@[simp] theorem restriction_zero : restriction (0 : R[X]) = 0 :=
by simp only [restriction, finset.sum_empty, support_zero]

@[simp] theorem restriction_one : restriction (1 : R[X]) = 1 :=
ext $ λ i, subtype.eq $ by rw [coeff_restriction', coeff_one, coeff_one]; split_ifs; refl

variables [semiring S] {f : R →+* S} {x : S}

theorem eval₂_restriction {p : R[X]} :
  eval₂ f x p =
  eval₂ (f.comp (subring.subtype (subring.closure (p.frange : set R)))) x p.restriction :=
begin
  simp only [eval₂_eq_sum, sum, support_restriction, ←@coeff_restriction _ _ p],
  refl,
end

section to_subring

variables (p : R[X]) (T : subring R)

/-- Given a polynomial `p` and a subring `T` that contains the coefficients of `p`,
return the corresponding polynomial whose coefficients are in `T`. -/
def to_subring (hp : (↑p.frange : set R) ⊆ T) : T[X] :=
∑ i in p.support, monomial i (⟨p.coeff i,
  if H : p.coeff i = 0 then H.symm ▸ T.zero_mem
  else hp (p.coeff_mem_frange _ H)⟩ : T)

variables (hp : (↑p.frange : set R) ⊆ T)
include hp

@[simp] theorem coeff_to_subring {n : ℕ} : ↑(coeff (to_subring p T hp) n) = coeff p n :=
begin
  simp only [to_subring, coeff_monomial, finset_sum_coeff, mem_support_iff, finset.sum_ite_eq',
    ne.def, ite_not],
  split_ifs,
  { rw h, refl },
  { refl }
end

@[simp] theorem coeff_to_subring' {n : ℕ} : (coeff (to_subring p T hp) n).1 = coeff p n :=
coeff_to_subring _ _ hp

@[simp] lemma support_to_subring :
  support (to_subring p T hp) = support p :=
begin
  ext i,
  simp only [mem_support_iff, not_iff_not, ne.def],
  conv_rhs { rw [← coeff_to_subring p T hp] },
  exact ⟨λ H, by { rw H, refl }, λ H, subtype.coe_injective H⟩
end

@[simp] theorem degree_to_subring : (to_subring p T hp).degree = p.degree :=
by simp [degree]

@[simp] theorem nat_degree_to_subring : (to_subring p T hp).nat_degree = p.nat_degree :=
by simp [nat_degree]

@[simp] theorem monic_to_subring : monic (to_subring p T hp) ↔ monic p :=
begin
  simp_rw [monic, leading_coeff, nat_degree_to_subring, ← coeff_to_subring p T hp],
  exact ⟨λ H, by { rw H, refl }, λ H, subtype.coe_injective H⟩
end

omit hp

@[simp] theorem to_subring_zero : to_subring (0 : R[X]) T (by simp [frange_zero]) = 0 :=
by { ext i, simp }

@[simp] theorem to_subring_one : to_subring (1 : R[X]) T
  (set.subset.trans frange_one $finset.singleton_subset_set_iff.2 T.one_mem) = 1 :=
ext $ λ i, subtype.eq $ by rw [coeff_to_subring', coeff_one, coeff_one]; split_ifs; refl

@[simp] theorem map_to_subring : (p.to_subring T hp).map (subring.subtype T) = p :=
by { ext n, simp [coeff_map] }

end to_subring

variables (T : subring R)

/-- Given a polynomial whose coefficients are in some subring, return
the corresponding polynomial whose coefficients are in the ambient ring. -/
def of_subring (p : T[X]) : R[X] :=
∑ i in p.support, monomial i (p.coeff i : R)

lemma coeff_of_subring (p : T[X]) (n : ℕ) :
  coeff (of_subring T p) n = (coeff p n : T) :=
begin
  simp only [of_subring, coeff_monomial, finset_sum_coeff, mem_support_iff, finset.sum_ite_eq',
    ite_eq_right_iff, ne.def, ite_not, not_not, ite_eq_left_iff],
  assume h,
  rw h,
  refl
end

@[simp] theorem frange_of_subring {p : T[X]} :
  (↑(p.of_subring T).frange : set R) ⊆ T :=
begin
  assume i hi,
  simp only [frange, set.mem_image, mem_support_iff, ne.def, finset.mem_coe, finset.coe_image]
    at hi,
  rcases hi with ⟨n, hn, h'n⟩,
  rw [← h'n, coeff_of_subring],
  exact subtype.mem (coeff p n : T)
end

end ring

section comm_ring
variables [comm_ring R]

section mod_by_monic

variables {q : R[X]}

lemma mem_ker_mod_by_monic (hq : q.monic) {p : R[X]} :
  p ∈ (mod_by_monic_hom q).ker ↔ q ∣ p :=
linear_map.mem_ker.trans (dvd_iff_mod_by_monic_eq_zero hq)

@[simp] lemma ker_mod_by_monic_hom (hq : q.monic) :
  (polynomial.mod_by_monic_hom q).ker = (ideal.span {q}).restrict_scalars R :=
submodule.ext (λ f, (mem_ker_mod_by_monic hq).trans ideal.mem_span_singleton.symm)

end mod_by_monic

end comm_ring

end polynomial

namespace ideal
open polynomial

section semiring
variables [semiring R]

/-- Transport an ideal of `R[X]` to an `R`-submodule of `R[X]`. -/
def of_polynomial (I : ideal R[X]) : submodule R R[X] :=
{ carrier := I.carrier,
  zero_mem' := I.zero_mem,
  add_mem' := λ _ _, I.add_mem,
  smul_mem' := λ c x H, by { rw [← C_mul'], exact I.mul_mem_left _ H } }

variables {I : ideal R[X]}
theorem mem_of_polynomial (x) : x ∈ I.of_polynomial ↔ x ∈ I := iff.rfl
variables (I)

/-- Given an ideal `I` of `R[X]`, make the `R`-submodule of `I`
consisting of polynomials of degree ≤ `n`. -/
def degree_le (n : with_bot ℕ) : submodule R R[X] :=
degree_le R n ⊓ I.of_polynomial

/-- Given an ideal `I` of `R[X]`, make the ideal in `R` of
leading coefficients of polynomials in `I` with degree ≤ `n`. -/
def leading_coeff_nth (n : ℕ) : ideal R :=
(I.degree_le n).map $ lcoeff R n

/-- Given an ideal `I` in `R[X]`, make the ideal in `R` of the
leading coefficients in `I`. -/
def leading_coeff : ideal R :=
⨆ n : ℕ, I.leading_coeff_nth n

end semiring

section comm_semiring
variables [comm_semiring R] [semiring S]

/-- If every coefficient of a polynomial is in an ideal `I`, then so is the polynomial itself -/
lemma polynomial_mem_ideal_of_coeff_mem_ideal (I : ideal R[X]) (p : R[X])
  (hp : ∀ (n : ℕ), (p.coeff n) ∈ I.comap (C : R →+* R[X])) : p ∈ I :=
sum_C_mul_X_pow_eq p ▸ submodule.sum_mem I (λ n hn, I.mul_mem_right _ (hp n))

/-- The push-forward of an ideal `I` of `R` to `R[X]` via inclusion
 is exactly the set of polynomials whose coefficients are in `I` -/
theorem mem_map_C_iff {I : ideal R} {f : R[X]} :
  f ∈ (ideal.map (C : R →+* R[X]) I : ideal R[X]) ↔ ∀ n : ℕ, f.coeff n ∈ I :=
begin
  split,
  { intros hf,
    apply submodule.span_induction hf,
    { intros f hf n,
      cases (set.mem_image _ _ _).mp hf with x hx,
      rw [← hx.right, coeff_C],
      by_cases (n = 0),
      { simpa [h] using hx.left },
      { simp [h] } },
    { simp },
    { exact λ f g hf hg n, by simp [I.add_mem (hf n) (hg n)] },
    { refine λ f g hg n, _,
      rw [smul_eq_mul, coeff_mul],
      exact I.sum_mem (λ c hc, I.mul_mem_left (f.coeff c.fst) (hg c.snd)) } },
  { intros hf,
    rw ← sum_monomial_eq f,
    refine (I.map C : ideal R[X]).sum_mem (λ n hn, _),
    simp [← C_mul_X_pow_eq_monomial],
    rw mul_comm,
    exact (I.map C : ideal R[X]).mul_mem_left _ (mem_map_of_mem _ (hf n)) }
end

lemma _root_.polynomial.ker_map_ring_hom (f : R →+* S) :
  (polynomial.map_ring_hom f).ker = f.ker.map (C : R →+* R[X]) :=
begin
  ext,
  rw [mem_map_C_iff, ring_hom.mem_ker, polynomial.ext_iff],
  simp_rw [coe_map_ring_hom, coeff_map, coeff_zero, ring_hom.mem_ker],
end

variable (I : ideal R[X])

theorem mem_leading_coeff_nth (n : ℕ) (x) :
  x ∈ I.leading_coeff_nth n ↔ ∃ p ∈ I, degree p ≤ n ∧ p.leading_coeff = x :=
begin
  simp only [leading_coeff_nth, degree_le, submodule.mem_map, lcoeff_apply, submodule.mem_inf,
    mem_degree_le],
  split,
  { rintro ⟨p, ⟨hpdeg, hpI⟩, rfl⟩,
    cases lt_or_eq_of_le hpdeg with hpdeg hpdeg,
    { refine ⟨0, I.zero_mem, bot_le, _⟩,
      rw [leading_coeff_zero, eq_comm],
      exact coeff_eq_zero_of_degree_lt hpdeg },
    { refine ⟨p, hpI, le_of_eq hpdeg, _⟩,
      rw [polynomial.leading_coeff, nat_degree, hpdeg], refl } },
  { rintro ⟨p, hpI, hpdeg, rfl⟩,
    have : nat_degree p + (n - nat_degree p) = n,
    { exact add_tsub_cancel_of_le (nat_degree_le_of_degree_le hpdeg) },
    refine ⟨p * X ^ (n - nat_degree p), ⟨_, I.mul_mem_right _ hpI⟩, _⟩,
    { apply le_trans (degree_mul_le _ _) _,
      apply le_trans (add_le_add (degree_le_nat_degree) (degree_X_pow_le _)) _,
      rw [← with_bot.coe_add, this],
      exact le_rfl },
    { rw [polynomial.leading_coeff, ← coeff_mul_X_pow p (n - nat_degree p), this] } }
end

theorem mem_leading_coeff_nth_zero (x) :
  x ∈ I.leading_coeff_nth 0 ↔ C x ∈ I :=
(mem_leading_coeff_nth _ _ _).trans
⟨λ ⟨p, hpI, hpdeg, hpx⟩, by rwa [← hpx, polynomial.leading_coeff,
  nat.eq_zero_of_le_zero (nat_degree_le_of_degree_le hpdeg),
  ← eq_C_of_degree_le_zero hpdeg],
λ hx, ⟨C x, hx, degree_C_le, leading_coeff_C x⟩⟩

theorem leading_coeff_nth_mono {m n : ℕ} (H : m ≤ n) :
  I.leading_coeff_nth m ≤ I.leading_coeff_nth n :=
begin
  intros r hr,
  simp only [set_like.mem_coe, mem_leading_coeff_nth] at hr ⊢,
  rcases hr with ⟨p, hpI, hpdeg, rfl⟩,
  refine ⟨p * X ^ (n - m), I.mul_mem_right _ hpI, _, leading_coeff_mul_X_pow⟩,
  refine le_trans (degree_mul_le _ _) _,
  refine le_trans (add_le_add hpdeg (degree_X_pow_le _)) _,
  rw [← with_bot.coe_add, add_tsub_cancel_of_le H],
  exact le_rfl
end

theorem mem_leading_coeff (x) :
  x ∈ I.leading_coeff ↔ ∃ p ∈ I, polynomial.leading_coeff p = x :=
begin
  rw [leading_coeff, submodule.mem_supr_of_directed],
  simp only [mem_leading_coeff_nth],
  { split, { rintro ⟨i, p, hpI, hpdeg, rfl⟩, exact ⟨p, hpI, rfl⟩ },
    rintro ⟨p, hpI, rfl⟩, exact ⟨nat_degree p, p, hpI, degree_le_nat_degree, rfl⟩ },
  intros i j, exact ⟨i + j, I.leading_coeff_nth_mono (nat.le_add_right _ _),
    I.leading_coeff_nth_mono (nat.le_add_left _ _)⟩
end

/--
If `I` is an ideal, and `pᵢ` is a finite family of polynomials each satisfying
`∀ k, (pᵢ)ₖ ∈ Iⁿⁱ⁻ᵏ` for some `nᵢ`, then `p = ∏ pᵢ` also satisfies `∀ k, pₖ ∈ Iⁿ⁻ᵏ` with `n = ∑ nᵢ`.
-/
lemma _root_.polynomial.coeff_prod_mem_ideal_pow_tsub {ι : Type*} (s : finset ι) (f : ι → R[X])
  (I : ideal R) (n : ι → ℕ) (h : ∀ (i ∈ s) k, (f i).coeff k ∈ I ^ (n i - k)) (k : ℕ) :
  (s.prod f).coeff k ∈ I ^ (s.sum n - k) :=
begin
  classical,
  induction s using finset.induction with a s ha hs generalizing k,
  { rw [sum_empty, prod_empty, coeff_one, zero_tsub, pow_zero, ideal.one_eq_top],
    exact submodule.mem_top },
  { rw [sum_insert ha, prod_insert ha, coeff_mul],
    apply sum_mem,
    rintro ⟨i, j⟩ e,
    obtain rfl : i + j = k := nat.mem_antidiagonal.mp e,
    apply ideal.pow_le_pow add_tsub_add_le_tsub_add_tsub,
    rw pow_add,
    exact ideal.mul_mem_mul (h _ (finset.mem_insert.mpr $ or.inl rfl) _)
      (hs (λ i hi k, h _ (finset.mem_insert.mpr $ or.inr hi) _) j) }
end

end comm_semiring

section ring
variables [ring R]

/-- `R[X]` is never a field for any ring `R`. -/
lemma polynomial_not_is_field : ¬ is_field R[X] :=
begin
  nontriviality R,
  intro hR,
  obtain ⟨p, hp⟩ := hR.mul_inv_cancel X_ne_zero,
  have hp0 : p ≠ 0,
  { rintro rfl,
    rw [mul_zero] at hp,
    exact zero_ne_one hp },
  have := degree_lt_degree_mul_X hp0,
  rw [←X_mul, congr_arg degree hp, degree_one, nat.with_bot.lt_zero_iff, degree_eq_bot] at this,
  exact hp0 this,
end

/-- The only constant in a maximal ideal over a field is `0`. -/
lemma eq_zero_of_constant_mem_of_maximal (hR : is_field R)
  (I : ideal R[X]) [hI : I.is_maximal] (x : R) (hx : C x ∈ I) : x = 0 :=
begin
  refine classical.by_contradiction (λ hx0, hI.ne_top ((eq_top_iff_one I).2 _)),
  obtain ⟨y, hy⟩ := hR.mul_inv_cancel hx0,
  convert I.mul_mem_left (C y) hx,
  rw [← C.map_mul, hR.mul_comm y x, hy, ring_hom.map_one],
end

end ring

section comm_ring
variables [comm_ring R]

/-- If `P` is a prime ideal of `R`, then `P.R[x]` is a prime ideal of `R[x]`. -/
lemma is_prime_map_C_iff_is_prime (P : ideal R) :
  is_prime (map (C : R →+* R[X]) P : ideal R[X]) ↔ is_prime P :=
begin
  -- Porting note: the following proof avoids quotient rings
  -- It can be golfed substantially by using something like
  -- `(quotient.is_domain_iff_prime (map C P : ideal R[X]))`
  split,
  { intro H,
    have := @comap_is_prime R R[X] (R →+* R[X]) _ _ _ C (map C P) H,
    convert this using 1,
    ext x,
    simp only [mem_comap, mem_map_C_iff],
    split,
    { rintro h (-|n),
      { simpa only [coeff_C_zero] using h },
      { simp only [coeff_C_ne_zero (nat.succ_ne_zero _), submodule.zero_mem] } },
    { intro h, simpa only [coeff_C_zero] using h 0 } },
  { intro h,
    constructor,
    { rw [ne.def, eq_top_iff_one, mem_map_C_iff, not_forall],
      use 0,
      rw [coeff_one_zero, ← eq_top_iff_one], exact h.1 },
    { intros f g, simp only [mem_map_C_iff], contrapose!,
      rintro ⟨hf, hg⟩,
      classical,
      let m := nat.find hf,
      let n := nat.find hg,
      refine ⟨m + n, _⟩,
      rw [coeff_mul, ← finset.insert_erase ((@finset.nat.mem_antidiagonal _ (m,n)).mpr rfl),
        finset.sum_insert (finset.not_mem_erase _ _), (P.add_mem_iff_left _).not],
      { apply mt h.2, rw [not_or_distrib], exact ⟨nat.find_spec hf, nat.find_spec hg⟩ },
      apply P.sum_mem,
      rintro ⟨i, j⟩ hij,
      rw [finset.mem_erase, finset.nat.mem_antidiagonal] at hij,
      simp only [ne.def, prod.mk.inj_iff, not_and_distrib] at hij,
      obtain (hi|hj) : i < m ∨ j < n,
      { rw [or_iff_not_imp_left, not_lt, le_iff_lt_or_eq],
        rintro (hmi|rfl),
        { rw [← not_le], intro hnj, exact (add_lt_add_of_lt_of_le hmi hnj).ne hij.2.symm, },
        { simpa only [eq_self_iff_true, not_true, false_or, add_right_inj, not_and_self]
            using hij, } },
      { rw [mul_comm], apply P.mul_mem_left, exact not_not.1 (nat.find_min hf hi) },
      { apply P.mul_mem_left, exact not_not.1 (nat.find_min hg hj) } } }
end

/-- If `P` is a prime ideal of `R`, then `P.R[x]` is a prime ideal of `R[x]`. -/
lemma is_prime_map_C_of_is_prime {P : ideal R} (H : is_prime P) :
  is_prime (map (C : R →+* R[X]) P : ideal R[X]) :=
(is_prime_map_C_iff_is_prime P).mpr H

theorem is_fg_degree_le [is_noetherian_ring R] (I : ideal R[X]) (n : ℕ) :
  submodule.fg (I.degree_le n) :=
is_noetherian_submodule_left.1 (is_noetherian_of_fg_of_noetherian _
  ⟨_, degree_le_eq_span_X_pow.symm⟩) _

end comm_ring

end ideal

variables {σ : Type v} {M : Type w}
variables [comm_ring R] [comm_ring S] [add_comm_group M] [module R M]

section prime
variables (σ) {r : R}

namespace polynomial
lemma prime_C_iff : prime (C r) ↔ prime r :=
⟨ comap_prime C (eval_ring_hom (0 : R)) (λ r, eval_C),
  λ hr, by { have := hr.1,
    rw ← ideal.span_singleton_prime at hr ⊢,
    { convert ideal.is_prime_map_C_of_is_prime hr using 1,
      rw [ideal.map_span, set.image_singleton] },
    exacts [λ h, this (C_eq_zero.1 h), this] } ⟩
end polynomial

namespace mv_polynomial

private lemma prime_C_iff_of_fintype [fintype σ] : prime (C r : mv_polynomial σ R) ↔ prime r :=
begin
  rw (rename_equiv R (fintype.equiv_fin σ)).to_mul_equiv.prime_iff,
  convert_to prime (C r) ↔ _, { congr, apply rename_C },
  { symmetry, induction fintype.card σ with d hd,
    { exact (is_empty_alg_equiv R (fin 0)).to_mul_equiv.symm.prime_iff },
    { rw [hd, ← polynomial.prime_C_iff],
      convert (fin_succ_equiv R d).to_mul_equiv.symm.prime_iff,
      rw ← fin_succ_equiv_comp_C_eq_C, refl } },
end

lemma prime_C_iff : prime (C r : mv_polynomial σ R) ↔ prime r :=
⟨ comap_prime C constant_coeff (constant_coeff_C _),
  λ hr, ⟨ λ h, hr.1 $ by { rw [← C_inj, h], simp },
    λ h, hr.2.1 $ by { rw ← constant_coeff_C _ r, exact h.map _ },
    λ a b hd, begin
      obtain ⟨s,a',b',rfl,rfl⟩ := exists_finset_rename₂ a b,
      rw ← algebra_map_eq at hd, have : algebra_map R _ r ∣ a' * b',
      { convert (kill_compl subtype.coe_injective).to_ring_hom.map_dvd hd, simpa, simp },
      rw ← rename_C (coe : s → σ), let f := (rename (coe : s → σ)).to_ring_hom,
      exact (((prime_C_iff_of_fintype s).2 hr).2.2 a' b' this).imp f.map_dvd f.map_dvd,
    end ⟩ ⟩

variable {σ}
lemma prime_rename_iff (s : set σ) {p : mv_polynomial s R} :
  prime (rename (coe : s → σ) p) ↔ prime p :=
begin
  classical, symmetry, let eqv := (sum_alg_equiv R _ _).symm.trans
    (rename_equiv R $ (equiv.sum_comm ↥sᶜ s).trans $ equiv.set.sum_compl s),
  rw [← prime_C_iff ↥sᶜ, eqv.to_mul_equiv.prime_iff], convert iff.rfl,
  suffices : (rename coe).to_ring_hom = eqv.to_alg_hom.to_ring_hom.comp C,
  { apply ring_hom.congr_fun this },
  { apply ring_hom_ext,
    { intro, dsimp [eqv], erw [iter_to_sum_C_C, rename_C, rename_C] },
    { intro, dsimp [eqv], erw [iter_to_sum_C_X, rename_X, rename_X], refl } },
end

end mv_polynomial

end prime

namespace polynomial

@[priority 100]
instance {R : Type*} [comm_ring R] [is_domain R] [wf_dvd_monoid R] :
  wf_dvd_monoid R[X] :=
{ well_founded_dvd_not_unit := begin
    classical,
    refine rel_hom_class.well_founded (⟨λ (p : R[X]),
        ((if p = 0 then ⊤ else ↑p.degree : with_top (with_bot ℕ)), p.leading_coeff), _⟩ :
        dvd_not_unit →r prod.lex (<) dvd_not_unit)
      (prod.lex_wf (with_top.well_founded_lt $ with_bot.well_founded_lt nat.lt_wf)
        ‹wf_dvd_monoid R›.well_founded_dvd_not_unit),
    rintros a b ⟨ane0, ⟨c, ⟨not_unit_c, rfl⟩⟩⟩,
    rw [polynomial.degree_mul, if_neg ane0],
    split_ifs with hac,
    { rw [hac, polynomial.leading_coeff_zero],
      apply prod.lex.left,
      exact lt_of_le_of_ne le_top with_top.coe_ne_top },
    have cne0 : c ≠ 0 := right_ne_zero_of_mul hac,
    simp only [cne0, ane0, polynomial.leading_coeff_mul],
    by_cases hdeg : c.degree = 0,
    { simp only [hdeg, add_zero],
      refine prod.lex.right _ ⟨_, ⟨c.leading_coeff, (λ unit_c, not_unit_c _), rfl⟩⟩,
      { rwa [ne, polynomial.leading_coeff_eq_zero] },
      rw [polynomial.is_unit_iff, polynomial.eq_C_of_degree_eq_zero hdeg],
      use [c.leading_coeff, unit_c],
      rw [polynomial.leading_coeff, polynomial.nat_degree_eq_of_degree_eq_some hdeg] },
    { apply prod.lex.left,
      rw polynomial.degree_eq_nat_degree cne0 at *,
      rw [with_top.coe_lt_coe, polynomial.degree_eq_nat_degree ane0,
          ← with_bot.coe_add, with_bot.coe_lt_coe],
      exact lt_add_of_pos_right _ (nat.pos_of_ne_zero (λ h, hdeg (h.symm ▸ with_bot.coe_zero))) },
  end }

end polynomial

/-- Hilbert basis theorem: a polynomial ring over a noetherian ring is a noetherian ring. -/
protected theorem polynomial.is_noetherian_ring [is_noetherian_ring R] :
  is_noetherian_ring R[X] :=
is_noetherian_ring_iff.2 ⟨assume I : ideal R[X],
let M := well_founded.min (is_noetherian_iff_well_founded.1 (by apply_instance))
  (set.range I.leading_coeff_nth) ⟨_, ⟨0, rfl⟩⟩ in
have hm : M ∈ set.range I.leading_coeff_nth := well_founded.min_mem _ _ _,
let ⟨N, HN⟩ := hm, ⟨s, hs⟩ := I.is_fg_degree_le N in
have hm2 : ∀ k, I.leading_coeff_nth k ≤ M := λ k, or.cases_on (le_or_lt k N)
  (λ h, HN ▸ I.leading_coeff_nth_mono h)
  (λ h x hx, classical.by_contradiction $ λ hxm,
    have ¬M < I.leading_coeff_nth k, by refine well_founded.not_lt_min
      (well_founded_submodule_gt _ _) _ _ _; exact ⟨k, rfl⟩,
    this ⟨HN ▸ I.leading_coeff_nth_mono (le_of_lt h), λ H, hxm (H hx)⟩),
have hs2 : ∀ {x}, x ∈ I.degree_le N → x ∈ ideal.span (↑s : set R[X]),
from hs ▸ λ x hx, submodule.span_induction hx (λ _ hx, ideal.subset_span hx) (ideal.zero_mem _)
  (λ _ _, ideal.add_mem _) (λ c f hf, f.C_mul' c ▸ ideal.mul_mem_left _ _ hf),
⟨s, le_antisymm
  (ideal.span_le.2 $ λ x hx, have x ∈ I.degree_le N, from hs ▸ submodule.subset_span hx, this.2) $
begin
  have : submodule.span R[X] ↑s = ideal.span ↑s, by refl,
  rw this,
  intros p hp, generalize hn : p.nat_degree = k,
  induction k using nat.strong_induction_on with k ih generalizing p,
  cases le_or_lt k N,
  { subst k, refine hs2 ⟨polynomial.mem_degree_le.2
      (le_trans polynomial.degree_le_nat_degree $ with_bot.coe_le_coe.2 h), hp⟩ },
  { have hp0 : p ≠ 0,
    { rintro rfl, cases hn, exact nat.not_lt_zero _ h },
    have : (0 : R) ≠ 1,
    { intro h, apply hp0, ext i, refine (mul_one _).symm.trans _,
      rw [← h, mul_zero], refl },
    haveI : nontrivial R := ⟨⟨0, 1, this⟩⟩,
    have : p.leading_coeff ∈ I.leading_coeff_nth N,
    { rw HN, exact hm2 k ((I.mem_leading_coeff_nth _ _).2
        ⟨_, hp, hn ▸ polynomial.degree_le_nat_degree, rfl⟩) },
    rw I.mem_leading_coeff_nth at this,
    rcases this with ⟨q, hq, hdq, hlqp⟩,
    have hq0 : q ≠ 0,
    { intro H, rw [← polynomial.leading_coeff_eq_zero] at H,
      rw [hlqp, polynomial.leading_coeff_eq_zero] at H, exact hp0 H },
    have h1 : p.degree = (q * polynomial.X ^ (k - q.nat_degree)).degree,
    { rw [polynomial.degree_mul', polynomial.degree_X_pow],
      rw [polynomial.degree_eq_nat_degree hp0, polynomial.degree_eq_nat_degree hq0],
      rw [← with_bot.coe_add, add_tsub_cancel_of_le, hn],
      { refine le_trans (polynomial.nat_degree_le_of_degree_le hdq) (le_of_lt h) },
      rw [polynomial.leading_coeff_X_pow, mul_one],
      exact mt polynomial.leading_coeff_eq_zero.1 hq0 },
    have h2 : p.leading_coeff = (q * polynomial.X ^ (k - q.nat_degree)).leading_coeff,
    { rw [← hlqp, polynomial.leading_coeff_mul_X_pow] },
    have := polynomial.degree_sub_lt h1 hp0 h2,
    rw [polynomial.degree_eq_nat_degree hp0] at this,
    rw ← sub_add_cancel p (q * polynomial.X ^ (k - q.nat_degree)),
    refine (ideal.span ↑s).add_mem _ ((ideal.span ↑s).mul_mem_right _ _),
    { by_cases hpq : p - q * polynomial.X ^ (k - q.nat_degree) = 0,
      { rw hpq, exact ideal.zero_mem _ },
      refine ih _ _ (I.sub_mem hp (I.mul_mem_right _ hq)) rfl,
      rwa [polynomial.degree_eq_nat_degree hpq, with_bot.coe_lt_coe, hn] at this },
    exact hs2 ⟨polynomial.mem_degree_le.2 hdq, hq⟩ }
end⟩⟩

attribute [instance] polynomial.is_noetherian_ring

namespace polynomial

theorem exists_irreducible_of_degree_pos
  {R : Type u} [comm_ring R] [is_domain R] [wf_dvd_monoid R]
  {f : R[X]} (hf : 0 < f.degree) : ∃ g, irreducible g ∧ g ∣ f :=
wf_dvd_monoid.exists_irreducible_factor
  (λ huf, ne_of_gt hf $ degree_eq_zero_of_is_unit huf)
  (λ hf0, not_lt_of_lt hf $ hf0.symm ▸ (@degree_zero R _).symm ▸ with_bot.bot_lt_coe _)

theorem exists_irreducible_of_nat_degree_pos
  {R : Type u} [comm_ring R] [is_domain R] [wf_dvd_monoid R]
  {f : R[X]} (hf : 0 < f.nat_degree) : ∃ g, irreducible g ∧ g ∣ f :=
exists_irreducible_of_degree_pos $ by { contrapose! hf, exact nat_degree_le_of_degree_le hf }

theorem exists_irreducible_of_nat_degree_ne_zero
  {R : Type u} [comm_ring R] [is_domain R] [wf_dvd_monoid R]
  {f : R[X]} (hf : f.nat_degree ≠ 0) : ∃ g, irreducible g ∧ g ∣ f :=
exists_irreducible_of_nat_degree_pos $ nat.pos_of_ne_zero hf

lemma linear_independent_powers_iff_aeval
  (f : M →ₗ[R] M) (v : M) :
  linear_independent R (λ n : ℕ, (f ^ n) v)
    ↔ ∀ (p : R[X]), aeval f p v = 0 → p = 0 :=
begin
  rw linear_independent_iff,
  simp only [finsupp.total_apply, aeval_endomorphism, forall_iff_forall_finsupp, sum, support,
    coeff, of_finsupp_eq_zero],
  exact iff.rfl,
end

lemma disjoint_ker_aeval_of_coprime
  (f : M →ₗ[R] M) {p q : R[X]} (hpq : is_coprime p q) :
  disjoint (aeval f p).ker (aeval f q).ker :=
begin
  rw disjoint_iff_inf_le,
  intros v hv,
  rcases hpq with ⟨p', q', hpq'⟩,
  simpa [linear_map.mem_ker.1 (submodule.mem_inf.1 hv).1,
         linear_map.mem_ker.1 (submodule.mem_inf.1 hv).2]
    using congr_arg (λ p : R[X], aeval f p v) hpq'.symm,
end

lemma sup_aeval_range_eq_top_of_coprime
  (f : M →ₗ[R] M) {p q : R[X]} (hpq : is_coprime p q) :
  (aeval f p).range ⊔ (aeval f q).range = ⊤ :=
begin
  rw eq_top_iff,
  intros v hv,
  rw submodule.mem_sup,
  rcases hpq with ⟨p', q', hpq'⟩,
  use aeval f (p * p') v,
  use linear_map.mem_range.2 ⟨aeval f p' v, by simp only [linear_map.mul_apply, aeval_mul]⟩,
  use aeval f (q * q') v,
  use linear_map.mem_range.2 ⟨aeval f q' v, by simp only [linear_map.mul_apply, aeval_mul]⟩,
  simpa only [mul_comm p p', mul_comm q q', aeval_one, aeval_add]
    using congr_arg (λ p : R[X], aeval f p v) hpq'
end

lemma sup_ker_aeval_le_ker_aeval_mul {f : M →ₗ[R] M} {p q : R[X]} :
  (aeval f p).ker ⊔ (aeval f q).ker ≤ (aeval f (p * q)).ker :=
begin
  intros v hv,
  rcases submodule.mem_sup.1 hv with ⟨x, hx, y, hy, hxy⟩,
  have h_eval_x : aeval f (p * q) x = 0,
  { rw [mul_comm, aeval_mul, linear_map.mul_apply, linear_map.mem_ker.1 hx, linear_map.map_zero] },
  have h_eval_y : aeval f (p * q) y = 0,
  { rw [aeval_mul, linear_map.mul_apply, linear_map.mem_ker.1 hy, linear_map.map_zero] },
  rw [linear_map.mem_ker, ←hxy, linear_map.map_add, h_eval_x, h_eval_y, add_zero],
end

lemma sup_ker_aeval_eq_ker_aeval_mul_of_coprime
  (f : M →ₗ[R] M) {p q : R[X]} (hpq : is_coprime p q) :
  (aeval f p).ker ⊔ (aeval f q).ker = (aeval f (p * q)).ker :=
begin
  apply le_antisymm sup_ker_aeval_le_ker_aeval_mul,
  intros v hv,
  rw submodule.mem_sup,
  rcases hpq with ⟨p', q', hpq'⟩,
  have h_eval₂_qpp' := calc
    aeval f (q * (p * p')) v = aeval f (p' * (p * q)) v :
      by rw [mul_comm, mul_assoc, mul_comm, mul_assoc, mul_comm q p]
    ... = 0 :
      by rw [aeval_mul, linear_map.mul_apply, linear_map.mem_ker.1 hv, linear_map.map_zero],
  have h_eval₂_pqq' := calc
    aeval f (p * (q * q')) v = aeval f (q' * (p * q)) v :
      by rw [←mul_assoc, mul_comm]
    ... = 0 :
      by rw [aeval_mul, linear_map.mul_apply, linear_map.mem_ker.1 hv, linear_map.map_zero],
  rw aeval_mul at h_eval₂_qpp' h_eval₂_pqq',
  refine ⟨aeval f (q * q') v, linear_map.mem_ker.1 h_eval₂_pqq',
          aeval f (p * p') v, linear_map.mem_ker.1 h_eval₂_qpp', _⟩,
  rw [add_comm, mul_comm p p', mul_comm q q'],
  simpa only [map_add, map_mul, aeval_one] using congr_arg (λ p : R[X], aeval f p v) hpq'
end

end polynomial

namespace mv_polynomial

lemma is_noetherian_ring_fin_0 [is_noetherian_ring R] :
  is_noetherian_ring (mv_polynomial (fin 0) R) :=
is_noetherian_ring_of_ring_equiv R
  ((mv_polynomial.is_empty_ring_equiv R pempty).symm.trans
   (rename_equiv R fin_zero_equiv'.symm).to_ring_equiv)

theorem is_noetherian_ring_fin [is_noetherian_ring R] :
  ∀ {n : ℕ}, is_noetherian_ring (mv_polynomial (fin n) R)
| 0 := is_noetherian_ring_fin_0
| (n+1) :=
  @is_noetherian_ring_of_ring_equiv (polynomial (mv_polynomial (fin n) R)) _ _ _
    (mv_polynomial.fin_succ_equiv _ n).to_ring_equiv.symm
    (@polynomial.is_noetherian_ring (mv_polynomial (fin n) R) _ (is_noetherian_ring_fin))

/-- The multivariate polynomial ring in finitely many variables over a noetherian ring
is itself a noetherian ring. -/
instance is_noetherian_ring [finite σ] [is_noetherian_ring R] :
  is_noetherian_ring (mv_polynomial σ R) :=
by casesI nonempty_fintype σ; exact
@is_noetherian_ring_of_ring_equiv (mv_polynomial (fin (fintype.card σ)) R) _ _ _
  (rename_equiv R (fintype.equiv_fin σ).symm).to_ring_equiv is_noetherian_ring_fin

/-- Auxiliary lemma:
Multivariate polynomials over an integral domain
with variables indexed by `fin n` form an integral domain.
This fact is proven inductively,
and then used to prove the general case without any finiteness hypotheses.
See `mv_polynomial.no_zero_divisors` for the general case. -/
lemma no_zero_divisors_fin (R : Type u) [comm_semiring R] [no_zero_divisors R] :
  ∀ (n : ℕ), no_zero_divisors (mv_polynomial (fin n) R)
| 0 := (mv_polynomial.is_empty_alg_equiv R _).injective.no_zero_divisors _ (map_zero _) (map_mul _)
| (n+1) := begin
    haveI := no_zero_divisors_fin n,
    exact (mv_polynomial.fin_succ_equiv R n).injective.no_zero_divisors _ (map_zero _) (map_mul _)
  end

/-- Auxiliary definition:
Multivariate polynomials in finitely many variables over an integral domain form an integral domain.
This fact is proven by transport of structure from the `mv_polynomial.no_zero_divisors_fin`,
and then used to prove the general case without finiteness hypotheses.
See `mv_polynomial.no_zero_divisors` for the general case. -/
lemma no_zero_divisors_of_finite (R : Type u) (σ : Type v) [comm_semiring R] [finite σ]
  [no_zero_divisors R] : no_zero_divisors (mv_polynomial σ R) :=
begin
  casesI nonempty_fintype σ,
  haveI := no_zero_divisors_fin R (fintype.card σ),
  exact (rename_equiv R (fintype.equiv_fin σ)).injective.no_zero_divisors _ (map_zero _) (map_mul _)
end

instance {R : Type u} [comm_semiring R] [no_zero_divisors R] {σ : Type v} :
  no_zero_divisors (mv_polynomial σ R) :=
⟨λ p q h, begin
  obtain ⟨s, p, rfl⟩ := exists_finset_rename p,
  obtain ⟨t, q, rfl⟩ := exists_finset_rename q,
  have :
    rename (subtype.map id (finset.subset_union_left s t) : {x // x ∈ s} → {x // x ∈ s ∪ t}) p *
    rename (subtype.map id (finset.subset_union_right s t) : {x // x ∈ t} → {x // x ∈ s ∪ t}) q = 0,
  { apply rename_injective _ subtype.val_injective, simpa using h },
  letI := mv_polynomial.no_zero_divisors_of_finite R {x // x ∈ (s ∪ t)},
  rw mul_eq_zero at this,
  cases this; [left, right],
  all_goals { simpa using congr_arg (rename subtype.val) this }
end⟩

/-- The multivariate polynomial ring over an integral domain is an integral domain. -/
instance {R : Type u} {σ : Type v} [comm_ring R] [is_domain R] : is_domain (mv_polynomial σ R) :=
begin
  apply no_zero_divisors.to_is_domain _,
  exact add_monoid_algebra.nontrivial,
  exact mv_polynomial.no_zero_divisors
end

lemma map_mv_polynomial_eq_eval₂ {S : Type*} [comm_ring S] [finite σ]
  (ϕ : mv_polynomial σ R →+* S) (p : mv_polynomial σ R) :
  ϕ p = mv_polynomial.eval₂ (ϕ.comp mv_polynomial.C) (λ s, ϕ (mv_polynomial.X s)) p :=
begin
  casesI nonempty_fintype σ,
  refine trans (congr_arg ϕ (mv_polynomial.as_sum p)) _,
  rw [mv_polynomial.eval₂_eq', ϕ.map_sum],
  congr,
  ext,
  simp only [monomial_eq, ϕ.map_pow, ϕ.map_prod, ϕ.comp_apply, ϕ.map_mul, finsupp.prod_pow],
end

/-- If every coefficient of a polynomial is in an ideal `I`, then so is the polynomial itself,
multivariate version. -/
lemma mem_ideal_of_coeff_mem_ideal (I : ideal (mv_polynomial σ R)) (p : mv_polynomial σ R)
  (hcoe : ∀ (m : σ →₀ ℕ), p.coeff m ∈ I.comap (C : R →+* mv_polynomial σ R)) : p ∈ I :=
begin
  rw as_sum p,
  suffices : ∀ m ∈ p.support, monomial m (mv_polynomial.coeff m p) ∈ I,
  { exact submodule.sum_mem I this },
  intros m hm,
  rw [← mul_one (coeff m p), ← C_mul_monomial],
  suffices : C (coeff m p) ∈ I,
  { exact I.mul_mem_right (monomial m 1) this },
  simpa [ideal.mem_comap] using hcoe m
end

/-- The push-forward of an ideal `I` of `R` to `mv_polynomial σ R` via inclusion
 is exactly the set of polynomials whose coefficients are in `I` -/
theorem mem_map_C_iff {I : ideal R} {f : mv_polynomial σ R} :
  f ∈ (ideal.map (C : R →+* mv_polynomial σ R) I :
  ideal (mv_polynomial σ R)) ↔ ∀ (m : σ →₀ ℕ), f.coeff m ∈ I :=
begin
  split,
  { intros hf,
    apply submodule.span_induction hf,
    { intros f hf n,
      cases (set.mem_image _ _ _).mp hf with x hx,
      rw [← hx.right, coeff_C],
      by_cases (n = 0),
      { simpa [h] using hx.left },
      { simp [ne.symm h] } },
    { simp },
    { exact λ f g hf hg n, by simp [I.add_mem (hf n) (hg n)] },
    { refine λ f g hg n, _,
      rw [smul_eq_mul, coeff_mul],
      exact I.sum_mem (λ c hc, I.mul_mem_left (f.coeff c.fst) (hg c.snd)) } },
  { intros hf,
    rw as_sum f,
    suffices : ∀ m ∈ f.support, monomial m (coeff m f) ∈
      (ideal.map C I : ideal (mv_polynomial σ R)),
    { exact submodule.sum_mem _ this },
    intros m hm,
    rw [← mul_one (coeff m f), ← C_mul_monomial],
    suffices : C (coeff m f) ∈ (ideal.map C I : ideal (mv_polynomial σ R)),
    { exact ideal.mul_mem_right _ _ this },
    apply ideal.mem_map_of_mem _,
    exact hf m }
end

lemma ker_map (f : R →+* S) :
  (map f : mv_polynomial σ R →+* mv_polynomial σ S).ker = f.ker.map (C : R →+* mv_polynomial σ R) :=
begin
  ext,
  rw [mv_polynomial.mem_map_C_iff, ring_hom.mem_ker, mv_polynomial.ext_iff],
  simp_rw [coeff_map, coeff_zero, ring_hom.mem_ker],
end

end mv_polynomial

section unique_factorization_domain
variables {D : Type u} [comm_ring D] [is_domain D] [unique_factorization_monoid D] (σ)
open unique_factorization_monoid

namespace polynomial

@[priority 100]
instance unique_factorization_monoid : unique_factorization_monoid D[X] :=
begin
  haveI := arbitrary (normalization_monoid D),
  haveI := to_normalized_gcd_monoid D,
  exact ufm_of_gcd_of_wf_dvd_monoid
end

end polynomial

namespace mv_polynomial

private lemma unique_factorization_monoid_of_fintype [fintype σ] :
  unique_factorization_monoid (mv_polynomial σ D) :=
(rename_equiv D (fintype.equiv_fin σ)).to_mul_equiv.symm.unique_factorization_monoid $
begin
  induction fintype.card σ with d hd,
  { apply (is_empty_alg_equiv D (fin 0)).to_mul_equiv.symm.unique_factorization_monoid,
    apply_instance },
  { apply (fin_succ_equiv D d).to_mul_equiv.symm.unique_factorization_monoid,
    exactI polynomial.unique_factorization_monoid },
end

@[priority 100]
instance : unique_factorization_monoid (mv_polynomial σ D) :=
begin
  rw iff_exists_prime_factors,
  intros a ha, obtain ⟨s,a',rfl⟩ := exists_finset_rename a,
  obtain ⟨w,h,u,hw⟩ := iff_exists_prime_factors.1
    (unique_factorization_monoid_of_fintype s) a' (λ h, ha $ by simp [h]),
  exact ⟨ w.map (rename coe),
    λ b hb, let ⟨b',hb',he⟩ := multiset.mem_map.1 hb in he ▸ (prime_rename_iff ↑s).2 (h b' hb'),
    units.map (@rename s σ D _ coe).to_ring_hom.to_monoid_hom u,
    by erw [multiset.prod_hom, ← map_mul, hw] ⟩,
end

end mv_polynomial
end unique_factorization_domain
