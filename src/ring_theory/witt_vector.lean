-- import data.list.basic
-- import data.set.finite
import data.nat.prime
import data.nat.choose
import data.int.gcd
import data.mv_polynomial
import algebra.group_power
-- import algebra.char_p
import group_theory.subgroup
import ring_theory.multiplicity
-- import ring_theory.unique_factorization_domain
-- import data.padics.padic_integers
-- import number_theory.quadratic_reciprocity
import algebra.invertible
-- import deprecated.group

import tactic

universes u v w u₁

-- ### FOR_MATHLIB
-- everything in this section should move to other files

section finset

variables {G : Type u} [comm_group G]
variables {H : Type v} [comm_group H]
variables (i : G → H) [is_group_hom i]
variables {X : Type w} [decidable_eq X] (s : finset X) (f : X → G)

-- Generalise this to arbitrary property that is respected by addition/multiplication:
-- example applications: sum_pos, sum_neg, ... others?
lemma dvd_sum {α : Type*} {β : Type*} [decidable_eq α] [comm_ring β]
  (s : finset α) (f : α → β) (b : β) (H : ∀ a ∈ s, b ∣ f a) :
  b ∣ s.sum f :=
begin
  let t := s,
  replace H : ∀ a ∈ t, b ∣ f a := H,
  have hs : s ⊆ t := finset.subset.refl s,
  revert hs,
  apply finset.induction_on s, {simp},
  intros a s' ha IH hs',
  rw finset.insert_subset at hs',
  cases hs' with has hs',
  simp [*, dvd_add]
end

lemma coe_nat_dvd {α : Type*} [comm_ring α] (m n : ℕ) (h : m ∣ n) :
  (m : α) ∣ n :=
by { rcases h with ⟨k, rfl⟩, refine ⟨k, by norm_cast⟩ }

end finset

namespace mv_polynomial

open mv_polynomial finsupp

lemma eval₂_assoc'
  {R : Type*} [decidable_eq R] [comm_semiring R]
  {S : Type*} [decidable_eq S] [comm_semiring S]
  {T : Type*} [decidable_eq T] [comm_semiring T]
  {σ : Type*} [decidable_eq σ]
  {τ : Type*} [decidable_eq τ]
  {ι : Type*} [decidable_eq ι]
  (f : S → T) [is_semiring_hom f]
  (φ : σ → T) (q : τ → mv_polynomial σ S)
  (p : mv_polynomial τ S) :
  eval₂ f (λ t, eval₂ f φ (q t)) p = eval₂ f φ (eval₂ C q p) :=
by { rw eval₂_comp_left (eval₂ f φ), congr, funext, simp }

variables {R : Type*} {S : Type*} (f : R → S) {ι : Type*}
variables [decidable_eq R] [comm_ring R]
variables [decidable_eq S] [comm_ring S]
variables [is_ring_hom f] [decidable_eq ι]

lemma eval₂_sum' {X : Type*} [decidable_eq X] (s : finset X) (g : ι → S)
  (i : X → mv_polynomial ι R) :
  eval₂ f g (s.sum i) = s.sum (λ x, eval₂ f g $ i x) :=
begin
  apply finset.induction_on s,
  { simp },
  { intros x' s' hx' IH,
    simp [finset.sum_insert hx', IH] }
end

end mv_polynomial

namespace modp
variables {α : Type*} [comm_ring α] {p : ℕ} (hp : nat.prime p)

notation x ` modᵢ ` I := (ideal.quotient.mk I x)
notation x ` modₛ ` s := (ideal.quotient.mk (ideal.span s) x)
notation x ` modₑ ` a := (ideal.quotient.mk (ideal.span ({a})) x)

lemma char_one.one_eq_zero [char_p α 1] : (1 : α) = 0 :=
by exact_mod_cast char_p.cast_eq_zero α 1

lemma char_one.elim [char_p α 1] (a b : α) : a = b :=
by rw [← one_mul a, ← one_mul b, char_one.one_eq_zero, zero_mul, zero_mul]

instance char_one_of_is_unit (h : is_unit (p : α)) :
  char_p (ideal.span ({p} : set α)).quotient 1 :=
⟨begin
  intro n,
  have helper : ∀ m : ℕ, (m : (ideal.span ({p} : set α)).quotient) =
    ideal.quotient.mk (ideal.span ({p} : set α)) (m : α),
  { intro m, induction m with m ih, {refl}, simp [ih] },
  split,
  { intro hn, exact one_dvd n },
  { rintro ⟨c, rfl⟩,
    rw is_unit_iff_exists_inv at h,
    rcases h with ⟨b, hb⟩,
    rw [helper, nat.cast_mul, nat.cast_one, ← hb,
      ideal.quotient.eq_zero_iff_mem, mul_assoc],
    exact ideal.mul_mem_right _ (ideal.subset_span $ set.mem_singleton p) }
end⟩

include hp
instance (h : ¬ is_unit (p : α)) : char_p (ideal.span ({p} : set α)).quotient p :=
⟨begin
  intro n,
  have helper : ∀ m : ℕ, (m : (ideal.span ({p} : set α)).quotient) =
    ideal.quotient.mk (ideal.span ({p} : set α)) (m : α),
  { intro m, induction m with m ih, {refl}, simp [ih] },
  split,
  { intro H,
    rw [helper, ideal.quotient.eq_zero_iff_mem, ideal.mem_span_singleton] at H,
    rcases H with ⟨c, hc⟩,
    cases nat.coprime_or_dvd_of_prime hp n with hn hn,
    swap, {exact hn},
    have key := nat.gcd_eq_gcd_ab p n,
    delta nat.coprime at hn, rw hn at key,
    replace key := congr_arg (λ k : ℤ, (k : α)) key,
    simp only [int.cast_coe_nat, int.cast_add, int.coe_nat_zero, int.cast_mul, int.cast_one,
      int.coe_nat_succ, zero_add, hc] at key,
    rw [mul_assoc, ← mul_add] at key,
    exfalso, apply h,
    rw is_unit_iff_exists_inv,
    exact ⟨_, key.symm⟩ },
  { rintro ⟨c, rfl⟩,
    apply eq_zero_of_zero_dvd,
    use p,
    rw [zero_mul, helper (p*c), ideal.quotient.eq_zero_iff_mem, nat.cast_mul],
    exact ideal.mul_mem_right _ (ideal.subset_span $ set.mem_singleton p) }
end⟩
.

lemma add_pow (a b : α) : ((a + b)^p modₑ (p : α)) = (a^p modₑ (p : α)) + (b^p modₑ (p : α)) :=
begin
  classical,
  by_cases H : is_unit (p : α),
  { haveI := modp.char_one_of_is_unit H, exact char_one.elim _ _ },
  { haveI := modp.char_p hp H, simpa using add_pow_char _ hp _ _, apply_instance }
end

end modp

section
open multiplicity

-- use `lift` instead
-- lemma integral_of_denom_eq_one (r : ℚ) (h : r.denom = 1) : (r.num : ℚ) = r :=
-- begin
--   lift r to ℤ using h,
--   rw [← rat.cast_of_int, @rat.num_denom r, h, ← rat.mk_nat_eq],
--   norm_cast, delta rat.of_int rat.mk_nat, congr,
--   simp only [nat.gcd_one_right, int.nat_abs, nat.div_one]
-- end

end

-- ### end FOR_MATHLIB

-- proper start of this file

open mv_polynomial set

variables (α : Type u) [decidable_eq α] [comm_ring α]

lemma dvd_sub_pow_of_dvd_sub (p : ℕ) [hp : fact p.prime] (a b : α) (h : (p : α) ∣ a - b) (k : ℕ) :
  (p^(k+1) : α) ∣ a^(p^k) - b^(p^k) :=
begin
  induction k with k ih, { simpa using h }, clear h,
  simp only [nat.succ_eq_add_one],
  rcases ih with ⟨c, hc⟩,
  rw sub_eq_iff_eq_add' at hc,
  replace hc := congr_arg (λ x, x^p) hc,
  dsimp only at hc,
  rw [← pow_mul, add_pow, finset.sum_range_succ, nat.choose_self, nat.cast_one, mul_one,
    nat.sub_self, pow_zero, mul_one] at hc,
  conv { congr, skip, rw [nat.pow_succ] },
  simp only [nat.pow_eq_pow] at hc,
  rw [hc, pow_mul, add_sub_cancel'], clear hc a,
  apply dvd_sum,
  intros i hi,
  rw finset.mem_range at hi,
  rw mul_pow,
  conv { congr, skip, congr, congr, skip, rw mul_comm },
  repeat { rw mul_assoc, apply dvd_mul_of_dvd_right }, clear c b,
  norm_cast,
  apply coe_nat_dvd,
  by_cases H : i = 0,
  { subst H,
    suffices : p ^ (k + 1 + 1) ∣ (p ^ (k + 1)) ^ p, by simpa,
    rw ← nat.pow_mul,
    apply nat.pow_dvd_pow,
    refine le_trans (add_le_add_left' $ le_add_left $ le_refl _ : k + 1 + 1 ≤ k + 1 + (k + 1)) _,
    refine le_trans (le_of_eq _) (nat.mul_le_mul_left (k+1) $ (hp.two_le : 2 ≤ p)),
    rw mul_two },
  have i_pos := nat.pos_of_ne_zero H, clear H,
  rw nat.pow_succ,
  apply mul_dvd_mul,
  { generalize H : (p^(k+1)) = b,
    have := nat.sub_pos_of_lt hi,
    conv {congr, rw ← nat.pow_one b},
    apply nat.pow_dvd_pow,
    exact this },
  exact nat.prime.dvd_choose i_pos hi ‹_›
end

open mv_polynomial

-- noncomputable theory

variables (p : ℕ) [fact p.prime]
variables {R : Type u} [decidable_eq R] [comm_ring R]

open_locale big_operators

theorem range_sum_eq_fin_univ_sum {α} [add_comm_monoid α] (f : ℕ → α) (n) :
  ∑ i in finset.range n, f i = ∑ i : fin n, f i :=
begin
  symmetry,
  apply finset.sum_bij (λ (i : fin n) _, (i : ℕ)),
  { rintros ⟨i, hi⟩ _, simpa only [finset.mem_range, fin.coe_mk] using hi, },
  { simp only [forall_prop_of_true, finset.mem_univ, eq_self_iff_true, forall_true_iff], },
  { simp only [forall_prop_of_true, finset.mem_univ, fin.ext_iff, fin.coe_eq_val,
      imp_self, forall_2_true_iff], },
  { simp only [finset.mem_univ, exists_prop_of_true, finset.mem_range],
    intros i hi, exact ⟨⟨i, hi⟩, (fin.coe_mk hi).symm⟩, }
end

noncomputable def witt_polynomial (n : ℕ) : mv_polynomial ℕ R :=
(finset.range (n+1)).sum (λ i, (C (p^i) * X i ^ (p^(n-i))))

variables (R)

/-- View a polynomial written in terms of the basis of Witt polynomials
as a polynomial written in terms of the standard basis.

In particular, this sends `X n` to `witt_polynomial p n`.
This fact is recorded in `from_W_to_X_basis_W_n`. -/
noncomputable def from_W_to_X_basis : mv_polynomial ℕ R →ₐ[R] mv_polynomial ℕ R :=
aeval _ _ (witt_polynomial p)

-- instance from_W_to_X_basis.is_ring_hom : is_ring_hom (from_W_to_X_basis p R) :=
-- by delta from_W_to_X_basis; apply_instance

lemma witt_polynomial_zero : (witt_polynomial p 0 : mv_polynomial ℕ R) = X 0 :=
begin
  delta witt_polynomial,
  simp [finset.sum_range_succ, finset.range_zero, finset.sum_empty],
end

lemma from_W_to_X_basis_W_n (n) : from_W_to_X_basis p R (X n) = witt_polynomial p n :=
by simp [from_W_to_X_basis]

-- variables {R} -- (pu : units R) (hp : (pu : R) = p)

-- We need p to be invertible for the following definitions

/-- The `X_in_terms_of_W p R n` is the polynomial on the basis of Witt polynomials
that corresponds to the ordinary `X n`.
This means that `from_W_to_X_basis` sends `X_in_terms_of_W p R n` to `X n`.
This fact is recorded in `from_W_to_X_basis_X_in_terms_of_W`. -/
noncomputable def X_in_terms_of_W [invertible (p : R)] :
  ℕ → mv_polynomial ℕ R
| n := (X n - (∑ i : fin n,
  have _ := i.2, (C (p^(i : ℕ)) * (X_in_terms_of_W i)^(p^(n-i))))) * C (⅟p ^ n)

lemma X_in_terms_of_W_eq [invertible (p : R)] {n : ℕ} : X_in_terms_of_W p R n =
    (X n - (∑ i in finset.range n, C (p^i) * X_in_terms_of_W p R i ^ p ^ (n - i))) *
      C (⅟p ^ n) :=
by { rw [X_in_terms_of_W, range_sum_eq_fin_univ_sum], }

/-- View a polynomial written in terms of the standard basis
as a polynomial written in terms of the Witt basis.

This sends `witt_polynomial p n` to `X n`,
and `X n` to `X_in_terms_of_W p R n`. -/
noncomputable def from_X_to_W_basis [invertible (p : R)] :
  mv_polynomial ℕ R →ₐ[R] mv_polynomial ℕ R :=
aeval _ _ (X_in_terms_of_W p R)

-- instance from_X_to_W_basis.is_ring_hom : is_ring_hom (from_X_to_W_basis p pu hp) :=
-- by delta from_X_to_W_basis; apply_instance

lemma X_in_terms_of_W_zero [invertible (p : R)] :
  X_in_terms_of_W p R 0 = witt_polynomial p 0 :=
begin
  rw X_in_terms_of_W_eq,
  rw finset.range_zero,
  rw finset.sum_empty,
  rw witt_polynomial_zero,
  simp
end

lemma X_in_terms_of_W_aux [invertible (p : R)] {n} : X_in_terms_of_W p R n * C (p^n) =
  X n - ∑ i in finset.range n, C (p^i) * (X_in_terms_of_W p R i)^p^(n-i) :=
by rw [X_in_terms_of_W_eq, mul_assoc, ← C_mul, ← mul_pow, inv_of_mul_self, one_pow, C_1, mul_one]

section -- Kudos to Mario

theorem rat.ring_hom_unique {α} [ring α]
  (f g : ℚ → α) [is_ring_hom f] [is_ring_hom g] (r : ℚ) : f r = g r :=
rat.num_denom_cases_on' r $ λ a b b0, begin
  let φ : ℤ →+* α := (ring_hom.of f).comp (int.cast_ring_hom ℚ),
  let ψ : ℤ →+* α := (ring_hom.of g).comp (int.cast_ring_hom ℚ),
  rw [rat.mk_eq_div, int.cast_coe_nat],
  have b0' : (b:ℚ) ≠ 0 := nat.cast_ne_zero.2 b0,
  have : ∀ n : ℤ, f n = g n := λ n,
    (ring_hom.eq_int_cast φ n).trans
    (ring_hom.eq_int_cast ψ n).symm,
  calc f (a * b⁻¹)
      = f a * f b⁻¹ * (g (b:ℤ) * g b⁻¹) : by rw [
    int.cast_coe_nat, ← is_ring_hom.map_mul g,
    mul_inv_cancel b0', is_ring_hom.map_one g, mul_one,
    is_ring_hom.map_mul f]
  ... = g a * f b⁻¹ * (f (b:ℤ) * g b⁻¹) : by rw [this a, ← this b]
  ... = g (a * b⁻¹) : by rw [
    int.cast_coe_nat, mul_assoc, ← mul_assoc (f b⁻¹),
    ← is_ring_hom.map_mul f, inv_mul_cancel b0',
    is_ring_hom.map_one f, one_mul,
    is_ring_hom.map_mul g]
end

end

-- Important: gonna need this
-- have fC : ∀ (a : ℚ), f (C a) = C a,
-- { intro a, show (f ∘ C) a = _, apply rat.ring_hom_unique (f ∘ C) C a },

lemma X_in_terms_of_W_prop' [invertible (p : R)]
  (f : mv_polynomial ℕ R →ₐ[R] mv_polynomial ℕ R)
  (fX : ∀ (n : ℕ), f (X n) = witt_polynomial p n)
  (n : ℕ) : f (X_in_terms_of_W p R n) = X n :=
begin
  have fC : ∀ r, f (C r) = C r := f.commutes,
  apply nat.strong_induction_on n,
  clear n, intros n H,
  rw [X_in_terms_of_W_eq],
  simp only [f.map_mul, alg_hom.map_sub f, fC, fX, alg_hom.map_sum],
  rw [finset.sum_congr rfl, (_ : @witt_polynomial p _ R _ _ n -
    (finset.range n).sum (λ i, C (p^i) * (X i)^p^(n-i)) = C (p^n) * X n)],
  { rw [mul_right_comm, ← C_mul, ← mul_pow, mul_inv_of_self, one_pow, C_1, one_mul] },
  { simp [witt_polynomial, nat.sub_self],
    rw finset.sum_range_succ,
    simp },
  { intros i h,
    rw finset.mem_range at h,
    simp only [alg_hom.map_mul f, alg_hom.map_pow f, fC, function.comp_app],
    rw H _ h }
end

lemma from_W_to_X_basis_X_in_terms_of_W [invertible (p : R)] (n : ℕ) :
  from_W_to_X_basis p R (X_in_terms_of_W p R n) = X n :=
begin
  apply X_in_terms_of_W_prop' p R _ _ n,
  intro n,
  exact from_W_to_X_basis_W_n p R n,
end

--move this
lemma mv_polynomial.alg_hom_is_id {σ : Type*} (f : mv_polynomial σ R →ₐ[R] mv_polynomial σ R)
  (hf : ∀ i : σ, f (X i) = X i) : f = alg_hom.id _ _ :=
begin
  ext p : 1,
  have H : is_semiring_hom f.to_ring_hom := by apply_instance,
  apply mv_polynomial.is_id _ H f.commutes hf,
end

lemma from_W_to_X_basis_comp_from_X_to_W_basis [invertible (p : R)] :
  (from_W_to_X_basis p R).comp (from_X_to_W_basis p _) = alg_hom.id _ _ :=
begin
  apply mv_polynomial.alg_hom_is_id,
  intro n,
  rw [from_X_to_W_basis, alg_hom.comp_apply, aeval_X],
  exact from_W_to_X_basis_X_in_terms_of_W p R n
end

lemma from_X_to_W_basis_witt_polynomial [invertible (p : R)] (n : ℕ) :
  (from_X_to_W_basis p R) (witt_polynomial p n) = X n :=
begin

end

lemma from_X_to_W_basis_comp_from_W_to_X_basis [invertible (p : R)] :
  (from_X_to_W_basis p R).comp (from_W_to_X_basis p _) = alg_hom.id _ _ :=
begin
  apply mv_polynomial.alg_hom_is_id,
  intro n,
  -- rw ← from_W_to_X_basis_X_in_terms_of_W p R n,
  -- refine X_in_terms_of_W_prop' p R _ _ n,
  -- have := X_in_terms_of_W_prop' p R (from_W_to_X_basis p R) (from_W_to_X_basis_W_n p R) n,
  -- conv_rhs { rw [← this] },
  rw [alg_hom.comp_apply],

  -- rw [from_W_to_X_basis],
  rw [from_X_to_W_basis],

  -- convert this using 1,
  -- delta from_X_to_W_basis function.comp, erw eval₂_X,
  -- squeeze_simp [from_X_to_W_basis],
  -- refine X_in_terms_of_W_prop' p R _ _ _ n,
  -- { intro r, apply eval₂_C },
  -- { intro k, erw from_W_to_X_basis_W_n p }
end

#exit

lemma X_in_terms_of_W_prop₂ [invertible (p : R)] (k : ℕ) :
  (witt_polynomial p k).eval₂ C (X_in_terms_of_W p R) = X k :=
begin
  suffices : from_X_to_W_basis p R (C (p^k) * X k) +
    from_X_to_W_basis p R (finset.sum (finset.range k) (λ (i : ℕ), C (p^i) * (X i)^p^(k-i))) = X k,
  { simpa [witt_polynomial, finset.sum_range_succ] },
  suffices : ∀ i, from_X_to_W_basis p R (C (p^i) * (X i)^p^(k-i)) =
    C (p^i) * (X_in_terms_of_W p R i)^p^(k-i),
  { rw [from_X_to_W_basis, eval₂_mul, eval₂_C, eval₂_X, X_in_terms_of_W_eq,
        mul_comm, mul_assoc, ← C_mul, ← mul_pow, inv_mul_of_self, one_pow, C_1, mul_one,
        ← finset.sum_hom (eval₂ C $ X_in_terms_of_W p R),
        sub_add_eq_add_sub, sub_eq_iff_eq_add, hp],
    congr,
    funext i,
    exact this i },
  intro i,
  rw [from_X_to_W_basis, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]
end

lemma X_in_terms_of_W_prop [invertible (p : R)] (n : ℕ) : (X_in_terms_of_W p R n).eval₂ C (witt_polynomial p) = X n :=
begin
  change from_W_to_X_basis p R _ = X n,
  apply X_in_terms_of_W_prop',
  -- { intro r, apply eval₂_C },
  { intro n, apply from_W_to_X_basis_W_n }
end

-- lemma from_X_to_W_basis_comp_from_W_to_X_basis (f) :
--   from_X_to_W_basis p pu hp (from_W_to_X_basis p _ f) = f :=
-- begin
--   show (from_X_to_W_basis p pu hp ∘ from_W_to_X_basis p _) f = f,
--   apply mv_polynomial.is_id,
--   { apply_instance },
--   { intro r,
--     let : _ := _,
--     refine @rat.ring_hom_unique _ _ _ _ this (by apply_instance) r,
--     let F := (from_X_to_W_basis p ∘ from_W_to_X_basis p _),
--     change is_ring_hom (λ (r : ℚ), F (C r)),
--     show is_ring_hom (F ∘ C),
--     exact is_ring_hom.comp _ _ },
--   { intro n,
--     delta from_W_to_X_basis function.comp,
--     erw eval₂_X,
--     delta from_X_to_W_basis,
--     apply X_in_terms_of_W_prop₂ }
-- end

-- lemma from_X_to_W_basis_X_n (n) : from_X_to_W_basis p (witt_polynomial p n) = X n :=
-- by simp only [from_X_to_W_basis, eval₂_X, X_in_terms_of_W_prop₂]

-- -- def to_W_basis : mv_polynomial ℕ ℚ ≃r mv_polynomial ℕ ℚ :=
-- { to_fun    := from_X_to_W_basis p,
--   inv_fun   := from_W_to_X_basis p ℚ,
--   left_inv  := λ _, from_W_to_X_basis_comp_from_X_to_W_basis _ _,
--   right_inv := λ _, from_X_to_W_basis_comp_from_W_to_X_basis _ _,
--   hom       := by apply_instance }

variables {idx : Type*} [decidable_eq idx]

def rat.pu : units ℚ :=
⟨p, 1/p,
mul_one_div_cancel (by exact_mod_cast ne_of_gt (nat.prime.pos ‹_›)),
one_div_mul_cancel (by exact_mod_cast ne_of_gt (nat.prime.pos ‹_›))⟩

noncomputable def witt_structure_rat (Φ : mv_polynomial idx ℚ) : ℕ → mv_polynomial (idx × ℕ) ℚ :=
λ n, eval₂ C (λ k : ℕ,
   Φ.eval₂ C (λ b, ((witt_polynomial p k).rename (λ i, (b,i)))))
     (X_in_terms_of_W p (rat.pu p) rfl n)

theorem witt_structure_rat_prop (Φ : mv_polynomial idx ℚ) (n) :
  (witt_polynomial p n).eval₂ C (witt_structure_rat p Φ) =
    Φ.eval₂ C (λ b : idx, ((witt_polynomial p n).rename (λ i : ℕ, (b,i)))) :=
begin
  delta witt_structure_rat,
  rw [← function.comp, eval₂_assoc, X_in_terms_of_W_prop₂ p _ _ n, eval₂_X]
end

theorem witt_structure_prop_exists_unique (Φ : mv_polynomial idx ℚ) :
  ∃! (φ : ℕ → mv_polynomial (idx × ℕ) ℚ), ∀ (n : ℕ),
  (witt_polynomial p n).eval₂ C φ =
    Φ.eval₂ C (λ b : idx, ((witt_polynomial p n).rename (λ i : ℕ, (b,i)))) :=
begin
  refine ⟨witt_structure_rat p Φ, _, _⟩,
  { intro n, apply witt_structure_rat_prop },
  { intros φ H,
    unfold witt_structure_rat,
    funext n,
    rw show φ n = ((X_in_terms_of_W p (rat.pu p) rfl n).eval₂ C (witt_polynomial p)).eval₂ C φ,
    { rw [X_in_terms_of_W_prop p, eval₂_X] },
    rw ← eval₂_assoc,
    -- unfold function.comp,
    congr,
    funext k,
    exact H k },
end

lemma witt_structure_rat_rec_aux (Φ : mv_polynomial idx ℚ) (n) :
  (witt_structure_rat p Φ n) * C (p^n) =
  Φ.eval₂ C (λ b, ((witt_polynomial p n).rename (λ i, (b,i)))) -
  (finset.range n).sum (λ i, C (p^i) * (witt_structure_rat p Φ i)^p^(n-i)) :=
begin
  have := @X_in_terms_of_W_aux p _ _ _ _ (rat.pu p) rfl n,
  replace := congr_arg (eval₂ C (λ k : ℕ,
  Φ.eval₂ C (λ b, ((witt_polynomial p k).rename (λ i, (b,i)))))) this,
  rw [eval₂_mul, eval₂_C] at this,
  convert this, clear this,
  conv_rhs { simp only [eval₂_sub, eval₂_X] },
  rw sub_left_inj,
  simp only [eval₂_sum'],
  apply finset.sum_congr rfl,
  intros i hi,
  rw [eval₂_mul, eval₂_C, eval₂_pow],
  refl
end

lemma witt_structure_rat_rec (Φ : mv_polynomial idx ℚ) (n) :
  (witt_structure_rat p Φ n) = C (1/p^n) *
  (Φ.eval₂ C (λ b, ((witt_polynomial p n).rename (λ i, (b,i)))) -
  (finset.range n).sum (λ i, C (p^i) * (witt_structure_rat p Φ i)^p^(n-i))) :=
begin
  rw [← witt_structure_rat_rec_aux p Φ n, mul_comm, mul_assoc,
      ← C_mul, mul_one_div_cancel, C_1, mul_one],
  exact pow_ne_zero _ (nat.cast_ne_zero.2 $ ne_of_gt (nat.prime.pos ‹_›))
end

noncomputable def witt_structure_int (Φ : mv_polynomial idx ℤ) (n : ℕ) : mv_polynomial (idx × ℕ) ℤ :=
finsupp.map_range rat.num (rat.coe_int_num 0) (witt_structure_rat p (map (coe : ℤ → ℚ) Φ) n)
.

section
variables {ι : Type*} [decidable_eq ι]

-- lemma mv_polynomial.ext_iff (p q : mv_polynomial ι α) :
-- (∀ m, coeff m p = coeff m q) ↔ p = q :=
-- ⟨mv_polynomial.ext p q, λ h m, by rw h⟩

lemma nat.map_cast {α : Type*} {β : Type*} (f : α → β) [semiring α] [semiring β] [is_semiring_hom f]
  (n : ℕ) : f (n : α) = n :=
ring_hom.map_nat_cast (ring_hom.of f) n

variables {S : Type*} [decidable_eq S] [comm_ring S]

lemma map_witt_polynomial (f : R → S) [is_ring_hom f] (n) :
  map f (witt_polynomial p n) = witt_polynomial p n :=
begin
  apply mv_polynomial.ext,
  intro m,
  rw coeff_map,
  delta witt_polynomial,
  rw [← finset.sum_hom _ (coeff m), ← finset.sum_hom _ (coeff m), ← finset.sum_hom _ f],
  { apply finset.sum_congr rfl,
    intros i hi,
    repeat {rw [coeff_C_mul m, coeff_X]},
    rw is_ring_hom.map_mul f,
    split_ifs;
    [ rw is_ring_hom.map_one f, rw is_ring_hom.map_zero f ];
    simp only [mul_one, mul_zero],
    rw is_semiring_hom.map_pow f, congr,
    exact nat.map_cast f p },
  all_goals {apply_instance}
end

end

lemma mv_polynomial.coe_int_rat_map_injective (I : Type*) [decidable_eq I] :
  function.injective (map (coe : ℤ → ℚ) : mv_polynomial I ℤ → mv_polynomial I ℚ) :=
begin
  rw is_add_group_hom.injective_iff _,
  all_goals {try {apply_instance}},
  intros f hf,
  apply mv_polynomial.ext,
  intro m,
  rw ← mv_polynomial.ext_iff at hf,
  specialize hf m,
  rw [coeff_map, coeff_zero] at hf,
  rw coeff_zero,
  exact_mod_cast hf
end
.

lemma duh (a b c d : R) (h1 : a = c) (h2 : b = d) : a - b = c - d :=
by simp *
.

variables {ι : Type*} {σ : Type*} [decidable_eq ι] [decidable_eq σ]
variables {S : Type*} [decidable_eq S] [comm_ring S]
variables {T : Type*} [decidable_eq T] [comm_ring T]

@[simp] lemma map_pow (f : R → S) [is_semiring_hom f] (Φ : mv_polynomial ι R) (n : ℕ) :
  (Φ^n).map f = (Φ.map f)^n :=
is_semiring_hom.map_pow _ _ _

lemma foo (Φ : mv_polynomial idx ℤ) (n : ℕ)
  (IH : ∀ m : ℕ, m < n → map coe (witt_structure_int p Φ m) = witt_structure_rat p (map coe Φ) m) :
  map (coe : ℤ → ℚ) (Φ.eval₂ C (λ b, ((witt_polynomial p n).rename (λ i, (b,i)))) -
  (finset.range n).sum (λ i, C (p^i) * (witt_structure_int p Φ i)^p^(n-i))) =
  ((map coe Φ).eval₂ C (λ b, ((witt_polynomial p n).rename (λ i, (b,i)))) -
  (finset.range n).sum (λ i, C (p^i) * (witt_structure_rat p (map coe Φ) i)^p^(n-i))) :=
begin
  rw [is_ring_hom.map_sub (map (coe : ℤ → ℚ)), ← finset.sum_hom (map (coe : ℤ → ℚ))],
  all_goals {try {apply_instance}},
  work_on_goal 1 { exact @is_add_group_hom.to_is_add_monoid_hom _ _ _ _ _ _ },
  apply duh,
  { rw map_eval₂, congr' 1, funext b, dsimp, rw map_rename,
    erw map_witt_polynomial,
    refl },
  apply finset.sum_congr rfl,
  intros i hi,
  rw finset.mem_range at hi,
  specialize IH i hi,
  rw [map_mul, map_C, map_pow, IH],
  norm_cast
end
.

def doh {α : Type*} [comm_ring α] : add_comm_monoid α := by apply_instance
def dah {α : Type*} [comm_ring α] : add_monoid α := by apply_instance

def bah {α : Type*} [comm_ring α] (n : ℕ) :
  is_add_monoid_hom (ideal.quotient.mk (ideal.span ({((p^(n+1) : ℕ) : α)} : set α))) :=
by apply_instance
.

def boh {α : Type*} {β : Type*} [comm_semiring α] [comm_semiring β] (f : α → β) [is_semiring_hom f] :
  is_add_monoid_hom f := by apply_instance
-- set_option class.instance_max_depth 50

-- def aahrg (k : ℕ) (φ) : ((C (p : ℤ) ^ k * φ : mv_polynomial ι ℤ) modₑ ↑p) =
--   (0 : ideal.quotient (ideal.span {(p : mv_polynomial ι ℤ)})) := _

lemma C_eq_coe_nat (n : ℕ) : (C ↑n : mv_polynomial ι R) = n :=
begin
  induction n with n ih, {simp},
  simp [nat.succ_eq_add_one, ih]
end

lemma quux (n : ℕ) :
  ((witt_polynomial p (n + 1) : mv_polynomial ℕ ℤ) modₑ (↑(p^(n+1)) : mv_polynomial ℕ ℤ)) =
  ((eval₂ C (λ i, ((X i)^p)) (witt_polynomial p n)) modₑ (↑(p^(n+1)) : mv_polynomial ℕ ℤ)) :=
begin
  delta witt_polynomial,
  rw [← finset.sum_hom (ideal.quotient.mk _),
      ← finset.sum_hom (eval₂ C (λ (i : ℕ), X i ^ p)),
      ← finset.sum_hom (ideal.quotient.mk _),
      finset.sum_range_succ],
  all_goals {try { apply doh }},
  work_on_goal 0 {
    convert zero_add _ using 1,
    work_on_goal 1 { apply dah },
    congr' 1,
    work_on_goal 0 {
      apply ideal.quotient.eq_zero_iff_mem.mpr,
      apply ideal.mul_mem_right _ _,
      apply ideal.subset_span,
      rw [mem_singleton_iff, ← C_eq_coe_nat],
      norm_cast },
    apply finset.sum_congr rfl,
    intros i hi,
    rw [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, ← pow_mul],
    congr,
    rw [mul_comm, ← nat.pow_succ],
    rw finset.mem_range at hi,
    congr,
    replace hi := nat.le_of_lt_succ hi,
    exact nat.succ_sub hi },
  all_goals { try {apply bah} },
  { refine @boh _ _ _ _ _ _, },
end
.

lemma eq_mod_iff_dvd_sub (a b c : α) :
  (a modₑ c) = (b modₑ c) ↔ c ∣ a - b :=
by rw [← sub_eq_zero, ← ideal.quotient.mk_sub,
  ideal.quotient.eq_zero_iff_mem, ideal.mem_span_singleton]

lemma fermat_little' (a : zmod p) : a^p = a :=
begin
  have ppos : p > 0 := nat.prime.pos ‹_›,
  by_cases h : a = 0,
  { subst a, apply zero_pow ppos },
  { have := zmod.fermat_little p h,
    replace := congr_arg (λ x, a * x) this,
    simp at this,
    convert this,
    rw ← pow_succ, congr, clear this h a _inst_3,
    revert ppos p, omega manual nat }
end

lemma int_pol_mod_p (φ : mv_polynomial ι ℤ) :
  ((φ.eval₂ C (λ i, (X i)^p)) modₑ ↑p) = (φ^p modₑ ↑p) :=
begin
  apply mv_polynomial.induction_on φ,
  { intro n, rw [eval₂_C, eq_mod_iff_dvd_sub, ← C_eq_coe_nat, ← C_pow, ← C_sub],
    suffices : (p : ℤ) ∣ n - n^p,
    { rcases this with ⟨d, h⟩, refine ⟨C d, _⟩, rw [h, C_mul, int.nat_cast_eq_coe_nat] },
      rw ← zmodp.eq_zero_iff_dvd_int ‹_›,
      rw [int.cast_sub, int.cast_pow, sub_eq_zero],
      symmetry, apply fermat_little' },
  { intros f g hf hg, rw [eval₂_add, ideal.quotient.mk_add, hf, hg, modp.add_pow], assumption },
  { intros f i hf, rw [eval₂_mul, ideal.quotient.mk_mul, hf, eval₂_X, mul_pow, ideal.quotient.mk_mul] }
end

lemma zrum (a b : α) (h : (a modₑ (p : α)) = (b modₑ (p : α))) (k : ℕ) :
  (a^(p^k) modₑ (p^(k+1) : α)) = (b^(p^k) modₑ (p^(k+1) : α)) :=
begin
  rw eq_mod_iff_dvd_sub at h ⊢,
  apply dvd_sub_pow_of_dvd_sub,
  exact h
end

lemma xyzzy (p : mv_polynomial ι ℚ) :
  map (coe : ℤ → ℚ) (finsupp.map_range rat.num (rat.coe_int_num 0) p) = p ↔
  ∀ m, (coeff m p).denom = 1 :=
begin
  split; intro h,
  { rw ← mv_polynomial.ext_iff at h, intro m,
    rw [← h m, coeff_map],
    apply rat.coe_int_denom },
  { apply mv_polynomial.ext, intro m,
    rw coeff_map,
    apply integral_of_denom_eq_one,
    exact h m }
end

lemma baz (φ : mv_polynomial ι ℤ) (c) (n : ℤ) (hn : n ≠ 0) :
  (coeff c (C (1 / (n : ℚ)) * map (coe : ℤ → ℚ) φ)).denom = 1 ↔ n ∣ coeff c φ :=
begin
  split,
  { intro h,
    rw [coeff_C_mul, coeff_map] at h,
    refine ⟨((1 : ℚ) / n * ↑(coeff c φ)).num, _⟩,
    suffices : (↑(coeff c φ) : ℚ) = (_ : ℤ),
    { rwa int.cast_inj at this },
    replace h := integral_of_denom_eq_one _ h,
    rw [int.cast_mul, h, ← mul_assoc, mul_one_div_cancel, one_mul],
    exact_mod_cast hn },
  { rintros ⟨d, h⟩,
    rw [coeff_C_mul, coeff_map, h, int.cast_mul, ← mul_assoc, one_div_mul_cancel, one_mul],
    { apply rat.coe_int_denom },
    { exact_mod_cast hn } }
end

lemma baz_nat (φ : mv_polynomial ι ℤ) (c) (n : ℕ) (hn : n ≠ 0) :
  (coeff c (C (1 / (n : ℚ)) * map (coe : ℤ → ℚ) φ)).denom = 1 ↔ (n : ℤ) ∣ coeff c φ :=
begin
  have := baz φ c n (by exact_mod_cast hn),
  rwa [show ((n : ℤ) : ℚ) = n, by simp] at this,
end
.

lemma droj (φ : mv_polynomial ι ℤ) (n : ℕ) (hn : n ≠ 0) :
  (n : mv_polynomial ι ℤ) ∣ φ ↔ ∀ c, (n : ℤ) ∣ coeff c φ :=
begin
  split,
  { rintros ⟨d, rfl⟩ c, rw [← C_eq_coe_nat, coeff_C_mul, int.nat_cast_eq_coe_nat], apply dvd_mul_right },
  { intro h, refine ⟨finsupp.map_range (λ k, k/n) (by simp) φ, _⟩,
    apply mv_polynomial.ext,
    intro c,
    rw [← C_eq_coe_nat, coeff_C_mul],
    dsimp [coeff] at h ⊢,
    rcases h c with ⟨d, h⟩,
    rw [h, int.mul_div_cancel_left, int.nat_cast_eq_coe_nat],
    exact_mod_cast hn }
end

lemma eval₂_mod (φ : mv_polynomial ι R) (f : R → S) [is_semiring_hom f] (g₁ : ι → S) (g₂ : ι → S) (s : S)
  (h : ∀ i, (g₁ i modₑ s) = (g₂ i modₑ s)) :
  ((φ.eval₂ f g₁) modₑ s) = (φ.eval₂ f g₂ modₑ s) :=
begin
  rw [eval₂_comp_right (ideal.quotient.mk _) f g₁, eval₂_comp_right (ideal.quotient.mk _) f g₂,
    function.comp, function.comp],
  all_goals {try {apply_instance}},
  congr, funext i, rw h i,
end

lemma rename_mod (φ₁ φ₂ : mv_polynomial ι R) (g : ι → σ) (r : mv_polynomial ι R)
  (h : (φ₁ modₑ r) = (φ₂ modₑ r)) :
  ((φ₁.rename g) modₑ (r.rename g)) = (φ₂.rename g modₑ (r.rename g)) :=
begin
  rw eq_mod_iff_dvd_sub at h ⊢,
  rcases h with ⟨d, h⟩,
  refine ⟨d.rename g, _⟩,
  rw [← rename_sub, ← rename_mul],
  congr, exact h,
end

lemma rename_mod_C (φ₁ φ₂ : mv_polynomial ι R) (g : ι → σ) (r : R)
  (h : (φ₁ modₑ (C r)) = (φ₂ modₑ (C r))) :
  ((φ₁.rename g) modₑ (C r)) = (φ₂.rename g modₑ (C r)) :=
begin
  rwa [← rename_C g, rename_mod],
end

lemma eval₂_rename (f : R → S) [is_semiring_hom f] (k : ι → σ) (g : σ → S) (Φ : mv_polynomial ι R) :
  (Φ.rename k).eval₂ f g = Φ.eval₂ f (g ∘ k) :=
eval₂_rename f k g Φ

-- Achtung die Reihenfolge!!
lemma rename_eval₂ (k : ι → σ) (g : σ → mv_polynomial ι R) (Φ : mv_polynomial ι R) :
  (Φ.eval₂ C (g ∘ k)).rename k = (Φ.rename k).eval₂ C (rename k ∘ g) :=
rename_eval₂ k Φ g

-- Achtung die Reihenfolge!!
lemma rename_prodmk_eval₂ (s : σ) (g : ι → mv_polynomial ι R) (Φ : mv_polynomial ι R) :
  (Φ.eval₂ C g).rename (prod.mk s) = Φ.eval₂ C (λ x, (g x).rename (prod.mk s)) :=
rename_prodmk_eval₂ Φ s g

lemma eval₂_congr (f : R → S) [is_semiring_hom f] (g₁ g₂ : ι → S) (φ : mv_polynomial ι R)
  (h : ∀ {i : ι} {c : ι →₀ ℕ}, i ∈ c.support → coeff c φ ≠ 0 → g₁ i = g₂ i) :
  φ.eval₂ f g₁ = φ.eval₂ f g₂ :=
eval₂_congr f g₁ g₂ $ by { intros, solve_by_elim }

lemma blur (Φ : mv_polynomial idx ℤ) (n : ℕ)
  (IH : ∀ m : ℕ, m < (n + 1) → map coe (witt_structure_int p Φ m) = witt_structure_rat p (map coe Φ) m) :
  Φ.eval₂ C (λ (b : idx), rename (λ (i : ℕ), (b, i)) (eval₂ C (λ i, ((X i)^p)) (witt_polynomial p n))) =
  (witt_polynomial p n).eval₂ C (λ (i : ℕ), (witt_structure_int p Φ i).eval₂ C $ λ bi, (X bi)^p) :=
begin
  apply mv_polynomial.coe_int_rat_map_injective,
  have := witt_structure_rat_prop p (map coe Φ) n,
  replace := congr_arg (λ ψ, eval₂ C (λ bi, (X bi)^p) ψ) this,
  simp only [map_eval₂, function.comp, map_rename, map_witt_polynomial, map_pow, map_X] at this ⊢,
  rw [← eval₂_assoc, ← eval₂_assoc] at this,
  simp only [function.comp, eval₂_rename] at this,
  simp only [rename_prodmk_eval₂, rename_pow, rename_X],
  rw ← this, clear this,
  apply eval₂_congr,
  intros i c hi hc,
  rw IH,
  delta witt_polynomial at hc,
  rw ← finset.sum_hom (coeff c) at hc,
  work_on_goal 0 {
    rcases finset.exists_ne_zero_of_sum_ne_zero hc with ⟨j, hj, hcj⟩,
    dsimp only at hcj,
    rw [X_pow_eq_single, C_mul_monomial, coeff_monomial] at hcj,
    split_ifs at hcj,
    { subst c,
      rw finsupp.mem_support_single at hi,
      cases hi, subst i, rwa finset.mem_range at hj, },
    { contradiction }
  },
  exact coeff.is_add_monoid_hom c
end
.

lemma eval₂_sum (f : R → S) [is_semiring_hom f] (g : ι → S) (X : finset σ) (φ : σ → mv_polynomial ι R) :
  eval₂ f g (X.sum φ) = X.sum (λ s, eval₂ f g (φ s)) :=
begin
  apply finset.induction_on X, {simp},
  intros s Y hs, simp [*, finset.sum_insert],
end

lemma bar (Φ : mv_polynomial idx ℤ) (n : ℕ) :
  map (coe : ℤ → ℚ) (witt_structure_int p Φ n) = witt_structure_rat p (map (coe : ℤ → ℚ) Φ) n :=
begin
  apply nat.strong_induction_on n, clear n,
  intros n IH,
  erw xyzzy,
  intro c,
  rw witt_structure_rat_rec p _ n,
  rw ← foo p Φ n IH,
  rw show (p : ℚ)^n = ((p^n : ℕ) : ℤ), by simp,
  rw baz,
  work_on_goal 1 { rw int.coe_nat_pow, apply pow_ne_zero, exact_mod_cast ne_of_gt (nat.prime.pos ‹_›) },
  induction n with n ih, {simp}, clear ih, revert c,
  rw ← droj,
  work_on_goal 1 { suffices : (p ^ n.succ : ℤ) ≠ 0, { exact_mod_cast this },
    apply pow_ne_zero, exact_mod_cast ne_of_gt (nat.prime.pos ‹_›) },
  rw ← eq_mod_iff_dvd_sub,
  calc _ = (Φ.eval₂ C (λ (b : idx), rename (λ (i : ℕ), (b, i)) (witt_polynomial p (nat.succ n))) modₑ ↑(p^(n+1))) : rfl
     ... = (Φ.eval₂ C (λ (b : idx), rename (λ (i : ℕ), (b, i)) (eval₂ C (λ i, ((X i)^p)) (witt_polynomial p n))) modₑ ↑(p^(n+1))) :
     begin
      apply eval₂_mod, intro b,
      rw [← C_eq_coe_nat], apply rename_mod_C, rw C_eq_coe_nat,
      rw [nat.succ_eq_add_one],
      exact quux p n,
     end
     ... = _ : by rw blur p Φ n IH
     ... = _ :
     begin
      delta witt_polynomial,
      conv_lhs { congr, simp [eval₂_sum] },
      rw [← finset.sum_hom (ideal.quotient.mk _), ← finset.sum_hom (ideal.quotient.mk _)],
      { apply finset.sum_congr rfl,
        intros i hi,
        rw finset.mem_range at hi, replace hi := nat.le_of_lt_succ hi,
        rw [eval₂_mul, ← C_pow, eval₂_C, eval₂_pow, eval₂_X],
        rw [show (p:ℤ)^i = (p^i : ℕ), by simp, ← int.nat_cast_eq_coe_nat, C_eq_coe_nat],
        rw [eq_mod_iff_dvd_sub, ← mul_sub],
        rw show p^(n+1) = p^i * p^(n+1-i),
        { rw ← nat.pow_add, congr' 1, clear IH, revert hi i n, omega manual nat },
        rw nat.cast_mul,
        apply mul_dvd_mul_left,
        rw show n + 1 - i = n - i + 1,
        { exact nat.succ_sub hi },
        rw nat.cast_pow,
        rw [nat.pow_succ, mul_comm, pow_mul],
        apply dvd_sub_pow_of_dvd_sub,
        rw ← eq_mod_iff_dvd_sub,
        apply int_pol_mod_p },
        apply doh, all_goals {apply bah}
     end,
end
.

lemma witt_structure_int_prop.aux (Φ : mv_polynomial idx ℤ) (n : ℕ) :
  map (coe : ℤ → ℚ) ((witt_polynomial p n).eval₂ C (witt_structure_int p Φ)) =
  (witt_polynomial p n).eval₂ C (witt_structure_rat p (map coe Φ)) :=
begin
  rw [map_eval₂, map_witt_polynomial],
  congr' 1,
  funext i, apply bar
end

theorem witt_structure_int_prop (Φ : mv_polynomial idx ℤ) (n) :
  (witt_polynomial p n).eval₂ C (witt_structure_int p Φ) =
    Φ.eval₂ C (λ b : idx, ((witt_polynomial p n).rename (λ i : ℕ, (b,i)))) :=
begin
  apply mv_polynomial.coe_int_rat_map_injective,
  convert witt_structure_rat_prop p (map coe Φ) n,
  { rw [map_eval₂, map_witt_polynomial], congr' 1, funext i, apply bar },
  { rw map_eval₂, congr' 1, funext b, delta function.comp,
    rw [map_rename, map_witt_polynomial], }
end

theorem witt_structure_int_exists_unique (Φ : mv_polynomial idx ℤ) :
  ∃! (φ : ℕ → mv_polynomial (idx × ℕ) ℤ),
  ∀ (n : ℕ), (witt_polynomial p n).eval₂ C φ =
    Φ.eval₂ C (λ b : idx, ((witt_polynomial p n).rename (λ i : ℕ, (b,i)))) :=
begin
  refine ⟨witt_structure_int p Φ, _, _⟩,
  { apply witt_structure_int_prop },
  { intros φ H,
    funext i,
    apply mv_polynomial.coe_int_rat_map_injective,
    rw bar,
    refine congr_fun _ i,
    have := (witt_structure_prop_exists_unique p (map coe Φ)),
    apply unique_of_exists_unique this,
    { clear this, intro n,
      specialize H n,
      convert congr_arg (map (coe : ℤ → ℚ)) H using 1,
      { rw [map_eval₂, map_witt_polynomial] },
      { rw map_eval₂, delta function.comp, congr' 1, funext b,
        rw [map_rename, map_witt_polynomial] } },
    { intro n, apply witt_structure_rat_prop } },
end
.

-- lemma eval₂_rename_prodmk (f : R → S) [is_semiring_hom f] (g : σ × ι → S) (s : σ) (φ : mv_polynomial ι R) :
--   (rename (prod.mk s) φ).eval₂ f g = eval₂ f (λ i, g (s, i)) φ :=
-- eval₂_rename_prodmk f φ g s
-- begin
--   apply mv_polynomial.induction_on φ,
--   { intro r, rw [rename_C, eval₂_C, eval₂_C] },
--   { intros p q hp hq, rw [rename_add, eval₂_add, eval₂_add, hp, hq] },
--   { intros p i hp, rw [rename_mul, rename_X, eval₂_mul, eval₂_mul, eval₂_X, eval₂_X, hp] }
-- end

lemma eval_rename_prodmk (g : σ × ι → R) (s : σ) (φ : mv_polynomial ι R) :
  (rename (prod.mk s) φ).eval g = eval (λ i, g (s, i)) φ :=
eval₂_rename_prodmk id _ _ _

theorem witt_structure_prop (Φ : mv_polynomial idx ℤ) (n) :
  (witt_polynomial p n).eval₂ C (λ i, map (coe : ℤ → R) (witt_structure_int p Φ i)) =
  (map coe Φ).eval₂ C (λ b, ((witt_polynomial p n).rename (λ i, (b,i)))) :=
begin
  have := witt_structure_int_prop p Φ n,
  replace := congr_arg (λ ψ, map (coe : ℤ → R) ψ) this,
  dsimp at this ⊢,
  rw [map_eval₂, map_eval₂, map_witt_polynomial] at this,
  simp only [function.comp, map_rename] at this ⊢,
  erw this, clear this,
  dsimp,
  suffices : (λ (x : idx), rename (prod.mk x) (map (coe : ℤ → R) (witt_polynomial p n))) =
    (λ (b : idx), rename (prod.mk b) (witt_polynomial p n)),
  { replace := congr_arg (λ g, eval₂ C g (map coe Φ)) this,
    dsimp at this, exact this },
  funext i, rw map_witt_polynomial
end

noncomputable def witt_add : ℕ → mv_polynomial (bool × ℕ) ℤ := witt_structure_int p (X tt + X ff)

noncomputable def witt_mul : ℕ → mv_polynomial (bool × ℕ) ℤ := witt_structure_int p (X tt * X ff)

noncomputable def witt_neg : ℕ → mv_polynomial (unit × ℕ) ℤ := witt_structure_int p (-X unit.star)

include p
def witt_vectors (α : Type*) := ℕ → α
omit p

namespace witt_vectors

local notation `𝕎` := witt_vectors -- type as `𝕎`

instance : functor (𝕎 p) :=
{ map := λ α β f v, f ∘ v,
  map_const := λ α β a v, λ _, a }

instance : is_lawful_functor (𝕎 p) :=
{ map_const_eq := λ α β, rfl,
  id_map := λ α v, rfl,
  comp_map := λ α β γ f g v, rfl }

variable (R)

instance : has_zero (𝕎 p R) :=
⟨λ _, 0⟩

variable {R}

def Teichmuller (r : R) : 𝕎 p R
| 0 := r
| (n+1) := 0

@[simp] lemma Teichmuller_zero : Teichmuller p (0:R) = 0 :=
funext $ λ n, match n with | 0 := rfl | (n+1) := rfl end

variable (R)

instance : has_one (𝕎 p R) :=
⟨Teichmuller p 1⟩

noncomputable instance : has_add (𝕎 p R) :=
⟨λ x y n, (witt_add p n).eval₂ (coe : ℤ → R) $ λ bn, cond bn.1 (x bn.2) (y bn.2)⟩

noncomputable instance : has_mul (𝕎 p R) :=
⟨λ x y n, (witt_mul p n).eval₂ (coe : ℤ → R) $ λ bn, cond bn.1 (x bn.2) (y bn.2)⟩

noncomputable instance : has_neg (𝕎 p R) :=
⟨λ x n, (witt_neg p n).eval₂ (coe : ℤ → R) $ λ bn, x bn.2⟩

variable {R}

@[simp] lemma Teichmuller_one : Teichmuller p (1:R) = 1 := rfl

-- TODO(jmc): Prove this
-- lemma Teichmuller_mul (x y : R) :
--   Teichmuller p (x * y) = Teichmuller p x * Teichmuller p y := sorry

variable {p}

noncomputable def ghost_component (n : ℕ) (w : 𝕎 p R) : R :=
(witt_polynomial p n).eval w

section map
open function
variables {α} {β : Type*}

def map (f : α → β) : 𝕎 p α → 𝕎 p β := λ w, f ∘ w

lemma map_injective (f : α → β) (hf : injective f) :
  injective (map f : 𝕎 p α → 𝕎 p β) :=
λ x y h, funext $ λ n, hf $ by exact congr_fun h n

lemma map_surjective (f : α → β) (hf : surjective f) :
  surjective (map f : 𝕎 p α → 𝕎 p β) :=
λ x, ⟨λ n, classical.some $ hf $ x n,
by { funext n, dsimp [map], rw classical.some_spec (hf (x n)) }⟩

variables (f : R → S) [is_ring_hom f]

@[simp] lemma map_zero : map f (0 : 𝕎 p R) = 0 :=
funext $ λ n, is_ring_hom.map_zero f

@[simp] lemma map_one : map f (1 : 𝕎 p R) = 1 :=
funext $ λ n,
match n with
| 0     := is_ring_hom.map_one f
| (n+1) := is_ring_hom.map_zero f
end

@[simp] lemma map_add (x y : 𝕎 p R) :
  map f (x + y) = map f x + map f y :=
funext $ λ n,
begin
  show f (eval₂ coe _ _) = eval₂ coe _ _,
  rw eval₂_comp_left f,
  congr' 1,
  { exact int.eq_cast' (f ∘ coe) },
  { funext bn, cases bn with b i,
    exact match b with | tt := rfl | ff := rfl end },
  recover, all_goals {apply_instance},
end

@[simp] lemma map_mul (x y : 𝕎 p R) :
  map f (x * y) = map f x * map f y :=
funext $ λ n,
begin
  show f (eval₂ coe _ _) = eval₂ coe _ _,
  rw eval₂_comp_left f,
  congr' 1,
  { exact int.eq_cast' (f ∘ coe) },
  { funext bn, cases bn with b i,
    exact match b with | tt := rfl | ff := rfl end },
  recover, all_goals {apply_instance},
end

@[simp] lemma map_neg (x : 𝕎 p R) :
  map f (-x) = -map f x :=
funext $ λ n,
begin
  show f (eval₂ coe _ _) = eval₂ coe _ _,
  rw eval₂_comp_left f,
  congr' 1,
  { exact int.eq_cast' (f ∘ coe) },
  recover, all_goals {apply_instance},
end

end map

noncomputable def ghost_map : 𝕎 p R → (ℕ → R) := λ w n, ghost_component n w

@[simp] lemma ghost_map.zero : ghost_map (0 : 𝕎 p R) = 0 :=
funext $ λ n,
begin
  delta ghost_map ghost_component witt_polynomial eval,
  rw eval₂_sum,
  apply finset.sum_eq_zero,
  intros i hi,
  rw [eval₂_mul, eval₂_pow, eval₂_X],
  convert mul_zero _,
  apply zero_pow _,
  apply nat.pow_pos,
  apply nat.prime.pos, assumption,
end

@[simp] lemma ghost_map.one : ghost_map (1 : 𝕎 p R) = 1 :=
funext $ λ n,
begin
  delta ghost_map ghost_component witt_polynomial eval,
  rw eval₂_sum,
  have : 0 ∈ finset.range (n+1),
  { rw finset.mem_range, exact nat.succ_pos n },
  rw ← finset.insert_erase this,
  rw finset.sum_insert (finset.not_mem_erase 0 (finset.range (n + 1))),
  convert add_zero _,
  { apply finset.sum_eq_zero, intros i hi,
    rw [eval₂_mul, eval₂_pow, eval₂_X],
    rw finset.mem_erase at hi,
    suffices H : (1 : 𝕎 p R) i = 0,
    { rw [H, zero_pow, mul_zero], apply nat.pow_pos, exact nat.prime.pos ‹_› },
    rw ← Teichmuller_one, cases hi with hi bla, revert hi,
    exact match i with
    | 0 := λ H, false.elim (H rfl)
    | (n+1) := λ H, rfl
    end },
  { rw [eval₂_mul, eval₂_pow, eval₂_X, eval₂_C],
    dsimp, rw one_mul, symmetry,
    apply one_pow }
end

variable {R}

-- Unfortunately the following lemma doesn't typecheck,
-- because we don't know that (𝕎 p R) is a comm_semiring

-- @[simp] lemma ghost_map.compat (x : idx → 𝕎 p R) (φ : mv_polynomial (idx × ℕ) ℤ) :
--   ghost_map (φ.eval₂ coe (λ bn, x bn.1)) = φ.eval₂ coe (λ bn, ghost_map (x bn.1)) :=
-- funext $ λ n,
-- begin
--   delta ghost_map ghost_component,
--   have := congr_arg (λ (ψ : mv_polynomial (bool × ℕ) R), ψ.eval $ λ (bn : bool × ℕ), cond bn.1 (x bn.2) (y bn.2)) (witt_structure_prop p (X tt + X ff) n),
--   convert this using 1; clear this,
--   { delta witt_vectors.has_add witt_add, dsimp [eval],
--     rw ← eval₂_assoc' _ _ _ _,
--     work_on_goal 0 { congr' 1, funext i, apply eval₂_eq_eval_map },
--     all_goals {try {assumption}, try {apply_instance}} },
--   { dsimp,
--     rw [mv_polynomial.map_add, eval₂_add, eval_add],
--     congr' 1,
--     all_goals {
--       erw [mv_polynomial.map_X (coe : ℤ → R), eval₂_X, eval_rename_prodmk],
--       congr } }
-- end

@[simp] lemma ghost_map.add (x y : 𝕎 p R) :
  ghost_map (x + y) = ghost_map x + ghost_map y :=
funext $ λ n,
begin
  delta ghost_map ghost_component,
  have := congr_arg (λ (ψ : mv_polynomial (bool × ℕ) R), ψ.eval $ λ (bn : bool × ℕ), cond bn.1 (x bn.2) (y bn.2)) (witt_structure_prop p (X tt + X ff) n),
  convert this using 1; clear this,
  { delta witt_vectors.has_add witt_add, dsimp [eval],
    rw ← eval₂_assoc' _ _ _ _,
    work_on_goal 0 { congr' 1, funext i, apply eval₂_eq_eval_map },
    all_goals {try {assumption}, try {apply_instance}} },
  { dsimp,
    rw [mv_polynomial.map_add, eval₂_add, eval_add],
    congr' 1,
    all_goals {
      erw [mv_polynomial.map_X (coe : ℤ → R), eval₂_X, eval_rename_prodmk],
      congr } }
end

@[simp] lemma ghost_map.mul (x y : 𝕎 p R) :
  ghost_map (x * y) = ghost_map x * ghost_map y :=
funext $ λ n,
begin
  delta ghost_map ghost_component,
  have := congr_arg (λ (ψ : mv_polynomial (bool × ℕ) R), ψ.eval $ λ (bn : bool × ℕ), cond bn.1 (x bn.2) (y bn.2)) (witt_structure_prop p (X tt * X ff) n),
  convert this using 1; clear this,
  { delta witt_vectors.has_mul witt_mul, dsimp [eval],
    rw ← eval₂_assoc' _ _ _ _,
    work_on_goal 0 { congr' 1, funext i, apply eval₂_eq_eval_map },
    all_goals {try {assumption}, try {apply_instance}} },
  { dsimp,
    rw [mv_polynomial.map_mul, eval₂_mul, eval_mul],
    congr' 1,
    all_goals {
      erw [mv_polynomial.map_X (coe : ℤ → R), eval₂_X, eval_rename_prodmk],
      congr } }
end

@[simp] lemma ghost_map.neg (x : 𝕎 p R) :
  ghost_map (-x) = - ghost_map x :=
funext $ λ n,
begin
  delta ghost_map ghost_component,
  have := congr_arg (λ (ψ : mv_polynomial (unit × ℕ) R), ψ.eval $ λ (bn : unit × ℕ), (x bn.2)) (witt_structure_prop p (-X unit.star) n),
  convert this using 1; clear this,
  { delta witt_vectors.has_neg witt_neg, dsimp [eval],
    rw ← eval₂_assoc' _ _ _ _,
    work_on_goal 0 { congr' 1, funext i, apply eval₂_eq_eval_map },
    all_goals {try {assumption}, try {apply_instance}} },
  { dsimp,
    rw [mv_polynomial.map_neg, map_X],
    have := eval_rename_prodmk (λ i : unit × ℕ, x i.2) () (witt_polynomial p n),
    dsimp at this,
    rw ← this, clear this,
    rw ← eval_neg,
    congr' 1,
    have := eval₂_neg (X ()) C (λ (b : unit), rename (prod.mk b) (witt_polynomial p n : mv_polynomial ℕ R)),
    rw eval₂_X at this,
    dsimp at this ⊢,
    exact this.symm }
end
.

#print eval₂_neg

lemma ghost_map.equiv_of_unit (pu : units R) (hp : (pu : R) = p) :
  𝕎 p R ≃ (ℕ → R) :=
{ to_fun := ghost_map,
  inv_fun := λ x n, (X_in_terms_of_W p pu hp n).eval x,
  left_inv :=
  begin
    intro x, funext n,
    dsimp [ghost_map, ghost_component, eval],
    rw eval₂_assoc' (id : R → R),
    { convert eval_X _, exact X_in_terms_of_W_prop p pu hp n },
    all_goals { assumption <|> apply_instance }
  end,
  right_inv :=
  begin
    intro x, funext n,
    dsimp [ghost_map, ghost_component, eval],
    rw eval₂_assoc' (id : R → R),
    { convert eval_X _,
      { simp only [eval₂_X, X_in_terms_of_W_prop₂] },
      { apply_instance } },
    all_goals { assumption <|> apply_instance }
  end }

lemma ghost_map.bijective_of_unit (pu : units R) (hp : (pu : R) = p) :
  function.bijective (ghost_map : 𝕎 p R → ℕ → R) :=
let H := (ghost_map.equiv_of_unit pu hp).bijective in
by { convert H using 1, delta ghost_map.equiv_of_unit, refl }

section
open function
variables {α' : Type*} [has_zero α'] [has_one α'] [has_add α'] [has_mul α'] [has_neg α']
variables {β : Type*} [comm_ring β]

def comm_ring_of_injective (f : α' → β) (inj : injective f)
  (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ {x y}, f (x + y) = f x + f y)
  (mul : ∀ {x y}, f (x * y) = f x * f y) (neg : ∀ {x}, f (-x) = - f x) :
  comm_ring α' :=
begin
  refine_struct { ..‹has_zero α'›, ..‹has_one α'›, ..‹has_add α'›, ..‹has_mul α'›, ..‹has_neg α'› },
  all_goals { intros, apply inj,
    repeat { erw zero <|> erw one <|> erw add <|> erw mul <|> erw neg },
    try {simp [mul_assoc, mul_add, add_mul] } },
  rw add_comm,
  rw mul_comm
end

def comm_ring_of_surjective (f : β → α') (sur : surjective f)
  (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ {x y}, f (x + y) = f x + f y)
  (mul : ∀ {x y}, f (x * y) = f x * f y) (neg : ∀ {x}, f (-x) = - f x) :
  comm_ring α' :=
begin
  refine_struct { ..‹has_zero α'›, ..‹has_one α'›, ..‹has_add α'›, ..‹has_mul α'›, ..‹has_neg α'› },
  all_goals {
    try { intro a, rcases sur a with ⟨a, rfl⟩ },
    try { intro b, rcases sur b with ⟨b, rfl⟩ },
    try { intro c, rcases sur c with ⟨c, rfl⟩ },
    repeat { erw ← zero <|> erw ← one <|> erw ← add <|> erw ← mul <|> erw ← neg },
    try {simp [mul_assoc, mul_add, add_mul] } },
  rw add_comm,
  rw mul_comm
end

variable (R)

def mv_polynomial.counit : mv_polynomial R ℤ →+* R :=
eval₂_hom coe id

-- instance mv_polynomial.counit.is_ring_hom : is_ring_hom (mv_polynomial.counit R) :=
-- by delta mv_polynomial.counit; apply_instance

lemma counit_surjective : surjective (mv_polynomial.counit R) :=
λ r, ⟨X r, eval₂_X _ _ _⟩

end

variable (R)

def aux₁ : comm_ring (𝕎 p (mv_polynomial R ℚ)) :=
comm_ring_of_injective (ghost_map)
  (ghost_map.bijective_of_unit ((rat.pu p).map C)
  (by rw ← C_eq_coe_nat; refl)).1
  (@ghost_map.zero p _ (mv_polynomial R ℚ) _ _)
  (ghost_map.one) (ghost_map.add) (ghost_map.mul) (ghost_map.neg)

local attribute [instance] aux₁
.

def aux₂ : comm_ring (𝕎 p (mv_polynomial R ℤ)) :=
have hom : is_ring_hom (mv_polynomial.map coe : mv_polynomial R ℤ → mv_polynomial R ℚ), by apply_instance,
comm_ring_of_injective (map $ mv_polynomial.map (coe : ℤ → ℚ))
  (map_injective _ $ mv_polynomial.coe_int_rat_map_injective _)
  (@map_zero _ _ _ _ _ _ _ _ _ hom)
  (@map_one _ _ _ _ _ _ _ _ _ hom)
  (@map_add _ _ _ _ _ _ _ _ _ hom)
  (@map_mul _ _ _ _ _ _ _ _ _ hom)
  (@map_neg _ _ _ _ _ _ _ _ _ hom)

local attribute [instance] aux₂
.

instance : comm_ring (𝕎 p R) :=
comm_ring_of_surjective
(map $ mv_polynomial.counit _) (map_surjective _ $ counit_surjective _)
  (@map_zero _ _ _ _ _ _ _ _ _ (mv_polynomial.counit.is_ring_hom R))
  (@map_one _ _ _ _ _ _ _ _ _ (mv_polynomial.counit.is_ring_hom R))
  (@map_add _ _ _ _ _ _ _ _ _ (mv_polynomial.counit.is_ring_hom R))
  (@map_mul _ _ _ _ _ _ _ _ _ (mv_polynomial.counit.is_ring_hom R))
  (@map_neg _ _ _ _ _ _ _ _ _ (mv_polynomial.counit.is_ring_hom R))

end witt_vectors
