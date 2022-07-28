/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import data.polynomial.ring_division
import dynamics.periodic_pts

/-!
# IMO 2006 Q5

Let $P(x)$ be a polynomial of degree $n>1$ with integer coefficients, and let $k$ be a positive
integer. Consider the polynomial $Q(x) = P(P(\ldots P(P(x))\ldots))$, where $P$ occurs $k$ times.
Prove that there are at most $n$ integers $t$ such that $Q(t)=t$.

## Sketch of solution

The following solution is adapted from
https://artofproblemsolving.com/wiki/index.php/2006_IMO_Problems/Problem_5.

Let $P^k$ denote the polynomial $P$ composed with itself $k$ times. We rely on a key observation: if
$P^k(t)=t$, then $P(P(t))=t$. We prove this by building the cyclic list
$(P(t)-t,P^2(t)-P(t),\ldots)$, and showing that each entry divides the next, which by transitivity
implies they all divide each other, and thus have the same absolute value.

If the entries in this list are all pairwise equal, then we can show inductively that for positive
$n$, $P^n(t)-t$ must always have the same sign as $P(t)-t$. Substituting $n=k$ gives us $P(t)=t$ and
in particular $P(P(t))=t$.

Otherwise, there must be two consecutive entries that are opposites of one another. This means
$P^{n+2}(t)-P^{n+1}(t)=P^n(t)-P^{n+1}(t)$, which implies $P^{n+2}(t)=P^n(t)$ and $P(P(t))=t$.

With this lemma, we can reduce the problem to the case $k=2$. If every root of $P(P(t))-t$ is also a
root of $P(t)-t$, then we're done. Otherwise, there exist $a$ and $b$ with $a\ne b$ and $P(a)=b$,
$P(b)=a$. For any root $t$ of $P(P(t))-t$, defining $u=P(t)$, we easily verify $a-t\mid b-u$,
$b-u\mid a-t$, $a-u\mid b-t$, $b-t\mid a-u$, which imply $|a-t|=|b-u|$ and $|a-u|=|b-t|$. By casing
on these equalities, we deduce $a+b=t+u$. This means that every root of $P(P(t))-t$ is a root of
$P(t)+t-a-b$, and we're again done.
-/

open function polynomial

/-- If every entry in a cyclic list of integers divides the next, then they all have the same
absolute value -/
theorem nat_abs_eq_of_chain_dvd {l : cycle ℤ} {x y : ℤ} (hl : l.chain (∣))
  (hx : x ∈ l) (hy : y ∈ l) : x.nat_abs = y.nat_abs :=
begin
  rw cycle.chain_iff_pairwise at hl,
  exact int.nat_abs_eq_of_dvd_dvd (hl x hx y hy) (hl y hy x hx)
end

theorem add_eq_add_of_nat_abs_eq_of_nat_abs_eq {a b c d : ℤ} (hne : a ≠ b)
  (h₁ : (c - a).nat_abs = (d - b).nat_abs) (h₂ : (c - b).nat_abs = (d - a).nat_abs) :
  a + b = c + d :=
begin
  cases int.nat_abs_eq_nat_abs_iff.1 h₁ with h₁ h₁,
  { cases int.nat_abs_eq_nat_abs_iff.1 h₂ with h₂ h₂,
    { exact (hne $ by linarith).elim  },
    { linarith } },
  { linarith }
end

/-- The main lemma in the proof: if $P^k(t)=t$, then $P(P(t))=t$. -/
theorem periodic_lemma {P : polynomial ℤ} {t : ℤ}
  (ht : t ∈ periodic_pts (λ x, P.eval x)) : is_periodic_pt (λ x, P.eval x) 2 t :=
begin
  -- The cycle [P(t) - t, P(P(t)) - P(t), ...]
  let C : cycle ℤ := (periodic_orbit (λ x, P.eval x) t).map (λ x, P.eval x - x),
  have HC : ∀ {n : ℕ}, (λ x, P.eval x)^[n + 1] t - ((λ x, P.eval x)^[n] t) ∈ C,
  { intro n,
    rw [cycle.mem_map, function.iterate_succ_apply'],
    exact ⟨_, iterate_mem_periodic_orbit ht n, rfl⟩ },

  -- Elements in C are all divisible by one another.
  have Hdvd : C.chain (∣),
  { rw [cycle.chain_map, periodic_orbit_chain' _ ht],
    intro n,
    convert sub_dvd_eval_sub ((λ x, P.eval x)^[n + 1] t) ((λ x, P.eval x)^[n] t) P;
    rw function.iterate_succ_apply' },

  -- Any two entries in C have the same absolute value.
  have Habs : ∀ m n : ℕ, ((λ x, P.eval x)^[m + 1] t - ((λ x, P.eval x)^[m] t)).nat_abs =
    ((λ x, P.eval x)^[n + 1] t - ((λ x, P.eval x)^[n] t)).nat_abs :=
  λ m n, nat_abs_eq_of_chain_dvd Hdvd HC HC,

  -- We case on whether the elements on C are pairwise equal.
  by_cases HC' : C.chain (=),
  { -- Any two entries in C are equal.
    have Heq : ∀ m n : ℕ, (λ x, P.eval x)^[m + 1] t - ((λ x, P.eval x)^[m] t) =
      ((λ x, P.eval x)^[n + 1] t - ((λ x, P.eval x)^[n] t)) :=
    λ m n, cycle.chain_iff_pairwise.1 HC' _ HC _ HC,

    -- The sign of P^n(t) - t is the same as P(t) - t for positive n. Proven by induction on n.
    have IH : ∀ n : ℕ, ((λ x, P.eval x)^[n + 1] t - t).sign = (P.eval t - t).sign,
    { intro n,
      induction n with n IH,
      { refl },
      { apply eq.trans _ (int.sign_add_eq_of_sign_eq IH),
        have H := Heq n.succ 0,
        dsimp at H ⊢,
        rw [←H, sub_add_sub_cancel'] } },

    -- This implies that the sign of P(t) - t is the same as the sign of P^k(t) - t, which is 0.
    -- Hence P(t) = t and P(P(t)) = P(t).
    rcases ht with ⟨(_ | k), hk, hk'⟩,
    { exact (irrefl 0 hk).elim },
    { have H := IH k,
      rw [hk'.is_fixed_pt.eq, sub_self, int.sign_zero, eq_comm, int.sign_eq_zero_iff_zero,
        sub_eq_zero] at H,
      simp [is_periodic_pt, is_fixed_pt, H] } },
  { -- We take two nonequal consecutive entries.
    rw [cycle.chain_map, periodic_orbit_chain' _ ht] at HC',
    push_neg at HC',
    cases HC' with n hn,

    -- They must have opposite sign, so that P^{k + 1}(t) - P^k(t) = P^{k + 2}(t) - P^{k + 1}(t).
    cases int.nat_abs_eq_nat_abs_iff.1 (Habs n n.succ) with hn' hn',
    { apply (hn _).elim,
      convert hn';
      simp only [function.iterate_succ_apply'] },

    -- We deduce P^{k + 2}(t) = P^k(t) and hence P(P(t)) = t.
    { rw [neg_sub, sub_right_inj] at hn',
      simp only [function.iterate_succ_apply'] at hn',
      exact @is_periodic_pt_of_mem_periodic_pts_of_is_periodic_pt_iterate _ _ t 2 n ht hn'.symm } }
end

@[simp] theorem iterate_comp_eval (P : polynomial ℤ) (k : ℕ) (t : ℤ) :
  (P.comp^[k] X).eval t = ((λ x, P.eval x)^[k] t) :=
begin
  induction k with k IH,
  { simp },
  { rw [iterate_succ_apply', iterate_succ_apply', eval_comp, IH] }
end

@[simp] theorem nat_degree_iterate_comp (P : polynomial ℤ) (k : ℕ) :
  (P.comp^[k] X).nat_degree = P.nat_degree ^ k :=
begin
  induction k with k IH,
  { simp },
  { rw [iterate_succ_apply', nat_degree_comp, IH, pow_succ] }
end

theorem iterate_comp_ne_X {P : polynomial ℤ} (hP : 1 < P.nat_degree) {k : ℕ} (hk : 0 < k) :
  P.comp^[k] X - X ≠ 0 :=
by { rw sub_ne_zero, apply_fun nat_degree, simpa using (one_lt_pow hP hk.ne').ne' }

/-- We solve the problem for the specific case k = 2 first. -/
theorem imo2006_q5' {P : polynomial ℤ} (hP : 1 < P.nat_degree) :
  (P.comp P - X).roots.to_finset.card ≤ P.nat_degree :=
begin
  -- Auxiliary lemmas on degrees.
  have hPX : (P - X).nat_degree = P.nat_degree,
  { rw nat_degree_sub_eq_left_of_nat_degree_lt,
    simpa using hP },
  have hPX' : P - X ≠ 0,
  { intro h,
    rw [h, nat_degree_zero] at hPX,
    rw ←hPX at hP,
    exact (zero_le_one.not_lt hP).elim },

  -- If every root of P(P(t)) - t is also a root of P(t) - t, then we're done.
  by_cases H : (P.comp P - X).roots.to_finset ⊆ (P - X).roots.to_finset,
  { exact (finset.card_le_of_subset H).trans ((multiset.to_finset_card_le _).trans
      ((card_roots' _).trans_eq hPX)) },

  -- Otherwise, take a, b with P(a) = b, P(b) = a, a ≠ b.
  { rcases (finset.not_subset _ _).1 H with ⟨a, ha, hab⟩,
    replace ha := is_root_of_mem_roots (multiset.mem_to_finset.1 ha),
    simp [sub_eq_zero] at ha,
    simp [mem_roots hPX'] at hab,
    set b := P.eval a,
    rw sub_eq_zero at hab,

    -- More auxiliary lemmas on degree.
    have hPab : (P + X - a - b).nat_degree = P.nat_degree,
    { rw [sub_sub, ←int.cast_add],
      have h₁ : (P + X).nat_degree = P.nat_degree,
      { rw nat_degree_add_eq_left_of_nat_degree_lt,
        simpa using hP },
      rw nat_degree_sub_eq_left_of_nat_degree_lt;
      rwa h₁,
      rw nat_degree_int_cast,
      exact zero_lt_one.trans hP },
    have hPab' : P + X - a - b ≠ 0,
    { intro h,
      rw [h, nat_degree_zero] at hPab,
      rw ←hPab at hP,
      exact (zero_le_one.not_lt hP).elim },

    -- We claim that every root of P(P(t)) - t is a root of P(t) + t - a - b. This allows us to
    -- conclude the problem.
    suffices H' : (P.comp P - X).roots.to_finset ⊆ (P + X - a - b).roots.to_finset,
    { exact (finset.card_le_of_subset H').trans ((multiset.to_finset_card_le _).trans $
        (card_roots' _).trans_eq hPab) },

    { -- Let t be a root of P(P(t)) - t, define u = P(t).
      intros t ht,
      replace ht := is_root_of_mem_roots (multiset.mem_to_finset.1 ht),
      simp [sub_eq_zero] at ht,
      simp only [mem_roots hPab', sub_eq_iff_eq_add, multiset.mem_to_finset, is_root.def, eval_sub,
        eval_add, eval_X, eval_C, eval_int_cast, int.cast_id, zero_add],

      -- An auxiliary lemma proved earlier implies we only need to show |t - a| = |u - b| and
      -- |t - b| = |u - a|. We prove this by establishing that each side of either equation divides
      -- the other.
      apply (add_eq_add_of_nat_abs_eq_of_nat_abs_eq hab _ _).symm;
      apply int.nat_abs_eq_of_dvd_dvd;
      set u := P.eval t,
      { rw [←ha, ←ht], apply sub_dvd_eval_sub },
      { apply sub_dvd_eval_sub },
      { rw ←ht, apply sub_dvd_eval_sub },
      { rw ←ha, apply sub_dvd_eval_sub } } }
end

/-- The general problem follows easily from the k = 2 case. -/
theorem imo2006_q5 {P : polynomial ℤ} (hP : 1 < P.nat_degree) {k : ℕ} (hk : 0 < k) :
  (P.comp^[k] X - X).roots.to_finset.card ≤ P.nat_degree :=
begin
  apply (finset.card_le_of_subset $ λ t ht, _).trans (imo2006_q5' hP),
  have hP' : P.comp P - X ≠ 0 := by simpa using iterate_comp_ne_X hP zero_lt_two,
  replace ht := is_root_of_mem_roots (multiset.mem_to_finset.1 ht),
  simp only [sub_eq_zero, is_root.def, eval_sub, iterate_comp_eval, eval_X] at ht,
  simpa [mem_roots hP', sub_eq_zero] using periodic_lemma ⟨k, hk, ht⟩
end
