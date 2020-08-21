import measure_theory.interval_integral
import measure_theory.lebesgue_measure
import analysis.special_functions.exp_log
import analysis.transcendental.small_lemmas

noncomputable theory
open_locale classical
open_locale big_operators
open small_lemmas

notation α`[X]` := polynomial α

namespace e_transcendental_lemmas

/-- # Definition and some theorems about differentiating multiple times
-/

/-Definition
For any integer polynomial $f$ and $n\in\mathbb N$ we define `deriv_n f n` to be the $n$-th derivative of polynomial $f$. $h^{[n]}$ means $h\circ h\circ h\cdots\circ h$ $n$-times.
-/
def deriv_n (f : ℤ[X]) (n : ℕ) : ℤ[X] := polynomial.derivative ^[n] f

/-Lemma
the zeroth derivative of polynomial $f$ is $f$ itself.
-/
lemma zeroth_deriv (f : ℤ[X]) : deriv_n f 0 = f :=
begin
    -- This is purely definition of `deriv_n f n`
    -- We also used $f^{[n]}=\mathrm{id}$ and $\mathrm{id} x = x$.
    rw deriv_n, simp only [id.def, function.iterate_zero],
end

/-Lemma
the derivative of $f^{(n)}$ is $f^{(n+1)}$
-/
lemma deriv_succ (f : ℤ[X]) (n : ℕ) : (deriv_n f n).derivative = (deriv_n f (n+1)) :=
begin
    -- By definition and $h^{[n+1]}=h\circ h^{[n]}$
    rw [deriv_n, deriv_n, function.iterate_succ'],
end

/-Lemma
the $n$-th derivative of zero polynomial is $0$
-/
lemma deriv_zero_p (n : ℕ) : deriv_n 0 n = 0 :=
begin
    -- We prove by induction. Base case and inductive case can all be done with `simp`
    induction n with n hn; simp only [deriv_n, id.def, function.iterate_zero], rw <-deriv_n, assumption,
end

/-Lemma
If the $n$-th coefficient of $f$ is $a_n$, then the $n$-th coefficient in $f^{(k)}$ is $\left(\prod_{i=0}^{k-1} (n+k-i)\right)a_{n+k}$
-/
lemma deriv_n_coeff (f : ℤ[X]) (k : ℕ) : ∀ n : ℕ, (deriv_n f k).coeff n = (∏ i in finset.range k, (n+k-i)) * (f.coeff (n+k)) :=
begin
    -- So we use induction on $k$
    induction k with k ih,
    -- For the zeroth derivative, $f^{(0)}=f$. This case is true by `simp`.
    simp only [add_zero, nat.nat_zero_eq_zero, one_mul, finset.range_zero, finset.prod_empty], rw deriv_n, simp only [forall_const, id.def, eq_self_iff_true, function.iterate_zero],

    -- Let us assume our claim is true for $k$ and consider the $m$-th coefficient.
    intro m,
    -- We know that $f^{(k+1)}=\left(f^{(k)}\right)'$ and for any polynomial $g$, the $m$-th coefficient of $g'$ is $(m+1)\times (m+1)$-th coefficient of $g$. Then we can use induction hypothesis with $m+1$.
    rw [deriv_n, function.iterate_succ'], simp only [function.comp_app, int.coe_nat_succ], rw <-deriv_n,
    rw polynomial.coeff_derivative, rw ih (m+1),
    rw finset.prod_range_succ, simp only [int.coe_nat_succ, int.nat_cast_eq_coe_nat],
    -- The rest of the proves are trivial to a pair of human eyes. But we need to give computers some hint to solve this triviality.
    have triv : (∏ (x : ℕ) in finset.range k, ((m:ℤ) + 1 + ↑k - ↑x)) = ∏ (x : ℕ) in finset.range k, (↑m + (↑k + 1) - ↑x),
    {
        apply congr_arg, ext, simp only [sub_left_inj], ring,
    }, rw triv,
    replace triv : (m + 1 : ℤ) = (m + (k+1) - k:ℤ),
    {
        rw add_sub_assoc, simp only [add_sub_cancel'],
    }, rw triv,
    replace triv : f.coeff (m + 1 + k) = f.coeff (m + k.succ),
    {
        rw nat.succ_eq_add_one, ring,
    },
    rw triv, ring,
end

/-Lemma
Like first derivative, higher derivatives still respect addition
-/
lemma deriv_n_add (p q :ℤ[X]) (n : ℕ) : (deriv_n (p+q) n) = (deriv_n p n) + (deriv_n q n) :=
begin
    induction n with n ih, rw [deriv_n, deriv_n, deriv_n], simp only [id.def, function.iterate_zero],
    rw [deriv_n, deriv_n, deriv_n, function.iterate_succ'], simp only [function.comp_app], rw [<-deriv_n,<-deriv_n,<-deriv_n, ih], simp only [polynomial.derivative_add],
end

/-Lemma
For any polynomial $f$ with degree $d$, the $d+1$-th derivative is zero.
-/
theorem deriv_too_much (f : ℤ[X]): (deriv_n f (f.nat_degree + 1)) = 0 :=
begin
    -- We prove that all coefficient of $f^{(d+1)}$ is zero.
    ext,
    -- We use lemma `deriv_n_coeff` and all coefficient of zero polynomial is $0$.
    rw deriv_n_coeff, simp only [int.coe_nat_succ, polynomial.coeff_zero, mul_eq_zero], right,
    -- Then the problem reduces to prove that $d+1$-th coeffcient of $f$ is zero. But $f$ has degree $d$. So we just need $d < d+1$. This is proved by `linarith`.
    apply polynomial.coeff_eq_zero_of_nat_degree_lt, linarith,
end

/-Lemma
if $i+1\le n$ then $n-(i+1)+1=n-i$
-/
private lemma nat_sub_eq (n i : ℕ) (h : i + 1 ≤ n) : (n - (i + 1) + 1) = n - i :=
begin
    have triv : n - (i+1) = n - i - 1, exact rfl,
    rw triv, apply nat.sub_add_cancel, exact nat.le_sub_left_of_add_le h,
end

/-Lemma
We have the pascal triangle
\[{n\choose k+1}+{n\choose k} = {n+1\choose k+1}\]
-/
private lemma pascal_triangle (n k : ℕ) : (n.choose (k+1)) + (n.choose k) = (n+1).choose (k+1) :=
begin
    -- This is actually how `mathlib` defined binomial coefficient.
    exact add_comm (nat.choose n (k + 1)) (nat.choose n k),
end

/-Theorem
We also have that for $p,q\in\mathbb Z[x]$,
\[
    (p\times q)^{(n)} = \sum_{i=0}^n\left({n\choose i}p^{(i)}q^{(n-i)}\right)
\]
-/

lemma deriv_n_poly_prod (p q : ℤ[X]) (n : ℕ) : deriv_n (p * q) n = ∑ k in finset.range n.succ, (polynomial.C (n.choose k:ℤ)) * (deriv_n p (n-k)) * (deriv_n q k) :=
begin
    -- We prove by induction on $n$.
    induction n with n IH,
    -- For $n=0$, we are using `zeroth_deriv`.
    simp only [zeroth_deriv, nat.choose_self, int.cast_coe_nat, ring_hom.eq_int_cast, one_mul, nat.cast_one, finset.sum_singleton, finset.range_one],

    {
        -- For inductive case
        -- We use $(pq)^{(n+1)}=d(pq)^{(n)}$, inductive hypothesis and that derivative is linear.
        rw deriv_n, rw function.iterate_succ', dsimp, rw <-deriv_n,
        rw IH, simp only [polynomial.derivative_sum, polynomial.derivative_mul, zero_mul, polynomial.derivative_C, zero_add, polynomial.derivative_sum, polynomial.derivative_mul, zero_mul, polynomial.derivative_C, zero_add],
        -- The rest of the proves is essentially openning and closing brackets and renaming summing indeces.
        rw finset.sum_add_distrib,
        conv_lhs {rw finset.sum_range_succ', rw finset.sum_range_succ, simp only [zeroth_deriv, nat.choose_self, one_mul, nat.choose_zero_right, int.coe_nat_zero, nat.sub_self, polynomial.C_1, int.coe_nat_succ, nat.sub_zero, zero_add]},
        have eq :
        ∑ (i : ℕ) in finset.range n,
          polynomial.C (n.choose (i + 1):ℤ) * (deriv_n p (n - (i + 1))).derivative * deriv_n q (i + 1) +
        (deriv_n p n).derivative * q +
        (p * (deriv_n q n).derivative +
         ∑ (x : ℕ) in finset.range n, polynomial.C (n.choose x:ℤ) * deriv_n p (n - x) * (deriv_n q x).derivative) =
        (∑ (i : ℕ) in finset.range n,
          polynomial.C (n.choose (i + 1):ℤ) * (deriv_n p (n - (i + 1))).derivative * deriv_n q (i + 1)) +
        (∑ (x : ℕ) in finset.range n, polynomial.C (n.choose x:ℤ) * deriv_n p (n - x) * (deriv_n q x).derivative) +
        ((deriv_n p n).derivative * q + (p * (deriv_n q n).derivative)) := by ring,
        rw [eq, <-finset.sum_add_distrib],

        replace eq :
        (∑ (x : ℕ) in finset.range n,
        (polynomial.C (n.choose (x + 1):ℤ) * (deriv_n p (n - (x + 1))).derivative * deriv_n q (x + 1) +
           polynomial.C (n.choose x:ℤ) * deriv_n p (n - x) * (deriv_n q x).derivative)) =
        (∑ (x : ℕ) in finset.range n,
        (polynomial.C (n.choose (x + 1):ℤ) * (deriv_n p (n - x)) * deriv_n q (x + 1) +
           polynomial.C (n.choose x:ℤ) * deriv_n p (n - x) * (deriv_n q (x+1)))),
        {
            apply finset.sum_congr, exact rfl, intros i hi, simp only [deriv_succ, int.cast_coe_nat, ring_hom.eq_int_cast, add_left_inj], simp only [finset.mem_range] at hi,
            replace hi : i + 1 ≤ n := hi,
            rw nat_sub_eq _ _ hi,
        }, rw eq,

        replace eq :
        (∑ (x : ℕ) in finset.range n,
        (polynomial.C (n.choose (x + 1):ℤ) * (deriv_n p (n - x)) * deriv_n q (x + 1) +
           polynomial.C (n.choose x:ℤ) * deriv_n p (n - x) * (deriv_n q (x+1)))) =
        (∑ (x : ℕ) in finset.range n,
        ((polynomial.C (n.choose (x + 1):ℤ) + polynomial.C (n.choose x:ℤ)) * (deriv_n p (n - x)) * deriv_n q (x + 1))),
        {
            apply congr_arg, rw function.funext_iff, intro i, ring,
        }, rw eq,

        replace eq :
        (∑ (x : ℕ) in finset.range n,
        ((polynomial.C (n.choose (x + 1):ℤ) + polynomial.C (n.choose x:ℤ)) * (deriv_n p (n - x)) * deriv_n q (x + 1))) =
        (∑ (x : ℕ) in finset.range n,
        ((polynomial.C (n.choose (x + 1) + (n.choose x):ℤ)) * (deriv_n p (n - x)) * deriv_n q (x + 1))),
        {
            apply congr_arg, rw function.funext_iff, intro i, simp only [int.cast_add, ring_hom.eq_int_cast],
        }, rw eq,

        replace eq :
        (∑ (x : ℕ) in finset.range n,
        ((polynomial.C (n.choose (x + 1) + (n.choose x):ℤ)) * (deriv_n p (n - x)) * deriv_n q (x + 1))) =
        (∑ (x : ℕ) in finset.range n,
        ((polynomial.C ((n+1).choose (x + 1):ℤ)) * (deriv_n p (n - x)) * deriv_n q (x + 1))),
        {
            apply congr_arg, rw function.funext_iff, intro i, rw <-pascal_triangle, simp only [int.coe_nat_add],
        }, rw eq,

        conv_rhs {rw finset.sum_range_succ', rw finset.sum_range_succ}, simp only [deriv_succ, zeroth_deriv, nat.succ_eq_add_one, nat.choose_self, int.cast_coe_nat, ring_hom.eq_int_cast, one_mul, nat.succ_sub_succ_eq_sub, nat.choose_zero_right, int.coe_nat_zero, nat.sub_self, int.cast_one, int.coe_nat_succ, nat.sub_zero, zero_add], ring,
    }
end

/-Theorem
For a polynomial $f$ then if $n>0$, we have $f^{(n)}=f^{(n-1)}\times f'$
-/

theorem poly_pow_deriv (f : ℤ[X]) (n : ℕ) (hn : 0 < n) : (f ^ n).derivative = (polynomial.C (n:ℤ)) * (f ^ (n-1)) * f.derivative :=
begin
    induction n with n IH,
    exfalso, linarith,
    {
        cases n,
        simp only [ring_hom.eq_int_cast, one_mul, int.coe_nat_zero, int.cast_one, int.coe_nat_succ, pow_one, zero_add, pow_zero],
        replace IH := IH (nat.succ_pos n),
        rw nat.succ_eq_add_one, rw pow_add, simp only [int.cast_coe_nat, int.cast_add, ring_hom.eq_int_cast, polynomial.derivative_mul, int.cast_one, nat.succ_add_sub_one,
 int.coe_nat_succ, pow_one], rw IH, simp only [nat.succ_sub_succ_eq_sub, polynomial.C_add, polynomial.C_1, int.coe_nat_succ, nat.sub_zero, nat.succ_sub_succ_eq_sub,
 int.coe_nat_succ, nat.sub_zero],
        have eq1 : (polynomial.C ↑n + 1) * f ^ n * f.derivative * f = (polynomial.C ↑n + 1) * f ^ (n+1) * f.derivative,
        {
            rw pow_add, simp only [int.cast_coe_nat, ring_hom.eq_int_cast, pow_one], ring,
        } ,
        rw eq1, rw nat.succ_eq_add_one, repeat {rw add_mul}, simp only [int.cast_coe_nat, ring_hom.eq_int_cast, one_mul],
    }
end

/-- # Assumption-/
/-Theorem
fundamental theorem of calculus and integration by part is assumed. I am waiting for them to arrive in `mathlib` and I will update this part and prove relatvent additional assumptions.
-/


private lemma ftc1 (f : ℝ -> ℝ) {hf : measurable f} {hf2 : continuous f} (a b : ℝ) (h : a ≤ b) {hf3 : measure_theory.integrable_on f (set.Icc a b)} (x0 : ℝ) (hx0 : x0 ∈ set.Icc a b) :
  has_deriv_at (λ (b : ℝ), ∫ (x : ℝ) in a..b, f x) (f x0) x0 :=
begin
  apply interval_integral.integral_has_deriv_at_of_tendsto_ae,
  simp only [], exact hf,
  unfold interval_integrable,
  split,
  apply measure_theory.integrable_on.mono hf3,
  intros y hy,
  simp only [set.mem_Ioc, set.mem_Icc] at ⊢ hy hx0,
  split, linarith, linarith,
  apply le_refl _,

  apply measure_theory.integrable_on.mono hf3,
  intros y hy,
  simp only [set.mem_Ioc, set.mem_Icc] at ⊢ hy hx0,
  split, linarith, linarith,
  apply le_refl _,

  apply filter.tendsto_inf_left,
  exact continuous.tendsto hf2 x0,
end

theorem ftc' (F f: ℝ -> ℝ) {hF : differentiable ℝ F}
{F_deriv : deriv F = f} {hf : measurable f} {hf1 : continuous f}
(a b : ℝ) (h : a ≤ b) :  (∫ x in a..b, f x) = F b - F a :=
begin
  by_cases hab : (a = b),
  rw hab, simp only [interval_integral.integral_same, sub_self],

  set G := (λ x, (∫ t in a..x, f t)) with hG,
  have prop := ftc1 f a b h,
  rw <-hG at prop,
  have hG1 : differentiable_on ℝ G (set.Icc a b),
  {
    intros x hx,
    have prop := ftc1 f a b h x hx,
    refine differentiable_at.differentiable_within_at _,
    rw hG,
    exact has_deriv_at.differentiable_at prop,
    exact hf, exact hf1,

    apply continuous.integrable_on_compact _ hf1,
    exact real.locally_finite_volume, exact compact_Icc,
  },
  have H : (set.Icc a b).indicator (deriv G) = (set.Icc a b).indicator f,
  {
    apply set.indicator_congr,
    intros x0 hx0,
    replace prop := prop x0 hx0,
    exact has_deriv_at.deriv prop,
  },
  have H2 : (set.Icc a b).indicator (deriv G) = (set.Icc a b).indicator (deriv F),
  {
    exact eq.trans H (congr_arg (set.Icc a b).indicator (eq.symm F_deriv)),
  },

  replace H2 : ∀ y ∈ set.Icc a b, (deriv (F - G)) y = 0,
  {
    intros y hy,
    change deriv (λ t, F t - G t) y = 0,
    rw deriv_sub, rw sub_eq_zero,

    have eq1 : (set.Icc a b).indicator (deriv F) y = deriv F y,
    exact if_pos hy, rw <-eq1,
    have eq2 : (set.Icc a b).indicator (deriv G) y = deriv G y,
    exact if_pos hy, rw <-eq2, exact congr_fun H2.symm y,

    dsimp only [],
    exact hF y,

    dsimp only [],
    exact has_deriv_at.differentiable_at (prop y hy),
  },

  have key : ∀ y ∈ set.Ioc a b, (F - G) y = (F - G) a,
  {
    intros y hy,
    have ineq : a < y, simp only [set.mem_Ioc] at hy, exact hy.1,
    have key := exists_deriv_eq_slope (F - G) ineq _ _,
    rcases key with ⟨c, hc, hc2⟩,
    have hc' : c ∈ set.Icc a b,
      simp only [set.mem_Icc, set.mem_Ioc, set.mem_Ioo] at hy ⊢ hc,
      split, linarith, linarith,
    rw H2 c hc' at hc2,
    replace hc2 := eq.symm hc2,
    rw div_eq_zero_iff at hc2,
    cases hc2, exact sub_eq_zero.mp hc2,
    simp only [set.mem_Icc, set.mem_Ioc, set.mem_Ioo] at hy ⊢ hc, linarith,

    apply continuous_on.sub,
    simp only [], apply continuous.continuous_on,
    apply differentiable.continuous hF,

    have hG1' : continuous_on G (set.Icc a b),
      apply differentiable_on.continuous_on hG1,
    simp only [], apply continuous_on.mono hG1',
    apply set.Icc_subset_Icc, exact le_refl a, exact hy.2,

    apply differentiable_on.sub,
    simp only [], exact differentiable.differentiable_on hF,
    simp only [], apply differentiable_on.mono hG1,
    intros z hz,
    simp only [set.mem_Icc, set.mem_Ioc, set.mem_Ioo] at *,
    split, linarith, linarith,
  },

  have G_a : G a = 0,
  {
    rw hG, simp only [interval_integral.integral_same],
  },
  have G_b : G b = ∫ x in a .. b, f x,
  {
    rw hG,
  },
  rw <-G_b,
  have eq : G b = G b - 0, rw sub_zero, rw eq, rw <-G_a,
  rw sub_eq_sub_iff_sub_eq_sub,
  suffices : F b - G b = F a - G a, linarith,
  replace key := key b _,
  simp only [pi.sub_apply] at key ⊢, exact key,
  simp only [set.mem_Icc, set.mem_Ioc, set.mem_Ioo] at *,
  split, exact lt_of_le_of_ne h hab, exact le_refl b,

  exact hf, exact hf1,
  apply measure_theory.integrable_on.mono_set (continuous.integrable_on_compact (@compact_Icc a b) hf1),
  exact set.subset.rfl,
  exact real.locally_finite_volume,
end

theorem ftc (f: ℝ -> ℝ) {hf : differentiable ℝ f} {hf2 : measurable (deriv f)} {hf3 : continuous (deriv f)} (a b : ℝ) (h : a ≤ b) :  (∫ x in a..b, (deriv f) x) = f b - f a :=
begin
  refine ftc' f (deriv f) a b h,
  simp only [], exact hf,
  refl, exact hf2, exact hf3,
end

theorem integrate_by_part (f g : ℝ -> ℝ)
  {hf : differentiable ℝ f} {hf2 : measurable (deriv f)}
  {hf3 : measurable f} {hf4 : continuous (deriv f)}
  {hg : differentiable ℝ g} {hg2 : measurable (deriv g)}
  {hg3 : measurable g} {hg4 : continuous (deriv g)}
  (a b : ℝ) (h : a ≤ b) :
  (∫ x in a..b, (f x)*(deriv g x)) = (f b) * (g b) - (f a) * (g a) - (∫ x in a..b, (deriv f x) * (g x)) :=

begin
  have eq1 := ftc (f * g) a b h,
  have eq2 :  (∫ (x : ℝ) in a..b, deriv (f * g) x) =  (∫ (x : ℝ) in a..b, (deriv f x) * g x + f x * (deriv g x)),
  {
    rw interval_integral.integral_of_le h,
    rw interval_integral.integral_of_le h,
    apply congr_arg, ext y,
    apply deriv_mul,
    simp only [],
    exact hf y,
    simp only [],
    exact hg y,
  },
  rw eq2 at eq1,
  rw interval_integral.integral_add at eq1,
  simp only [pi.mul_apply] at eq1 ⊢,
  rw <-eq1, simp only [add_sub_cancel'],
  apply measurable.mul,
  simp only [], exact hf2,
  simp only [], exact hg3,
  rw interval_integrable,
  have H1 : continuous (λ x, (deriv f x) * g x),
  {
    apply continuous.mul _ _, exact normed_ring_top_monoid,
    exact hf4, apply @differentiable.continuous ℝ _ ℝ _ _ ℝ _ _ _,
    exact hg,
  },

  split,
  apply measure_theory.integrable_on.mono_set (continuous.integrable_on_compact (@compact_Icc a b) H1),
  exact set.Ioc_subset_Icc_self,
  exact real.locally_finite_volume,
  apply measure_theory.integrable_on.mono_set (continuous.integrable_on_compact (@compact_Icc a b) H1),
  rw set.Ioc_eq_empty, exact (set.Icc a b).empty_subset, exact h,
  exact real.locally_finite_volume,

  apply measurable.mul, exact hf3, exact hg2,
  rw interval_integrable,
  have H2 : continuous (λ x, f x * deriv g x),
  {
    apply continuous.mul _ _, exact normed_ring_top_monoid,
    apply @differentiable.continuous ℝ _ ℝ _ _ ℝ _ _ _,
    exact hf, exact hg4,
  },
  split,


  apply measure_theory.integrable_on.mono_set (continuous.integrable_on_compact (@compact_Icc a b) H2),
  exact set.Ioc_subset_Icc_self,
  exact real.locally_finite_volume,
  apply measure_theory.integrable_on.mono_set (continuous.integrable_on_compact (@compact_Icc a b) H2),
  rw set.Ioc_eq_empty, exact (set.Icc a b).empty_subset, exact h,
  exact real.locally_finite_volume,

  apply differentiable.mul hf hg,
  apply continuous.measurable,
  {
    have eq1 : deriv (f * g) = (deriv f) * g + f * (deriv g),
      ext, simp only [pi.add_apply, pi.mul_apply],
      change (deriv (λ x, (f x * g x))) x = deriv f x * g x + f x * deriv g x,
    rw deriv_mul,
    simp only [], exact hf x,
    simp only [], exact hg x,
    rw eq1, apply continuous.add _ _,
    exact normed_top_monoid, apply continuous.mul _ _,
    exact normed_ring_top_monoid, exact hf4,
    apply differentiable.continuous hg,
    apply continuous.mul _ _, exact normed_ring_top_monoid,
    apply differentiable.continuous hf, exact hg4,
  },
  {
    have eq1 : deriv (f * g) = (deriv f) * g + f * (deriv g),
      ext, simp only [pi.add_apply, pi.mul_apply],
      change (deriv (λ x, (f x * g x))) x = deriv f x * g x + f x * deriv g x,
    rw deriv_mul,
    simp only [], exact hf x,
    simp only [], exact hg x,
    rw eq1, apply continuous.add _ _,
    exact normed_top_monoid, apply continuous.mul _ _,
    exact normed_ring_top_monoid, exact hf4,
    apply differentiable.continuous hg,
    apply continuous.mul _ _, exact normed_ring_top_monoid,
    apply differentiable.continuous hf, exact hg4,
  },
end

/-Theorem
integrations on a set $S$ of two identical functions are indentical
-/
theorem same_integral {S : set ℝ} (f g : ℝ -> ℝ) : f = g -> (∫ x in S, f x) = ∫ x in S, g x :=
begin
  intro h,
  simp only [],
  exact congr_arg (measure_theory.integral (measure_theory.measure_space.volume.restrict S)) h,
end

/-Theorem
integrations of two identical functions are indentical
-/
theorem same_integral' (f g : ℝ -> ℝ) : f = g -> (∫ x, f x) = ∫ x, g x :=
begin
    exact congr_arg (λ (f : ℝ → ℝ), ∫ (x : ℝ), f x),
end

/-Theorem
identical function have identical derivatives
-/
theorem same_deriv (f g : ℝ -> ℝ) (x : ℝ) : f = g -> deriv f x = deriv g x := λ h, congr_fun (congr_arg deriv h) x

/-Theorem
If forall $x\in(a,b), 0 \le f(x)\le c$ then
$$
\int_a^b f\le (b-a)c
$$
-/
theorem integral_le_max_times_length (f : ℝ -> ℝ) {h1 : measurable f} (a b : ℝ) (h : a ≤ b) (c : ℝ)
    (f_nonneg : ∀ x ∈ set.Icc a b, 0 ≤ f x) (c_max : ∀ x ∈ set.Icc a b, f x ≤ c) :
    (∫ x in a..b, f x) ≤ (b - a) * c :=
begin
    have triv1 : (∫ x in a..b, f x) = ∥(∫ x in a..b, f x)∥,
    {
        rw real.norm_eq_abs,
        rw abs_of_nonneg,
        rw interval_integral.integral_of_le h,
        apply measure_theory.integral_nonneg_of_ae,
        apply (@measure_theory.ae_restrict_iff ℝ _ _ (set.Ioc a b) _ _).2,
        apply measure_theory.ae_of_all,
        intros x hx,
        simp only [and_imp, set.mem_Ioc, pi.zero_apply, ge_iff_le, set.mem_Icc] at *,
        refine f_nonneg x _ _,
        linarith, linarith,
        simp only [pi.zero_apply],
        refine is_measurable_le measurable_zero h1,
    },
    rw triv1,
    have triv2 := @interval_integral.norm_integral_le_of_norm_le_const ℝ _ _ _ _ _ _ a b c f _,

    rw abs_of_nonneg at triv2,
    linarith,
    linarith,
    intros x hx,
    rw real.norm_eq_abs,
    rw abs_of_nonneg,
    have eq1 : min a b = a := min_eq_left h,
    have eq2 : max a b = b := max_eq_right h,
    simp only [set.mem_Ioc, eq1, eq2] at hx ⊢,
    refine c_max x _,
    simp only [set.mem_Icc],
    split, linarith, linarith,
    refine f_nonneg x _,
    have eq1 : min a b = a := min_eq_left h,
    have eq2 : max a b = b := max_eq_right h,
    simp only [eq1, eq2, set.mem_Ioc, set.mem_Icc] at ⊢ hx,
    split, linarith, linarith,
end

/-Theorem
$$
\frac{\mathrm{d}\exp(t-x)}{\mathrm{d}x}=-\exp(t-x)
$$
-/
theorem deriv_exp_t_x (t : ℝ) : deriv (λ x, real.exp (t-x)) = -(λ x, real.exp (t-x)) :=
begin
    have triv : (λ x, real.exp (t-x)) = real.exp ∘ (λ x, t - x) := by simp only [],
    ext,
    rw triv,
    rw deriv.scomp, simp only [neg_mul_eq_neg_mul_symm, deriv_exp, differentiable_at_const, mul_one, algebra.id.smul_eq_mul, one_mul, zero_sub, deriv_sub, differentiable_at_id', pi.neg_apply, deriv_id'', deriv_const'],

    simp only [differentiable_at_id', differentiable_at.exp],
    apply differentiable_at.const_sub,
    exact differentiable_at_id,
end

/-Theorem
$$
\frac{\mathrm{d}-\exp(t-x)}{\mathrm{d}x}=\exp(t-x)
$$
-/
theorem deriv_exp_t_x' (t : ℝ) : (deriv (λ x, - (real.exp (t-x)))) = (λ x, real.exp (t-x)) :=
begin
    simp only [deriv_exp, differentiable_at_const, mul_one, zero_sub, deriv_sub, differentiable_at_id', deriv_id'', deriv.neg', deriv_const', mul_neg_eq_neg_mul_symm, differentiable_at.sub, neg_neg],
end

/--
# about I
-/

/-Definition
Suppose $f$ is an integer polynomial with degree $n$ and $t\ge0$ then define
    \[I(f,t):=\int_0^t \exp(t-x)f(z)\mathrm{d}x\]
We use integration by parts to prove
    \[I(f,t)=\exp(t)\left(\sum_{i=0}^n f^{(i)}(0)\right)-\sum_{i=0}^n f^{(i)}(t)\]

The two different ways of representing $I(f,t)$ we give us upper bound and lower bound when we are using this on transcendence of $e$.
-/
def I (f : ℤ[X]) (t : ℝ) : ℝ :=
    t.exp * (∑ i in finset.range f.nat_degree.succ, (f_eval_on_ℝ (deriv_n f i) 0)) - (∑ i in finset.range f.nat_degree.succ, (f_eval_on_ℝ (deriv_n f i) t))

/--
I equivalent definition
\[I(f,t):=\int_0^t \exp(t-x)f(z)\mathrm{d}x\]
-/
def II (f : ℤ[X]) (t : ℝ) : ℝ := ∫ x in 0..t, real.exp(t - x) * (f_eval_on_ℝ f x)

/-Theorem
$I(0,t)$ is 0.
-/
theorem II_0 (t : ℝ) (ht : 0 ≤ t) : II 0 t = 0 :=
begin
    -- We are integrating $\exp(t-x)\times 0$
    rw II, unfold f_eval_on_ℝ,
    simp only [mul_zero, polynomial.eval_zero, polynomial.map_zero],
    rw interval_integral.integral_of_le ht,
    apply measure_theory.integral_zero,
end

/-Theorem
By integration by part we have:
\[I(f, t) = e^tf(0)-f(t)+I(f',t)\]
-/
lemma II_integrate_by_part (f : ℤ[X]) (t : ℝ) (ht : 0 ≤ t) :
    (II f t) = (real.exp t) * (f_eval_on_ℝ f 0) - (f_eval_on_ℝ f t) + (II f.derivative t) :=
begin
    rw II,
    -- We have $$\int_0^t \exp(t-x)f(x)\mathrm{d}x=\int_0^t f(x)\frac{\mathrm{d}}{\mathrm{d}x}(-\exp(t-x))\mathrm{d}x$$
    have eq : (∫ x in 0..t, (t - x).exp * f_eval_on_ℝ f x) = (∫ x in 0..t, f_eval_on_ℝ f x * (deriv (λ x, - (real.exp (t-x))) x)),
    {
        -- apply congr_arg,
        rw interval_integral.integral_of_le ht,
        rw interval_integral.integral_of_le ht,
        apply same_integral, ext, simp only [deriv_exp_t_x'], ring,
    },
    rw eq,
    -- Apply integration by part to $$\int_0^t f(x)\frac{\mathrm{d}}{\mathrm{d}x}(-\exp(t-x))\mathrm{d}x$$.
    replace eq := integrate_by_part (f_eval_on_ℝ f) (λ (x : ℝ), -(t - x).exp) 0 t ht,
    rw eq,
    simp only [mul_one, neg_sub_neg, real.exp_zero, sub_zero, mul_neg_eq_neg_mul_symm, sub_self],
    replace eq : (∫ x in 0..t, -(deriv (f_eval_on_ℝ f) x * (t - x).exp)) = ∫ x in 0..t, -((λ x, (deriv (f_eval_on_ℝ f) x * (t - x).exp)) x),
    {
        rw interval_integral.integral_of_le ht,
    },
    rw eq, rw interval_integral.integral_neg, simp only [sub_neg_eq_add], rw II,
    replace eq : (∫ (x : ℝ) in 0..t, (t - x).exp * f_eval_on_ℝ f.derivative x) = ∫ (x : ℝ) in 0..t, deriv (f_eval_on_ℝ f) x * (t - x).exp,
    {
        rw interval_integral.integral_of_le ht,
        rw interval_integral.integral_of_le ht,
        apply same_integral, ext, ring, rw f_eval_on_ℝ,
        rw derivative_emb, rw <-polynomial.deriv,
        have triv : deriv (λ (x : ℝ), polynomial.eval x (polynomial.map ℤembℝ f)) x = deriv (f_eval_on_ℝ f) x,
        {
            apply same_deriv, ext, rw f_eval_on_ℝ,
        },
        rw triv, ring,
    }, rw eq, ring,

    apply polynomial.differentiable,
    apply continuous.measurable,
    apply @differentiable.continuous ℝ _ ℝ _ _ ℝ _ _ _ _,
    rw f_eval_on_ℝ_deriv,
    apply polynomial.differentiable,

    apply continuous.measurable,
    apply @differentiable.continuous ℝ _ ℝ _ _ ℝ _ _ _ _,
    apply polynomial.differentiable,

    rw f_eval_on_ℝ_deriv,
    apply @differentiable.continuous ℝ _ ℝ _ _ ℝ _ _ _ _,
    apply polynomial.differentiable,

    apply differentiable.neg,
    change differentiable ℝ (real.exp ∘ (λ (y : ℝ), (t - y))),
    apply differentiable.comp,
    exact real.differentiable_exp,
    have : (λ (y : ℝ), t - y) = (λ (y : ℝ), -(y-t)),
    ext y, rw neg_sub, rw this, apply differentiable.neg,
    apply differentiable.sub_const, exact differentiable_id',

    apply continuous.measurable,
    rw deriv_exp_t_x',
    change continuous (real.exp ∘ (λ (y : ℝ), (t - y))),
    apply continuous.comp (real.continuous_exp) _,
    apply @differentiable.continuous ℝ _ ℝ _ _ ℝ _ _ _ _,
    have : (λ (y : ℝ), t - y) = (λ (y : ℝ), -(y-t)),
    ext y, rw neg_sub, rw this, apply differentiable.neg,
    apply differentiable.sub_const, exact differentiable_id',

    apply continuous.measurable,
    apply continuous.neg _, exact normed_top_group,
    change continuous (real.exp ∘ (λ (y : ℝ), (t - y))),
    apply continuous.comp (real.continuous_exp) _,
    apply @differentiable.continuous ℝ _ ℝ _ _ ℝ _ _ _ _,
    have : (λ (y : ℝ), t - y) = (λ (y : ℝ), -(y-t)),
    ext y, rw neg_sub, rw this, apply differentiable.neg,
    apply differentiable.sub_const, exact differentiable_id',

    rw deriv_exp_t_x',
    change continuous (real.exp ∘ (λ (y : ℝ), (t - y))),
    apply continuous.comp (real.continuous_exp) _,
    apply @differentiable.continuous ℝ _ ℝ _ _ ℝ _ _ _ _,
    have : (λ (y : ℝ), t - y) = (λ (y : ℝ), -(y-t)),
    ext y, rw neg_sub, rw this, apply differentiable.neg,
    apply differentiable.sub_const, exact differentiable_id',
end

/-Theorem
Combine the theorem above with induction we get for all $m\in\mathbb N$
\[
I(f,t)=e^t\sum_{i=0}^m f^{(i)}(0)-\sum_{i=0}^m f^{(i)}(t)
\]
-/
lemma II_integrate_by_part_m (f : ℤ[X]) (t : ℝ) (ht : 0 ≤ t) (m : ℕ) :
    II f t = t.exp * (∑ i in finset.range (m+1), (f_eval_on_ℝ (deriv_n f i) 0)) - (∑ i in finset.range (m+1), f_eval_on_ℝ (deriv_n f i) t) + (II (deriv_n f (m+1)) t) :=
begin
    induction m with m ih,
    rw [deriv_n,II_integrate_by_part], simp only [function.iterate_one, finset.sum_singleton, finset.range_one], rw deriv_n, simpa only [id.def, function.iterate_zero],

    rw [ih, II_integrate_by_part],
    have triv : m.succ + 1 = (m+1).succ := by ring, rw triv, generalize hM : m + 1 = M,
    replace triv : t.exp * ∑ (i : ℕ) in finset.range M, f_eval_on_ℝ (deriv_n f i) 0 -
        ∑ (i : ℕ) in finset.range M, f_eval_on_ℝ (deriv_n f i) t +
      (t.exp * f_eval_on_ℝ (deriv_n f M) 0 - f_eval_on_ℝ (deriv_n f M) t + II (deriv_n f M).derivative t)
      = t.exp * ((∑ (i : ℕ) in finset.range M, f_eval_on_ℝ (deriv_n f i) 0) + (f_eval_on_ℝ (deriv_n f M) 0))
      - ((∑ (i : ℕ) in finset.range M, f_eval_on_ℝ (deriv_n f i) t) + f_eval_on_ℝ (deriv_n f M) t) + II (deriv_n f M).derivative t := by ring,
    rw triv,
    replace triv : ∑ (i : ℕ) in finset.range M, f_eval_on_ℝ (deriv_n f i) 0 + f_eval_on_ℝ (deriv_n f M) 0 = ∑ (i : ℕ) in finset.range M.succ, f_eval_on_ℝ (deriv_n f i) 0,
        rw finset.sum_range_succ, ring,
    rw triv,
    replace triv : (∑ (i : ℕ) in finset.range M, f_eval_on_ℝ (deriv_n f i) t + f_eval_on_ℝ (deriv_n f M) t) = (∑ (i : ℕ) in finset.range M.succ, f_eval_on_ℝ (deriv_n f i) t),
        rw finset.sum_range_succ, ring,
    rw triv,
    replace triv : (deriv_n f M).derivative= (deriv_n f M.succ),
    {
        conv_rhs {rw deriv_n}, rw function.iterate_succ',
        replace triv : (polynomial.derivative ∘ (polynomial.derivative^[M])) f = (polynomial.derivative (polynomial.derivative^[M] f)) := rfl,
        rw triv, rw <-deriv_n,
    }, rwa triv,
end

/-Theorem
So the using if $f$ has degree $n$, then $f^{(n+1)}$ is zero we have the two definition of $I(f,t)$ agrees.
-/
theorem II_eq_I (f : ℤ[X]) (t : ℝ) (ht : 0 ≤ t) : II f t = I f t :=
begin
    have II_integrate_by_part_m := II_integrate_by_part_m f t ht f.nat_degree,
    have triv := deriv_too_much f, rw I,
    rw [triv, II_0, add_zero] at II_integrate_by_part_m;
    assumption,
end

/-Theorem
\[\left|I(f,t)\right|\le \int_0^t \left|e^{t-x}f(x)\right|\mathrm{d}x\]
-/
lemma abs_II_le1 (f : ℤ[X]) (t : ℝ) (ht : 0 ≤ t) : abs (II f t) ≤ ∫ x in 0..t, abs ((t-x).exp * (f_eval_on_ℝ f x)) :=
begin
    have triv : (∫ x in 0..t, abs ((t-x).exp * (f_eval_on_ℝ f x))) = ∫ x in 0..t, ∥(t-x).exp * (f_eval_on_ℝ f x)∥,
    {
        apply congr_arg, refl,
    }, rw triv,

    replace triv : abs (II f t) = ∥ (∫ (x : ℝ) in 0..t, (t - x).exp * f_eval_on_ℝ f x) ∥,
    {
        rw real.norm_eq_abs,
        apply congr_arg,
        unfold II,
    }, rw triv,
    have ineq := @interval_integral.norm_integral_le_abs_integral_norm ℝ ℝ _ _ _ _ _ _ _ _ 0 t (λ x:ℝ, (t-x).exp * f_eval_on_ℝ f x) _,
    rw abs_of_nonneg at ineq,
    refine ineq,
    {
        rw interval_integral.integral_of_le ht,
        apply measure_theory.integral_nonneg_of_ae,
        apply (@measure_theory.ae_restrict_iff ℝ _ _ (set.Ioc 0 t) _ _).2,
        apply measure_theory.ae_of_all,
        intros x hx,
        simp only [normed_field.norm_mul, pi.zero_apply],
        apply mul_nonneg,
        exact norm_nonneg (real.exp (t - x)),
        exact norm_nonneg (f_eval_on_ℝ f x),
        simp only [normed_field.norm_mul, pi.zero_apply],
        apply is_measurable.congr (is_measurable.univ),
        ext, split,
        intros hx, simp only [set.mem_univ, set.mem_set_of_eq] at hx ⊢,
        apply mul_nonneg, exact norm_nonneg _, exact norm_nonneg _,
        simp only [set.mem_univ, forall_true_iff],
    },
end

/-- # $\bar{f}$
- Say $f(T)=a_0+a_1T+a_2T^2+\cdots+a_nT^n$. Then $\bar{f}=|a_0|+|a_1|T+|a_2|T^2+\cdots+|a_n|T^n$
- We proved some theorems about $\bar{f}$
-/

def f_bar (f : ℤ[X]) : ℤ[X] :=
{ support := f.support,
  to_fun  := λ n, abs (f.coeff n),
  mem_support_to_fun := λ n,
    ⟨λ hn, begin
        simp only [abs_eq_zero, ne.def], have h := (f.3 n).1 hn, simp only [ne.def] at h, assumption
     end, λ hn, begin
        simp only [abs_eq_zero, ne.def] at hn, apply (f.3 n).2, simpa only [],
     end⟩}

/-Theorem
By our construction the $n$-th coefficient of $\bar{f}$ is the absolute value of $n$-th coefficient of $f$
-/
theorem bar_coeff (f : ℤ[X]) (n : ℕ) : (f_bar f).coeff n = abs (f.coeff n) :=
begin
    -- true by definition
    dsimp [f_bar], refl,
end

/-Theorem
By our construction, $\bar{f}$ and $f$ has the same support
-/
theorem bar_supp (f : ℤ[X]) : (f_bar f).1 = f.1 :=
begin
    -- true by definition
    dsimp [f_bar], refl,
end

/-Theorem
Since $\bar{f}$ and $f$ has the same support, they have the same degree.
-/
theorem bar_same_deg (f : ℤ[X]) : (f_bar f).nat_degree = f.nat_degree :=
begin
    apply polynomial.nat_degree_eq_of_degree_eq,
    -- degree is defined to be $\sup$ of support. Since support of $\bar{f}$ and $f$ are the same, their degree is the same.
    rw polynomial.degree, rw polynomial.degree, rw bar_supp,
end

/-Theorem
$\bar{0}=0$
-/
theorem f_bar_0 : f_bar 0 = 0 :=
begin
    ext, rw bar_coeff, simp only [abs_zero, polynomial.coeff_zero],
end

/-Theorem
for any $f\in\mathbb Z$, if $\bar{f}=0$ then $f=0$
-/
theorem f_bar_eq_0 (f : ℤ[X]) : f_bar f = 0 -> f = 0 :=
begin
    intro h, rw polynomial.ext_iff at h, ext,
    have hn := h n, simp only [polynomial.coeff_zero] at hn, rw bar_coeff at hn, simp only [abs_eq_zero, polynomial.coeff_zero] at hn ⊢, assumption,
end

private lemma coeff_sum (f : ℕ -> (ℤ[X])) (m : ℕ) (s : finset ℕ) : (∑ i in s, (f i).coeff m) = (∑ i in s, f i).coeff m :=
begin
    apply finset.induction_on s, simp only [finset.sum_empty, polynomial.coeff_zero],
    intros a s ha, simp only [forall_prop_of_true, polynomial.finset_sum_coeff],
end

theorem coeff_f_bar_mul (f g : ℤ[X]) (n : ℕ) : (f_bar (f*g)).coeff n = abs(∑ p in finset.nat.antidiagonal n, (f.coeff p.1)*(g.coeff p.2)) :=
begin
    rw bar_coeff (f*g) n, rw polynomial.coeff_mul,
end

theorem f_bar_eq (f : ℤ[X]) : f_bar f = ∑ i in finset.range f.nat_degree.succ, polynomial.C (abs (f.coeff i)) * polynomial.X^i :=
begin
    ext, rw bar_coeff, rw <-coeff_sum, simp_rw [polynomial.coeff_C_mul_X], simp only [finset.mem_range, finset.sum_ite_eq], split_ifs, refl, simp only [not_lt] at h,
    rw polynomial.coeff_eq_zero_of_nat_degree_lt h, exact rfl,
end

/-Theorem
For any $x\in(0,t)$
$|f(x)|\le \bar{f}(t)$
-/
lemma f_bar_ineq (f : ℤ[X]) (t : ℝ) : ∀ x ∈ set.Icc 0 t, abs (f_eval_on_ℝ f x) ≤ f_eval_on_ℝ (f_bar f) t :=
begin
    intros x hx,
    -- If we write $f(X)=a_0+a_1X+\cdots+a_nX^n$. Then $f(x)=a_0+a_1x+\cdots+a_nx^n$
    have lhs : f_eval_on_ℝ f x = ∑ i in f.support, (f.coeff i : ℝ) * x ^ i,
    {
        rw [f_eval_on_ℝ, polynomial.eval_map, polynomial.eval₂, finsupp.sum],
        apply congr_arg, ext, norm_cast,
    },
    rw lhs,
    -- So $|f(x)|=|a_0+a_1x+\cdots+a_nx^n|\le |a_0|+|a_1|x+\cdots+|a_n|x^n$. (We assumed $x\ge0$).
    have ineq1 : abs (∑ (i : ℕ) in f.support, (f.coeff i:ℝ) * x ^ i) ≤ ∑ i in f.support, (abs (f.coeff i:ℝ) * (x ^ i)),
    {
        -- we have $|a_0+a_1x+\cdots+a_nx^n|\le|a_0|+|a_1x|+\cdots+|a_nx^n|$
        have ineq1' := @finset.abs_sum_le_sum_abs ℝ ℕ _ (λ i, (f.coeff i:ℝ) * (x ^ i)) f.support, simp only [] at ineq1',
        -- and $|a_0|+|a_1x|+\cdots+|a_nx^n|=|a_0|+|a_1|x+\cdots+|a_n|x^n$
        have eq1 : ∑ (x_1 : ℕ) in f.support, abs (↑(f.coeff x_1) * x ^ x_1) = ∑ (x_1 : ℕ) in f.support, abs (↑(f.coeff x_1)) * x ^ x_1,
        {
            apply congr_arg, ext, rw abs_mul,
            rw @abs_of_nonneg ℝ _ (x^x_1) _, apply pow_nonneg, exact (set.mem_Icc.1 hx).1,
        },
        rw eq1 at ineq1', exact ineq1',
    },

    -- $\bar{f}(t)=|a_0|+|a_1|t+\cdots+|a_n|t^n$
    have rhs : f_eval_on_ℝ (f_bar f) t = ∑ i in (f_bar f).support, abs (f.coeff i:ℝ) * t ^ i,
    {
        rw [f_eval_on_ℝ, polynomial.eval_map, polynomial.eval₂, finsupp.sum],
        apply congr_arg, ext, norm_cast,
    },
    rw rhs,

    -- Since $x^i\le t^i$, we have $|a_0|+|a_1|x+\cdots+|a_n|x^n\le|a_0|+|a_1|t+\cdots+|a_n|t^n$
    have ineq2 : ∑ (i : ℕ) in f.support, abs (f.coeff i:ℝ) * x ^ i ≤  ∑ i in (f_bar f).support, abs (f.coeff i:ℝ) * t ^ i,
    {
        rw bar_supp, apply finset.sum_le_sum, intros n hn,
        suffices : x ^ n ≤ t ^ n,
        {
            apply mul_le_mul, exact le_refl (abs ↑(polynomial.coeff f n)), exact this, apply pow_nonneg, exact (set.mem_Icc.1 hx).1, exact abs_nonneg ↑(polynomial.coeff f n),
        },
        apply pow_le_pow_of_le_left, exact (set.mem_Icc.1 hx).1, exact (set.mem_Icc.1 hx).2,
    },
    -- combine `ineq1` and `ineq2` we are done.
    exact le_trans ineq1 ineq2,
end

private lemma continuous_exp_f (f : ℤ[X]) (t : ℝ) (ht : t ≥ 0) : continuous (λ (x : ℝ), abs (real.exp (t - x) * f_eval_on_ℝ f x)) :=
begin
    -- $|e^{t-x}f(x)|$ is composition of absolute value function and $e^{t-x}f(x)$
      have eq1 : (λ (x : ℝ), abs (real.exp (t - x) * f_eval_on_ℝ f x)) = abs ∘ (λ (x : ℝ), (real.exp (t - x) * f_eval_on_ℝ f x)) := by simp only [eq_self_iff_true], rw eq1,
      -- We know that absolute value function is continuous.
      have cont1 := real.continuous_abs,
      -- We now prove that $e^{t-x}f(x)$ is continuous by proving $e^{t-x}$ and $f(x)$ are continuous.
      have cont2 : continuous (λ (x : ℝ), real.exp (t - x) * f_eval_on_ℝ f x),
      {
        -- $e^{t-x}$ is composition of $\exp$ and $t-x$.
        have eq2 : (λ x : ℝ, real.exp (t-x)) = real.exp ∘ (λ x : ℝ, t - x), simp only [],
        have cont21 : continuous (λ x : ℝ, real.exp (t-x)), rw eq2,
        -- $\exp$ is continuous
        have cont20 := real.continuous_exp,
        -- $t-x$ is the constant function $t$ minus the identity function
        have cont201 : continuous (λ (x : ℝ), t - x),
        have eq3 : (λ (x : ℝ), t - x) = (λ (x : ℝ), (λ _, t) x - id x), ext, simp only [id], rw eq3,
        -- constant function is continuous
        have cont3 : continuous (λ _ :ℝ, t), exact continuous_const,
        -- identity function is continuous
        have cont3' : continuous (@id ℝ), exact continuous_id,
        -- hence $t-x$ is continuous
        have cont33 := continuous.sub cont3 cont3', assumption,
        -- hence $e^{t-x}$ is continuous
        exact continuous.comp cont20 cont201,
        -- evaluating a polynomial is continuous
        have cont4 : continuous (λ x , f_eval_on_ℝ f x),
          unfold f_eval_on_ℝ, exact polynomial.continuous (polynomial.map ℤembℝ f),
        -- hence the product is continuous
        exact continuous.mul cont21 cont4,
      },
      exact continuous.comp cont1 cont2,
end

/-Theorem
$$
\int_0^t |e^{t-x}f(d)|\mathrm{d}x\le te^t\bar{f}(t)
$$
-/
private lemma II_le2' (f : ℤ[X]) (t : ℝ) (ht : t ≥ 0) : (∫ x in 0..t, abs ((t-x).exp * (f_eval_on_ℝ f x))) ≤ t * t.exp * (f_eval_on_ℝ (f_bar f) t) :=
begin
    -- we are using `integral_le_max_times_length`
    -- so we need to prove $|e^{t-x}f(x)|\le e^t\bar{f}(t)$
    have ineq1 := integral_le_max_times_length ((λ x, abs ((t - x).exp * f_eval_on_ℝ f x))) 0 t ht (t.exp * f_eval_on_ℝ (f_bar f) t) _ _,
    simp only [sub_zero] at ineq1,
    have triv : t * (t.exp * f_eval_on_ℝ (f_bar f) t) = t * t.exp * f_eval_on_ℝ (f_bar f) t := by ring,
    rw triv at ineq1, exact ineq1,

    -- This to prove the functions we used are measurable and integrable.
    {
      refine continuous.measurable _,
      apply continuous_exp_f _ _ ht,
    },

    -- This is to prove $0\le|e^{t-x}f(x)|$
    {
        intros x hx, simp only [ge_iff_le],
        exact abs_nonneg (real.exp (t - x) * f_eval_on_ℝ f x),
    },

    -- This is to prove $|e^{t-x}f(x)|\le e^t \bar{f}(t)$
    {
        intros x hx, simp only [set.indicator, set.mem_Icc],
        rw abs_mul,
        have triv : abs (t - x).exp = (t-x).exp, {
            apply abs_of_pos, exact (t - x).exp_pos,
        },
        rw triv,
        -- We have $|f(x)|\le\bar{f}(t)$
        have ineq1 := f_bar_ineq f t x hx,
        -- We have $e^{t-x}\le e^{t}$
        have ineq2 : (t - x).exp ≤ t.exp,
        {
            rw real.exp_le_exp, rw sub_le, simp only [sub_self], exact hx.1,
        },
        exact mul_le_mul ineq2 ineq1 (abs_nonneg _) (le_of_lt (real.exp_pos t)),
    },
end

/-Theorem
$$|I(f,t)|\le te^t\bar{f}(t)$$
-/
theorem abs_II_le2 (f : ℤ[X]) (t : ℝ) (ht : 0 ≤ t) : abs (II f t) ≤ t * t.exp * (f_eval_on_ℝ (f_bar f) t) :=
begin
    -- combine `abs_II_le1` and previous lemma.
    have ineq1 := (abs_II_le1 f t ht),
    have ineq2 := (II_le2' f t ht),
    exact le_trans (abs_II_le1 f t ht) (II_le2' f t ht),
end

end e_transcendental_lemmas


-- #lint
