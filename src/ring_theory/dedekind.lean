import ring_theory.dedekind_domain
universes u v

variables (R : Type u) [comm_ring R] {A : Type v} [comm_ring A]
variables (K : Type u) [field K] (R' : Type u) [integral_domain R']
variables [algebra R A]

open function
open_locale big_operators

/-
Chopping block:
-- class discrete_valuation_ring [comm_ring R] : Prop :=
--     (int_domain : is_integral_domain(R))
--     (unique_nonzero_prime : ∃ Q : ideal R,
--     Q ≠ ⊥ → Q.is_prime →  (∀ P : ideal R, P.is_prime → P = ⊥ ∨ P = Q)
--     )
--     (is_pir : is_principal_ideal_ring(R))
-/

--make lemma that the image of P under the local map is that of the unique prime ideal of the local ring
/-
(almost) Need that the localization is another dedekind domain.
In general, noetherian is preserved under localizations, same with Krull dim

https://math.mit.edu/classes/18.785/2017fa/LectureNotes2.pdf

Should prove that `discrete_valuation_ring R ↔ {is_noetherian : _, is_integrally_closed : _, is_one_dim : _, is_local_ring : _`.
most of these things then drop out easily.
-/
lemma dedekind_id_imp_dedekind_dvr [is_dedekind_domain R'] : is_dedekind_domain_dvr R' :=
begin
  refine {is_noetherian_ring := is_dedekind_domain.is_noetherian_ring, is_dvr_at_nonzero_prime := _, not_is_field := is_dedekind_domain.not_is_field},
  intros P hp_nonzero hp_prime,
  letI := hp_prime,
  have f := localization.of (ideal.prime_compl P), --this line fails without the letI
  rw discrete_valuation_ring.iff_pid_with_one_nonzero_prime (localization.at_prime P),
  split, swap,
  { --local Krull dim = 1
    rcases local_ring.maximal_ideal_unique (localization.at_prime P) with ⟨q',hqmax, hq2⟩,
    use q',
    fsplit,
    exact ⟨ by { sorry, } , ideal.is_maximal.is_prime hqmax,⟩,
    rintro Q ⟨nebot, hQ⟩,
    have h1 : Q.is_maximal, sorry,
    apply hq2 Q h1,
  },

  repeat {sorry},
end

example (X : Type*) [comm_ring X] [local_ring X] (I : ideal X) (hI : I.is_maximal): false :=
begin
  rcases local_ring.maximal_ideal_unique X with ⟨p, hpmax, hp⟩,
  simp only [] at hp,
  sorry,
end

/-
lemma dedekind_dvr_imp_dedekind_inv [is_dedekind_domain_dvr R'] : is_dedekind_domain_inv R' :=
begin
    sorry,
end

lemma dedekind_inv_imp_dedekind_id [is_dedekind_domain_inv R'] : is_dedekind_domain R' :=
begin
  sorry,
end

lemma dedekind_id_imp_dedekind_inv [is_dedekind_domain R'] : is_dedekind_domain_inv R' :=
by {have I := dedekind_id_imp_dedekind_dvr R', exact @dedekind_dvr_imp_dedekind_inv R' _ I,}

lemma dedekind_inv_imp_dedekind_dvr [is_dedekind_domain_inv R'] : is_dedekind_domain_dvr R' :=
by {letI := dedekind_inv_imp_dedekind_id R', exact dedekind_id_imp_dedekind_dvr R',}

lemma dedekind_dvr_imp_dedekind_id (f : fraction_map R' $ localization (non_zero_divisors R')) [dedekind_dvr R'] : dedekind_id R' :=
by {letI := dedekind_dvr_imp_dedekind_inv R', exact dedekind_inv_imp_dedekind_id R' f,}
-/


/-
Time to break a lot of things !

probably morally correct: fractional ideals have prime factorization !
(→ regular ideals have prime factorization)

-/


open_locale classical

--make analogous statement for submodules

namespace dedekind

lemma maximal_gt_bot (M : ideal R') (hm : M.is_maximal) (non_field : ∃(I : ideal R'), ⊥ < I ∧ I < ⊤) : ⊥ < M :=
begin
  split, suffices : ⊥ ≤ M, assumption, simp only [bot_le],
  intro mle,
  have : M = ⊥, have h1 : M ≤ ⊥, assumption, have h2 : ⊥ ≤ M, simp only [bot_le], exact le_antisymm h1 h2,
  unfold ideal.is_maximal at hm,
  rcases hm with ⟨ne_top, h1⟩,
  contrapose! h1,
  rcases non_field with ⟨I, ibot, itop⟩,
  use I, rw this at *,
  split, assumption,
  cases itop, contrapose! itop_right, rw itop_right,
  exact le_refl ⊤,
end

lemma top_contains_nonzero_prime (non_field : ∃(I : ideal R'), ⊥ < I ∧ I < ⊤) : ∃(P : ideal R'), P.is_prime ∧ ⊥ < P ∧ P < ⊤ :=
begin
  cases @ideal.exists_maximal R' _ _ with P hp,
  use P,
  split,
  exact ideal.is_maximal.is_prime hp,
  split,
  refine maximal_gt_bot R' P hp non_field,
  unfold ideal.is_maximal at hp,
  rcases hp with ⟨ne_top, pkey⟩,
  exact lt_top_iff_ne_top.mpr ne_top,
end

/-
Suppose not, then the set of ideals that do not contain a product of primes is nonempty, and by set_has_maximal
must have a maximal element M.
Since M is not prime, ∃ (r,s : R-M) such that rs ∈ M.
Since r ∉ M, M+(r) > M, and since M is maximal, M+(r) and M+(s) must be divisible by some prime.
Now observe that (M+(r))(M+(s)) is divisible by some primes, but M*M ⊂ M, rM ⊂ M, sM ⊂ M, and rs ⊂ M, so
this is contained in M, but this is a contradiction.
-/

lemma ideal_contains_prime_product [is_dedekind_domain R'] (I : ideal R') (gt_zero : ⊥ < I) : ∃(pset : multiset $ ideal R'), ∅ < pset ∧ pset.prod ≤ I ∧ (∀(P ∈ pset), ideal.is_prime P ∧ ⊥ < P) :=
begin
  letI : is_noetherian R' R', exact is_dedekind_domain.is_noetherian_ring,
  by_contra hyp,
  push_neg at hyp,
  let A := {J : ideal R' | ∀(qset : multiset $ ideal R'), ∅ < qset → qset.prod ≤ J → (∃ (P : ideal R'), P ∈ qset ∧ (P.is_prime → ¬⊥ < P))},
  have key : A.nonempty,
  {use I, exact hyp },
  rcases set_has_maximal_iff_noetherian.2 _ A key with ⟨M, Mkey, maximal⟩,
  rw set.mem_set_of_eq at Mkey,
  by_cases ne_top : M = ⊤,
  { --basically krull's theorem
    have not_field : ¬ is_field R', exact is_dedekind_domain.not_is_field,
    rcases ring.not_is_field_iff_exists_prime.1 not_field with ⟨P, ne0, hp⟩,
    have netop := hp.1,
    have bot_lt := bot_lt_iff_ne_bot.mpr ne0,
    rw ne_top at *,
    let qs := ({P} : multiset $ ideal R'),
    have h2 : ∅ < qs, exact (∅ : multiset $ ideal R').lt_cons_self P,
    have h3 : qs.prod ≤ ⊤, have blah : qs.prod = P, exact multiset.prod_singleton P, rw blah, exact submodule.comap_subtype_eq_top.mp rfl,
    rcases Mkey qs h2 h3 with ⟨Q, qeq, qkey⟩,
    have blah : Q = P, exact multiset.mem_singleton.1 qeq,
    rw [blah,ne_top] at *,
    apply qkey, assumption', },
  by_cases ne_bot : M = ⊥,
  { have h1 := maximal I, --have that if the maximum of a set of ideals is ⊥, then it only contains ⊥, contra since I < ⊥ and I ∈ A
    have h2 : I ∈ A, simpa,
    rw ne_bot at h1,
    have h4 : ⊥ ≤ I,
    {cases gt_zero, exact gt_zero_left,},
    cases gt_zero,
    have := h1 h2 h4,
    rw this at *, tauto, },
  by_cases non_prime : ideal.is_prime M,
  { have h1 : ({M} : multiset $ ideal R').prod ≤  M,
    suffices h2 : ({M} : multiset $ ideal R').prod = M, rw h2, exact le_refl M,
    exact multiset.prod_singleton M,
    have h3 : ∅ < ({M} : multiset $ ideal R'), exact (∅ : multiset $ ideal R').lt_cons_self M,
    rcases Mkey {M} h3 h1 with ⟨P, hp, hp2⟩,
    have := multiset.mem_singleton.1 hp,
    subst this,
    exact hp2 non_prime (bot_lt_iff_ne_bot.mpr ne_bot) },
  unfold ideal.is_prime at non_prime,
  push_neg at non_prime,
  rcases non_prime ne_top with ⟨r, s, hr, hs, hrs⟩,
  clear' non_prime ne_top,
  set rm := M + ideal.span{r} with hrm,
  set sm := M + ideal.span{s} with hrs,
  have h1 : M < rm ∧ M < sm,
  { split; apply submodule.lt_add_iff_not_mem.2; assumption },
  cases h1 with rgt sgt,
  have main : rm*sm ≤ M,
  { simp only [hrm, hrs, left_distrib, right_distrib],
    repeat {rw ideal.add_eq_sup},
    simp only [ideal.mul_le_left, ideal.mul_le_right, sup_le_iff, true_and],
    have := ideal.span_singleton_mul_span_singleton r s,
    rw this, rw ideal.span_le, exact set.singleton_subset_iff.mpr hr },
  have key1 : rm ∉ A,
  { intro rma,
    cases rgt,
    have h1 := maximal rm rma rgt_left,
    have : rm ≠ M, {exfalso, apply rgt_right, rw h1, simp only [set.le_eq_subset] },
    exact this h1, },
  have key2 : sm ∉ A,
  { intro sma,
    cases sgt,
    have h1 := maximal sm sma sgt_left,
    have : sm ≠ M, {exfalso, apply sgt_right, rw h1, simp only [set.le_eq_subset]},
    exact this h1, },
  rw set.mem_set_of_eq at key1, rw set.mem_set_of_eq at key2,
  push_neg at key1, push_neg at key2,
  rcases key1 with ⟨qs1, qpos1, qle1, qprime1⟩,
  rcases key2 with ⟨qs2, qpos2, qle2, qprime2⟩,
  set qs := qs1 + qs2,
  have h1 : ∅ < qs, exact add_pos qpos1 qpos2,
  have h2 : qs.prod ≤ M, simp only [multiset.prod_add], have h' := submodule.mul_le_mul qle1 qle2, exact le_trans h' main,
  rcases Mkey qs h1 h2 with ⟨P, hp, Pkey⟩,
  have h3 : P.is_prime ∧ ⊥ < P, cases multiset.mem_add.mp hp, exact qprime1 P h, exact qprime2 P h,
  cases h3 with h3 h4,
  exact Pkey h3 h4,
  assumption,
end

/-
For any proper ideal I, there exists an element, γ, in K (the field of fractions of R) such that
γ I ⊂ R.
Proof:
Pick some a ∈ I, then (a) contains a product of primes, and fix P_1, … such that
P_1…P_r ⊂ (a), etc.

broken, not sure how to state it.

lemma frac_mul_ideal_contains_ring [dedekind_id R'] (I : ideal R') (h_nonzero : I ≠ ⊥) (h_nontop : I ≠ ⊤ ) : ∃ (γ : fraction_ring R'), γI ⊂ R :=
begin
  sorry,
end

-/

/-
For any ideal I, there exists J such that IJ is principal.
proof:
Let 0 ≠ α ∈ I, and let J = { β ∈ R : β I ⊂ (α )}.
We can see that J is an ideal.
and we have that IJ ⊂ (α).
Since IJ ⊂ (α), we have that A = IJ/α is an ideal of R.

If A = R, then IJ = (α) and we are done,
otherwise, A is a proper ideal, and we can use frac_mul_ideal_contains_ring
to have a γ ∈ K-R such that γ A ⊂ R. Since R is integrally closed,
it suffices to show that γ is a root of a monic polynomial over R.

We have that J ⊂ A, as α ∈ I. so γ J ⊂ γ A ⊂ R.
We make the observation that γ J ⊂ J.

-/
lemma exists_ideal_prod_principal [is_dedekind_domain R'](I : ideal R') : ∃ (J : ideal R'), (I * J).is_principal ∧ (J ≠ ⊥) :=
begin
  sorry,
end


lemma mem_of_span_mul {a x : R'} {B : ideal R'} (mem : x ∈ submodule.span R' {a} * B) : ∃(r : R'), ∃(b ∈ B), x = r * a * b :=
begin
  sorry,
end

lemma ddk_mul_right_inj [is_dedekind_domain R'] (A B C : ideal R') (A ≠ ⊥ ) : A * B = A * C ↔ B=C :=
begin
  symmetry,
  split,
  {intro, rw a,},
  rcases exists_ideal_prod_principal(R')(A) with ⟨ J ,Jkey, ne_bot⟩,
  intro ab_eq_ac,
  have mul_eq : J * A * B = J * A  * C,
  {rw [mul_assoc, ab_eq_ac,mul_assoc],},
  rcases Jkey.principal with ⟨a, akey⟩,
  rw [mul_comm(J)(A), akey] at mul_eq,
  have h1 : a ≠ 0,
  intro eq_zero,
  have h2 : A * J = ⊥,
  rw eq_zero at *,
  rw submodule.span_singleton_eq_bot.mpr at akey,
  exact akey,
  refl,
  cases ideal.mul_eq_bot.1 h2, exact H h, exact ne_bot h,
  apply le_antisymm; intros x xkey,
  { have h2 : a * x ∈ submodule.span R' {a} * B, have : a ∈ (submodule.span R' {a} : submodule R' R'), exact submodule.mem_span_singleton_self a,
    exact ideal.mul_mem_mul this xkey,
    have h3 : ∃(y ∈ submodule.span R' {a} * B), a * x = y, exact bex.intro (a * x) h2 rfl,
    rcases h3 with ⟨y , yin, yan⟩,
    rw mul_eq at yin,
    rcases mem_of_span_mul R' yin with ⟨r, c, ckey, yeq⟩,
    rw [yeq, mul_comm r a, mul_assoc ] at yan,
    have : x = r * c, exact (@mul_right_inj' _ _ _ x (r*c) h1).mp yan,
    rw this,
    exact ideal.mul_mem_left C ckey, },
  { have h2 : a * x ∈ submodule.span R' {a} * C, have : a ∈ (submodule.span R' {a} : submodule R' R'), exact submodule.mem_span_singleton_self a,
    exact ideal.mul_mem_mul this xkey,
    have h3 : ∃(y ∈ submodule.span R' {a} * C), a * x = y, exact bex.intro (a * x) h2 rfl,
    rcases h3 with ⟨y , yin, yan⟩,
    rw ← mul_eq at yin,
    rcases mem_of_span_mul R' yin with ⟨r, c, ckey, yeq⟩,
    rw [yeq, mul_comm r a, mul_assoc ] at yan,
    have : x = r * c, exact (@mul_right_inj' _ _ _ x (r*c) h1).mp yan,
    rw this,
    exact ideal.mul_mem_left B ckey, },
end

/-
TODO: Refactor ddk_left_inj to be more like mul_left_inj
-/
lemma ddk_left_inj [is_dedekind_domain R'] (A B C : ideal R') ( C ≠ ⊥ ) : A * C = B * C ↔ A = B :=
begin
  rw [mul_comm(A), mul_comm(B)],
  have h1 := ddk_mul_right_inj R' C A B C H, --why does this require so many args?
  exact h1,
end

--This is currently dead wrong
lemma ideal_prime_factorization [is_dedekind_domain R'] (I : ideal R') : ∃ (pset : finset $ ideal R'), ∃(powset : finset $ ℕ ), (finset.card pset = finset.card powset) ∧ (∀(P ∈  pset), ideal.is_prime(P)) ∧ false :=
begin
  sorry,
end

--every ideal is generated by at most two elements of dedekind domain
lemma two_generators [is_dedekind_domain R'] (I : ideal R') : ∃ (a b : R'), I = ideal.span {a,b} :=
begin
  by_cases ⊥ < I,
  tactic.swap,
  {
    have h1 : I = ⊥ ,
    contrapose! h, split, have : ⊥ ≤ I, exact bot_le, exact this, contrapose! h,
    exact le_antisymm h (@bot_le _ _ I),
    use (0 : R'), use (0 : R'), rw h1, simp, },
  cases submodule.nonzero_mem_of_bot_lt h with a ane,
  use a,

  sorry,
end
end dedekind
