import data.nat.totient
import number_theory.quadratic_reciprocity

open_locale classical
open_locale big_operators

section definitions

variable (n : ℕ)

def divisors : finset ℕ :=
finset.filter (λ x : ℕ, x ∣ n) (finset.Ico 1 (n + 1))

def proper_divisors : finset ℕ :=
finset.filter (λ x : ℕ, x ∣ n) (finset.Ico 1 n)

lemma not_proper_self :
¬ n ∈ proper_divisors n :=
begin 
  rw proper_divisors,
  simp,
end

lemma mem_divisors {m : ℕ} : 
n ∈ divisors m ↔ n ∣ m ∧ m ≠ 0:=
begin
  rw divisors,
  simp,
  split,
  { intro hyp, split, exact hyp.right, have h1 := hyp.left, omega },
  { intro hyp, split, swap, exact hyp.left,
    unfold has_dvd.dvd at hyp,
    cases hyp with ex nonzero,
    cases ex with c hc, rw hc,  split,
    { cases n, exfalso, apply nonzero, rw zero_mul at hc, apply hc,
      apply nat.succ_le_succ, apply nat.zero_le },
    {cases c,
    {exfalso, apply nonzero, rw mul_zero at hc, exact hc},
    { have h1 : 1 ≤ c.succ := by { apply nat.succ_le_succ, apply nat.zero_le },
      conv_lhs {rw ← nat.mul_one n}, apply nat.lt_succ_of_le,
      apply nat.mul_le_mul_left, apply h1,
    } } }
end

variable {n}

lemma divisor_le {m : ℕ}:
n ∈ divisors m → n ≤ m :=
begin
  rw divisors, simp only [and_imp, finset.Ico.mem, finset.mem_filter],
  intros a b c, omega,
end

variable (n)

--lemma mem_proper_divisors : sorry := sorry

lemma divisors_eq_proper_divisors_insert_self (posn : 0 < n) :
divisors n = has_insert.insert n (proper_divisors n) :=
begin
  ext,
  rw finset.mem_insert,
  rw divisors,
  rw proper_divisors,
  simp only [finset.Ico.mem, finset.mem_filter],
  split,
  { intro h, cases h,
    by_cases a = n, { left, exact h },
    { right, split, swap, exact h_right, omega } },
  { intro h, cases h,
   {rw h, simp only [nat.succ_pos', and_true, lt_add_iff_pos_right, dvd_refl], omega },
   { split, { have h1 := h.left, omega }, exact h.right } }
end

def sum_divisors : ℕ :=
∑ i in divisors n, i

def sum_proper_divisors : ℕ :=
∑ i in proper_divisors n, i

@[simp]
lemma divisors_0 :
divisors 0 = ∅ :=
begin
  ext, rw mem_divisors, simp,
end

lemma sum_divisors_eq_sum_proper_divisors_add_self :
sum_divisors n = sum_proper_divisors n + n :=
begin
  rw sum_divisors,
  rw sum_proper_divisors,
  by_cases n = 0,
  { rw h,
    have h1 : proper_divisors 0 = ∅, ext, rw proper_divisors, simp,
    rw h1, simp },
  { rw divisors_eq_proper_divisors_insert_self,
    rw finset.sum_insert, rw add_comm,
    apply not_proper_self, omega, }
end

def perfect : Prop :=
sum_proper_divisors n = n

end definitions

section basic_lemmas

lemma perfect_iff_sum_divisors_twice {n : ℕ} :
perfect n ↔ sum_divisors n = 2 * n :=
begin
  rw sum_divisors_eq_sum_proper_divisors_add_self,
  rw perfect, omega,
end

@[simp]
lemma divisors_1 :
divisors 1 = ({1} : finset ℕ) :=
begin
  ext, rw mem_divisors, simp,
end

lemma mem_1_divisors {n : ℕ} (nonzero : n ≠ 0):
1 ∈ divisors n :=
begin
  rw mem_divisors, simp [nonzero],
end

lemma mem_self_divisors {n : ℕ} (nonzero : n ≠ 0):
n ∈ divisors n :=
begin
  rw mem_divisors, simp [nonzero],
end

lemma pos_sum_divisors {n : ℕ} (posn : 0 < n) :
0 < sum_divisors n :=
begin
  unfold sum_divisors,
  have h : ∑ i in divisors n, 0 = 0, rw finset.sum_eq_zero_iff, simp,
  rw ← h,
  apply finset.sum_lt_sum, simp,
  existsi 1, simp only [nat.succ_pos', exists_prop, and_true],
  apply mem_1_divisors, omega
end

@[simp]
lemma divisors_pow_prime {p : ℕ} (pp : p.prime) (k : ℕ)  {x : ℕ} :
x ∈ divisors (p ^ k) ↔  ∃ (j : ℕ) (H : j ≤ k), x = p ^ j :=
begin
  simp only [ne.def, mem_divisors], rw nat.dvd_prime_pow pp,
  split,
  { intro h, cases h, exact h_left },
  { intro h,
    split, exact h,
    { have pos := nat.pos_pow_of_pos k (nat.prime.pos pp), omega } }
end

lemma divisors_pow_prime_insert {p : ℕ} (pp : p.prime) (k : ℕ)  :
divisors (p ^ (k + 1)) = has_insert.insert (p ^ (k + 1)) (divisors (p ^ k)) :=
begin
  ext,
  simp [divisors_pow_prime pp],
  split,
  { intro h, cases h, cases h_h, 
    by_cases h_w = k + 1,
    { left, rw h at h_h_right, exact h_h_right },
    { right, existsi h_w, split, omega, exact h_h_right }
  },
  { intro h, cases h, existsi k + 1, tauto,
    cases h, existsi h_w, split, omega, exact h_h.right }
end

@[simp]
lemma sum_divisors_0 :
sum_divisors 0 = 0 :=
begin
  rw sum_divisors, rw divisors_0, simp,
end

lemma sum_divisors_pow_prime {p : ℕ} (pp : p.prime) (k : ℕ)  :
sum_divisors (p ^ k) * (p - 1)= (p ^ (k + 1) - 1) :=
begin
  rw sum_divisors,
  induction k, simp,
  rw divisors_pow_prime_insert pp,
  rw finset.sum_insert, 
  { rw add_mul, rw k_ih,
    rw nat.pow_succ p (k_n.succ), rw nat.succ_eq_add_one,
    rw ← nat.add_sub_assoc, swap, apply nat.pos_pow_of_pos (k_n + 1) (nat.prime.pos pp),
    refine congr (congr rfl _) rfl,
    have h : (p - 1) + 1 = p := nat.sub_add_cancel (nat.prime.pos pp),
    conv_rhs {rw ← h, rw mul_add, rw h}, simp,
  },
  { intro contra,
    have h := divisor_le contra,
    have g1 :=  nat.mul_lt_mul_of_pos_left (nat.prime.one_lt pp) (nat.pos_pow_of_pos (k_n) (nat.prime.pos pp)),
    rw nat.pow_succ at h, rw mul_one at g1, linarith,
  }
end

lemma sum_divisors_prime {p : ℕ} (pp : p.prime)  :
sum_divisors p = p + 1 :=
begin
  have h1 := sum_divisors_pow_prime pp 1,
  rw nat.pow_one at h1,
  have h2 : (p + 1) * (p - 1) = p ^ 2 - 1,
  {
    rw nat.mul_sub_left_distrib, repeat {rw add_mul},
    rw nat.pow_two, simp only [mul_one, one_mul],
    rw add_comm, rw nat.add_sub_add_left,
  },
  rw ← h2 at h1,
  apply nat.eq_of_mul_eq_mul_right _ h1,
  apply nat.prime.pred_pos pp
end

lemma sum_divisors_pow_2 (k : ℕ) :
sum_divisors (2 ^ k) = (2 ^ (k + 1) - 1) :=
begin
  have h := sum_divisors_pow_prime nat.prime_two k,
  rw mul_one at h,
  apply h,
end

lemma odd_sum_divisors_pow_2 (k : ℕ) :
¬ has_dvd.dvd 2 (sum_divisors (2 ^ k)) :=
begin
  rw sum_divisors_pow_2 k,
  intro contra,
  have h : 2 ∣ 2 ^ (k + 1) - 1 + 1,
  { existsi 2 ^ k,
    rw [← nat.pred_eq_sub_one, ← nat.succ_eq_add_one, nat.succ_pred_eq_of_pos _],
    { rw [mul_comm, nat.pow_succ] },
    apply nat.pos_pow_of_pos, omega,
  },
  rw ← nat.dvd_add_iff_right contra at h,
  have h:= nat.le_of_dvd _ h; linarith,
end

lemma divisors_prime {p : ℕ} (pp : p.prime) :
divisors p = {p, 1} :=
begin
  ext,
  simp only [mem_divisors, ne.def, finset.mem_insert, finset.mem_singleton],
  split,
  { intro h, cases h, rw nat.dvd_prime pp at h_left, tauto },
  { intro h, split, rw or_comm at h, rw ← nat.dvd_prime pp at h, apply h, apply nat.prime.ne_zero pp }
end

lemma card_pair_eq_2 {x y : ℕ} (neq : x ≠ y) :
({x, y} : finset ℕ).card = 2 :=
begin
  rw finset.card_insert_of_not_mem, rw finset.card_singleton, rw finset.mem_singleton, apply neq,
end

lemma prime_iff_two_divisors {n : ℕ} :
n.prime ↔ (divisors n).card = 2 :=
begin
  split,
  { intro np, rw divisors_prime np, apply card_pair_eq_2 (nat.prime.ne_one np),},
  { intro h,
    have ge2 : 2 ≤ n, iterate 2 {cases n, rw ← h, simp }, omega,
    have ex := nat.exists_prime_and_dvd ge2, cases ex with p hp,
    have subs : {n, 1} ⊆ divisors n,
    { rw finset.subset_iff, intro x, simp only [finset.mem_insert, finset.mem_singleton],
      intro h, cases h; rw h_1, apply mem_self_divisors, omega, apply mem_1_divisors, omega },
    have seteq : {n, 1} = divisors n,
    { apply finset.eq_of_subset_of_card_le subs _, rw h, rw card_pair_eq_2 _, omega },
    have pdvd : p ∈ divisors n, rw mem_divisors, split, apply hp.right, omega,
    rw ← seteq at pdvd, simp only [finset.mem_insert, finset.mem_singleton] at pdvd,
    cases pdvd, rw ← pdvd, apply hp.left,
    exfalso, rw pdvd at hp, apply nat.not_prime_one hp.left
  }
end

lemma subset_eq_divisors_of_sum_eq_sum {n : ℕ} (nonzero: n ≠ 0) {s : finset ℕ} (hsub: ∀ (x : ℕ), x ∈ s → x ∣ n) :
s.sum id = sum_divisors n → s = divisors n :=
begin
  have subs : s ⊆ divisors n,
  { rw finset.subset_iff, intros x hx, rw mem_divisors,
    split, apply (hsub x hx), apply nonzero },
  intro h,
  apply finset.subset.antisymm subs _,
  have h' := nat.lt_irrefl (s.sum id),
  contrapose h, rw finset.subset_iff at h, simp only [classical.not_forall, classical.not_imp] at h,
  intro contra, apply h',
  cases h with x hx,
  have posx : 0 < id x,
  { rw id.def, apply nat.pos_of_ne_zero, intro contra, apply nonzero,
    rw contra at hx, apply nat.eq_zero_of_zero_dvd,
    rw mem_divisors at hx, apply hx.left.left },
  have h := finset.sum_lt_sum_of_subset subs (by simpa) posx (by simp),
  rw sum_divisors at contra, simp only [id.def] at h, rw ← contra at h, apply h
end


lemma prime_and_one_of_sum_two_divisors_eq_sum_divisors {x y : ℕ} (nonzero : x ≠ 0) (hneq : x ≠ y) (hdvd : y ∣ x) (hsum : x + y = sum_divisors x) :
x.prime ∧ y = 1 :=
begin
  have hdivs : {x, y} = divisors x,
  {
    apply subset_eq_divisors_of_sum_eq_sum nonzero _,
    { rw ← hsum, apply finset.sum_pair hneq, },
    { intro z, simp only [finset.mem_insert, finset.mem_singleton], intro h,
      cases h; rw h, apply hdvd } },
  have card2 := card_pair_eq_2 hneq, rw hdivs at card2, rw ← prime_iff_two_divisors at card2,
  split, apply card2,
  rw divisors_prime card2 at hdivs,
  have memy : y ∈ ({x, y} : finset ℕ), simp,
  rw hdivs at memy, simp only [finset.mem_insert, finset.mem_singleton] at memy,
  cases memy, exfalso, apply hneq, symmetry, apply memy,
  apply memy
end

lemma coprime_factor_eq_gcd_left {a b m n : ℕ} (cop : m.coprime n) (am : a ∣ m) (bn : b ∣ n):
a = (a * b).gcd m :=
begin
  rw nat.gcd_eq_left_iff_dvd at am,
  conv_lhs {rw ← am}, symmetry,
  apply nat.coprime.gcd_mul_right_cancel a,
  apply nat.coprime.coprime_dvd_left bn cop.symm,
end

lemma sum_divisors_multiplicative (m n : ℕ) :
nat.coprime m n → sum_divisors (m * n) = (sum_divisors m) * (sum_divisors n) :=
begin
  intro cop,
  by_cases m = 0, { rw h, simp }, have mne0 := h,
  by_cases n = 0, { rw h, simp }, have nne0 := h,
  repeat {rw sum_divisors},
  rw finset.sum_mul_sum,
  symmetry,
  apply finset.sum_bij (λ x : ℕ × ℕ, λ (h : x ∈ _), x.fst * x.snd),
  { simp only [prod.forall], intros a b hab, dsimp, simp only [finset.mem_product] at hab,
    repeat {rw mem_divisors at hab}, rw mem_divisors,
    split, apply mul_dvd_mul hab.left.left hab.right.left, 
    intro contra, cases nat.eq_zero_of_mul_eq_zero contra,
    apply hab.left.right h_1, apply hab.right.right h_1 },
  { simp only [prod.forall], intros a b hab, dsimp, simp only [finset.mem_product] at hab },
  { simp only [prod.forall], intros a b c hab h1 h2, 
    dsimp at *, rw finset.mem_product at *, repeat {rw mem_divisors at *},
    ext; dsimp,
    { transitivity (a * b).gcd m,
      { apply coprime_factor_eq_gcd_left cop hab.left.left hab.right.left },
      { rw h2, symmetry, apply coprime_factor_eq_gcd_left cop h1.left.left h1.right.left } },
    { transitivity (b * a).gcd n,
      { apply coprime_factor_eq_gcd_left cop.symm hab.right.left hab.left.left },
      { rw mul_comm, rw h2, rw mul_comm, symmetry,
      apply coprime_factor_eq_gcd_left cop.symm h1.right.left h1.left.left } } },
  { simp only [exists_prop, prod.exists, finset.mem_product],
    intros c hc,
    existsi c.gcd m, existsi c.gcd n, split,
    { split; rw mem_divisors; split, apply nat.gcd_dvd_right _, apply mne0,
      apply nat.gcd_dvd_right _, apply nne0 },
    { rw ← nat.coprime.gcd_mul c cop,
      symmetry, apply nat.gcd_eq_left,
      rw mem_divisors at hc, apply hc.left } }
end

end basic_lemmas

section mersenne_to_perfect

theorem two_le_exponent_of_prime_mersenne {p : ℕ} :
nat.prime (2 ^ p - 1) → 2 ≤ p :=
begin
  intro np,
  cases p,
  { simp only [nat.sub_self, nat.pow_zero] at np,
    exfalso, apply nat.not_prime_zero np },
  cases p, 
  { simp only [nat.succ_sub_succ_eq_sub, nat.sub_zero, nat.pow_one] at np,
    exfalso, apply nat.not_prime_one np },
  omega,
end

/-
theorem prime_exponent_of_prime_mersenne {p : ℕ} :
nat.prime (2 ^ p - 1) → p.prime :=
begin
  intro mp,
  have h2 := two_le_exponent_of_prime_mersenne mp,
  revert mp,
  contrapose,
  intro np,
  have h := nat.exists_dvd_of_not_prime h2 np,
  cases h with m hm,
  let n := p / m, 
  have nm :=  nat.div_mul_cancel hm.left,
  change n * m = p at nm,
  have g := geom_sum_mul_add (2 ^ n - 1) m, simp only [nat.pow_eq_pow] at g,
  have sp : 2 ^ n - 1 + 1 = 2 ^ n,
  { apply nat.succ_pred_eq_of_pos,
    change (2 ^ n) - 0 > 0, simp only [gt_iff_lt, nat.sub_zero],
    apply nat.pos_pow_of_pos, simp },
  rw sp at g,
  rw ← nat.pow_mul n m 2 at g,
  rw nm at g,
  rw ← g,
  simp only [nat.add_succ_sub_one, add_zero],
  apply nat.not_prime_mul,
  { rw geom_series,
    have f : ℕ → ℕ := 1,
    have h1 : ∃ (i : ℕ) (H : i ∈ finset.range m), f i < (2 ^ n) ^ i,
    {
      
      sorry
    },
    transitivity ∑ (i : ℕ) in finset.range m, 1, swap,
    apply finset.sum_lt_sum,
    { intros i hi, conv_lhs {rw ← nat.pow_zero 2},
      rw nat.pow_eq_pow, rw ← nat.pow_mul n i 2,
      apply nat.pow_le_pow_of_le_right; simp },
    { existsi 1, simp only [exists_prop, finset.mem_range],
      split,
      { cases m, have h := nat.eq_zero_of_zero_dvd hm.left, rw h at h2, linarith,
        cases m, have ha := hm.right.left, exfalso, apply ha, refl,
        apply nat.succ_lt_succ, apply nat.succ_pos },
      { conv_lhs {rw ← pow_zero 2}, rw nat.pow_eq_pow, rw pow_one,
        apply nat.pow_lt_pow_of_lt_right, simp,
        by_cases n = 0, rw h at nm, rw ← nm at h2, rw zero_mul at h2, exfalso, linarith,
        have h' :=  nat.eq_or_lt_of_le (nat.zero_le n), cases h',
        {exfalso, rw h' at h, apply h',},
        {apply h'}
      }
    },
    {
      sorry
    }
  },
  {
    sorry
  },
end -/

theorem mersenne_to_perfect (p : ℕ) :
nat.prime (2 ^ p - 1) → perfect ((2 ^ (p - 1)) * (2 ^ p - 1)) :=
begin
  intro mp,
  have hp : 2 ≤ p := two_le_exponent_of_prime_mersenne mp,
  rw perfect_iff_sum_divisors_twice,
  rw sum_divisors_multiplicative,
  {
    rw sum_divisors_pow_2,
    rw sum_divisors_prime (mp),
    have pow_pos : 2^p > 0 := by { have h := nat.prime.pos mp, omega },
    repeat {rw ← nat.pred_eq_sub_one}, -- (2 ^ p),
    repeat {rw ← nat.succ_eq_add_one},
    rw nat.succ_pred_eq_of_pos pow_pos,
    have pps : p.pred.succ = p, apply nat.succ_pred_eq_of_pos, omega,
    rw pps,
    rw ← mul_assoc,
    rw mul_comm,
    refine congr (congr rfl _) rfl,
    rw ← pps,
    rw [nat.pred_succ, nat.pow_succ, mul_comm]
  },
  {
    have h : (2 ^ p - 1) = (2 ^ p - 1) ^ 1 := by simp,
    rw h,
    apply nat.coprime_pow_primes _ _ nat.prime_two mp _,
    apply ne_of_lt,
    rw ← nat.pred_eq_sub_one,
    rw ← nat.pred_succ 2,
    apply nat.pred_lt_pred, omega,
    rw nat.pred_succ 2,
    change 2 ^ 2 ≤ 2 ^ p,
    apply nat.pow_le_pow_of_le_right, omega, apply hp,
  }
end

end mersenne_to_perfect

section fin_mult_and_coprime_part

variables {p n : ℕ} 

lemma finite_multiplicity_nat_of_prime_nonzero (pp : p.prime) (pos : 0 < n):
multiplicity.finite p n :=
begin
  rw multiplicity.finite_nat_iff, split,
  { have h := nat.prime.one_lt pp, omega },
  apply pos,
end

variables (pp : p.prime) (pos : 0 < n)

def fin_mult : ℕ :=
(multiplicity p n).get (finite_multiplicity_nat_of_prime_nonzero pp pos)

lemma lift_fin_mult :
↑(fin_mult pp pos) = multiplicity p n :=
begin
  unfold fin_mult, simp,
end

lemma pow_fin_mult_divides :
p ^ (fin_mult pp pos) ∣ n :=
begin
  rw ← nat.pow_eq_pow,
  apply multiplicity.pow_multiplicity_dvd (finite_multiplicity_nat_of_prime_nonzero pp pos),
end

lemma fin_mult_greatest {m : ℕ} : 
fin_mult pp pos < m → ¬ p ^ m ∣ n :=
begin
  intro h,
  rw ← nat.pow_eq_pow,
  apply multiplicity.is_greatest' (finite_multiplicity_nat_of_prime_nonzero pp pos) h,
end

def coprime_part : ℕ :=
n / (p ^ (fin_mult pp pos))

lemma pow_fin_mult_coprime_part_eq_self :
(coprime_part pp pos) * p ^ (fin_mult pp pos) = n :=
begin
  rw coprime_part,
  rw nat.div_mul_cancel (pow_fin_mult_divides pp pos),
end

lemma not_dvd_coprime_part :
¬ (has_dvd.dvd p (coprime_part pp pos)) :=
begin
  have hlt : (fin_mult pp pos) < (fin_mult pp pos) + 1 := by omega,
  have h := fin_mult_greatest pp pos hlt,
  contrapose h, simp only [classical.not_not] at *,
  rw nat.pow_succ p (fin_mult pp pos),
  rw mul_comm,
  have hself := dvd_refl (p ^ (fin_mult pp pos)),
  have mdm := mul_dvd_mul h hself,
  rw (pow_fin_mult_coprime_part_eq_self pp pos) at mdm,
  apply mdm,
end

lemma coprime_coprime_part :
p.coprime (coprime_part pp pos) :=
begin
  cases nat.coprime_or_dvd_of_prime pp (coprime_part pp pos), apply h,
  exfalso, apply not_dvd_coprime_part pp pos h,
end

lemma coprime_of_prime_not_dvd (pp : p.prime) (h : ¬ p ∣ n) :
n.coprime p :=
begin
  rw ← nat.pow_one p,
  apply nat.prime.coprime_pow_of_not_dvd pp h,
end

lemma dvd_coprime_part_of_coprime_dvd {m : ℕ} (hmn : has_dvd.dvd m n) (hmp : ¬ has_dvd.dvd p m) :
has_dvd.dvd m (coprime_part pp pos) :=
begin
  have h : (p ^ (fin_mult pp pos)).coprime (coprime_part pp pos),
  { apply nat.coprime.symm,
    apply nat.prime.coprime_pow_of_not_dvd pp (not_dvd_coprime_part pp pos) },
  have h1 := nat.coprime.gcd_mul m h,
  rw mul_comm at h1,
  rw (pow_fin_mult_coprime_part_eq_self pp pos) at h1,
  rw nat.gcd_eq_left hmn at h1,
  have h2 : m.coprime (p ^ fin_mult pp pos) := nat.prime.coprime_pow_of_not_dvd pp hmp,
  unfold nat.coprime at h2,
  rw h2 at h1, rw one_mul at h1,
  rw nat.gcd_eq_left_iff_dvd, rw ← h1,
end



end fin_mult_and_coprime_part

section perfect_to_mersenne

theorem even_perfect_to_mersenne {n : ℕ} (even : has_dvd.dvd 2 n) (perf : perfect n) (posn : 0 < n):
∃ (p : ℕ), n = (2 ^ (p - 1)) * (2 ^ p - 1) ∧ nat.prime (2 ^ p - 1) :=
begin
  let k := fin_mult nat.prime_two posn,
  let x := coprime_part nat.prime_two posn,
  have hxk := (pow_fin_mult_coprime_part_eq_self nat.prime_two posn),
  change x * 2 ^ k = n at hxk,
  have posk : 0 < k,
  { by_cases k = 0,
    { rw ← hxk at even, rw h at even, simp only [mul_one, nat.pow_zero] at even,
      exfalso, apply not_dvd_coprime_part nat.prime_two posn even },
    { contrapose h, simp only [le_zero_iff_eq, not_lt] at h, rw classical.not_not, apply h } },
  
  existsi k + 1,
  rw [nat.add_succ_sub_one, add_zero],
  have hiff : n = 2 ^ k * (2 ^ (k + 1) - 1) ↔ 2 * n = 2 * 2 ^ k * (2 ^ (k + 1) - 1),
  { split, intro h, rw h, ring,
  intro h, apply nat.eq_of_mul_eq_mul_left (nat.prime.pos nat.prime_two), rw h, ring },
  rw [hiff, mul_comm 2 (2 ^ k), ← nat.pow_succ 2, nat.succ_eq_add_one],
  
  
  rw perfect_iff_sum_divisors_twice at perf,
  rw ← perf,
  rw ← hxk at perf,
  change sum_divisors (x * 2 ^ k) = 2 * (x * 2 ^ k) at perf,
  rw sum_divisors_multiplicative at perf, swap,
  { apply nat.prime.coprime_pow_of_not_dvd nat.prime_two (not_dvd_coprime_part nat.prime_two posn)},
  symmetry' at perf,

  rw hxk at perf,
  have dvd2n : sum_divisors (2 ^ k) ∣ 2 * n, {existsi (sum_divisors x), rw perf, rw mul_comm},
  have cop2 := coprime_of_prime_not_dvd nat.prime_two (odd_sum_divisors_pow_2 k),
  have dvdn := nat.coprime.dvd_of_dvd_mul_left cop2 dvd2n,
  have dvdx : sum_divisors (2 ^ k) ∣ x := dvd_coprime_part_of_coprime_dvd nat.prime_two posn dvdn (odd_sum_divisors_pow_2 k),
  --have posn2 : 0 < 2 * n := by linarith,
  let y := x / sum_divisors (2 ^ k),
  have ysdpow : y * sum_divisors (2 ^ k) = x := nat.div_mul_cancel dvdx,

  rw ← hxk at perf,
  change 2 * (x * 2 ^ k) = sum_divisors x * sum_divisors (2 ^ k) at perf,
  rw mul_comm at perf,
  rw mul_assoc at perf,
  rw ← nat.pow_succ 2 k at perf,
  rw ← ysdpow at perf,
  rw mul_comm at perf,
  rw ← mul_assoc at perf,
  have h := (nat.eq_of_mul_eq_mul_right _) perf, swap,
  {rw gt_iff_lt, apply pos_sum_divisors (nat.pos_pow_of_pos k (nat.prime.pos nat.prime_two))},
  rw ysdpow at *,

  have xnonzero : x ≠ 0, 
  { assume contra, rw ← hxk at posn, rw contra at posn, rw zero_mul at posn, linarith },
  have xneqy : x ≠ y,
  { symmetry, rw ← ysdpow, rw sum_divisors_pow_2, rw ← mul_one y, rw mul_assoc, rw one_mul,
    intro contra, have h := nat.eq_of_mul_eq_mul_left _ contra,
    { have h'' := nat.le_succ_of_pred_le (nat.le_of_eq h.symm),
      have h' := nat.pow_lt_pow_of_lt_right (by omega : 2 > 1) posk,
      change 2 ^ k * 2 ≤ 2 * 1 at h'', rw mul_comm at h'',
      have h3 :=  nat.le_of_mul_le_mul_left h'' (nat.prime.pos nat.prime_two),
      rw nat.pow_zero at h', linarith },
    { by_cases y = 0, swap, apply nat.pos_of_ne_zero h,
      rw h at ysdpow, rw zero_mul at ysdpow, rw ← ysdpow at hxk, rw zero_mul at hxk,
      exfalso, rw hxk at posn, linarith } },
  have hxy : x.prime ∧ y = 1,
  { apply prime_and_one_of_sum_two_divisors_eq_sum_divisors xnonzero xneqy _, swap,
    { existsi sum_divisors (2 ^ k), rw ysdpow },
    rw [← h, ← ysdpow, sum_divisors_pow_2],
    have powpos : 2 ^ k.succ > 0, apply nat.pos_pow_of_pos, linarith,
    symmetry, rw ← nat.succ_pred_eq_of_pos powpos, rw nat.succ_eq_add_one, rw add_mul,
    simp only [nat.add_succ_sub_one, add_zero, one_mul, add_left_inj], rw mul_comm },

  have xeq : x = sum_divisors (2 ^ k), rw ← ysdpow, rw hxy.right, simp,
  have xp : x.prime := hxy.left,

  split, swap, rw sum_divisors_pow_2 at xeq, rw ← xeq, apply xp,
  rw ← (pow_fin_mult_coprime_part_eq_self nat.prime_two posn),
  rw sum_divisors_multiplicative, swap,
  { apply nat.prime.coprime_pow_of_not_dvd nat.prime_two (not_dvd_coprime_part nat.prime_two posn)},
  rw [sum_divisors_prime xp, xeq, sum_divisors_pow_2],
  refine congr (congr rfl _) rfl,
  apply nat.succ_pred_eq_of_pos, simp only [nat.nat_zero_eq_zero, gt_iff_lt],
  apply nat.pos_pow_of_pos (k + 1) (nat.prime.pos nat.prime_two)
end

end perfect_to_mersenne

section perfect_iff_mersenne

theorem even_perfect_iff_mersenne {n : ℕ} (posn: 0 < n):
2 ∣ n ∧ perfect n ↔ ∃ (p : ℕ), n = (2 ^ (p - 1)) * (2 ^ p - 1) ∧ nat.prime (2 ^ p - 1) :=
begin
  split, intro even_perf, exact even_perfect_to_mersenne even_perf.left even_perf.right posn,
  intro h, cases h with p hp, rw hp.left, split, swap, apply mersenne_to_perfect p hp.right,
  rw nat.prime.dvd_mul nat.prime_two, left,
  rw nat.dvd_prime_pow nat.prime_two, existsi 1,
  simp only [exists_prop, and_true, eq_self_iff_true, nat.pow_one],
  have gt2 := two_le_exponent_of_prime_mersenne hp.right, omega
end

end perfect_iff_mersenne