/-
import algebra.direct_sum
import algebra.group.units
import algebra.module.basic
import algebra.ring.basic
--import algebraic_geometry.open
--import algebraic_geometry.prime_spectrum
import data.equiv.ring
import data.fintype.basic
--import data.matrix.basic
import data.polynomial.degree.basic
import data.polynomial.div
import field_theory.minimal_polynomial
import linear_algebra.char_poly
import ring_theory.ideal.basic
import ring_theory.polynomial.basic
import ring_theory.principal_ideal_domain
import tactic

open ideal
open polynomial
--open prime_spectrum
--open set
open function finsupp finset

local attribute [instance] classical.prop_decidable
-/

import tactic
import data.polynomial.degree.basic
import logic.function.basic
import algebra.big_operators.basic


open_locale big_operators
open_locale classical

open function polynomial finsupp finset

namespace reverse

variables {R : Type*} [semiring R] {f : polynomial R}

lemma finset_of_bounded {S : set ℕ} (N : ℕ) {nN : ∀ (n ∈ S), n ≤ N} : S.finite :=
set.finite.subset (set.finite_le_nat N) nN

lemma le_degree_of_mem_supp (a : ℕ) :
  a ∈ f.support → a ≤ nat_degree f :=
begin
  rw mem_support_iff_coeff_ne_zero,
  exact le_nat_degree_of_ne_zero,
end

def rev_at (N : ℕ) : ℕ → ℕ := λ (i : ℕ), (N - i) + i * min 1 (i - N)

@[simp] lemma rev_at_small {N n : ℕ} (H : n ≤ N) : rev_at N n = N-n :=
begin
--  sorry,
--/-
  unfold rev_at,
  rw [nat.sub_eq_zero_of_le H, min_eq_right (nat.zero_le 1), mul_zero, add_zero],
--/
end

@[simp] lemma rev_at_large {N n : ℕ} (H : N < n) : rev_at N n = n :=
begin
--  sorry,
--/-
  unfold rev_at,
  rw [min_eq_left, mul_one, nat.sub_eq_zero_of_le (le_of_lt H), zero_add],
  rw [nat.one_succ_zero, nat.succ_le_iff],
  exact nat.sub_pos_of_lt H,
--/
end

@[simp] lemma rev_at_invol {N n : ℕ} : (rev_at N (rev_at N n)) = n :=
begin
  by_cases n ≤ N,
    { rw [rev_at_small h, rev_at_small (nat.sub_le N n), nat.sub_sub_self h], },
    { push_neg at h,
      repeat {rw rev_at_large h}, },
end


@[simp] lemma rev_support :
  {a : ℕ | ∃ b ∈ f.support , a = rev_at (nat_degree f) b}.finite :=
begin
  apply finset_of_bounded (nat_degree f),
  rintros n ⟨rn, rnsupp, rfl⟩,
  rw [rev_at_small (by exact le_degree_of_mem_supp rn rnsupp)],
  exact (nat_degree f).sub_le rn,
end

def at_infty {N : ℕ} (H : nat_degree f ≤ N) : polynomial R :=
⟨((rev_at N) '' ↑(f.support)).to_finset, (λ (i : ℕ), f.coeff (rev_at N i)), begin
  intros a,
  split,
  { rw set.mem_to_finset,
    intro,
    rcases a_1 with ⟨ b , bsupp , rfl⟩,
    rwa [rev_at_invol, ← mem_support_iff_coeff_ne_zero], },
  { intro h,
    rw ← @rev_at_invol N a,
    apply set.mem_to_finset.mpr,
    apply set.mem_image_of_mem,
    exact mem_support_iff_coeff_ne_zero.mpr h, },
end⟩

/-
lemma finfin : ∀ (S : finset ℕ) , {pp : ℕ | ∃ q ∈ S, pp = q}.finite :=
begin
  intro,
  by_cases (S.nonempty),
    { let M : ℕ := finset.max' S h,
      refine finset_of_bounded (finset.max' S h),
      intros n nH,
      apply finset.le_max',
      finish, },
      { have Sne : S=∅,{tidy,apply h,use a,exact a_1, },
      finish,},
end
-/

lemma nonempty_of_card_nonzero {α : Type*} {s : finset α} : s.card ≠ 0 → s.nonempty := 
begin
  contrapose,
  push_neg,
  rw [nonempty_iff_ne_empty, not_not, card_eq_zero, imp_self],
  exact trivial,
end

lemma card_two_d {sup : finset ℕ} : 2 ≤ sup.card → finset.min' sup (begin
  apply nonempty_of_card_nonzero,linarith,
end) ≠ finset.max' sup (begin
  apply nonempty_of_card_nonzero,linarith,
end) :=
begin
  intro,
  apply ne_of_lt,
  apply finset.min'_lt_max'_of_card,
  exact nat.succ_le_iff.mp a,
end

lemma card_two (sup : finset ℕ) {H : 2 ≤ sup.card} : finset.min' sup ≠ finset.max' sup :=
mt (λ h, congr_fun h _) (ne_of_lt (finset.min'_lt_max'_of_card sup H))


lemma nat2 {N : ℕ} : N ≠ 0 ∧ N ≠ 1 → 2 ≤ N :=
begin
--    sorry,
--/-
--  omega,
  intro,
  cases a with a0 a1,
  refine lt_of_le_of_ne _ (ne.symm a1),
  exact lt_of_le_of_ne (zero_le N) (ne.symm a0),
--/
end

lemma leading_coeff_nonzero_of_nonzero : f ≠ 0 ↔ leading_coeff f ≠ 0 :=
begin
--    sorry,
--/-
  exact not_congr leading_coeff_eq_zero.symm,
--/
end

--#check zero_divisor

def inj_mul (x : R) := ∀ ⦃a b : R⦄ , x*a=x*b → a=b

/-
lemma xy {a b c : R} (H : inj_mul a) : a*b=a*c → b=c :=
begin
  exact H,
end

lemma xxv {RR : Type*} [integral_domain RR] {x y z : RR} {h : x ≠ 0} : x*y=x*z → y=z := mul_left_cancel' h
-/



lemma non_zero_of_nonempty_support : f.1.nonempty → f ≠ 0 :=
begin
--    sorry,
--/-
  intro,
  cases a with N Nhip,
  rw mem_support_iff_coeff_ne_zero at Nhip,
  finish,
--/
end

lemma nonempty_support_of_non_zero : f ≠ 0 → f.1.nonempty :=
begin
--    sorry,
--/-
  intro fne,
  rw nonempty_iff_ne_empty,
  apply ne_empty_of_mem,
  rw mem_support_iff_coeff_ne_zero,
  exact leading_coeff_nonzero_of_nonzero.mp fne,
--/
end

lemma non_zero_iff : f.1.nonempty ↔ f ≠ 0 :=
begin
--  sorry,
--/-
  split,
    { exact non_zero_of_nonempty_support, },
    { exact nonempty_support_of_non_zero, },
--/
end

lemma zero_iff : ¬ f.1.nonempty ↔ f = 0 :=
begin
  rw not_congr,
    { exact not_not, },
    { exact non_zero_iff, },
end


--#print prefix polynomial

--#check f.3



/-
lemma le_degree_of_mem_supp : ∀ a : ℕ , a ∈ f.1 → a ≤ nat_degree f :=
begin
--    sorry,
/-
    intros a,
    contrapose,
    push_neg,
    intros ah,
    rw (f.3 a),
    push_neg,
    apply coeff_eq_zero_of_nat_degree_lt,
    exact ah,
--/
end
-/

lemma not_mem_support_of_gt_degree : ∀ a : ℕ , nat_degree f < a → a ∉ f.1 :=
begin
--    sorry,
--/-
  intros a a_1 a_2,
  rw finsupp.mem_support_iff at a_2,
  apply a_2 (coeff_eq_zero_of_nat_degree_lt a_1),
--/
end


namespace trade

def trailing_degree {R : Type*} [semiring R] (p : polynomial R) : with_top ℕ := p.support.inf some

lemma trailing_degree_lt_wf : well_founded (λp q : polynomial R, trailing_degree p < trailing_degree q) :=
inv_image.wf trailing_degree (with_top.well_founded_lt nat.lt_wf)


def nat_trailing_degree {R : Type*} [semiring R] (p : polynomial R) : ℕ := (trailing_degree p).get_or_else 0
def trailing_coeff {R : Type*} [semiring R] (f : polynomial R) : R := f.coeff (nat_trailing_degree f)

@[simp] lemma trailing_degree_zero {R : Type*} [semiring R] : trailing_degree (0 : polynomial R) = ⊤ := rfl

@[simp] lemma nat_trailing_degree_zero {R : Type*} [semiring R] : nat_trailing_degree (0 : polynomial R) = 0 := rfl

lemma trailing_degree_eq_top {R : Type*} [semiring R] {p : polynomial R} : trailing_degree p = ⊤ ↔ p = 0 :=
⟨λ h, by rw [trailing_degree, ← min_eq_inf_with_top] at h;
  exact support_eq_empty.1 (min_eq_none.1 h),
λ h, h.symm ▸ rfl⟩

lemma trailing_degree_eq_nat_trailing_degree {R : Type*} [semiring R] {p : polynomial R} (hp : p ≠ 0) : trailing_degree p = (nat_trailing_degree p : with_top ℕ) :=
let ⟨n, hn⟩ :=
  not_forall.1 (mt option.eq_none_iff_forall_not_mem.2 (mt trailing_degree_eq_top.1 hp)) in
have hn : trailing_degree p = some n := not_not.1 hn,
by rw [nat_trailing_degree, hn]; refl

lemma le_trailing_degree_of_ne_zero {n : ℕ} (h : f.coeff n ≠ 0) : trailing_degree f ≤ n :=
show @has_le.le (with_top ℕ) _ (f.support.inf some : with_top ℕ) (some n : with_top ℕ),
from finset.inf_le (finsupp.mem_support_iff.2 h)

lemma nat_trailing_degree_le_of_ne_zero {n : ℕ} (h : f.coeff n ≠ 0) : nat_trailing_degree f ≤ n :=
begin
  rw [← with_top.coe_le_coe, ← trailing_degree_eq_nat_trailing_degree],
  exact le_trailing_degree_of_ne_zero h,
  { assume h, subst h, exact h rfl }
end

lemma nat_trailing_degree_le_of_mem_supp (a : ℕ) :
  a ∈ f.support → nat_trailing_degree f ≤ a:=
begin
  rw mem_support_iff_coeff_ne_zero,
  exact nat_trailing_degree_le_of_ne_zero,
end


@[simp] lemma trailing_coeff_zero : trailing_coeff (0 : polynomial R) = 0 := rfl

@[simp] lemma trailing_coeff_eq_zero : trailing_coeff f = 0 ↔ f = 0 :=
⟨λ h, by_contradiction $ λ hp, mt mem_support_iff.1
  (not_not.2 h) (mem_of_min (trailing_degree_eq_nat_trailing_degree hp)),
λ h, h.symm ▸ leading_coeff_zero⟩

lemma trailing_coeff_eq_zero_iff_deg_eq_top : trailing_coeff f = 0 ↔ trailing_degree f = ⊤ :=
by rw [trailing_coeff_eq_zero, trailing_degree_eq_top]



lemma trailing_coeff_nonzero_of_nonzero : f ≠ 0 ↔ trailing_coeff f ≠ 0 :=
begin
--    sorry,
--/-
  apply not_congr trailing_coeff_eq_zero.symm,
--/
end


def rev_at (N : ℕ) : ℕ → ℕ := λ i : ℕ , (N-i) + i*min 1 (i-N)



@[simp] lemma rev_at_small {N n : ℕ} (H : n ≤ N) : rev_at N n = N-n :=
begin
--  sorry,
--/-
  unfold rev_at,
  rw [nat.sub_eq_zero_of_le H, min_eq_right (nat.zero_le 1), mul_zero, add_zero],
--/
end

@[simp] lemma rev_at_large {N n : ℕ} (H : N < n) : rev_at N n = n :=
begin
--  sorry,
--/-
  unfold rev_at,
  rw [min_eq_left, mul_one, nat.sub_eq_zero_of_le (le_of_lt H), zero_add],
  rw [nat.one_succ_zero, nat.succ_le_iff],
  exact nat.sub_pos_of_lt H,
--/
end

@[simp] lemma rev_at_invol {N n : ℕ} : rev_at N (rev_at N n) = n :=
begin
  unfold rev_at,
  by_cases n ≤ N,
  { 
    simp [nat.sub_eq_zero_of_le (nat.sub_le N n),nat.sub_eq_zero_of_le h, nat.sub_sub_self h], },
  { rw not_le at h,
    simp [nat.sub_eq_zero_of_le (le_of_lt (h)), min_eq_left (nat.succ_le_of_lt (nat.sub_pos_of_lt h))], },
end



/-
@[simp] lemma rev_at_invol {N : ℕ} : involutive (rev_at N) :=
begin
  intro i,
  unfold rev_at,
  by_cases i ≤ N,
  { simp [nat.sub_eq_zero_of_le (nat.sub_le N i),nat.sub_eq_zero_of_le h, nat.sub_sub_self h], },
  { rw not_le at h,
    simp [nat.sub_eq_zero_of_le (le_of_lt (h)), min_eq_left (nat.succ_le_of_lt (nat.sub_pos_of_lt h))], },
end
-/

def rev_support (f : polynomial R) : set ℕ := {a : ℕ | ∃ aa ∈ f.1 , a = rev_at (nat_degree f) aa}


--variables f : polynomial R
--variables {R : Type*} [comm_ring R] 
--#check f.trade.trailing_degree

def shift_support (f : polynomial R) (n : ℕ) 
--{hn : (n : with_top ℕ) ≤ trailing_degree p}
 : set ℕ := {a : ℕ | ∃ aa ∈ f.support , a = aa - n}

--#check shift_support f 100

lemma rev_support_finite (f : polynomial R) : (rev_support f).finite :=
begin
--    sorry,
--/-
  refine finset_of_bounded (nat_degree f),
  intros n nH,
  rcases nH with ⟨ rn , r1 , rfl ⟩ ,
  rw (rev_at_small (le_degree_of_mem_supp rn r1)),
  apply (nat_degree f).sub_le rn,
--/
end

--#exit



def reflect : ℕ → polynomial R → polynomial R := λ N : ℕ , λ p : polynomial R , ⟨ (rev_at N '' ↑(p.support)).to_finset , λ i : ℕ , p.coeff (rev_at N i) , begin
  simp_rw [set.mem_to_finset, set.mem_image, mem_coe, mem_support_iff],
  intro,
  split,
    { intro a_1,
      rcases a_1 with ⟨ a , ha , rfl⟩,
      rwa rev_at_invol, },
    { intro,
      use (rev_at N a),
      rwa [rev_at_invol, eq_self_iff_true, and_true], },
end ⟩

def reverse : polynomial R → polynomial R := λ f , reflect f.nat_degree f

--#exit

def at_infty : polynomial R → polynomial R := reverse
--noncomputable def at_infty {R : Type*} [semiring R] : polynomial R → polynomial R := λ p : polynomial R , ⟨ (rev_at (nat_degree p) '' ↑(p.support)).to_finset , λ i : ℕ , p.2 (rev_at (nat_degree p) i) , by tidy ⟩
/-  at_infty è la versione che continua a funzionare.  at_inftyv era quella con cui ho scritto i lemmi successivi
noncomputable def at_infty {R : Type*} [semiring R] : polynomial R → polynomial R := λ p : polynomial R , ⟨ (rev_at (nat_degree p) '' ↑(p.support)).to_finset , λ i : ℕ , p.2 (rev_at (nat_degree p) i) , by tidy ⟩
-/

/-
noncomputable def at_inftyv {R : Type*} [semiring R] : polynomial R → polynomial R := λ p : polynomial R , begin
  refine ⟨ (rev_support_finite p).to_finset , λ i : ℕ , p.2 (rev_at (nat_degree p) i) , _ ⟩,
--members
  tidy,
    {apply a_1_h_w,rw a_1_h_h at a_2,rw ← a_2,apply congr_arg p.2,symmetry,exact rev_invol,},
    {symmetry,exact rev_invol,},
end
-/

@[simp] lemma at_infty_zero : at_infty (0 : polynomial R) = 0 :=
begin
  refl,
end

lemma reversal_coeff_small {a : ℕ} {H : a ≤ nat_degree f}: f.coeff (nat_degree f - a) = (at_infty f).coeff a :=
begin
--  sorry,
--/-
  rw ← (rev_at_small H),
  refl,
---/
end

lemma reversal_coeff_small' {a : ℕ} {H : a ≤ nat_degree f}: f.coeff a = (at_infty f).coeff (nat_degree f - a) :=
begin
--  sorry,
--/-
  rwa [← @rev_at_invol f.nat_degree a, rev_at_small H, rev_at_small _, reversal_coeff_small, nat.sub_sub_self _];
    { exact (nat_degree f).sub_le a, },
---/
end

lemma coeff_eq_zero_of_not_mem_support {a : ℕ} : a ∉ f.support → f.coeff a = 0 :=
begin
--  sorry,
--/-
  contrapose,
  push_neg,
  exact mem_support_iff_coeff_ne_zero.mpr,
--/
end


lemma reversal_coeff_large {a : ℕ} (H : nat_degree f < a) : (at_infty f).coeff a = 0 :=
begin
--  sorry,
--/-
  apply not_mem_support_iff.mp,
  rw [rev_at_large H],
  exact not_mem_support_of_gt_degree a H,
end



lemma supp_at_infty_of_supp {a : ℕ} : a ∈ (at_infty f).support ↔ rev_at (nat_degree f) a ∈ f.support :=
begin
  split;
    { intro,
      finish, },
end

lemma supp_at_infty_of_supp' {a : ℕ} : rev_at (nat_degree f) a ∈ (at_infty f).support ↔ a ∈ f.support :=
begin
  split,
    { --have : rev_at (nat_degree f) (rev_at f.nat_degree a) = a, by rw rev_at_invol,
      rw ← @rev_at_invol f.nat_degree a,
      intro,
--      rw ← rev_at_invol,
      apply (@supp_at_infty_of_supp R _ f (rev_at f.nat_degree a)).mp,
      convert a_1,
      exact rev_at_invol.symm, },
    { have : rev_at (nat_degree f) (rev_at f.nat_degree a) = a, by exact rev_at_invol,
      rw ← this,
      intro,
      rw rev_at_invol,
      apply (@supp_at_infty_of_supp R _ f (rev_at f.nat_degree a)).mpr a_1, },
end


lemma defs_by_Johann_trailing {R : Type*} [semiring R] {f : polynomial R} (h : f ≠ 0) :
  nat_trailing_degree f = f.support.min' (non_zero_iff.mpr h) :=
begin
  apply le_antisymm,
  { apply le_min',
    intros y hy,
    exact nat_trailing_degree_le_of_mem_supp y hy },
  { apply finset.min'_le,
    rw mem_support_iff_coeff_ne_zero,
    exact trailing_coeff_nonzero_of_nonzero.mp h, },
end


lemma defs_by_Johann {R : Type*} [semiring R] {f : polynomial R} (h : f ≠ 0) :
  f.nat_degree = f.support.max' (non_zero_iff.mpr h) :=
begin
  apply le_antisymm,
  { apply finset.le_max',
    rw mem_support_iff_coeff_ne_zero,
    exact leading_coeff_nonzero_of_nonzero.mp h, },
  { apply max'_le,
    intros y hy,
    exact le_degree_of_mem_supp y hy, }
end


lemma defs_by_Johann_support {R : Type*} [semiring R] {f : polynomial R} (h : f.support.nonempty) :
  f.nat_degree = f.support.max' h :=
begin
  apply le_antisymm,
  { apply finset.le_max',
    rw finsupp.mem_support_iff,
    show f.leading_coeff ≠ 0,
    rw [ne.def, polynomial.leading_coeff_eq_zero],
    rwa [finset.nonempty_iff_ne_empty, ne.def, finsupp.support_eq_empty] at h, },
  { apply polynomial.le_nat_degree_of_ne_zero,
    have := finset.max'_mem _ h,
    rwa finsupp.mem_support_iff at this, }
end

lemma defs_with_Johann {h : f.support.nonempty} : nat_trailing_degree f = f.support.min' h :=
begin
  apply le_antisymm,
  { apply nat_trailing_degree_le_of_ne_zero,
    have := finset.min'_mem _ h,
    rwa finsupp.mem_support_iff at this, },
  { apply min'_le,
    rw finsupp.mem_support_iff,
    show trailing_coeff f ≠ 0,
    rw [ne.def, trailing_coeff_eq_zero],
    rwa [finset.nonempty_iff_ne_empty, ne.def, finsupp.support_eq_empty] at h, },
end

lemma coeff_zero_of_le_trailing_degree : ∀ n : ℕ , n < nat_trailing_degree f → coeff f n = 0 :=
begin
  by_cases fne : f.support.nonempty,
    { intros n nh,
      have : nat_trailing_degree f = f.support.min' fne, by refine defs_with_Johann,
      have : n < f.support.min' fne,
        { rwa ← this, },
      have : n ∉ f.support,
      intro,
      have fsupplt : f.support.min' fne ≤ n,
        { apply min'_le,assumption, },
        exact nat.lt_le_antisymm this fsupplt,
      finish,},
    { intros n nh,
      apply (coeff_eq_zero_of_not_mem_support),
      intro,
      apply fne,
      use n,
      assumption, },
end

lemma finset.min'_mem_min {α : Type} [decidable_linear_order α] {s : finset α} (hs : s.nonempty) :
  s.min' hs ∈ s.min :=
--by rw [option.mem_def, finset.min', option.some_get]
--/-
begin
  -- Unfold the definition of ∈ for options
  rw option.mem_def,
  -- Unfold the definition of min'
  rw finset.min',
  -- some (option.get ↥(s.min.is_some)) is just s.min
  rw option.some_get,
end
--/

lemma at_infty_zero_iff : at_infty f = 0 ↔ f = 0 :=
begin
  split,
    { intro,
      ext1,
      have : ∀ n : ℕ, coeff (at_infty f) n = 0,
        rw a,
        exact coeff_zero,
        rw coeff_zero,
      by_cases h: n ≤ nat_degree f,
        { rw reversal_coeff_small',
          { exact this (f.nat_degree - n), },
          { assumption, }, },
        { apply coeff_eq_zero_of_nat_degree_lt,
          exact not_le.mp h, }, },
    { intro,
      convert at_infty_zero, },
end

lemma at_infty_nonzero_iff : at_infty f ≠ 0 ↔ f ≠ 0 :=
begin
  split;
    { contrapose,
      push_neg,
      rw at_infty_zero_iff,
      exact congr_arg (λ {f : polynomial R}, f), },
end


lemma supp_low_high {a : ℕ} : a ∈ f.support → nat_trailing_degree f ≤ a ∧ a ≤ nat_degree f :=
begin
  by_cases h : f = 0,
    { rw h,
      intro a,
      solve_by_elim, },
    { intro,
      have fne : f.support.nonempty, exact (non_zero_iff).mpr h,
      split,
        { apply min_le_of_mem a_1,
          rw @defs_with_Johann R _ f fne,
          exact finset.min'_mem_min fne, },
        { exact le_degree_of_mem_supp a a_1, }, },
end

lemma prova {s : finset ℕ} {e : ℕ} (he : e ∈ s) : s.nonempty :=
begin
  exact nonempty_iff_ne_empty.mpr (ne_empty_of_mem he),
end

lemma finset.mem_rev_max_min {s : finset ℕ} {e : ℕ} (he : e ∈ s) {hs : s.nonempty} : rev_at (max' s hs) e ≤  (max' s hs) - (min' s hs) :=
begin
  have emax : e ≤ s.max' hs, by apply le_max' s e he,
  rw rev_at_small emax,
  have inint : (s.max' hs - e : int) ≤ s.max' hs - s.min' hs,
    norm_num,
    exact min'_le s e he,
  have minmax : s.min' hs ≤ s.max' hs,
    apply le_max' s (s.min' hs) (min'_mem s hs),
  refine int.coe_nat_le.mp _,
  convert inint,
    { exact int.coe_nat_sub emax, },
    { exact int.coe_nat_sub minmax, },
end

lemma finset.mem_rev_max {s : finset ℕ} {e : ℕ} {he : e ∈ s} {hs : s.nonempty} : rev_at (max' s hs) e ≤  (max' s hs) :=
begin
  exact le_trans (finset.mem_rev_max_min he) ((max' s hs).sub_le (min' s hs)),
end

lemma rev_at_le {N n : ℕ} : n ≤ N → rev_at N n ≤ N :=
begin
  intro,
  rw rev_at_small a,
  exact nat.sub_le N n,
end

lemma rev_at_le_iff {N n : ℕ} : n ≤ N ↔ rev_at N n ≤ N :=
begin
  split,
    { exact rev_at_le, },
    { intro,
      convert @rev_at_le N (rev_at N n) a,
      rw rev_at_invol, },
end

lemma supp_high_high {a : ℕ} : a ∈ (at_infty f).support → a ≤ nat_degree f :=
begin
  intro,
  rw supp_at_infty_of_supp at a_1,
  rw rev_at_le_iff,
  exact le_degree_of_mem_supp (rev_at (nat_degree f) a) a_1,
end

lemma supp_high_low {a : ℕ} : a ∈ (at_infty f).support → a ≤ nat_degree f - nat_trailing_degree f :=
begin
  intro,
  rw supp_at_infty_of_supp at a_1,
  rw [defs_by_Johann, defs_with_Johann],
    { 
      rw ← (@rev_at_invol _ a),
      apply finset.mem_rev_max_min,
      rwa ← defs_by_Johann, },
  rw ← non_zero_iff,
  exact prova a_1,
end


lemma nat_degree_mem_support_of_nonzero : f ≠ 0 → f.nat_degree ∈ f.support :=
begin
  intro,
  apply (f.3 f.nat_degree).mpr,
  exact leading_coeff_nonzero_of_nonzero.mp a,
end



lemma nat_trailing_degree_mem_support_of_nonzero : f ≠ 0 → nat_trailing_degree f ∈ f.support :=
begin
  intro,
  apply (f.3 (nat_trailing_degree f)).mpr,
  exact trailing_coeff_nonzero_of_nonzero.mp a,
end

lemma inf_le_sup {α : Type*} [decidable_linear_order α] {s : finset α} (hs : s.nonempty) : (min' s hs) ≤ (max' s hs) :=
begin
  apply min'_le,
  exact max'_mem s hs,
end

lemma nat_trailing_degree_le_nat_degree : nat_trailing_degree f ≤ nat_degree f :=
begin
  by_cases H : f.support.nonempty,
    { rw [defs_by_Johann (non_zero_iff.mp H),defs_with_Johann],
        exact inf_le_sup H, },
    { rw zero_iff at H,
      rw [H, nat_degree_zero, nat_trailing_degree_zero], },
end

lemma coeff_eq_zero_of_trailing_degree_lt {n : ℕ} (h : (n : with_top ℕ) < trailing_degree f) : coeff f n = 0 :=
not_not.1 (mt le_trailing_degree_of_ne_zero (not_le_of_gt h))

lemma coeff_eq_zero_of_lt_nat_trailing_degree {p : polynomial R} {n : ℕ} (h : n < nat_trailing_degree p) :
  p.coeff n = 0 :=
begin
  apply coeff_eq_zero_of_trailing_degree_lt,
  by_cases hp : p = 0,
  { subst hp, exact with_top.coe_lt_top n, },
  { rwa [trailing_degree_eq_nat_trailing_degree hp, with_top.coe_lt_coe] },
end

theorem le_trailing_degree_C_mul_X_pow (r : R) (n : ℕ) : (n : with_top ℕ) ≤ trailing_degree (C r * X^n) :=
begin
  rw [← single_eq_C_mul_X],
  refine finset.le_inf (λ b hb, _),
  rw list.eq_of_mem_singleton (finsupp.support_single_subset hb),
  exact le_refl _,
end




theorem le_nat_trailing_degree_C_mul_X_pow (n : ℕ) (H : f ≠ 0) : n ≤ nat_trailing_degree (f * X^n) :=
begin
  rw defs_by_Johann_trailing,
  apply le_min',
  intros y,
  rw [mem_support_iff_coeff_ne_zero],
  contrapose!,
  intro,
  apply coeff_eq_zero_of_lt_nat_trailing_degree,
  


  rw [← single_eq_C_mul_X],
  refine finset.le_inf (λ b hb, _),
  rw list.eq_of_mem_singleton (finsupp.support_single_subset hb),
  exact le_refl _,
end



lemma degree_at_infty_eq : (at_infty f).nat_degree = f.nat_degree - nat_trailing_degree f :=
begin
  by_cases H : f = 0,
    { rw [H, at_infty_zero, nat_degree_zero, nat_trailing_degree_zero], },
    { have on_mem : ∀ (a : ℕ) , a ∈ (at_infty f).support → a ≤ nat_degree f - nat_trailing_degree f,
      { intro,
        exact supp_high_low, },
      apply le_antisymm,
        { apply supp_high_low,
          apply nat_degree_mem_support_of_nonzero,
          exact ((at_infty_nonzero_iff).mpr H), },
        { have : (f.nat_degree - nat_trailing_degree f) ∈ (at_infty f).support,
            { rw supp_at_infty_of_supp,
              rw rev_at_small,
                { rw nat.sub_sub_self,
                    { exact nat_trailing_degree_mem_support_of_nonzero H, },
                    { exact nat_trailing_degree_le_nat_degree, }, },
          { exact (nat_degree f).sub_le (nat_trailing_degree f), }, },
          apply le_degree_of_mem_supp,
          exact this, }, },
end

lemma lead_trail_coeff : (at_infty f).coeff (at_infty f).nat_degree = f.coeff (nat_trailing_degree f) :=
begin
  rw [degree_at_infty_eq, ← reversal_coeff_small'],
  exact nat_trailing_degree_le_nat_degree,
end

@[simp] lemma reflect_invol {N : ℕ} : reflect N (reflect N f) = f :=
begin
  ext1,
  unfold reflect,
  simp only [coeff_mk, rev_at_invol],
end


lemma co_mul_X : (f*X).coeff (f.nat_degree+1) = (f).coeff f.nat_degree :=
begin
  exact coeff_mul_X f (nat_degree f),
end

lemma nonzero_coeff : f ≠ 0 → ∃ n : ℕ , f.coeff n ≠ 0 :=
begin
  intro,
  use f.nat_degree,
  apply leading_coeff_nonzero_of_nonzero.mp a,
end

lemma coeff_nonzero : (∃ n : ℕ , f.coeff n ≠ 0) → f ≠ 0 :=
begin
  finish,
end

lemma nonzero_coeff_iff : f ≠ 0 ↔ ∃ n : ℕ , f.coeff n ≠ 0 :=
begin
  split,
    { exact nonzero_coeff, },
    { exact coeff_nonzero, },
end

lemma zero_coeff_iff : f = 0 ↔ ∀ n : ℕ , f.coeff n = 0 :=
begin
  split,
    { finish, },
    { intro,
      ext1,
      apply a n, },
end

lemma mul_X_nonzero_iff : f ≠ 0 ↔ f*X ≠ 0 :=
begin
  split,
    { intros a b,
      apply a,
      rw zero_coeff_iff,
      intro,
      rw [← coeff_mul_X, b],
      refl, },
    { intros a b,
      apply a,
      rw [b, zero_mul], },
end

lemma non_empty_iff_mul_X_nonzero : f.support.nonempty ↔ f*X ≠ 0 :=
begin
  split,
    { intro,
      rw ← mul_X_nonzero_iff,
      exact non_zero_iff.mp a, },
    { intro,
      rw non_zero_iff,
      exact left_ne_zero_of_mul a, },
end




def shift_by : ℕ → ℕ → ℕ := λ n , λ i , n+i

@[simp] lemma shift_small {N a : ℕ} (H : a ≤ N) : shift_by a (N - a) = N :=
begin
  unfold shift_by,
  rw [add_comm, nat.sub_add_cancel H],
end

lemma shift_by_monotone (i : ℕ) : monotone (shift_by i) :=
begin
  intros m n hmn,
  exact add_le_add_left hmn i,
end

@[simp] lemma mul_X_mem_support {n : ℕ} : n.succ ∈ (f*X).support ↔ n ∈ f.support :=
begin
  repeat {rw mem_support_iff_coeff_ne_zero},
  rw coeff_mul_X,
end

@[simp] lemma mul_X_mem_support_shift {n : ℕ} : shift_by 1 n ∈ (f*X).support ↔ n ∈ f.support :=
begin
  unfold shift_by,
  rw [add_comm, ← nat.succ_eq_add_one, mul_X_mem_support],
end

@[simp] lemma nonzero_of_mem_support_mul_X {n : ℕ} : n ∈ (f*X).support → 1 ≤ n :=
begin
  intro a,
  suffices : n ≠ 0, by omega,
  intro n0,
  rw [n0,mem_support_iff] at a,
  apply a,
  exact coeff_mul_X_zero f,
end

@[simp] lemma mul_X_mem_support_shift' {n : ℕ} : n ∈ (f*X).support ↔ 1 ≤ n ∧ (n-1) ∈ f.support :=
begin
  split,
    { intro,
      split,
        { apply nonzero_of_mem_support_mul_X a, },
        { rwa [← mul_X_mem_support_shift, shift_small (nonzero_of_mem_support_mul_X a)], }, },
    { intro,
      cases a with inen npsup,
      convert mul_X_mem_support_shift.mpr npsup,
      exact (shift_small inen).symm, },
end


lemma mul_X_support : (f*X).support = ((shift_by 1) '' ↑(f.support)).to_finset :=
begin
  ext1,
  rw [mul_X_mem_support_shift', set.mem_to_finset],
  split,
    { intro,
      rw [← coe_image, ← shift_small a_1.left],
      exact (mem_image_of_mem (shift_by 1) a_1.right), },
    {
      intro,
      rw set.mem_image at a_1,
      rcases a_1 with ⟨ a_1 , ha_1 , rfl ⟩,
      split,
        { exact nat.le.intro rfl, },
        { convert ha_1,
          exact norm_num.sub_nat_pos (1 + a_1) 1 a_1 rfl, },
    },
end


lemma mem_in_union_set {α : Type*} {s t : set α} (x : α) : x ∈ t → x ∈ (s ∪ t) :=
set.mem_union_right s

lemma mem_in_union {α : Type*} {s t : finset α} (x : α) : x ∈ t → x ∈ (s ∪ t) :=
mem_union_right s

lemma mem_in_union_singleton {α : Type*} {s : finset α} (x : α) : x ∈ (s ∪ {x}) :=
begin
  apply mem_in_union x,
  rw mem_singleton,
end

lemma nonempty_of_mem_singleton {α : Type*} {s : finset α} (x : α) : (s ∪ {x}).nonempty :=
begin
  apply nonempty_of_ne_empty,
  apply ne_empty_of_mem,
  rw [mem_union, mem_singleton],
  right,
  refl,
end

/-
lemma nonempty_of_mem {s : finset ℕ} (x : ℕ) : (s ∪ {x}).nonempty :=
begin
  convert (nonempty_of_mem_singleton x),
end

lemma mem_in_union_nd {s : finset ℕ} (x : ℕ) : x ∈ s ∪ {x} :=
begin
  rw mem_union,
  right,
  rw mem_singleton,
end

lemma nonempty_of_mem_nd {s : finset ℕ} (x : ℕ) : (s ∪ {x}).nonempty :=
begin
  apply nonempty_of_ne_empty,
  apply ne_empty_of_mem,
  exact mem_in_union_nd x,
end
-/

lemma fin {α : Type*} [decidable_linear_order α] {s : finset α} (x : α) : s ⊆ {x} → finset.max' (s ∪ {x} ) (by exact nonempty_of_mem_singleton x) = x :=
begin
  rw ← union_eq_right_iff_subset,
  intro,
  convert max'_singleton x,
end

lemma finN {s : finset ℕ} (x : ℕ) : s ⊆ {x} → finset.max' (s ∪ {x} ) (by convert nonempty_of_mem_singleton x) = x :=
begin
  rw ← union_eq_right_iff_subset,
  intro,
  convert max'_singleton x,
end

--lemma finz {s : finset ℕ} : s ⊆ {0} → finset.max' (s ∪ {0} ) (by convert nonempty_of_mem_singleton 0) = 0 :=
lemma finz {s : finset ℕ} : s ⊆ {0} → finset.max' (s ∪ {0} ) (by convert nonempty_of_mem_singleton 0) = 0 :=
begin
  exact finN 0,
end

lemma nonempty_union_of_nonempty {α : Type*} [decidable_linear_order α] {s t : finset α} (hs : s.nonempty) (ht : t.nonempty) : (s ∪ t).nonempty :=
begin
  cases hs,
  use hs_w,
  exact mem_union_left t hs_h,
end


@[simp] lemma max'_union_eq_right_of_le {α : Type*} [decidable_linear_order α]
 {s t : finset α} {hs : s.nonempty} {ht : t.nonempty}
 (hst : finset.max' s hs ≤ finset.max' t ht) :
 finset.max' (s ∪ t) (nonempty_union_of_nonempty hs ht) = finset.max' t ht :=
begin
  apply le_antisymm,
    { apply max'_le,
      intros a ha,
      rw mem_union at ha,
      cases ha,
        { exact le_trans (le_max' s a ha) hst, },
        { exact le_max' t a ha, }, },
    { apply le_max',
      apply mem_union_right,
      exact max'_mem t ht, },
end


@[simp] lemma max'_union_eq_left_of_le {α : Type*} [decidable_linear_order α] {s t : finset α} {hs : s.nonempty} {ht : t.nonempty}
 (hst : finset.max' t ht ≤ finset.max' s hs) :
 finset.max' (s ∪ t) (nonempty_union_of_nonempty hs ht) = finset.max' s hs :=
begin
  simp_rw finset.union_comm s t,
  exact max'_union_eq_right_of_le hst,
end

lemma max'_union {α : Type*} [decidable_linear_order α] (s t : finset α) {hs : s.nonempty} {ht : t.nonempty}
 : finset.max' (s ∪ t) (nonempty_union_of_nonempty hs ht) = max (finset.max' s hs) (finset.max' t ht) :=
begin
  by_cases h : (finset.max' s hs) ≤ (finset.max' t ht),
    { rw [max_eq_right h, max'_union_eq_right_of_le h], },
    { rw not_le at h,
      rw [max_eq_left (le_of_lt h), max'_union_eq_left_of_le (le_of_lt h)], },
end

--#exit

lemma finsu {α : Type*} [decidable_linear_order α] (s : finset α) {hs : s.nonempty} (x : α) : x ≤ finset.max' s hs → finset.max' (s ∪ {x} ) (nonempty_of_mem_singleton x) = finset.max' s hs :=
begin
  intro,
  rw [max'_union, max_eq_left],
  refine a,
  exact (singleton_nonempty x),
end

lemma finsu0 (s : finset ℕ) {hs : s.nonempty} :
 finset.max' (s ∪ {0} ) (by convert nonempty_union_of_nonempty hs (singleton_nonempty 0))
= finset.max' s hs :=
begin
  convert (finsu s 0) (zero_le (max' s hs)),
end

lemma nat_degree_eq_max : nat_degree f = finset.max' (f.1 ∪ {0}) (by convert nonempty_of_mem_singleton 0) :=
begin
  by_cases h : f = 0,
    { rw h,
      refl, },
    { rw finsu0 f.support,
        { refine defs_by_Johann h, }, },
end


lemma monotone.map_max' {α : Type*} {β : Type*} [decidable_linear_order α] [decidable_linear_order β]
{f : α → β} {a : finset α} {ha : a.nonempty} : monotone f → finset.max' (f '' ↑a).to_finset (begin
  convert (nonempty.image ha) f,
  simp_rw [← coe_image],
  ext1,
  rw set.mem_to_finset,
  refl,
end) =
f (finset.max' a ha) :=
begin
  intro,
  apply le_antisymm,
    { apply max'_le,
      intros y hy,
      rw set.mem_to_finset at hy,
      rcases hy with ⟨ x , hx, rfl⟩,
      exact a_1 (le_max' a x hx), },
    { apply le_max',
      rw set.mem_to_finset,
      rw set.mem_image,
      use (a.max' ha),
      refine ⟨ max'_mem a ha , rfl ⟩, },
end



lemma mem_support_monomial {R : Type*} [semiring R] {n a : ℕ} :
  a ∈ (X ^ n : polynomial R).support → a = n :=
begin
  intro,
  rw [mem_support_iff_coeff_ne_zero, coeff_X_pow n a] at a_1,
  finish,
end  

lemma support_monomial {R : Type*} [semiring R] {n : ℕ} :
  (X ^ n : polynomial R).support ⊆ singleton n :=
begin
  intros a,
  rw mem_singleton,
  exact mem_support_monomial,
end

lemma mem_support_term {n a : ℕ} {c : R} : a ∈ (C c * X ^ n).support → a = n :=
begin
  intro,
  rw [mem_support_iff_coeff_ne_zero, coeff_C_mul_X c n a] at a_1,
  finish,
end

lemma support_term {n : ℕ} {c : R} : (C c * X ^ n).support ⊆ singleton n :=
begin
  intro a,
  rw mem_singleton,
  exact mem_support_term,
end


lemma support_term_nonzero {n : ℕ} {c : R} (h : c ≠ 0): (C c * X ^ n).support = singleton n :=
begin
  ext1,
  rw mem_singleton,
  split,
    { exact mem_support_term, },
    { intro,
      rwa [mem_support_iff_coeff_ne_zero, ne.def, a_1, coeff_C_mul, coeff_X_pow_self n, mul_one], },
end

@[simp] lemma nat_degree_mul_X_eq_shift {f : polynomial R} (a : f ≠ (0 : polynomial R)) : (f*(X : polynomial R)).nat_degree = ((shift_by 1) '' ↑(f.support)).to_finset.max' (begin
  rw ← non_zero_iff at a,
  convert (nonempty.image a (shift_by 1)),
  ext1,
  rw [set.mem_to_finset, ← coe_image],
  refl,
end) :=
begin
  rwa defs_by_Johann,
  simp_rw mul_X_support,
  exact mul_X_nonzero_iff.mp a,
end

@[simp] lemma nat_degree_mul_X {f : polynomial R} (a : f ≠ (0 : polynomial R)) : (f*(X : polynomial R)).nat_degree = (f).nat_degree+1 :=
begin
  have : f.nat_degree +1 = shift_by 1 f.nat_degree, by exact add_comm (nat_degree f) 1,
  rw this,
  rw defs_by_Johann a,
  rw defs_by_Johann (mul_X_nonzero_iff.mp a),
  simp_rw mul_X_support,
  convert (@monotone.map_max' ℕ ℕ _ _ (shift_by 1) f.support (non_zero_iff.mpr a)) (shift_by_monotone 1),
end

--#exit

--#check as_sum
/-
lemma X_comm (a : ℕ) : (X : polynomial R)^a * X = X^(a+1) :=
begin
  rw pow_succ,
  exact pow_mul_comm' X a,
end

lemma mul_X_coeff : ∀ (n : ℕ) , (f*X).coeff (n+1) = f.coeff n :=
begin
  intro,
  rw coeff_mul_X,
end
-/


@[simp] lemma reflect_term (N n : ℕ) {c : R} : reflect N (C c * X ^ n) = C c * X ^ (rev_at N n) :=
begin
  ext1,
  unfold reflect,
  rw coeff_mk,
  by_cases h : rev_at N n = n_1,
    { rw [h, coeff_C_mul, coeff_C_mul, coeff_X_pow_self, ← h, rev_at_invol, coeff_X_pow_self], },
    { rw coeff_eq_zero_of_not_mem_support,
        { symmetry,
          apply coeff_eq_zero_of_not_mem_support,
          intro,
          apply h,
          exact (mem_support_term a).symm, },
        { 
          intro,
          apply h,
          rw ← @rev_at_invol N n_1,
          apply congr_arg _,
          exact (mem_support_term a).symm, }, },
end

@[simp] lemma reflect_monomial (N : ℕ) {n : ℕ} : reflect N (X ^ n : polynomial R) = X ^ (rev_at N n) :=
begin
  rw [← one_mul (X^n), ← C_1, ← one_mul (X^(rev_at N n)), reflect_term, C_1],
end


@[simp] lemma reflect_mul_term {N n : ℕ} {H : f.nat_degree ≤ N } : reflect (N+n) (f * X ^ n) = reflect N f :=
begin
  by_cases f0 : f = 0,
    { rw [f0, zero_mul],
      refl, },
    { ext1,
      unfold reflect,
      dsimp,
      by_cases n1small : n_1 ≤ N,
        { rw [rev_at_small (le_add_right n1small), rev_at_small n1small, nat.sub_add_comm n1small,coeff_mul_X_pow], },
        {
          rw not_le at n1small,
          rw [rev_at_large n1small, coeff_eq_zero_of_nat_degree_lt (gt_of_gt_of_ge n1small H)],
          by_cases n1medium : n_1 ≤ N + n,
            rw rev_at_small n1medium,
            rw coeff_eq_zero_of_lt_nat_trailing_degree,
            rw defs_by_Johann_trailing _,
            have : n ≤ (f * X ^ n).support.min' sorry,
              apply le_trailing_degree_C_mul_X_pow,
              
            rw nat.sub_add_comm _,
            rw coeff_mul_X_pow,
          sorry,
        },}
end


#exit

@[simp] lemma reflect_mul_term {N n : ℕ} {H : n + f.nat_degree ≤ N } : reflect N (f * X ^ n) = reflect (N-n) f :=
begin
  ext1,
  unfold reflect,
  dsimp,
  by_cases n1small : n_1 < n,
    rw rev_at_small,
      {
        
        sorry,
      },
    { refine le_trans _ H,
      apply le_of_lt (nat.lt_add_right n_1 n (nat_degree f) n1small), },
  rw coeff_mul_X_pow f n (rev_at N n_1),
  by_cases h : rev_at N n = n_1,
    { rw [h, coeff_C_mul, coeff_C_mul, coeff_X_pow_self, ← h, rev_at_invol, coeff_X_pow_self], },
    { rw coeff_eq_zero_of_not_mem_support,
        { symmetry,
          apply coeff_eq_zero_of_not_mem_support,
          intro,
          apply h,
          exact (mem_support_term a).symm, },
        { 
          intro,
          apply h,
          rw ← @rev_at_invol N n_1,
          apply congr_arg _,
          exact (mem_support_term a).symm, }, },
end








@[simp] lemma nat_degree_term {n : ℕ} {c : R} {hc : c ≠ 0} : (C c * X^n : polynomial R).nat_degree = n :=
begin
  have : nontrivial R := nontrivial_of_ne c 0 hc,
  rw nat_degree_mul',
    {
      rw [nat_degree_C, zero_add, nat_degree_pow', @nat_degree_X _ _ this, mul_one],
      rw [leading_coeff_X, one_pow],
      intro,
      apply hc,
      rw [← mul_one c, a, mul_zero],
    },
    { rwa [leading_coeff_C, leading_coeff_X_pow n, mul_one], },
end

@[simp] lemma nat_degree_monomial {n : ℕ} {h : (1:R) ≠ 0} : (X^n : polynomial R).nat_degree = n :=
begin
  rwa [← one_mul (X^n), ← C_1, nat_degree_term],
end

@[simp] lemma reverse_term {n : ℕ} {c : R} : reverse (C c * X ^ n) = C c :=
begin
  unfold reverse,
  simp,
  by_cases c0 : c = 0,
    { rw [c0, C_0, zero_mul], },
    { conv_rhs {rw ← mul_one (C c)},
      apply congr_arg _,
      convert pow_zero X,
      rw ← @rev_at_invol (C c * X ^ n).nat_degree 0,
      apply congr_arg,
      rw [rev_at_small (zero_le _), nat.sub_zero, (nat_degree_mul'), nat_degree_C, zero_add],
        { rw nat_degree_monomial,
          intro,
          apply c0,
          exact eq_of_zero_eq_one (eq.symm a) c 0, },
        { rwa [leading_coeff_C c, leading_coeff_X_pow n, mul_one], }, },
end


@[simp] lemma revrev_X_monomial {n : ℕ} {c : R} : reverse (X*((C c)*X^n)) = reverse ((C c)*X^n) :=
begin
  rw [X_mul, mul_assoc, ← X_mul, ← pow_succ],
  simp,
end


lemma xx {n : ℕ} : ¬ ((-1 : int) = n) ↔ (-1 : int) ≠ n :=
begin
  exact iff.rfl,
end

lemma xy {a b : ℕ} {h : b = 0} : a+b=a :=
begin
  omega,
end



lemma nonzero_or_of_nonzero_sum {a b : R} : a+b ≠ 0 → a ≠ 0 ∨ b ≠ 0 :=
begin
  contrapose,
  push_neg,
  intro,
  cases a_1 with a0 b0,
  rw [a0, b0, add_zero],
end


@[simp] lemma support_union {f g : polynomial R} {y : ℕ} : y ∈ support (f+g) → y ∈ support f ∪ support g :=
begin
  rw [mem_support_iff_coeff_ne_zero, coeff_add, mem_union, mem_support_iff_coeff_ne_zero,  mem_support_iff_coeff_ne_zero],
  exact nonzero_or_of_nonzero_sum,
end

lemma split_sum {ι : Type*} {s t : finset ι} (hst : disjoint s t) {f : ι → polynomial R} : (∑ (i : ι) in s, f i) + (∑ (i : ι) in t, f i) = (∑ (i : ι) in s ∪ t, (f i)) :=
begin
  rw sum_union hst,
end


--def invert_coeff (a : ℕ) : polynomial R →+ R := λ p : polynomial R , begin
--  use p.coeff a,
--end

lemma shave_mem {α : Type*} {a : α} {s : finset α} : a ∈ s → s = singleton a ∪ (s \ singleton a) ∧ disjoint (singleton a) (s \ singleton a) :=
begin
  intro,
  split,
    { rwa [union_sdiff_self_eq_union, right_eq_union_iff_subset, singleton_subset_iff], },
    { rw [singleton_disjoint, mem_sdiff],
      push_neg,
      intro,
      exact mem_singleton.mpr rfl, },
end

noncomputable def remove_leading_coefficient (f : polynomial R) : polynomial R := (∑ (i : ℕ) in finset.range f.nat_degree, (C (f.coeff i)) * X^i)

@[simp] lemma support_remove_leading_coefficient_sub : (remove_leading_coefficient f).support ⊆ range f.nat_degree :=
begin
  unfold remove_leading_coefficient,
  intros a,
  simp_rw [mem_support_iff_coeff_ne_zero, (finset_sum_coeff (range (nat_degree f)) (λ (b : ℕ), C (coeff f b) * X ^ b) a), coeff_C_mul_X (f.coeff _) _ a],
  finish,
end


lemma not_mem_of_not_mem_supset {a b : finset ℕ} (h : a ⊆ b) {n : ℕ} : n ∉ b → n ∉ a :=
begin
  apply mt,
  solve_by_elim,
end

@[simp] lemma support_remove_leading_coefficient_ne : f.nat_degree ∉ (remove_leading_coefficient f).support :=
begin
  apply not_mem_of_not_mem_supset support_remove_leading_coefficient_sub,
  exact not_mem_range_self,
end


@[simp] lemma ne_nat_degree_of_mem_support_remove {a : ℕ} : a ∈ (remove_leading_coefficient f).support → a ≠ f.nat_degree :=
begin
  contrapose,
  push_neg,
  intro,
  rw a_1,
  exact support_remove_leading_coefficient_ne,
end






lemma mem_diff_of_mem_remove_leading_coefficient {a : ℕ} : a ∈ (remove_leading_coefficient f).support → a ∈ (f.support \ {f.nat_degree}) :=
begin
  rw [mem_sdiff, mem_support_iff_coeff_ne_zero, mem_support_iff_coeff_ne_zero, not_mem_singleton],
  intro,
  split,
    { intro,
      apply a_1,
      unfold remove_leading_coefficient,
      simp only [coeff_X_pow, mul_boole, finset_sum_coeff, coeff_C_mul, mem_range, finset.sum_ite_eq],
      split_ifs,
        { assumption, },
        { refl, }, },
    { apply ne_nat_degree_of_mem_support_remove,
      rwa mem_support_iff_coeff_ne_zero, },
end

@[simp] lemma coeff_remove_eq_coeff_of_ne {a : ℕ} (h : a ≠ f.nat_degree) : (remove_leading_coefficient f).coeff a = f.coeff a :=
begin
  unfold remove_leading_coefficient,
  simp_rw [finset_sum_coeff, coeff_C_mul, coeff_X_pow, mul_boole, finset.sum_ite_eq],
  split_ifs,
    { refl, },
    { symmetry,
      apply coeff_eq_zero_of_nat_degree_lt,
      rw [mem_range, not_lt] at h_1,
      exact lt_of_le_of_ne h_1 (ne.symm h), },
end

@[simp] lemma coeff_remove_nat_degree : (remove_leading_coefficient f).coeff f.nat_degree = 0 :=
begin
  unfold remove_leading_coefficient,
  simp only [coeff_X_pow, mul_boole, not_mem_range_self, finset_sum_coeff, coeff_C_mul, if_false, finset.sum_ite_eq],
end

lemma mem_remove_leading_coefficient_of_mem_diff {a : ℕ} : a ∈ (f.support \ {f.nat_degree}) → a ∈ (remove_leading_coefficient f).support :=
begin
  rw [mem_sdiff, mem_support_iff_coeff_ne_zero, mem_support_iff_coeff_ne_zero, not_mem_singleton],
  intro,
  cases a_1 with fa asmall,
  rwa coeff_remove_eq_coeff_of_ne asmall,
end

lemma support_remove_leading_coefficient (f0 : f ≠ 0) : (remove_leading_coefficient f).support = f.support \ {f.nat_degree} :=
begin
  ext,
  split,
    { rw mem_support_iff_coeff_ne_zero,
      by_cases ha : a = f.nat_degree,
        { rw ha,
          intro,
          exfalso,
          exact a_1 coeff_remove_nat_degree, },
        { rw [coeff_remove_eq_coeff_of_ne ha, mem_sdiff, not_mem_singleton],
          intro,
          exact ⟨mem_support_iff_coeff_ne_zero.mpr a_1 , ha ⟩,
        }, },
    { exact mem_remove_leading_coefficient_of_mem_diff, },
end

lemma remove_leading_coefficient_nonzero_of_large_support (f0 : 2 ≤ f.support.card) : (remove_leading_coefficient f).support.nonempty :=
begin
  have fn0 : f ≠ 0,
    rw [← non_zero_iff, nonempty_iff_ne_empty],
    intro,
    rw ← card_eq_zero at a,
    finish,
  rw nonempty_iff_ne_empty,
  apply ne_empty_of_mem,
  rotate,
  use nat_trailing_degree f,
  rw [mem_support_iff_coeff_ne_zero, coeff_remove_eq_coeff_of_ne, ← mem_support_iff_coeff_ne_zero],
    { exact nat_trailing_degree_mem_support_of_nonzero fn0, },
    { rw [defs_by_Johann fn0, defs_by_Johann_trailing fn0],
      exact card_two_d f0, },
end

lemma nat_degree_remove_leading_coefficient (f0 : 2 ≤ f.support.card) : (remove_leading_coefficient f).nat_degree < f.nat_degree :=
begin
  rw defs_by_Johann (non_zero_iff.mp (remove_leading_coefficient_nonzero_of_large_support f0)),
  apply nat.lt_of_le_and_ne _ (ne_nat_degree_of_mem_support_remove ((remove_leading_coefficient f).support.max'_mem (non_zero_iff.mpr _))),
  apply max'_le,
    rw support_remove_leading_coefficient,
      { intros y hy,
        apply le_nat_degree_of_ne_zero,
        rw mem_sdiff at hy,
        exact (mem_support_iff_coeff_ne_zero.mp hy.1), },
      { rw ← non_zero_iff,
        apply nonempty_of_card_nonzero,
        omega, },
end


lemma support_remove_lt (h : f ≠ 0) : (remove_leading_coefficient f).support.card < f.support.card :=
begin
  rw support_remove_leading_coefficient h,
  apply card_lt_card,
  split,
    { exact f.support.sdiff_subset {nat_degree f}, },
    { intro,
      rw defs_by_Johann h at a,
      have : f.support.max' (non_zero_iff.mpr h) ∈ f.support \ {f.support.max' (non_zero_iff.mpr h)} := a (max'_mem f.support (non_zero_iff.mpr h)),
      simp only [mem_sdiff, eq_self_iff_true, not_true, and_false, mem_singleton] at this,
      cases this, },
end

lemma sum_leading_term_remove (f : polynomial R) : f = (remove_leading_coefficient f) + (C f.leading_coeff) * X^f.nat_degree :=
begin
  ext1,
  by_cases nm : n = f.nat_degree,
    { rw [nm, coeff_add, coeff_C_mul, coeff_X_pow_self, mul_one, coeff_remove_nat_degree, zero_add],
      refl, },
    { simp only [*, coeff_remove_eq_coeff_of_ne nm, coeff_X_pow f.nat_degree n, add_zero, coeff_C_mul, coeff_add, if_false, mul_zero], },
end

lemma sum_lt_support (h : 2 ≤ f.support.card) : ∃ f0 f1 : polynomial R , f0.support.card < f.support.card ∧ f1.support.card < f.support.card ∧ f = f0+f1 :=
begin
  use (C (leading_coeff f))*X^f.nat_degree,
  use (remove_leading_coefficient f),
  split,
    { apply lt_of_lt_of_le _ h,
      convert one_lt_two,
      rw [support_term_nonzero, card_singleton],
      rw [← leading_coeff_nonzero_of_nonzero, ← non_zero_iff],
      apply nonempty_of_card_nonzero,
      omega, },
    { split,
        { apply support_remove_lt,
          rw ← non_zero_iff,
          apply nonempty_of_card_nonzero,
          omega, },
        { rw add_comm,
          exact sum_leading_term_remove f, }, },
end


lemma le_ind {P : polynomial R → Prop} {f g : polynomial R}
 {Psum : (P f) → (P g) → (P (f+g))} {Pmon : ∀ r : R , ∀ n : ℕ , P (C r * X^n)} :
 ∀ p : polynomial R, P p :=
 begin
   tidy,
 end




@[simp] lemma reflect_zero {n : ℕ} : reflect n (0 : polynomial R) = 0 :=
begin
  refl,
end

@[simp] lemma reflect_add {f g : polynomial R} {n : ℕ} : reflect n (f+g) = reflect n f + reflect n g :=
begin
  ext1,
  unfold reflect,
  simp only [coeff_mk, coeff_add],
end

lemma add_cancel {a b : R} {h : a=0} : a+b=b :=
begin
  rw [h, zero_add],
end


lemma monomial_of_card_support_le_one (h : f.support.card ≤ 1) : f = C f.leading_coeff * X^f.nat_degree :=
begin
  by_cases f0 : f = 0,
  { ext1,
    rw [f0, leading_coeff_zero, C_0, zero_mul], },
  conv
  begin
    congr,
    rw sum_leading_term_remove f,
    skip,
  end,
  apply add_cancel,
  rw [← support_eq_empty, ← card_eq_zero],
  apply nat.eq_zero_of_le_zero (nat.lt_succ_iff.mp _),
  convert support_remove_lt f0,
  apply le_antisymm _ h,
  exact card_le_of_subset (singleton_subset_iff.mpr (nat_degree_mem_support_of_nonzero f0)),
end

lemma reflect_mul_ind (N n : ℕ) {f g : polynomial R} {h : f.support.card ≤ n.succ} : reflect N (f*g) = reflect N (f) * reflect N (g) :=
begin
  induction n with n hn,
    { rw [monomial_of_card_support_le_one h, mul_assoc, X_pow_mul, ← mul_assoc],
      rw reflect_term,
      rw [monomial_of_card_support_le_one h, le_zero_iff_eq, card_eq_zero, support_eq_empty] at h,
      rw [h, zero_mul, reflect_zero, zero_mul], },
    {

      sorry,
    },
end




#exit
lemma reflect_mul_ind (N n : ℕ) {f g : polynomial R} {h : f.support.card ≤ n} : reflect N (f*g) = reflect N (f) * reflect N (g) :=
begin
  induction n with n hn,
    { rw [le_zero_iff_eq, card_eq_zero, support_eq_empty] at h,
      rw [h, zero_mul, reflect_zero, zero_mul], },
    {
      
      sorry,
    },
end




#exit

lemma reflect_mul (N : ℕ) {f g : polynomial R} : reflect N (f*g) = reflect N (f) * reflect N (g) :=
begin
  unfold reflect,
  tidy,
  simp * at *,
  exact reflect_invol,
end




#exit

#exit
@[simp] lemma nat_degree_sum {f g : polynomial R} {y : ℕ} : y ∈ support (f+g) → y ∈ support f ∪ support g :=
begin
  intros a,
  rw mem_support_iff_coeff_ne_zero,
  rw coeff_add,
  intros ha,
  rw mem_union,
  repeat {rw mem_support_iff_coeff_ne_zero},
  apply nonzero_or_of_nonzero_sum ha,
end




lemma nat_degree_sum_le {f g : polynomial R} : nat_degree (f+g) ≤ max (nat_degree f) (nat_degree g) :=
begin
  by_cases hfg : f+g = 0,
    { rw [hfg, nat_degree_zero],
    exact zero_le (max (nat_degree f) (nat_degree g)), },
    {
      rw defs_by_Johann hfg,
      apply max'_le,
      intros y hy,
      have : y ∈ support f ∪ support g,

      rw [mem_support_iff, add_apply] at hy,
      rw [add_apply, mem_support_iff, ne.def] at *,
      sorry,
    },
  by_cases hf : f = 0,
    { rw [hf, nat_degree_zero, zero_add, zero_add], },
    { by_cases hg : g = 0,
        { rw [hg, nat_degree_zero, add_zero, add_zero], },
        {
          repeat {rw defs_by_Johann _},


          sorry,
        }, },

  repeat {rw defs_by_Johann},
  
  convert max'_union,
end



#exit

lemma strip_pol {h : f ≠ 0} : f = (C (leading_coeff f))*X^f.nat_degree +  ∑ (i : ℕ) in finset.range f.nat_degree, (C (f.coeff i)) * X^i :=
begin
  ext1,
  by_cases hh : n = f.nat_degree,
    rw hh,
    rw coeff_add,
    conv_rhs
    begin
      congr,rw ← zero_add f.nat_degree,rw pow_add,rw pow_zero,rw one_mul,
    end,
    rw [coeff_mul_X_pow (C (f.leading_coeff)) f.nat_degree 0, coeff_C_zero],
    unfold leading_coeff,
    symmetry,
    rw [coeff_eq_zero_of_not_mem_support, zero_add],
    apply coeff_eq_zero_of_nat_degree_lt,
--    have : (∑ (i : ℕ) in range f.nat_degree, C (f.coeff i) * X ^ i).support = {a : ℕ | a ∈ (range f.nat_degree) ∧ (f.coeff a ≠ 0)}.to_finset,
--      library_search,

    have : (∑ (i : ℕ) in range f.nat_degree, C (f.coeff i) * X ^ i).support ⊆ range f.nat_degree,
      intros a ha,
      apply 
      

      
    
    rw ← hh,
    unfold nat_degree,
    rw hh,
    
    convert add_zero _,


    rw nat.
    conv_rhs
    begin
      congr,skip,
      rw coeff_eq_zero_of_not_mem_support,skip,
      
    end,

    convert add_zero ((C (f.coeff f.nat_degree) * X ^ f.nat_degree).coeff f.nat_degree),
      { rw add_zero,
        conv_rhs
        begin
          congr,congr,skip,skip,rw ← zero_add f.nat_degree,
        end,
        rw [coeff_mul_X_pow (C (f.coeff f.nat_degree)) f.nat_degree 0, coeff_C_zero], },
      {
        conv_rhs
        begin
          congr,congr,skip,skip,rw ← zero_add f.nat_degree,
        end,
        rw [coeff_mul_X_pow (C (f.coeff f.nat_degree)) f.nat_degree 0, coeff_C_zero],
        sorry,
      },


      conv_rhs
      begin
        congr,
        rw coeff_mul_X_pow (C (f.coeff f.nat_degree)) f.nat_degree 0,
        congr,congr,skip,rw ← add_zero f.nat_degree,
      end,

--      convert leading_coeff_monomial (f.leading_coeff) n,
      convert coeff_mul_X_pow (C (f.coeff f.nat_degree)) n 0,

      conv_rhs
      begin
        rw leading_coeff_monomial (f.leading_coeff) f.nat_degree,
      end,
  rw f.as_sum,

  
  --tidy,
  sorry,
end



#exit
lemma strip_pol {h : f ≠ 0} : f = (C (leading_coeff f))*X^f.nat_degree +  ∑ (i : ℕ) in finset.range f.nat_degree, (C (f.coeff i)) * X^i :=
begin
  ext1,
  by_cases hh : n = f.nat_degree,
    rw hh,
    rw coeff_add,
    convert add_zero ((C (f.coeff f.nat_degree) * X ^ f.nat_degree).coeff f.nat_degree),
      rw add_zero,
      conv_rhs
      begin
--        rw coeff_mul_X_pow (C (f.coeff f.nat_degree)) n 0,
        congr,congr,skip,skip,rw ← zero_add f.nat_degree,
      end,
      rw [coeff_mul_X_pow (C (f.coeff f.nat_degree)) f.nat_degree 0, coeff_C_zero],


      conv_rhs
      begin
        congr,
        rw coeff_mul_X_pow (C (f.coeff f.nat_degree)) f.nat_degree 0,
        congr,congr,skip,rw ← add_zero f.nat_degree,
      end,

--      convert leading_coeff_monomial (f.leading_coeff) n,
      convert coeff_mul_X_pow (C (f.coeff f.nat_degree)) n 0,

      conv_rhs
      begin
        rw leading_coeff_monomial (f.leading_coeff) f.nat_degree,
      end,
  rw f.as_sum,

  
  --tidy,
  sorry,
end

lemma polind {P : polynomial R → bool} {H0 : ∀ c : R , ∀ n : ℕ , P (C c * X^n)} {Hsum : ∀ f g : polynomial R , P f → P g → P (f + g)} : ∀ p : polynomial R , P p :=
--lemma polind {P : polynomial R → bool} {H0 : ∀ c : R , ∀ n : ℕ , P (C c * X^n)} {Hsum : ∀ f g : polynomial R , f.support ∩ g.support = ∅ → P (f + g)} : ∀ p : polynomial R , P p :=
begin
  intro p,
  unfold_coes,
  let nte : ℕ := finset.card p.support,
  by_cases hh : nte = 0,
    { 
      have : p.support = ∅,
        finish,
      have : p = 0, by rwa ← support_eq_empty,
      rw this,
      convert (H0 (0 : R) 0),
      rw [C_0, zero_mul], },
    rw [card_eq_zero, support_eq_empty] at hh,
    let p0 : polynomial R := ∑ (i : ℕ) in finset.range p.nat_degree, (C (p.coeff i)) * X^i,
    have : p = p0 + (C (leading_coeff p))*X^p.nat_degree,
      library_search,
    
    
    


    
      rw hh at nte,
    {
        
      sorry,
    },
    {
      sorry,
    },
  

  sorry,
--  library_search,
end



#exit
lemma polind {P : polynomial R → bool} {H0 : ∀ c : R , ∀ n : ℕ , P (C c * X^n)} {Hsum : ∀ f g : polynomial R , P f → P g → P (f + g)} : ∀ p : polynomial R , P p :=
--lemma polind {P : polynomial R → bool} {H0 : ∀ c : R , ∀ n : ℕ , P (C c * X^n)} {Hsum : ∀ f g : polynomial R , f.support ∩ g.support = ∅ → P (f + g)} : ∀ p : polynomial R , P p :=
begin
  intro p,
  unfold_coes,
  let nte := finset.card p.support,
  by_cases hh : nte = 0,
    { have : p.support = ∅,
        finish,
      have : p = 0, by rwa ← support_eq_empty,
      rw this,
      convert (H0 (0 : R) 0),
      rw [C_0, zero_mul], },
    
    
    


    
      rw hh at nte,
  induction nte with n hn,
    {
        
      sorry,
    },
    {
      sorry,
    },
  

  sorry,
--  library_search,
end



#exit

@[simp] lemma revrev1 : reverse (f*X) = reverse f :=
begin
  unfold reverse,


--  tidy,
  by_cases f0 : f = 0,
    { rw [f0, mul_zero], },
    { rw X_mul,
      ext1,
      unfold reverse,
--      unfold reflect,
--      simp only [coeff_mk],
      
--        exact degree_mul_X f0,
     --   apply nat_degree_
      by_cases h : n ≤ nat_degree f,
        { unfold reflect,
          simp_rw [coeff_mk, rev_at_small h],
          rw [rev_at_small, degree_mul_X f0],
            { convert nat.succ_sub h,
              rw eq_iff_iff,
              split,
                { intro,
                  exact nat.succ_sub h, },
                { intro,
                  rw a,
                  apply coeff_mul_X, }, },
          rw degree_mul_X f0,
          exact nat.le_succ_of_le h, },
      rw not_le at h,
      rw coeff_eq_zero_of_nat_degree_lt,
      symmetry,
      apply reversal_coeff_large h,
      have : (reflect (f * X).nat_degree (f * X)).nat_degree ≤ f.nat_degree,
        {
          rw nat_degree_eq_max,
          apply max'_le,
          intros d hd,
          norm_num at hd,
          cases hd,
            { change (reflect (f * X).nat_degree (f * X)).coeff d ≠ 0 at hd,
              rw ← mem_support_iff_coeff_ne_zero at hd,
              have : ∃ e : ℕ , e ∈ (f*X).support ∧ d = rev_at (f * X).nat_degree e,
                use (rev_at (f * X).nat_degree d),
                rw rev_at_invol,
                split,
                  { unfold reflect at hd,
                    simp at hd,
                    rcases hd with ⟨ _ , _ , rfl ⟩,
                    rw rev_at_invol,
                    simp,
                    assumption, },
                  { refl, },
              cases this,
              cases this_h,
              norm_num at this_h_left,
              cases this_h_left,
--              squeeze_simp *,--simp only [mem_support_iff, ne.def] at this_h_left,
              rw this_h_right,
              rw rev_at_small,
                { rw degree_mul_X f0,
                  omega, },
                { rw degree_mul_X f0,
                  apply nat.le_succ_of_pred_le,
                  apply le_degree_of_mem_supp,
                  apply mem_support_iff_coeff_ne_zero.mpr (this_h_left_right), }, },
            { rw hd,
              exact zero_le _, }, },
      exact gt_of_gt_of_ge h this, },
end

--#exit


@[simp] lemma revrev11 : reverse (X*f) = reverse f :=
begin
  by_cases f0 : f = 0,
    { rw [f0, mul_zero], },
    { rw X_mul,
      ext1,
      unfold reverse,
      by_cases h : n ≤ nat_degree f,
        { unfold reflect,
          simp_rw [coeff_mk, rev_at_small h],
          rw [rev_at_small, degree_mul_X f0],
            { convert nat.succ_sub h,
              rw eq_iff_iff,
              split,
                { intro,
                  exact nat.succ_sub h, },
                { intro,
                  rw a,
                  apply coeff_mul_X, }, },
          rw degree_mul_X f0,
          exact nat.le_succ_of_le h, },
      rw not_le at h,
      rw coeff_eq_zero_of_nat_degree_lt,
      symmetry,
      apply reversal_coeff_large h,
      have : (reflect (f * X).nat_degree (f * X)).nat_degree ≤ f.nat_degree,
        {
          rw nat_degree_eq_max,
          apply max'_le,
          intros d hd,
          norm_num at hd,
          cases hd,
            { change (reflect (f * X).nat_degree (f * X)).coeff d ≠ 0 at hd,
              rw ← mem_support_iff_coeff_ne_zero at hd,
              have : rev_at (f * X).nat_degree d ∈ (f*X).support,
                  { unfold reflect at hd,
                    simp at hd,
                    rcases hd with ⟨ _ , _ , rfl ⟩,
                    rw rev_at_invol,
                    simp,
                    assumption, },
              apply nat.le_of_lt_succ,
              rw [nat.succ_eq_add_one, ← degree_mul_X f0],
              rw ← @rev_at_invol (f*X).nat_degree d,
              apply le_degree_of_mem_supp,
              rw mem_support_iff_coeff_ne_zero,
              norm_num at this,
              cases this,
              rw mem_support_iff_coeff_ne_zero at hd,
--              simp * at this_right,
--              simp_rw [mem_coe, ← mem_support_iff_coeff_ne_zero] at this_right,
              simp only,--simp only [mem_support_iff, ne.def] at this_h_left,
              --rw this_right,
              
              rw degree_mul_X f0,
              rw degree_mul_X f0,
              apply nat.le_succ_of_pred_le,
              apply mem_support_iff_coeff_ne_zero.mpr (this_h_left_right), },
            { rw hd,
              exact zero_le _, }, },
      exact gt_of_gt_of_ge h this, },
end

#exit



@[simp] lemma revrev1 : reverse (X*f) = reverse f :=
begin
  by_cases f0 : f = 0,
    { rw [f0, mul_zero], },
    { rw X_mul,
      ext1,
      unfold reverse,
--      unfold reflect,
--      simp only [coeff_mk],
      
--        exact degree_mul_X f0,
     --   apply nat_degree_
      by_cases h : n ≤ nat_degree f,
        { unfold reflect,
          simp only [coeff_mk],
          rw rev_at_small h,
          rw rev_at_small,
            { rw degree_mul_X f0,
            --squeeze_simp * at *,
              convert nat.succ_sub h,
              rw eq_iff_iff,
              fsplit, work_on_goal 0 { intros a }, work_on_goal 1 { intros a },
                { exact nat.succ_sub h, },
                { rw a,
                  apply coeff_mul_X, }, },
          rw degree_mul_X f0,
          exact nat.le_succ_of_le h, },
      simp * at *,
      rw coeff_eq_zero_of_nat_degree_lt,
      symmetry,
      apply reversal_coeff_large h,
      have : (reflect (f * X).nat_degree (f * X)).nat_degree ≤ f.nat_degree,
        {
          rw nat_degree_eq_max,
          apply max'_le,
          intros d hd,
          norm_num at hd,
          cases hd,
            { change (reflect (f * X).nat_degree (f * X)).coeff d ≠ 0 at hd,
              rw ← mem_support_iff_coeff_ne_zero at hd,
              have : ∃ e : ℕ , e ∈ (f*X).support ∧ d = rev_at (f * X).nat_degree e,
                use (rev_at (f * X).nat_degree d),
                rw rev_at_invol,
                split,
                  { unfold reflect at hd,
                    simp at hd,
                    rcases hd with ⟨ _ , _ , rfl ⟩,
                    rw rev_at_invol,
                    simp,
                    assumption, },
                  { refl, },
              cases this,
              cases this_h,
              norm_num at this_h_left,
              cases this_h_left,
--              squeeze_simp *,--simp only [mem_support_iff, ne.def] at this_h_left,
              rw this_h_right,
              rw rev_at_small,
              rw degree_mul_X f0,
              omega,
              rw degree_mul_X f0,
              apply nat.le_succ_of_pred_le,
              apply le_degree_of_mem_supp,
              apply mem_support_iff_coeff_ne_zero.mpr (this_h_left_right), },
            { rw hd,
              exact zero_le _, }, },
      exact gt_of_gt_of_ge h this, },
end

#exit


@[simp] lemma revrev1 : reverse (X*f) = reverse f :=
begin
  by_cases f0 : f = 0,
    { rw [f0, mul_zero], },
    { rw X_mul,
      ext1,
      unfold reverse,
--      unfold reflect,
--      simp only [coeff_mk],
      
--        exact degree_mul_X f0,
     --   apply nat_degree_
      by_cases h : n ≤ nat_degree f,
        { unfold reflect,
          simp only [coeff_mk],
          rw rev_at_small h,
          rw rev_at_small,
            { rw degree_mul_X f0,
            --squeeze_simp * at *,
              convert nat.succ_sub h,
              rw eq_iff_iff,
              fsplit, work_on_goal 0 { intros a }, work_on_goal 1 { intros a },
                { exact nat.succ_sub h, },
                { rw a,
                  apply coeff_mul_X, }, },
          rw degree_mul_X f0,
          exact nat.le_succ_of_le h, },
      simp * at *,
      rw coeff_eq_zero_of_nat_degree_lt,
      symmetry,
      apply reversal_coeff_large h,
      have : (reflect (f * X).nat_degree (f * X)).nat_degree ≤ f.nat_degree,
        {
          rw nat_degree_eq_max,
          apply max'_le,
          intros d hd,
          norm_num at hd,
          cases hd,
            { have : (reflect (f * X).nat_degree (f * X)).coeff d ≠ 0,
                exact hd,
              rw ← mem_support_iff_coeff_ne_zero at this,
              have : ∃ e : ℕ , e ∈ (f*X).support ∧ d = rev_at (f * X).nat_degree e,
                use (rev_at (f * X).nat_degree d),
                rw rev_at_invol,
                split,
                  unfold reflect at this,
                  work_on_goal 0 { dsimp at *, simp at *, cases this, cases this_h, induction this_h_right, cases this_h_left, simp at *, fsplit, work_on_goal 0 { assumption }, assumption }, work_on_goal 0 { refl }, cases this, cases this_h, simp at *, cases this_h_left,
              rw this_h_right,
              rw rev_at_small,
              rw degree_mul_X f0,
              omega,
              rw degree_mul_X f0,
              apply nat.le_succ_of_pred_le,
              apply le_degree_of_mem_supp,
              apply mem_support_iff_coeff_ne_zero.mpr (this_h_left_right),
            },
            { rw hd,
              exact zero_le _, },
        },
      exact gt_of_gt_of_ge h this, },
end

#exit

@[simp] lemma revrev1 : reverse (X*f) = reverse f :=
begin
  by_cases f0 : f = 0,
    { rw [f0, mul_zero], },
    { have degX : (f * X).nat_degree = (f).nat_degree+1, by exact degree_mul_X f0,
      have : X*f=f*X, by exact X_mul,
      rw this,
      ext1,
      unfold reverse,
      unfold reflect,
      simp only [coeff_mk],
      
--        exact degree_mul_X f0,
     --   apply nat_degree_
      by_cases h : n ≤ nat_degree f,
        { rw rev_at_small h,
          rw rev_at_small,
            { simp * at *,
              convert nat.succ_sub h,
              rw eq_iff_iff,
              fsplit, work_on_goal 0 { intros a }, work_on_goal 1 { intros a },
                { exact nat.succ_sub h, },
                { rw a,
                  apply coeff_mul_X, }, },
          rw degree_mul_X f0,
          exact nat.le_succ_of_le h, },
       },
end

#exit

@[simp] lemma revrev : reverse (reverse f) = X^(nat_trailing_degree f)*f :=
begin
  by_cases f0 : f = 0,
    { rw [f0, mul_zero],
      refl, },
    { ext1,
      unfold reverse,
      unfold reflect,
      by_cases h : n < nat_trailing_degree f,
        { have : (X^(nat_trailing_degree f) * f).coeff n = 0,
            apply coeff_zero_of_le_trailing_degree n,
            induction nat_trailing_degree f,
              { rwa [pow_zero, one_mul], },
              { rw [pow_succ],
                have : nat_trailing_degree (X ^ n_1 * f) + 1 = nat_trailing_degree (X * X ^ n_1 * f),
                  symmetry,
                  unfold nat_trailing_degree,
                  have : X * X ^ n_1 * f ≠ 0,
                    intro,
                    apply f0,
                    ext1,
                    apply non_zero_iff.mp,
                    
                refine nat_trailing_degree_le_of_ne_zero,
                apply coeff_mul_X,
                sorry, },
    },

    simp * at *,
      sorry, },
    { sorry, },
  
  rw coeff_mk,
  simp only [rev_at_invol],
  refl,
end

#exit

@[simp] lemma revrevval {M N n : ℕ} {M ≤ N} : rev_at M (rev_at N n) = n :=
begin
  ext1,
  unfold reflect,
  rw coeff_mk,
  simp only [rev_at_invol],
  refl,
end


#reduce rev_at 3 (rev_at 5 6)
#reduce rev_at 4 (rev_at 3 4)

#exit

@[simp] lemma revrev : reverse (reverse f) = X^(nat_trailing_degree f)*f :=
begin
  ext1,
  unfold reverse,
  
  rw coeff_mk,
  simp only [rev_at_invol],
  refl,
end

#exit





lemma revrevn {R : Type*} [field R] {p q : polynomial R} {n : ℕ} {Hp : coeff p ≠ 0} {Hq : coeff q ≠ 0} {Hpq : coeff (p*q) ≠ 0} : coeff (at_infty (p * q)) n = coeff (at_infty p * at_infty q) n :=
begin
  rw p.as_sum,
  rw q.as_sum,
  simp * at *,
  library_search,
--  simp * at *,
--  rw coeff_of_degree
--  unfold_coes,
--  hint,
  sorry,
end


#exit

--try induction, using rev_at something fixed, greater than or equal to the degree


@[simp] lemma atat {H : coeff f 0 ≠ 0} : at_infty (at_infty f) = f :=
begin
  sorry,
end



lemma revrevn {R : Type*} [field R] {p q : polynomial R} {n : ℕ} {Hp : coeff p ≠ 0} {Hq : coeff q ≠ 0} {Hpq : coeff (p*q) ≠ 0} : coeff (at_infty (p * q)) n = coeff (at_infty p * at_infty q) n :=
begin
  rw p.as_sum,
  rw q.as_sum,
  simp * at *,
  library_search,
--  simp * at *,
--  rw coeff_of_degree
--  unfold_coes,
--  hint,
  sorry,
end

#exit


lemma revrev {R : Type*} [semiring R] {p q : polynomial R} : at_infty (p * q) = at_infty p * at_infty q :=
begin
  ext1,
  
  rw p.as_sum,
  rw q.as_sum,
  unfold_coes,
--  hint,
  sorry,
end


#check polynomial.mul
#check polynomial


#exit

@[simp] lemma trailing_coeff_mul {R : Type*} [comm_ring R] [integral_domain R] (p q : polynomial R) : trailing_coeff (p * q) =
  trailing_coeff p * trailing_coeff q :=
begin
  unfold trailing_coeff,
  repeat {rw ← lead_trail_coeff},
  convert leading_coeff_mul (at_infty (p)) (at_infty (q)),


  have : leading_coeff (at_infty (p)) = (at_infty (p)).coeff (at_infty (p)).nat_degree, by refl,
  rw ← this,
  have : leading_coeff (at_infty (q)) = (at_infty (q)).coeff (at_infty (q)).nat_degree, by refl,
  rw ← this,
  have : leading_coeff (at_infty (p*q)) = (at_infty (p*q)).coeff (at_infty (p*q)).nat_degree, by refl,
  rw ← this,

    --library_search,


--  refine (leading_coeff_mul (at_infty p) (at_infty q)),
  sorry,
end



/-
@[simp] lemma trailing_coeff_mul (p q : polynomial R) : trailing_coeff (p * q) =
  trailing_coeff p * trailing_coeff q :=
begin
  by_cases hp : p = 0,
  { simp only [hp, zero_mul, trailing_coeff_zero] },
  { by_cases hq : q = 0,
    { simp only [hq, mul_zero, trailing_coeff_zero] },
    { rw [trailing_coeff_mul'],
      exact mul_ne_zero (mt trailing_coeff_eq_zero.1 hp) (mt trailing_coeff_eq_zero.1 hq) } }
end
-/



#exit


--lemma lead_trail_supps {R : Type*} [semiring R] {f : polynomial R} {hs : f.support.nonempty}: (at_infty f).support.max' = f.support.min' :=


lemma xx {s : finset ℕ} {hs : s.nonempty} : (finset.image (rev_at (finset.max' s hs)) s).nonempty :=
begin
  exact nonempty.image hs (rev_at (max' s hs)),
end
-- : finset.max' (finset.image (rev_at (finset.max' s hs)) s) (by sorry) = rev_at (finset.max' s hs) (finset.min' s hs) :=

--#check finset.image
--#check finset.range


def mon {α β : Type*} [linear_order α] [linear_order β] (f : α → β) := ∀ ⦃x y : α⦄, x ≤ y → f y ≤ f x

lemma min_max_mon {α β : Type*} [decidable_linear_order α] [decidable_linear_order β]
  {s : finset α} (hs : s.nonempty) {f : α → β} (mf : mon f) :
  max' (image f s) (hs.image f) = f (min' s hs) :=
begin
  apply le_antisymm,
    { refine (image f s).max'_le (nonempty.image hs f) (f (min' s hs)) _,
      intros x hx,
      rw mem_image at hx,
      rcases hx with ⟨ b , bs , rfl⟩,
      apply mf,
      apply min'_le,
      assumption, },
    { apply le_max',
      refine mem_image_of_mem f _,
      exact min'_mem s hs, },
end

def rev_at_n (N : ℕ) : ℕ → ℕ := λ i : ℕ , (N-i)

lemma min_max {s : finset ℕ} {hs : s.nonempty} : max' (image (rev_at_n (max' s hs)) s) (by exact nonempty.image hs (rev_at_n (max' s hs))) = rev_at_n (max' s hs) (min' s hs) :=
begin
  refine min_max_mon hs _,
  intros x y hxy,
  unfold rev_at_n,
  omega,
end

/-
lemma min_max {s : finset ℕ} {hs : s.nonempty} : max' (image (rev_at (max' s hs)) s) (by exact nonempty.image hs (rev_at (max' s hs))) = rev_at (max' s hs) (min' s hs) :=
begin
  sorry,
end

lemma min_max2 {s : finset ℕ} {hs : s.nonempty} --{fne : f.support.nonempty}
 : finset.max' (finset.image (rev_at (finset.max' s hs)) s) (by exact nonempty.image hs (rev_at (max' s hs))) = rev_at (finset.max' s hs) (finset.min' s hs) :=
begin
  exact min_max,
end
-/

lemma ff {N n : ℕ} (H : n ≤ N) : rev_at N n = rev_at_n N n :=
begin
  rw rev_at_small H,
  refl,
end 

lemma le_degree_of_mem_support {R : Type*} [semiring R] {f : polynomial R} {a : ℕ} (H : a ∈ f.support) : a ≤ f.nat_degree :=
begin
  exact le_degree_of_mem_supp a H,
end 

lemma at_infty_degree_le_degree {R : Type*} [semiring R] {f : polynomial R} {a : ℕ} : (at_infty f).degree ≤ f.degree :=
begin
  by_cases H : f.support.nonempty,
    {
      rw nat_degree_eq
      sorry,
    },
    {
      sorry,
    },
--  unfold degree,
--  by_cases H : option.get_or_else f.degree = none,
  sorry,
end
--            { rw mem_image at a_1,
--              cases a_1,
--              cases a_1_h,
--              rw ← a_1_h_h,
--              rw degdeg,
--              unfold rev_at_n,
--              exact (f.support.max' fne).sub_le a_1_w, },



lemma lead_trail_min_max {R : Type*} [semiring R] {f : polynomial R} {ain : (at_infty f).support.nonempty} {fne : f.support.nonempty} : finset.max' (support (at_infty f)) ain = f.nat_degree - (f.support.min' fne) :=
begin
--  have : 
  convert min_max,
    { ext1,
      split,
        { intro ha,
          apply mem_image.mpr,
          have : (rev_at_n (f.support.max' fne) a) ∈ f.support,
            { rwa [ ← ff, ← defs_by_Johann, ← supp_at_infty_of_supp],

              sorry, },
          split,
            { use this,
              rw rev_at_n,
              simp only,
              rw nat.sub_sub_self,
              rw ← defs_by_Johann,
              unfold rev_at_n at this,
              have : a ≤ (at_infty f).nat_degree,
                exact le_degree_of_mem_supp a ha,
              refine le_trans this _,
              
              sorry, }, },
        { intro,
          have degdeg : f.nat_degree = f.support.max' fne, by exact defs_by_Johann fne,
          have alenat : a ≤ f.nat_degree,
            { rw mem_image at a_1,
              cases a_1,
              cases a_1_h,
              rw ← a_1_h_h,
              rw degdeg,
              unfold rev_at_n,
              exact (f.support.max' fne).sub_le a_1_w, },
          have : a ≤ f.support.max' fne,
            { exact has_le.le.trans_eq alenat degdeg, },
          rw supp_at_infty_of_supp,
          simp at *,
          cases a_1 with a1,
          cases a_1_h with a1supp a1refl,
          rw ff alenat,
          intro,
          apply a1supp,
          rw ← ff at a1refl,
          { rw ← ff at a_1,
            { apply not_mem_support_iff.mp,
              intro,
              apply a1supp,
              rw ← supp_at_infty_of_supp' at a_2,
              rw ← not_mem_support_iff at a_1,
              exfalso,
              apply a_1,
              rw ← a1refl,
              rw degdeg,
              rw rev_invol,
              finish, },
            { assumption, }, },
            sorry, }, },
    { exact defs_by_Johann fne, },
end

#exit
          rw ← supp_at_infty_of_supp',
          rw f.3 a1 at a_2,
          unfold rev_at_n,
          sorry, }, },
    { exact defs_by_Johann fne, },

#exit
--    rw ff _,
    --unfold rev_at_n,

  let ais : set ℕ := { a : ℕ | (at_infty f).coeff a ≠ 0},
  let  fs : set ℕ := { a : ℕ | f.coeff a ≠ 0},
  have : ais = rev_at f.nat_degree '' fs,
    { ext1,
    split,
      { 
        intro,
        use rev_at f.nat_degree x,
        split,
          { have : rev_at f.nat_degree x ∈ f.support,
            { 
              sorry, },
            intro,
            sorry, },
          { sorry, },
        have : ∃ (d : ℕ) , d ∈ fs ∧ rev_at f.nat_degree d = x,
          { sorry, },
        cases this with g,
        cases this_h with gh xrev,
        rw ← xrev,
        convert (set.mem_image_of_mem (rev_at (nat_degree f)) gh), },
      { 
        intro,
        cases a,
        intro,
        sorry, }, },
  sorry,
end

#exit
#exit

lemma lead_trail_coeff {R : Type*} [semiring R] {f : polynomial R} : (at_infty f).coeff (at_infty f).nat_degree = f.coeff (nat_trailing_degree f) :=
begin
  by_cases h : f = 0,
    { rw [h, at_infty_zero,coeff_zero, coeff_zero], },
    { have fne : f.support.nonempty, by exact non_zero_iff.mpr h,
      have atfne : (at_infty f).support.nonempty,
        { apply non_zero_iff.mpr,
          apply (at_infty_nonzero_iff).mpr h, },
--      have : (at_infty f).degree = max (at_infty f).support,
      have : degree (at_infty f) = some (max' (at_infty f).support atfne),
        { unfold degree,
          ext1,
          rw option.mem_def,
          rw option.mem_def,
          split,
            intro,
            ext1,simp at *,split,intro,rw ← a_3,symmetry,
            have : option.get_of_mem (at_infty f).support.sup a = a,
            --apply congr_arg option.get,

            suggest,
--            refine option.mem_def,
            rw option.some_get,
          sorry, },
      have : (at_infty f).nat_degree = max' (at_infty f).support atfne,
        let atf := atfne,
        cases atfne with mi mih,
        


        unfold nat_degree,
        unfold degree,
        --unfold max',
        cases atfne, cases fne,
        --tidy,

        unfold at_infty,
        cases atfne, cases fne,
--        tidy?,
      sorry, },
end

#exit

lemma xxx {R : Type*} [comm_ring R] {f : polynomial R} {a : ℕ} : a ∈ (at_infty f).support → a ≤ nat_trailing_degree f :=
begin
  intro,
  have : rev_at f.nat_degree a ∈ f.support,
    exact supp_at_infty_of_supp.mp a_1,
  have : rev_at f.nat_degree a ≤ f.nat_degree,
    exact le_degree_of_mem_supp (rev_at (nat_degree f) a) this,
  
  
  
  sorry,
  
  unfold at_infty,
  unfold nat_trailing_degree,
  unfold nat_degree,
  unfold degree,
  unfold trailing_degree,
--  library_search,
--  tidy?,
end

#exit

lemma at_infty_nat_degree_le {R : Type*} [semiring R] {f : polynomial R} : (at_infty f).nat_degree ≤ (nat_degree f) :=
begin
  by_cases h : f = 0,
    { rw [h, at_infty_zero], },
    { have : coeff (at_infty f) (at_infty f).nat_degree = coeff f (nat_trailing_degree f),
        library_search,
      have : (at_infty f).support ⊆ finset.range (f.nat_degree + 1),
        intros a ah,
        
        apply supp_supp.mp,

        convert supp_supp,
--        library_search,
      sorry, },
end

#exit      
#print prefix fin
#check fin 0
#check subsingleton (fin 0)


example : subsingleton $ fin 0 := begin
 apply_instance,
end

--#print subsingleton_fin_zero

--lemma ss : subsingleton (fin 0) :=
--begin
-- apply_instance,
----  exact subsingleton_fin_zero,
--end

--#check f.nat_trailing_degree



lemma lead_trail_coeff {R : Type*} [comm_ring R] {f : polynomial R} : (at_infty f).coeff (at_infty f).nat_degree = f.coeff (nat_trailing_degree f) :=
begin
  
  sorry,
  
  unfold at_infty,
  unfold nat_trailing_degree,
  unfold nat_degree,
  unfold degree,
  unfold trailing_degree,
--  library_search,
--  tidy?,
end

#exit

lemma lead_trail_degree {R : Type*} [comm_ring R] {f : polynomial R} : (at_infty f).degree = trailing_degree f :=
begin
  by_cases h : f = 0,
    { rw h,
      rw at_infty_zero,
      refl, },
    { have : at_infty f ≠ 0,
        { intro,
          apply h,
          exact (at_infty_zero_iff.mp a), },
      have : ∀ a : ℕ , nat_trailing_degree f < a → (at_infty f).coeff a = 0,
        intros a ah,

        sorry,
      ext1,
      split,
        { intro,
          norm_num,
          sorry, },
        
      unfold trailing_degree,
      unfold degree,
      have : finset.max' (at_infty f).support (by exact non_zero_iff.mpr h) = finset.min' f.support (by exact non_zero_iff h),

      sorry, },
end


#exit


lemma degree_at_infty_le_degree {R : Type*} [semiring R] {f : polynomial R} : degree (at_infty f) ≤ degree f :=
begin
  by_cases h : f = 0,
    { rw [h, at_infty_zero, degree_zero],
      exact (le_refl _), },
    { rw [degree, degree],
      have : f.support.nonempty, by exact (non_zero_iff.mpr h),
      have : (at_infty f).support.nonempty, by exact at_infty_zero_iff
      have : (at_infty f).support.nonempty, by exact (non_zero_iff.mpr h),
      have : (at_infty f).1.max' this ≤ (f.nat_degree),
      have : (at_infty f).support ≤ finset.range (f.nat_degree + 1), by exact supp_bound,
      
      have : ∀ a : ℕ , nat_degree 
      intros a ah,

      use f.nat_degree,
      sorry, },
end

#exit

lemma degree_at_infty_le_degree {R : Type*} [semiring R] {f : polynomial R} : degree (at_infty f) ≤ degree f :=
begin
  by_cases h : f = 0,
    { rw [h, at_infty_zero, degree_zero],
      exact (le_refl _), },
    { rw [degree, degree],
      have : f.support.nonempty, by exact (non_zero_iff.mpr h),
      have : (at_infty f).support.nonempty, by exact at_infty_zero_iff
      have : (at_infty f).support.nonempty, by exact (non_zero_iff.mpr h),
      have : (at_infty f).1.max' this ≤ (f.nat_degree),
      have : (at_infty f).support ≤ finset.range (f.nat_degree + 1), by exact supp_bound,
      
      have : ∀ a : ℕ , nat_degree 
      intros a ah,

      use f.nat_degree,
      sorry, },
end



lemma supp_bound {R : Type*} [semiring R] {f : polynomial R} : (at_infty f).support ⊆ finset.range (nat_degree f + 1) :=
begin
  intros a ah,
  rw supp_supp at ah,
  by_cases h : nat_degree f < a,
    { sorry, },
    { push_neg at h,
      rw finset.mem_range,
      exact nat.lt_succ_iff.mpr h, },
end

#exit

--#check f.1.max'



def trailing_coeff {R : Type*} [semiring R] (f : polynomial R) : R := f.coeff (nat_trailing_degree f)


--lemma xx {R : Type*} [semiring R] {f : polynomial R} : leading_coeff (at_infty f) = trailing_coeff f :=
lemma xx {R : Type*} [semiring R] {f : polynomial R} : (at_infty f).coeff (at_infty f).nat_degree  = trailing_coeff f :=
begin
--  unfold leading_coeff,
  rw ← reversal_coeff_small,



  sorry,
end

#exit

lemma at_infty_zero_iff {R : Type*} [semiring R] {f : polynomial R} : f = 0 ↔ at_infty f = 0 :=
begin
  split,
    { intro,
      convert at_infty_zero, },
    { contrapose,
      intros a,
      apply (leading_coeff_nonzero_of_nonzero.mpr),

      
      sorry, }
end


lemma lead_trail_degree {R : Type*} [comm_ring R] {f : polynomial R} : (at_infty f).degree = trailing_degree f :=
begin
  by_cases h : f = 0,
    { rw h,
      rw at_infty_zero,
      refl, },
    { have : at_infty f ≠ 0,
        
      unfold trailing_degree,
      unfold degree,
      have : finset.max' (at_infty f).support (by exact non_zero_iff.mpr h) = finset.min' f.support (by exact non_zero_iff h),

      sorry, },
end


#exit




lemma xx {A B : Prop} : A ↔ B ↔ ¬A ↔ ¬ B :=
begin
  tauto,
end



lemma zero_coeff_iff {R : Type*} [semiring R] {f : polynomial R} {a : ℕ} : f.coeff a = 0 ↔ a ∉ f.support :=
begin
  split,
    { contrapose,
      push_neg,
      exact (f.3 a).mp, },
    { contrapose,
      push_neg,
      exact (f.3 a).mpr, },
end


lemma not_mem_support_of_coeff_eq_zero {R : Type*} [semiring R] {f : polynomial R} {a : ℕ} : f.coeff a = 0 → a ∉ f.support :=
begin
  contrapose,
  push_neg,
  exact (f.3 a).mp,
end

lemma xx {R : Type*} [semiring R] {f : polynomial R} {a : ℕ} {H : nat_degree f < a} : f.coeff a = 0 :=
begin
  have : a ∉ f.support,
    { sorry, },
  suggest,
  sorry,
end

#exit
#exit
#exit

lemma xx {a b : ℕ} : (a : ℤ) ≤ b → a ≤ b :=
begin
    exact int.coe_nat_le.mp,
end


lemma mem_rev_support_iff {R : Type*} [semiring R] {p : polynomial R} {a : ℕ} : a ∈ p.support ↔ ((rev_at p.nat_degree) a) ∈ (at_infty p).support :=
begin
    by_cases h : a ≤ nat_degree p,
      { sorry, },
      { simp only [not_le, finsupp.mem_support_iff, ne.def] at *, fsplit, work_on_goal 0 { intros a_1 a_2 }, work_on_goal 1 { intros a_1 a_2 },
        apply a_1,
        clear a_1,
        unfold rev_at at a_2,
        have : 1 ≤ a - p.nat_degree,
          apply nat.succ_le_iff.mpr,
          exact nat.sub_pos_of_lt h,
        have : min 1 (a - p.nat_degree) = 1,
          exact min_eq_left this,
        rw [this, mul_one] at a_2,
        have : p.nat_degree ≤ a,
            apply le_of_lt h,
        have : p.nat_degree - a = 0,
            exact nat.sub_eq_zero_of_le this,
        rw [this, zero_add] at a_2,


--        library_search,
        have : ((p.nat_degree - a) : int) ≤ 0,
            apply le_of_lt,
            apply sub_lt_of_sub_lt,
            rw sub_zero,
            norm_cast,
            exact h,
        have : p.nat_degree - a = 0,
            apply nat.eq_zero_of_le_zero,
            apply int.coe_nat_le.mp,
            norm_cast at *,
--            library_search,
--            library_search,
--            apply nat.eq_zero_of_le_zero this,
            
--        convert le_zero_iff_eq,suggest,


        sorry, },
end
#exit
  simp only [finsupp.mem_support_iff, ne.def] at *, fsplit, work_on_goal 0 { intros a_1 a_2 }, work_on_goal 1 { intros a_1 a_2 },
    { apply a_1,
      clear a_1,
      
      sorry, },
    { sorry, },
end


#exit



lemma rev_support_rev_support {R : Type*} [semiring R] (p : polynomial R) : ((rev_support (at_infty p)) : set ℕ) = (shift_support p (nat_trailing_degree p)) :=
begin
  ext1,
  unfold rev_support,
  unfold shift_support,

  sorry,
end

#exit
  ext1, fsplit, work_on_goal 0 { intros a, cases a, cases a_h, simp only [finsupp.mem_support_iff, ne.def] at *, fsplit, work_on_goal 1 { simp only [exists_prop, finsupp.mem_support_iff, ne.def] at *, fsplit, work_on_goal 0 { assumption } } }, work_on_goal 1 { intros a, cases a, cases a_h, simp only [finsupp.mem_support_iff, ne.def] at *, fsplit, work_on_goal 1 { simp only [exists_prop, finsupp.mem_support_iff, ne.def] at *, fsplit, work_on_goal 0 { intros a } } },
    { sorry, },
    { exact a_w, },
    { apply a_h_w,
      unfold at_infty at a,
      
      sorry, },
    { sorry, },
end

#exit



lemma at_infty_zero_iff {R : Type*} [semiring R] {f : polynomial R} : f=0 ↔ at_infty f = 0 :=
begin
  split,
    { intro,
      rw a,
      exact at_infty_zero, },
    { intro,
      have : (at_infty 0).support = ∅,
        unfold at_infty,
        injections_and_clear,
        hint,

      --tidy,
--      convert reversal_coeff,

      sorry, },
end

#exit
lemma lead_trail_degree {R : Type*} [comm_ring R] {f : polynomial R} : (at_infty f).degree = trailing_degree f :=
begin
  by_cases h : f = 0,
    { rw h,
      rw at_infty_zero,
      refl, },
    { unfold trailing_degree,
      unfold degree,
      have : finset.max' (at_infty f).support (by exact non_zero_iff.mpr h) = finset.min' f.support (by exact non_zero_iff h),

      sorry, },
end

#exit

theorem lead_trail {R : Type*} [comm_ring R] {f : polynomial R} : nat_degree (at_infty f) = nat_trailing_degree f :=
begin
  by_cases H : f = 0,
    { rw H,
      rw at_infty_zero,
      refl, },
    { unfold nat_degree,
      unfold nat_trailing_degree,
      have : (at_infty f).degree = trailing_degree f,
        { sorry, },
      solve_by_elim,
      sorry, },
end

#exit


lemma reversal_coeff {R : Type*} [comm_ring R] {f : polynomial R} : ∀ a : ℕ , coeff f a = coeff (at_infty f) (nat_degree f - a) :=
begin
    intro,
    let scambio : set ℕ := {x : ℕ | ∃ xx ∈ f.1 , x = nat_degree f - xx},
    have : {x : ℕ | ∃ xx ∈ f.1 , x = nat_degree f - xx}.finite,
        {refine finset_of_bounded (nat_degree f),
        intros n hn,
        cases hn with xx xxh,
        cases xxh with xsu xid,
        rw xid,
        have : 0 ≤ xx, by exact zero_le xx,
        exact (nat_degree f).sub_le xx,},
    have : (at_infty f).1 = this.to_finset,
        ext,
        split,
            {intro,
            simp at *,use f.nat_degree -a_1,
            split,
                {intro,apply a_2,clear this a_2 scambio a,unfold at_infty,
                revert a_1,
                --suggest,
                 sorry,},
--                {intro,apply a_2,tidy, sorry,},
                {sorry,},},
            {sorry,},

--    unfold at_infty,
--    tidy,
--    tidy,
    let an : ℕ := nat_degree f - a,
    have : a = nat_degree f - an,
        {sorry,},
    rw this,
    conv_rhs {rw ← mul_neg_one (f.nat_degree - an), rw sub_add_eq_sub_sub,},
--    tidy,
--    apply congr coeff,
--    ring,

--    split,
--        {intro,unfold at_infty,
--        have : (∑ (i : ℕ) in finset.range f.nat_degree, C (f.coeff i) * X ^ (f.nat_degree - i)).support = finset.range f.nat_degree,
--            unfold_coes,
        --refine set.mem_def.mpr _,
        --simp * at *,tidy,
--        sorry,},
        {sorry,},
end

--#exit

lemma supp_infty {R : Type*} [comm_ring R] {f : polynomial R} : ∀ a : ℕ , (f.2 a = (at_infty f).2 (nat_degree f - a)) :=
begin
    intro,
    unfold at_infty,

--    split,
--        {intro,unfold at_infty,
--        have : (∑ (i : ℕ) in finset.range f.nat_degree, C (f.coeff i) * X ^ (f.nat_degree - i)).support = finset.range f.nat_degree,
--            unfold_coes,
        --refine set.mem_def.mpr _,
        --simp * at *,tidy,
--        sorry,},
        {sorry,},
end

lemma leading_to_constant {R : Type*} [comm_ring R] {f : polynomial R} : coeff f (nat_degree f) = coeff (at_infty f) 0 :=
begin
    unfold at_infty,
--    suggest,
--    tidy,
    sorry,
end


--#check at_infinity

--#exit


lemma non_zero_at_infty_iff_non_zero {R : Type*} [comm_ring R] {f : polynomial R} : f ≠ 0 ↔ at_infty f ≠ 0 :=
begin
    split,
        {intro,apply non_zero_iff.mp,use 0,
        have : leading_coeff f = coeff (at_infty f) 0,
            unfold at_infty,
            --tidy,
        sorry,},
end


--#check at_infinity

--#exit

-/

lemma two_mons {R : Type u} [comm_ring R] {f : polynomial R} {fnz : f ≠ 0} {sn1 :  ¬ f.support.card = 1} : 2 ≤ f.support.card :=
begin
    have fne : f.support.nonempty, by exact non_zero_iff.mpr fnz,
    have fge0 : 0 ≤ f.support.card, by exact zero_le f.support.card,
    have fn0 : f.support.card ≠ 0,
        apply finset.card_ne_zero_of_mem,
        exact f.support.min'_mem fne,
    have fn1 : f.support.card ≠ 1,
        exact sn1,
    let N : ℕ := f.support.card,
    have Nn0 : N ≠ 0,
        exact fn0,
    have Nn1 : N ≠ 1,
        exact fn1,
    have : ∃ a : ℕ , a.succ.succ = N,
        use N-2,
        omega,
    have : 2 ≤ N,
        apply nat2,
        split;{assumption,},
    assumption,
end



--#exit
lemma one_monomial {K : Type u} [field K] {f g h : (polynomial K)} {pro : f=g*h} : finset.card f.1 = 1 → finset.card g.1 = 1 :=
begin
    intro fip,
    have fne : f ≠ 0,
        apply non_zero_iff.mp,
        refine finset.card_pos.mp _,
        rw fip,
        exact nat.one_pos,
    revert fip,
    have gne : g ≠ 0,
        rw pro at fne,
        exact left_ne_zero_of_mul fne,
    have hne : h ≠ 0,
        rw pro at fne,
        exact right_ne_zero_of_mul fne,

    have lcg : coeff g (nat_degree g) ≠ 0,
        apply leading_coeff_nonzero_of_nonzero.mp gne,
    contrapose,
    intro gip,
    have : ¬ g.support.card = 0,
        intro,
        apply lcg,
        apply leading_coeff_eq_zero.mpr,
        finish,
    have gge2 : 2 ≤ g.support.card,
        apply nat2,
        split;{assumption,},
    have gnempty : g.support.nonempty, by exact non_zero_iff.mpr gne,
    have hnempty : h.support.nonempty, by exact non_zero_iff.mpr hne,
    let gmin : ℕ := finset.min' g.1 gnempty,
    let gmax : ℕ := finset.max' g.1 gnempty,
    let hmin : ℕ := finset.min' h.1 hnempty,
    let hmax : ℕ := finset.max' h.1 hnempty,
    have : leading_coeff (f) ≠ 0,
        finish,
    let ginfty : polynomial K := (at_infty g),
    let hinfty : polynomial K := (at_infty h),
    have : g.2 (finset.min' g.1 gnempty) = (at_infty g).2 ((finset.max' g.1 gnempty)-(finset.min' g.1 gnempty)),
        { unfold at_infty,norm_num,suggest,sorry,},
--    have : leading_coeff ginfty = coeff g gmin,
--        { simp * at *,unfold at_infty,sorry,},
--    have : leading_coeff ginfty ≠ 0,
--        {apply leading_coeff_nonzero_of_nonzero.mp,
----        apply non
--            sorry,
--        },
--    have : leading_coeff (ginfty*hinfty) ≠ 0,


    sorry,
end
#exit
    have : coeff (g*h) (gmin+hmin) = (coeff g (gmin)) * (coeff h (hmin)),
        finish,
    have : finset.nat.antidiagonal (gmin + hmin) = {⟨ gmin , hmin ⟩},
--        suggest,

        rw coeff_mul g h (gmin+hmin),



--    have fmin : coeff f (gmin*hmin) ≠ 0,
--        apply coeff_mul (g h gmin*hmin),
    --    have : ↑M = nat_degree g,
--        exact degree_eq_iff_nat_degree_eq gne,
    -- g.support.nonempty,


--    have : ∃ a : ℕ , (f.1) = {a},
--        apply finset.card_eq_one.mp fip,
--    cases this with N Nh,
--    let a : K := leading_coeff f,
--    let a : K := f.2 N,
--    have : f.2 N ≠ 0,
--        apply (f.3 N).mp,
--        rw Nh,
--        exact finset.mem_singleton.mpr rfl,

--    intro,
--    contrapose,
--    intro hip,
--        intro fip,
--        apply hip,

end

#exit
λ poly, ∑ i in range (nat_degree poly), coeff i poly * X ^ (i - N)
N = multiplicity x f

let N := enat.get (multiplicity X f) _
obtain ⟨g, hg⟩ : X ^ N ∣ f := pow_multiplicity_dvd _,
(factors x).card






lemma gdivmon {N : ℕ} {K : Type u} [field K] {g : (polynomial K)} (gdiv : g ∣ (X^N)) : g = (C (leading_coeff g))*X^(nat_degree g) :=
begin
    have gne0 : g ≠ 0,
    intro,
    rw a at gdiv,
    cases gdiv,
    rw zero_mul at gdiv_h,
    have : X^N ≠ (0 : polynomial K),
        induction N with N hN,
            {
                simp * at *,
            },
            {
                rw nat.succ_eq_add_one,
                rw pow_succ,
                rw ← mul_zero X,
                intro,
                apply hN,
                apply (mulinj X).mp,
                exact a_1,
                exact integral_domain.to_is_integral_domain (polynomial K),
                exact X_ne_zero,
                apply (mulinj X).mp,
                exact a_1,
                exact integral_domain.to_is_integral_domain (polynomial K),
                exact X_ne_zero,
            },
        apply this,
        exact gdiv_h,
-- forse non serve separare i casi?
    by_cases (nat_degree g = 0),
        {
            simp * at *,
            have : g.leading_coeff = g.coeff (nat_degree g), by exact rfl,
            rw h at this,
            rw this,
            apply eq_C_of_degree_eq_zero,
            apply (degree_eq_iff_nat_degree_eq gne0).mpr,
            exact h,
        },
        {
            let Ix : ideal (polynomial K) := ideal.span ({X} : set (polynomial K)),
            have : is_maximal (Ix),
                refine principal_ideal_ring.is_maximal_of_irreducible _,
                exact irreducible_X,
            --have : X^N ∈ Ix,
--        suggest,
--        refine is_maximal.is_prime _,
            sorry,
        },
end

#exit



--#check nat_degree
--#print degree
--#print is_integral_domain



variables {K : Type u} [field K]
variables I : ideal (polynomial K)

variables u : K
#print is_unit
#check units.mk



--#exit
lemma invunit {u : K} : is_unit u → is_unit u⁻¹ :=
begin
    intro uh,
    cases uh with uu uv,
    use uu⁻¹,
    rw ← uv,
    exact units.coe_inv' uu,
end



lemma gen_unit_incl {x y : R} : is_unit y → ((submodule.span R ({x} : set R)).1 ⊆ (submodule.span R ({y*x} : set R)).1) :=
begin
    let Rx : submodule R R := (submodule.span R ({x} : set R)),
    have Rxp : submodule.is_principal Rx,
        refine {principal := _},
        use x,
--    let xex : R :=submodule.is_principal.generator Rx,
    let Ryx : submodule R R := (submodule.span R ({y*x} : set R)),
    have Ryxp : submodule.is_principal Ryx,
        refine {principal := _},
        use y*x,
    intro hip,
    cases hip with yi yiv,
    have invs : ↑(yi⁻¹)*(↑yi)=(1 : R),
        exact units.inv_mul yi,
    have prinv : x = ↑(yi⁻¹) * (y*x),
        rw ← mul_assoc,
        rw ← yiv,
        rw invs,
        rw one_mul,
    intros z zh,
    have : ∃ s : R , s • x = z,
        rw ← submodule.mem_span_singleton,
        exact zh,
    cases this with r rh,
    have : z = (r*↑ yi⁻¹) • (yi*x),
--Johan suggests trying with simp
        rw smul_eq_mul,
        rw mul_assoc,
        rw ← mul_assoc _ _ x,
        rw units.inv_mul,
        rw one_mul,
        symmetry,
        exact rh,
    rw yiv at this,
    rw this,
    apply submodule.mem_span_singleton.mpr,
    use r * ↑yi⁻¹,
end

lemma gen_unit_eq {x y : R} : is_unit y → ((submodule.span R ({x} : set R)) = (submodule.span R ({y*x} : set R))) :=
begin
    intro hip,
    ext1,
    split,
        {
            apply gen_unit_incl,
            exact hip,
        },
        {
            cases hip with yi yip,
            have : x = (↑yi⁻¹)*↑yi*x,
                rw units.inv_mul,
                rw one_mul,
            intro hx,
            rw mul_assoc at this,
            rw this,
            apply gen_unit_incl,
                exact is_unit_unit yi⁻¹,
            rw yip,
            exact hx,
        },
end


lemma pii {H : I ≠ ⊥}: ∃ p : polynomial K , monic p ∧ I = span {p} :=
begin
    have piI : submodule.is_principal I,
        exact is_principal_ideal_ring.principal I,
    let p1 : polynomial K := submodule.is_principal.generator I,
    have Igen : submodule.span (polynomial K) {p1} = I,
        exact submodule.is_principal.span_singleton_generator I,
        symmetry' at Igen,
    let lc : K := coeff p1 (nat_degree p1),
    have lcu : is_unit (lc),
        refine is_unit_iff_ne_zero.mpr _,
        intro p10,
        apply H,
        have : p1=0,
            apply leading_coeff_eq_zero.mp,
            exact p10,
            rw Igen,
            apply span_eq_bot.mpr,
            rw this,
            intro x,
            exact set.mem_singleton_iff.mp,
    have lci : is_unit (lc⁻¹),
        exact invunit lcu,
    use p1*(C lc⁻¹),
    split,
        {
            apply monic_mul_leading_coeff_inv,
            intro,
            apply H,
            rw a at Igen,
            rw Igen,
            rw submodule.span_singleton_eq_bot,
        },
        {
            rw mul_comm,
            rw Igen,
            apply gen_unit_eq,
            apply is_unit_C.mpr,
            exact lci,
        },
end

lemma divis {N : ℕ} : ∀ (I : ideal (polynomial K)) , (I ≠ ⊥) → (X^N ∈ I) → ∃ k : ℕ , I = span {X^k} :=
begin
    intros I Ih xn,
    have : ∃ p : polynomial K , monic p ∧ I = span {p},
        apply pii,
        exact Ih,
    cases this with p pc,
    have : submodule.is_principal I,
        exact is_principal_ideal_ring.principal I,
    let g : polynomial K := submodule.is_principal.generator I,
    let I1 := submodule.span (polynomial K) ({g} : set (polynomial K)),
    have II1 : I1 = I,
        exact submodule.is_principal.span_singleton_generator I,
    have impli : X^N ∈ I1 → ∃ r : (polynomial K), X^N = r • g,
    --∃ h : polynomial K , X^N = h • g,
        rw submodule.mem_span_singleton,
        simp only [eq_comm],
        exact id,
    have gdivN : g ∣ X^N,
        exact (submodule.is_principal.mem_iff_generator_dvd I).mp xn,
    have : g = (C (leading_coeff g))*X^(nat_degree g),
        library_search,

    have : (∃ (r : polynomial K), X ^ N = r • g),
        apply impli,
        rw II1,
        exact xn,
--    use nat_degree p,
    sorry,
end


#exit

lemma divis {N : ℕ} : ∀ (I : ideal (polynomial K)) , (I ≠ ⊥) → (X^N ∈ I) → ∃ k : ℕ , I = span {X^k} :=
begin
    intros I In0 hX,
    have piI : submodule.is_principal I,
        exact is_principal_ideal_ring.principal I,
    let p1 : polynomial K := submodule.is_principal.generator I,
    let p : polynomial K := p1 * C ((coeff p1 (nat_degree p1))⁻¹),
    have : monic p,
        apply monic_mul_leading_coeff_inv,
        intro p1h,
        simp * at *,
        have : I = span {p1},
--            suggest,



--    cases hX with a b,
    induction N with N hN,
        {
            use 0,
            simp * at *,
            apply eq_top_of_is_unit_mem,
            exact hX,
            exact is_unit_one,
        },
        {

            sorry,
        },
end
#exit

            by_cases (∃ (q : polynomial R), p=q*X),
                {
                    cases h with q qh,
                    rw qh at hX,
                    have hX1 : (ideal.span {p}).1 = set.range (λ (x : (polynomial R)), x • p), by exact submodule.span_singleton_eq_range p,
                    simp * at hX1,
                    have hXn : X^N.succ ∈ (span {q * X}).carrier, by assumption,
                    have : X^N.succ ∈ set.range (λ (x : polynomial R), x * (q * X)),
                        {
                            rw ← hX1,
                            exact hXn,
                        },
                    cases this with r rh,
                    simp at rh,
                    rw nat.succ_eq_add_one at rh,
                    rw pow_succ at rh,
                    rw mul_comm X (X^N) at rh,
                    rw ← mul_assoc r q X at rh,
                    rw mul_comm (r*q) X at rh,
                    rw mul_comm (X^N) X at rh,
                    have rh1 : (r * q) = X ^ N,
                        rw ← mulinj X,
                        exact rh,
                        exact integral_domain.to_is_integral_domain (polynomial R),
                        exact X_ne_zero,
                    have : X ^ N ∈ span {q},
                        {
                            rw ← rh1,
                            refine submodule.smul_mem _ _ _,
                            exact set.has_singleton,
                            apply submodule.subset_span,
                            exact set.mem_singleton q,
                        },
                    revert p,
                    have dom : no_zero_divisors (polynomial R), by exact domain.to_no_zero_divisors,
                    have : r * q = X ^ N,
                        {
                            apply mulinj X,
                            exact rh,
                            exact dom,

                            sorry,
                        },

                    rw hX1 at hX,
                    have hX2 : X ^ N.succ ∈ set.range (λ (x : (polynomial R)), x • p),
                        {
                            refine set.mem_Inter.mp _ (λ (x : polynomial R), x • p),
                            symmetry' at hX1,
--                            suggest,
                            sorry,
                        },
--                    have hX3 : ∃ (q : polynomial R) , q*p = X ^ N.succ,
--                        {
--
--                            sorry,
--                        },


                    sorry,
                },
                {
                    sorry,
                },
        },
end



#exit
lemma divis {R : Type u} [field R] {p : polynomial R} {N : ℕ} : (X^N : polynomial R) ∈ (ideal.span {p} : ideal (polynomial R)) → ∃ k : ℕ , ∃ a : units (polynomial R) , (p) = (a.1*X^k) :=
begin
    intro hX,
    induction N with N hN,
        {
            use 0,
            simp *,
            have trid : span {p} = ⊤,
                {
                    apply eq_top_of_is_unit_mem,
                    exact hX,
                    exact is_unit_one,
                },
            have uni : is_unit p,
            {
                apply span_singleton_eq_top.mp,
                exact trid,
            },
            cases uni with pi pip,
            use pi,
            rw ← pip,
            refl,
        },
        {
            by_cases (∃ (q : polynomial R), p=q*X),
                {
                    cases h with q qh,
                    rw qh at hX,
                    have hX1 : (ideal.span {p}).1 = set.range (λ (x : (polynomial R)), x • p), by exact submodule.span_singleton_eq_range p,
                    simp * at hX1,
                    have hXn : X^N.succ ∈ (span {q * X}).carrier, by assumption,
                    have : X^N.succ ∈ set.range (λ (x : polynomial R), x * (q * X)),
                        {
                            rw ← hX1,
                            exact hXn,
                        },
                    cases this with r rh,
                    simp at rh,
                    rw nat.succ_eq_add_one at rh,
                    rw pow_succ at rh,
                    rw mul_comm X (X^N) at rh,
                    rw ← mul_assoc r q X at rh,
                    rw mul_comm (r*q) X at rh,
                    rw mul_comm (X^N) X at rh,
                    have rh1 : (r * q) = X ^ N,
                        rw ← mulinj X,
                        exact rh,
                        exact integral_domain.to_is_integral_domain (polynomial R),
                        exact X_ne_zero,
                    have : X ^ N ∈ span {q},
                        {
                            rw ← rh1,
                            refine submodule.smul_mem _ _ _,
                            exact set.has_singleton,
                            apply submodule.subset_span,
                            exact set.mem_singleton q,
                        },
                    revert p,
                    have dom : no_zero_divisors (polynomial R), by exact domain.to_no_zero_divisors,
                    have : r * q = X ^ N,
                        {
                            apply mulinj X,
                            exact rh,
                            exact dom,

                            sorry,
                        },

                    rw hX1 at hX,
                    have hX2 : X ^ N.succ ∈ set.range (λ (x : (polynomial R)), x • p),
                        {
                            refine set.mem_Inter.mp _ (λ (x : polynomial R), x • p),
                            symmetry' at hX1,
--                            suggest,
                            sorry,
                        },
--                    have hX3 : ∃ (q : polynomial R) , q*p = X ^ N.succ,
--                        {
--
--                            sorry,
--                        },


                    sorry,
                },
                {
                    sorry,
                },
        },
end

#exit
    have : ∃ q : polynomial R , q*p = X^N, by exact mem_span_singleton'.mp hX,
    cases this with q qh,
    use N-nat_degree q,
    have : unique_factorization_domain (polynomial R), by exact principal_ideal_ring.to_unique_factorization_domain,
    tidy,
    let ff := associates.factor_set X^N,
    sorry,

lemma nilp2 {R : Type u} [field R] (M : matrix n n R) : (∃ N : ℕ , M^N = 0) → M^(fintype.card n) = 0 :=
begin
    intro hp,
    cases hp with N hN,
--    let chiM : polynomial R := char_poly M,
    let gens := {p : polynomial R | eval M (map (algebra_map R (matrix n n R)) p) = 0},
    let I : ideal (polynomial R) :=  span gens,
--    have PID : is_principal_ideal_ring (polynomial R), by exact euclidean_domain.to_principal_ideal_domain,
--    have PII : submodule.is_principal I, by exact is_principal_ideal_ring.principal I,
    let minpol := submodule.is_principal.generator I,
    have IPI : submodule.span (polynomial R) {minpol} = I, by exact submodule.is_principal.span_singleton_generator I,
    rw IPI at *,
    have XN0 : ((X^N).map (algebra_map R (matrix n n R))).eval M = 0,
        {
            sorry,
--            unfold eval,
--            finish,
        },
    have XNg : X^N ∈ gens, by assumption,
    have XNI : X^N ∈ I, by exact submodule.subset_span XNg,
    have divi : ∃ pol : polynomial R , pol*minpol = X^N,
        {
            refine submodule.mem_span_singleton.mp _,
            rw IPI,
            exact XNI,
        },
    cases divi with pof pofh,
    have : minpol = X^(N-nat_degree pof),
        {
--            hint,
            sorry,
        },
    have cp0 : ((char_poly M).map (algebra_map R (matrix n n R))).eval M = 0,
        {
            apply char_poly_map_eval_self,
        },
    have cpg : char_poly M ∈ gens, by assumption,
    have cpI : char_poly M ∈ I, by exact submodule.subset_span cpg,
--    rw IPI at cpI,
    have : nat_degree minpol ≤ nat_degree (char_poly M),
        {
            sorry,
        },
    sorry,
end
#exit


lemma nilp {R : Type u} [comm_ring R] (M : matrix n n R) : (∃ N : ℕ , M^N = 0) ↔ M^(fintype.card n) = 0 :=
begin
    split,
        {
            intro hp,
            cases hp with N hN,
            let chiM : polynomial R := char_poly M,
            --let mend := matrix.to_lin M,
--            let End := linear_map.endomorphism_ring ,
            let A := algebra.adjoin_eq_span {M},

            sorry,
        },
        {
            intro,
            use fintype.card n,
            assumption,
        },
end
--char_poly
#exit

--noncomputable def Cstar := prime_spectrum.comap (polynomial.C : R →+* polynomial R)
def Spec_Rx := prime_spectrum (polynomial R)
def D_f {R : Type u} [comm_ring R] (r : R) := ((zero_locus {r})ᶜ : set (prime_spectrum R))
def V_f {R : Type u} [comm_ring R] (r : R) := ((zero_locus {r})  : set (prime_spectrum R))
--def free (R : Type u) [comm_ring R] (n : ℕ) := direct_sum {i : ℕ // i ≤ n} (λ i , R)
def free (R : Type u) [comm_ring R] (n : ℕ) := semimodule R (direct_sum {i : ℕ // i ≤ n} (λ (i : {i : ℕ // i ≤ n}), R))

section Rx2Rclosed

-- {M : Type u} {n : ℕ} {β : {i : ℕ | i ≤ n} → Type u} (df : β := λ i : {i : ℕ | i ≤ n} , R)} [add_comm_group M] {h : semimodule R M}
#check (free R n : Type u)
#check semimodule R R
def R1 (R : Type u) [comm_ring R] := (semimodule R R : Type u)
#check R1 R

lemma pr : R1 R = free R 1 :=
begin
    sorry,
end

#print semimodule


variables (f : (free R n) →ₗ[R] (free R n))
#check (linear_map f : (free R n) → (free R n))
#print linear_map


lemma vect {R : Type u} [comm_ring R] [integral_domain R] {n : ℕ} (f : (free R n) → (free R n)) (H : linear_map.is_linear (f : (free R n) →ₗ[R] (free R n))):=
-- (f : linear_map R (free n) (free n)) : true := sorry,-- (linear_map f) :




#exit

lemma radbound {R : Type u} [comm_ring R] {f g : polynomial R} {mon : monic g} :
 (f ∈ ((radical (ideal.span {g})).1 : set (polynomial R))) ↔ (f^(nat_degree g) ∈ ((ideal.span {g}).1 : set (polynomial R))) :=
begin
    split,
        {
            let quo : Type u := ideal.quotient (ideal.span {g} : ideal (polynomial R)),
            sorry,
        },
        {
            intro fh,
            exact ⟨g.nat_degree,fh⟩,
        },
end


lemma mapsto {R : Type u} [comm_ring R] {f g : polynomial R} {mon : monic g} (P : prime_spectrum (polynomial R)) :
 (f ∉ P.1 ∧ g ∈ P.1) → ∃ i : {n | n < nat_degree g} , (coeff (mod_by_monic (f^(nat_degree g)) g) i) ∉ (Cstar P).1 :=
begin
    intro,
    cases a, cases P,

    sorry,
end


lemma controllo {R : Type u} [comm_ring R] {f g : polynomial R} {mon : monic g} (P : prime_spectrum (polynomial R)) :
 image_of_Df (mod_by_monic (f^(nat_degree g)) g) = (⋃ i : {n | n < nat_degree g} , D_f (coeff (mod_by_monic (f^(nat_degree g)) g) i)) :=
begin
--    tidy,
    dsimp at *,
    unfold image_of_Df,
--    suggest,
    sorry,
end


lemma proclosed {R : Type u} [comm_ring R] {f g : polynomial R} {mon : monic g} :
 Cstar '' (D_f f ∩ V_f g) = (⋃ i : {n | n < nat_degree g} , D_f (coeff (mod_by_monic (f^(nat_degree g)) g) i)) :=
begin
--    hint,
    sorry,
end
-- ((prime_spectrum.zero_locus {f} : set Spec_Rx) ⋂ (prime_spectrum.zero_locus {g} : set Spec_Rx)) = ∅ :=

lemma proclosed1 {R : Type u} [comm_ring R] {f g : polynomial R} {mon : monic g} :
 ∃ r : {n | n < nat_degree g} → R , Cstar '' (D_f f ∩ V_f g) = (⋃ i : {n | n < nat_degree g} , D_f (r i)) :=
begin
    sorry,
end



end Rx2Rclosed


--def reverse_coeffs {R : Type*} [comm_ring R] (p : polynomial R) {H : p ≠ 0} : polynomial R := begin
--    let rev : ℕ → ℕ := λ i , max 0 (nat_degree p - i),
--#check multiplicity
def shift_coeffs {R : Type*} [comm_ring R] (p : polynomial R) {H : p ≠ 0} : polynomial R := begin
    let mindegree : ℕ := (finset.min' p.1 (by exact non_zero_iff.mpr H)),
    let rev : ℕ → ℕ := λ i , i+mindegree,
    let revi : ℕ → ℕ := λ i , i-mindegree,

    refine ⟨ _ , _ , _ ⟩,
    {-- support
--        let revpsup : set ℕ := revi '' ({pp : ℕ | ∃ q ∈ p.1, pp = q}),
        have : (revi '' ({pp : ℕ | ∃ q ∈ p.1, pp = q})).finite,
            {apply finset_of_bounded (nat_degree p),
            intros n nr,
            rcases nr with ⟨ nr , nrh , ren⟩,
            rw ← ren,
            have subrevi : revi nr = nr -mindegree,by refl,
            rw subrevi,
            refine le_trans _ _ ,
                {use nr,},
                {exact nat.sub_le nr mindegree,},
                {rcases nrh with ⟨ nrn , nrnh , fff ⟩,
                rw fff,
                apply le_nat_degree_of_ne_zero,apply (p.mem_support_to_fun nrn).mp,assumption,},
            },
        exact this.to_finset,
    },
    {-- to_fun
--sono confuso: perché sono arrivato in R e non in N?
        use λ i , p.2 (rev i),
--        sorry,
    },
    {-- non-zero
        intros a,
        split,
            {intro,tidy,apply a_1_h_left,clear a_1_h_left,
            rw ← a_2,
            apply congr,
                {refl,},
                {have : rev (revi a_1_w) = revi a_1_w + mindegree,exact rfl,
                rw this,
                have : revi a_1_w = a_1_w - mindegree,exact rfl,
                rw this,--library_search,
                sorry,},
            have : revi a_1_w=a_1_w - mindegree,by exact rfl,
            rw this at a_2,
            have : a_1_w = 0,
            simp * at *,
            sorry,},
            {sorry,},
    },
end

--lemma trailing_degree {K : Type*} [field K] {f : polynomial K} {H : f ≠ 0} : leading_coeff reverse

