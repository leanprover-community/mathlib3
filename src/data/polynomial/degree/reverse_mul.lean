import tactic
import data.polynomial.degree.basic
import data.polynomial.degree.trailing_degree
import logic.function.basic
import algebra.big_operators.basic


open_locale big_operators
open_locale classical

open function polynomial finsupp finset

namespace reverse

variables {R : Type*} [semiring R] {f : polynomial R}

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

lemma coeff_eq_zero_of_not_mem_support {a : ℕ} : a ∉ f.support → f.coeff a = 0 :=
begin
  contrapose,
  push_neg,
  exact mem_support_iff_coeff_ne_zero.mpr,
end

lemma leading_coeff_nonzero_of_nonzero : f ≠ 0 ↔ leading_coeff f ≠ 0 :=
begin
  exact not_congr leading_coeff_eq_zero.symm,
end

lemma mem_support_term {n a : ℕ} {c : R} : a ∈ (C c * X ^ n).support → a = n :=
begin
  intro,
  rw [mem_support_iff_coeff_ne_zero, coeff_C_mul_X c n a] at a_1,
  finish,
end

lemma support_term (c : R) (n : ℕ) : (C c * X ^ n).support ⊆ singleton n :=
begin
  intro a,
  rw mem_singleton,
  exact mem_support_term,
end

lemma card_support_term_le_one {c : R} {n : ℕ} : (C c * X ^ n).support.card ≤ 1 :=
begin
  rw ← card_singleton n,
  apply card_le_of_subset,
  exact support_term c n,
end

lemma nat_degree_mem_support_of_nonzero : f ≠ 0 → f.nat_degree ∈ f.support :=
begin
  intro,
  apply (f.3 f.nat_degree).mpr,
  exact leading_coeff_nonzero_of_nonzero.mp a,
end

lemma le_nat_degree_of_mem_supp (a : ℕ) :
  a ∈ f.support → a ≤ nat_degree f:=
begin
  rw mem_support_iff_coeff_ne_zero,
  exact le_nat_degree_of_ne_zero,
end

lemma le_degree_of_mem_supp (a : ℕ) :
  a ∈ f.support → a ≤ nat_degree f :=
begin
  rw mem_support_iff_coeff_ne_zero,
  exact le_nat_degree_of_ne_zero,
end

lemma non_zero_of_nonempty_support : f.support.nonempty → f ≠ 0 :=
begin
  intro,
  cases a with N Nhip,
  rw mem_support_iff_coeff_ne_zero at Nhip,
  finish,
end

lemma nonempty_support_of_non_zero : f ≠ 0 → f.support.nonempty :=
begin
  intro fne,
  rw nonempty_iff_ne_empty,
  apply ne_empty_of_mem,
  rw mem_support_iff_coeff_ne_zero,
  exact leading_coeff_nonzero_of_nonzero.mp fne,
end

lemma non_zero_iff : f.support.nonempty ↔ f ≠ 0 :=
begin
  split,
    { exact non_zero_of_nonempty_support, },
    { exact nonempty_support_of_non_zero, },
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

lemma support_term_nonzero {c : R} {n : ℕ} (h : c ≠ 0): (C c * X ^ n).support = singleton n :=
begin
  ext1,
  rw mem_singleton,
  split,
    { exact mem_support_term, },
    { intro,
      rwa [mem_support_iff_coeff_ne_zero, ne.def, a_1, coeff_C_mul, coeff_X_pow_self n, mul_one], },
end

@[simp] lemma nat_degree_monomial {a : R} (n : ℕ) (ha : a ≠ 0) : nat_degree (C a * X ^ n) = n :=
begin
  rw defs_by_Johann,
    { simp_rw support_term_nonzero ha,
      exact max'_singleton n, },
    { intro,
      apply ha,
      rw [← C_inj, C_0],
      apply mul_X_pow_eq_zero a_1, },
end

lemma nat_degree_term_le (a : R) (n : ℕ) : nat_degree (C a * X ^ n) ≤ n :=
begin
  by_cases a0 : a = 0,
    rw [a0, C_0, zero_mul, nat_degree_zero],
    exact nat.zero_le _,


    rw defs_by_Johann,
      { simp_rw [support_term_nonzero a0, max'_singleton n], },
      { intro,
        apply a0,
        rw [← C_inj, C_0],
        apply mul_X_pow_eq_zero a_1, },
end


@[simp] lemma trailing_coeff_eq_zero : trailing_coeff f = 0 ↔ f = 0 :=
⟨λ h, by_contradiction $ λ hp, mt mem_support_iff.1
  (not_not.2 h) (mem_of_min (trailing_degree_eq_nat_trailing_degree hp)),
λ h, h.symm ▸ leading_coeff_zero⟩

lemma trailing_coeff_nonzero_of_nonzero : f ≠ 0 ↔ trailing_coeff f ≠ 0 :=
begin
  apply not_congr trailing_coeff_eq_zero.symm,
end


lemma nat_trailing_degree_mem_support_of_nonzero : f ≠ 0 → nat_trailing_degree f ∈ f.support :=
begin
  rw mem_support_iff_coeff_ne_zero,
  exact trailing_coeff_nonzero_of_nonzero.mp,
end

lemma nat_trailing_degree_le_of_mem_supp (a : ℕ) :
  a ∈ f.support → nat_trailing_degree f ≤ a:=
begin
  rw mem_support_iff_coeff_ne_zero,
  exact nat_trailing_degree_le_of_ne_zero,
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




noncomputable def remove_leading_coefficient (f : polynomial R) : polynomial R := (∑ (i : ℕ) in finset.range f.nat_degree, (C (f.coeff i)) * X^i)

@[simp] lemma coeff_remove_nat_degree : (remove_leading_coefficient f).coeff f.nat_degree = 0 :=
begin
  unfold remove_leading_coefficient,
  simp only [coeff_X_pow, mul_boole, not_mem_range_self, finset_sum_coeff, coeff_C_mul, if_false, finset.sum_ite_eq],
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

lemma sum_leading_term_remove (f : polynomial R) : f = (remove_leading_coefficient f) + (C f.leading_coeff) * X^f.nat_degree :=
begin
  ext1,
  by_cases nm : n = f.nat_degree,
    { rw [nm, coeff_add, coeff_C_mul, coeff_X_pow_self, mul_one, coeff_remove_nat_degree, zero_add],
      refl, },
    { simp only [*, coeff_remove_eq_coeff_of_ne nm, coeff_X_pow f.nat_degree n, add_zero, coeff_C_mul, coeff_add, if_false, mul_zero], },
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

lemma not_mem_of_not_mem_supset {a b : finset ℕ} (h : a ⊆ b) {n : ℕ} : n ∉ b → n ∉ a :=
begin
  apply mt,
  solve_by_elim,
end

@[simp] lemma support_remove_leading_coefficient_sub : (remove_leading_coefficient f).support ⊆ range f.nat_degree :=
begin
  unfold remove_leading_coefficient,
  intros a,
  simp_rw [mem_support_iff_coeff_ne_zero, (finset_sum_coeff (range (nat_degree f)) (λ (b : ℕ), C (coeff f b) * X ^ b) a), coeff_C_mul_X (f.coeff _) _ a],
  finish,
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

lemma mem_remove_leading_coefficient_of_mem_diff {a : ℕ} : a ∈ (f.support \ {f.nat_degree}) → a ∈ (remove_leading_coefficient f).support :=
begin
  rw [mem_sdiff, mem_support_iff_coeff_ne_zero, mem_support_iff_coeff_ne_zero, not_mem_singleton],
  intro,
  cases a_1 with fa asmall,
  rwa coeff_remove_eq_coeff_of_ne asmall,
end

lemma support_remove_leading_coefficient : (remove_leading_coefficient f).support = f.support \ {f.nat_degree} :=
begin
  by_cases f0 : f = 0,
    { rw f0,
      apply (support_eq_empty).mpr,
      refl, },
    { ext,
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
        { exact mem_remove_leading_coefficient_of_mem_diff, }, },
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
end

lemma support_remove_lt (h : f ≠ 0) : (remove_leading_coefficient f).support.card < f.support.card :=
begin
  rw support_remove_leading_coefficient,
  apply card_lt_card,
  split,
    { exact f.support.sdiff_subset {nat_degree f}, },
    { intro,
      rw defs_by_Johann h at a,
      have : f.support.max' (non_zero_iff.mpr h) ∈ f.support \ {f.support.max' (non_zero_iff.mpr h)} := a (max'_mem f.support (non_zero_iff.mpr h)),
      simp only [mem_sdiff, eq_self_iff_true, not_true, and_false, mem_singleton] at this,
      cases this, },
end

lemma add_cancel {a b : R} {h : a=0} : a+b=b :=
begin
  rw [h, zero_add],
end

lemma term_of_card_support_le_one (h : f.support.card ≤ 1) : f = C f.leading_coeff * X^f.nat_degree :=
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

lemma support_remove_leading_coefficient_lt (h : f ≠ 0) : (remove_leading_coefficient f).support.card < f.support.card :=
begin
  apply card_lt_card,
  rw [support_remove_leading_coefficient, ssubset_iff_of_subset],
    { use f.nat_degree,
      rw [← mem_sdiff, sdiff_sdiff_self_left, inter_singleton_of_mem, mem_singleton],
      rw mem_support_iff_coeff_ne_zero,
      exact leading_coeff_nonzero_of_nonzero.mp h, },
    { exact f.support.sdiff_subset {nat_degree f}, },
end

lemma remove_leading_coefficient_monomial {r : R} {n : ℕ} : remove_leading_coefficient (C r * X^n) = 0 :=
begin
  by_cases h : r = 0,
    { rw [h, C_0, zero_mul],
      refl, },
    { rw [← support_eq_empty, ← sdiff_self (singleton n), support_remove_leading_coefficient],
      congr,
        { exact support_term_nonzero h, },
        { exact nat_degree_monomial n h, }, },
end

lemma remove_leading_coefficient_card : f.support.card ≤ 1 → (remove_leading_coefficient f) = 0 :=
begin
  intro,
  rw [term_of_card_support_le_one a, remove_leading_coefficient_monomial],
end

lemma nat_degree_remove_leading_coefficient_le : (remove_leading_coefficient f).nat_degree ≤ f.nat_degree :=
begin
  by_cases su : f.support.card ≤ 1,
    {
      rw [remove_leading_coefficient_card su, nat_degree_zero],
      exact zero_le f.nat_degree, },
    { apply le_of_lt,
      exact nat_degree_remove_leading_coefficient (nat.succ_le_iff.mpr (not_le.mp su)), },
end


def rev_at (N : ℕ) : ℕ → ℕ := λ i : ℕ , (N-i) + i*min 1 (i-N)

@[simp] lemma rev_at_invol {N n : ℕ} : rev_at N (rev_at N n) = n :=
begin
  unfold rev_at,
  by_cases n ≤ N,
  {
    simp [nat.sub_eq_zero_of_le (nat.sub_le N n),nat.sub_eq_zero_of_le h, nat.sub_sub_self h], },
  { rw not_le at h,
    simp [nat.sub_eq_zero_of_le (le_of_lt (h)), min_eq_left (nat.succ_le_of_lt (nat.sub_pos_of_lt h))], },
end

@[simp] lemma rev_at_small {N n : ℕ} (H : n ≤ N) : rev_at N n = N-n :=
begin
  unfold rev_at,
  rw [nat.sub_eq_zero_of_le H, min_eq_right (nat.zero_le 1), mul_zero, add_zero],
end


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

@[simp] lemma reflect_smul (N : ℕ) {r : R} : reflect N (C r * f) = C r * (reflect N f) :=
begin
  ext1,
  unfold reflect,
  simp only [coeff_mk, coeff_C_mul],
end

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

@[simp] lemma reflect_monomial (N n : ℕ) : reflect N ((X : polynomial R) ^ n) = X ^ (rev_at N n) :=
begin
  rw [← one_mul (X^n), ← one_mul (X^(rev_at N n)), ← C_1, reflect_term],
end

def reverse : polynomial R → polynomial R := λ f , reflect f.nat_degree f

lemma nat_degree_add_of_mul_leading_coeff_nonzero (f g: polynomial R) (fg: f.leading_coeff * g.leading_coeff ≠ 0) :
 (f * g).nat_degree = f.nat_degree + g.nat_degree :=
begin
  apply le_antisymm,
    { exact nat_degree_mul_le, },
    { apply le_nat_degree_of_mem_supp,
      rw mem_support_iff_coeff_ne_zero,
      convert fg,
      exact coeff_mul_degree_add_degree f g, },
end


lemma pol_ind_Rhom_prod_on_card (cf cg : ℕ) {rp : ℕ → polynomial R → polynomial R}
 (rp_add  : ∀ f g : polynomial R , ∀ F : ℕ ,
  rp F (f+g) = rp F f + rp F g)
 (rp_smul : ∀ f : polynomial R , ∀ r : R , ∀ F : ℕ ,
  rp F ((C r)*f) = C r * rp F f)
 (rp_mon : ∀ n N : ℕ , n ≤ N →
  rp N (X^n) = X^(N-n)) :
 ∀ N O : ℕ , ∀ f g : polynomial R ,
 f.support.card ≤ cf.succ → g.support.card ≤ cg.succ → f.nat_degree ≤ N → g.nat_degree ≤ O →
 (rp (N + O) (f*g)) = (rp N f) * (rp O g) :=
begin
  have rp_zero : ∀ T : ℕ , rp T (0 : polynomial R) = 0,
    intro,
    rw [← zero_mul (1 : polynomial R), ← C_0, rp_smul (1 : polynomial R) 0 T, C_0, zero_mul, zero_mul],
  induction cf with cf hcf,
  --first induction: base case
    { induction cg with cg hcg,
    -- second induction: base case
      { intros N O f g Cf Cg Nf Og,
        rw [term_of_card_support_le_one Cf, term_of_card_support_le_one Cg],
        rw [mul_assoc, X_pow_mul, mul_assoc, ← pow_add X],
        repeat {rw rp_smul},
        repeat {rw rp_mon},
        rw [mul_assoc, X_pow_mul, mul_assoc, ← pow_add X],
        congr,
        omega,
        repeat {assumption,},
        rw add_comm,
        exact add_le_add Nf Og, },
    -- second induction: induction step
      { intros N O f g Cf Cg Nf Og,
        by_cases g0 : g = 0,
          { rw [g0, mul_zero, rp_zero, rp_zero, mul_zero], },

          { rw [sum_leading_term_remove g, mul_add, rp_add, rp_add, mul_add],

            rw hcg N O f (remove_leading_coefficient g) Cf _ Nf _,
            rw hcg N O f (_) Cf _ Nf _,

            exact (le_add_left card_support_term_le_one),
            exact (le_trans (nat_degree_term_le g.leading_coeff g.nat_degree) Og),

            rw ← nat.lt_succ_iff,
            apply gt_of_ge_of_gt Cg _,
            apply support_remove_leading_coefficient_lt g0,

            exact le_trans nat_degree_remove_leading_coefficient_le Og, }, }, },

  --first induction: induction step
    { intros N O f g Cf Cg Nf Og,

      by_cases f0 : f=0,
        { rw [f0, zero_mul, rp_zero, rp_zero, zero_mul], },

        { rw [sum_leading_term_remove f, add_mul, rp_add, rp_add, add_mul],

          rw hcf N O (remove_leading_coefficient f) (g) _ Cg _ Og,
          rw hcf N O (_) (g) _ Cg _ Og,

          exact (le_add_left card_support_term_le_one),
          exact (le_trans (nat_degree_term_le f.leading_coeff f.nat_degree) Nf),

          rw ← nat.lt_succ_iff,
          apply gt_of_ge_of_gt Cf _,
          apply support_remove_leading_coefficient_lt f0,

          exact le_trans nat_degree_remove_leading_coefficient_le Nf, }, },
end

lemma pol_ind_Rhom_prod {rp : ℕ → polynomial R → polynomial R}
 (rp_add  : ∀ f g : polynomial R , ∀ F : ℕ ,
  rp F (f+g) = rp F f + rp F g)
 (rp_smul : ∀ f : polynomial R , ∀ r : R , ∀ F : ℕ ,
  rp F ((C r)*f) = C r * rp F f)
 (rp_mon : ∀ n N : ℕ , n ≤ N →
  rp N (X^n) = X^(N-n)) :
 ∀ N O : ℕ , ∀ f g : polynomial R ,
 f.nat_degree ≤ N → g.nat_degree ≤ O →
 (rp (N + O) (f*g)) = (rp N f) * (rp O g) :=
begin
  intros N O f g,
  apply pol_ind_Rhom_prod_on_card f.support.card g.support.card rp_add rp_smul rp_mon,
  exact f.support.card.le_succ,
  exact g.support.card.le_succ,
end

@[simp] theorem reflect_mul {f g : polynomial R} {F G : ℕ} (Ff : f.nat_degree ≤ F) (Gg : g.nat_degree ≤ G) :
 reflect (F+G) (f*g) = reflect F f * reflect G g :=
begin
  apply pol_ind_Rhom_prod,
    { apply reflect_add, },
    { intros f r F,
      rw reflect_smul, },
    { intros n N Nn,
      rw [reflect_monomial, rev_at_small Nn], },
    { assumption },
    { assumption },
end

theorem reverse_mul (f g : polynomial R) {fg : f.leading_coeff*g.leading_coeff ≠ 0} :
 reverse (f*g) = reverse f * reverse g :=
begin
  unfold reverse,
  convert reflect_mul (le_refl _) (le_refl _),
    exact nat_degree_add_of_mul_leading_coeff_nonzero f g fg,
end
end reverse
