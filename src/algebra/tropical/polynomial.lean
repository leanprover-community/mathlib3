/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import algebra.tropical.big_operators
import data.polynomial.eval
import data.polynomial.inductions
import data.real.basic

/-!

# Tropical polynomials

This file defines polynomials over tropical algebra structures.

-/

universes u v
variables {R S α : Type*}

open_locale big_operators

-- local notation `Rᵗ` := tropical (with_top R)
-- local notation `ℝᵗ` := tropical (with_top ℝ)

section big_operators

open tropical

namespace polynomial

variables [semiring R]

def eval_eq (p q : polynomial R) : Prop :=
∀ x : R, eval x p = eval x q

lemma eval_eq_equivalence : equivalence (eval_eq : polynomial R → polynomial R → Prop) :=
⟨λ _ _, rfl, λ _ _ h _, (h _).symm, λ _ _ _ h h' _, (h _).trans (h' _)⟩

instance eval_setoid : setoid (polynomial R) :=
{ r := eval_eq,
  iseqv := eval_eq_equivalence }

lemma quot_eq_iff {p q : polynomial R} : ⟦p⟧ = ⟦q⟧ ↔ ∀ x : R, eval x p = eval x q :=
quotient.eq

@[simp] lemma erase_update_same (p : polynomial R) (n : ℕ) (a : R) :
  erase n (p.update n a) = p.erase n :=
begin
  ext,
  rw [coeff_erase, coeff_erase],
  split_ifs with h h;
  simp [coeff_update, h]
end

@[simp] lemma _root_.ite_ite_pos {α : Type*} (p : Prop) [decidable p] (f g h : α) :
  ite p (ite p f g) h = ite p f h :=
by split_ifs; refl

lemma erase_add (p q : polynomial R) (n : ℕ) :
  erase n (p + q) = erase n p + erase n q :=
begin
  ext i,
  simp_rw [coeff_add, coeff_erase],
  split_ifs;
  simp
end

@[simp] lemma erase_erase (p : polynomial R) (n : ℕ) :
  erase n (erase n p) = erase n p :=
begin
  ext,
  simp_rw coeff_erase,
  split_ifs;
  refl
end

lemma erase_nat_degree_lt (p : polynomial R) (i : ℕ) (hi : p.nat_degree < i) :
  p.erase i = p :=
begin
  ext,
  simp_rw coeff_erase,
  split_ifs with h h,
  { simpa [h] using (coeff_eq_zero_of_nat_degree_lt hi).symm },
  { refl }
end

lemma update_eq_monomial_add_erase (p : polynomial R) (n : ℕ) (a : R) :
  p.update n a = monomial n a + p.erase n :=
by { rw ←monomial_add_erase (p.update n a) n, simp }

lemma trop_eval_le_monomial_eval [linear_ordered_add_comm_monoid_with_top S]
  (p : polynomial (tropical S)) (x : tropical S) (i : ℕ) : eval x p ≤ p.coeff i * x ^ i :=
begin
  cases le_or_lt i p.nat_degree with hi hi,
  { rw [eval_eq_finset_sum, ←untrop_le_iff, finset.untrop_sum'],
    refine finset.inf_le _,
    simpa using nat.lt_succ_of_le hi },
  { simp [coeff_eq_zero_of_nat_degree_lt hi] }
end

lemma eval_le_coeff_zero [linear_ordered_add_comm_monoid_with_top S]
  (p : polynomial (tropical S)) (x : tropical S) :
  eval x p ≤ p.coeff 0 :=
by simpa using trop_eval_le_monomial_eval p x 0

lemma eval_at_zero (p : polynomial R) :
  eval 0 p = p.coeff 0 :=
begin
  induction p using polynomial.induction_on with x p q hp hq i x h,
  { simp },
  { simp [hp, hq] },
  { simp [coeff_X_pow, i.succ_ne_zero.symm] }
end

def least_coeff_at [has_le R] (p : polynomial R) (i : ℕ) : Prop :=
∀ (b : R), ⟦p.update i b⟧ = ⟦p⟧ → p.coeff i ≤ b

lemma least_coeff_at_zero [preorder R] (p : polynomial R) : p.least_coeff_at 0 :=
begin
  intros b h,
  rw quot_eq_iff at h,
  simpa [eval_at_zero] using eq.ge (h 0)
end

lemma least_coeff_at_iff_contra [linear_order R] {p : polynomial R} {i : ℕ} :
  p.least_coeff_at i ↔ (∀ b < p.coeff i, ⟦p.update i b⟧ ≠ ⟦p⟧) :=
⟨λ h b hb H, (h b H).not_lt hb,
 λ h b H, (le_or_lt (p.coeff i) b).cases_on id (λ hb, absurd H (h b hb))⟩

lemma least_coeff_at_of_injective_add [preorder R] (p : polynomial R) (i : ℕ)
   (ha : ∀ x : R, function.injective (+ x)) : p.least_coeff_at i :=
begin
  intros b h,
  rw [quot_eq_iff, update_eq_monomial_add_erase, ←monomial_add_erase p i] at h,
  refine eq.ge (ha (eval 1 (p.erase i)) _),
  simpa [erase_add, erase_erase] using h 1
end

-- lemma least_coeff_at_nat_degree_lt' [linear_ordered_add_comm_monoid_with_top S]
--   (p : polynomial (tropical S)) (i : ℕ) (hi : p.nat_degree < i) : p.least_coeff_at i :=
-- begin
--   intros b h,
--   rw [quot_eq_iff, update_eq_monomial_add_erase] at h,
--   rw coeff_eq_zero_of_nat_degree_lt hi,
--   -- refine eq.ge _,
--   specialize h 1,
--   simp [erase_nat_degree_lt _ _ hi, add_eq_right_iff] at h,
-- end


-- def red_at [linear_ordered_add_comm_monoid_with_top S] (p : polynomial (tropical S)) (i : ℕ) :
--   polynomial (tropical S) :=
-- if _ then _ else p

-- #exit

-- instance [add_comm_group S] [partial_order S] [covariant_class S S (+) (≤)] : has_ordered_sub S :=
-- begin
-- end

-- instance [add_comm_group S] [partial_order S] [has_ordered_sub] : has_ordered_sub S :=

lemma trop_eval_monotone_left [linear_ordered_add_comm_monoid_with_top S]
  (p : polynomial (tropical S)) :
  monotone (λ x, eval x p) := λ x y h,
begin
  induction p using polynomial.induction_on with p p q hp hq i p hp,
  { simp },
  { cases le_total (eval y p) (eval y q) with hy hy;
    cases le_total (eval x p) (eval x q) with hx hx,
    { simpa [hx, hy] using hp },
    { simpa [hx, hy] using hx.trans hp },
    { simpa [hx, hy] using hx.trans hq },
    { simpa [hx, hy] using hq } },
  { rw [←untrop_le_iff] at hp ⊢,
    simpa [succ_nsmul', ←add_assoc] using add_le_add hp h }
end

lemma trop_eval_monotone_left' [linear_ordered_add_comm_monoid S]
  (p : polynomial (tropical (with_top S))) :
  monotone (λ x, eval x p) := λ x y h,
begin
  induction p using polynomial.induction_on with p p q hp hq i p hp,
  { simp },
  { cases le_total (eval y p) (eval y q) with hy hy;
    cases le_total (eval x p) (eval x q) with hx hx,
    { simpa [hx, hy] using hp },
    { simpa [hx, hy] using hx.trans hp },
    { simpa [hx, hy] using hx.trans hq },
    { simpa [hx, hy] using hq } },
  { rw [←untrop_le_iff] at hp ⊢,
    simpa [succ_nsmul', ←add_assoc] using add_le_add hp h }
end

@[simp] lemma zero_le_iff [partial_order S] [order_top S] {x : tropical S} :
  0 ≤ x ↔ x = 0 :=
by simp [←untrop_le_iff, eq_comm, untrop_eq_iff_eq_trop]

lemma eq_top_iff_forall_le [linear_order S] [order_top S] {x : S} :
  x = ⊤ ↔ ∀ y, y ≤ x :=
begin
  split,
  { simp {contextual := tt} },
  { contrapose!,
    rw [ne.def, eq_top_iff, not_le],
    intro h,
    exact ⟨⊤, h⟩ }
end

@[simp] lemma min_lt_left_iff [linear_order S] {a b : S} :
  min a b < a ↔ b < a :=
begin
  rcases lt_trichotomy a b with h|h|h,
  { simp [h.le] },
  { simp [h] },
  { simp [h.le] }
end

@[simp] lemma min_lt_right_iff [linear_order S] {a b : S} :
  min a b < b ↔ a < b :=
by rw [min_comm, min_lt_left_iff]

@[simp] lemma add_lt_left_iff [linear_order S] {a b : tropical S} :
  a + b < a ↔ b < a :=
min_lt_left_iff

@[simp] lemma add_lt_right_iff [linear_order S] {a b : tropical S} :
  a + b < b ↔ a < b :=
by rw [add_comm, add_lt_left_iff]

lemma range_eval_subset_Iic [linear_ordered_add_comm_monoid_with_top S]
  (p : polynomial (tropical S)) :
  is_lub (set.range (λ x, eval x p)) (p.coeff 0) :=
begin
  rw is_lub_iff_le_iff,
  intro b,
  split,
  { rintros h x ⟨y, rfl⟩,
    simpa using (eval_le_coeff_zero _ _).trans h },
  { rw mem_upper_bounds,
    intro h,
    simp only [forall_apply_eq_imp_iff', set.mem_range, forall_exists_index] at h,
    simpa [eval_at_zero] using h 0 }
end

lemma coeff_zero_eq_zero_of_eval_eq_zero [linear_ordered_add_comm_monoid S]
  {p : polynomial (tropical (with_top S))} {x : tropical (with_top S)}
  (h : eval x p = 0) :
  p.coeff 0 = 0 :=
begin
  by_cases hp : p = 0,
  { simp [hp] },
  { rw eval_eq_finset_sum at h,
    simp only [mul_eq_zero_iff, finset.trop_sum_eq_zero_iff, finset.mem_range] at h,
    simpa using h 0 }
end

lemma exists_trop_coe_eq_coeff_zero_unit
  (p : polynomial (tropical (with_top unit))) (h : p.coeff 0 < 0) :
  ∃ (x : unit), eval (trop (x : with_top unit)) p = p.coeff 0 :=
begin
  use unit.star,
  induction hx : eval (trop (unit.star : with_top unit)) p using tropical.trop_rec with x,
  induction x using with_top.rec_top_coe,
  { simp only [trop_top] at hx,
    simpa using (coeff_zero_eq_zero_of_eval_eq_zero hx).symm },
  { have hc : p.coeff 0 = trop (unit.star : with_top unit),
    { induction hx : p.coeff 0 using tropical.trop_rec with x,
      induction x using with_top.rec_top_coe,
      { simpa [hx] using h },
      { simp [with_top.coe_eq_coe] } },
    simp [hc, with_top.coe_eq_coe] }
end

lemma exists_trop_coe_eq_coeff_zero [linear_ordered_add_comm_monoid S] [no_top_order S]
  (p : polynomial (tropical (with_top S))) (h : p.coeff 0 < 0) :
  ∃ (x : S), eval (trop (x : with_top S)) p = p.coeff 0 :=
begin
  induction p using polynomial.induction_on with p p q hp hq i p hp,
  { simp },
  { simp only [coeff_add] at h,
    cases le_total (p.coeff 0) (q.coeff 0) with hl hl,
    { rw add_eq_left hl at h,
      by_cases hq' : q.coeff 0 < 0,
      { simp [hl], },
      {  },
      simp [hl],
    },
    {  },
  },
  -- contrapose! h,
  -- replace h : ∀ (x : S), eval (trop (x : with_top S)) p < p.coeff 0,
  -- { intro x,
  --   refine lt_of_le_of_ne _ (h x),
  --   exact eval_le_coeff_zero _ _ },
  -- replace h : ∀ (x : S), p.coeff 0 + ∑ i in finset.range p.nat_degree,
  --   p.coeff (i + 1) * (trop (x : with_top S)) ^ (i + 1) < p.coeff 0,
  -- { intro x,
  --   convert h x,
  --   rw [eval_eq_finset_sum, finset.range_add_one', finset.sum_insert],
  --   { simp },
  --   { simp } },
  -- -- replace h : ∀ (x : S),
  -- simp_rw @add_lt_left_iff _ _ (p.coeff 0) at h,
  -- rw ←untrop_le_iff,
  -- rw untrop_zero,
  -- rw [top_le_iff],
  -- rw eq_top_iff_forall_le,
  -- simp_rw [eval_eq_finset_sum, finset.range_add_one'] at h,
  -- rw finset.sum_insert at h,
  -- simp,
  -- refine untrop_injective _,
  -- rw [untrop_zero, eq_top_iff_forall_le],
  -- intro y,
  -- induction y using with_top.rec_top_coe,

  -- induction p using polynomial.induction_on with p p q hp hq i p hp,
  -- { simp },
  -- { simp only [coeff_add] at h,
  --   cases le_total (p.coeff 0) (q.coeff 0) with hl hl,
  --   { rw add_eq_left hl at h,
  --     obtain ⟨x, hx⟩ := hp h,
  --     use x,
  --     simp only [add_eq_left hl, coeff_add, eval_add, hx, add_eq_left_iff],
  --   },
  --   {  },
  -- },
end
#exit

variables [partial_order α] [add_group α] [has_ordered_sub α] {a b c d : with_top α}

-- lemma with_top.tsub_coe_le_iff_right {a : with_top α} {b : α} {c : with_top α}
--   (hb : b ≠ ⊤) : a - b ≤ c ↔ a ≤ c + b :=
@[simp] lemma with_top.tsub_coe_le_iff_right {a : with_top α} {b : α} {c : with_top α} :
  a - b ≤ c ↔ a ≤ c + b :=
begin
  induction a using with_top.rec_top_coe,
  { simp },
  { induction c using with_top.rec_top_coe,
    { simp },
    { simp [←with_top.coe_sub, ←with_top.coe_add] } }
end

lemma with_top.tsub_le_iff_right (hb : b ≠ ⊤) : a - b ≤ c ↔ a ≤ c + b :=
begin
  induction b using with_top.rec_top_coe,
  { exact absurd rfl hb },
  { exact with_top.tsub_coe_le_iff_right }
end

lemma with_top.coe_nsmul [add_monoid S] (n : ℕ) (x : S) :
  ((n • x : S) : with_top S) = n • x :=
by { cases n; simp }

lemma trop_least_coeff_at_iff [linear_ordered_add_comm_group S]
  [has_ordered_sub S] [contravariant_class S S (+) (≤)]
  (p : polynomial (tropical (with_top S))) (i : ℕ) (hi : p.coeff i < 0) :
  p.least_coeff_at i ↔ ∃ (x : S), eval (trop ↑x) p = p.coeff i * (trop ↑x) ^ i :=
begin
  induction ha : p.coeff i using tropical.trop_rec with a,
  induction a using with_top.rec_top_coe,
  { simpa [ha] using hi },
  split,
  { contrapose!,
    intro h,
    replace h : ⟦p⟧ = ⟦p.erase i⟧,
    { rw quot_eq_iff,
      intro x,
      nth_rewrite_lhs 0 [←monomial_add_erase p i],
      rw eval_add,
      rw add_eq_right_iff,
      induction x using tropical.trop_rec,
      induction x using with_top.rec_top_coe,
      { cases i,
        { simp [←ha] at h,
          simp,
        },

        {  },
      },
      simp,
      -- rw eval_add,
      -- -- refine lt_of_le_of_ne _ (h x),
      -- -- rw ←untrop_le_iff,
      -- refine (trop_eval_le_monomial_eval _ _ i).trans (eq.le _),
      -- rw ha
      },
  }


end
#exit

lemma trop_least_coeff_at_iff' [linear_ordered_add_comm_group S]
  [has_ordered_sub S] [contravariant_class S S (+) (≤)]
  (p : polynomial (tropical (with_top S))) (i : ℕ) (hi : p.coeff i < 0) :
  p.least_coeff_at i ↔ ∃ (x : S), eval (trop ↑x) p = p.coeff i * (trop ↑x) ^ i :=
begin
  induction ha : p.coeff i using tropical.trop_rec with a,
  induction a using with_top.rec_top_coe,
  { simpa [ha] using hi },
  split,
  { contrapose!,
    intro h,
    replace h : ∀ (x : S), eval (trop ↑x) p < trop a * (trop ↑x) ^ i,
    { intro x,
      refine lt_of_le_of_ne _ (h x),
      rw ←untrop_le_iff,
      refine (trop_eval_le_monomial_eval _ _ i).trans (eq.le _),
      rw ha },
    let φ : tropical (with_top S) → tropical (with_top S) := λ x, eval x (p.erase i),
    by_cases H : ∃ (ε : S), ∀ (x : S), φ (trop ↑x) ≤ trop ↑ε,
    { obtain ⟨ε, H⟩ := H,
      cases le_or_lt 0 ε with hpos hneg,
      { by_cases hb : ∃ (b : S), b ∈ set.Ioo (a - ε) a,
        { obtain ⟨b, hb⟩ := hb,
          rw [set.mem_Ioo] at hb,
          contrapose! hb,
          intro hb',
          have : ∀ x, eval x p / (trop b * x ^ i) ≤ eval x p / (trop a * x ^ i) * trop ε,
          { intro x,
            rw [←untrop_le_iff],
            simp only [untrop_trop, untrop_mul, untrop_pow, untrop_div],
            induction x using tropical.trop_rec,
            induction x using with_top.rec_top_coe,
            { cases i,
              { simp only [mul_one, untrop_trop, untrop_mul, trop_top, untrop_div, pow_zero],
                induction untrop (eval 0 p) using with_top.rec_top_coe with c,
                { simp },
                { suffices : c ≤ c - a + ε + b,
                  { simpa [←with_top.coe_sub, ←with_top.coe_add] },
                  rw [sub_add_eq_add_sub, sub_add_eq_add_sub, le_sub_iff_add_le, add_assoc,
                      add_comm ε],
                  exact add_le_add_left (tsub_le_iff_right.mp hb'.le) _ } },
              { simpa [succ_nsmul', with_top.le_coe_iff] using hpos } },
            { rw [untrop_trop, ←with_top.coe_nsmul, ←with_top.coe_add, ←with_top.coe_add],
              induction eval (trop (x : with_top S)) p using tropical.trop_rec with x',
              induction x' using with_top.rec_top_coe,
              { simp },
              { simp_rw [untrop_trop, ←with_top.coe_sub, ←with_top.coe_add, with_top.coe_le_coe],
                rw tsub_le_iff_tsub_le,
                rw [sub_add_eq_sub_sub, sub_sub_self, sub_eq_add_neg, add_comm, ←add_assoc],
                rw [add_le_add_iff_right, add_comm, ←sub_eq_add_neg],
                exact hb'.le } } },
          suffices : p.coeff i ≤ trop (b : with_top S),
          { simpa [ha, ←untrop_le_iff] },
          refine hb (trop (b : with_top S)) _,
          rw quot_eq_iff,
          intro y,
          rw update_eq_monomial_add_erase,
          -- intro hl,
          -- specialize hl (trop (b : with_top S)) sorry,
          -- refine hb.right.not_le _,
        },
        {  },
         },
      {  },
    },
    },
  { contrapose!,
    intros H h,
    have : ∀ x, eval x p < p.coeff i * x ^ i :=
      λ x, lt_of_le_of_ne (trop_eval_le_monomial_eval _ x _) (H x),
    obtain ⟨b, hb⟩ : ∃ b, b < p.coeff i,
    { contrapose! this,
      use 1,
      simpa using this _ },
    refine h b hb _,
    rw quot_eq_iff,
    intro x,

    -- set q : polynomial (tropical S) := p.erase i,
  },
  { rintro ⟨x, hx⟩ b H,
    rw quot_eq_iff at H,
    specialize H x,
    have : b * x ^ i < p.coeff i * x ^ i,
    { rw ←untrop_lt_iff at hb ⊢,
      rw lt_iff_le_not_le at hb ⊢,
      simp_rw untrop_mul at ⊢,
      cases hb with hb hb',
      split,
      { exact add_le_add_right hb _ },
      { contrapose! hb',
      },
      -- simp,
      -- haveI : covariant_class S S (function.swap (+)) (<) :=
      -- by { refine @covariant_swap_add_lt_of_covariant_add_lt _ _ _ _, },
      -- exact add_lt_add_right hb _,
    },
    nth_rewrite_lhs 0 [←monomial_add_erase p i] at hx H,
    rw [eval_add, eval_monomial, add_eq_left_iff] at hx,
    rw [update_eq_monomial_add_erase, eval_add, eval_monomial, add_eq_left hx,
        eval_add, eval_monomial, eq_comm, add_eq_iff] at H,
    -- rw [←erase_add_monomial_coeff_eq_self p i, eval_add, erase_add_monomial_coeff_eq_self] at hx,
    -- rw H at hx,
    -- rw [update_eq_monomial_add_erase, ←monomial_add_erase p i, erase_add, erase_erase,
    --     erase_monomial, zero_add, eval_add, eval_add, eval_monomial, eval_monomial] at H,
    -- rw [add_eq_iff, add_eq_right_iff] at H,
    -- rw eval_add at hx,
    -- rw eval_monomial at hx,
  },
end

end polynomial

-- open tropical polynomial

-- variables [linear_ordered_semiring R]

-- section linear_ordered_add_comm_monoid_with_top
-- variables [linear_ordered_add_comm_monoid_with_top α] {a b : α}

-- @[simp] lemma min_eq_top_iff : min a b = ⊤ ↔ a = ⊤ ∧ b = ⊤ :=
-- begin
--   split,
--   { rw min_eq_iff,
--     rintro (⟨rfl, h⟩|⟨rfl, h⟩);
--     simpa using h },
--   { rintro ⟨rfl, rfl⟩,
--     simp },
-- end

-- end linear_ordered_add_comm_monoid_with_top

-- -- def polynomial.trop_eval (p : polynomial Rᵗ) (hp : p ≠ 0) : R → R :=
-- -- λ x, with_top.untop (untrop (eval (trop (x : with_top R)) p)) $
-- --   begin
-- --     simp only [untrop_eq_iff_eq_trop, ne.def, trop_top],
-- --     induction p using polynomial.induction_on with p p q IH IH' n p IH,
-- --     { simpa [untrop_eq_iff_eq_trop] using hp },
-- --     { simp only [not_and, eval_add, tropical.add_eq_zero_iff],
-- --       intro hp0,
-- --       refine IH' _,
-- --       rintro rfl,
-- --       exact IH (by simpa using hp) hp0 },
-- --     { contrapose! hp,
-- --       refine mul_eq_zero_of_left _ _,
-- --       simpa using hp }
-- --   end


-- -- lemma trop_eval_eq_infi (p : polynomial Rᵗ) (hp : p ≠ 0) (x : R) :
-- --   p.trop_eval hp x = with_top.untop (list.minimum ((list.range p.nat_degree).map _)) _
