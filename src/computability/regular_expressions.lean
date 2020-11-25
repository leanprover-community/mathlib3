/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Fox Thomson.
-/
import data.fintype.basic
import data.finset.basic
import tactic.rcases
import tactic.omega

/-!
# Regular Expressions

This file contains the formal definition for regular expressions and basic lemmas. Note these are
regular expressions in terms of formal language theory. Note this is different to regex's used in
computer science such as the POSIX standard.
-/

universe u

variables {α : Type u} [dec : decidable_eq α]

/-- This is the definition of regular expressions. The names used here is to mirror the definition
  of a Kleene algebra (https://en.wikipedia.org/wiki/Kleene_algebra).
  `RZero` matches nothing
  `RNull` matches only the empty string
  `RChar a` matches only the string 'a'
  `RStar M` matches any finite concatenation of strings which match `M`
  `RPlus M N` matches anything which match `M` or `N`
  `RComp M N` matches `x ++ y` if `x` matches `M` and `y` matches `N` -/
inductive regular_expression (α : Type u) : Type (u+1)
| RZero : regular_expression
| RNull : regular_expression
| RChar : α → regular_expression
| RStar : regular_expression → regular_expression
| RPlus : regular_expression → regular_expression → regular_expression
| RComp : regular_expression → regular_expression → regular_expression

namespace regular_expression

instance regular_expression_inhabited : inhabited (regular_expression α) := ⟨ RZero ⟩

instance : has_add (regular_expression α) := ⟨RPlus⟩
instance : has_mul (regular_expression α) := ⟨RComp⟩
instance : has_one (regular_expression α) := ⟨RNull⟩
instance : has_zero (regular_expression α) := ⟨RZero⟩

/-- `match_null M` is true if and only if `M` matches the empty string -/
def match_null : regular_expression α → bool
| RZero := ff
| RNull := tt
| (RChar _) := ff
| (RStar M) := tt
| (RPlus M N) := M.match_null || N.match_null
| (RComp M N) := M.match_null && N.match_null

include dec

/-- `M.feed a` matches `x` if `M` matches `"a" ++ x` -/
def feed : regular_expression α → α → regular_expression α
| RZero _ := RZero
| RNull _ := RZero
| (RChar a₁) a₂ := if a₁ = a₂ then RNull else RZero
| (RStar M) a := RComp (feed M a) (RStar M)
| (RPlus M N) a := RPlus (feed M a) (feed N a)
| (RComp M N) a :=
  ite M.match_null (RPlus (RComp (feed M a) N) (feed N a)) (RComp (feed M a) N)

/-- `M.rmatch x` is true if and only if `M` matches `x` -/
def rmatch : regular_expression α → list α → bool
| M [] := match_null M
| M (a::as) := rmatch (M.feed a) as

lemma RZero_rmatch (x : list α) : rmatch RZero x = ff :=
begin
  induction x,
    rw [rmatch, match_null],
  rwa [rmatch, feed],
end

@[simp] lemma zero_rmatch (x : list α) : rmatch 0 x = ff := RZero_rmatch x

lemma RNull_rmatch_iff (x : list α) : rmatch RNull x ↔ x = [] :=
begin
  cases x,
    dec_trivial,
  rw [rmatch, feed, RZero_rmatch],
  dec_trivial
end

@[simp] lemma one_rmatch_iff (x : list α) : rmatch 1 x ↔ x = [] := RNull_rmatch_iff x

lemma RChar_rmatch_iff (a : α) (x : list α) : rmatch (RChar a) x ↔ x = [a] :=
begin
  cases x with _ x,
    dec_trivial,
  cases x,
    rw [rmatch, feed],
    split_ifs;
    tauto,
  rw [rmatch, feed],
  split_ifs,
    rw RNull_rmatch_iff,
    tauto,
  rw RZero_rmatch,
  tauto
end

lemma RPlus_rmatch_iff (P Q : regular_expression α) (x : list α) :
  (RPlus P Q).rmatch x ↔ P.rmatch x ∨ Q.rmatch x :=
begin
  induction x with _ _ ih generalizing P Q,
  { repeat {rw rmatch},
    rw match_null,
    finish },
  { repeat {rw rmatch},
    rw feed,
    exact ih _ _ }
end

@[simp] lemma add_rmatch_iff (P Q : regular_expression α) (x : list α) :
  (P + Q).rmatch x ↔ P.rmatch x ∨ Q.rmatch x := RPlus_rmatch_iff P Q x

lemma RComp_rmatch_iff (P Q : regular_expression α) (x : list α) :
  (RComp P Q).rmatch x ↔ ∃ t u : list α, x = t ++ u ∧ P.rmatch t ∧ Q.rmatch u :=
begin
  induction x with a x ih generalizing P Q,
  { rw [rmatch, match_null],
    split,
    { intro h,
      refine ⟨ [], [], rfl, _ ⟩,
      rw [rmatch, rmatch],
      rwa band_coe_iff at h },
    { rintro ⟨ t, u, h₁, h₂ ⟩,
      cases list.append_eq_nil.1 h₁.symm with ht hu,
      subst ht,
      subst hu,
      repeat {rw rmatch at h₂},
      finish } },
  { rw [rmatch, feed],
    split_ifs with hnull,
    { rw [RPlus_rmatch_iff, ih],
      split,
      { rintro (⟨ t, u, _ ⟩ | h),
        { exact ⟨ a :: t, u, by tauto ⟩ },
        { exact ⟨ [], a :: x, rfl, hnull, h ⟩ } },
      { rintro ⟨ t, u, h, hP, hQ ⟩,
        cases t with b t,
        { right,
          rw list.nil_append at h,
          rw ←h at hQ,
          exact hQ },
        { left,
          refine ⟨ t, u, by finish, _, hQ ⟩,
          rw rmatch at hP,
          convert hP,
          finish } } },
    { rw ih,
      split;
      rintro ⟨ t, u, h, hP, hQ ⟩,
      { exact ⟨ a :: t, u, by tauto ⟩ },
      { cases t with b t,
        { contradiction },
        { refine ⟨ t, u, by finish, _, hQ ⟩,
          rw rmatch at hP,
          convert hP,
          finish } } } }
end

@[simp] lemma mul_rmatch_iff (P Q : regular_expression α) (x : list α) :
  (P * Q).rmatch x ↔ ∃ t u : list α, x = t ++ u ∧ P.rmatch t ∧ Q.rmatch u := RComp_rmatch_iff P Q x

lemma RStar_rmatch_iff (P : regular_expression α) : ∀ (x : list α),
  (RStar P).rmatch x ↔ ∃ S : list (list α), x = S.join ∧ ∀ t ∈ S, ¬(list.empty t) ∧ P.rmatch t
| x :=
begin
  have IH := λ t (h : list.length t < list.length x), RStar_rmatch_iff t,
  clear RStar_rmatch_iff,
  split,
  { cases x with a x,
    { intro,
      fconstructor,
      exact [],
      tauto },
    { rw [rmatch, feed, RComp_rmatch_iff],
      rintro ⟨ t, u, hs, ht, hu ⟩,
      have hwf : u.length < (list.cons a x).length,
      { rw [hs, list.length_cons, list.length_append],
        omega },
      rw IH _ hwf at hu,
      rcases hu with ⟨ S', hsum, helem ⟩,
      use (a :: t) :: S',
      split,
      { finish },
      { intros t' ht',
        cases ht' with ht' ht',
        { rw ht',
          exact ⟨ dec_trivial, ht ⟩ },
        { exact helem _ ht' } } } },
  { rintro ⟨ S, hsum, helem ⟩,
    cases x with a x,
    { dec_trivial },
    { rw [rmatch, feed, RComp_rmatch_iff],
      cases S with t' U,
      { exact ⟨ [], [], by tauto ⟩ },
      { cases t' with b t,
        { finish },
        refine ⟨ t, U.join, by finish, _, _ ⟩,
        { specialize helem (b :: t) _,
          rw rmatch at helem,
          convert helem.2,
          finish,
          finish },
        { have hwf : U.join.length < (list.cons a x).length,
          { rw hsum,
            simp only
              [list.join, list.length_append, list.cons_append, list.length_join, list.length],
            omega },
          rw IH _ hwf,
          refine ⟨ U, rfl, λ t h, helem t _ ⟩,
          right,
          assumption } } } }
end
using_well_founded {
  rel_tac := λ _ _, `[exact ⟨(λ L₁ L₂ : list _, L₁.length < L₂.length), inv_image.wf _ nat.lt_wf⟩]
}

lemma add_assoc (P Q R : regular_expression α) (x : list α) :
  ((P + Q) + R).rmatch x ↔ (P + (Q + R)).rmatch x := by finish

lemma add_comm (P Q : regular_expression α) (x : list α) :
  (P + Q).rmatch x ↔ (Q + P).rmatch x := by finish

lemma mul_add (P Q R : regular_expression α) (x : list α) :
  (P * (Q + R)).rmatch x ↔ ((P * Q) + (P * R)).rmatch x :=
begin
  simp only [mul_rmatch_iff, add_rmatch_iff],
  split,
  { rintro ⟨ s, t, hsum, hP, (hQ | hR) ⟩,
    left,
    rotate,
    right,
    all_goals
    { use [s, t],
      tauto } },
  { rintro (h | h);
    rcases h with ⟨ s, t, hsum, hP, h ⟩;
    use [s, t];
    tauto }
end

lemma add_zero (P : regular_expression α) (x : list α) : (P + 0).rmatch x ↔ P.rmatch x := by finish
lemma zero_add (P : regular_expression α) (x : list α) : (0 + P).rmatch x ↔ P.rmatch x := by finish
lemma mul_zero (P : regular_expression α) (x : list α) : (P * 0).rmatch x ↔ rmatch 0 x := by finish
lemma zero_mul (P : regular_expression α) (x : list α) : (0 * P).rmatch x ↔ rmatch 0 x := by finish
lemma mul_one (P : regular_expression α) (x : list α) : (P * 1).rmatch x ↔ P.rmatch x :=
begin
  simp only [mul_rmatch_iff, one_rmatch_iff],
  split,
  { rintro ⟨ t, u, hx, hp, hu ⟩,
    finish },
  { intro h,
    use [x, []],
    finish }
end
lemma one_mul (P : regular_expression α) (x : list α) : (1 * P).rmatch x ↔ P.rmatch x :=
begin
  simp only [mul_rmatch_iff, one_rmatch_iff],
  split,
  { rintro ⟨ t, u, hx, hp, hu ⟩,
    finish },
  { intro h,
    use [[], x],
    finish }
end

lemma add_self (P : regular_expression α) (x : list α) : (P + P).rmatch x ↔ P.rmatch x := by finish

end regular_expression
