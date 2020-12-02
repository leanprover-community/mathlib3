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
  `zero` matches nothing
  `epsilon` matches only the empty string
  `char a` matches only the string 'a'
  `star M` matches any finite concatenation of strings which match `M`
  `plus M N` matches anything which match `M` or `N`
  `comp M N` matches `x ++ y` if `x` matches `M` and `y` matches `N` -/
inductive regular_expression (α : Type u) : Type (u+1)
| zero : regular_expression
| epsilon : regular_expression
| char : α → regular_expression
| star : regular_expression → regular_expression
| plus : regular_expression → regular_expression → regular_expression
| comp : regular_expression → regular_expression → regular_expression

namespace regular_expression

instance : inhabited (regular_expression α) := ⟨zero⟩

instance : has_add (regular_expression α) := ⟨plus⟩
instance : has_mul (regular_expression α) := ⟨comp⟩
instance : has_one (regular_expression α) := ⟨epsilon⟩
instance : has_zero (regular_expression α) := ⟨zero⟩

/-- `match_epsilon M` is true if and only if `M` matches the empty string -/
def match_epsilon : regular_expression α → bool
| zero := ff
| epsilon := tt
| (char _) := ff
| (star M) := tt
| (plus M N) := M.match_epsilon || N.match_epsilon
| (comp M N) := M.match_epsilon && N.match_epsilon

include dec

/-- `M.deriv a` matches `x` if `M` matches `a :: x`, the Brzozowski derivative of `M` with respect
  to `a` -/
def deriv : regular_expression α → α → regular_expression α
| zero _ := zero
| epsilon _ := zero
| (char a₁) a₂ := if a₁ = a₂ then epsilon else zero
| (star M) a := comp (deriv M a) (star M)
| (plus M N) a := plus (deriv M a) (deriv N a)
| (comp M N) a :=
  if M.match_epsilon then
    (plus (comp (deriv M a) N) (deriv N a))
  else
    (comp (deriv M a) N)

/-- `M.rmatch x` is true if and only if `M` matches `x` -/
def rmatch : regular_expression α → list α → bool
| M [] := match_epsilon M
| M (a::as) := rmatch (M.deriv a) as

/-- Two regular expressions are equivalent if they match exactly the same strings -/
def equiv (P Q : regular_expression α) : Prop := ∀ x, P.rmatch x ↔ Q.rmatch x

local infix ` ≈ ` := equiv

@[refl] lemma equiv_refl (P : regular_expression α) : P ≈ P := λ x, by refl
@[symm] lemma equiv_symm (P Q : regular_expression α) : P ≈ Q → Q ≈ P := λ h x, (h x).symm
@[trans] lemma equiv_trans (P Q R : regular_expression α) : P ≈ Q → Q ≈ R → P ≈ R :=
λ h₁ h₂ x, iff.trans (h₁ x) (h₂ x)

@[simp] lemma equiv_def (P Q : regular_expression α) : P ≈ Q ↔ ∀ x, P.rmatch x ↔ Q.rmatch x :=
by refl

lemma zero_rmatch' (x : list α) : rmatch zero x = ff :=
begin
  induction x,
    rw [rmatch, match_epsilon],
  rwa [rmatch, deriv],
end

@[simp] lemma zero_rmatch (x : list α) : rmatch 0 x = ff := zero_rmatch' x

lemma epsilon_rmatch_iff (x : list α) : rmatch epsilon x ↔ x = [] :=
begin
  cases x,
    dec_trivial,
  rw [rmatch, deriv, zero_rmatch'],
  dec_trivial
end

@[simp] lemma one_rmatch_iff (x : list α) : rmatch 1 x ↔ x = [] := epsilon_rmatch_iff x

lemma char_rmatch_iff (a : α) (x : list α) : rmatch (char a) x ↔ x = [a] :=
begin
  cases x with _ x,
    dec_trivial,
  cases x,
    rw [rmatch, deriv],
    split_ifs;
    tauto,
  rw [rmatch, deriv],
  split_ifs,
    rw epsilon_rmatch_iff,
    tauto,
  rw zero_rmatch',
  tauto
end

lemma plus_rmatch_iff (P Q : regular_expression α) (x : list α) :
  (plus P Q).rmatch x ↔ P.rmatch x ∨ Q.rmatch x :=
begin
  induction x with _ _ ih generalizing P Q,
  { repeat {rw rmatch},
    rw match_epsilon,
    finish },
  { repeat {rw rmatch},
    rw deriv,
    exact ih _ _ }
end

@[simp] lemma add_rmatch_iff (P Q : regular_expression α) (x : list α) :
  (P + Q).rmatch x ↔ P.rmatch x ∨ Q.rmatch x := plus_rmatch_iff P Q x

lemma comp_rmatch_iff (P Q : regular_expression α) (x : list α) :
  (comp P Q).rmatch x ↔ ∃ t u : list α, x = t ++ u ∧ P.rmatch t ∧ Q.rmatch u :=
begin
  induction x with a x ih generalizing P Q,
  { rw [rmatch, match_epsilon],
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
  { rw [rmatch, deriv],
    split_ifs with hepsilon,
    { rw [plus_rmatch_iff, ih],
      split,
      { rintro (⟨ t, u, _ ⟩ | h),
        { exact ⟨ a :: t, u, by tauto ⟩ },
        { exact ⟨ [], a :: x, rfl, hepsilon, h ⟩ } },
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
  (P * Q).rmatch x ↔ ∃ t u : list α, x = t ++ u ∧ P.rmatch t ∧ Q.rmatch u := comp_rmatch_iff P Q x

lemma star_rmatch_iff (P : regular_expression α) : ∀ (x : list α),
  (star P).rmatch x ↔ ∃ S : list (list α), x = S.join ∧ ∀ t ∈ S, ¬(list.empty t) ∧ P.rmatch t
| x :=
begin
  have IH := λ t (h : list.length t < list.length x), star_rmatch_iff t,
  clear star_rmatch_iff,
  split,
  { cases x with a x,
    { intro,
      fconstructor,
      exact [],
      tauto },
    { rw [rmatch, deriv, comp_rmatch_iff],
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
    { rw [rmatch, deriv, comp_rmatch_iff],
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

lemma add_assoc (P Q R : regular_expression α) : (P + Q) + R ≈ P + (Q + R) := by finish

lemma add_comm (P Q : regular_expression α) : P + Q ≈ Q + P := by finish

lemma mul_add (P Q R : regular_expression α) : P * (Q + R) ≈ (P * Q) + (P * R) :=
begin
  intro x,
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

lemma add_zero (P : regular_expression α) : P + 0 ≈ P := by finish
lemma zero_add (P : regular_expression α) : 0 + P ≈ P := by finish
lemma mul_zero (P : regular_expression α) : P * 0 ≈ 0 := by finish
lemma zero_mul (P : regular_expression α) : 0 * P ≈ 0 := by finish

lemma mul_one (P : regular_expression α) : P * 1 ≈ P :=
begin
  intro x,
  simp only [mul_rmatch_iff, one_rmatch_iff],
  split,
  { rintro ⟨ t, u, hx, hp, hu ⟩,
    finish },
  { intro h,
    use [x, []],
    finish }
end

lemma one_mul (P : regular_expression α) : 1 * P ≈ P :=
begin
  intro x,
  simp only [mul_rmatch_iff, one_rmatch_iff],
  split,
  { rintro ⟨ t, u, hx, hp, hu ⟩,
    finish },
  { intro h,
    use [[], x],
    finish }
end

lemma add_self (P : regular_expression α) : P + P ≈ P := by finish

end regular_expression
