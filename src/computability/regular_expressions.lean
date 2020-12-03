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

/-- We first define a language as a set of strings over an alphabet. -/
@[derive [has_union, has_emptyc, has_mem (list α), has_singleton (list α)]]
def language (α) := set (list α)

namespace language

instance : inhabited (language α) := ⟨∅⟩

instance : has_zero (language α) := ⟨∅⟩
instance : has_one (language α) := ⟨{[]}⟩

instance : has_add (language α) := ⟨set.union⟩
instance : has_mul (language α) := ⟨λ l m, (l.prod m).image (λ p, p.1 ++ p.2)⟩

@[simp] lemma zero_def : (0 : language α) = ∅ := rfl
@[simp] lemma one_def : (1 : language α) = {[]} := rfl

@[simp] lemma add_def (l m : language α) : l + m = l ∪ m := rfl
@[simp] lemma mul_def (l m : language α) : l * m = (l.prod m).image (λ p, p.1 ++ p.2) := rfl

/-- The star of a language `L` is the set of all strings which can be written by concatenating
  strings from `L`. -/
def star (l : language α) : language α :=
{ x | ∃ S : list (list α), x = S.join ∧ ∀ y ∈ S, ¬(list.empty y) ∧ y ∈ l}

@[simp] lemma star_def (l : language α) :
  l.star = { x | ∃ S : list (list α), x = S.join ∧ ∀ y ∈ S, ¬(list.empty y) ∧ y ∈ l} := rfl

end language


/-- This is the definition of regular expressions. The names used here is to mirror the definition
  of a Kleene algebra (https://en.wikipedia.org/wiki/Kleene_algebra).
  `zero` matches nothing
  `epsilon` matches only the empty string
  `char a` matches only the string 'a'
  `star M` matches any finite concatenation of strings which match `M`
  `plus M N` matches anything which match `M` or `N`
  `comp M N` matches `x ++ y` if `x` matches `M` and `y` matches `N` -/
inductive regular_expression (α : Type u) : Type u
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

@[simp] lemma zero_def : (zero : regular_expression α) = 0 := rfl
@[simp] lemma one_def : (epsilon : regular_expression α) = 1 := rfl

@[simp] lemma plus_def (P Q : regular_expression α) : plus P Q = P + Q := rfl
@[simp] lemma comp_def (P Q : regular_expression α) : comp P Q = P * Q := rfl

/-- `matches M` provides a language which contains all strings that `M` matches -/
def matches : regular_expression α → language α
| zero := 0
| epsilon := 1
| (char a) := {[a]}
| (plus M N) := M.matches + N.matches
| (comp M N) := M.matches * N.matches
| (star M) := M.matches.star

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
| zero _ := 0
| epsilon _ := 0
| (char a₁) a₂ := if a₁ = a₂ then 1 else 0
| (star M) a := deriv M a * star M
| (plus M N) a := deriv M a + deriv N a
| (comp M N) a :=
  if M.match_epsilon then
    deriv M a * N + deriv N a
  else
    deriv M a * N

/-- `M.rmatch x` is true if and only if `M` matches `x`. This is a computable definition equivalent
  to `matches` -/
def rmatch : regular_expression α → list α → bool
| M [] := match_epsilon M
| M (a::as) := rmatch (M.deriv a) as

@[simp] lemma zero_rmatch (x : list α) : rmatch 0 x = ff :=
begin
  rw ←zero_def,
  induction x,
    rw [rmatch, match_epsilon],
  rwa [rmatch, deriv],
end

@[simp] lemma one_rmatch_iff (x : list α) : rmatch 1 x ↔ x = [] :=
begin
  rw ←one_def,
  cases x,
    dec_trivial,
  rw [rmatch, deriv, zero_rmatch],
  dec_trivial
end

@[simp] lemma char_rmatch_iff (a : α) (x : list α) : rmatch (char a) x ↔ x = [a] :=
begin
  cases x with _ x,
    dec_trivial,
  cases x,
    rw [rmatch, deriv],
    split_ifs;
    tauto,
  rw [rmatch, deriv],
  split_ifs,
    rw one_rmatch_iff,
    tauto,
  rw zero_rmatch,
  tauto
end

@[simp] lemma add_rmatch_iff (P Q : regular_expression α) (x : list α) :
  (P + Q).rmatch x ↔ P.rmatch x ∨ Q.rmatch x :=
begin
  rw ←plus_def,
  induction x with _ _ ih generalizing P Q,
  { repeat {rw rmatch},
    rw match_epsilon,
    finish },
  { repeat {rw rmatch},
    rw deriv,
    exact ih _ _ }
end

@[simp] lemma mul_rmatch_iff (P Q : regular_expression α) (x : list α) :
  (P * Q).rmatch x ↔ ∃ t u : list α, x = t ++ u ∧ P.rmatch t ∧ Q.rmatch u :=
begin
  induction x with a x ih generalizing P Q,
  { rw [←comp_def, rmatch, match_epsilon],
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
  { rw [←comp_def, rmatch, deriv],
    split_ifs with hepsilon,
    { rw [add_rmatch_iff, ih],
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

@[simp] lemma star_rmatch_iff (P : regular_expression α) : ∀ (x : list α),
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
    { rw [rmatch, deriv, mul_rmatch_iff],
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
    { rw [rmatch, deriv, mul_rmatch_iff],
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

@[simp] lemma matches_iff_rmatch (P : regular_expression α) :
  ∀ x : list α, x ∈ P.matches ↔ P.rmatch x :=
begin
  intro x,
  induction P with _ _ _ _ _ _ _ _ _ ih₁ ih₂ generalizing x;
  rw matches,
  { simp },
  { simp },
  { simp },
  { finish },
  { finish },
  { simp,
    split,
    { rintro ⟨ x, hmatch₁, y, hmatch₂, hsum ⟩,
      rw ih₁ at hmatch₁,
      rw ih₂ at hmatch₂,
      exact ⟨ x, y, hsum.symm, hmatch₁, hmatch₂ ⟩ },
    { rintro ⟨ x, y, hsum, hmatch₁, hmatch₂ ⟩,
      rw ←ih₁ at hmatch₁,
      rw ←ih₂ at hmatch₂,
      exact ⟨ x, hmatch₁, y, hmatch₂, hsum.symm ⟩ } },
end

omit dec

lemma add_assoc (P Q R : regular_expression α) : ((P + Q) + R).matches = (P + (Q + R)).matches :=
by {classical, ext, finish}
lemma add_comm (P Q : regular_expression α) : (P + Q).matches = (Q + P).matches :=
by {classical, ext, finish}

lemma mul_add (P Q R : regular_expression α) :
  (P * (Q + R)).matches = ((P * Q) + (P * R)).matches :=
begin
  classical,
  ext x,
  simp only [mul_rmatch_iff, matches_iff_rmatch, add_rmatch_iff],
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

lemma add_zero (P : regular_expression α) : (P + 0).matches = P.matches :=
by {classical, ext, finish}
lemma zero_add (P : regular_expression α) : (0 + P).matches = P.matches :=
by {classical, ext, finish}

lemma mul_zero (P : regular_expression α) : (P * 0).matches = (0 : regular_expression α).matches :=
by {classical, ext, finish}
lemma zero_mul (P : regular_expression α) : (0 * P).matches = (0 : regular_expression α).matches :=
by {classical, ext, finish}

lemma mul_one (P : regular_expression α) : (P * 1).matches = P.matches :=
begin
  classical,
  ext x,
  simp only [mul_rmatch_iff, matches_iff_rmatch, one_rmatch_iff],
  split,
  { rintro ⟨ t, u, hx, hp, hu ⟩,
    finish },
  { intro h,
    use [x, []],
    finish }
end

lemma one_mul (P : regular_expression α) : (1 * P).matches = P.matches :=
begin
  classical,
  ext x,
  simp only [mul_rmatch_iff, matches_iff_rmatch, one_rmatch_iff],
  split,
  { rintro ⟨ t, u, hx, hp, hu ⟩,
    finish },
  { intro h,
    use [[], x],
    finish }
end

lemma add_self (P : regular_expression α) : (P + P).matches = P.matches :=
by {classical, ext, finish}

end regular_expression
