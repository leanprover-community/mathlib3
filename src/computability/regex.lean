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
# Regular Expression

This file contains the formal definition for regular expressions and basic lemmas.
-/

universe u

variables {α : Type u} [dec : decidable_eq α]

/-- This is the definition of regular expressions
  `RZero` matches nothing
  `RNull` matches only the empty string
  `RChar a` matches only the string 'a'
  `RStar M` matches any finite concatenation of strings which match `M`
  `RPlus M N` matches anything which match `M` or `N`
  `RComp M N` matches `x ++ y` if `x` matches `M` and `y` matches `N` -/
inductive regex (α : Type u) : Type (u+1)
| RZero : regex
| RNull : regex
| RChar : α → regex
| RStar : regex → regex
| RPlus : regex → regex → regex
| RComp : regex → regex → regex

namespace regex

instance regex_inhabited : inhabited (regex α) := ⟨ RZero ⟩

/-- `match_null M` is true if and only if `M` matches the empty string -/
def match_null : regex α → bool
| RZero := ff
| RNull := tt
| (RChar _) := ff
| (RStar M) := tt
| (RPlus M N) := M.match_null || N.match_null
| (RComp M N) := M.match_null && N.match_null

include dec

/-- `M.feed a` matches `x` if `M` matches `"a" ++ x` -/
def feed : regex α → α → regex α
| RZero _ := RZero
| RNull _ := RZero
| (RChar a₁) a₂ := if a₁ = a₂ then RNull else RZero
| (RStar M) a := RComp (feed M a) (RStar M)
| (RPlus M N) a := RPlus (feed M a) (feed N a)
| (RComp M N) a :=
  ite M.match_null (RPlus (RComp (feed M a) N) (feed N a)) (RComp (feed M a) N)

/-- `M.rmatch x` is true if and only if `M` matches `x` -/
def rmatch : regex α → list α → bool
| M [] := match_null M
| M (a::as) := rmatch (M.feed a) as

lemma RZero_rmatch (s : list α) : rmatch RZero s = ff :=
begin
  induction s,
    rw [rmatch, match_null],
  rwa [rmatch, feed],
end

lemma RNull_rmatch_iff (s : list α) : rmatch RNull s ↔ s = [] :=
begin
  cases s,
    dec_trivial,
  rw [rmatch, feed, RZero_rmatch],
  dec_trivial
end

lemma RChar_rmatch_iff (a : α) (s : list α) : rmatch (RChar a) s ↔ s = [a] :=
begin
  cases s with _ s,
    dec_trivial,
  cases s,
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

lemma RPlus_rmatch_iff (P Q : regex α) (s : list α) :
  (RPlus P Q).rmatch s ↔ P.rmatch s ∨ Q.rmatch s :=
begin
  induction s with _ _ ih generalizing P Q,
  { repeat {rw rmatch},
    rw match_null,
    finish },
  { repeat {rw rmatch},
    rw feed,
    exact ih _ _ }
end

lemma RComp_rmatch_iff (P Q : regex α) (s : list α) :
  (RComp P Q).rmatch s ↔ ∃ t u : list α, s = t ++ u ∧ P.rmatch t ∧ Q.rmatch u :=
begin
  induction s with a s ih generalizing P Q,
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
        { exact ⟨ [], a :: s, rfl, hnull, h ⟩ } },
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

lemma RStar_rmatch_iff (P : regex α) : ∀ (s : list α),
  (RStar P).rmatch s ↔ ∃ S : list (list α), s = S.join ∧ ∀ t ∈ S, ¬(list.empty t) ∧ P.rmatch t
| s :=
begin
  have IH := λ t (h : list.length t < list.length s), RStar_rmatch_iff t,
  clear RStar_rmatch_iff,
  split,
  { cases s with a s,
    { intro,
      fconstructor,
      exact [],
      tauto },
    { rw [rmatch, feed, RComp_rmatch_iff],
      rintro ⟨ t, u, hs, ht, hu ⟩,
      have hwf : u.length < (list.cons a s).length,
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
    cases s with a s,
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
        { have hwf : U.join.length < (list.cons a s).length,
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

end regex
