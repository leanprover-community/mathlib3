/-
  Copyright (c) 2019 Seul Baek. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Seul Baek

  Detailed recipes for building resolution proofs.
-/

import tactic.spass.cnf
import tactic.spass.list

universes u v

variable {α : Type u}

local notation `&`     := term.sym
local notation a `&` b := term.app a b
local notation a `#` k := term.vpp a k

@[derive has_reflect] inductive recipe : Type
| hyp (k : nat)   : recipe
| prm (c : cla)   : recipe → recipe
| sub (μ : smaps) : recipe → recipe
| con (b : bool) (k : nat) : recipe → recipe
| res (k m : nat) : recipe → recipe → recipe

namespace recipe

def repr_core : nat → recipe → string
| k (recipe.hyp m) := spaces k ++ "hyp " ++ m.repr ++ "\n"
| k (recipe.prm c ρ) :=
  spaces k ++ "prm " ++ c.repr ++ "\n" ++ (ρ.repr_core $ k + 2)
| k (recipe.sub μ ρ) :=
  spaces k ++ "sub " ++ μ.repr ++ "\n" ++ (ρ.repr_core $ k + 2)
| k (recipe.res m n ρ σ) :=
  spaces k ++ "res " ++ m.repr ++ " " ++ n.repr ++ "\n" ++
  (ρ.repr_core $ k + 2) ++ (σ.repr_core $ k + 2)
| k (recipe.con b m ρ) :=
  spaces k ++ "con " ++ b.repr ++ " " ++ m.repr ++
  "\n" ++ (ρ.repr_core $ k + 2)

def repr : recipe → string := repr_core 0

instance has_repr : has_repr recipe := ⟨repr⟩
meta instance has_to_format : has_to_format recipe := ⟨λ x, repr x⟩

def run (m : mat) : recipe → option cla
| (recipe.hyp k)   := m.nth k
| (recipe.prm d ρ) :=
   do c ← ρ.run,
      if cla.exteq c d
      then some d
      else none
| (recipe.sub μ ρ) :=
   do c ← ρ.run, some (c.subst μ)
| (recipe.con ff k ρ) :=
  do c ← ρ.run,
     t ← c.fst.nth k,
     option.guard (λ _, t ∈ c.fst.remove_nth k) (c.fst.remove_nth k, c.snd)
| (recipe.con tt k ρ) :=
  do c ← ρ.run,
     t ← c.snd.nth k,
     option.guard (λ _, t ∈ c.snd.remove_nth k) (c.fst, c.snd.remove_nth k)
| (recipe.res k n ρ σ) :=
  do c ← ρ.run,
     d ← σ.run,
     t ← c.snd.nth k,
     s ← d.fst.nth n,
     option.guard (λ _, t = s)
     (c.fst ++ d.fst.remove_nth n,
      c.snd.remove_nth k ++ d.snd)

end recipe

open tactic option list

lemma fav_of_run_eq_some
  (M : model α) (m : mat) (h0 : m.fav M) :
  ∀ ρ : recipe, ∀ c : cla, ρ.run m = some c → c.fav M
| (recipe.hyp k) c h1 v :=
  by { simp only [recipe.run] at h1,
       have h2 := list.mem_iff_nth.elim_right ⟨_, h1⟩,
       apply h0 _ _ h2 }
| (recipe.prm d ρ) c h0 v :=
  begin
    simp only [recipe.run, option.bind_eq_some] at h0,
    rcases h0 with ⟨e, h1, h2⟩,
    by_cases h3 : (cla.exteq e d),
    { rw if_pos h3 at h2,
      rw ← option.some.inj h2,
      have h4 := fav_of_run_eq_some _ _ h1 v,
      apply cla.holds_of_exteq h4 h3 },
    rw if_neg h3 at h2, cases h2
  end
| (recipe.sub μ ρ) c h1 v :=
  begin
    simp only [recipe.run] at h1,
    cases h2 : (ρ.run m) with d,
    { rw [h2, option.none_bind] at h1, cases h1 },
    rw [h2, option.some_bind] at h1,
    have h3 := fav_of_run_eq_some ρ d h2,
    rw [← option.some.inj h1, cla.holds_subst],
    apply h3
  end
| (recipe.con ff k ρ) c h1 v :=
  begin
    simp only [recipe.run] at h1,
    rw bind_eq_some at h1, rcases h1 with ⟨d, h1, h2⟩,
    rw bind_eq_some at h2, rcases h2 with ⟨t, h2, h3⟩,
    rw guard_eq_some at h3,
    cases h3 with h3 h4, subst h3,
    have h5 := fav_of_run_eq_some _ _ h1 v,
    cases d with nd pd,
    rcases h5 with ⟨s, h5, h6⟩ | h5,
    { left, refine ⟨s, _, h6⟩,
      rw mem_iff_nth_eq_some_or_mem_remove_nth k at h5,
      cases h5, {exact h5},
      have : s = t,
      { apply some.inj (eq.trans h5.symm h2) },
      rw this, assumption },
    right, apply h5
  end
| (recipe.con tt k ρ) c h1 v :=
  begin
    simp only [recipe.run] at h1,
    rw bind_eq_some at h1, rcases h1 with ⟨d, h1, h2⟩,
    rw bind_eq_some at h2, rcases h2 with ⟨t, h2, h3⟩,
    rw guard_eq_some at h3,
    cases h3 with h3 h4, subst h3,
    have h5 := fav_of_run_eq_some _ _ h1 v,
    cases d with nd pd,
    rcases h5 with h5 | ⟨s, h5, h6⟩,
    { left, apply h5 },
    right, refine ⟨s, _, h6⟩,
    rw mem_iff_nth_eq_some_or_mem_remove_nth k at h5,
    cases h5, {exact h5},
    have : s = t,
    { apply some.inj (eq.trans h5.symm h2) },
    rw this, assumption
  end
| (recipe.res k n ρ σ) c h1 v :=
  begin
    simp only [recipe.run] at h1,
    rw bind_eq_some at h1, rcases h1 with ⟨d, h1, h2⟩,
    rw bind_eq_some at h2, rcases h2 with ⟨e, h2, h3⟩,
    rw bind_eq_some at h3, rcases h3 with ⟨i, h3, h4⟩,
    rw bind_eq_some at h4, rcases h4 with ⟨j, h4, h5⟩,
    rw guard_eq_some at h5,
    rcases h5 with ⟨h5, h6⟩,
    subst h5, subst h6,
    cases d with nd pd,
    cases e with ne pe,
    rcases (fav_of_run_eq_some ρ _ h1 v)
      with ⟨t, ht1, ht2⟩ | ⟨t, ht1, ht2⟩,
    { left, refine ⟨t, mem_append_left _ ht1, ht2⟩ },
    rcases (fav_of_run_eq_some σ _ h2 v)
      with ⟨s, hs1, hs2⟩ | ⟨s, hs1, hs2⟩,
    { rw list.mem_iff_nth_eq_some_or_mem_remove_nth k at ht1,
      rw list.mem_iff_nth_eq_some_or_mem_remove_nth n at hs1,
      cases ht1,
      { right, refine ⟨t, mem_append_left _ ht1, ht2⟩ },
      cases hs1,
      { left, refine ⟨s, mem_append_right _ hs1, hs2⟩ },
      have ht3 : t = i,
      { apply some.inj (eq.trans ht1.symm h3) },
      have hs3 : s = i,
      { apply some.inj (eq.trans hs1.symm h4) },
      subst ht3, subst hs3, cases hs2 ht2 },
    right, refine ⟨s, mem_append_right _ hs1, hs2⟩
end

lemma tas_of_run_empty [inhabited α] (p : form) (ρ : recipe) :
  ρ.run (cnf p.neg).renumber = some ([], []) → p.tas α :=
begin
  rintros h0 M,
  apply classical.by_contradiction,
  rw not_exists, intro h3,
  rcases (fav_of_run_eq_some M _ _ ρ _ h0
    (vas.default α)) with ⟨_, ⟨_⟩, _⟩ | ⟨_, ⟨_⟩, _⟩,
  apply fav_renumber_of_fav,
  intro v, apply holds_cnf_of_holds,
  rw form.holds_neg, apply h3
end
