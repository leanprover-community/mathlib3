/-
  Copyright (c) 2019 Seul Baek. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Seul Baek

  Second-order substitutions.
-/

import tactic.spass.term2
import logic.basic logic.function

universe u

variable {α : Type u}

local notation f `₀↦` a := assign a f
local notation `#` := term₂.var
local notation a `&` b := term₂.app a b

@[reducible] def sub₂ : Type := list (nat × term₂)

namespace sub₂

open list

@[reducible] def incr : sub₂ → sub₂ :=
map (prod.map nat.succ (term₂.incr))

def get (k : nat) : sub₂ → option term₂
| []            := none
| ((m, a) :: σ) := if k = m then a else get σ

end sub₂

lemma get_eq_of_ne {k m : nat} (a : term₂) (σ : sub₂) :
  k ≠ m → sub₂.get k ((m, a) :: σ) = sub₂.get k σ :=
by {intro h0, simp only [sub₂.get, if_neg h0]}

lemma get_zero_incr :
  ∀ σ : sub₂, σ.incr.get 0 = none
| []            := rfl
| ((m, a) :: σ) :=
  begin
    have h0 : sub₂.get 0 (sub₂.incr ((m, a) :: σ)) =
              sub₂.get 0 (sub₂.incr σ),
    { apply get_eq_of_ne,
      apply (ne.symm $ nat.succ_ne_zero _) },
    rw h0, apply get_zero_incr,
  end

lemma get_succ_incr (k : nat) :
  ∀ σ : sub₂, σ.incr.get (k + 1) = term₂.incr <$> (σ.get k)
| []            := rfl
| ((m, a) :: σ) :=
  begin
    by_cases h0 : k = m,
    { have h1 : sub₂.get (k + 1) (sub₂.incr ((m, a) :: σ)) =
                some a.incr,
      { simp only [sub₂.get, sub₂.incr, if_true,
          prod.map, list.map, eq_self_iff_true, h0],
        refl },
     have h2 : term₂.incr <$> sub₂.get k ((m, a) :: σ) =
               some a.incr,
     { simp only [sub₂.get, sub₂.incr, if_true,
       prod.map, list.map, eq_self_iff_true, h0], refl },
     simp only [h1, h2] },
    have h1 : sub₂.get (k + 1) (sub₂.incr ((m, a) :: σ)) =
              sub₂.get (k + 1) (sub₂.incr σ),
    { simp only [sub₂.get, sub₂.incr, if_false, prod.map,
     list.map, eq_self_iff_true, not.imp h0 nat.succ_inj] },
    have h2 : term₂.incr <$> sub₂.get k ((m, a) :: σ) =
              term₂.incr <$> sub₂.get k σ,
    { simp only [sub₂.get, sub₂.incr, if_false,
      prod.map,list.map, eq_self_iff_true, h0] },
    simp only [h1, h2, get_succ_incr σ]
  end

namespace term₂

def subst (σ : sub₂) : term₂ → term₂
| (# k)   := (σ.get k).get_or_else (# k)
| (a & b) := a.subst & b.subst

lemma subst_eq_of_get_eq_none {σ : sub₂} {k : nat} :
  σ.get k = none → (# k).subst σ = # k :=
by {intro h1, simp only [h1, option.get_or_else, subst]}

lemma subst_eq_of_get_eq_some {σ : sub₂} {k : nat} {a : term₂} :
  σ.get k = some a → (# k).subst σ = a :=
by {intro h1, simp only [h1, option.get_or_else, subst]}

end term₂

namespace model

def subst (M : model α) (σ : sub₂) : model α :=
λ k : nat,
match σ.get k with
| none   := M k
| some a := a.val M
end

lemma subst_eq_of_get_eq_none
  (M : model α) {σ : sub₂} {k : nat} :
  σ.get k = none → M.subst σ k = M k :=
by {intro h1, simp only [h1, model.subst]}

lemma subst_eq_of_get_eq_some
  (M : model α) {σ : sub₂} {k : nat} {a : term₂} :
  σ.get k = some a → M.subst σ k = a.val M :=
by {intro h1, simp only [h1, model.subst]}

lemma assign_subst (M : model α) (v : value α) (σ : sub₂) :
  ((M.subst σ) ₀↦ v) = (subst (M ₀↦ v) σ.incr) :=
begin
  rw function.funext_iff,
  intro k, cases k,
  { have h0 := get_zero_incr σ,
    simp only [subst, h0], refl },
  have h0 := get_succ_incr k σ,
  cases h1 : sub₂.get k σ with a,
  { rw h1 at h0,
    have h2 : (subst M σ ₀↦v) k.succ = M k,
    { simp only [assign, model.subst_eq_of_get_eq_none _ h1] },
    have h3 : subst (M ₀↦v) (sub₂.incr σ) k.succ = M k,
    { simp only [assign, model.subst_eq_of_get_eq_none _ h0] },
    simp only [h2, h3] },
  rw h1 at h0,
  have h2 : (subst M σ ₀↦v) k.succ = a.val M,
  { simp only [assign, model.subst_eq_of_get_eq_some _ h1] },
  have h3 : subst (M ₀↦v) (sub₂.incr σ) k.succ = a.val M,
  { simp only [assign, subst_eq_of_get_eq_some _ h0,
    term₂.val_assign_incr] },
  simp only [h2, h3]
end

end model

lemma val_subst (M : model α) (σ : sub₂) :
  ∀ a : term₂, term₂.val M (a.subst σ) = term₂.val (M.subst σ) a
| (# k) :=
  begin
    rw function.funext_iff, intro as,
    cases h1 : σ.get k with s,
    { simp only [term₂.val, term₂.subst_eq_of_get_eq_none h1,
        model.subst_eq_of_get_eq_none M h1] },
    simp only [term₂.val, term₂.subst_eq_of_get_eq_some h1,
      model.subst_eq_of_get_eq_some M h1],
  end
| (a & b) :=
  begin
    rw function.funext_iff, intro as,
    have h1 := val_subst a,
    have h2 := val_subst b,
    simp only [term₂.val, term₂.subst, h1, h2],
  end
