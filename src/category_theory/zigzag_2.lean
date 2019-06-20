-- Copyright (c) 2019 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.category
import category_theory.eq_to_hom
import category_theory.equivalence
import data.fin
import tactic

@[simp] lemma fin.last_val (n : ℕ) : (fin.last n).val = n := rfl

lemma squeeze {a b : ℕ} (h : a ≤ b) (h' : b < a + 1) : a = b :=
begin
  cases h, refl, linarith,
end


namespace tactic
meta def force {α : Type} (t : tactic α) : tactic α :=
do gs ← get_goals,
   r ← t,
   gs' ← get_goals,
   guard (gs ≠ gs') <|> fail "tactic succeeded, but did not change the goal",
   return r

namespace interactive
meta def force (t : itactic) := tactic.force t
end interactive
end tactic

open opposite

namespace category_theory

universes v₁ u₁ -- declare the `v`'s first; see `category_theory.category` for an explanation

def Δ := ℕ
instance : category Δ :=
{ hom := λ n m, { f : fin n → fin m | monotone f},
  id := λ n, ⟨id, by obviously⟩,
  comp := λ l m n f g, ⟨g.val ∘ f.val, by obviously⟩ }

namespace Δ
instance  {n m : Δ} : has_coe_to_fun (n ⟶ m) :=
{ F := λ f, fin n → fin m,
  coe := λ f, f.val }

@[simp] lemma id_coe {n : Δ} (x : fin n) : ((𝟙 n) : fin n → fin n) x = x := rfl
@[simp] lemma comp_coe {l m n : Δ} (f : l ⟶ m) (g : m ⟶ n) (x : fin l) : (f ≫ g : fin l → fin n) x = g (f x) := rfl
@[simp] lemma mk_coe {n m : Δ} (f : fin n → fin m) (h) (x) : (⟨f, h⟩ : n ⟶ m) x = f x := rfl

@[extensionality] lemma hom_ext {n m : Δ} {f g : n ⟶ m} (h : (f : fin n → fin m) = g) : f = g :=
begin
  cases f,
  cases g,
  congr,
  assumption,
end

end Δ

def above {n m : Δ} (f : n ⟶ m) (j : fin m) := { i : fin n | f i ≥ j }

def T_map {n m : Δ} (f : n ⟶ m) : fin (n + 1) →  fin (m + 1) :=
λ i, if h : i.val < n then (f (i.cast_lt h)).cast_succ else fin.last _

lemma T_map_mono {n m : Δ} {f : n ⟶ m} : monotone (T_map f) :=
λ a b h,
begin
  cases f,
  dsimp [T_map] at *,
  split_ifs,
  {tidy},
  {apply fin.le_last},
  {rw [fin.le_iff_val_le_val] at h,
  dsimp [(Δ)] at n, -- without this line linarith doesn't know that n : ℕ and fails
  linarith},
  {apply fin.le_last}
end

lemma T_map_id {n : Δ} : T_map (𝟙 _) = @id (fin (n + 1)) :=
funext (λ a,
begin
  dsimp [T_map],
  split_ifs,
  {tidy},
  {exact fin.eq_of_veq (eq.trans rfl (eq.symm (nat.eq_of_lt_succ_of_not_lt a.is_lt h)))}
end)

-- These two lemmas should go in fin.lean. Something similiar might already be in mathlib.
lemma cast_succ_val_lt {n : ℕ} {i : fin n} : (fin.cast_succ i).val < n :=
begin
 rw [fin.cast_succ_val],
 exact i.is_lt,
end

lemma cast_lt_cast_succ {n : ℕ} (i : fin n) :
  fin.cast_lt (fin.cast_succ i) (cast_succ_val_lt) = i :=
fin.eq_of_veq (by simp only [fin.cast_lt_val, fin.cast_succ_val])

lemma T_map_comp {l m n : Δ} {f : l ⟶ m} {g : m ⟶ n} : T_map (f ≫ g) = (T_map g) ∘ (T_map f) :=
funext (λ a,
begin
  dsimp [T_map],
  split_ifs,
  { -- a.val < l
    by_cases h2 : ((dite (a.val < l) (λ h, fin.cast_succ (f (fin.cast_lt a h)))
      (λ h, fin.last m)).val < m), -- see https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60split_ifs.60.2C.20and.20nested.20.60dite.60/near/167593063
    { -- (dite (a.val < l) (λ h, fin.cast_succ (f (fin.cast_lt a h))) (λ h, fin.last m)).val < m
      rw dif_pos h2,
      split_ifs,
      simp [cast_lt_cast_succ] at *,
    },
    { -- ¬((dite (a.val < l) (λ h, fin.cast_succ (f (fin.cast_lt a h))) (λ h, fin.last m)).val < m)
      rw dif_neg h2,
      split_ifs at h2,
      rw [fin.cast_succ_val] at h2,
      exact absurd ((f (fin.cast_lt a h)).is_lt) h2,
    },
  },
  { -- ¬(a.val < l)
    by_cases h2 : ((dite (a.val < l) (λ h, fin.cast_succ (f (fin.cast_lt a h)))
            (λ h, fin.last m)).val < m),
    { -- (dite (a.val < l) (λ h, fin.cast_succ (f (fin.cast_lt a h))) (λ h, fin.last m)).val < m
      rw dif_pos h2,
      split_ifs at h2 with h3, -- with h3 isn't working. split_ifs introduces a new variable called h2
      simp [fin.last] at h2,
      dsimp [(Δ)] at m,
      exact (absurd h2_1 (irrefl m)),
    },
    { -- ¬((dite (a.val < l) (λ h, fin.cast_succ (f (fin.cast_lt a h))) (λ h, fin.last m)).val < m)
      rw dif_neg h2,
    },
  }
end)

def T : Δ ⥤ Δ :=
{ obj := λ n, (n + 1 : ℕ),
  map := λ n m f, ⟨T_map f, T_map_mono⟩,
  map_id' := λ n, Δ.hom_ext T_map_id,
  map_comp' := λ l n m f g, Δ.hom_ext T_map_comp}



def Δ_ := ℕ
instance : has_coe Δ_ Δ :=
{ coe := λ n, (n + 1 : ℕ) }

instance category_Δ_ : category Δ_ :=
{ hom := λ n m, { f : fin (n+1) → fin (m+1) | monotone f ∧ f 0 = 0 ∧ f (fin.last _) = fin.last _ },
  id := λ n, ⟨id, by obviously⟩,
  comp := λ l m n f g, ⟨g.val ∘ f.val,
  by obviously,
  by {cases g with _ hg,
      cases f with _ hf,
      dsimp at *,
      rw [hf.2.1, hg.2.1]},
  by {cases g with _ hg,
      cases f with _ hf,
      dsimp at *,
      rw [hf.2.2, hg.2.2]}⟩ }.


def prime_obj (n : Δ) : Δ_ᵒᵖ := op (n : ℕ)
def prime_map_fn {n m : Δ} (f : n ⟶ m) (j : fin (m + 1)) : fin (n + 1) := sorry
def prime_map {n m : Δ} (f : n ⟶ m) : (prime_obj n) ⟶ (prime_obj m) :=
begin
  apply has_hom.hom.op,
  fsplit,
  exact prime_map_fn f,

  sorry,
end

def prime : Δ ⥤ Δ_ᵒᵖ :=
{ obj := prime_obj,
  map := λ n m f, prime_map f,
  map_id' := sorry,
  map_comp' := sorry }

namespace prime
instance : ess_surj prime := sorry
instance : full prime := sorry
instance : faithful prime := sorry

def is_equivalence : is_equivalence prime :=
  is_equivalence.of_fully_faithfully_ess_surj prime
end prime

variables (C : Type u₁) [𝒞 : category.{v₁} C]
include 𝒞

structure zigzag :=
(n : Δ)
(singular : fin n → C)
(regular : fin (n+1) → C)
(forwards : Π (i : fin n), regular (i.cast_succ) ⟶ singular i)
(backwards : Π (i : fin n), regular (i.succ) ⟶ singular i)

namespace zigzag

structure hom (X Y : zigzag.{v₁} C):=
(f : fin X.n → fin Y.n)


end zigzag

end category_theory
