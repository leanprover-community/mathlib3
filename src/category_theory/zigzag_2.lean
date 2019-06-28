-- Copyright (c) 2019 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.category
import category_theory.eq_to_hom
import category_theory.equivalence
import data.fin data.finset data.fintype
import category_theory.opposites
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

instance : has_coe Δ ℕ := {coe := λ n, n}

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

-- These two lemmas should go in fin.lean. Something similiar might already be in mathlib.
lemma cast_succ_val_lt {n : ℕ} {i : fin n} : (fin.cast_succ i).val < n :=
begin
 rw [fin.cast_succ_val],
 exact i.is_lt,
end

lemma cast_lt_cast_succ {n : ℕ} (i : fin n) (h : (fin.cast_succ i).val < n) :
  fin.cast_lt (fin.cast_succ i) h = i :=
fin.eq_of_veq (by simp only [fin.cast_lt_val, fin.cast_succ_val])

lemma cast_lt_succ {n : ℕ} (i : fin n) (h₁ : (fin.succ i).val < n) (h₂ : i.val + 1 < n) :
  fin.cast_lt (fin.succ i) h₁ = ⟨i.val + 1, h₂⟩ :=
fin.eq_of_veq $ by rw [fin.cast_lt_val, fin.succ_val]

section T
def T_map {n m : Δ} (f : n ⟶ m) : fin (n + 1) →  fin (m + 1) :=
λ i, if h : i.val < n then (f (i.cast_lt h)).cast_succ else fin.last _




lemma T_map_mono {n m : Δ} (f : n ⟶ m) : monotone (T_map f) :=
λ a b h,
begin
  cases f,
  dsimp [T_map] at *,
  split_ifs,
  { solve_by_elim },
  { apply fin.le_last },
  { rw [fin.le_iff_val_le_val] at h,
    dsimp [(Δ)] at n, -- without this line linarith doesn't know that n : ℕ and fails
    linarith },
  { apply fin.le_last }
end

lemma T_map_id {n : Δ} (a : fin (n+1)) : T_map (𝟙 _) a = a :=
begin
  dsimp [T_map],
  split_ifs,
  { simp },
  { exact fin.eq_of_veq (eq.trans rfl (eq.symm (nat.eq_of_lt_succ_of_not_lt a.is_lt h))) }
end


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
  map := λ n m f, ⟨T_map f, T_map_mono f⟩,
  map_id' := λ n, Δ.hom_ext (funext T_map_id),
  map_comp' := λ l n m f g, Δ.hom_ext T_map_comp}

lemma T_map_f_eq_f {n m : Δ} (f : n ⟶ m) {j : fin n} :
  T_map f (fin.cast_succ j) = fin.cast_succ (f j) :=
begin
  dsimp [T_map],
  split_ifs,
  {rw [cast_lt_cast_succ]},
  {exact absurd j.is_lt h}
end

lemma T_f_eq_f {n m : Δ} (f : n ⟶ m) {j : fin n} :
  T.map f (fin.cast_succ j) = fin.cast_succ (f j) :=
begin
  dsimp [T],
  apply T_map_f_eq_f
end



end T

section above

-- Changed above to be of type finset (fin n) rather than set (fin n)
def above {n m : Δ} (f : n ⟶ m) (j : fin m) := finset.univ.filter { i : fin n | f i ≥ j }

@[simp] lemma mem_above_iff {n m : Δ} {f : n ⟶ m} {j : fin m} {i : fin n} :
  (i ∈ (above f j)) ↔ f i ≥ j :=
⟨λ h, (finset.mem_filter.1 h).2, λ h, finset.mem_filter.2 ⟨finset.mem_univ i, h⟩⟩

lemma n_mem_above_of_T {n m : Δ} {f : n ⟶ m} {j : fin (m + 1)} :
  fin.mk n (lt_add_one _) ∈ (above (T.map f) j) :=
mem_above_iff.2
begin
  {show T_map f ⟨n,_⟩ ≥ j,
  dsimp [T_map],
  dsimp [(Δ)] at n,
  have h : ¬(n < n) := irrefl n,
  split_ifs,
  apply fin.le_last,}
end

lemma above_of_T_non_empty {n m : Δ} {f : n ⟶ m} {j : fin (m + 1)} :
  above (T.map f) j ≠ ∅ := finset.ne_empty_of_mem n_mem_above_of_T

def prime_map_fn {n m : Δ} (f : n ⟶ m) (j : fin (m + 1)) : fin (n + 1) :=
(above (T.map f) j).min' above_of_T_non_empty

lemma prime_map_fn_mem_above {n m : Δ} {f : n ⟶ m} {j : fin (m + 1)} :
  prime_map_fn f j ∈ above (T.map f) j :=
finset.min'_mem _ above_of_T_non_empty

lemma prime_map_fn_le {n m : Δ} {f : n ⟶ m} {j : fin (m + 1)} {i : fin (n + 1)}
    (h : (T.map f) i ≥ j) : prime_map_fn f j ≤ i :=
finset.min'_le _ _ _ (mem_above_iff.2 h)

lemma le_prime_map_fn {n m : Δ} {f : n ⟶ m} {j : fin (m + 1)} {i : fin (n + 1)}
    (h : ∀ k : fin (n + 1), (T.map f) k ≥ j → i ≤ k) : i ≤ prime_map_fn f j :=
finset.le_min' _ _ _ $ λ _ w, h _ (mem_above_iff.1 w)

lemma T_f_of_prime_map_fn_ge {n m : Δ} (f : n ⟶ m) (j : fin (m + 1)) :
  (T.map f) (prime_map_fn f j) ≥ j :=
mem_above_iff.1 prime_map_fn_mem_above

lemma zero_lt_T_obj {n : Δ} : (0 : ℕ) < T.obj n := by {dsimp [T], apply nat.succ_pos}

lemma prime_map_fn_zero_eq_zero {n m : Δ} {f : n ⟶ m} :
  prime_map_fn f ⟨0, zero_lt_T_obj⟩ = ⟨0, zero_lt_T_obj⟩ :=
le_antisymm (prime_map_fn_le (fin.zero_le _)) (fin.zero_le _)

lemma above_subset_above {n m : Δ} {f : n ⟶ m} {j k : fin m} (h : j ≥ k) :
  above f j ⊆ above f k :=
λ i w, mem_above_iff.2 $ ge_trans (mem_above_iff.1 w) h

lemma prime_map_mono {n m : Δ} {f : n ⟶ m} {j k : fin (m + 1)} (h : j ≤ k) :
  prime_map_fn f j ≤ prime_map_fn f k :=
finset.min'_le _ _ _ $ (above_subset_above h) prime_map_fn_mem_above

lemma n_le_mem_above_T_m {n m : Δ} {f : n ⟶ m} {i : fin (n+1)} (h : (T.map f) i ≥ fin.last m) :
  fin.last n ≤ i :=
begin
  cases f,
  dsimp at *,
  dsimp [T, T_map] at *,
  split_ifs at h with w,
  {-- i.val < n
  dsimp [(≥), (≤), fin.le] at h,
  have w' : (f_val (fin.cast_lt i w)).val < m := (f_val (fin.cast_lt i w)).is_lt,
  exact absurd h (nat.lt_le_antisymm w')
  },
  {-- ¬ i.val < n
  exact not_lt.mp w}
end

lemma prime_map_fn_top_eq_top {n m : Δ} {f : n ⟶ m} :
  prime_map_fn f (fin.last m) = fin.last n :=
le_antisymm (fin.le_last _) (finset.le_min' _ _ _ $ λ i h, n_le_mem_above_T_m (mem_above_iff.1 h))

lemma prime_map_fn_id {n : Δ} {i : fin (n + 1)} :
  prime_map_fn (𝟙 _) i = i :=
le_antisymm
(prime_map_fn_le (by {rw [T.map_id'], exact le_refl _}))
(finset.le_min' _ _ _ (λ j h, by {rw [T.map_id'] at h, exact (mem_above_iff.1 h)}))

lemma prime_map_fn_comp_le {l m n : Δ} {f : l ⟶ m} {g : m ⟶ n} {i : fin (n + 1)} :
  prime_map_fn (f ≫ g) i ≤ prime_map_fn f (prime_map_fn g i) :=
prime_map_fn_le
begin
  rw [T.map_comp'],
  simp [Δ.comp_coe],
  have w := T_f_of_prime_map_fn_ge g i,
  cases (T.map g) with g_T mono,
  exact ge_trans (mono (T_f_of_prime_map_fn_ge f (prime_map_fn g i))) w,
end

lemma le_prime_map_fn_comp {l m n : Δ} {f : l ⟶ m} {g : m ⟶ n} {i : fin (n + 1)} :
  prime_map_fn f (prime_map_fn g i) ≤ prime_map_fn (f ≫ g) i :=
le_prime_map_fn $ λ k w,
begin
  rw [T.map_comp'] at w,
  simp [Δ.comp_coe] at w,
  exact prime_map_fn_le (prime_map_fn_le w),
end

lemma prime_map_fn_comp {l m n : Δ} {f : l ⟶ m} {g : m ⟶ n} {i : fin (n + 1)} :
  prime_map_fn (f ≫ g) i = prime_map_fn f (prime_map_fn g i)  :=
le_antisymm prime_map_fn_comp_le le_prime_map_fn_comp


end above

section Δ_
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

end Δ_

namespace Δ_

instance  {n m : Δ_} : has_coe_to_fun (n ⟶ m) :=
{ F := λ f, fin (n + 1) → fin (m + 1),
  coe := λ f, f.val }

@[simp] lemma id_coe {n : Δ_} (x : fin n) : ((𝟙 n) : fin (n + 1) → fin _) x = x := rfl
@[simp] lemma comp_coe {l m n : Δ_} (f : l ⟶ m) (g : m ⟶ n) (x : fin (l+1)) :
  (f ≫ g : fin _ → fin _) x = g (f x)
:= rfl
@[simp] lemma mk_coe {n m : Δ_} (f : fin _ → fin _) (h) (x) : (⟨f, h⟩ : n ⟶ m) x = f x := rfl

@[extensionality] lemma hom_ext {n m : Δ_} {f g : n ⟶ m} (h : (f : fin _ → fin _) = g) : f = g :=
begin
  cases f,
  cases g,
  congr,
  assumption,
end

instance : has_coe Δ_ᵒᵖ ℕ := {coe := λ n, unop n}

@[simp] lemma op_id_coe {n : Δ_ᵒᵖ} (x) : ((𝟙 n) : fin (n + 1) → fin _) x = x := rfl
@[simp] lemma op_comp_coe {l m n : Δ_ᵒᵖ} (f : l ⟶ m) (g : m ⟶ n) (x : fin _) :
  (f ≫ g : fin _ → fin _) x = f (g x)
:= rfl

@[extensionality] lemma op_hom_ext {n m : Δ_ᵒᵖ} {f g : n ⟶ m} (h : (f : fin _ → fin _) = g) :
  f = g :=
has_hom.hom.unop_inj $ hom_ext h


@[simp] lemma f_zero {m n : Δ_} {f : n ⟶ m} : f 0 = 0 := by tidy
@[simp] lemma f_op_zero {m n : Δ_ᵒᵖ} {f : n ⟶ m} : f 0 = 0 := f_zero

@[simp] lemma f_last {m n : Δ_} {f : n ⟶ m} : f (fin.last _) = fin.last _ := by tidy
@[simp] lemma f_op_last {m n : Δ_ᵒᵖ} {f : n ⟶ m} : f (fin.last m) = fin.last _ := f_last

lemma f_mono {n m : Δ_} (f : n ⟶ m) : monotone f :=
by tidy
lemma f_op_mono {n m : Δ_ᵒᵖ} (f : n ⟶ m) : monotone f := f_mono _

end Δ_

section prime

def prime_obj (n : Δ) : Δ_ᵒᵖ := op (n : ℕ)


def prime_map {n m : Δ} (f : n ⟶ m) : (prime_obj n) ⟶ (prime_obj m) :=
has_hom.hom.op
  ⟨prime_map_fn f,
  -- f' mono
  λ j k h, prime_map_mono h,
  -- f' 0 = 0
  prime_map_fn_zero_eq_zero
  ,
  -- f' m = n
  prime_map_fn_top_eq_top⟩


lemma prime_map_id (n : Δ) : prime_map (𝟙 n) = 𝟙 _ :=
Δ_.op_hom_ext (funext (λ _,
begin
  rw [Δ_.op_id_coe],
  dsimp [prime_map, has_hom.hom.op],
  exact prime_map_fn_id
end))

lemma prime_map_comp (l m n : Δ) (f : l ⟶ m) (g : m ⟶ n) :
  prime_map (f ≫ g) = prime_map f ≫ prime_map g :=
Δ_.op_hom_ext (funext (λ _,
begin
  rw [Δ_.op_comp_coe],
  dsimp [prime_map, has_hom.hom.op],
  apply prime_map_fn_comp,
end))


def prime : Δ ⥤ Δ_ᵒᵖ :=
{ obj := prime_obj,
  map := λ _ _ f, prime_map f,
  map_id' := prime_map_id,
  map_comp' := prime_map_comp }

lemma f_lt_of_neq {n m : Δ} {f : n ⟶ m} {i j : fin n} (w : i ≤ j) (h : f i ≠ f j) :
  f i < f j := lt_of_le_of_ne (f.property w) h

lemma prime_f_of_f_succ_le_succ  {n m : Δ} {f : n ⟶ m} {i : fin n} (w : i.val + 1 < n)
    (h : f i ≠ f ⟨i.val+1,w⟩) : prime.map f (f i).succ ≤ i.succ :=
prime_map_fn_le
begin
  have w'' : i ≤ ⟨i.val+1,w⟩ := nat.le_succ _,
  have w' := f_lt_of_neq w'' h,
  dsimp [T,T_map],
  split_ifs with h₁,
  { rw [cast_lt_succ i h₁ w],
    dsimp [(≥), (≤), (<), (fin.le), (fin.lt)] at *,
    rw [fin.succ_val] at *,
    apply w',},
  {apply fin.le_last}
end

lemma lt_succ_iff_le_cast_succ {n : ℕ} {i : fin n} {j : fin (n + 1)} :
  j < i.succ ↔ j ≤ i.cast_succ :=
begin
  dsimp [(<), (≤), (fin.le), (fin.lt)],
  rw fin.succ_val,
  exact nat.lt_succ_iff
end

lemma succ_le_prime_f_of_f_succ  {n m : Δ} {f : n ⟶ m} {i : fin n} (w : i.val + 1 < n)
    (h : f i ≠ f ⟨i.val+1,w⟩) : i.succ ≤ prime.map f (f i).succ :=
le_prime_map_fn $ λ k T_k_ge,
begin
  by_contradiction, -- is there such a thing as by_contradiction with a?
  have w' : T.map f k ≤ T.map f i.cast_succ :=
      (T.map f).property (lt_succ_iff_le_cast_succ.1 (lt_of_not_ge a)),
  rw [T_f_eq_f] at w',
  exact nat.lt_le_antisymm (lt_succ_iff_le_cast_succ.2 w') T_k_ge
end


lemma prime_f_of_f {n m : Δ} {f : n ⟶ m} {i : fin n} {w : i.val + 1 < n} (h : f i ≠ f ⟨i.val+1,w⟩)
 : i.succ = prime.map f (f i).succ  :=
le_antisymm (succ_le_prime_f_of_f_succ w h) (prime_f_of_f_succ_le_succ w h)

lemma prime_f_lt_n {n m : Δ} {f : n ⟶ m} {j : fin m} (h : prime.map f j.cast_succ ≠ prime.map f j.succ) :
  (prime.map f j.cast_succ).val < n :=
begin
  have w : j.cast_succ ≤ j.succ := by {dsimp [(≤), fin.le], rw [fin.succ_val], apply nat.le_succ},
  have w' : prime.map f j.cast_succ < prime.map f j.succ := lt_of_le_of_ne (Δ_.f_op_mono _ w) h,
  dsimp [(<), fin.lt] at w',
  exact lt_of_lt_of_le w' (fin.le_last _),
end

-- Still need to prove this lemma
lemma f_prime_f_j_le_j {n m : Δ} {f : n ⟶ m} {j : fin m}
    {h : prime.map f j.cast_succ ≠ prime.map f j.succ} :
  f ((prime.map f j.cast_succ).cast_lt (prime_f_lt_n h)) ≤ j := sorry

lemma j_le_f_prime_f_j {n m : Δ} {f : n ⟶ m} {j : fin m}
    {h : prime.map f j.cast_succ ≠ prime.map f j.succ} :
  j ≤ f ((prime.map f j.cast_succ).cast_lt (prime_f_lt_n h)) :=
begin
  dsimp [prime] at *,
  have w := T_f_of_prime_map_fn_ge f j.cast_succ,
  dsimp [T, T_map] at *,
  split_ifs at w with h_1,
  {apply w},
  {exact absurd (prime_f_lt_n h) h_1},
end


lemma f_prime_f_j_eq_j {n m : Δ} {f : n ⟶ m} {j : fin m}
    (h : prime.map f j.cast_succ ≠ prime.map f j.succ) :
  f ((prime.map f j.cast_succ).cast_lt (prime_f_lt_n h)) = j :=
le_antisymm f_prime_f_j_le_j j_le_f_prime_f_j


end prime

section below

def below {n m : ℕ} (f : fin (m + 1) → fin (n + 1)) (j : fin (n + 1)) :=
  finset.univ.filter {i : fin (m + 1) | f i ≤ j}

@[simp] lemma mem_below_iff {n m : ℕ} {f : fin (m + 1) → fin (n + 1)} {j : fin (n + 1)}
    {i : fin (m + 1)} :
  (i ∈ (below f j)) ↔ f i ≤ j :=
⟨λ h, (finset.mem_filter.1 h).2, λ h, finset.mem_filter.2 ⟨finset.mem_univ i, h⟩⟩


lemma zero_mem_below {n m : Δ_ᵒᵖ} {f : n ⟶ m} {j : fin (n + 1)} :
  (0 : fin (m + 1)) ∈ (below f j) :=
mem_below_iff.2
begin
  {show f 0 ≤ j,
  rw [Δ_.f_op_zero],
  exact fin.zero_le _,}
end

lemma below_non_empty {n m : Δ_ᵒᵖ} {f : n ⟶ m} {j : fin (n + 1)} :
  below f j ≠ ∅ := finset.ne_empty_of_mem zero_mem_below

lemma below_subset_below {n m : Δ_ᵒᵖ} {f : n ⟶ m} {j k : fin (n + 1)} (h : j ≤ k) :
  below f j ⊆ below f k :=
λ x w, mem_below_iff.2 $ le_trans (mem_below_iff.1 w) h


lemma m_not_in_below {n m : Δ_ᵒᵖ} {f : n ⟶ m} {j : fin n} :
  (fin.last m : fin (unop m + 1)) ∉ below f (fin.cast_succ j) := λ h,
begin
  have w := mem_below_iff.1 h,
  rw [Δ_.f_op_last] at w,
  dsimp [fin.last, (≤), fin.le] at w,
  exact nat.lt_le_antisymm (j.is_lt) w
end



def prime_inv_map_fn_aux {n m : Δ_ᵒᵖ} (f : n ⟶ m) (j : fin n) : fin (m + 1) :=
  finset.max' (below f (fin.cast_succ j)) below_non_empty

lemma prime_inv_map_fn_aux_mem_below {n m : Δ_ᵒᵖ} {f : n ⟶ m} {j : fin n} :
  prime_inv_map_fn_aux f j ∈ below f (fin.cast_succ j) :=
finset.max'_mem _ _

lemma f_prime_inv_map_fn_aux_le {n m : Δ_ᵒᵖ} {f : n ⟶ m} {j : fin n} :
  f (prime_inv_map_fn_aux f j) ≤ fin.cast_succ j :=
mem_below_iff.1 prime_inv_map_fn_aux_mem_below

lemma prime_inv_map_fn_aux_le {n m : Δ_ᵒᵖ} {f : n ⟶ m} {j : fin n} {i : fin (m + 1)}
    (h : ∀ k : fin (m + 1), f k ≤ fin.cast_succ j → k ≤ i) : prime_inv_map_fn_aux f j ≤ i :=
finset.max'_le _ _ _(λ k w, h _ (mem_below_iff.1 w))


lemma prime_inv_map_fn_aux_ge {n m : Δ_ᵒᵖ} {f : n ⟶ m} {j : fin n} {i : fin (m + 1)}
    (h : f i ≤ (fin.cast_succ j)) :
  i ≤ prime_inv_map_fn_aux f j := finset.le_max' _ _ _ (mem_below_iff.2 h)

-- Again these should go in fin
lemma cast_succ_le {n : ℕ} {j k : fin n} (h : j ≤ k) : fin.cast_succ j ≤ fin.cast_succ k := h

lemma cast_succ_le' {n : ℕ} {j k : fin n} (h : fin.cast_succ j ≤ fin.cast_succ k) : j ≤ k := h

lemma cast_lt_le {n : ℕ} {j k : fin (n + 1)} {j_lt : j.val < n} {k_lt : k.val < n} (h : j ≤ k) :
  fin.cast_lt j j_lt ≤ fin.cast_lt k k_lt :=
h

lemma prime_inv_map_fn_aux_mono {n m : Δ_ᵒᵖ} {f : n ⟶ m} {j k : fin n} (h : j ≤ k) :
  prime_inv_map_fn_aux f j ≤ prime_inv_map_fn_aux f k :=
prime_inv_map_fn_aux_ge $
    mem_below_iff.1 ((below_subset_below (cast_succ_le h)) prime_inv_map_fn_aux_mem_below)


lemma prime_inv_map_fn_aux_neq_m {n m : Δ_ᵒᵖ} {f : n ⟶ m} {j : fin n} :
  (prime_inv_map_fn_aux f j).val ≠ (fin.last m).val :=
λ h,
begin
  have w := @prime_inv_map_fn_aux_mem_below _ _ f j,
  rw (fin.eq_of_veq h) at w,
  exact m_not_in_below w,
end

lemma prime_inv_map_fn_aux_lt_n {n m : Δ_ᵒᵖ} {f : n ⟶ m} {j : fin n} :
  (prime_inv_map_fn_aux f j).val < m :=
nat.lt_of_le_and_ne
  (nat.le_of_lt_succ (prime_inv_map_fn_aux f j).is_lt)
  (begin
    have w' := @prime_inv_map_fn_aux_neq_m _ _ f j,
    simp only [fin.last_val] at w',
    exact w',
  end)

def prime_inv_map_fn {n m : Δ_ᵒᵖ} (f : n ⟶ m) (j : fin n) : fin m :=
fin.cast_lt (prime_inv_map_fn_aux f j) prime_inv_map_fn_aux_lt_n

lemma cast_succ_prime_inv_map_fn {n m : Δ_ᵒᵖ} (f : n ⟶ m) (j : fin n) :
  fin.cast_succ (prime_inv_map_fn f j) = prime_inv_map_fn_aux f j := fin.cast_succ_cast_lt _ _

lemma f_prime_inv_map_fn_le {n m : Δ_ᵒᵖ} (f : n ⟶ m) (j : fin n) :
  f (fin.cast_succ (prime_inv_map_fn f j)) ≤ fin.cast_succ j :=
begin
  rw [cast_succ_prime_inv_map_fn],
  exact cast_succ_le f_prime_inv_map_fn_aux_le,
end


lemma prime_inv_map_fn_ge {n m : Δ_ᵒᵖ} {f : n ⟶ m} {j : fin n} {i : fin (m + 1)}
    (h : f i ≤ (fin.cast_succ j)) :
  i ≤ fin.cast_succ (prime_inv_map_fn f j) :=
finset.le_max' _ _ _ (mem_below_iff.2 h)

lemma prime_inv_map_fn_le {n m : Δ_ᵒᵖ} {f : n ⟶ m} {j : fin n} {i : fin m}
    (h : ∀ k : fin (m + 1), f k ≤ fin.cast_succ j → k ≤ fin.cast_succ i) :
  prime_inv_map_fn f j ≤ i :=
begin
  dsimp [prime_inv_map_fn],
  rw [←cast_lt_cast_succ i],
  apply prime_inv_map_fn_aux_le h,
  exact i.is_lt,
end

lemma prime_inv_map_fn_mono {n m : Δ_ᵒᵖ} {f : n ⟶ m} : monotone (prime_inv_map_fn f) :=
λ _ _ h, cast_lt_le (prime_inv_map_fn_aux_mono h)

def prime_inv_obj (n : Δ_ᵒᵖ) : Δ := unop n

def prime_inv_map {n m : Δ_ᵒᵖ} (f : n ⟶ m) : (prime_inv_obj n) ⟶ (prime_inv_obj m) :=
subtype.mk (prime_inv_map_fn f) prime_inv_map_fn_mono

lemma prime_comp_prime_inv_le {n m : Δ_ᵒᵖ} (f : n ⟶ m) (j : fin (m + 1)) :
  prime.map (prime_inv_map f) j ≤ f j :=
prime_map_fn_le
begin
  dsimp [T, T_map],
  split_ifs,
  { apply prime_inv_map_fn_ge,
    rw [fin.cast_succ_cast_lt], },
  { apply fin.le_last },
end


lemma prime_inv_map_fn_implies_le {n m : Δ_ᵒᵖ} {f : n ⟶ m} {j : fin (m + 1)} {k : fin n}
  (h : fin.cast_succ (prime_inv_map_fn f k) ≥ j) : f j ≤ fin.cast_succ k :=
le_trans ((Δ_.f_op_mono f) h) (f_prime_inv_map_fn_le f k)

lemma le_prime_comp_prime_inv {n m : Δ_ᵒᵖ} (f : n ⟶ m) (j : fin (m + 1)) :
  f j ≤ prime.map (prime_inv_map f) j :=
le_prime_map_fn (λ k h,
begin
  dsimp [T, T_map] at h,
  split_ifs at h with w,
  { exact prime_inv_map_fn_implies_le h},
  { exact nat.le_trans (fin.le_last (f j)) (not_lt.mp w),}
end)


lemma prime_comp_prime_inv {n m : Δ_ᵒᵖ} (f : n ⟶ m) : prime.map (prime_inv_map f) = f :=
Δ_.op_hom_ext $ funext $
  λ j, le_antisymm (prime_comp_prime_inv_le f j) (le_prime_comp_prime_inv f j)

lemma prime_inv_comp_prime_le {n m : Δ} (f : n ⟶ m) (j : fin n) :
  prime_inv_map (prime.map f) j ≤ f j :=
prime_inv_map_fn_le (λ k h,
begin
  dsimp [prime, prime_map_fn] at *,
  have w'' := T_map_mono f h,
  rw [T_map_f_eq_f] at w'',
  apply le_trans (T_f_of_prime_map_fn_ge f k) w'',
end)

lemma le_prime_inv_comp_prime {n m : Δ} (f : n ⟶ m) (j : fin n) :
  f j ≤ prime_inv_map (prime.map f) j :=
cast_succ_le' (prime_inv_map_fn_ge (prime_map_fn_le
begin
  rw [T_f_eq_f],
  apply le_refl,
end))

lemma prime_inv_comp_prime {n m : Δ} (f : n ⟶ m) : prime_inv_map (prime.map f) = f := Δ.hom_ext $ funext $
  λ j, le_antisymm (prime_inv_comp_prime_le f j) (le_prime_inv_comp_prime f j)

end below


namespace prime
instance : ess_surj prime := {obj_preimage := λ n, unop n, iso' := by obviously}
instance : full prime :=
{ preimage := λ _ _ f, prime_inv_map f,
  witness' := λ _ _ f, prime_comp_prime_inv f}
instance : faithful prime :=
⟨λ n m f g h,
begin
  have w := congr_arg prime_inv_map h,
  rwa [prime_inv_comp_prime, prime_inv_comp_prime] at w,
end⟩

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

lemma reg_succ {X : zigzag.{v₁} C} {i : fin X.n} {w : (i.val + 1) < X.n} :
  X.regular (i.succ) = X.regular (fin.mk (i.val + 1) w).cast_succ :=
congr_arg _ (fin.eq_of_veq (by {simp only [fin.cast_succ_val, fin.succ_val]}))





namespace zigzag

structure hom (X Y : zigzag.{v₁} C) :=
(f_sing : X.n ⟶ Y.n)
(g : Π (i : fin X.n), X.singular i ⟶ Y.singular ((f_sing : fin X.n → fin Y.n) i)) -- g_i arrows
(reg_id : Π (j : fin (Y.n + 1)), Y.regular j = X.regular (prime.map f_sing j)) -- identity arrows
(sing_comm_eq : ∀ (i : fin X.n) (w : (i.val + 1) < X.n)
    (h : f_sing (fin.mk (i.val + 1) w) = f_sing i),
      X.backwards i ≫ g i = eq_to_hom (reg_succ C) ≫ X.forwards (fin.mk (i.val + 1) w) ≫ g ((fin.mk (i.val + 1) w)) ≫ eq_to_hom (congr_arg Y.singular h))
(reg_comm_eq : ∀ (j : fin (Y.n)) (w : (j.val + 1) < Y.n)
    (h : (prime.map f_sing j.cast_succ) = (prime.map f_sing j.succ)),
    Y.forwards j = eq_to_hom (reg_id j.cast_succ) ≫ eq_to_hom (congr_arg X.regular h) ≫ eq_to_hom (eq.symm (reg_id j.succ)) ≫ Y.backwards j)
(sing_comm_neq : ∀ (i : fin X.n) (w : (i.val + 1) < X.n) (h : f_sing i ≠ f_sing (fin.mk (i.val + 1) w)),
  X.backwards i ≫ g i = eq_to_hom (congr_arg X.regular (prime_f_of_f h)) ≫ eq_to_hom (eq.symm (reg_id (f_sing i).succ)) ≫ Y.backwards (f_sing i))
(reg_comm_neq :  ∀ (j : fin Y.n) (h : prime.map f_sing j.cast_succ ≠ prime.map f_sing j.succ),
  eq_to_hom (reg_id j.cast_succ) ≫ eq_to_hom (congr_arg X.regular (eq.symm (fin.cast_succ_cast_lt (prime.map f_sing j.cast_succ) (prime_f_lt_n h)))) ≫ X.forwards ((prime.map f_sing j.cast_succ).cast_lt (prime_f_lt_n h)) ≫ g ((prime.map f_sing j.cast_succ).cast_lt (prime_f_lt_n h)) ≫ eq_to_hom (congr_arg Y.singular (f_prime_f_j_eq_j h)) = Y.forwards j)
-- Need to make sure the last square commutes


end zigzag

end category_theory
