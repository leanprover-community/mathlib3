import data.fin
import tactic

def hom (n m : ℕ) := fin n → fin m
def map {n m : ℕ} (f : hom n m) : hom (n+1) (m+1) :=
λ i, if h : i.val < n then (f (i.cast_lt h)).cast_succ else fin.last _

lemma map_increasing {n m : ℕ} (f: hom n m) (w : monotone f) : monotone (map f) :=
λ a b h,
begin
  dsimp [map],
  split_ifs,
  {tidy},
  {apply fin.le_last},
  {rw [fin.le_iff_val_le_val] at h,
  linarith},
  {apply fin.le_last}
end


lemma map_id {n m : ℕ} (f : hom n m) : map (@id (fin n)) = @id (fin (n+1)) :=
funext (λ a,
begin
  dsimp [map],
  split_ifs,
  {tidy},
  {exact (fin.ext_iff _ _).2  (eq.trans rfl (eq.symm (nat.eq_of_lt_succ_of_not_lt a.is_lt h)))}
end)


lemma cast_succ_val_lt {n : ℕ} (i : fin n) : (fin.cast_succ i).val < n :=
begin
 rw [fin.cast_succ_val],
 exact i.is_lt,
end

lemma cast_lt_cast_succ {n : ℕ} (i : fin n)  :
  fin.cast_lt (fin.cast_succ i) (cast_succ_val_lt _) = i :=
fin.eq_of_veq (by simp only [fin.cast_lt_val, fin.cast_succ_val])

lemma map_comp {l m n : ℕ} (f : hom l m) (g : hom m n) : map (g ∘ f) = (map g) ∘ (map f) :=
funext (λ a,
begin
  dsimp [map],
  split_ifs,
  { -- a.val < l
    by_cases h2 : ((dite (a.val < l) (λ h, fin.cast_succ (f (fin.cast_lt a h)))
      (λ h, fin.last m)).val < m),
    { -- (dite (a.val < l) (λ h, fin.cast_succ (f (fin.cast_lt a h))) (λ h, fin.last m)).val < m
      rw dif_pos h2,
      split_ifs,
      tidy,
      simp [cast_lt_cast_succ],
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
      split_ifs at h2,
      simp [fin.last] at h2,
      exact (absurd h2 (irrefl m)),
    },
    { -- ¬((dite (a.val < l) (λ h, fin.cast_succ (f (fin.cast_lt a h))) (λ h, fin.last m)).val < m)
      rw dif_neg h2,
    },
  }
end).



-- One way to define the maximum of the set (above f j) is to use nat.find_greatest. One simply way
-- to do this is to change the definition of above from set (fin n) to set ℕ
def above {n m : ℕ} (f : hom n m) (j : fin m) : set (fin n) := {i | f i ≥ j}

def above' {n m : ℕ} (f : hom n m) (j : fin m) : set ℕ := {i : ℕ | ∃ h : i < n, f ⟨i, h⟩ ≥ j}

-- To use find_greatest, above' f j must be decidable
instance {n m : ℕ} (f : hom n m) (j : fin m) : decidable_pred (above' f j) := sorry

def hom_ (n m : ℕ) := fin (n+1) → fin (m+1)

def prime_map_fn {n m : ℕ} (f : hom_ n m) (j : fin (m+2)) : fin (n+2) :=
nat.find_greatest (above' (map f) j) (n+1)



#print prime_map_fn
