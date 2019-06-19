import data.fin
import tactic

def hom (n m : ℕ) := fin n → fin m
def map {n m : ℕ} (f : hom n m) : hom (n+1) (m+1) :=
λ i, if h : i.val < n then (f (i.cast_lt h)).cast_succ else fin.last _

lemma map_increasing {n m : ℕ} (f: hom n m) (h : monotone f) : monotone (map f) :=
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

lemma map_comp {l m n : ℕ} (f : hom l m) (g : hom m n) : map (g ∘ f) = (map g) ∘ (map f) :=
begin
  ext,
  dsimp [map],
  split_ifs,
   { split_ifs,
    by_cases h2 : ((dite (x.val < l) (λ (h : x.val < l), fin.cast_succ (f (fin.cast_lt x h)))
            (λ (h : ¬x.val < l), fin.last m)).val < m),
    {
      rw dif_pos h2,
      split_ifs,
      tidy,
      sorry
    },
    {
      rw dif_neg h2,
      sorry
    }
  },
  {
    sorry
  }-- succeeds, but does nothing
end
