import data.nat.basic

def fin.with_max (n m : ℕ) (h : m > 0) : fin m :=
⟨ min n (m-1), begin
                 have p := min_le_right n (nat.pred m),
                 have q := nat.lt_succ_of_le p,
                 rw nat.succ_pred_eq_of_pos at q,
                 exact q,
                 assumption
               end ⟩

def CHAR_MAX : ℕ := 0xFF

def nat.trunc_to_char (n : ℕ) : char :=
  if h : n > CHAR_MAX then
    ⟨ CHAR_MAX, by exact dec_trivial ⟩
  else
    ⟨ n, begin
           simp at h,
           left,
           transitivity CHAR_MAX + 1,
           apply nat.lt_succ_of_le,
           assumption,
           exact dec_trivial
         end ⟩