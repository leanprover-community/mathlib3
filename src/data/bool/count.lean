import data.nat.parity

namespace list

namespace chain'

variables {l : list bool}

theorem two_mul_count_bool_of_even (hl : chain' (≠) l) (h2 : even (length l)) (b : bool) :
  2 * count b l = length l :=
begin
  cases h2 with n hn,
  suffices : count b l = n, by rw [this, hn, two_mul],
  induction n with n ihn generalizing l,
  { rw [zero_add, length_eq_zero] at hn,
    rw [hn, count_nil] },
  { rw [nat.succ_eq_add_one, add_add_add_comm, ← add_assoc] at hn,
    rcases l with (_|⟨x, _|⟨y, l⟩⟩); iterate 2 { try { injection hn with hn } },
    rw [count_cons', count_cons', @ihn l hl.tail.tail hn, add_assoc, nat.succ_eq_add_one,
      add_right_inj],
    have := hl.rel_head,
    clear_dependent l ihn,
    revert this x y b,
    dec_trivial }
end

theorem two_mul_count_bool_eq_ite (hl : chain' (≠) l) (b : bool) :
  2 * count b l = if even (length l) then length l else
    if b ∈ l.head' then length l + 1 else length l - 1 :=
begin
  by_cases h2 : even (length l),
  { rw [if_pos h2, hl.two_mul_count_bool_of_even h2] },
  { cases l with x l, { exact (h2 even_zero).elim },
    simp only [if_neg h2, count_cons', mul_add, head', option.mem_some_iff, @eq_comm _ x],
    rw [length_cons, nat.even_add_one, not_not] at h2,
    replace hl : l.chain' (≠) := hl.tail,
    rw [hl.two_mul_count_bool_of_even h2],
    split_ifs; simp }
end

theorem length_sub_one_le_two_mul_count_bool (hl : chain' (≠) l) (b : bool) :
  length l - 1 ≤ 2 * count b l :=
by { rw [hl.two_mul_count_bool_eq_ite], split_ifs; simp [le_tsub_add, nat.le_succ_of_le] }

theorem length_div_two_le_count_bool (hl : chain' (≠) l) (b : bool) : length l / 2 ≤ count b l :=
begin
  rw [nat.div_le_iff_le_mul_add_pred two_pos, ← tsub_le_iff_right],
  exact length_sub_one_le_two_mul_count_bool hl b
end

lemma two_mul_count_bool_le_length_add_one (hl : chain' (≠) l) (b : bool) :
  2 * count b l ≤ length l + 1 :=
by { rw [hl.two_mul_count_bool_eq_ite], split_ifs; simp [nat.le_succ_of_le] }

end chain'

end list
