import data.nat.basic
--#print nat

lemma h (n : ℕ) (hn : 0 < n) : ¬n = 0 :=
begin
  contrapose hn,
  simp at hn,
  simp,
  exact hn,
end

#lint

  -- induction n with d hd,
  -- { exfalso,
  --   have hn' := nat.not_lt_zero _ hn,
  --   exact hn', },
  -- { apply nat.succ_ne_zero _, },

  -- contrapose hn,
  -- simp at hn,
  -- simp,
  -- exact hn,
