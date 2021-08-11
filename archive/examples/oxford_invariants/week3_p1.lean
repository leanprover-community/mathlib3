import algebra.big_operators.basic
import data.nat.modeq

open_locale big_operators

def b : ℕ → ℕ := sorry

-- -- `a ≡ b [MOD n]`
theorem week3_p1_aux {n : ℕ} (a : ℕ → ℕ) (ha : ∀ i < n + 1, a (i+1) ∣ a i + a (i+2)) :
  ∃ b : ℕ, (b : ℚ) = ∑ i in finset.range (n+2), (a 0 * a (n+2))/(a i * a (i + 1)) :=
begin
  suffices : ∀ n, (∀ i < n + 1, a (i+1) ∣ a i + a (i+2)) →
    ∃ b : ℕ, (b : ℚ) = ∑ i in finset.range (n+2), (a 0 * a (n+2))/(a i * a (i + 1))
           ∧ a n * b ≡ a 0 [MOD a (n + 1)],
  { obtain ⟨b, hb, -⟩ := this n ha,
    exact ⟨b, hb⟩ },
  clear_dependent n,
  intros n ha,
  induction n,
  -- { simp,
  -- use 1,
  -- simp,
  -- norm_num,
  -- }
end

lemma nat.modeq.modeq_zero_iff' {a b : ℕ} : a ≡ b [MOD 0] ↔ a = b :=
by rw [nat.modeq, nat.mod_zero, nat.mod_zero]

theorem week3_p1_aux_aux {n : ℕ} (a : ℕ → ℕ) (ha : ∀ i < n, a (i+1) ∣ a i + a (i+2)) :
  ∃ b : ℕ, (b : ℚ) = ∑ i in finset.range n, (a 0 * a n)/(a i * a (i + 1)) :=
begin
  suffices : ∀ n, (∀ i < n, a (i+1) ∣ a i + a (i+2)) →
    ∃ b : ℕ, (b : ℚ) = ∑ i in finset.range n, (a 0 * a n)/(a i * a (i + 1))
           ∧ a (n - 1) * b ≡ a 0 [MOD a n],
  { obtain ⟨b, hb, -⟩ := this n ha,
    exact ⟨b, hb⟩ },
  clear_dependent n,
  intros n ha,
  induction n with n ih,
  { simp,
    rw [nat.modeq.comm, nat.modeq.modeq_zero_iff] },
  obtain ⟨b, hb₁, hb₂⟩ := ih (λ i hi, ha i $ nat.lt_succ_of_lt hi),
  cases n,
  {
    simp at hb₁,
  },
  use (a (n - 1) + a (n + 1))/a n + a 0 - a (n - 1) * b,
  obtain han | han := eq_or_ne (a n) 0,
  {
    rw [han, nat.modeq.modeq_zero_iff'] at hb₂,
    suffices h : a (n.succ - 1) * ((a (n - 1) + a (n + 1)) / a n + a 0 - a (n - 1) * b) ≡ a 0
      [MOD a n.succ],
    { sorry },
    have := ha (n - 1) ((nat.sub_le_self _ _).trans_lt $ nat.lt_succ_self _),
    rw [nat.succ_sub_one, han, zero_mul, ←hb₂, nat.modeq.comm, nat.modeq.modeq_zero_iff],
  },
  split,
  { sorry },
  { sorry },

end

theorem week3_p1 {n : ℕ} (hn : 2 ≤ n) (a : ℕ → ℕ) (ha : ∀ i < n, a (i+1) ∣ a i + a (i+2)) :
  ∃ b : ℕ, (b : ℚ) = ∑ i in finset.range n, (a 0 * a n)/(a i * a (i + 1)) :=
begin
  obtain ⟨_, rfl⟩ := nat.le.dest hn,
  have := week3_p1_aux,
  -- obtain _ | _ | _ := hn,
  -- { sorry },

  -- { sorry },
  -- exact week3_p1_aux a ha,
end
