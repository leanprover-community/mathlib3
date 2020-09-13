import data.nat.basic

namespace nat

/-! ### `find` -/
section find

@[simp] lemma find_eq_zero {p : ℕ → Prop} [decidable_pred p] (h : ∃ (n : ℕ), p n) :
  nat.find h = 0 ↔ p 0 :=
begin
  split,
  { intro h0, rw [← h0], apply nat.find_spec },
  { intro hp, apply nat.eq_zero_of_le_zero, exact nat.find_min' _ hp }
end

@[simp] lemma find_pos {p : ℕ → Prop} [decidable_pred p] (h : ∃ (n : ℕ), p n) :
  0 < nat.find h ↔ ¬ p 0 :=
by rw [nat.pos_iff_ne_zero, not_iff_not, nat.find_eq_zero]

end find

/-! ### `find_greatest` -/
section find_greatest

/-- `find_greatest P b` is the largest `i ≤ bound` such that `P i` holds, or `0` if no such `i`
exists -/
protected def find_greatest (P : ℕ → Prop) [decidable_pred P] : ℕ → ℕ
| 0       := 0
| (n + 1) := if P (n + 1) then n + 1 else find_greatest n

variables {P : ℕ → Prop} [decidable_pred P]

@[simp] lemma find_greatest_zero : nat.find_greatest P 0 = 0 := rfl

@[simp] lemma find_greatest_eq : ∀{b}, P b → nat.find_greatest P b = b
| 0       h := rfl
| (n + 1) h := by simp [nat.find_greatest, h]

@[simp] lemma find_greatest_of_not {b} (h : ¬ P (b + 1)) :
  nat.find_greatest P (b + 1) = nat.find_greatest P b :=
by simp [nat.find_greatest, h]

lemma find_greatest_spec_and_le :
  ∀{b m}, m ≤ b → P m → P (nat.find_greatest P b) ∧ m ≤ nat.find_greatest P b
| 0       m hm hP :=
  have m = 0, from le_antisymm hm (nat.zero_le _),
  show P 0 ∧ m ≤ 0, from this ▸ ⟨hP, le_refl _⟩
| (b + 1) m hm hP :=
  begin
    by_cases h : P (b + 1),
    { simp [h, hm] },
    { have : m ≠ b + 1 := assume this, h $ this ▸ hP,
      have : m ≤ b := (le_of_not_gt $ assume h : b + 1 ≤ m, this $ le_antisymm hm h),
      have : P (nat.find_greatest P b) ∧ m ≤ nat.find_greatest P b :=
        find_greatest_spec_and_le this hP,
      simp [h, this] }
  end

lemma find_greatest_spec {b} : (∃m, m ≤ b ∧ P m) → P (nat.find_greatest P b)
| ⟨m, hmb, hm⟩ := (find_greatest_spec_and_le hmb hm).1

lemma find_greatest_le : ∀ {b}, nat.find_greatest P b ≤ b
| 0       := le_refl _
| (b + 1) :=
  have nat.find_greatest P b ≤ b + 1, from le_trans find_greatest_le (nat.le_succ b),
  by by_cases P (b + 1); simp [h, this]

lemma le_find_greatest {b m} (hmb : m ≤ b) (hm : P m) : m ≤ nat.find_greatest P b :=
(find_greatest_spec_and_le hmb hm).2

lemma find_greatest_is_greatest {P : ℕ → Prop} [decidable_pred P] {b} :
  (∃ m, m ≤ b ∧ P m) → ∀ k, nat.find_greatest P b < k ∧ k ≤ b → ¬ P k
| ⟨m, hmb, hP⟩ k ⟨hk, hkb⟩ hPk := lt_irrefl k $ lt_of_le_of_lt (le_find_greatest hkb hPk) hk

lemma find_greatest_eq_zero {P : ℕ → Prop} [decidable_pred P] :
  ∀ {b}, (∀ n ≤ b, ¬ P n) → nat.find_greatest P b = 0
| 0       h := find_greatest_zero
| (n + 1) h :=
begin
  have := nat.find_greatest_of_not (h (n + 1) (le_refl _)),
  rw this, exact find_greatest_eq_zero (assume k hk, h k (le_trans hk $ nat.le_succ _))
end

lemma find_greatest_of_ne_zero {P : ℕ → Prop} [decidable_pred P] :
  ∀ {b m}, nat.find_greatest P b = m → m ≠ 0 → P m
| 0       m rfl h := by { have := @find_greatest_zero P _, contradiction }
| (b + 1) m rfl h :=
decidable.by_cases
  (assume hb : P (b + 1), by { have := find_greatest_eq hb, rw this, exact hb })
  (assume hb : ¬ P (b + 1), find_greatest_of_ne_zero (find_greatest_of_not hb).symm h)

end find_greatest

end nat
