import order.monotone

variables {α : Type*} [linear_order α]

/-- A sequence is `peaky` with respect to `r` when it has infinitely many peaks, i.e. values that
    compare as `r` to all that follow. -/
def peaky (f : ℕ → α) (r : α → α → Prop) : Prop :=
∀ x, ∃ y, x < y ∧ ∀ z, y < z → r (f y) (f z)

/-- A subsequence that enumerates an infinite subset of a `peaky` sequence's peaks. -/
noncomputable def peaks (f : ℕ → α) (r : α → α → Prop) (hf : peaky f r) : ℕ → ℕ
| 0       := classical.some (hf 0)
| (n + 1) := classical.some (hf (peaks n))

section peaks
variables {f : ℕ → α} {r : α → α → Prop} (hf : peaky f r)

/-- Each value attained by `peaks` is a peak. -/
theorem peaks_def {z : ℕ} (n : ℕ) (hp : peaks f r hf n < z) : r (f (peaks f r hf n)) (f z) :=
begin
  cases n,
  all_goals { cases classical.some_spec (hf _) with _ H, exact H _ hp }
end

theorem peaks_strict_mono : strict_mono (peaks f r hf) :=
strict_mono_nat_of_lt_succ (λ n, begin
  cases n,
  all_goals { cases classical.some_spec (hf _) with H _, exact H }
end)

theorem peaks_values_strict_anti [H : is_trans α r] ⦃a b : ℕ⦄ (h : a < b)  :
  r (f (peaks f r hf a)) (f (peaks f r hf b)) :=
@nat.rel_of_forall_rel_succ_of_lt α r H (f ∘ (peaks f r hf))
  (λ n, peaks_def hf n (peaks_strict_mono hf (nat.lt_succ_self n))) a b h

end peaks

/-- A sequence is `nonpeaky` with respect to `r` when eventually, all of its values are valleys,
    i.e. values that compare as `r` to some that follow. -/
def nonpeaky (f : ℕ → α) (r : α → α → Prop) (m : ℕ) : Prop :=
∀ y, m < y → ∃ z, y < z ∧ r (f y) (f z)

/-- An auxiliary definition for `valleys`. -/
noncomputable def valleys' (f : ℕ → α) (r : α → α → Prop) (m : ℕ) (hf : nonpeaky f r m) :
  ℕ → {n // m < n}
| 0       := let hm := nat.lt_succ_self m in ⟨classical.some (hf _ hm),
               hm.trans (classical.some_spec (hf _ hm)).1⟩
| (n + 1) := let hm := (valleys' n).2 in ⟨classical.some (hf (valleys' n).1 hm),
               hm.trans (classical.some_spec (hf _ hm)).1⟩

/-- A sequence that enumerates an infinite subset of a `nonpeaky` sequence's valleys. -/
noncomputable def valleys (f : ℕ → α) (r : α → α → Prop) (m : ℕ) (hf : nonpeaky f r m) (n : ℕ) :
  ℕ :=
(valleys' f r m hf n).1

section valleys
variables {f : ℕ → α} {m : ℕ} {r : α → α → Prop} (hf : nonpeaky f r m)

theorem valleys_strict_mono : strict_mono (valleys f r m hf) :=
strict_mono_nat_of_lt_succ (λ n, begin
  cases n,
  all_goals { cases classical.some_spec (hf _ _) with H _, exact H }
end)

theorem valleys_values_monotone ⦃a b : ℕ⦄ (h : a ≤ b) [H : is_refl α r] [H' : is_trans α r] :
  r (f (valleys f r m hf a)) (f (valleys f r m hf b)) :=
@nat.rel_of_forall_rel_succ_of_le α r H H' (f ∘ (valleys f r m hf)) (λ n, begin
  cases n,
  all_goals { cases classical.some_spec (hf _ _) with _ H, exact H }
end) a b h

end valleys

theorem bolzano_weierstrass' (f : ℕ → α) : ∃ (g : ℕ → ℕ),
  strict_mono g ∧ (strict_anti (f ∘ g) ∨ monotone (f ∘ g)) :=
begin
  by_cases hf : ∀ x, ∃ y, x < y ∧ ∀ z, y < z → f z < f y,
  { change peaky f (>) at hf,
    exact ⟨_, peaks_strict_mono hf, or.inl (λ a b h, peaks_values_strict_anti hf h)⟩ },
  { push_neg at hf,
    cases hf with m hf,
    change nonpeaky f (≤) m at hf,
    exact ⟨_, valleys_strict_mono hf, or.inr (λ a b h, valleys_values_monotone hf h)⟩ }
end

theorem bolzano_weierstrass (f : ℕ → α) : ∃ (g : ℕ → ℕ),
  strict_mono g ∧ (strict_mono (f ∘ g) ∨ antitone (f ∘ g)) :=
begin
  by_cases hf : ∀ x, ∃ y, x < y ∧ ∀ z, y < z → f y < f z,
  { change peaky f (<) at hf,
    exact ⟨_, peaks_strict_mono hf, or.inl (λ a b h, peaks_values_strict_anti hf h)⟩ },
  { push_neg at hf,
    cases hf with m hf,
    change nonpeaky f (≥) m at hf,
    exact ⟨_, valleys_strict_mono hf, or.inr (λ a b h, valleys_values_monotone hf h)⟩ }
end
