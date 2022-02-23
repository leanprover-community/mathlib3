/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import order.monotone

variables {α : Type*} [linear_order α]

/-!
# Infinite Erdős–Szekeres Theorem

In this file, we prove that any sequence in a total order contains either an infinite increasing
subsequence or an infinite decreasing subsequence. This is an important lemma in the usual proof of
Bolzano-Weierstrass for `ℝ`.

## Main results

* `exists_strict_anti_or_monotone_subseq`: every sequence contains either a strict antitone
  subsequence or a monotone subsequence.
* `exists_strict_mono_or_antitone_subseq`: every sequence contains either a strict monotone
  subsequence or an antitone subsequence.
-/

/-- A sequence is `peaky` with respect to `r` when it has infinitely many peaks, i.e. values that
    compare as `r` to all that follow. -/
@[reducible] def peaky (r : α → α → Prop) (f : ℕ → α) : Prop :=
∀ x, ∃ y, x < y ∧ ∀ z, y < z → r (f y) (f z)

/-- A subsequence that enumerates an infinite subset of a `peaky` sequence's peaks. -/
noncomputable def peaks (f : ℕ → α) (r : α → α → Prop) (hf : peaky r f) : ℕ → ℕ
| 0       := classical.some (hf 0)
| (n + 1) := classical.some (hf (peaks n))

section peaks
variables {f : ℕ → α} {r : α → α → Prop} (hf : peaky r f)

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

/-- A sequence is `nonpeaky` with respect to `r` when all of its values after the `m`th one are
    valleys, i.e. values that compare as `r` to some that follows. -/
@[reducible] def nonpeaky (r : α → α → Prop) (f : ℕ → α) (m : ℕ) : Prop :=
∀ y, m < y → ∃ z, y < z ∧ r (f y) (f z)

/-- An auxiliary definition for `valleys`. -/
noncomputable def valleys' (f : ℕ → α) (r : α → α → Prop) (m : ℕ) (hf : nonpeaky r f m) :
  ℕ → {n // m < n}
| 0       := let hm := nat.lt_succ_self m in ⟨classical.some (hf _ hm),
               hm.trans (classical.some_spec (hf _ hm)).1⟩
| (n + 1) := let hm := (valleys' n).2 in ⟨classical.some (hf (valleys' n).1 hm),
               hm.trans (classical.some_spec (hf _ hm)).1⟩

/-- A sequence that enumerates an infinite subset of a `nonpeaky` sequence's valleys. -/
noncomputable def valleys (f : ℕ → α) (r : α → α → Prop) (m : ℕ) (hf : nonpeaky r f m) (n : ℕ) :
  ℕ :=
(valleys' f r m hf n).1

section valleys
variables {f : ℕ → α} {m : ℕ} {r : α → α → Prop} (hf : nonpeaky r f m)

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

theorem peaky_gt_or_nonpeaky_le (f : ℕ → α) : peaky (>) f ∨ ∃ m, nonpeaky (≤) f m :=
or_iff_not_imp_left.2 $ λ h, by { push_neg at h, exact h }

theorem peaky_lt_or_nonpeaky_ge (f : ℕ → α) : peaky (<) f ∨ ∃ m, nonpeaky (≥) f m :=
or_iff_not_imp_left.2 $ λ h, by { push_neg at h, exact h }

/-- Every sequence contains either a strict antitone subsequence or a monotone subsequence. -/
theorem exists_strict_anti_or_monotone_subseq (f : ℕ → α) : ∃ (g : ℕ → ℕ),
  strict_mono g ∧ (strict_anti (f ∘ g) ∨ monotone (f ∘ g)) :=
begin
  rcases peaky_gt_or_nonpeaky_le f with hf | ⟨m, hf⟩,
  { exact ⟨_, peaks_strict_mono hf, or.inl (λ a b h, peaks_values_strict_anti hf h)⟩ },
  { exact ⟨_, valleys_strict_mono hf, or.inr (λ a b h, valleys_values_monotone hf h)⟩ }
end

/-- Every sequence contains either a strict monotone subsequence or an antitone subsequence. -/
theorem exists_strict_mono_or_antitone_subseq (f : ℕ → α) : ∃ (g : ℕ → ℕ),
  strict_mono g ∧ (strict_mono (f ∘ g) ∨ antitone (f ∘ g)) :=
begin
  rcases peaky_lt_or_nonpeaky_ge f with hf | ⟨m, hf⟩,
  { exact ⟨_, peaks_strict_mono hf, or.inl (λ a b h, peaks_values_strict_anti hf h)⟩ },
  { exact ⟨_, valleys_strict_mono hf, or.inr (λ a b h, valleys_values_monotone hf h)⟩ }
end
