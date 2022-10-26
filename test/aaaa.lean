import tactic
import data.list.join

noncomputable theory
open_locale classical

variable {α : Type*}

def get_max [inhabited α] [linear_order α] (P : α → Prop) :=
classical.epsilon (λ (x : α), P x ∧ ∀ (y : α), x < y → ¬P y)

lemma epsilon_eq [inhabited α] {P : α → Prop} {x : α}
  (h₁ : P x) (h₂ : ∀ (y : α), P y → y = x) : classical.epsilon P = x :=
begin
  have h₃ : P = (λ (y : α), y = x),
  { ext y, split; intro h₃,
    { exact h₂ y h₃ },
    { rwa h₃ }},
  subst h₃, apply classical.epsilon_singleton,
end

lemma nat_get_max_spec {P : ℕ → Prop}
  (h₁ : ∃ (x : ℕ), P x) (h₂ : ∃ (x : ℕ), ∀ (y : ℕ), x ≤ y → ¬P y) :
  P (get_max P) ∧ ∀ (x : ℕ), get_max P < x → ¬P x :=
begin
  cases h₁ with m h₁, cases h₂ with n h₂, induction n with n ih,
  { cases h₂ m (zero_le m) h₁ },
  { simp_rw nat.succ_le_iff at h₂, by_cases h₃ : P n,
    { have : get_max P = n,
      { rw get_max, apply epsilon_eq,
        { use h₃, rintro k hk, exact h₂ k hk, },
        { rintro k ⟨h₄, h₅⟩, by_contra h₆,
          rw [←ne, ne_iff_lt_or_gt] at h₆, cases h₆,
          { cases h₅ n h₆ h₃ }, { cases h₂ k h₆ h₄ }}},
      rw this at *, clear this, exact ⟨h₃, h₂⟩ },
    { apply ih, rintro k hk, rw le_iff_eq_or_lt at hk, rcases hk with rfl | hk,
      { exact h₃ },
      { exact h₂ k hk }}},
end

lemma list.take_join_of_lt {l : list (list α)} {n : ℕ}
  (h : n < l.join.length) :
  ∃ (m k : ℕ) hh, k < (l.nth_le m hh).length ∧
  l.join.take n = (l.take m).join ++ (l.nth_le m hh).take k :=
begin
  generalize hX : l.length = X, symmetry' at hX,
  generalize hN : l.join.length = N, symmetry' at hN,
  rw ←hN at h, have hl : l ≠ [],
  { rintro rfl, rw hN at h, cases h },
  generalize hP : (λ (m : ℕ), (l.take m).join.length ≤ n) = P, symmetry' at hP,
  generalize hm : get_max P = m, symmetry' at hm,
  generalize hk : n - (l.take m).join.length = k, symmetry' at hk,
  have hP0 : P 0, { rw hP, simp },
  have hPX : ∀ (r : ℕ), X ≤ r → ¬P r,
  { rintro r hr, rw hP, push_neg, convert h, rw hX at hr,
    rw [hN, list.take_all_of_le hr] },
  obtain ⟨hm₁, hm₂⟩ := nat_get_max_spec ⟨0, hP0⟩ ⟨X, hPX⟩, rw ←hm at hm₁ hm₂,
  have hm₃ : ¬P m.succ := hm₂ _ (nat.lt_succ_self m),
  refine ⟨m, k, _, _, _⟩,
  { rw ←hX, by_contra' hx, cases hPX m hx hm₁ },
  { generalize_proofs h₁, rw hP at hm₁ hm₃, push_neg at hm₃,
    by_contra' hk₁, obtain ⟨k, rfl⟩ := nat.exists_eq_add_of_le hk₁,
    replace hk := congr_arg (λ (x : ℕ), x + (l.take m).join.length) hk,
    dsimp at hk, rw nat.sub_add_cancel hm₁ at hk, rw ←hk at hm₃,
    contrapose! hm₃, rw [add_comm, ←add_assoc], convert le_self_add,
    simp [nat.succ_eq_add_one, list.take_add, list.join_append,
      list.length_append, list.take_one_drop_eq_of_lt_length h₁] },
  conv { to_lhs, rw [←list.take_append_drop m.succ l, list.join_append] },
  have hn₁ : (l.take m).join.length ≤ n, { rwa hP at hm₁ },
  have hn₂ : n < (l.take m.succ).join.length,
  { rw hP at hm₃, push_neg at hm₃, exact hm₃ },
  rw list.take_append_of_le_length (le_of_lt hn₂),
  change m.succ with m + 1, have hmX : m < X,
  { by_contra' hx, exact hPX m hx hm₁ },
  rw [list.take_add, list.join_append, list.take_one_drop_eq_of_lt_length,
    list.join_singleton], swap, { rwa ←hX },
  have : n = (list.take m l).join.length + k,
  { rw hk, exact (nat.add_sub_of_le hn₁).symm },
  subst this, rw list.take_append,
end

lemma list.take_join {l : list (list α)} {n : ℕ} (h : l ≠ []) :
  ∃ (m k : ℕ) hh, l.join.take n = (l.take m).join ++ (l.nth_le m hh).take k :=
begin
  by_cases h₁ : l.join.length ≤ n,
  { refine ⟨l.length - 1, (l.last h).length, _, _⟩,
    { apply nat.pred_lt, change ¬(l.length = 0), rwa list.length_eq_zero },
    { generalize_proofs hh, revert hh, intro hh,
      rw [list.take_all_of_le h₁, list.nth_le_length_sub_one h], clear hh,
      rw (_ : l.last h = (l.last h).take (l.last h).length), swap,
      { symmetry, apply list.take_all_of_le, refl },
      rw [list.take_length, ←list.join_drop_length_sub_one h, list.take_length,
        ←list.join_append, list.take_append_drop] }},
  { push_neg at h₁, obtain ⟨m, k, h₂, h₃, h₄⟩ := list.take_join_of_lt h₁,
    exact ⟨m, k, h₂, h₄⟩ },
end
