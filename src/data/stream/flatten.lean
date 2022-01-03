import tactic
open nat
open list

namespace stream

namespace flatten
def f₁ {α : Type*} (f : ℕ → {l : list α // l ≠ []}) (i : ℕ) : {l : list α // l ≠ []} :=
dite ((f 0).1.length = 1) (λ h, f i.succ)
(λ h, ite (i = 0) ⟨tail (f 0).1, begin
  have h₁ := (f 0).2,
  cases (f 0).val with x xs,
  { exact (h₁ rfl).elim },
  { dsimp at h, rw [add_left_eq_self, length_eq_zero] at h, exact h },
end⟩ (f i))

def f₂ {α : Type*} (xs : {l : list α // l ≠ []}) : inhabited α :=
by { cases xs with xs h, cases xs with x xs, exact (h rfl).elim, use x }

end flatten

open flatten

def flatten' {α : Type*} : (ℕ → {l : list α // l ≠ []}) → ℕ → α
| f 0 := @head α (f₂ (f 0)) (f 0).1
| f (succ n) := flatten' (f₁ f) n

def flatten {α : Type*} (f : ℕ → list α) (hf : ∀ n, f n ≠ []) : ℕ → α :=
flatten' (λ k, ⟨f k, hf k⟩)

-- `f` collects elements of `α` that have the same value under the map `v`,
-- and collects them ordered by this value
variables {α β : Type*} [linear_order β] {v : α → β}
  (f : ℕ → list α)
  (hf : ∀ n, f n ≠ [])
  (hv1 : ∀ n, ∀ i j ∈ f n, v i = v j)
  (hv2 : ∀ n, ∀ i ∈ f n, ∀ j ∈ f (n+1), v i < v j)
include hv1 hv2

lemma flatten_le (n : ℕ) : v (flatten f hf n) ≤ v (flatten f hf (n+1)) :=
begin
  revert f, induction n with n hn; rintro f hf hv1 hv2,
  { rw [flatten, flatten', flatten', flatten', f₁], dsimp, split_ifs,
    { dsimp, apply le_of_lt, apply hv2;
      { apply head_mem_self, apply hf }},
    { apply le_of_eq, dsimp, apply hv1,
      { apply head_mem_self, apply hf },
      { apply mem_of_mem_tail, apply head_mem_self,
        have h₁ := hf 0, cases f 0 with x xs,
        { apply (h₁ rfl).elim },
        { rw tail, simp at h, rw length_eq_zero at h, exact h }}}},
  { generalize hf' : (λ n, (f₁ (λ n, ⟨f n, hf n⟩) n).1) = f',
    have hf' : ∀ n, f' n ≠ [],
    { intro k, subst f', dsimp, rw f₁,
      split_ifs with h h₁; dsimp at h ⊢;
      try { apply hf },
      { have h₂ := hf 0, cases f 0 with x xs,
        { exact (h₂ rfl).elim },
        { dsimp at *, simp at h, rw length_eq_zero at h, exact h }}},
    have hn₁ : v (flatten f' hf' n) ≤ v (flatten f' hf' (n + 1)),
    { apply hn; clear hn n,
      { rintro n i j hi hj, subst f', dsimp at hi hj, rw f₁ at hi hj,
        split_ifs at hi hj with h h₁; dsimp at hi hj;
        try { apply hv1 _ _ _ hi hj },
        { apply hv1 0 _ _; apply mem_of_mem_tail; assumption }},
      { rintro n i hi j hj, subst f', dsimp at hi hj, dunfold stream.flatten.f₁ at hi hj,
        split_ifs at hi hj with h₁ h₂; dsimp at *,
        { apply hv2; assumption },
        { apply hv2,
          { apply mem_of_mem_tail, assumption },
          { cases h₂ }},
        { cases h₂ },
        { replace hi := mem_of_mem_tail hi, apply hv2,
          { assumption },
          { rw h at hj, assumption }},
        { apply hv2; assumption }}},
    have h₁ : ∀ n, flatten f hf (n + 1) = flatten f' hf' n,
    { intro k, rw [flatten, flatten, flatten'], congr, funext i, subst f',
      dsimp, simp_rw f₁, split_ifs with h₁ h₂; refl },
    rw [h₁, h₁], exact hn₁ },
end

end stream
