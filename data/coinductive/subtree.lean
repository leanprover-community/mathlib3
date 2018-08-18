
import data.coinductive.basic

universes u₀ u₁ u₂

local prefix `♯`:0 := cast (by casesm* _ ∧ _ ; simp [*] <|> cc <|> solve_by_elim)

namespace coinduction.subtree

open coinduction.approx

variables {ι : Type u₁}
variables {α : ι → Type u₀}
variables {β : Π i, α i → Type u₂}
variables (γ : Π i (a : α i), β i a → ι)
variables {i : ι}

inductive select' : ∀ {j : ι} {n : ℕ}, cofix_a γ j n → path @β → α i → Prop
| nil {n : ℕ} (x : α i) (ch : Π b, cofix_a γ (γ i x b) n) :
  select' (cofix_a.intro x ch) [] x
| cons {n : ℕ} {j} (a : α j) (x : β j a) (y : α i)
       (ch : Π b, cofix_a γ (γ j a b) n) (ps : path @β) :
  select' (ch x) ps y →
  select' (cofix_a.intro a ch) (⟨_,a,x⟩ :: ps) y
variables {n : ℕ}

inductive subtree' : ∀ {j : ι} {m : ℕ} (ps : path @β) (x : cofix_a γ j m), cofix_a γ i n → Prop
| nil (x : α i) (y : cofix_a γ i n) :
  subtree' [] y y
| cons {m : ℕ} {j} (a : α j) (x : β j a) (y : cofix_a γ i n )
       (ch : Π b, cofix_a γ (γ j a b) n) (ps : path @β) :
  subtree' ps (ch x) y →
  subtree' (⟨_,a,x⟩ :: ps) (cofix_a.intro a ch) y

-- def subtree' : ∀ {i : ι} {n : ℕ} (ps : path @β) (x : cofix_a γ i (n + ps.length)), roption (Σ i, cofix_a γ i n)
--  | i n [] t := return ⟨_,t⟩
--  | i' n (⟨i, y, j⟩ :: ys) (cofix_a.intro y' ch) :=
-- assert (i' = i ∧ y == y') $ λ h,
-- subtree' ys (ch $ ♯ j)

#check cofix_a.intro

end coinduction.subtree
