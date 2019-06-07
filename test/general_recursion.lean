import tactic.norm_num
import tactic.linarith
import tactic.omega
import data.pfun.tactic
import data.nat.basic

universes u_1 u_2

namespace roption.examples
open function has_fix complete_partial_order

@[partial]
def easy.intl (easy : ℕ → ℕ → roption ℕ) : ℕ → ℕ → roption ℕ
| x y := pure x

example : ∀ (x y : ℕ), easy x y = pure x :=
roption.examples.easy.equations._eqn_1

@[partial]
def div.intl (div : ℕ → ℕ → roption ℕ) : ℕ → ℕ → roption ℕ
| x y :=
if y ≤ x ∧ y > 0
  then div (x - y) y
  else pure x

example : ∀ (x y : ℕ), div x y = ite (y ≤ x ∧ y > 0) (div (x - y) y) (pure x) :=
roption.examples.div.equations._eqn_1

inductive tree (α : Type*)
| nil {} : tree | node (x : α) : tree → tree → tree

open tree

@[partial]
def tree_map.intl {α β} (f : α → β) (tree_map : tree α → roption (tree β)) : tree α → roption (tree β)
| nil := pure nil
| (node x t₀ t₁) :=
do tt₀ ← tree_map t₀,
   tt₁ ← tree_map t₁,
   pure $ node (f x) tt₀ tt₁

example : ∀ {α : Type u_1} {β : Type u_2} (f : α → β), tree_map f nil = pure nil :=
@roption.examples.tree_map.equations._eqn_1

example : ∀ {α : Type u_1} {β : Type u_2} (f : α → β) (x : α) (t₀ t₁ : tree α),
  tree_map f (node x t₀ t₁) =
    tree_map f t₀ >>= λ (tt₀ : tree β), tree_map f t₁ >>= λ (tt₁ : tree β), pure (node (f x) tt₀ tt₁) :=
@roption.examples.tree_map.equations._eqn_2

@[partial]
def tree_map'.intl {α β} (f : α → β) (tree_map : tree α → roption (tree β)) : tree α → roption (tree β)
| nil := pure nil
| (node x t₀ t₁) :=
node (f x) <$> tree_map t₀ <*> tree_map t₁

example : ∀ {α : Type u_1} {β : Type u_2} (f : α → β), tree_map' f nil = pure nil :=
@roption.examples.tree_map'.equations._eqn_1

example : ∀ {α : Type u_1} {β : Type u_2} (f : α → β) (x : α) (t₀ t₁ : tree α),
  tree_map' f (node x t₀ t₁) = node (f x) <$> tree_map' f t₀ <*> tree_map' f t₁ :=
@roption.examples.tree_map'.equations._eqn_2

@[partial]
def f91.intl (f91 : ℕ → roption ℕ) (n : ℕ) : roption ℕ :=
if n > 100
  then pure $ n - 10
  else f91 (n + 11) >>= f91

example : ∀ (n : ℕ), f91 n = ite (n > 100) (pure (n - 10)) (f91 (n + 11) >>= f91) :=
roption.examples.f91.equations._eqn_1

lemma f91_spec (n : ℕ) : (∃ n', n < n' + 11 ∧ n' ∈ f91 n) :=
begin
  apply well_founded.induction (measure_wf $ λ n, 101 - n) n,
  clear n, dsimp [measure,inv_image], intros n ih,
  by_cases h' : n > 100,
  { rw [roption.examples.f91.equations._eqn_1,if_pos h'],
    existsi n - 10, rw nat.sub_add_eq_add_sub, norm_num [pure],
    apply le_of_lt, transitivity 100, norm_num, exact h' },
  { rw [roption.examples.f91.equations._eqn_1,if_neg h'],
    simp, rcases ih (n + 11) _ with ⟨n',hn₀,hn₁⟩,
    rcases ih (n') _ with ⟨n'',hn'₀,hn'₁⟩,
    refine ⟨n'',_,_,hn₁,hn'₁⟩,
    { clear ih hn₁ hn'₁, omega },
    { clear ih hn₁, omega },
    { clear ih, omega } },
end

lemma f91_dom (n : ℕ) : (f91 n).dom :=
by rw roption.dom_iff_mem; apply exists_imp_exists _ (f91_spec n); simp

def f91' (n : ℕ) : ℕ := (f91 n).get (f91_dom n)

#eval f91' 109
-- 99

lemma f91_spec' (n : ℕ) : f91' n = if n > 100 then n - 10 else 91 :=
begin
  suffices : (∃ n', n' ∈ f91 n ∧ n' = if n > 100 then n - 10 else 91),
  { dsimp [f91'], rw roption.get_eq_of_mem,
    rcases this with ⟨n,_,_⟩, subst n, assumption },
  apply well_founded.induction (measure_wf $ λ n, 101 - n) n,
  clear n, dsimp [measure,inv_image], intros n ih,
  by_cases h' : n > 100,
  { rw [roption.examples.f91.equations._eqn_1,if_pos h',if_pos h'],
    simp [pure] },
  { rw [roption.examples.f91.equations._eqn_1,if_neg h',if_neg h'],
    simp, rcases ih (n + 11) _ with ⟨n',hn'₀,hn'₁⟩,
    split_ifs at hn'₁,
    { subst hn'₁, norm_num at hn'₀, refine ⟨_,hn'₀,_⟩,
      rcases ih (n+1) _ with ⟨n',hn'₀,hn'₁⟩,
      split_ifs at hn'₁,
      { subst n', convert hn'₀, clear hn'₀ hn'₀ ih, omega },
      { subst n', exact hn'₀ },
      { clear ih hn'₀, omega } },
    { refine ⟨_,hn'₀,_⟩, subst n',
      rcases ih 91 _ with ⟨n',hn'₀,hn'₁⟩,
      rw if_neg at hn'₁, subst n', exact hn'₀,
      { clear ih hn'₀ hn'₀, omega, },
      { clear ih hn'₀, omega, } },
    { clear ih, omega } }
end

end roption.examples
