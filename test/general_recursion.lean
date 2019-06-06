import tactic.norm_num
import tactic.linarith
import tactic.omega
import data.pfun.tactic
import data.nat.basic

universes u_1 u_2

namespace roption.examples
open function has_fix complete_partial_order

@[recursive_decl]
def easy.intl (easy : ℕ → ℕ → roption ℕ) : ℕ → ℕ → roption ℕ
| x y := pure x

example : ∀ (x y : ℕ), easy x y = pure x :=
roption.examples.easy.equations._eqn_1

@[recursive_decl]
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

@[recursive_decl]
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

@[recursive_decl]
def tree_map'.intl {α β} (f : α → β) (tree_map : tree α → roption (tree β)) : tree α → roption (tree β)
| nil := pure nil
| (node x t₀ t₁) :=
node (f x) <$> tree_map t₀ <*> tree_map t₁

example : ∀ {α : Type u_1} {β : Type u_2} (f : α → β), tree_map' f nil = pure nil :=
@roption.examples.tree_map'.equations._eqn_1

example : ∀ {α : Type u_1} {β : Type u_2} (f : α → β) (x : α) (t₀ t₁ : tree α),
  tree_map' f (node x t₀ t₁) = node (f x) <$> tree_map' f t₀ <*> tree_map' f t₁ :=
@roption.examples.tree_map'.equations._eqn_2

@[recursive_decl]
def f91.intl (f91 : ℕ → roption ℕ) (n : ℕ) : roption ℕ :=
if n > 100
  then pure $ n - 10
  else f91 (n + 11) >>= f91

example : ∀ (n : ℕ), f91 n = ite (n > 100) (pure (n - 10)) (f91 (n + 11) >>= f91) :=
roption.examples.f91.equations._eqn_1

-- #check nat.lt_of_add_lt_add_left

-- example (n : ℕ) : (∃ n', n < n' + 11 ∧ n' ∈ f91 n) :=
-- begin
--   generalize h : 101 - n = k, revert n,
--   apply nat.strong_induction_on k,
--   intros k ih k' h,
--   by_cases h' : k' > 100,
--   { rw [roption.examples.f91.equations._eqn_1,if_pos h'],
--     existsi k' - 10, rw nat.sub_add_eq_add_sub, norm_num [pure],
--     apply le_of_lt, transitivity 100, norm_num, exact h' },
--   { have := ih (k - 11) _ (k' + 11) _,
--     rcases this with ⟨z,hz,hz'⟩, replace hz := nat.lt_of_add_lt_add_right hz,
--     rw [roption.examples.f91.equations._eqn_1,if_neg h'],
--     simp, rw ← roption.eq_some_iff at hz', rw hz',
--     have := ih k' _ z _,
--     rcases this with ⟨y,hy,hy'⟩,
--     existsi [y,_,z,roption.mem_some _], exact hy',
--     { transitivity, apply hz, apply hy },
--     { subst k, rw nat.lt_sub_left_iff_add_lt, }
--   },
-- end

end roption.examples
