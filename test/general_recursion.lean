import tactic.norm_num
import tactic.linarith
import tactic.omega
import tactic.find_unused
import data.pfun.fix
import data.nat.basic

universes u_1 u_2

namespace roption.examples
open function has_fix omega_complete_partial_order

/-! `easy` is a trivial, non-recursive example -/

def easy.intl (easy : ℕ → ℕ → roption ℕ) : ℕ → ℕ → roption ℕ
| x y := pure x

def easy :=
fix easy.intl

-- automation coming soon
theorem easy.cont : continuous' easy.intl :=
pi.continuous_ext easy.intl
  (λ (x : ℕ),
     pi.continuous_ext (λ (g : ℕ → ℕ → roption ℕ), easy.intl g x)
       (λ (x_1 : ℕ), id (cont_const' (pure x))))

-- automation coming soon
@[main_declaration]
theorem easy.equations.eqn_1 (x y : ℕ) : easy x y = pure x :=
by rw [easy, lawful_fix.fix_eq easy.cont]; refl

/-! division on natural numbers -/

def div.intl (div : ℕ → ℕ → roption ℕ) : ℕ → ℕ → roption ℕ
| x y :=
if y ≤ x ∧ y > 0
  then div (x - y) y
  else pure x

def div : ℕ → ℕ → roption ℕ :=
fix div.intl

-- automation coming soon
theorem div.cont : continuous' div.intl :=
pi.continuous_ext div.intl
  (λ (x : ℕ),
     pi.continuous_ext (λ (g : ℕ → ℕ → roption ℕ), div.intl g x)
       (λ (x_1 : ℕ),
          id
            (cont_ite' (λ (x_2 : ℕ → ℕ → roption ℕ), x_2 (x - x_1) x_1)
               (λ (x_1 : ℕ → ℕ → roption ℕ), pure x)
               ((λ (v_1 : ℕ),
                   pi.continuous_congr (λ (v_1 : ℕ) (x_2 : ℕ → ℕ → roption ℕ), x_2 (x - x_1) v_1) v_1
                     (pi.continuous_congr (λ (v : ℕ) (g : ℕ → ℕ → roption ℕ) (x : ℕ), g v x) (x - x_1)
                        cont_id'))
                  x_1)
               (cont_const' (pure x)))))

-- automation coming soon
@[main_declaration]
theorem div.equations.eqn_1 (x y : ℕ) : div x y = if y ≤ x ∧ y > 0 then div (x - y) y else pure x :=
by conv_lhs { rw [div, lawful_fix.fix_eq div.cont] }; refl

inductive tree (α : Type*)
| nil {} : tree
| node (x : α) : tree → tree → tree

open roption.examples.tree

/-! `map` on a `tree` using monadic notation -/

def tree_map.intl {α β : Type*} (f : α → β) (tree_map : tree α → roption (tree β)) : tree α → roption (tree β)
| nil := pure nil
| (node x t₀ t₁) :=
do tt₀ ← tree_map t₀,
   tt₁ ← tree_map t₁,
   pure $ node (f x) tt₀ tt₁

-- automation coming soon
def tree_map {α : Type u_1} {β : Type u_2} (f : α → β) : tree α → roption (tree β) :=
fix (tree_map.intl f)

-- automation coming soon
theorem tree_map.cont : ∀ {α : Type u_1} {β : Type u_2} (f : α → β), continuous' (tree_map.intl f) :=
λ {α : Type u_1} {β : Type u_2} (f : α → β),
  pi.continuous_ext (tree_map.intl f)
    (λ (x : tree α),
       tree.cases_on x (id (cont_const' (pure nil)))
         (λ (x_x : α) (x_a x_a_1 : tree α),
            id
              (cont_bind' (λ (x : tree α → roption (tree β)), x x_a)
                 (λ (x : tree α → roption (tree β)) (tt₀ : tree β),
                    x x_a_1 >>= λ (tt₁ : tree β), pure (node (f x_x) tt₀ tt₁))
                 (pi.continuous_congr (λ (v : tree α) (x : tree α → roption (tree β)), x v) x_a cont_id')
                 (pi.continuous_ext
                    (λ (x : tree α → roption (tree β)) (tt₀ : tree β),
                       x x_a_1 >>= λ (tt₁ : tree β), pure (node (f x_x) tt₀ tt₁))
                    (λ (x : tree β),
                       cont_bind' (λ (x : tree α → roption (tree β)), x x_a_1)
                         (λ (x_1 : tree α → roption (tree β)) (tt₁ : tree β), pure (node (f x_x) x tt₁))
                         (pi.continuous_congr (λ (v : tree α) (x : tree α → roption (tree β)), x v) x_a_1
                            cont_id')
                         (pi.continuous_ext
                            (λ (x_1 : tree α → roption (tree β)) (tt₁ : tree β), pure (node (f x_x) x tt₁))
                            (λ (x_1 : tree β), cont_const' (pure (node (f x_x) x x_1)))))))))

-- automation coming soon
@[main_declaration]
theorem tree_map.equations.eqn_1 {α : Type u_1} {β : Type u_2} (f : α → β) : tree_map f nil = pure nil :=
by rw [tree_map,lawful_fix.fix_eq (tree_map.cont f)]; refl

-- automation coming soon
@[main_declaration]
theorem tree_map.equations.eqn_2 {α : Type u_1} {β : Type u_2} (f : α → β) (x : α) (t₀ t₁ : tree α) :
  tree_map f (node x t₀ t₁) = tree_map f t₀ >>= λ (tt₀ : tree β), tree_map f t₁ >>= λ (tt₁ : tree β), pure (node (f x) tt₀ tt₁) :=
by conv_lhs { rw [tree_map,lawful_fix.fix_eq (tree_map.cont f)] }; refl

/-! `map` on a `tree` using applicative notation -/

def tree_map'.intl {α β} (f : α → β) (tree_map : tree α → roption (tree β)) : tree α → roption (tree β)
| nil := pure nil
| (node x t₀ t₁) :=
node (f x) <$> tree_map t₀ <*> tree_map t₁

-- automation coming soon
def tree_map' {α : Type u_1} {β : Type u_2} (f : α → β) : tree α → roption (tree β) :=
fix (tree_map'.intl f)

-- automation coming soon
theorem tree_map'.cont : ∀ {α : Type u_1} {β : Type u_2} (f : α → β), continuous' (tree_map'.intl f) :=
λ {α : Type u_1} {β : Type u_2} (f : α → β),
  pi.continuous_ext (tree_map'.intl f)
    (λ (x : tree α),
       tree.cases_on x (id (cont_const' (pure nil)))
         (λ (x_x : α) (x_a x_a_1 : tree α),
            id
              (cont_seq' (λ (x : tree α → roption (tree β)), node (f x_x) <$> x x_a)
                 (λ (x : tree α → roption (tree β)), x x_a_1)
                 (cont_map' (node (f x_x)) (λ (x : tree α → roption (tree β)), x x_a)
                    (pi.continuous_congr (λ (v : tree α) (x : tree α → roption (tree β)), x v) x_a cont_id'))
                 (pi.continuous_congr (λ (v : tree α) (x : tree α → roption (tree β)), x v) x_a_1 cont_id'))))

-- automation coming soon
@[main_declaration]
theorem tree_map'.equations.eqn_1 {α : Type u_1} {β : Type u_2} (f : α → β) :
  tree_map' f nil = pure nil :=
by rw [tree_map',lawful_fix.fix_eq (tree_map'.cont f)]; refl

-- automation coming soon
@[main_declaration]
theorem tree_map'.equations.eqn_2 {α : Type u_1} {β : Type u_2} (f : α → β) (x : α) (t₀ t₁ : tree α) :
  tree_map' f (node x t₀ t₁) = node (f x) <$> tree_map' f t₀ <*> tree_map' f t₁ :=
by conv_lhs { rw [tree_map',lawful_fix.fix_eq (tree_map'.cont f)] }; refl

/-! f91 is a function whose proof of termination cannot rely on the structural
ordering of its arguments and does not use the usual well-founded order
on natural numbers. It is an interesting candidate to show that `fix` lets us disentangle
the issue of termination from the definition of the function. -/

def f91.intl (f91 : ℕ → roption ℕ) (n : ℕ) : roption ℕ :=
if n > 100
  then pure $ n - 10
  else f91 (n + 11) >>= f91

-- automation coming soon
def f91 : ℕ → roption ℕ := fix f91.intl

-- automation coming soon
lemma f91.cont : continuous' f91.intl :=
pi.continuous_ext f91.intl
  (λ (x : ℕ),
     id
       (cont_ite' (λ (x_1 : ℕ → roption ℕ), pure (x - 10)) (λ (x_1 : ℕ → roption ℕ), x_1 (x + 11) >>= x_1)
          (cont_const' (pure (x - 10)))
          (cont_bind' (λ (x_1 : ℕ → roption ℕ), x_1 (x + 11)) (λ (x : ℕ → roption ℕ), x)
             (pi.continuous_congr (λ (v : ℕ) (x : ℕ → roption ℕ), x v) (x + 11) cont_id')
             (pi.continuous_ext (λ (x : ℕ → roption ℕ), x)
                (λ (x_1 : ℕ), pi.continuous_congr (λ (v : ℕ) (g : ℕ → roption ℕ), g v) x_1 cont_id')))))
.
-- automation coming soon
@[main_declaration]
theorem f91.equations.eqn_1 (n : ℕ) : f91 n = ite (n > 100) (pure (n - 10)) (f91 (n + 11) >>= f91) :=
by conv_lhs { rw [f91, lawful_fix.fix_eq f91.cont] }; refl

lemma f91_spec (n : ℕ) : (∃ n', n < n' + 11 ∧ n' ∈ f91 n) :=
begin
  apply well_founded.induction (measure_wf $ λ n, 101 - n) n,
  clear n, dsimp [measure,inv_image], intros n ih,
  by_cases h' : n > 100,
  { rw [roption.examples.f91.equations.eqn_1,if_pos h'],
    existsi n - 10, rw nat.sub_add_eq_add_sub, norm_num [pure],
    apply le_of_lt, transitivity 100, norm_num, exact h' },
  { rw [roption.examples.f91.equations.eqn_1,if_neg h'],
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

@[main_declaration]
lemma f91_spec' (n : ℕ) : f91' n = if n > 100 then n - 10 else 91 :=
begin
  suffices : (∃ n', n' ∈ f91 n ∧ n' = if n > 100 then n - 10 else 91),
  { dsimp [f91'], rw roption.get_eq_of_mem,
    rcases this with ⟨n,_,_⟩, subst n, assumption },
  apply well_founded.induction (measure_wf $ λ n, 101 - n) n,
  clear n, dsimp [measure,inv_image], intros n ih,
  by_cases h' : n > 100,
  { rw [roption.examples.f91.equations.eqn_1,if_pos h',if_pos h'],
    simp [pure] },
  { rw [roption.examples.f91.equations.eqn_1,if_neg h',if_neg h'],
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

#list_unused_decls ["src/data/pfun/fix.lean","src/order/omega_complete_partial_order.lean","src/data/nat/up.lean"]
