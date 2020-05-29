import tactic.induction tactic.linarith

inductive le : ℕ → ℕ → Type
| zero {n} : le 0 n
| succ {n m} : le n m → le (n + 1) (m + 1)

inductive lt : ℕ → ℕ → Type
| zero {n} : lt 0 (n + 1)
| succ {n m} : lt n m → lt (n + 1) (m + 1)

inductive unit_param (a : unit) : Type
| intro : unit_param

inductive unit_index : unit → Type
| intro : unit_index ()

inductive Fin : ℕ → Type
| zero {n} : Fin (n + 1)
| succ {n} : Fin n → Fin (n + 1)

inductive List (α : Sort*) : Sort*
| nil {} : List
| cons {} (x : α) (xs : List) : List

namespace List

def append {α} : List α → List α → List α
| nil ys := ys
| (cons x xs) ys := cons x (append xs ys)

end List

inductive Vec (α : Sort*) : ℕ → Sort*
| nil : Vec 0
| cons {n} : α → Vec n → Vec (n + 1)

inductive Two : Type | zero | one

inductive ℕ' : Type
| intro : ℕ → ℕ'

example (k) : 0 + k = k :=
begin
  induction' k,
  { refl },
  { simp }
end

example {k} (fk : Fin k) : Fin (k + 1) :=
begin
  induction' fk,
  { exact Fin.zero },
  { exact Fin.succ ih }
end

example {α} (l : List α) : l.append List.nil = l :=
begin
  induction' l,
  { refl },
  { dsimp only [List.append],
    exact (congr_arg _ ih)
  }
end

example {k l} (h : lt k l) : le k l :=
begin
  induction' h,
  { exact le.zero },
  { exact le.succ ih }
end

example {k l} : lt k l → le k l :=
begin
  induction' k; induction' l; intro hlt,
  { cases hlt },
  { exact le.zero },
  { cases hlt },
  { cases hlt,
    exact le.succ (@ih l hlt_a),
  }
end

-- A simple induction with complex arguments.
example {k} (h : lt (k + 1) k) : false :=
begin
  induction' h,
  { exact ih }
end

-- This example tests type-based naming.
example (k : ℕ') (i : ℕ') : ℕ :=
begin
  induction' k,
  -- (do tactic.fail_if_success (tactic.resolve_name `n)),
  induction' i,
  exact (n + m)
end

-- This example checks that constructor arguments don't 'steal' the names of
-- generalised hypotheses.
example (n : list ℕ) (n : ℕ) : list ℕ :=
begin
  -- this performs induction on (n : ℕ)
  induction' n,
  { exact n },
  { -- n is the list, which was automatically generalized and keeps its name.
    -- n_1 is the recursive argument of `nat.succ`. It would be called `n` if
    -- there wasn't already an `n` in the context.
    exact (n_1 :: n)
  }
end

-- This example tests whether `induction'` gets confused when there are
-- additional cases around.
example (k : ℕ) (t : Two) : 0 + k = k :=
begin
  cases t,
  induction' k,
  { refl },
  { simp },
  induction' k,
  { refl },
  { simp }
end

-- The type of the induction premise can be a complex expression so long as it
-- normalises to an inductive (possibly applied to params/indexes).
example (n) : 0 + n = n :=
begin
  let T := ℕ,
  change T at n,
  induction' n; simp
end

-- Fail if the type of the induction premise is not an inductive type
example {α} (x : α) (f : α → α) : unit :=
begin
  success_if_fail { induction' x },
  success_if_fail { induction' f },
  exact ()
end

--------------------------------------------------------------------------------
-- Jasmin's original use cases
--------------------------------------------------------------------------------

namespace expressions

inductive exp : Type
| Var  : string → exp
| Num  : ℤ → exp
| Plus : exp → exp → exp

export exp

def subst (ρ : string → exp) : exp → exp
| (Var y)      := ρ y
| (Num i)      := Num i
| (Plus e₁ e₂) := Plus (subst e₁) (subst e₂)


-- TODO type-based naming
lemma subst_Var (e : exp) :
  subst (λx, Var x) e = e :=
begin
  induction' e,
  case Var {
    rename x s,
    /- Desired state here. -/
    rw [subst]
  },
  case Num {
    rename x z,
    /- Desired state here. -/
    rw [subst]
  },
  case Plus {
    rw [subst],
    rw ih_e,
    rw ih_e_1
   }
end

end expressions


/- Less-than -/

namespace less_than

inductive lt : nat → nat → Type
| zero_succ (n : nat) : lt 0 (1 + n)
| succ_succ {n m : nat} : lt n m → lt (1 + n) (1 + m)

inductive lte : nat → nat → Type
| zero (n : nat) : lte 0 n
| succ {n m : nat} : lte n m → lte (1 + n) (1 + m)

lemma lt_lte {n m} : lt n m → lte n m :=
  begin
    intro lt_n_m,
    induction' lt_n_m,
    case less_than.lt.zero_succ : i {
      constructor
    },
    case less_than.lt.succ_succ : i j lt_i_j ih {
      constructor,
      apply ih
    }
  end.

end less_than


/- Palindromes -/

namespace palindrome

inductive palindrome {α : Type} : list α → Prop
| nil : palindrome []
| single (x : α) : palindrome [x]
| sandwich (x : α) (xs : list α) (hpal : palindrome xs) :
  palindrome ([x] ++ xs ++ [x])

axiom reverse_append_sandwich {α : Type} (x : α) (ys : list α) :
  list.reverse ([x] ++ ys ++ [x]) = [x] ++ list.reverse ys ++ [x]

lemma rev_palindrome {α : Type} (xs : list α) (hpal : palindrome xs) :
  palindrome (list.reverse xs) :=
begin
  induction' hpal,
  case nil {
    exact palindrome.nil
  },
  case single {
    exact palindrome.single _
  },
  case sandwich {
    rw reverse_append_sandwich,
    apply palindrome.sandwich,
    apply ih
  }
end

end palindrome


/- Transitive Closure -/

namespace transitive_closure

inductive tc {α : Type} (r : α → α → Prop) : α → α → Prop
| base (x y : α) (hr : r x y) : tc x y
| step (x y z : α) (hr : r x y) (ht : tc y z) : tc x z

/- The transitive closure is a nice example with lots of variables to keep track
of. We start with a lemma where the variable names do not collide with those
appearing in the definition of the inductive predicate. -/

lemma tc_pets₁ {α : Type} (r : α → α → Prop) (c : α) :
  ∀a b, tc r a b → r b c → tc r a c :=
begin
  intros a b htab hrbc,
  induction' htab fixing c,
  case base : _ _ hrab {
    exact tc.step _ _ _ hrab (tc.base _ _ hrbc)
  },
  case step : _ x _ hrax {
    exact tc.step _ _ _ hrax (ih hrbc)
  }
end

/- The same proof, but this time the variable names clash. Also, this time we
let `xinduction` generalize `z`. -/

lemma tc_pets₂ {α : Type} (r : α → α → Prop) (z : α) :
  ∀x y, tc r x y → r y z → tc r x z :=
begin
  intros x y htxy hryz,
  induction' htxy,
  case base : _ _ hrxy {
    exact tc.step _ _ _ hrxy (tc.base _ _ hryz)
  },
  case step : _ x' y hrxx' htx'y ih {
    exact tc.step _ _ _ hrxx' (ih _ hryz)
  }
end

/- Another proof along the same lines. -/

lemma tc_trans {α : Type} (r : α → α → Prop) (c : α) :
  ∀a b : α, tc r a b → tc r b c → tc r a c :=
begin
  intros a b htab htbc,
  induction' htab,
  case base {
    exact tc.step _ _ _ hr htbc
  },
  case step {
    exact tc.step _ _ _ hr (ih _ htbc)
  }
end

end transitive_closure


/- Evenness -/

inductive even : ℕ → Prop
| zero    : even 0
| add_two : ∀k : ℕ, even k → even (k + 2)

lemma not_even_2_mul_add_1 (n : ℕ) :
  ¬ even (2 * n + 1) :=
begin
  intro h,
  induction' h,
  -- TODO no case tag since there's only one goal. I don't really like this, but
  -- this is the behaviour of induction/cases.
  {
    apply ih (n - 1),
    cases n,
    case zero {
      linarith
    },
    case succ {
      simp [nat.succ_eq_add_one] at *,
      linarith
    }
  }
end


/- Big-Step Semantics -/

namespace semantics

def state :=
string → ℕ

def state.update (name : string) (val : ℕ) (s : state) : state :=
λname', if name' = name then val else s name'

notation s `{` name ` ↦ ` val `}` := state.update name val s

inductive stmt : Type
| skip   : stmt
| assign : string → (state → ℕ) → stmt
| seq    : stmt → stmt → stmt
| ite    : (state → Prop) → stmt → stmt → stmt
| while  : (state → Prop) → stmt → stmt

export stmt

/- Our first version is partly uncurried, like in the Logical Verification
course, and also like in Concrete Semantics. This makes the binary infix
notation possible. -/

inductive big_step : stmt × state → state → Prop
| skip {s} :
  big_step (skip, s) s
| assign {x a s} :
  big_step (assign x a, s) (s{x ↦ a s})
| seq {S T s t u} (hS : big_step (S, s) t)
    (hT : big_step (T, t) u) :
  big_step (seq S T, s) u
| ite_true {b : state → Prop} {S T s t} (hcond : b s)
    (hbody : big_step (S, s) t) :
  big_step (ite b S T, s) t
| ite_false {b : state → Prop} {S T s t} (hcond : ¬ b s)
    (hbody : big_step (T, s) t) :
  big_step (ite b S T, s) t
| while_true {b : state → Prop} {S s t u} (hcond : b s)
    (hbody : big_step (S, s) t)
    (hrest : big_step (while b S, t) u) :
  big_step (while b S, s) u
| while_false {b : state → Prop} {S s} (hcond : ¬ b s) :
  big_step (while b S, s) s

infix ` ⟹ `:110 := big_step

lemma not_big_step_while_true {S s t} :
  ¬ (while (λ_, true) S, s) ⟹ t :=
begin
  intro hw,
  induction' hw,
  case while_true {
    exact ih_hw_1
  },
  case while_false {
    apply hcond,
    trivial
  }
end

/- Desired proof script:

lemma not_big_step_while_true {S s t} :
  ¬ (while (λ_, true) S, s) ⟹ t :=
begin
  xinduction hw,
  case while_true {
    exact ih_hrest },
  case while_false {
    apply hcond,
    apply true.intro }
end -/

/- The next version is fully curried. Ideally, both versions should behave more
or less the same as far as induction is concerned. -/

inductive curried_big_step : stmt → state → state → Prop
| skip {s} :
  curried_big_step skip s s
| assign {x a s} :
  curried_big_step (assign x a) s (s{x ↦ a s})
| seq {S T s t u} (hS : curried_big_step S s t)
    (hT : curried_big_step T t u) :
  curried_big_step (seq S T) s u
| ite_true {b : state → Prop} {S T s t} (hcond : b s)
    (hbody : curried_big_step S s t) :
  curried_big_step (ite b S T) s t
| ite_false {b : state → Prop} {S T s t} (hcond : ¬ b s)
    (hbody : curried_big_step T s t) :
  curried_big_step (ite b S T) s t
| while_true {b : state → Prop} {S s t u} (hcond : b s)
    (hbody : curried_big_step S s t)
    (hrest : curried_big_step (while b S) t u) :
  curried_big_step (while b S) s u
| while_false {b : state → Prop} {S s} (hcond : ¬ b s) :
  curried_big_step (while b S) s s

set_option trace.check true

lemma not_curried_big_step_while_true {S s t} :
  ¬ curried_big_step (while (λ_, true) S) s t :=
begin
  intro hw,
  induction' hw,
  case while_true {
    exact ih_hw_1,
  },
  case while_false {
    exact hcond trivial
  }
end

end semantics


/- Small-Step Semantics -/

namespace semantics

inductive small_step : stmt × state → stmt × state → Prop
| assign {x a s} :
  small_step (assign x a, s) (skip, s{x ↦ a s})
| seq_step {S S' T s s'} (hS : small_step (S, s) (S', s')) :
  small_step (seq S T, s) (seq S' T, s')
| seq_skip {T s} :
  small_step (seq skip T, s) (T, s)
| ite_true {b : state → Prop} {S T s} (hcond : b s) :
  small_step (ite b S T, s) (S, s)
| ite_false {b : state → Prop} {S T s} (hcond : ¬ b s) :
  small_step (ite b S T, s) (T, s)
| while {b : state → Prop} {S s} :
  small_step (while b S, s) (ite b (seq S (while b S)) skip, s)

/- The next example yields unprovable subgoals, where the variables `S`, `s'`,
`T`, and `T'` are not instantiated properly. The reason seems to be that
`(S, s)` and `(T, t)` are replaced en bloc, and hence `(S, s')` and `(S, t')`
are left alone. `cases` does the right thing but gives no induction
hypothesis. -/

-- TODO tuple equation simplification
lemma small_step_if_equal_states {S T s t s' t'}
    (hstep : small_step (S, s) (T, t)) (hs : s' = s) (ht : t' = t) :
  small_step (S, s') (T, t') :=
begin
  -- revert hstep,
  -- generalize eq₁ : (S, s) = index₁,
  -- generalize eq₂ : (T, t) = index₂,
  -- intro hstep,
  -- revert S T s t s' t' hs ht,
  -- induction hstep; clear index₁ index₂; intros S T s t s' t' hs ht eq₁ eq₂,
  -- case seq_step : S_ S'_ T_ s t hS {
  --   clear index₁ index₂,
  --   injection eq₁,
  --   clear eq₁,
  --   subst h_1,
  --   subst h_2,
  --   injection eq₂,
  --   clear eq₂,
  --   subst h_1,
  --   subst h_2,
  -- },

  -- induction' hstep,
  -- { rw [hs, ht],
  --   exact small_step.assign,
  -- },
  -- {
  --   -- TODO is this the correct IH?
  --   -- TODO naming
  --   -- TODO the index equations in the IH could be simplified further
  --   rw [hs, ht],
  --   exact small_step.seq_step hstep
  -- },
  -- { rw [hs, ht]
  -- , exact small_step.seq_skip,
  -- },
  -- { rw [hs, ht],
  --   exact small_step.ite_true hcond,
  -- },
  -- { rw [hs, ht],
  --   exact small_step.ite_false hcond,
  -- },
  -- { rw [hs, ht],
  --   exact small_step.while,
  -- }
  sorry
end

/- `cases` is better behaved. -/

lemma small_step_if_equal_states₂ {S T s t s' t'}
    (hstep : small_step (S, s) (T, t)) (hs : s' = s) (ht : t' = t) :
  small_step (S, s') (T, t') :=
begin
  cases hstep,
  case small_step.assign : x a {
    change t' = s{x ↦ a s} at ht,  /- Change back! -/
    clear hstep,
    /- Desired state here. -/
    rw [hs, ht],
    exact small_step.assign },
  case small_step.seq_step : S S' T s t hS {
    clear hstep,
    have ih : ∀s s' t t', s' = s → t' = t →
      small_step (S, s') (S', t') := sorry,
    /- Ideally the one-point rule shouldn't be used here. -/
    /- Desired state here. -/
    rw [hs, ht],
    exact small_step.seq_step hS },
  case small_step.seq_skip {
    clear hstep,
    /- Desired state here. -/
    rw [hs, ht],
    exact small_step.seq_skip },
  case small_step.ite_true : _ _ _ _ hcond {
    clear hstep,
    /- Desired state here. -/
    rw [hs, ht],
    exact small_step.ite_true hcond },
  case small_step.ite_false : _ _ _ _ hcond {
    clear hstep,
    /- Desired state here. -/
    rw [hs, ht],
    exact small_step.ite_false hcond },
  case small_step.while : b S {
    clear hstep,
    /- Desired state here. -/
    rw [hs, ht],
    exact small_step.while }
end

end semantics


/- TODO: Do examples like `measure_induct_rule` in `Lambda_Free_RPOs`? -/
