import tactic.induction tactic.linarith

set_option trace.app_builder true
-- set_option pp.all true

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

example (k) : 0 + k = k :=
begin
  induction' k,
  { refl },
  { simp [ih] }
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
  { simp [ih, List.append] }
end

example {k l} (h : lt k l) : le k l :=
begin
  induction' h,
  { constructor },
  { constructor,
    assumption
  }
end

-- This example tests whether `induction'` gets confused when there are
-- additional cases around.
example (k) (t : Two) : 0 + k = k :=
begin
  cases t,
  induction' k,
  { refl },
  { simp [ih] },
  induction' k,
  { refl },
  { simp [ih] }
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


-- TODO debug
namespace tactic

meta def trace_unique_name (n : name) : tactic unit := do
  (expr.local_const u _ _ _) ← resolve_name n,
  trace u

meta def trace_tag : tactic unit := do
  (t : list name) ← get_main_tag,
  trace t

end tactic


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


example (n : ℕ) : ℕ :=
begin
  apply nat.succ,
  tactic.trace_tag
end


-- TODO case tags, type-based naming
lemma subst_Var (e : exp) :
  subst (λx, Var x) e = e :=
begin
  induction e,
  case Var {
    tactic.trace_unique_name `e,
    let x : ℕ := 2,
    cases x,
    { tactic.trace_unique_name `e, sorry },
    { sorry }
  },
  { sorry },
  { sorry }
  -- (do
  --   gs ← tactic.get_goals,
  --   ts ← gs.mmap tactic.get_tag,
  --   ts.mmap' (λ t, tactic.trace (format_tag t)),
  --   pure ()
  -- ),
  -- case Var {
  --   -- rename e s,
  --   rename x s,
  --   /- Desired state here. -/
  --   rw [subst]
  -- },
  -- -- case Num {
  -- {
  --   -- rename e z,
  --   rename x z,
  --   /- Desired state here. -/
  --   rw [subst]
  -- },
  -- -- case Plus {
  -- {
  --   rw [subst],
  --   rw ih_e,
  --   rw ih_e_1
  --  }
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

-- TODO case tags
lemma lt_lte {n m} : lt n m → lte n m :=
  begin
    intro lt_n_m,
    induction' lt_n_m,
    {
    -- case less_than.lt.zero_succ : k {
      constructor
    },
    -- case less_than.lt.succ_succ : k l lt_k_l ih {
    {
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

-- TODO case tags, no type-changing index-based renaming
lemma rev_palindrome {α : Type} (xs : list α) (hpal : palindrome xs) :
  palindrome (list.reverse xs) :=
begin
  induction' hpal,
  -- case palindrome.nil {
  {
    exact palindrome.nil
  },
  -- case palindrome.single {
  {
    -- TODO Currently, the index-based renaming generates the name `xs`, which
    -- is a bit of a misnomer. To prevent this, the index-based renaming should
    -- only apply when the constructor argument being named has the same base
    -- type as the index/indices for which it is named.
    rename xs x,
    exact palindrome.single _
  },
  -- case palindrome.sandwich {
  {
    rename xs x,
    rename xs_1 xs,
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

-- TODO case tags, fixing
lemma tc_pets₁ {α : Type} (r : α → α → Prop) (c : α) :
  ∀a b, tc r a b → r b c → tc r a c :=
begin
  intros a b htab hrbc,
  induction' htab,
  -- Desired syntax above: `induction htab fixing c`.
  -- case tc.base {   -- should be `case base`
  {
    rename hr hrab,
    exact tc.step _ _ _ hrab (tc.base _ _ hrbc) },
  -- case tc.step {   -- should be `case step`
  {
    rename y x,
    rename hr hrax,
    specialize ih c,
    exact tc.step _ _ _ hrax (ih hrbc) }
end

/- The same proof, but this time the variable names clash. Also, this time we
let `xinduction` generalize `z`. -/

lemma tc_pets₂ {α : Type} (r : α → α → Prop) (z : α) :
  ∀x y, tc r x y → r y z → tc r x z :=
begin
  intros x y htxy hryz,
  induction htxy generalizing z,
  /- Desired syntax above: `induction htxy`. -/
  case tc.base {   -- should be `case base`
    clear x y,
    rename htxy_x x,
    rename htxy_y y,
    rename htxy_hr hr,
    rename hryz hryz,   -- just to move it back where it used to be
    /- Desired state here. Writing `case tc.base : hrxy` above would rename `hr`
    to `hrxy`. -/
    rename hr hrxy,
    /- Like this. -/
    exact tc.step _ _ _ hrxy (tc.base _ _ hryz)
  },
  case tc.step {   -- should be `case step`
    clear x y,
    rename htxy_x x,
    rename htxy_y ya,   -- fresh (Isabelle-style) name to avoid clash
    rename htxy_z y,
    rename htxy_hr hr,
    rename htxy_ht ht,
    rename htxy_ih ih,
    rename hryz hryz,   -- just to move it back where it used to be
    /- Desired state here. Writing `case tc.step : x' hrxx' htx'y ih` would also
    rename `y`, `hr`, `ht`, and `ih` to `x'`, `hrxx'`, `htx'y`, and `ih`,
    respectively. -/
    rename ya x',
    rename hr hrxx',
    rename ht htx'y,
    rename ih ih,
    /- Like this. -/
    exact tc.step _ _ _ hrxx' (ih _ hryz)
  }
end

/- Another proof along the same lines. -/

lemma tc_trans {α : Type} (r : α → α → Prop) (c : α) :
  ∀a b : α, tc r a b → tc r b c → tc r a c :=
begin
  intros a b htab htbc,
  induction htab generalizing c,
  /- Desired syntax: `induction htab`. -/
  case tc.base {
    clear a b,
    rename htab_x a,
    rename htab_y b,
    rename htab_hr hr,
    rename htbc htbc,
    /- Desired state here. -/
    exact tc.step _ _ _ hr htbc
  },
  case tc.step {
    clear a b,
    rename htab_x a,
    rename htab_y y,
    rename htab_z b,
    rename htab_hr hr,
    rename htab_ht ht,
    rename htab_ih ih,
    rename htbc htbc,
    /- Desired state here. -/
    exact tc.step _ _ _ hr (ih _ htbc)
  }
end

end transitive_closure


/- Evenness -/

inductive even : ℕ → Prop
| zero    : even 0
| add_two : ∀k : ℕ, even k → even (k + 2)

-- TODO case tags, complex indices
lemma not_even_2_mul_add_1 (n : ℕ) :
  ¬ even (2 * n + 1) :=
begin
  generalize heq : 2 * n + 1 = x,
  intro h,
  revert n,
  induction' h,
  /- Desired syntax for the above two lines: `intro h, induction h`. -/
  -- case even.zero {
  {
    cases heq },
  -- case even.add_two : k hk ih {
  {
    apply ih (n - 1),
    cases n,
    case nat.zero {
      linarith },
    case nat.succ : m {
      simp [nat.succ_eq_add_one] at *,
      linarith } }
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

-- TODO case tags, complex indices
lemma not_big_step_while_true {S s t} :
  ¬ (while (λ_, true) S, s) ⟹ t :=
begin
  generalize heq : (while (λ_, true) S, s) = ws,
  intro hw,
  induction hw generalizing S s,
  /- Desired syntax for all of the above: `induction hw`. -/
  all_goals {
    cases heq;
    clear heq
  },
  { /- case while_true -/
    clear ws t,
    rename hw_S S,
    rename hw_s s,
    rename hw_t ta,
    rename hw_u t,
    rename hw_hcond hcond,
    have ih_hbody : ∀{Sa : stmt}, while (λ_x : state, true) Sa = S → false :=
      begin
        intros,
        apply hw_ih_hbody,
        rw a
      end,
    clear hw_ih_hbody,
    rename hw_hbody hbody,
    rename hw_hrest hrest,
    have ih_hrest : false :=
      begin
        apply hw_ih_hrest,
        refl
      end,
    clear hw_ih_hrest,
    /- Desired state here. -/
    exact ih_hrest
  },
  { /- case while_false -/
    clear ws t hw_S,
    rename hw_s s,
      -- `rename hw_s t` would also be OK, but let us proceed from left to right
    rename hw_hcond hcond,
    /- Desired state here. -/
    apply hcond,
    apply true.intro
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

-- TODO case tags, complex indices
lemma not_curried_big_step_while_true {S s t} :
  ¬ curried_big_step (while (λ_, true) S) s t :=
begin
  generalize heq : while (λ_, true) S = w,
  intro hw,
  induction hw generalizing S,
  /- Desired syntax for all of the above: `induction hw`. -/
  /- It is not possible (or necessary) to generalize `s` here, probably because
  it does not occur elsewhere in the goal. -/
  all_goals {
    cases heq;
    clear heq
  },
  { /- case while_true -/
    clear w t,
    rename hw_S S,
    rename hw_s s,
    rename hw_t ta,
    rename hw_u t,
    rename hw_hcond hcond,
    have ih_hbody : ∀{Sa : stmt}, while (λ (_x : state), true) Sa = S → false :=
      begin
        intros,
        apply hw_ih_hbody,
        rw a
      end,
    clear hw_ih_hbody,
    rename hw_hbody hbody,
    rename hw_hrest hrest,
    have ih_hrest : false :=
      begin
        apply hw_ih_hrest,
        refl
      end,
    clear hw_ih_hrest,
    /- Desired state here. -/
    exact ih_hrest },
  { /- case while_false -/
    clear w t hw_S,
    rename hw_s s,
      -- `rename hw_s t` would also be OK, but let us proceed from left to right
    rename hw_hcond hcond,
    /- Desired state here. -/
    apply hcond,
    apply true.intro
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
--ouq

/- The next example yields unprovable subgoals, where the variables `S`, `s'`,
`T`, and `T'` are not instantiated properly. The reason seems to be that
`(S, s)` and `(T, t)` are replaced en bloc, and hence `(S, s')` and `(S, t')`
are left alone. `cases` does the right thing but gives no induction
hypothesis. -/

lemma small_step_if_equal_states {S T s t s' t'}
    (hstep : small_step (S, s) (T, t)) (hs : s' = s) (ht : t' = t) :
  small_step (S, s') (T, t') :=
begin
  induction hstep,
  repeat { sorry }
end

/- `cases` is better behaved. -/

-- TODO case tags, complex indices
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
  case small_step.seq_step : S S' T hS {
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
  case small_step.ite_true : b t hcond {
    clear hstep,
    /- Desired state here. -/
    rw [hs, ht],
    exact small_step.ite_true hcond },
  case small_step.ite_false : b s hcond {
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
