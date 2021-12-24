import algebra.group.basic
import data.nat.basic
import tactic.explode_widget


-- Section monoid.
--   Variable A : Set.
--   Variable e : A.
--   Variable f : A -> A -> A.

--   Infix "+" := f.

--   Hypothesis assoc : forall a b c, (a + b) + c = a + (b + c).
--   Hypothesis identl : forall a, e + a = a.
--   Hypothesis identr : forall a, a + e = a.

-- We add variables and hypotheses characterizing an arbitrary instance of the algebraic structure of monoids. We have an associative binary operator and an identity element for it.
-- It is easy to define an expression tree type for monoid expressions. A Var constructor is a "catch-all" case for subexpressions that we cannot model. These subexpressions could be actual Gallina variables, or they could just use functions that our tactic is unable to understand.

section
universe u
variables (A : Type u)
inductive mexp : Type (u+1)
| Ident : mexp
| Var : A -> mexp
| Op : mexp -> mexp -> mexp

-- Next, we write an interpretation function.
-- this evaluates an expression using the given functions
variables (e : A) (f : A → A → A)
local infix `*` := f
open mexp
def mdenote : mexp A → A
| Ident := e
| (Var v) := v
| (Op me1 me2) := mdenote me1 * mdenote me2

-- We will normalize expressions by flattening them into lists, via associativity, so it is helpful to have a denotation function for lists of monoid values.

def mldenote : list A → A
| [] := e
| (x :: ls') := x * mldenote ls'

-- The flattening function itself is easy to implement.

def flatten : mexp A → list A
| (Ident) := []
| (Var x) := [x]
| (Op me1 me2) := flatten me1 ++ flatten me2

-- This function has a straightforward correctness proof in terms of our denote functions.

variables
(assoc : ∀ a b c, (a * b) * c = a * (b * c))
(identl : forall a, e * a = a)
(identr : forall a, a * e = a)
include assoc identl identr
lemma flatten_correct' (ml2 ml1) :
  f (mldenote A e f ml1) (mldenote A e f ml2) = mldenote A e f (ml1 ++ ml2) :=
begin
  induction ml1;
  simp [mldenote, assoc, *],
end

theorem flatten_correct (me) : mdenote A e f me = mldenote A e f (flatten A me) :=
begin
  induction me; simp [mdenote, flatten, mldenote, flatten_correct', *],
  rw flatten_correct' A e f assoc identl identr,
end

-- Now it is easy to prove a theorem that will be the main tool behind our simplification tactic.

theorem monoid_reflect (me1 me2) (h : mldenote A e f (flatten A me1) = mldenote A e f (flatten A me2)) :
  mdenote A e f me1 = mdenote A e f me2 :=
begin
  repeat {rw flatten_correct A e f assoc identl identr},
  assumption,
end
-- We implement reification into the mexp type.

end

meta def reify (ty : expr) (u : level) : expr → name → expr
| `(1) ``monoid := (expr.const ``mexp.Ident [u]).app ty -- : mexp %%t)
| `(%%me1 * %%me2) ``monoid :=
  let r1 := reify me1 ``monoid,
      r2 := reify me2 ``monoid,
      opp : expr := expr.const ``mexp.Op [u] in
      ((opp.app ty).app r1).app r2
| `(0) ``add_monoid := (expr.const ``mexp.Ident [u]).app ty -- : mexp %%t)
| `(%%me1 + %%me2) ``add_monoid :=
  let r1 := reify me1 ``add_monoid,
      r2 := reify me2 ``add_monoid,
      opp : expr := expr.const ``mexp.Op [u] in
      ((opp.app ty).app r1).app r2
    -- `(%%opp %%r1 %%r2)
| r _ := ((expr.const ``mexp.Var [u]).app ty).app r

-- The final monoid tactic works on goals that equate two monoid terms. We reify each and change the goal to refer to the reified versions, finishing off by applying monoid_reflect and simplifying uses of mldenote. Recall that the change tactic replaces a conclusion formula with another that is definitionally equal to it.

open tactic
meta def monoid_tac : tactic unit :=
do
  `(%%e₁ = %%e₂) ← target
  | fail "monoid tactic failed: the goal is not an equality",
  α ← infer_type e₁,
  (cs, add) ← (mk_app ``monoid [α] >>= mk_instance >>= λ t, pure (t, ``monoid))
      <|> (mk_app ``add_monoid [α] >>= mk_instance >>= λ t, pure (t, ``add_monoid)),
  expr.sort (level.succ u) ← infer_type α,
  let r1 := reify α u e₁ add,
  let r2 := reify α u e₂ add,
  (l, f) ← match add with
  | ``monoid :=
    do l ← to_expr ``(mdenote %%α 1 (*) %%r1 =
                (mdenote %%α 1 (*) %%r2)),
       f ← to_expr ``(monoid_reflect %%α 1 (*) mul_assoc one_mul mul_one),
       return (l, f)
  | ``add_monoid :=
    do l ← to_expr ``(mdenote %%α 0 (+) %%r1 = (mdenote %%α 0 (+) %%r2)),
       f ← to_expr ``(monoid_reflect %%α 0 (+) add_assoc zero_add add_zero),
       return (l, f)
  | _ := fail "not additive or multiplicative monoid"
  end,
  change l,
  apply f,
  `[dsimp [_root_.flatten, mldenote]],
  try reflexivity

-- We can make short work of theorems like this one:


theorem t1 (a b c d : ℕ) : a * b * c * d = a * (b * c) * d :=
begin monoid_tac, end
theorem t2 {M : Type*} (a b c d : M) [add_monoid M] : a + b + c + d = a + (b + c) + d :=
begin monoid_tac, end

#explode_widget t2
--   ============================
--    a + (b + (c + (d + e))) = a + (b + (c + (d + e)))

-- Our tactic has canonicalized both sides of the equality, such that we can finish the proof by reflexivity.

--     reflexivity.
--   Qed.

-- It is interesting to look at the form of the proof.

--   Print t1.










lemma test {M : Type*} [monoid M] {a b c : M} : a * b * c = a * (b * c) :=
begin
  monoid_tac,
end

#print test
#lint
