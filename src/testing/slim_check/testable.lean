/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Simon Hudon
-/

import testing.slim_check.arbitrary

/-!
# Testable Class

Testable propositions have a procedure that can generate counter-examples
together with a proof that they invalidate the proposition.

This is a port of the Haskell QuickCheck library.

## How to get started

A proposition can be tested by writing it out as:

```lean
#eval testable.check (∀ xs : list ℕ, (∃ x ∈ xs, x < 3) → (∀ y ∈ xs, y < 5))
-- ===================
-- Found problems!

-- xs := [0, 5]
-- x := 0
-- y := 5
-- -------------------

#eval testable.check (∀ x : ℕ, 2 ∣ x → x < 100)
-- ===================
-- Found problems!

-- x := 258
-- -------------------

#eval testable.check (∀ (α : Type) (xs ys : list α), xs ++ ys = ys ++ xs)
-- ===================
-- Found problems!

-- α := ℤ
-- xs := [-4]
-- ys := [1]
-- -------------------

#eval testable.check (∀ x ∈ [1,2,3], x < 4)
-- Success
```

`testable.check p` finds a `testable p` instance which lets us find
data to test the proposition `p`.  For instance, `testable.check (∀ x
: ℕ, 2 ∣ x → x < 100)` builds the `testable` instance step by step
with:

```
testable (∀ x : ℕ, 2 ∣ x → x < 100) -: arbitrary ℕ, decidable (λ x, 2 ∣ x), testable (λ x, x < 100)
testable (λ x, x < 100)              -: decidable (λ x, x < 100)
```

`arbitrary ℕ` lets us create random data of type `ℕ` in a way that
helps find small counter-examples.  Next, the test of the proposition
hinges on `2 ∣ 100` and `x < 100` to both be decidable. The
implication between the two could be tested as a whole but it would be
less informative. Indeed, we could generate a hundred odd numbers and
the property would be shown to hold for each but the right conclusion
is that we haven't found meaningful examples. Instead, when `2 ∣ x`
does not hold, we reject the example (i.e.  we do not count it toward
the 100 required positive examples) and we start over. Therefore, when
`testable.check` prints `Success`, it means that a hundred even
numbers were found to be less than 100.

### Polymorphism

The property `testable.check (∀ (α : Type) (xs ys : list α), xs ++ ys
= ys ++ xs)` shows us that type-polymorphic properties can be
tested. `α` is instantiated with `ℤ` first and then tested as normal
monomorphic properties.

### What do I do if I'm testing a property about my newly defined type?

Let us consider a type made for a new formalization:

```lean
structure my_type :=
(x y : ℕ)
(h : x ≤ y)
```

How do we test a property about `my_type`? For instance, let us consider
`testable.check $ ∀ a b : my_type, a.y ≤ b.x → a.x ≤ b.y`. Writing this
property as is will give us an error because we do not have an instance
of `arbitrary my_type`. We can define one as follows:

```lean
instance : arbitrary my_type :=
{ arby := do
  x ← arby ℕ,
  xy_diff ← arby ℕ,
  return { x := x, y := x + xy_diff, h := /- some proof -/ } }
```

We can see that the instance is very simple because our type is built
up from other type that have `arbitrary` instances. `arbitrary` also
has a `shrink` method but it is optional. We may want to implement one
for ease of testing as:

```lean
/- ... -/
  shrink := λ ⟨x,y,h⟩, (λ ⟨x,y⟩, { x := x, y := x + y, h := /- proof -/}) <$> shrink (x, y - x)
}
```

Again, we take advantage of the fact that other types have useful
`shrink` implementations, in this case `prod`.

## Main definitions
  * `testable` class
  * `testable.check` a way to test a proposition using random examples

## Tags

random testing

## References

  * https://hackage.haskell.org/package/QuickCheck

-/

universes u v

variable α : Type u
variable β : α → Prop
variable f : Type → Prop

namespace slim_check

/-- Result of trying to disprove `p` -/
@[derive inhabited]
inductive test_result (p : Prop)
  /- succeed when we find another example satisfying `p` -/
| success : (psum unit p) → test_result
  /- give up when a well-formed example cannot be generated -/
| gave_up {} : ℕ → test_result
  /- a counter-example to `p`; the strings specify values for the relevant variables -/
| failure : ¬ p → (list string) → test_result

/-- `testable p` uses random examples to try to disprove `p` -/
class testable (p : Prop) :=
(run [] (minimize : bool) : gen (test_result p)) --

open list

open test_result

/-- applicative combinator proof carrying test results -/
def combine {p q : Prop} : psum unit (p → q) → psum unit p → psum unit q
| (psum.inr f) (psum.inr x) := psum.inr (f x)
| _ _ := psum.inl ()

/-- Combine the test result for properties `p` and `q` to create a test for the conjunction -/
def and_counter_example {p q : Prop} :
  test_result p →
  test_result q →
  test_result (p ∧ q)
 | (failure Hce xs) _ := failure (λ h, Hce h.1) xs
 | _ (failure Hce xs) := failure (λ h, Hce h.2) xs
 | (success xs) (success ys) := success $ combine (combine (psum.inr and.intro) xs) ys
 | (gave_up n) (gave_up m) := gave_up $ n + m
 | (gave_up n) _ := gave_up n
 | _ (gave_up n) := gave_up n

/-- If `q → p`, then `¬ p → ¬ q` which means that testing `p` can allow us
to find counter-examples to `q` -/
def convert_counter_example {p q : Prop}
  (h : q → p) :
  test_result p →
  opt_param (psum unit (p → q)) (psum.inl ()) →
  test_result q
 | (failure Hce xs) _ := failure (mt h Hce) xs
 | (success Hp) Hpq := success (combine Hpq Hp)
 | (gave_up n) _ := gave_up n

/-- test `q` by testing `p` and proving the equivalence between the two -/
def convert_counter_example' {p q : Prop}
  (h : p ↔ q) (r : test_result p) :
  test_result q :=
convert_counter_example h.2 r (psum.inr h.1)

/-- When we assign a value to a universally quantified variable,
we record that value using this function so that our counter-examples
can be informative -/
def add_to_counter_example (x : string) {p q : Prop}
  (h : q → p)
: test_result p →
  opt_param (psum unit (p → q)) (psum.inl ()) →
  test_result q
 | (failure Hce xs) _ := failure (mt h Hce) $ x :: xs
 | r hpq := convert_counter_example h r hpq

/-- add some formatting to the information recorded by `add_to_counter_example` -/
def add_var_to_counter_example {γ : Type v} [has_to_string γ]
  (var : string) (x : γ) {p q : Prop}
  (h : q → p)
: test_result p →
  opt_param (psum unit (p → q)) (psum.inl ()) →
  test_result q :=
@add_to_counter_example (var ++ " := " ++ to_string x) _ _ h

/-- gadget used to introspect the name of bound variables -/
@[simp, nolint unused_arguments]
def named_binder (n : option string) (p : Prop) : Prop := p

/-- Is the given test result a failure? -/
def is_failure {p} : test_result p → bool
| (test_result.failure _ _) := tt
| _ := ff

instance and_testable (p q : Prop) [testable p] [testable q] :
  testable (p ∧ q) :=
⟨ λ min, do
   xp ← testable.run p min,
   xq ← testable.run q min,
   pure $ and_counter_example xp xq ⟩

@[priority 5000]
instance imp_dec_testable {var} (p : Prop) [decidable p] (β : p → Prop)
  [∀ h, testable (β h)]
: testable (named_binder var $ Π h, β h) :=
⟨ λ min, do
    if h : p
    then (λ r, convert_counter_example ($ h) r (psum.inr $ λ q _, q)) <$> testable.run (β h) min
    else return $ gave_up 1 ⟩

@[priority 2000]
instance all_types_testable (var : string) [testable (f ℤ)]
: testable (named_binder (some var) $ Π x, f x) :=
⟨ λ min, do
    r ← testable.run (f ℤ) min,
    return $ add_var_to_counter_example var "ℤ" ($ ℤ) r ⟩

/-- testable instance for universal properties; use the chosen example and
instantiate the universal quantification with it -/
def test_one (x : α) [testable (β x)] (var : option (string × string) := none) : testable (Π x, β x) :=
⟨ λ min, do
    r ← testable.run (β x) min,
    return $ match var with
      | none := convert_counter_example ($ x) r
      | (some (v,x_str)) := add_var_to_counter_example v x_str ($ x) r
      end ⟩

/-- testable instance for a property iterating over the element of a list -/
@[priority 5000]
instance test_forall_in_list (var : string) (var' : option string)
  [∀ x, testable (β x)] [has_to_string α] :
  Π xs : list α, testable (named_binder (some var) $ ∀ x, named_binder var' $ x ∈ xs → β x)
| [] := ⟨ λ min, return $ success $ psum.inr (by { introv x h, cases h} ) ⟩
| (x :: xs) :=
⟨ λ min, do
    r ← testable.run (β x) min,
    match r with
     | failure _ _ := return $ add_var_to_counter_example var x
                               (by { intro h, apply h, left, refl }) r
     | success hp := do
       rs ← @testable.run _ (test_forall_in_list xs) min,
       return $ convert_counter_example
                               (by { intros h i h',
                                     apply h,
                                     right, apply h' })
                               rs
                               (combine (psum.inr
                                $ by { intros j h, simp only [ball_cons,named_binder],
                                       split ; assumption, } ) hp)
     | gave_up n := do
       rs ← @testable.run _ (test_forall_in_list xs) min,
       match rs with
        | (success _) := return $ gave_up n
        | (failure Hce xs) := return $ failure
                    (by { simp only [ball_cons,named_binder],
                          apply not_and_of_not_right _ Hce, }) xs
        | (gave_up n') := return $ gave_up (n + n')
       end
    end ⟩

/-- Test proposition `p` by randomly selecting one of the provided
testable instance -/
def combine_testable (p : Prop)
  (t : list $ testable p) (h : 0 < t.length)
: testable p :=
⟨ λ min, have 0 < length (map (λ t, @testable.run _ t min) t),
    by { rw [length_map], apply h },
  gen.one_of (list.map (λ t, @testable.run _ t min) t) this ⟩

/-- Once a property fails to hold on an example, look for smaller counter-examples
to show the user -/
def minimize [∀ x, testable (β x)] (x : α) (r : test_result (β x)) : lazy_list α → gen (Σ x, test_result (β x))
| lazy_list.nil := pure ⟨x,r⟩
| (lazy_list.cons x xs) := do
  ⟨r⟩ ← uliftable.up $ testable.run (β x) tt,
     if is_failure r
       then pure ⟨x, convert_counter_example id r (psum.inl ())⟩
       else minimize $ xs ()

@[priority 5000]
instance exists_testable {p : Prop}
  (var var' : option string)
  [testable (named_binder var (∀ x, named_binder var' $ β x → p))] :
  testable (named_binder var' (named_binder var (∃ x, β x) → p)) :=
⟨ λ min, do
    x ← testable.run (named_binder var (∀ x, named_binder var' $ β x → p)) min,
    pure $ convert_counter_example' exists_imp_distrib.symm x ⟩

/-- Test a universal property by choosing arbitrary examples to instantiate the
bound variable with -/
instance var_testable [has_to_string α] [arbitrary α] [∀ x, testable (β x)]
  (var : option string)
: testable (named_binder var $ Π x : α, β x) :=
⟨ λ min, do
   uliftable.adapt_down (arby α) $
   λ x, do
     r ← testable.run (β x) ff,
     uliftable.adapt_down (if is_failure r ∧ min then minimize _ _ x r (shrink x) else pure ⟨x,r⟩) $
     λ ⟨x,r⟩, return $ match var with
                      | none := add_to_counter_example (to_string x) ($ x) r
                      | (some v) := add_var_to_counter_example v x ($ x) r
                      end⟩

@[priority 3000]
instance unused_var_testable {β} [inhabited α] [testable β]
  (var : option string)
: testable (named_binder var $ Π x : α, β) :=
⟨ λ min, do
  r ← testable.run β min,
  pure $ convert_counter_example ($ default _) r (psum.inr $ λ x _, x) ⟩

@[priority 2000]
instance subtype_var_testable {p : α → Prop} [has_to_string α] [arbitrary (subtype p)]
  [∀ x, testable (β x)]
  (var var' : option string)
: testable (named_binder var $ Π x : α, named_binder var' $ p x → β x) :=
⟨ λ min,
   do r ← @testable.run (∀ x : subtype p, β x.val) (slim_check.var_testable _ _ var) min,
      pure $ convert_counter_example'
        ⟨λ (h : ∀ x : subtype p, β x) x h', h ⟨x,h'⟩,
         λ h ⟨x,h'⟩, h x h'⟩
        r ⟩

@[priority 100]
instance decidable_testable {p : Prop} [decidable p] : testable p :=
⟨ λ min, return $ if h : p then success (psum.inr h) else failure h [] ⟩

section io

variable (p : Prop)

open nat

variable {p}

/-- execute `cmd` and repeat every time the result is `gave_up` or at most
`n` times -/
def retry (cmd : rand (test_result p)) : ℕ → rand (test_result p)
 | 0 := return $ gave_up 1
 | (succ n) := do
r ← cmd,
match r with
 | success hp := return $ success hp
 | (failure Hce xs) := return (failure Hce xs)
 | (gave_up _) := retry n
end

/-- Count the number of times the test procedure gave up -/
def give_up (x : ℕ) : test_result p → test_result p
 | (success (psum.inl ())) := gave_up x
 | (success (psum.inr p))  := success (psum.inr p)
 | (gave_up n) := gave_up (n+x)
 | (failure Hce xs) := failure Hce xs

variable (p)

variable [testable p]

/-- configuration for testing a property -/
@[derive [has_reflect, inhabited]]
structure slim_check_cfg :=
(num_inst : ℕ := 100) -- number of examples
(max_size : ℕ := 100) -- final size argument

/-- Try `n` times to find a counter-example for `p` -/
def testable.run_suite_aux (cfg : slim_check_cfg) : test_result p → ℕ → rand (test_result p)
 | r 0 := return r
 | r (succ n) :=
do let size := (cfg.num_inst - n - 1) * cfg.max_size / cfg.num_inst,
   x ← retry ( (testable.run p tt).run ⟨ size ⟩) 10,
   match x with
    | (success (psum.inl ())) := testable.run_suite_aux r n
    | (success (psum.inr Hp)) := return $ success (psum.inr Hp)
    | (failure Hce xs) := return (failure Hce xs)
    | (gave_up g) := testable.run_suite_aux (give_up g r) n
   end

/-- Try to find a counter-example of `p` -/
def testable.run_suite (cfg : slim_check_cfg := {}) : rand (test_result p) :=
testable.run_suite_aux p cfg (success $ psum.inl ()) cfg.num_inst

/-- Run a test suite for `p` in `io` -/
def testable.check' (cfg : slim_check_cfg := {}) : io (test_result p) :=
io.run_rand (testable.run_suite p cfg)

namespace tactic

open tactic expr

meta def add_binder_name : expr → ℕ → option expr
| (pi n bi d b) _ :=
  let n := to_string n in
  some $ const ``named_binder [] (const ``option.some [level.zero] (`(string) : expr) (reflect n : expr)) (pi n bi d b)
| e@`(@Exists %%α %%(lam n bi d b)) _ :=
  let n := to_string n in
  some $ const ``named_binder [] (const ``option.some [level.zero] (`(string) : expr) (reflect n : expr)) e
| e _ := none

meta def add_existential_decorations : expr → expr
| e@`(@Exists %%α %%(lam n bi d b)) :=
  let n := to_string n in
  const ``named_binder [] (const ``option.some [level.zero] (`(string) : expr) (reflect n : expr)) e
| e := e

@[reducible]
def decorations_of (p : Prop) := Prop

meta def add_decorations : expr → expr | e :=
e.replace $ λ e _,
  match e with
  | (pi n bi d b) :=
    let n := to_string n in
    some $ const ``named_binder [] (const ``option.some [level.zero] (`(string) : expr) (reflect n : expr)) (pi n bi (add_existential_decorations d) (add_decorations b))
  | e := none
  end

meta def mk_decorations : tactic unit := do
`(tactic.decorations_of %%p) ← target,
exact $ add_decorations p

end tactic

/-- Run a test suite for `p` and return true or false: should we believe that `p` holds? -/
def testable.check (p : Prop) (cfg : slim_check_cfg := {}) (p' : tactic.decorations_of p . tactic.mk_decorations) [testable p'] : io bool := do
x ← io.run_rand (testable.run_suite p' cfg),
match x with
 | (success _) := io.put_str_ln ("Success") >> return tt
 | (gave_up n) := io.put_str_ln ("Gave up " ++ repr n ++ " times") >> return ff
 | (failure _ xs) := do
   io.put_str_ln "\n===================",
   io.put_str_ln "Found problems!",
   io.put_str_ln "",
   list.mmap' io.put_str_ln xs,
   io.put_str_ln "-------------------",
   return ff
end

end io

end slim_check
