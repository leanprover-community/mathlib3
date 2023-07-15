/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/

import testing.slim_check.sampleable

/-!
# `testable` Class

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Testable propositions have a procedure that can generate counter-examples
together with a proof that they invalidate the proposition.

This is a port of the Haskell QuickCheck library.

## Creating Customized Instances

The type classes `testable` and `sampleable` are the means by which
`slim_check` creates samples and tests them. For instance, the proposition
`∀ i j : ℕ, i ≤ j` has a `testable` instance because `ℕ` is sampleable
and `i ≤ j` is decidable. Once `slim_check` finds the `testable`
instance, it can start using the instance to repeatedly creating samples
and checking whether they satisfy the property. This allows the
user to create new instances and apply `slim_check` to new situations.

### Polymorphism

The property `testable.check (∀ (α : Type) (xs ys : list α), xs ++ ys
= ys ++ xs)` shows us that type-polymorphic properties can be
tested. `α` is instantiated with `ℤ` first and then tested as normal
monomorphic properties.

The monomorphisation limits the applicability of `slim_check` to
polymorphic properties that can be stated about integers. The
limitation may be lifted in the future but, for now, if
one wishes to use a different type than `ℤ`, one has to refer to
the desired type.

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
of `sampleable my_type`. We can define one as follows:

```lean
instance : sampleable my_type :=
{ sample := do
  x ← sample ℕ,
  xy_diff ← sample ℕ,
  return { x := x, y := x + xy_diff, h := /- some proof -/ } }
```

We can see that the instance is very simple because our type is built
up from other type that have `sampleable` instances. `sampleable` also
has a `shrink` method but it is optional. We may want to implement one
for ease of testing as:

```lean
/- ... -/
  shrink := λ ⟨x,y,h⟩, (λ ⟨x,y⟩, { x := x, y := x + y, h := /- proof -/}) <$> shrink (x, y - x) }
```

Again, we take advantage of the fact that other types have useful
`shrink` implementations, in this case `prod`.

### Optimizing the sampling

Some properties are guarded by a proposition. For instance, recall this
example:

```lean
#eval testable.check (∀ x : ℕ, 2 ∣ x → x < 100)
```

When testing the above example, we generate a natural number, we check
that it is even and test it if it is even or throw it away and start
over otherwise. Statistically, we can expect half of our samples to be
thrown away by such a filter. Sometimes, the filter is more
restrictive. For instance we might need `x` to be a `prime`
number. This would cause most of our samples to be discarded.

We can help `slim_check` find good samples by providing specialized
sampleable instances. Below, we show an instance for the subtype
of even natural numbers. This means that, when producing
a sample, it is forced to produce a proof that it is even.

```lean
instance {k : ℕ} [fact (0 < k)] : sampleable { x : ℕ // k ∣ x } :=
{ sample := do { n ← sample ℕ, pure ⟨k*n, dvd_mul_right _ _⟩ },
  shrink := λ ⟨x,h⟩, (λ y, ⟨k*y, dvd_mul_right _ _⟩) <$> shrink x }
```

Such instance will be preferred when testing a proposition of the shape
`∀ x : T, p x → q`

We can observe the effect by enabling tracing:

```lean
/- no specialized sampling -/
#eval testable.check (∀ x : ℕ, 2 ∣ x → x < 100) { trace_discarded := tt }
-- discard
--  x := 1
-- discard
--  x := 41
-- discard
--  x := 3
-- discard
--  x := 5
-- discard
--  x := 5
-- discard
--  x := 197
-- discard
--  x := 469
-- discard
--  x := 9
-- discard

-- ===================
-- Found problems!

-- x := 552
-- -------------------

/- let us define a specialized sampling instance -/
instance {k : ℕ} : sampleable { x : ℕ // k ∣ x } :=
{ sample := do { n ← sample ℕ, pure ⟨k*n, dvd_mul_right _ _⟩ },
  shrink := λ ⟨x,h⟩, (λ y, ⟨k*y, dvd_mul_right _ _⟩) <$> shrink x }

#eval testable.check (∀ x : ℕ, 2 ∣ x → x < 100) { enable_tracing := tt }
-- ===================
-- Found problems!

-- x := 358
-- -------------------
```

Similarly, it is common to write properties of the form: `∀ i j, i ≤ j → ...`
as the following example show:

```lean
#eval check (∀ i j k : ℕ, j < k → i - k < i - j)
```

Without subtype instances, the above property discards many samples
because `j < k` does not hold. Fortunately, we have appropriate
instance to choose `k` intelligently.

## Main definitions
  * `testable` class
  * `testable.check`: a way to test a proposition using random examples

## Tags

random testing

## References

  * https://hackage.haskell.org/package/QuickCheck

-/

universes u v

variables var var' : string
variable α : Type u
variable β : α → Prop
variable f : Type → Prop

namespace slim_check

/-- Result of trying to disprove `p`

The constructors are:
  *  `success : (psum unit p) → test_result`
     succeed when we find another example satisfying `p`
     In `success h`, `h` is an optional proof of the proposition.
     Without the proof, all we know is that we found one example
     where `p` holds. With a proof, the one test was sufficient to
     prove that `p` holds and we do not need to keep finding examples.
   * `gave_up {} : ℕ → test_result`
     give up when a well-formed example cannot be generated.
     `gave_up n` tells us that `n` invalid examples were tried.
     Above 100, we give up on the proposition and report that we
     did not find a way to properly test it.
   * `failure : ¬ p → (list string) → ℕ → test_result`
     a counter-example to `p`; the strings specify values for the relevant variables.
     `failure h vs n` also carries a proof that `p` does not hold. This way, we can
     guarantee that there will be no false positive. The last component, `n`,
     is the number of times that the counter-example was shrunk.
-/
@[derive inhabited]
inductive test_result (p : Prop)
| success : (psum unit p) → test_result
| gave_up {} : ℕ → test_result
| failure : ¬ p → (list string) → ℕ → test_result

/-- format a `test_result` as a string. -/
protected def test_result.to_string {p} : test_result p → string
| (test_result.success (psum.inl ())) := "success (without proof)"
| (test_result.success (psum.inr h)) := "success (with proof)"
| (test_result.gave_up n) := sformat!"gave up {n} times"
| (test_result.failure a vs _) := sformat!"failed {vs}"


/-- configuration for testing a property -/
@[derive [has_reflect, inhabited]]
structure slim_check_cfg :=
(num_inst : ℕ                   := 100)  -- number of examples
(max_size : ℕ                   := 100)  -- final size argument
(trace_discarded : bool         := ff)   -- enable the printing out of discarded samples
(trace_success : bool           := ff)   -- enable the printing out of successful tests
(trace_shrink : bool            := ff)   -- enable the printing out of shrinking steps
(trace_shrink_candidates : bool := ff)   -- enable the printing out of shrinking candidates
(random_seed : option ℕ         := none) -- specify a seed to the random number generator to
                                         -- obtain a deterministic behavior
(quiet : bool                   := ff)   -- suppress success message when running `slim_check`

instance {p} : has_to_string (test_result p) := ⟨ test_result.to_string ⟩

/--
`printable_prop p` allows one to print a proposition so that
`slim_check` can indicate how values relate to each other.
-/
class printable_prop (p : Prop) :=
(print_prop : option string)

@[priority 100] -- see [note priority]
instance default_printable_prop {p} : printable_prop p :=
⟨ none ⟩

/-- `testable p` uses random examples to try to disprove `p`. -/
class testable (p : Prop) :=
(run [] (cfg : slim_check_cfg) (minimize : bool) : gen (test_result p))

open _root_.list

open test_result

/-- applicative combinator proof carrying test results -/
def combine {p q : Prop} : psum unit (p → q) → psum unit p → psum unit q
| (psum.inr f) (psum.inr x) := psum.inr (f x)
| _ _ := psum.inl ()

/-- Combine the test result for properties `p` and `q` to create a test for their conjunction. -/
def and_counter_example {p q : Prop} :
  test_result p →
  test_result q →
  test_result (p ∧ q)
| (failure Hce xs n) _ := failure (λ h, Hce h.1) xs n
| _ (failure Hce xs n) := failure (λ h, Hce h.2) xs n
| (success xs) (success ys) := success $ combine (combine (psum.inr and.intro) xs) ys
| (gave_up n) (gave_up m) := gave_up $ n + m
| (gave_up n) _ := gave_up n
| _ (gave_up n) := gave_up n

/-- Combine the test result for properties `p` and `q` to create a test for their disjunction -/
def or_counter_example {p q : Prop} :
  test_result p →
  test_result q →
  test_result (p ∨ q)
| (failure Hce xs n) (failure Hce' ys n') := failure (λ h, or_iff_not_and_not.1 h ⟨Hce, Hce'⟩)
  (xs ++ ys) (n + n')
| (success xs) _ := success $ combine (psum.inr or.inl) xs
| _ (success ys) := success $ combine (psum.inr or.inr) ys
| (gave_up n) (gave_up m) := gave_up $ n + m
| (gave_up n) _ := gave_up n
| _ (gave_up n) := gave_up n

/-- If `q → p`, then `¬ p → ¬ q` which means that testing `p` can allow us
to find counter-examples to `q`. -/
def convert_counter_example {p q : Prop}
  (h : q → p) :
  test_result p →
  opt_param (psum unit (p → q)) (psum.inl ()) →
  test_result q
| (failure Hce xs n) _ := failure (mt h Hce) xs n
| (success Hp) Hpq := success (combine Hpq Hp)
| (gave_up n) _ := gave_up n

/-- Test `q` by testing `p` and proving the equivalence between the two. -/
def convert_counter_example' {p q : Prop}
  (h : p ↔ q) (r : test_result p) :
  test_result q :=
convert_counter_example h.2 r (psum.inr h.1)

/-- When we assign a value to a universally quantified variable,
we record that value using this function so that our counter-examples
can be informative. -/
def add_to_counter_example (x : string) {p q : Prop}
  (h : q → p) :
  test_result p →
  opt_param (psum unit (p → q)) (psum.inl ()) →
  test_result q
| (failure Hce xs n) _ := failure (mt h Hce) (x :: xs) n
| r hpq := convert_counter_example h r hpq

/-- Add some formatting to the information recorded by `add_to_counter_example`. -/
def add_var_to_counter_example {γ : Type v} [has_repr γ]
  (var : string) (x : γ) {p q : Prop}
  (h : q → p) : test_result p →
  opt_param (psum unit (p → q)) (psum.inl ()) →
  test_result q :=
@add_to_counter_example (var ++ " := " ++ repr x) _ _ h

/-- Gadget used to introspect the name of bound variables.

It is used with the `testable` typeclass so that
`testable (named_binder "x" (∀ x, p x))` can use the variable name
of `x` in error messages displayed to the user. If we find that instantiating
the above quantifier with 3 falsifies it, we can print:

```
==============
Problem found!
==============
x := 3
```
 -/
@[simp, nolint unused_arguments]
def named_binder (n : string) (p : Prop) : Prop := p

/-- Is the given test result a failure? -/
def is_failure {p} : test_result p → bool
| (test_result.failure _ _ _) := tt
| _ := ff

instance and_testable (p q : Prop) [testable p] [testable q] :
  testable (p ∧ q) :=
⟨ λ cfg min, do
   xp ← testable.run p cfg min,
   xq ← testable.run q cfg min,
   pure $ and_counter_example xp xq ⟩

instance or_testable (p q : Prop) [testable p] [testable q] :
  testable (p ∨ q) :=
⟨ λ cfg min, do
   xp ← testable.run p cfg min,
   match xp with
   | success (psum.inl h) := pure $ success (psum.inl h)
   | success (psum.inr h) := pure $ success (psum.inr $ or.inl h)
   | _ := do
     xq ← testable.run q cfg min,
     pure $ or_counter_example xp xq
   end ⟩

instance iff_testable (p q : Prop) [testable ((p ∧ q) ∨ (¬ p ∧ ¬ q))] :
  testable (p ↔ q) :=
⟨ λ cfg min, do
   xp ← testable.run ((p ∧ q) ∨ (¬ p ∧ ¬ q)) cfg min,
   return $ convert_counter_example' (by tauto!) xp ⟩

open printable_prop

@[priority 1000]
instance dec_guard_testable (p : Prop) [printable_prop p] [decidable p] (β : p → Prop)
  [∀ h, testable (β h)] : testable (named_binder var $ Π h, β h) :=
⟨ λ cfg min, do
    if h : p
    then
      match print_prop p with
      | none := (λ r, convert_counter_example ($ h) r (psum.inr $ λ q _, q)) <$>
        testable.run (β h) cfg min
      | some str := (λ r, add_to_counter_example (sformat!"guard: {str}") ($ h) r
        (psum.inr $ λ q _, q)) <$> testable.run (β h) cfg min
      end
    else if cfg.trace_discarded ∨ cfg.trace_success then
      match print_prop p with
      | none := trace "discard" $ return $ gave_up 1
      | some str := trace sformat!"discard: {str} does not hold" $ return $ gave_up 1
      end
    else return $ gave_up 1 ⟩

/-- Type tag that replaces a type's `has_repr` instance with its `has_to_string` instance. -/
def use_has_to_string (α : Type*) := α

instance use_has_to_string.inhabited [I : inhabited α] : inhabited (use_has_to_string α) := I

/-- Add the type tag `use_has_to_string` to an expression's type. -/
def use_has_to_string.mk {α} (x : α) : use_has_to_string α := x

instance [has_to_string α] : has_repr (use_has_to_string α) :=
⟨ @to_string α _ ⟩

@[priority 2000]
instance all_types_testable [testable (f ℤ)] : testable (named_binder var $ Π x, f x) :=
⟨ λ cfg min, do
    r ← testable.run (f ℤ) cfg min,
    return $ add_var_to_counter_example var (use_has_to_string.mk "ℤ") ($ ℤ) r ⟩

/-- Trace the value of sampled variables if the sample is discarded. -/
def trace_if_giveup {p α β} [has_repr α] (tracing_enabled : bool) (var : string) (val : α) :
  test_result p → thunk β → β
| (test_result.gave_up _) :=
  if tracing_enabled then trace (sformat!" {var} := {repr val}")
  else ($ ())
| _ := ($ ())

/-- testable instance for a property iterating over the element of a list -/
@[priority 5000]
instance test_forall_in_list
  [∀ x, testable (β x)] [has_repr α] :
  Π xs : list α, testable (named_binder var $ ∀ x, named_binder var' $ x ∈ xs → β x)
| [] := ⟨ λ tracing min, return $ success $ psum.inr (by { introv x h, cases h} ) ⟩
| (x :: xs) :=
⟨ λ cfg min, do
    r ← testable.run (β x) cfg min,
    trace_if_giveup cfg.trace_discarded var x r $
      match r with
      | failure _ _ _ := return $ add_var_to_counter_example var x
                                 (by { intro h, apply h, left, refl }) r
      | success hp := do
         rs ← @testable.run _ (test_forall_in_list xs) cfg min,
         return $ convert_counter_example
                                 (by { intros h i h',
                                       apply h,
                                       right, apply h' })
                                 rs
                                 (combine (psum.inr
                                  $ by { intros j h, simp only [ball_cons, named_binder],
                                         split ; assumption, } ) hp)
      | gave_up n := do
         rs ← @testable.run _ (test_forall_in_list xs) cfg min,
         match rs with
         | (success _) := return $ gave_up n
         | (failure Hce xs n) := return $ failure
                      (by { simp only [ball_cons, named_binder],
                            apply not_and_of_not_right _ Hce, }) xs n
         | (gave_up n') := return $ gave_up (n + n')
         end
      end ⟩

/-- Test proposition `p` by randomly selecting one of the provided
testable instances. -/
def combine_testable (p : Prop)
  (t : list $ testable p) (h : 0 < t.length) : testable p :=
⟨ λ cfg min, have 0 < length (map (λ t, @testable.run _ t cfg min) t),
    by { rw [length_map], apply h },
  gen.one_of (list.map (λ t, @testable.run _ t cfg min) t) this ⟩

open sampleable_ext

/--
Format the counter-examples found in a test failure.
-/
def format_failure (s : string) (xs : list string) (n : ℕ) : string :=
let counter_ex := string.intercalate "\n" xs in
sformat!"
===================
{s}

{counter_ex}
({n} shrinks)
-------------------
"

/--
Format the counter-examples found in a test failure.
-/
def format_failure' (s : string) {p} : test_result p → string
| (success a) := ""
| (gave_up a) := ""
| (test_result.failure _ xs n) := format_failure s xs n

/--
Increase the number of shrinking steps in a test result.
-/
def add_shrinks {p} (n : ℕ) : test_result p → test_result p
| r@(success a) := r
| r@(gave_up a) := r
| (test_result.failure h vs n') := test_result.failure h vs $ n + n'

/-- Shrink a counter-example `x` by using `shrink x`, picking the first
candidate that falsifies a property and recursively shrinking that one.

The process is guaranteed to terminate because `shrink x` produces
a proof that all the values it produces are smaller (according to `sizeof`)
than `x`. -/
def minimize_aux [sampleable_ext α] [∀ x, testable (β x)] (cfg : slim_check_cfg) (var : string) :
  proxy_repr α → ℕ → option_t gen (Σ x, test_result (β (interp α x))) :=
well_founded.fix has_well_founded.wf $ λ x f_rec n, do
  if cfg.trace_shrink_candidates
    then return $ trace sformat!
      "candidates for {var} :=\n{repr (sampleable_ext.shrink x).to_list}\n" ()
    else pure (),
  ⟨y,r,⟨h₁⟩⟩ ← (sampleable_ext.shrink x).mfirst (λ ⟨a,h⟩, do
    ⟨r⟩ ← monad_lift (uliftable.up $ testable.run (β (interp α a)) cfg tt
      : gen (ulift $ test_result $ β $ interp α a)),
    if is_failure r
      then pure (⟨a, r, ⟨h⟩⟩ : (Σ a, test_result (β (interp α a)) × plift (sizeof_lt a x)))
      else failure),
  if cfg.trace_shrink then return $
    trace (sformat!"{var} := {repr y}" ++ format_failure' "Shrink counter-example:" r) ()
    else pure (),
  f_rec y h₁ (n+1) <|> pure ⟨y,add_shrinks (n+1) r⟩

/-- Once a property fails to hold on an example, look for smaller counter-examples
to show the user. -/
def minimize [sampleable_ext α] [∀ x, testable (β x)] (cfg : slim_check_cfg) (var : string)
  (x : proxy_repr α) (r : test_result (β (interp α x))) :
  gen (Σ x, test_result (β (interp α x))) := do
if cfg.trace_shrink then return $
  trace (sformat!"{var} := {repr x}" ++ format_failure' "Shrink counter-example:" r) ()
  else pure (),
x' ← option_t.run $ minimize_aux α _ cfg var x 0,
pure $ x'.get_or_else ⟨x, r⟩

@[priority 2000]
instance exists_testable (p : Prop)
  [testable (named_binder var (∀ x, named_binder var' $ β x → p))] :
  testable (named_binder var' (named_binder var (∃ x, β x) → p)) :=
⟨ λ cfg min, do
    x ← testable.run (named_binder var (∀ x, named_binder var' $ β x → p)) cfg min,
    pure $ convert_counter_example' exists_imp_distrib.symm x ⟩

/-- Test a universal property by creating a sample of the right type and instantiating the
bound variable with it -/
instance var_testable [sampleable_ext α] [∀ x, testable (β x)] :
  testable (named_binder var $ Π x : α, β x) :=
⟨ λ cfg min, do
   uliftable.adapt_down (sampleable_ext.sample α) $
   λ x, do
     r ← testable.run (β (sampleable_ext.interp α x)) cfg ff,
     uliftable.adapt_down (if is_failure r ∧ min
                          then minimize _ _ cfg var x r
                          else if cfg.trace_success
                          then trace (sformat!"  {var} := {repr x}") $ pure ⟨x,r⟩
                          else pure ⟨x,r⟩) $
     λ ⟨x,r⟩, return $ trace_if_giveup cfg.trace_discarded var x r (add_var_to_counter_example var x
      ($ sampleable_ext.interp α x) r) ⟩


/-- Test a universal property about propositions -/
instance prop_var_testable (β : Prop → Prop) [I : ∀ b : bool, testable (β b)] :
  testable (named_binder var $ Π p : Prop, β p) :=
⟨λ cfg min, do
  convert_counter_example (λ h (b : bool), h b) <$> @testable.run
    (named_binder var $ Π b : bool, β b) _ cfg min⟩

@[priority 3000]
instance unused_var_testable (β) [inhabited α] [testable β] :
  testable (named_binder var $ Π x : α, β) :=
⟨ λ cfg min, do
  r ← testable.run β cfg min,
  pure $ convert_counter_example ($ default) r (psum.inr $ λ x _, x) ⟩

@[priority 2000]
instance subtype_var_testable {p : α → Prop}
  [∀ x, printable_prop (p x)]
  [∀ x, testable (β x)]
  [I : sampleable_ext (subtype p)]  :
  testable (named_binder var $ Π x : α, named_binder var' $ p x → β x) :=
⟨ λ cfg min,
   do let test (x : subtype p) : testable (β x) :=
          ⟨ λ cfg min, do
              r ← testable.run (β x.val) cfg min,
              match print_prop (p x) with
              | none := pure r
              | some str := pure $ add_to_counter_example sformat!"guard: {str} (by construction)"
                id r (psum.inr id)
              end ⟩,
      r ← @testable.run (∀ x : subtype p, β x.val) (@slim_check.var_testable var _ _ I test) cfg
        min,
      pure $ convert_counter_example'
                 ⟨λ (h : ∀ x : subtype p, β x) x h', h ⟨x,h'⟩,
                  λ h ⟨x,h'⟩, h x h'⟩
                 r ⟩

@[priority 100]
instance decidable_testable (p : Prop) [printable_prop p] [decidable p] : testable p :=
⟨ λ cfg min, return $
  if h : p then success (psum.inr h)
  else
    match print_prop p with
    | none := failure h [] 0
    | some str := failure h [sformat!"issue: {str} does not hold"] 0
    end ⟩

instance eq.printable_prop {α} [has_repr α] (x y : α) : printable_prop (x = y) :=
⟨ some sformat!"{repr x} = {repr y}" ⟩

instance ne.printable_prop {α} [has_repr α] (x y : α) : printable_prop (x ≠ y) :=
⟨ some sformat!"{repr x} ≠ {repr y}" ⟩

instance le.printable_prop {α} [has_le α] [has_repr α] (x y : α) : printable_prop (x ≤ y) :=
⟨ some sformat!"{repr x} ≤ {repr y}" ⟩

instance lt.printable_prop {α} [has_lt α] [has_repr α] (x y : α) : printable_prop (x < y) :=
⟨ some sformat!"{repr x} < {repr y}" ⟩

instance perm.printable_prop {α} [has_repr α] (xs ys : list α) : printable_prop (xs ~ ys) :=
⟨ some sformat!"{repr xs} ~ {repr ys}" ⟩

instance and.printable_prop (x y : Prop) [printable_prop x] [printable_prop y] :
  printable_prop (x ∧ y) :=
⟨ do x' ← print_prop x,
    y' ← print_prop y,
    some sformat!"({x'} ∧ {y'})" ⟩

instance or.printable_prop (x y : Prop) [printable_prop x] [printable_prop y] :
  printable_prop (x ∨ y) :=
⟨ do x' ← print_prop x,
    y' ← print_prop y,
    some sformat!"({x'} ∨ {y'})" ⟩

instance iff.printable_prop (x y : Prop) [printable_prop x] [printable_prop y] :
  printable_prop (x ↔ y) :=
⟨ do x' ← print_prop x,
    y' ← print_prop y,
    some sformat!"({x'} ↔ {y'})" ⟩

instance imp.printable_prop (x y : Prop) [printable_prop x] [printable_prop y] :
  printable_prop (x → y) :=
⟨ do x' ← print_prop x,
    y' ← print_prop y,
    some sformat!"({x'} → {y'})" ⟩

instance not.printable_prop (x : Prop) [printable_prop x] : printable_prop (¬ x) :=
⟨ do x' ← print_prop x,
    some sformat!"¬ {x'}" ⟩

instance true.printable_prop : printable_prop true :=
⟨ some "true" ⟩

instance false.printable_prop : printable_prop false :=
⟨ some "false" ⟩

instance bool.printable_prop (b : bool) : printable_prop b :=
⟨ some $ if b then "true" else "false" ⟩

section io

open _root_.nat
variable {p : Prop}

/-- Execute `cmd` and repeat every time the result is `gave_up` (at most
`n` times). -/
def retry (cmd : rand (test_result p)) : ℕ → rand (test_result p)
| 0 := return $ gave_up 1
| (succ n) := do
r ← cmd,
match r with
| success hp := return $ success hp
| (failure Hce xs n) := return (failure Hce xs n)
| (gave_up _) := retry n
end

/-- Count the number of times the test procedure gave up. -/
def give_up (x : ℕ) : test_result p → test_result p
| (success (psum.inl ())) := gave_up x
| (success (psum.inr p))  := success (psum.inr p)
| (gave_up n) := gave_up (n+x)
| (failure Hce xs n) := failure Hce xs n

variable (p)

variable [testable p]

/-- Try `n` times to find a counter-example for `p`. -/
def testable.run_suite_aux (cfg : slim_check_cfg) : test_result p → ℕ → rand (test_result p)
| r 0 := return r
| r (succ n) :=
do let size := (cfg.num_inst - n - 1) * cfg.max_size / cfg.num_inst,
   when cfg.trace_success $ return $ trace sformat!"[slim_check: sample]" (),
   x ← retry ( (testable.run p cfg tt).run ⟨ size ⟩) 10,
   match x with
   | (success (psum.inl ())) := testable.run_suite_aux r n
   | (success (psum.inr Hp)) := return $ success (psum.inr Hp)
   | (failure Hce xs n) := return (failure Hce xs n)
   | (gave_up g) := testable.run_suite_aux (give_up g r) n
   end

/-- Try to find a counter-example of `p`. -/
def testable.run_suite (cfg : slim_check_cfg := {}) : rand (test_result p) :=
testable.run_suite_aux p cfg (success $ psum.inl ()) cfg.num_inst

/-- Run a test suite for `p` in `io`. -/
def testable.check' (cfg : slim_check_cfg := {}) : io (test_result p) :=
match cfg.random_seed with
| some seed := io.run_rand_with seed (testable.run_suite p cfg)
| none := io.run_rand (testable.run_suite p cfg)
end

namespace tactic

open _root_.tactic expr

/-!
## Decorations

Instances of `testable` use `named_binder` as a decoration on
propositions in order to access the name of bound variables, as in
`named_binder "x" (forall x, x < y)`.  This helps the
`testable` instances create useful error messages where variables
are matched with values that falsify a given proposition.

The following functions help support the gadget so that the user does
not have to put them in themselves.
-/

/-- `add_existential_decorations p` adds `a `named_binder` annotation at the
root of `p` if `p` is an existential quantification. -/
meta def add_existential_decorations : expr → expr
| e@`(@Exists %%α %%(lam n bi d b)) :=
  let n := to_string n in
  const ``named_binder [] (`(n) : expr) e
| e := e

/-- Traverse the syntax of a proposition to find universal quantifiers
and existential quantifiers and add `named_binder` annotations next to
them. -/
meta def add_decorations : expr → expr | e :=
e.replace $ λ e _,
  match e with
  | (pi n bi d b) :=
    let n := to_string n in
    some $ const ``named_binder [] (`(n) : expr)
      (pi n bi (add_existential_decorations d) (add_decorations b))
  | e := none
  end

/-- `decorations_of p` is used as a hint to `mk_decorations` to specify
that the goal should be satisfied with a proposition equivalent to `p`
with added annotations. -/
@[reducible, nolint unused_arguments]
def decorations_of (p : Prop) := Prop

/-- In a goal of the shape `⊢ tactic.decorations_of p`, `mk_decoration` examines
the syntax of `p` and add `named_binder` around universal quantifications and
existential quantifications to improve error messages.

This tool can be used in the declaration of a function as follows:

```lean
def foo (p : Prop) (p' : tactic.decorations_of p . mk_decorations) [testable p'] : ...
```

`p` is the parameter given by the user, `p'` is an equivalent proposition where
the quantifiers are annotated with `named_binder`.
-/
meta def mk_decorations : tactic unit := do
`(tactic.decorations_of %%p) ← target,
exact $ add_decorations p

end tactic

/-- Run a test suite for `p` and return true or false: should we believe that `p` holds? -/
def testable.check (p : Prop) (cfg : slim_check_cfg := {})
  (p' : tactic.decorations_of p . tactic.mk_decorations) [testable p'] : io punit := do
x ← match cfg.random_seed with
    | some seed := io.run_rand_with seed (testable.run_suite p' cfg)
    | none := io.run_rand (testable.run_suite p' cfg)
    end,
match x with
| (success _) := when (¬ cfg.quiet) $ io.put_str_ln "Success"
| (gave_up n) := io.fail sformat!"Gave up {repr n} times"
| (failure _ xs n) := do
  io.fail $ format_failure "Found problems!" xs n
end

end io

end slim_check
