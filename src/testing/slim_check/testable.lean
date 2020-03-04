
import testing.slim_check.arbitrary

universes u v

variable α : Type u
variable β : α → Prop
variable f : Type → Prop

namespace slim_check

inductive test_result (p : Prop)
| success : (psum unit p) → test_result
| gave_up {} : ℕ → test_result
| failure : ¬ p → (list string) → test_result

class testable (p : Prop) :=
(run (minimize : bool) : gen (test_result p)) --

open list

open test_result

def combine {p q : Prop} : psum unit (p → q) → psum unit p → psum unit q
 | (psum.inr f) (psum.inr x) := psum.inr (f x)
 | _ _ := psum.inl ()

def convert_counter_example {p q : Prop}
  (h : q → p)
: test_result p →
  opt_param (psum unit (p → q)) (psum.inl ()) →
  test_result q
 | (failure Hce xs) _ := failure (mt h Hce) xs
 | (success Hp) Hpq := success (combine Hpq Hp)
 | (gave_up n) _ := gave_up n

def add_to_counter_example (x : string) {p q : Prop}
  (h : q → p)
: test_result p →
  opt_param (psum unit (p → q)) (psum.inl ()) →
  test_result q
 | (failure Hce xs) _ := failure (mt h Hce) $ x :: xs
 | r hpq := convert_counter_example h r hpq

def add_var_to_counter_example {γ : Type v} [has_to_string γ]
  (var : string) (x : γ) {p q : Prop}
  (h : q → p)
: test_result p →
  opt_param (psum unit (p → q)) (psum.inl ()) →
  test_result q :=
@add_to_counter_example (var ++ " := " ++ to_string x) _ _ h

instance imp_dec_testable (p : Prop) [decidable p] (β : p → Prop)
  [∀ h, testable (β h)]
: testable (Π h, β h) :=
⟨ λ min, do
    if h : p
    then (λ r, convert_counter_example ($ h) r (psum.inr $ λ q _, q)) <$> testable.run (β h) min
    else return $ gave_up 1 ⟩

instance all_types_testable [testable (f ℤ)]
: testable (Π x, f x) :=
⟨ λ min, do
    r ← testable.run (f ℤ) min,
    return $ add_to_counter_example "ℤ" ($ ℤ) r ⟩

def test_one (x : α) [testable (β x)] (var : option (string × string) := none)
: testable (Π x, β x) :=
⟨ λ min, do
    r ← testable.run (β x) min,
    return $ match var with
     | none := convert_counter_example ($ x) r
     | (some (v,x_str)) := add_var_to_counter_example v x_str ($ x) r
    end ⟩

def test_forall_in_list (var : string) [∀ x, testable (β x)] [has_to_string α]
: Π xs : list α, testable (∀ x, x ∈ xs → β x)
 | [] := ⟨ λ min, return $ success $ psum.inr (by { introv h, cases h} ) ⟩
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
                                $ by { intros j h, simp only [ball_cons],
                                       split ; assumption, } ) hp)
     | gave_up n := do
       rs ← @testable.run _ (test_forall_in_list xs) min,
       match rs with
        | (success _) := return $ gave_up n
        | (failure Hce xs) := return $ failure
                    (by { simp only [ball_cons],
                          apply not_and_of_not_right _ Hce, }) xs
        | (gave_up n') := return $ gave_up (n + n')
       end
    end ⟩

def combine_testable (p : Prop)
  (t : list $ testable p) (h : 0 < t.length)
: testable p :=
⟨ λ min, have 0 < length (map (λ t, @testable.run _ t min) t),
    by { rw [length_map], apply h },
  one_of (list.map (λ t, @testable.run _ t min) t) this ⟩

def is_failure {p} : test_result p → bool
| (test_result.failure _ _) := tt
| _ := ff

def minimize [∀ x, testable (β x)] (x : α) (r : test_result (β x)) : lazy_list α → gen (Σ x, test_result (β x))
| lazy_list.nil := pure ⟨x,r⟩
| (lazy_list.cons x xs) := do
  ⟨r⟩ ← liftable.up' $ testable.run (β x) tt,
     if is_failure r
       then pure ⟨x, convert_counter_example id r (psum.inl ())⟩
       else minimize $ xs ()

def var_testable [has_to_string α] [arbitrary α] [∀ x, testable (β x)]
  (var : option string := none)
: testable (Π x : α, β x) :=
⟨ λ min, liftable.down' $ do
  x ← arby α,
  (do
    ⟨r⟩ ← liftable.up' $ testable.run (β x) ff,
    ⟨x,r⟩ ← if is_failure r ∧ min then minimize _ _ x r (shrink x) else pure ⟨x,r⟩,
    return ⟨match var with
     | none := add_to_counter_example (to_string x) ($ x) r
     | (some v) := add_var_to_counter_example v x ($ x) r
    end⟩) ⟩

instance pi_testable [has_to_string α] [arbitrary α] [∀ x, testable (β x)]
: testable (Π x : α, β x) :=
var_testable α β

instance de_testable {p : Prop} [decidable p] : testable p :=
⟨ λ min, return $ if h : p then success (psum.inr h) else failure h [] ⟩

section io

variable (p : Prop)
variable [testable p]

open nat

variable {p}

def retry (cmd : rand (test_result p)) : ℕ → rand (test_result p)
 | 0 := return $ gave_up 1
 | (succ n) := do
r ← cmd,
match r with
 | success hp := return $ success hp
 | (failure Hce xs) := return (failure Hce xs)
 | (gave_up _) := retry n
end

def give_up_once (x : ℕ) : test_result p → test_result p
 | (success (psum.inl ())) := gave_up x
 | (success (psum.inr p))  := success (psum.inr p)
 | (gave_up n) := gave_up (n+x)
 | (failure Hce xs) := failure Hce xs

variable (p)

def testable.run_suite_aux (bound : ℕ) : test_result p → ℕ → rand (test_result p)
 | r 0 := return r
 | r (succ n) :=
do x ← retry ( (testable.run p tt).run ⟨ (bound - n - 1) ⟩) 10,
   match x with
    | (success (psum.inl ())) := testable.run_suite_aux r n
    | (success (psum.inr Hp)) := return $ success (psum.inr Hp)
    | (failure Hce xs) := return (failure Hce xs)
    | (gave_up g) := testable.run_suite_aux (give_up_once g r) n
   end

def testable.run_suite (bound : ℕ := 100) :=
testable.run_suite_aux p bound (success $ psum.inl ()) (2*bound)

def testable.check (bound : ℕ := 100) : io (test_result p) :=
io.run_rand (testable.run_suite p bound)

def testable.check' (bound : ℕ := 100) : io bool := do
x ← io.run_rand (testable.run_suite p bound),
match x with
 | (success _) := return tt
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
