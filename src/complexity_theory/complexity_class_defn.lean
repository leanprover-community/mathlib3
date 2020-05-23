import data.equiv.denumerable
import tactic

universe u
noncomputable theory

-- for now we're using total functions

namespace complexity

variables (I O : Type u) [encodable I] [encodable O]
open encodable

structure algorithm :=
(machine : Type u)
(eval : I → O)
(runtime : I → ℕ)
-- M.runtime i ≤ k should be read as
-- M halts on input i in at most k steps
(runspace : I → ℕ)

variables {I O}

-- encode i ≤ 2^n should be read as 
-- i is representable with n bits
def time_bound (M : algorithm I O) (bound : ℕ → ℕ) : Prop :=
∀ i n, encode i ≤ 2^n → M.runtime i ≤ bound n

def space_bound (M : algorithm I O) (bound : ℕ → ℕ) : Prop :=
∀ i n, encode i ≤ 2^n → M.runtime i ≤ bound n

-- if an algorithm runs in time at most f, then it also runs in space at most f
theorem time_le_space (M : algorithm I O) (f : ℕ → ℕ) :
time_bound M f → space_bound M f  := sorry

-- if an algorithm runs in space at most f, then it also runs in time at most 2^f
theorem space_le_exp_of_time (M : algorithm I O) (f : ℕ → ℕ) :
space_bound M f → time_bound M (λ x, 2^(f x)) := sorry


structure decision_problem := 
(domain : Type u) --[encodable domain]
(domain_encoding : encodable domain)
(problem : domain → bool)

#check decision_problem

structure promise_problem := 
(domain : Type u)
(domain_encoding : encodable domain)
(problem : domain →. bool)

-- todo: redefine decision_problem so that it's a promise_problem that happens to be total

structure complexity_class := 
(problems : set decision_problem)


-- im going to worry about function classes later, since I don't have a good guess about what API i will need. It should be easy to define the lift from classes of decision problems to classes of function problems. 