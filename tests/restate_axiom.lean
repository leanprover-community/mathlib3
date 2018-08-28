import tactic.restate_axiom

open tactic

structure A :=
(x : ℕ)
(a' : x = 1 . skip)
(b : x = 2 . skip)

restate_axiom A.a'
example (z : A) : z.x = 1 := begin success_if_fail { rw A.a' }, rw A.a end

restate_axiom A.b f
example (z : A) : z.x = 2 := by rw A.f

restate_axiom A.b
example (z : A) : z.x = 2 := by rw A.b_lemma
