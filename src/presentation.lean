import measure_theory.constructions.polish
import analysis.calculus.specific_functions

/-!
# My beautiful introduction to typeclasses

-/

noncomputable theory

/- Typeclasses are a device to register some kinds of structures on some types. The types are
unbundled, but the system has a way to look automatically for these structures, so that no input
is needed from the user. -/

lemma aux1 : continuous (λ (z : ℂ), real.exp (complex.abs z)) :=
by continuity
--?

#print continuous
/- structure continuous : Π {α : Type u_1} {β : Type u_2} [topological_space α]
  [topological_space β], (α → β) → Prop
the fields between square brackets [topological_space α] and [topological_space β] are filled
automatically by the system
-/

/- We can check that the system knows how to find a topology by the command `by apply_instance`,
which means: please, Lean, fetch my an instance of what I am asking for. -/
def foo : topological_space ℝ := by apply_instance

/- Checking which instance has been found by Lean is not that instructive: -/
#print foo
/- uniform_space.to_topological_space -/
#print uniform_space.to_topological_space
/-
@[instance, priority 100, reducible]
def uniform_space.to_topological_space : Π {α : Type u} [uniform_space α], topological_space α
This means that Lean has found a uniform_space instance on ℝ, and deduced a topological_space
instance from it. The uniform space instance is again found by instance search. There is a
(possibly complicated) recursion going on here.
-/

/- One can see the full shape of the topologies found by Lean by printing the details of aux1. -/
set_option pp.all true
#check aux1
set_option pp.all false
/-
@continuous.{0 0} complex real
    (@uniform_space.to_topological_space.{0} complex
       (@metric_space.to_uniform_space'.{0} complex
          (@semi_normed_ring.to_pseudo_metric_space.{0} complex
             (@semi_normed_comm_ring.to_semi_normed_ring.{0} complex
                (@normed_comm_ring.to_semi_normed_comm_ring.{0} complex
                   (@normed_field.to_normed_comm_ring.{0} complex complex.normed_field))))))
    (@uniform_space.to_topological_space.{0} real (@metric_space.to_uniform_space'.{0} real real.pseudo_metric_space))
    (λ (z : complex), real.exp (complex.abs z))
-/

/- Even better (or worse), one can follow all the tries made by Lean while looking for these
instances (including the failed ones) -/

set_option trace.class_instances true
example : topological_space ℂ := by apply_instance
set_option trace.class_instances false
/- In this case, it's not so bad, but in complicated situations it can get very long. -/


/-
Linters
Type synonyms (weak topology)
Trouver un exemple vraiment compliqué
Cache, haveI et letI
Parler des espaces polonais, et dire que c'est possible de faire sans avec @ (même si c'est
clairement plus fastidieux).
-/
