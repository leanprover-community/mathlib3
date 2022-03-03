import measure_theory.function.jacobian
import analysis.normed_space.weak_dual

/-!
# Topology with and without typeclasses
-/

noncomputable theory
open topological_space
variable {α : Type*}

/-! ### Topologies through typeclasses -/

/- Typeclasses are a device to register some kinds of structures on some types. The types are
unbundled, but the system has a way to look automatically for these structures, so that no input
is needed from the user.

cf. typeclasses in Isabelle/HOL, typeclasses or canonical classes in coq
-/

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

/- The main hierarchy contains topological spaces, metric spaces, normed spaces and a few extension
of these. -/
example {E : Type} {h : normed_group E} : topological_space E := by apply_instance

/- Many additional properties of the topology are additional typeclasses, that don't bring new
data. -/

#check t2_space
-- Π (α : Type u_1) [_inst_2 : topological_space α], Prop

/- They can also be found automatically by instance search -/

example {E : Type*} {h : metric_space E} : t2_space E := by apply_instance

/- Here is a nontrival example, mixing topology and linear algebra. -/
set_option trace.class_instances true

example {E : Type*} [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E] :
  complete_space (ℝ →L[ℝ] E) :=
by apply_instance

set_option trace.class_instances false

/-- Sometimes, Lean needs some help -/
example {𝕜 : Type*} [nondiscrete_normed_field 𝕜] [complete_space 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] [finite_dimensional 𝕜 E] :
  complete_space (𝕜 →L[𝕜] E) :=
begin
  -- haveI : complete_space E := finite_dimensional.complete 𝕜 E,
  /- `haveI` is here for performance reasons, with caching -/
  apply_instance
end

/- One needs some discipline to avoid performance problems:
* adjust priorities of some instance
* avoid loops
* avoid instances that take too long to be found

Ensured by linters that check the whole library at every PR.
Should be dramatically improved in Lean 4.
-/

/-! ### Type synonyms -/

/- Sometimes, one wants to put several topologies on a single type.

Example: the dual of a normed real vector space has:
* the norm topology
* the weak-* topology

If one registers two different topologies on the same type, instance search will find randomly
one or the other.

Solution: type synonyms. Instance search does not unfold the types unless a specific attribute is
set, so it won't get confused
-/

/-- A copy of a type, endowed with the discrete topology -/
def discrete_copy (α : Type) : Type := α

instance {α : Type} : topological_space (discrete_copy α) := ⊥
instance {α : Type} : discrete_topology (discrete_copy α) := ⟨rfl⟩

set_option pp.all true

example : continuous (λ (x : discrete_copy ℝ), (id x : ℝ)) :=
begin
  rw continuous_def,
  assume s hs,
  exact is_open_discrete _,
end

set_option pp.all false


#check weak_dual


/-!
### Polish spaces

99% of the time, the maths fit well with the picture "one type / one natural topology".
1% of the time, it gets messy
-/

namespace fake_copy

/-- A Polish space is a topological space with second countable topology, that can be endowed
with a metric for which it is complete.
We register an instance from complete second countable metric space to polish space, and not the
other way around as this is the most common use case.

To endow a Polish space with a complete metric space structure, use
```
letI : metric_space α := polish_space_metric α,
haveI : complete_space α := complete_polish_space_metric α,
haveI : second_countable_topology α := polish_space.second_countable α,
```
-/
class polish_space (α : Type*) [h : topological_space α] : Prop :=
(second_countable [] : second_countable_topology α)
(complete : ∃ m : metric_space α, m.to_uniform_space.to_topological_space = h ∧
  @complete_space α m.to_uniform_space)

@[priority 100]
instance polish_space_of_complete_second_countable
  [m : metric_space α] [h : second_countable_topology α] [h' : complete_space α] :
  polish_space α :=
{ second_countable := h,
  complete := ⟨m, rfl, h'⟩ }

/-- Construct on a Polish space a metric (compatible with the topology) which is complete. -/
def polish_space_metric (α : Type*) [ht : topological_space α] [h : polish_space α] :
  metric_space α :=
h.complete.some.replace_topology h.complete.some_spec.1.symm

lemma complete_polish_space_metric (α : Type*) [ht : topological_space α] [h : polish_space α] :
  @complete_space α (polish_space_metric α).to_uniform_space :=
begin
  convert h.complete.some_spec.2,
  exact metric_space.replace_topology_eq _ _
end

/-- A set in a topological space is clopenable if there exists a finer Polish topology for which
this set is open and closed. It turns out that this notion is equivalent to being Borel-measurable,
but this is nontrivial (see `is_clopenable_iff_measurable_set`). -/
def is_clopenable [t : topological_space α] (s : set α) : Prop :=
∃ (t' : topological_space α), t' ≤ t ∧ @polish_space α t' ∧ @is_closed α t' s ∧ @is_open α t' s

/- Things get more painful than usually, but are still possible to do using `@` versions,
desactivating typeclass inference and making it possible to do everything by hand. -/

#check is_closed.is_clopenable

#check polish_space.exists_polish_space_forall_le

#check measurable_set.image_of_continuous_on_inj_on

#check measure_theory.integral_image_eq_integral_abs_det_fderiv_smul

end fake_copy
