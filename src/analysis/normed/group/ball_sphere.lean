import analysis.normed.group.basic

/-!
# Negation on spheres and balls

In this file we define `has_involutive_neg` instances for spheres, open balls, and closed balls in a
semi normed group.
-/

open metric set

variables {E : Type*} [semi_normed_group E]

/-- We equip the sphere, in a seminormed group, with a formal operation of negation, namely the
antipodal map. -/
instance {r : ℝ} : has_involutive_neg (sphere (0 : E) r) :=
{ neg := λ w, ⟨-↑w, by simp⟩,
  neg_neg := λ x, subtype.ext $ neg_neg x }

@[simp] lemma coe_neg_sphere {r : ℝ} (v : sphere (0 : E) r) :
  (((-v) : sphere _ _) : E) = - (v:E) :=
rfl

/-- We equip the ball, in a seminormed group, with a formal operation of negation, namely the
antipodal map. -/
instance {r : ℝ} : has_involutive_neg (ball (0 : E) r) :=
{ neg := λ w, ⟨-↑w, by simpa using w.coe_prop⟩,
  neg_neg := λ x, subtype.ext $ neg_neg x }

@[simp] lemma coe_neg_ball {r : ℝ} (v : ball (0 : E) r) :
  (((-v) : ball _ _) : E) = - (v:E) :=
rfl

/-- We equip the closed ball, in a seminormed group, with a formal operation of negation, namely the
antipodal map. -/
instance {r : ℝ} : has_involutive_neg (closed_ball (0 : E) r) :=
{ neg := λ w, ⟨-↑w, by simpa using w.coe_prop⟩,
  neg_neg := λ x, subtype.ext $ neg_neg x }

@[simp] lemma coe_neg_closed_ball {r : ℝ} (v : closed_ball (0 : E) r) :
  (((-v) : closed_ball _ _) : E) = - (v:E) :=
rfl


