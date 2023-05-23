/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth
-/
import analysis.normed.group.basic

/-!
# Negation on spheres and balls

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define `has_involutive_neg` instances for spheres, open balls, and closed balls in a
semi normed group.
-/

open metric set

variables {E : Type*} [seminormed_add_comm_group E] {r : ℝ}

/-- We equip the sphere, in a seminormed group, with a formal operation of negation, namely the
antipodal map. -/
instance : has_involutive_neg (sphere (0 : E) r) :=
{ neg := subtype.map has_neg.neg $ λ w, by simp,
  neg_neg := λ x, subtype.ext $ neg_neg x }

@[simp] lemma coe_neg_sphere {r : ℝ} (v : sphere (0 : E) r) :
  ↑(-v) = (-v : E) :=
rfl

instance : has_continuous_neg (sphere (0 : E) r) := ⟨continuous_neg.subtype_map _⟩

/-- We equip the ball, in a seminormed group, with a formal operation of negation, namely the
antipodal map. -/
instance {r : ℝ} : has_involutive_neg (ball (0 : E) r) :=
{ neg := subtype.map has_neg.neg $ λ w, by simp,
  neg_neg := λ x, subtype.ext $ neg_neg x }

@[simp] lemma coe_neg_ball {r : ℝ} (v : ball (0 : E) r) :
  ↑(-v) = (-v : E) :=
rfl

instance : has_continuous_neg (ball (0 : E) r) := ⟨continuous_neg.subtype_map _⟩

/-- We equip the closed ball, in a seminormed group, with a formal operation of negation, namely the
antipodal map. -/
instance {r : ℝ} : has_involutive_neg (closed_ball (0 : E) r) :=
{ neg := subtype.map has_neg.neg $ λ w, by simp,
  neg_neg := λ x, subtype.ext $ neg_neg x }

@[simp] lemma coe_neg_closed_ball {r : ℝ} (v : closed_ball (0 : E) r) :
  ↑(-v) = (-v : E) :=
rfl

instance : has_continuous_neg (closed_ball (0 : E) r) := ⟨continuous_neg.subtype_map _⟩
