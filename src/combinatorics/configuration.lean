/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import combinatorics.hall.basic
import data.fintype.card

/-!
# Configurations of Points and lines
This file introduces abstract configurations of points and lines, and proves some basic properties.

## Main definitions
* `configuration.nondegenerate`: Excludes certain degenerate configurations,
  and imposes uniqueness of intersection points.
* `configuration.has_points`: A nondegenerate configuration in which
  every pair of lines has an intersection point.
* `configuration.has_lines`:  A nondegenerate configuration in which
  every pair of points has a line through them.

## Todo
* Abstract projective planes.
-/

namespace configuration

universe u

variables (P L : Type u) [has_mem P L]

/-- A type synonym. -/
def dual := P

instance [this : inhabited P] : inhabited (dual P) := this

instance : has_mem (dual L) (dual P) :=
⟨function.swap (has_mem.mem : P → L → Prop)⟩

/-- A configuration is nondegenerate if:
  1) there does not exist a line that passes through all of the points,
  2) there does not exist a point that is on all of the lines,
  3) there is at most one line through any two points,
  4) any two lines have at most one intersection point.
  Conditions 3 and 4 are equivalent. -/
class nondegenerate : Prop :=
(exists_point : ∀ l : L, ∃ p, p ∉ l)
(exists_line : ∀ p, ∃ l : L, p ∉ l)
(eq_or_eq : ∀ {p₁ p₂ : P} {l₁ l₂ : L}, p₁ ∈ l₁ → p₂ ∈ l₁ → p₁ ∈ l₂ → p₂ ∈ l₂ → p₁ = p₂ ∨ l₁ = l₂)

/-- A nondegenerate configuration in which every pair of lines has an intersection point. -/
class has_points extends nondegenerate P L : Type u :=
(mk_point : L → L → P)
(mk_point_ax : ∀ l₁ l₂, mk_point l₁ l₂ ∈ l₁ ∧ mk_point l₁ l₂ ∈ l₂)

/-- A nondegenerate configuration in which every pair of points has a line through them. -/
class has_lines extends nondegenerate P L : Type u :=
(mk_line : P → P → L)
(mk_line_ax : ∀ p₁ p₂, p₁ ∈ mk_line p₁ p₂ ∧ p₂ ∈ mk_line p₁ p₂)

open nondegenerate has_points has_lines

instance [nondegenerate P L] : nondegenerate (dual L) (dual P) :=
{ exists_point := @exists_line P L _ _,
  exists_line := @exists_point P L _ _,
  eq_or_eq := λ l₁ l₂ p₁ p₂ h₁ h₂ h₃ h₄, (@eq_or_eq P L _ _ p₁ p₂ l₁ l₂ h₁ h₃ h₂ h₄).symm }

instance [has_points P L] : has_lines (dual L) (dual P) :=
{ mk_line := @mk_point P L _ _,
  mk_line_ax := mk_point_ax }

instance [has_lines P L] : has_points (dual L) (dual P) :=
{ mk_point := @mk_line P L _ _,
  mk_point_ax := mk_line_ax }

lemma has_points.exists_unique_point [has_points P L] (l₁ l₂ : L) (hl : l₁ ≠ l₂) :
  ∃! p, p ∈ l₁ ∧ p ∈ l₂ :=
⟨mk_point l₁ l₂, mk_point_ax l₁ l₂,
  λ p hp, (eq_or_eq hp.1 (mk_point_ax l₁ l₂).1 hp.2 (mk_point_ax l₁ l₂).2).resolve_right hl⟩

lemma has_lines.exists_unique_line [has_lines P L] (p₁ p₂ : P) (hp : p₁ ≠ p₂) :
  ∃! l : L, p₁ ∈ l ∧ p₂ ∈ l :=
has_points.exists_unique_point (dual L) (dual P) p₁ p₂ hp

end configuration
