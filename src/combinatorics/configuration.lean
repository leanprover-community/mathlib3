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
* `configuration`: Finite collections of points and lines with an incidence relation.
* `configuration.dual`: The dual configuration obtained by swapping points and lines.
* `configuration.nondegenerate`: Excludes certain degenerate configurations,
  and imposes uniqueness of intersection points.
* `configuration.has_points`: A nondegenerate configuration in which
  every pair of lines has an intersection point.
* `configuration.has_lines`:  nondegenerate configuration in which
  every pair of points has a line through them.

## Todo
* Abstract projective planes.
-/

open_locale big_operators

universe u

/-- A configuration is a finite collections of points and lines with an incidence relation. -/
structure configuration :=
(P : Type u)
(fP : fintype P)
(L : Type u)
(fL : fintype L)
(R : P → L → Prop)

instance : inhabited (configuration) :=
⟨⟨empty, fintype.of_is_empty, empty, fintype.of_is_empty, empty.elim⟩⟩

namespace configuration

variables (c : configuration)

instance : fintype c.P := c.fP

instance : fintype c.L := c.fL

/-- The dual configuration is obtained by swapping points and lines. -/
def dual : configuration :=
{ P := c.L,
  fP := c.fL,
  L := c.P,
  fL := c.fP,
  R := λ p l, c.R l p }

lemma dual_dual : c.dual.dual = c :=
by cases c; refl

/-- A configuration is nondegenerate if:
  1) there does not exist a line that passes through all of the points,
  2) there does not exist a point that is on all of the lines,
  3) there is at most one line through any two points,
  4) there is at most one point through at two lines.
  Conditions 3 and 4 are equivalent. -/
structure nondegenerate : Prop :=
(exists_point : ∀ l : c.L, ∃ p : c.P, ¬ c.R p l)
(exists_line : ∀ p : c.P, ∃ l : c.L, ¬ c.R p l)
(unique : ∀ p₁ p₂ : c.P, ∀ l₁ l₂ : c.L,
  c.R p₁ l₁ → c.R p₂ l₁ → c.R p₁ l₂ → c.R p₂ l₂ → p₁ = p₂ ∨ l₁ = l₂)

/-- A nondegenerate configuration in which every pair of lines has an intersection point. -/
structure has_points extends nondegenerate c : Prop :=
(exists_point' : ∀ l₁ l₂ : c.L, l₁ ≠ l₂ → ∃ p : c.P, c.R p l₁ ∧ c.R p l₂)

/-- A nondegenerate configuration in which every pair of points has a line through them. -/
structure has_lines extends nondegenerate c : Prop :=
(exists_line' : ∀ p₁ p₂ : c.P, p₁ ≠ p₂ → ∃ l : c.L, c.R p₁ l ∧ c.R p₂ l)

variables {c}

lemma has_points.exists_unique_point (hc : c.has_points) (l₁ l₂ : c.L) (hl : l₁ ≠ l₂) :
  ∃! p : c.P, c.R p l₁ ∧ c.R p l₂ :=
exists_unique_of_exists_of_unique (hc.exists_point' l₁ l₂ hl)
  (λ p₁ p₂ ⟨h₁, h₂⟩ ⟨h₃, h₄⟩, (hc.unique p₁ p₂ l₁ l₂ h₁ h₃ h₂ h₄).resolve_right hl)

lemma has_lines.exists_unique_line (hc : c.has_lines) (p₁ p₂ : c.P) (hp : p₁ ≠ p₂) :
  ∃! l : c.L, c.R p₁ l ∧ c.R p₂ l :=
exists_unique_of_exists_of_unique (hc.exists_line' p₁ p₂ hp)
  (λ l₁ l₂ ⟨h₁, h₂⟩ ⟨h₃, h₄⟩, (hc.unique p₁ p₂ l₁ l₂ h₁ h₂ h₃ h₄).resolve_left hp)

lemma nondegenerate.dual (hc : c.nondegenerate) : c.dual.nondegenerate :=
{ exists_point := hc.exists_line,
  exists_line := hc.exists_point,
  unique := λ p₁ p₂ l₁ l₂ h₁ h₂ h₃ h₄, (hc.unique l₁ l₂ p₁ p₂ h₁ h₃ h₂ h₄).symm }

lemma has_points.dual (hc : c.has_points) : c.dual.has_lines :=
{ exists_line' := hc.exists_point',
  .. hc.to_nondegenerate.dual }

lemma has_lines.dual (hc : c.has_lines) : c.dual.has_points :=
{ exists_point' := hc.exists_line',
  .. hc.to_nondegenerate.dual }

end configuration
