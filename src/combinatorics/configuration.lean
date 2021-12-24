/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import combinatorics.hall.basic
import set_theory.fincard

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
* `configuration.line_count`: The number of lines through a given point.
* `configuration.point_count`: The number of lines through a given line.

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

/-- If a nondegenerate configuration has at least as many points as lines, then there exists
  an injective function `f` from lines to points, such that `f l` does not lie on `l`. -/
lemma nondegenerate.exists_injective_of_card_le [nondegenerate P L]
  [fintype P] [fintype L] (h : fintype.card L ≤ fintype.card P) :
  ∃ f : L → P, function.injective f ∧ ∀ l, (f l) ∉ l :=
begin
  classical,
  let t : L → finset P := λ l, (set.to_finset {p | p ∉ l}),
  suffices : ∀ s : finset L, s.card ≤ (s.bUnion t).card, -- Hall's marriage theorem
  { obtain ⟨f, hf1, hf2⟩ := (finset.all_card_le_bUnion_card_iff_exists_injective t).mp this,
    exact ⟨f, hf1, λ l, set.mem_to_finset.mp (hf2 l)⟩ },
  intro s,
  by_cases hs₀ : s.card = 0, -- If `s = ∅`, then `s.card = 0 ≤ (s.bUnion t).card`
  { simp_rw [hs₀, zero_le] },
  by_cases hs₁ : s.card = 1, -- If `s = {l}`, then pick a point `p ∉ l`
  { obtain ⟨l, rfl⟩ := finset.card_eq_one.mp hs₁,
    obtain ⟨p, hl⟩ := exists_point l,
    rw [finset.card_singleton, finset.singleton_bUnion, nat.one_le_iff_ne_zero],
    exact finset.card_ne_zero_of_mem (set.mem_to_finset.mpr hl) },
  suffices : (s.bUnion t)ᶜ.card ≤ sᶜ.card, -- Rephrase in terms of complements (uses `h`)
  { rw [finset.card_compl, finset.card_compl, tsub_le_iff_left] at this,
    replace := h.trans this,
    rwa [←add_tsub_assoc_of_le s.card_le_univ, le_tsub_iff_left
      (le_add_left s.card_le_univ), add_le_add_iff_right] at this },
  have hs₂ : (s.bUnion t)ᶜ.card ≤ 1, -- At most one line through two points of `s`
  { refine finset.card_le_one_iff.mpr (λ p₁ p₂ hp₁ hp₂, _),
    simp_rw [finset.mem_compl, finset.mem_bUnion, exists_prop, not_exists, not_and,
      set.mem_to_finset, set.mem_set_of_eq, not_not] at hp₁ hp₂,
    obtain ⟨l₁, l₂, hl₁, hl₂, hl₃⟩ :=
    finset.one_lt_card_iff.mp (nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hs₀, hs₁⟩),
    exact (eq_or_eq (hp₁ l₁ hl₁) (hp₂ l₁ hl₁) (hp₁ l₂ hl₂) (hp₂ l₂ hl₂)).resolve_right hl₃ },
  by_cases hs₃ : sᶜ.card = 0,
  { rw [hs₃, nat.le_zero_iff],
    rw [finset.card_compl, tsub_eq_zero_iff_le, has_le.le.le_iff_eq (finset.card_le_univ _),
        eq_comm, finset.card_eq_iff_eq_univ, hs₃, finset.eq_univ_iff_forall] at hs₃ ⊢,
    exact λ p, exists.elim (exists_line p) -- If `s = univ`, then show `s.bUnion t = univ`
      (λ l hl, finset.mem_bUnion.mpr ⟨l, finset.mem_univ l, set.mem_to_finset.mpr hl⟩) },
  { exact hs₂.trans (nat.one_le_iff_ne_zero.mpr hs₃) }, -- If `s < univ`, then consequence of `hs₂`
end

variables {P} (L)

/-- Number of points on a given line. -/
noncomputable def line_count (p : P) : ℕ := nat.card {l : L // p ∈ l}

variables (P) {L}

/-- Number of lines through a given point. -/
noncomputable def point_count (l : L) : ℕ := nat.card {p : P // p ∈ l}

end configuration
