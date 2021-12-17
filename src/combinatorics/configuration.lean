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
* `configuration.line_count`: The number of lines through a given point.
* `configuration.point_count`: The number of lines through a given line.

## Main statements
* `configuration.has_lines.card_le`: `has_lines` implies `card points ≤ card lines`.
* `configuration.has_points.card_le`: `has_points` implies `card lines ≤ card points`.

## Todo
* Abstract projective planes.
-/

open_locale big_operators

namespace configuration

universe u

variables (P L : Type u) [has_mem P L]

/-- A type synonym. -/
def dual := P

instance [this : inhabited P] : inhabited (dual P) := this

instance [this : fintype P] : fintype (dual P) := this

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
(eq_or_eq : ∀ {p₁ p₂ : P}, ∀ {l₁ l₂ : L}, p₁ ∈ l₁ → p₂ ∈ l₁ → p₁ ∈ l₂ → p₂ ∈ l₂ → p₁ = p₂ ∨ l₁ = l₂)

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
  suffices : ∀ s : finset L, s.card ≤ (s.bUnion t).card,
  { obtain ⟨f, hf1, hf2⟩ := (finset.all_card_le_bUnion_card_iff_exists_injective t).mp this,
    exact ⟨f, hf1, λ l, set.mem_to_finset.mp (hf2 l)⟩ },
  intro s,
  by_cases hs₀ : s.card = 0,
  { simp_rw [hs₀, zero_le] },
  by_cases hs₁ : s.card = 1,
  { obtain ⟨l, rfl⟩ := finset.card_eq_one.mp hs₁,
    obtain ⟨p, hl⟩ := exists_point l,
    rw [finset.card_singleton, finset.singleton_bUnion, nat.one_le_iff_ne_zero],
    exact finset.card_ne_zero_of_mem (set.mem_to_finset.mpr hl) },
  by_cases hs₂ : fintype.card P ≤ s.card,
  { obtain rfl := s.card_eq_iff_eq_univ.mp (le_antisymm s.card_le_univ (h.trans hs₂)),
    calc finset.univ.card = fintype.card L : finset.card_univ
    ... ≤ fintype.card P : h
    ... = (finset.univ.bUnion t).card : ((finset.univ.bUnion t).card_eq_iff_eq_univ.mpr
      (finset.eq_univ_iff_forall.mpr (λ p, finset.mem_bUnion.mpr _))).symm,
    obtain ⟨l, hl⟩ := @exists_line P L _ _ p,
    exact ⟨l, finset.mem_univ l, set.mem_to_finset.mpr hl⟩ },
  refine nat.lt_add_one_iff.mp (lt_of_lt_of_le (not_le.mp hs₂) _),
  rw [←tsub_le_iff_left, ←finset.card_compl, finset.card_le_one_iff],
  intros p₁ p₂ hp₁ hp₂,
  simp_rw [finset.mem_compl, finset.mem_bUnion, exists_prop, not_exists, not_and,
    set.mem_to_finset, set.mem_set_of_eq, not_not] at hp₁ hp₂,
  obtain ⟨l₁, l₂, hl₁, hl₂, hl₃⟩ :=
  finset.one_lt_card_iff.mp (nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hs₀, hs₁⟩),
  exact (eq_or_eq (hp₁ l₁ hl₁) (hp₂ l₁ hl₁) (hp₁ l₂ hl₂) (hp₂ l₂ hl₂)).resolve_right hl₃,
end

/-- Number of points on a given line. -/
def line_count (p : P) [fintype {l : L // p ∈ l}] : ℕ := fintype.card {l : L // p ∈ l}

/-- Number of lines through a given point. -/
def point_count (l : L) [fintype {p : P // p ∈ l}] : ℕ := fintype.card {p // p ∈ l}

lemma sum_line_count_eq_sum_point_count [fintype P] [fintype L]
  [Π p, fintype {l : L // p ∈ l}] [Π l : L, fintype {p // p ∈ l}] :
  ∑ p : P, line_count P L p = ∑ l : L, point_count P L l :=
begin
  simp_rw [line_count, point_count, ←fintype.card_sigma],
  apply fintype.card_congr,
  calc (Σ p, {l : L // p ∈ l}) ≃ {x : P × L // x.1 ∈ x.2} :
    (equiv.subtype_prod_equiv_sigma_subtype (∈)).symm
  ... ≃ {x : L × P // x.2 ∈ x.1} : (equiv.prod_comm P L).subtype_equiv (λ x, iff.rfl)
  ... ≃ (Σ l, {p // p ∈ l}) : equiv.subtype_prod_equiv_sigma_subtype (λ (l : L) (p : P), p ∈ l),
end

lemma has_lines.point_count_le_line_count
  [has_lines P L] (p : P) (l : L) (h : p ∉ l)
  [fintype {p // p ∈ l}] [fintype {l : L // p ∈ l}] :
  point_count P L l ≤ line_count P L p :=
fintype.card_le_of_injective (λ p', ⟨mk_line p p', (mk_line_ax p p').1⟩)
  (λ p₁ p₂ hp, subtype.ext ((eq_or_eq p₁.2 p₂.2 (mk_line_ax p p₁).2 (by
  { rw (show mk_line p p₁ = mk_line p p₂, from subtype.ext_iff.mp hp),
    exact (mk_line_ax p p₂).2 })).resolve_right (λ h', (congr_arg _ h').mp h (mk_line_ax p p₁).1)))

/- If a nondegenerate configuration has a unique line through any two points,
  then there are at least as many lines as points. -/
lemma has_lines.card_le [has_lines P L] [fintype P] [fintype L] :
  fintype.card P ≤ fintype.card L :=
begin
  classical,
  by_contradiction hc₂,
  obtain ⟨f, hf₁, hf₂⟩ := nondegenerate.exists_injective_of_card_le P L (le_of_not_le hc₂),
  have := calc ∑ p, line_count P L p = ∑ l, point_count P L l : sum_line_count_eq_sum_point_count P L
  ... ≤ ∑ l, line_count P L (f l) :
    finset.sum_le_sum (λ l hl, has_lines.point_count_le_line_count P L (f l) l (hf₂ l))
  ... = ∑ p in finset.univ.image f, line_count P L p : _
  ... < ∑ p, line_count P L p : _,
  { exact lt_irrefl _ this },
  { refine finset.sum_bij (λ l hl, f l) (λ l hl, finset.mem_image_of_mem f hl)
      (λ l hl, rfl) (λ l₁ l₂ hl₁ hl₂ hl₃, hf₁ hl₃) (λ p, _),
    convert finset.mem_image.mp,
    simp_rw [eq_comm] },
  { have key := mt (fintype.card_le_of_surjective f) hc₂,
    push_neg at key,
    obtain ⟨p, hp⟩ := key,
    refine finset.sum_lt_sum_of_subset ((finset.univ.image f).subset_univ) (finset.mem_univ p)
      _ _ (λ p hp₁ hp₂, zero_le (line_count P L p)),
    { rw [finset.mem_image],
      push_neg,
      exact λ l hl, hp l },
    { exact fintype.card_pos_iff.mpr ⟨⟨mk_line p p, (mk_line_ax p p).1⟩⟩ } },
end

/- If a nondegenerate configuration has a unique point on any two lines,
  then there are at least as many points as lines. -/
lemma has_points.card_le [has_points P L] [fintype P] [fintype L] :
  fintype.card L ≤ fintype.card P :=
@has_lines.card_le (dual L) (dual P) _ _ _ _

end configuration
