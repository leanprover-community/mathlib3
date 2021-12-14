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
* `configuration.line_count`: The number of lines through a given point.
* `configuration.point_count`: The number of lines through a given line.

## Main statements
* `configuration.has_lines.card_le`: `has_lines` implies `card points ≤ card lines`.
* `configuration.has_points.card_le`: `has_points` implies `card lines ≤ card points`.

## Todo
* Abstract projective planes.
-/

open_locale big_operators

universe u

variables (P L : Type u)

/-- A configuration is an incidence relation between collections of points and lines. -/
def configuration := P → L → Prop

namespace configuration

variables {P L} (c : configuration P L)

/-- The dual configuration is obtained by swapping points and lines. -/
def dual : configuration L P := λ l p, c p l

lemma dual_dual : c.dual.dual = c :=
rfl

/-- A configuration is nondegenerate if:
  1) there does not exist a line that passes through all of the points,
  2) there does not exist a point that is on all of the lines,
  3) there is at most one line through any two points,
  4) there is at most one point through at two lines.
  Conditions 3 and 4 are equivalent. -/
structure nondegenerate : Prop :=
(exists_point : ∀ l, ∃ p, ¬ c p l)
(exists_line : ∀ p, ∃ l, ¬ c p l)
(unique : ∀ p₁ p₂, ∀ l₁ l₂, c p₁ l₁ → c p₂ l₁ → c p₁ l₂ → c p₂ l₂ → p₁ = p₂ ∨ l₁ = l₂)

/-- A nondegenerate configuration in which every pair of lines has an intersection point. -/
structure has_points extends nondegenerate c : Prop :=
(exists_point' : ∀ l₁ l₂, l₁ ≠ l₂ → ∃ p, c p l₁ ∧ c p l₂)

/-- A nondegenerate configuration in which every pair of points has a line through them. -/
structure has_lines extends nondegenerate c : Prop :=
(exists_line' : ∀ p₁ p₂, p₁ ≠ p₂ → ∃ l, c p₁ l ∧ c p₂ l)

variables {c}

lemma has_points.exists_unique_point (hc : c.has_points) (l₁ l₂ : L) (hl : l₁ ≠ l₂) :
  ∃! p, c p l₁ ∧ c p l₂ :=
exists_unique_of_exists_of_unique (hc.exists_point' l₁ l₂ hl)
  (λ p₁ p₂ ⟨h₁, h₂⟩ ⟨h₃, h₄⟩, (hc.unique p₁ p₂ l₁ l₂ h₁ h₃ h₂ h₄).resolve_right hl)

lemma has_lines.exists_unique_line (hc : c.has_lines) (p₁ p₂ : P) (hp : p₁ ≠ p₂) :
  ∃! l, c p₁ l ∧ c p₂ l :=
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

/-- If a nondegenerate configuration has at least as many points as lines, then there exists
  an injective function `f` from lines to points, such that `f l` does not lie on `l`. -/
lemma nondegenerate.exists_injective_of_card_le  (hc : c.nondegenerate)
  [fintype P] [fintype L] (hc' : fintype.card L ≤ fintype.card P) :
  ∃ f, function.injective f ∧ ∀ l, ¬ c (f l) l :=
begin
  classical,
  let t : L → finset P := λ l, (set.to_finset {p | ¬ c p l}),
  suffices : ∀ s : finset L, s.card ≤ (s.bUnion t).card,
  { obtain ⟨f, hf1, hf2⟩ := (finset.all_card_le_bUnion_card_iff_exists_injective t).mp this,
    exact ⟨f, hf1, λ l, set.mem_to_finset.mp (hf2 l)⟩ },
  intro s,
  by_cases hs₀ : s.card = 0,
  { simp_rw [hs₀, zero_le] },
  by_cases hs₁ : s.card = 1,
  { obtain ⟨l, rfl⟩ := finset.card_eq_one.mp hs₁,
    obtain ⟨p, hl⟩ := hc.exists_point l,
    rw [finset.card_singleton, finset.singleton_bUnion, nat.one_le_iff_ne_zero],
    exact finset.card_ne_zero_of_mem (set.mem_to_finset.mpr hl) },
  by_cases hs₂ : fintype.card L ≤ s.card,
  { obtain rfl := s.card_eq_iff_eq_univ.mp (le_antisymm s.card_le_univ hs₂),
    suffices : finset.univ.bUnion t = finset.univ,
    { rwa [this, finset.card_univ, finset.card_univ] },
    refine finset.eq_univ_iff_forall.mpr (λ p, finset.mem_bUnion.mpr _),
    obtain ⟨l, hl⟩ := hc.exists_line p,
    exact ⟨l, finset.mem_univ l, set.mem_to_finset.mpr hl⟩ },
  suffices : (s.bUnion t)ᶜ.card ≤ 1,
  { rw [finset.card_compl, tsub_le_iff_left] at this,
    exact (add_le_add_iff_right 1).mp (le_trans (not_le.mp hs₂) (hc'.trans this)) },
  refine finset.card_le_one_iff.mpr (λ p₁ p₂ hp₁ hp₂, _),
  simp_rw [finset.mem_compl, finset.mem_bUnion, exists_prop, not_exists, not_and,
    set.mem_to_finset, set.mem_set_of_eq, not_not] at hp₁ hp₂,
  obtain ⟨l₁, l₂, hl₁, hl₂, hl₃⟩ :=
  finset.one_lt_card_iff.mp (nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hs₀, hs₁⟩),
  exact (hc.unique p₁ p₂ l₁ l₂
    (hp₁ l₁ hl₁) (hp₂ l₁ hl₁) (hp₁ l₂ hl₂) (hp₂ l₂ hl₂)).resolve_right hl₃,
end

variables (c)

/-- Number of points on a given line. -/
def line_count (p : P) [fintype {l // c p l}] : ℕ := fintype.card {l // c p l}

/-- Number of lines through a given point. -/
def point_count (l : L) [fintype {p // c p l}] : ℕ := fintype.card {p // c p l}

lemma sum_line_count_eq_sum_point_count [fintype P] [fintype L]
  [Π p, fintype {l // c p l}] [Π l, fintype {p // c p l}] :
  ∑ p : P, c.line_count p = ∑ l : L, c.point_count l :=
begin
  simp_rw [line_count, point_count, ←fintype.card_sigma],
  apply fintype.card_congr,
  calc (Σ p, {l // c p l}) ≃ {x : P × L // c x.1 x.2} :
    (equiv.subtype_prod_equiv_sigma_subtype c).symm
  ... ≃ {x : L × P // c x.2 x.1} : (equiv.prod_comm P L).subtype_equiv (λ x, iff.rfl)
  ... ≃ Σ l, {p // c p l} : equiv.subtype_prod_equiv_sigma_subtype (λ l p, c p l),
end

variables {c}

lemma has_lines.point_count_le_line_count
  (hc : c.has_lines) (p : P) (l : L) (h : ¬ c p l)
  [fintype {p // c p l}] [fintype {l // c p l}] :
  c.point_count l ≤ c.line_count p :=
begin
  let g : {p' // c p' l} → {l' // c p l'} :=
  λ p', ⟨classical.some (hc.exists_line' p p' (λ h', (congr_arg _ h').mp h p'.2)),
    (classical.some_spec (hc.exists_line' p p' (λ h', (congr_arg _ h').mp h p'.2))).1⟩,
  have hg : ∀ p', c ↑p' (g p') :=
  λ p', (classical.some_spec (hc.exists_line' p p' (λ h', (congr_arg _ h').mp h p'.2))).2,
  exact fintype.card_le_of_injective g (λ p₁ p₂ hp, subtype.ext
    ((hc.unique p₁ p₂ l (g p₁) p₁.2 p₂.2 (hg p₁) (by { rw hp, exact hg p₂, })).resolve_right
      (λ h', (congr_arg _ h').mp h (g p₁).2))),
end

/- If a nondegenerate configuration has a unique line through any two points,
  then there are at least as many lines as points. -/
lemma has_lines.card_le (hc : c.has_lines) [fintype P] [fintype L] :
  fintype.card P ≤ fintype.card L :=
begin
  classical,
  by_contradiction hc₂,
  obtain ⟨f, hf₁, hf₂⟩ := hc.to_nondegenerate.exists_injective_of_card_le (le_of_not_le hc₂),
  have := calc ∑ p, c.line_count p = ∑ l, c.point_count l : c.sum_line_count_eq_sum_point_count
  ... ≤ ∑ l, c.line_count (f l) :
    finset.sum_le_sum (λ l hl, hc.point_count_le_line_count (f l) l (hf₂ l))
  ... = ∑ p in finset.univ.image f, c.line_count p : _
  ... < ∑ p, c.line_count p : _,
  { exact lt_irrefl _ this },
  { refine finset.sum_bij (λ l hl, f l) (λ l hl, finset.mem_image_of_mem f hl)
      (λ l hl, rfl) (λ l₁ l₂ hl₁ hl₂ hl₃, hf₁ hl₃) (λ p, _),
    convert finset.mem_image.mp,
    simp_rw [eq_comm] },
  { have key := mt (fintype.card_le_of_surjective f) hc₂,
    push_neg at key,
    obtain ⟨p, hp⟩ := key,
    refine finset.sum_lt_sum_of_subset ((finset.univ.image f).subset_univ) (finset.mem_univ p)
      _ _ (λ p hp₁ hp₂, zero_le (c.line_count p)),
    { rw [finset.mem_image],
      push_neg,
      exact λ l hl, hp l },
    { have key1 : 1 < fintype.card P,
      { refine lt_of_le_of_lt _ (lt_of_not_ge hc₂),
        obtain ⟨l, hl⟩ := hc.exists_line p,
        exact fintype.card_pos_iff.mpr ⟨l⟩ },
      obtain ⟨q, hqp⟩ := fintype.exists_ne_of_one_lt_card key1 p,
      obtain ⟨l, hql, hpl⟩ := hc.exists_line' q p hqp,
      exact fintype.card_pos_iff.mpr ⟨⟨l, hpl⟩⟩ } },
end

/- If a nondegenerate configuration has a unique point on any two lines,
  then there are at least as many points as lines. -/
lemma has_points.card_le (hc : c.has_points) [fintype P] [fintype L] :
  fintype.card L ≤ fintype.card P :=
hc.dual.card_le

end configuration
