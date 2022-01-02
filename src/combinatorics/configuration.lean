/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import combinatorics.hall.basic
import data.fintype.card
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
(eq_or_eq : ∀ {p₁ p₂ : P} {l₁ l₂ : L}, p₁ ∈ l₁ → p₂ ∈ l₁ → p₁ ∈ l₂ → p₂ ∈ l₂ → p₁ = p₂ ∨ l₁ = l₂)

/-- A nondegenerate configuration in which every pair of lines has an intersection point. -/
class has_points extends nondegenerate P L : Type u :=
(mk_point : ∀ {l₁ l₂ : L} (h : l₁ ≠ l₂), P)
(mk_point_ax : ∀ {l₁ l₂ : L} (h : l₁ ≠ l₂), mk_point h ∈ l₁ ∧ mk_point h ∈ l₂)

/-- A nondegenerate configuration in which every pair of points has a line through them. -/
class has_lines extends nondegenerate P L : Type u :=
(mk_line : ∀ {p₁ p₂ : P} (h : p₁ ≠ p₂), L)
(mk_line_ax : ∀ {p₁ p₂ : P} (h : p₁ ≠ p₂), p₁ ∈ mk_line h ∧ p₂ ∈ mk_line h)

open nondegenerate has_points has_lines

instance [nondegenerate P L] : nondegenerate (dual L) (dual P) :=
{ exists_point := @exists_line P L _ _,
  exists_line := @exists_point P L _ _,
  eq_or_eq := λ l₁ l₂ p₁ p₂ h₁ h₂ h₃ h₄, (@eq_or_eq P L _ _ p₁ p₂ l₁ l₂ h₁ h₃ h₂ h₄).symm }

instance [has_points P L] : has_lines (dual L) (dual P) :=
{ mk_line := @mk_point P L _ _,
  mk_line_ax := λ _ _, mk_point_ax }

instance [has_lines P L] : has_points (dual L) (dual P) :=
{ mk_point := @mk_line P L _ _,
  mk_point_ax := λ _ _, mk_line_ax }

lemma has_points.exists_unique_point [has_points P L] (l₁ l₂ : L) (hl : l₁ ≠ l₂) :
  ∃! p, p ∈ l₁ ∧ p ∈ l₂ :=
⟨mk_point hl, mk_point_ax hl,
  λ p hp, (eq_or_eq hp.1 (mk_point_ax hl).1 hp.2 (mk_point_ax hl).2).resolve_right hl⟩

lemma has_lines.exists_unique_line [has_lines P L] (p₁ p₂ : P) (hp : p₁ ≠ p₂) :
  ∃! l : L, p₁ ∈ l ∧ p₂ ∈ l :=
has_points.exists_unique_point (dual L) (dual P) p₁ p₂ hp

variables {P L}

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

variables (P L)

lemma sum_line_count_eq_sum_point_count [fintype P] [fintype L] :
  ∑ p : P, line_count L p = ∑ l : L, point_count P l :=
begin
  classical,
  simp only [line_count, point_count, nat.card_eq_fintype_card, ←fintype.card_sigma],
  apply fintype.card_congr,
  calc (Σ p, {l : L // p ∈ l}) ≃ {x : P × L // x.1 ∈ x.2} :
    (equiv.subtype_prod_equiv_sigma_subtype (∈)).symm
  ... ≃ {x : L × P // x.2 ∈ x.1} : (equiv.prod_comm P L).subtype_equiv (λ x, iff.rfl)
  ... ≃ (Σ l, {p // p ∈ l}) : equiv.subtype_prod_equiv_sigma_subtype (λ (l : L) (p : P), p ∈ l),
end

variables {P L}

lemma has_lines.point_count_le_line_count [has_lines P L] {p : P} {l : L} (h : p ∉ l)
  [fintype {l : L // p ∈ l}] : point_count P l ≤ line_count L p :=
begin
  by_cases hf : infinite {p : P // p ∈ l},
  { exactI (le_of_eq nat.card_eq_zero_of_infinite).trans (zero_le (line_count L p)) },
  haveI := fintype_of_not_infinite hf,
  rw [line_count, point_count, nat.card_eq_fintype_card, nat.card_eq_fintype_card],
  have : ∀ p' : {p // p ∈ l}, p ≠ p' := λ p' hp', h ((congr_arg (∈ l) hp').mpr p'.2),
  exact fintype.card_le_of_injective (λ p', ⟨mk_line (this p'), (mk_line_ax (this p')).1⟩)
    (λ p₁ p₂ hp, subtype.ext ((eq_or_eq p₁.2 p₂.2 (mk_line_ax (this p₁)).2
      ((congr_arg _ (subtype.ext_iff.mp hp)).mpr (mk_line_ax (this p₂)).2)).resolve_right
        (λ h', (congr_arg _ h').mp h (mk_line_ax (this p₁)).1))),
end

lemma has_points.line_count_le_point_count [has_points P L] {p : P} {l : L} (h : p ∉ l)
  [hf : fintype {p : P // p ∈ l}] : line_count L p ≤ point_count P l :=
@has_lines.point_count_le_line_count (dual L) (dual P) _ _ l p h hf

variables (P L)

/-- If a nondegenerate configuration has a unique line through any two points,
  then there are at least as many lines as points. -/
lemma has_lines.card_le [has_lines P L] [fintype P] [fintype L] :
  fintype.card P ≤ fintype.card L :=
begin
  classical,
  by_contradiction hc₂,
  obtain ⟨f, hf₁, hf₂⟩ := nondegenerate.exists_injective_of_card_le (le_of_not_le hc₂),
  have := calc ∑ p, line_count L p = ∑ l, point_count P l : sum_line_count_eq_sum_point_count P L
  ... ≤ ∑ l, line_count L (f l) :
    finset.sum_le_sum (λ l hl, has_lines.point_count_le_line_count (hf₂ l))
  ... = ∑ p in finset.univ.image f, line_count L p :
    finset.sum_bij (λ l hl, f l) (λ l hl, finset.mem_image_of_mem f hl) (λ l hl, rfl)
      (λ l₁ l₂ hl₁ hl₂ hl₃, hf₁ hl₃) (λ p, by simp_rw [finset.mem_image, eq_comm, imp_self])
  ... < ∑ p, line_count L p : _,
  { exact lt_irrefl _ this },
  { obtain ⟨p, hp⟩ := not_forall.mp (mt (fintype.card_le_of_surjective f) hc₂),
    refine finset.sum_lt_sum_of_subset ((finset.univ.image f).subset_univ) (finset.mem_univ p)
      _ _ (λ p hp₁ hp₂, zero_le (line_count L p)),
    { simpa only [finset.mem_image, exists_prop, finset.mem_univ, true_and] },
    { rw [line_count, nat.card_eq_fintype_card, fintype.card_pos_iff],
      obtain ⟨l, hl⟩ := @exists_line P L _ _ p,
      exact let this := not_exists.mp hp l in ⟨⟨mk_line this, (mk_line_ax this).2⟩⟩ } },
end

/-- If a nondegenerate configuration has a unique point on any two lines,
  then there are at least as many points as lines. -/
lemma has_points.card_le [has_points P L] [fintype P] [fintype L] :
  fintype.card L ≤ fintype.card P :=
@has_lines.card_le (dual L) (dual P) _ _ _ _

variables {P L}

lemma has_lines.exists_bijective_of_card_eq [has_lines P L]
  [fintype P] [fintype L] (h : fintype.card P = fintype.card L) :
  ∃ f : L → P, function.bijective f ∧ ∀ l, point_count P l = line_count L (f l) :=
begin
  classical,
  obtain ⟨f, hf1, hf2⟩ := nondegenerate.exists_injective_of_card_le (ge_of_eq h),
  have hf3 := (fintype.bijective_iff_injective_and_card f).mpr ⟨hf1, h.symm⟩,
  refine ⟨f, hf3, λ l, (finset.sum_eq_sum_iff_of_le
    (by exact λ l hl, has_lines.point_count_le_line_count (hf2 l))).mp
      ((sum_line_count_eq_sum_point_count P L).symm.trans ((finset.sum_bij (λ l hl, f l)
        (λ l hl, finset.mem_univ (f l)) (λ l hl, refl (line_count L (f l)))
          (λ l₁ l₂ hl₁ hl₂ hl, hf1 hl) (λ p hp, _)).symm)) l (finset.mem_univ l)⟩,
  obtain ⟨l, rfl⟩ := hf3.2 p,
  exact ⟨l, finset.mem_univ l, rfl⟩,
end

end configuration
