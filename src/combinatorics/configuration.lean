/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import algebra.big_operators.order
import combinatorics.hall.basic
import data.fintype.big_operators
import set_theory.cardinal.finite

/-!
# Configurations of Points and lines

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
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
* `configuration.has_lines.card_le`: `has_lines` implies `|P| ≤ |L|`.
* `configuration.has_points.card_le`: `has_points` implies `|L| ≤ |P|`.
* `configuration.has_lines.has_points`: `has_lines` and `|P| = |L|` implies `has_points`.
* `configuration.has_points.has_lines`: `has_points` and `|P| = |L|` implies `has_lines`.
Together, these four statements say that any two of the following properties imply the third:
(a) `has_lines`, (b) `has_points`, (c) `|P| = |L|`.

-/

open_locale big_operators

set_option old_structure_cmd true

namespace configuration

variables (P L : Type*) [has_mem P L]

/-- A type synonym. -/
def dual := P

instance [this : inhabited P] : inhabited (dual P) := this

instance [finite P] : finite (dual P) := ‹finite P›
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
class has_points extends nondegenerate P L :=
(mk_point : Π {l₁ l₂ : L} (h : l₁ ≠ l₂), P)
(mk_point_ax : ∀ {l₁ l₂ : L} (h : l₁ ≠ l₂), mk_point h ∈ l₁ ∧ mk_point h ∈ l₂)

/-- A nondegenerate configuration in which every pair of points has a line through them. -/
class has_lines extends nondegenerate P L :=
(mk_line : Π {p₁ p₂ : P} (h : p₁ ≠ p₂), L)
(mk_line_ax : ∀ {p₁ p₂ : P} (h : p₁ ≠ p₂), p₁ ∈ mk_line h ∧ p₂ ∈ mk_line h)

open nondegenerate has_points (mk_point mk_point_ax) has_lines (mk_line mk_line_ax)

instance [nondegenerate P L] : nondegenerate (dual L) (dual P) :=
{ exists_point := @exists_line P L _ _,
  exists_line := @exists_point P L _ _,
  eq_or_eq := λ l₁ l₂ p₁ p₂ h₁ h₂ h₃ h₄, (@eq_or_eq P L _ _ p₁ p₂ l₁ l₂ h₁ h₃ h₂ h₄).symm }

instance [has_points P L] : has_lines (dual L) (dual P) :=
{ mk_line := @mk_point P L _ _,
  mk_line_ax := λ _ _, mk_point_ax,
  .. dual.nondegenerate _ _ }

instance [has_lines P L] : has_points (dual L) (dual P) :=
{ mk_point := @mk_line P L _ _,
  mk_point_ax := λ _ _, mk_line_ax,
  .. dual.nondegenerate _ _ }

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
  { rw [hs₃, le_zero_iff],
    rw [finset.card_compl, tsub_eq_zero_iff_le, has_le.le.le_iff_eq (finset.card_le_univ _),
        eq_comm, finset.card_eq_iff_eq_univ] at hs₃ ⊢,
    rw hs₃,
    rw finset.eq_univ_iff_forall at hs₃ ⊢,
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
  [finite {l : L // p ∈ l}] : point_count P l ≤ line_count L p :=
begin
  by_cases hf : infinite {p : P // p ∈ l},
  { exactI (le_of_eq nat.card_eq_zero_of_infinite).trans (zero_le (line_count L p)) },
  haveI := fintype_of_not_infinite hf,
  casesI nonempty_fintype {l : L // p ∈ l},
  rw [line_count, point_count, nat.card_eq_fintype_card, nat.card_eq_fintype_card],
  have : ∀ p' : {p // p ∈ l}, p ≠ p' := λ p' hp', h ((congr_arg (∈ l) hp').mpr p'.2),
  exact fintype.card_le_of_injective (λ p', ⟨mk_line (this p'), (mk_line_ax (this p')).1⟩)
    (λ p₁ p₂ hp, subtype.ext ((eq_or_eq p₁.2 p₂.2 (mk_line_ax (this p₁)).2
      ((congr_arg _ (subtype.ext_iff.mp hp)).mpr (mk_line_ax (this p₂)).2)).resolve_right
        (λ h', (congr_arg _ h').mp h (mk_line_ax (this p₁)).1))),
end

lemma has_points.line_count_le_point_count [has_points P L] {p : P} {l : L} (h : p ∉ l)
  [hf : finite {p : P // p ∈ l}] : line_count L p ≤ point_count P l :=
@has_lines.point_count_le_line_count (dual L) (dual P) _ _ l p h hf

variables (P L)

/-- If a nondegenerate configuration has a unique line through any two points, then `|P| ≤ |L|`. -/
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

/-- If a nondegenerate configuration has a unique point on any two lines, then `|L| ≤ |P|`. -/
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

lemma has_lines.line_count_eq_point_count [has_lines P L] [fintype P] [fintype L]
  (hPL : fintype.card P = fintype.card L) {p : P} {l : L} (hpl : p ∉ l) :
  line_count L p = point_count P l :=
begin
  classical,
  obtain ⟨f, hf1, hf2⟩ := has_lines.exists_bijective_of_card_eq hPL,
  let s : finset (P × L) := set.to_finset {i | i.1 ∈ i.2},
  have step1 : ∑ i : P × L, line_count L i.1 = ∑ i : P × L, point_count P i.2,
  { rw [←finset.univ_product_univ, finset.sum_product_right, finset.sum_product],
    simp_rw [finset.sum_const, finset.card_univ, hPL, sum_line_count_eq_sum_point_count] },
  have step2 : ∑ i in s, line_count L i.1 = ∑ i in s, point_count P i.2,
  { rw [s.sum_finset_product finset.univ (λ p, set.to_finset {l | p ∈ l})],
    rw [s.sum_finset_product_right finset.univ (λ l, set.to_finset {p | p ∈ l})],
    refine (finset.sum_bij (λ l hl, f l) (λ l hl, finset.mem_univ (f l)) (λ l hl, _)
      (λ _ _ _ _ h, hf1.1 h) (λ p hp, _)).symm,
    { simp_rw [finset.sum_const, set.to_finset_card, ←nat.card_eq_fintype_card],
      change (point_count P l) • (point_count P l) = (line_count L (f l)) • (line_count L (f l)),
      rw hf2 },
    { obtain ⟨l, hl⟩ := hf1.2 p,
      exact ⟨l, finset.mem_univ l, hl.symm⟩ },
    all_goals { simp_rw [finset.mem_univ, true_and, set.mem_to_finset], exact λ p, iff.rfl } },
  have step3 : ∑ i in sᶜ, line_count L i.1 = ∑ i in sᶜ, point_count P i.2,
  { rwa [←s.sum_add_sum_compl, ←s.sum_add_sum_compl, step2, add_left_cancel_iff] at step1 },
  rw ← set.to_finset_compl at step3,
  exact ((finset.sum_eq_sum_iff_of_le (by exact λ i hi, has_lines.point_count_le_line_count
    (set.mem_to_finset.mp hi))).mp step3.symm (p, l) (set.mem_to_finset.mpr hpl)).symm,
end

lemma has_points.line_count_eq_point_count [has_points P L] [fintype P] [fintype L]
  (hPL : fintype.card P = fintype.card L) {p : P} {l : L} (hpl : p ∉ l) :
  line_count L p = point_count P l :=
(@has_lines.line_count_eq_point_count (dual L) (dual P) _ _  _ _ hPL.symm l p hpl).symm

/-- If a nondegenerate configuration has a unique line through any two points, and if `|P| = |L|`,
  then there is a unique point on any two lines. -/
noncomputable def has_lines.has_points [has_lines P L] [fintype P] [fintype L]
  (h : fintype.card P = fintype.card L) : has_points P L :=
let this : ∀ l₁ l₂ : L, l₁ ≠ l₂ → ∃ p : P, p ∈ l₁ ∧ p ∈ l₂ := λ l₁ l₂ hl, begin
  classical,
  obtain ⟨f, hf1, hf2⟩ := has_lines.exists_bijective_of_card_eq h,
  haveI : nontrivial L := ⟨⟨l₁, l₂, hl⟩⟩,
  haveI := fintype.one_lt_card_iff_nontrivial.mp ((congr_arg _ h).mpr fintype.one_lt_card),
  have h₁ : ∀ p : P, 0 < line_count L p := λ p, exists.elim (exists_ne p) (λ q hq, (congr_arg _
    nat.card_eq_fintype_card).mpr (fintype.card_pos_iff.mpr ⟨⟨mk_line hq, (mk_line_ax hq).2⟩⟩)),
  have h₂ : ∀ l : L, 0 < point_count P l := λ l, (congr_arg _ (hf2 l)).mpr (h₁ (f l)),
  obtain ⟨p, hl₁⟩ := fintype.card_pos_iff.mp ((congr_arg _ nat.card_eq_fintype_card).mp (h₂ l₁)),
  by_cases hl₂ : p ∈ l₂, exact ⟨p, hl₁, hl₂⟩,
  have key' : fintype.card {q : P // q ∈ l₂} = fintype.card {l : L // p ∈ l},
  { exact ((has_lines.line_count_eq_point_count h hl₂).trans nat.card_eq_fintype_card).symm.trans
    nat.card_eq_fintype_card, },
  have : ∀ q : {q // q ∈ l₂}, p ≠ q := λ q hq, hl₂ ((congr_arg (∈ l₂) hq).mpr q.2),
  let f : {q : P // q ∈ l₂} → {l : L // p ∈ l} := λ q, ⟨mk_line (this q), (mk_line_ax (this q)).1⟩,
  have hf : function.injective f := λ q₁ q₂ hq, subtype.ext ((eq_or_eq q₁.2 q₂.2
    (mk_line_ax (this q₁)).2 ((congr_arg _ (subtype.ext_iff.mp hq)).mpr (mk_line_ax
      (this q₂)).2)).resolve_right (λ h, (congr_arg _ h).mp hl₂ (mk_line_ax (this q₁)).1)),
  have key' := ((fintype.bijective_iff_injective_and_card f).mpr ⟨hf, key'⟩).2,
  obtain ⟨q, hq⟩ := key' ⟨l₁, hl₁⟩,
  exact ⟨q, (congr_arg _ (subtype.ext_iff.mp hq)).mp (mk_line_ax (this q)).2, q.2⟩,
end in
{ mk_point := λ l₁ l₂ hl, classical.some (this l₁ l₂ hl),
  mk_point_ax := λ l₁ l₂ hl, classical.some_spec (this l₁ l₂ hl),
  .. ‹has_lines P L› }

/-- If a nondegenerate configuration has a unique point on any two lines, and if `|P| = |L|`,
  then there is a unique line through any two points. -/
noncomputable def has_points.has_lines [has_points P L] [fintype P] [fintype L]
  (h : fintype.card P = fintype.card L) : has_lines P L :=
let this := @has_lines.has_points (dual L) (dual P) _ _ _ _ h.symm in
{ mk_line := λ _ _, this.mk_point,
  mk_line_ax := λ _ _, this.mk_point_ax,
  .. ‹has_points P L› }

variables (P L)

/-- A projective plane is a nondegenerate configuration in which every pair of lines has
  an intersection point, every pair of points has a line through them,
  and which has three points in general position. -/
class projective_plane extends has_points P L, has_lines P L :=
(exists_config : ∃ (p₁ p₂ p₃ : P) (l₁ l₂ l₃ : L), p₁ ∉ l₂ ∧ p₁ ∉ l₃ ∧
  p₂ ∉ l₁ ∧ p₂ ∈ l₂ ∧ p₂ ∈ l₃ ∧ p₃ ∉ l₁ ∧ p₃ ∈ l₂ ∧ p₃ ∉ l₃)

namespace projective_plane

variables [projective_plane P L]

instance : projective_plane (dual L) (dual P) :=
{ exists_config :=
    let ⟨p₁, p₂, p₃, l₁, l₂, l₃, h₁₂, h₁₃, h₂₁, h₂₂, h₂₃, h₃₁, h₃₂, h₃₃⟩ :=
      @exists_config P L _ _ in
    ⟨l₁, l₂, l₃, p₁, p₂, p₃, h₂₁, h₃₁, h₁₂, h₂₂, h₃₂, h₁₃, h₂₃, h₃₃⟩,
  .. dual.has_points _ _,
  .. dual.has_lines _ _ }

/-- The order of a projective plane is one less than the number of lines through an arbitrary point.
Equivalently, it is one less than the number of points on an arbitrary line. -/
noncomputable def order : ℕ :=
line_count L (classical.some (@exists_config P L _ _)) - 1

lemma card_points_eq_card_lines [fintype P] [fintype L] : fintype.card P = fintype.card L :=
le_antisymm (has_lines.card_le P L) (has_points.card_le P L)

variables {P} (L)

lemma line_count_eq_line_count [finite P] [finite L] (p q : P) :
  line_count L p = line_count L q :=
begin
  casesI nonempty_fintype P,
  casesI nonempty_fintype L,
  obtain ⟨p₁, p₂, p₃, l₁, l₂, l₃, h₁₂, h₁₃, h₂₁, h₂₂, h₂₃, h₃₁, h₃₂, h₃₃⟩ := exists_config,
  have h := card_points_eq_card_lines P L,
  let n := line_count L p₂,
  have hp₂ : line_count L p₂ = n := rfl,
  have hl₁ : point_count P l₁ = n := (has_lines.line_count_eq_point_count h h₂₁).symm.trans hp₂,
  have hp₃ : line_count L p₃ = n := (has_lines.line_count_eq_point_count h h₃₁).trans hl₁,
  have hl₃ : point_count P l₃ = n := (has_lines.line_count_eq_point_count h h₃₃).symm.trans hp₃,
  have hp₁ : line_count L p₁ = n := (has_lines.line_count_eq_point_count h h₁₃).trans hl₃,
  have hl₂ : point_count P l₂ = n := (has_lines.line_count_eq_point_count h h₁₂).symm.trans hp₁,
  suffices : ∀ p : P, line_count L p = n, { exact (this p).trans (this q).symm },
  refine λ p, or_not.elim (λ h₂, _) (λ h₂, (has_lines.line_count_eq_point_count h h₂).trans hl₂),
  refine or_not.elim (λ h₃, _) (λ h₃, (has_lines.line_count_eq_point_count h h₃).trans hl₃),
  rwa (eq_or_eq h₂ h₂₂ h₃ h₂₃).resolve_right (λ h, h₃₃ ((congr_arg (has_mem.mem p₃) h).mp h₃₂)),
end

variables (P) {L}

lemma point_count_eq_point_count [finite P] [finite L] (l m : L) :
  point_count P l = point_count P m :=
line_count_eq_line_count (dual P) l m

variables {P L}

lemma line_count_eq_point_count [finite P] [finite L] (p : P) (l : L) :
  line_count L p = point_count P l :=
exists.elim (exists_point l) $ λ q hq, (line_count_eq_line_count L p q).trans $
  by { casesI nonempty_fintype P, casesI nonempty_fintype L,
    exact has_lines.line_count_eq_point_count (card_points_eq_card_lines P L) hq }

variables (P L)

lemma dual.order [finite P] [finite L] : order (dual L) (dual P) = order P L :=
congr_arg (λ n, n - 1) (line_count_eq_point_count _ _)

variables {P} (L)

lemma line_count_eq [finite P] [finite L] (p : P) : line_count L p = order P L + 1 :=
begin
  classical,
  obtain ⟨q, -, -, l, -, -, -, -, h, -⟩ := classical.some_spec (@exists_config P L _ _),
  casesI nonempty_fintype {l : L // q ∈ l},
  rw [order, line_count_eq_line_count L p q, line_count_eq_line_count L (classical.some _) q,
      line_count, nat.card_eq_fintype_card, nat.sub_add_cancel],
  exact fintype.card_pos_iff.mpr ⟨⟨l, h⟩⟩,
end

variables (P) {L}

lemma point_count_eq [finite P] [finite L] (l : L) : point_count P l = order P L + 1 :=
(line_count_eq (dual P) l).trans (congr_arg (λ n, n + 1) (dual.order P L))

variables (P L)

lemma one_lt_order [finite P] [finite L] : 1 < order P L :=
begin
  obtain ⟨p₁, p₂, p₃, l₁, l₂, l₃, -, -, h₂₁, h₂₂, h₂₃, h₃₁, h₃₂, h₃₃⟩ := @exists_config P L _ _,
  classical,
  casesI nonempty_fintype {p : P // p ∈ l₂},
  rw [←add_lt_add_iff_right, ←point_count_eq _ l₂, point_count, nat.card_eq_fintype_card],
  simp_rw [fintype.two_lt_card_iff, ne, subtype.ext_iff],
  have h := mk_point_ax (λ h, h₂₁ ((congr_arg _ h).mpr h₂₂)),
  exact ⟨⟨mk_point _, h.2⟩, ⟨p₂, h₂₂⟩, ⟨p₃, h₃₂⟩,
    ne_of_mem_of_not_mem h.1 h₂₁, ne_of_mem_of_not_mem h.1 h₃₁, ne_of_mem_of_not_mem h₂₃ h₃₃⟩,
end

variables {P} (L)

lemma two_lt_line_count [finite P] [finite L] (p : P) : 2 < line_count L p :=
by simpa only [line_count_eq L p, nat.succ_lt_succ_iff] using one_lt_order P L

variables (P) {L}

lemma two_lt_point_count [finite P] [finite L] (l : L) : 2 < point_count P l :=
by simpa only [point_count_eq P l, nat.succ_lt_succ_iff] using one_lt_order P L

variables (P) (L)

lemma card_points [fintype P] [finite L] : fintype.card P = order P L ^ 2 + order P L + 1 :=
begin
  casesI nonempty_fintype L,
  obtain ⟨p, -⟩ := @exists_config P L _ _,
  let ϕ : {q // q ≠ p} ≃ Σ (l : {l : L // p ∈ l}), {q // q ∈ l.1 ∧ q ≠ p} :=
  { to_fun := λ q, ⟨⟨mk_line q.2, (mk_line_ax q.2).2⟩, q, (mk_line_ax q.2).1, q.2⟩,
    inv_fun := λ lq, ⟨lq.2, lq.2.2.2⟩,
    left_inv := λ q, subtype.ext rfl,
    right_inv := λ lq, sigma.subtype_ext (subtype.ext ((eq_or_eq (mk_line_ax lq.2.2.2).1
      (mk_line_ax lq.2.2.2).2 lq.2.2.1 lq.1.2).resolve_left lq.2.2.2)) rfl },
  classical,
  have h1 : fintype.card {q // q ≠ p} + 1 = fintype.card P,
  { apply (eq_tsub_iff_add_eq_of_le (nat.succ_le_of_lt (fintype.card_pos_iff.mpr ⟨p⟩))).mp,
    convert (fintype.card_subtype_compl _).trans (congr_arg _ (fintype.card_subtype_eq p)) },
  have h2 : ∀ l : {l : L // p ∈ l}, fintype.card {q // q ∈ l.1 ∧ q ≠ p} = order P L,
  { intro l,
    rw [←fintype.card_congr (equiv.subtype_subtype_equiv_subtype_inter (∈ l.val) (≠ p)),
      fintype.card_subtype_compl (λ (x : subtype (∈ l.val)), x.val = p), ←nat.card_eq_fintype_card],
    refine tsub_eq_of_eq_add ((point_count_eq P l.1).trans _),
    rw ← fintype.card_subtype_eq (⟨p, l.2⟩ : {q : P // q ∈ l.1}),
    simp_rw subtype.ext_iff_val },
  simp_rw [←h1, fintype.card_congr ϕ, fintype.card_sigma, h2, finset.sum_const, finset.card_univ],
  rw [←nat.card_eq_fintype_card, ←line_count, line_count_eq, smul_eq_mul, nat.succ_mul, sq],
end

lemma card_lines [finite P] [fintype L] :
  fintype.card L = order P L ^ 2 + order P L + 1 :=
(card_points (dual L) (dual P)).trans (congr_arg (λ n, n ^ 2 + n + 1) (dual.order P L))

end projective_plane

end configuration
