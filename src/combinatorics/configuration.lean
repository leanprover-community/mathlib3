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
* `configuration.has_lines.card_le`: `has_lines` implies `|P| ≤ |L|`.
* `configuration.has_points.card_le`: `has_points` implies `|L| ≤ |P|`.
* `configuration.has_lines.has_points`: `has_lines` and `|P| = |L|` implies `has_points`.
* `configuration.has_points.has_lines`: `has_points` and `|P| = |L|` implies `has_lines`.
Together, these four statements say that any two of the following properties imply the third:
(a) `has_lines`, (b) `has_points`, (c) `|P| = |L|`.

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
  mk_point_ax := λ l₁ l₂ hl, classical.some_spec (this l₁ l₂ hl) }

/-- If a nondegenerate configuration has a unique point on any two lines, and if `|P| = |L|`,
  then there is a unique line through any two points. -/
noncomputable def has_points.has_lines [has_points P L] [fintype P] [fintype L]
  (h : fintype.card P = fintype.card L) : has_lines P L :=
let this := @has_lines.has_points (dual L) (dual P) _ _ _ _ h.symm in
{ mk_line := this.mk_point,
  mk_line_ax := this.mk_point_ax }

variables (P L)

/-- A projective plane is a nondegenerate configuration in which every pair of lines has
  an intersection point, every pair of points has a line through them,
  and which has three points in general position. -/
class projective_plane extends nondegenerate P L : Type u :=
(mk_point : ∀ {l₁ l₂ : L} (h : l₁ ≠ l₂), P)
(mk_point_ax : ∀ {l₁ l₂ : L} (h : l₁ ≠ l₂), mk_point h ∈ l₁ ∧ mk_point h ∈ l₂)
(mk_line : ∀ {p₁ p₂ : P} (h : p₁ ≠ p₂), L)
(mk_line_ax : ∀ {p₁ p₂ : P} (h : p₁ ≠ p₂), p₁ ∈ mk_line h ∧ p₂ ∈ mk_line h)
(exists_config : ∃ (p₁ p₂ p₃ : P) (l₁ l₂ l₃ : L), p₁ ∉ l₂ ∧ p₁ ∉ l₃ ∧
  p₂ ∉ l₁ ∧ p₂ ∈ l₂ ∧ p₂ ∈ l₃ ∧ p₃ ∉ l₁ ∧ p₃ ∈ l₂ ∧ p₃ ∉ l₃)

namespace projective_plane

@[priority 100] -- see Note [lower instance priority]
instance has_points [h : projective_plane P L] : has_points P L := { .. h }

@[priority 100] -- see Note [lower instance priority]
instance has_lines [h : projective_plane P L] : has_lines P L := { .. h }

instance [projective_plane P L] : projective_plane (dual L) (dual P) :=
{ mk_line := @mk_point P L _ _,
  mk_line_ax := λ _ _, mk_point_ax,
  mk_point := @mk_line P L _ _,
  mk_point_ax := λ _ _, mk_line_ax,
  exists_config := by
  { obtain ⟨p₁, p₂, p₃, l₁, l₂, l₃, h₁₂, h₁₃, h₂₁, h₂₂, h₂₃, h₃₁, h₃₂, h₃₃⟩ :=
    @exists_config P L _ _,
    exact ⟨l₁, l₂, l₃, p₁, p₂, p₃, h₂₁, h₃₁, h₁₂, h₂₂, h₃₂, h₁₃, h₂₃, h₃₃⟩ },
  .. dual.nondegenerate P L }

/-- The order of a projective plane is one less than the number of lines through an arbitrary point.
Equivalently, it is one less than the number of points on an arbitrary line. -/
noncomputable def order [projective_plane P L] : ℕ :=
line_count L (classical.some (@exists_config P L _ _)) - 1

variables [fintype P] [fintype L]

lemma card_points_eq_card_lines [projective_plane P L] : fintype.card P = fintype.card L :=
le_antisymm (has_lines.card_le P L) (has_points.card_le P L)

variables {P} (L)

lemma line_count_eq_line_count [projective_plane P L] (p q : P) :
  line_count L p = line_count L q :=
begin
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

lemma point_count_eq_point_count [projective_plane P L] (l m : L) :
  point_count P l = point_count P m :=
line_count_eq_line_count (dual P) l m

variables {P L}

lemma line_count_eq_point_count [projective_plane P L] (p : P) (l : L) :
  line_count L p = point_count P l :=
exists.elim (exists_point l) (λ q hq, (line_count_eq_line_count L p q).trans
  (has_lines.line_count_eq_point_count (card_points_eq_card_lines P L) hq))

variables (P L)

lemma dual.order [projective_plane P L] : order (dual L) (dual P) = order P L :=
congr_arg (λ n, n - 1) (line_count_eq_point_count _ _)

variables {P} (L)

lemma line_count_eq [projective_plane P L] (p : P) : line_count L p = order P L + 1 :=
begin
  classical,
  obtain ⟨q, -, -, l, -, -, -, -, h, -⟩ := classical.some_spec (@exists_config P L _ _),
  rw [order, line_count_eq_line_count L p q, line_count_eq_line_count L (classical.some _) q,
      line_count, nat.card_eq_fintype_card, nat.sub_add_cancel],
  exact fintype.card_pos_iff.mpr ⟨⟨l, h⟩⟩,
end

variables (P) {L}

lemma point_count_eq [projective_plane P L] (l : L) : point_count P l = order P L + 1 :=
(line_count_eq (dual P) l).trans (congr_arg (λ n, n + 1) (dual.order P L))


variables (P) (L)

lemma order_pos [projective_plane P L] : 0 < order P L :=
begin
  obtain ⟨p₁, p₂, p₃, l₁, l₂, l₃, h₁₂, h₁₃, h₂₁, h₂₂, h₂₃, h₃₁, h₃₂, h₃₃⟩ := @exists_config P L _ _,
  classical,
  rw [← nat.succ_lt_succ_iff, nat.succ_eq_add_one (order P L), ← point_count_eq P l₂, point_count,
    nat.card_eq_fintype_card, ← finset.card_univ],
  have : ({⟨p₂, h₂₂⟩, ⟨p₃, h₃₂⟩} : finset {p // p ∈ l₂}).card ≤ fintype.card {p // p ∈ l₂} :=
    finset.card_le_of_subset (finset.subset_univ _),
  rwa [finset.card_insert_eq_ite, if_neg, finset.card_singleton] at this,
  { simp only [finset.mem_singleton], rintro rfl, contradiction }
end

variables {P} (L)

lemma one_lt_line_count [projective_plane P L] (p : P) : 1 < line_count L p :=
by simpa only [line_count_eq L p, nat.succ_lt_succ_iff] using order_pos P L

-- better name?
lemma nontrivial_lines_through_point [projective_plane P L] (p : P) :
  nontrivial {l : L // p ∈ l} :=
begin
  classical,
  have := one_lt_line_count L p,
  rwa [line_count, nat.card_eq_fintype_card, fintype.one_lt_card_iff_nontrivial] at this,
end

variables (P) {L}

lemma one_lt_point_count [projective_plane P L] (l : L) : 1 < point_count P l :=
by simpa only [point_count_eq P l, nat.succ_lt_succ_iff] using order_pos P L

-- better name?
lemma nontrivial_line [projective_plane P L] (l : L) : nontrivial {p : P // p ∈ l} :=
@nontrivial_lines_through_point (dual L) (dual P) _ _ _ _ l

variables (P) (L)

open finset

lemma card_points' [projective_plane P L] : fintype.card P = order P L ^ 2 + order P L + 1 :=
begin
  let x : P := (classical.some (@exists_config P L _ _)),
  let Lx := {l : L // x ∈ l},
  let P' := ↥({x}ᶜ : set P),
  classical,
  suffices h : fintype.card P' = (order P L + 1) * order P L,
  { let e := (equiv.set.sum_compl ({x} : set P)).symm.trans (equiv.sum_comm _ _),
    rw [fintype.card_congr e, fintype.card_sum, set.card_singleton, h, pow_two, add_mul, one_mul] },
  let f : P' → Lx := λ p, ⟨mk_line p.2, (mk_line_ax p.2).2⟩,
  have hf' : ∀ y l, f y = l ↔ (y:P) ∈ (l:L),
  { intros y l, refine ⟨by rintro rfl; exact (mk_line_ax y.2).1, λ h, subtype.eq _⟩,
    exact (has_lines.exists_unique_line P L y x y.2).unique (mk_line_ax y.2) ⟨h,l.2⟩, },
  have hf : finset.image f univ = univ,
  { refine le_antisymm (subset_univ _) (λ l hl, _),
    obtain ⟨y, hy⟩ := @exists_ne _ (nontrivial_line P l.1) ⟨x, l.2⟩,
    rw [ne.def, subtype.ext_iff] at hy,
    simp only [hf', exists_prop, mem_univ, set_coe.exists, set.mem_singleton_iff,
      mem_image, exists_true_left, subtype.coe_mk, set.mem_compl_eq],
    exact ⟨y, hy, y.2⟩, },
  have hLx : fintype.card Lx = order P L + 1,
  { rw [← line_count_eq L x, line_count, nat.card_eq_fintype_card], },
  suffices hfib : ∀ l, (univ.filter (λ (x : P'), f x = l)).card = order P L,
  { refine (card_eq_sum_card_image f univ).trans _,
    simp only [hfib, sum_const, nsmul_eq_mul, nat.cast_id, hf, card_univ, hLx] },
  intro l,
  rw [← add_left_inj 1, eq_comm],
  calc order P L + 1
      = (univ.filter (λ (y : P), y ∈ l.val)).card : _
  ... = (univ.filter (λ (y : P), y = x ∨ (y ≠ x ∧ y ∈ l.val))).card : _
  ... = (univ.filter (λ (x : P'), f x = l)).card + 1 : _,
  { rw [← point_count_eq P l.1, point_count, nat.card_eq_fintype_card, fintype.card_subtype] },
  { congr, ext y, simp only [or_and_distrib_left, em, true_and],
    rw [iff.comm, or_iff_right_iff_imp], intro h, rw h, exact l.2 },
  have aux : disjoint (univ.filter (λ (a : P), a = x)) (univ.filter (λ a, a ≠ x ∧ a ∈ l.val)),
  { rw disjoint_filter, simp, },
  rw [filter_or, card_disjoint_union aux, add_comm, ← card_map (function.embedding.subtype _)],
  simp only [hf', ← card_singleton x],
  congr' 2,
  { ext y,
    simp only [true_and, exists_prop, function.embedding.coe_subtype, mem_univ,
      mem_map, set.mem_singleton_iff, exists_and_distrib_right, exists_eq_right, ne.def,
      subtype.exists, mem_filter, subtype.coe_mk, set.mem_compl_eq, subtype.val_eq_coe],
    rw ← exists_prop, apply exists_congr, intro h,
    erw mem_filter, simp only [true_and, mem_univ, subtype.coe_mk], },
  { ext y, simp only [true_and, mem_univ, mem_singleton, mem_filter], },
end

/-- An auxillary bijection for `card_points`. -/
def card_points_aux (α β : Type u) (γ : β → Type u) [decidable_eq α] [Π b : β, decidable_eq (γ b)]
  (f : ∀ {a₁ a₂ : α} (h : a₁ ≠ a₂), Σ b : β, γ b × γ b) (g : ∀ b : β, γ b → α)
  (h1 : ∀ {a₁ a₂ : α} (h : a₁ ≠ a₂), g (f h).1 (f h).2.1 = a₁)
  (h2 : ∀ {a₁ a₂ : α} (h : a₁ ≠ a₂), g (f h).1 (f h).2.2 = a₂)
  (h3 : ∀ b : β, function.injective (g b))
  (h4 : ∀ {b : Σ b : β, γ b × γ b} (h : b.2.1 ≠ b.2.2), f ((h3 b.1).ne h) = b) :
  (α × α ⊕ Σ b : β, γ b) ≃ α ⊕ Σ b : β, γ b × γ b :=
{ to_fun := sum.elim (λ a, if h : a.1 = a.2 then sum.inl a.1 else sum.inr (f h))
    (λ b, sum.inr ⟨b.1, (b.2, b.2)⟩),
  inv_fun := sum.elim (λ a, sum.inl (a, a))
    (λ b, if h : b.2.1 = b.2.2 then sum.inr ⟨b.1, b.2.1⟩ else sum.inl (g b.1 b.2.1, g b.1 b.2.2)),
  left_inv := by
  { rintros (a | b),
    { by_cases h : a.1 = a.2,
      { rw [sum.elim_inl, dif_pos h, sum.elim_inl, sum.inl.inj_iff],
        exact prod.ext rfl h },
      { rw [sum.elim_inl, dif_neg h, sum.elim_inr, h1, h2, prod.mk.eta, dif_neg],
        refine λ h', h _,
        rw [←h1 h, h', h2] } },
    { rw [sum.elim_inr, sum.elim_inr, dif_pos rfl, sigma.eta] }, },
  right_inv := by
  { rintros (a | b),
    { rw [sum.elim_inl, sum.elim_inl, dif_pos rfl] },
    { by_cases h : b.2.1 = b.2.2,
      { rw [sum.elim_inr, dif_pos h, sum.elim_inr, sum.inr.inj_iff],
        exact sigma.ext rfl (heq_of_eq (prod.ext rfl h)) },
      { rw [sum.elim_inr, dif_neg h, sum.elim_inl, dif_neg ((h3 b.1).ne h), h4] } } } }

variables (P L)

lemma card_points [projective_plane P L] : fintype.card P = order P L ^ 2 + order P L + 1 :=
begin
  classical,
  have h1 : ∀ l : L, fintype.card {p : P // p ∈ l} = order P L + 1 :=
  λ l, nat.card_eq_fintype_card.symm.trans (point_count_eq P l),
  let h := fintype.card_congr (card_points_aux P L (λ l, {p : P // p ∈ l})
    (λ p₁ p₂ h, ⟨mk_line h, ⟨p₁, (mk_line_ax h).1⟩, ⟨p₂, (mk_line_ax h).2⟩⟩)
    (λ l p, p) (λ p₁ p₂ h, rfl) (λ p₁ p₂ h, rfl) (λ l, subtype.coe_injective) _),
  { simp_rw [fintype.card_sum, fintype.card_sigma, fintype.card_prod, h1,
      finset.sum_const, smul_eq_mul, finset.card_univ, ←card_points_eq_card_lines] at h,
    rwa [nat.mul_succ, ←add_assoc, add_comm, add_right_inj, ←mul_add, mul_right_inj',
      nat.succ_mul_succ_eq, add_assoc, add_comm (order P L), ←add_assoc, add_left_inj, ←sq] at h,
    exact (fintype.card_pos_iff.mpr (nonempty_of_exists (@exists_config P L _ _))).ne' },
  { rintros ⟨l, ⟨p₁, hp₁⟩, ⟨p₂, hp₂⟩⟩ h,
    rw [ne, subtype.ext_iff, subtype.coe_mk, subtype.coe_mk] at h,
    have key := (eq_or_eq (mk_line_ax h).1 (mk_line_ax h).2 hp₁ hp₂).resolve_left h,
    subst key,
    refl },
end

lemma card_lines [projective_plane P L] : fintype.card L = order P L ^ 2 + order P L + 1 :=
(card_points (dual L) (dual P)).trans (congr_arg (λ n, n ^ 2 + n + 1) (dual.order P L))

end projective_plane

end configuration
