/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/

import group_theory.general_commutator

/-!

# Nilpotent groups

A basic API for nilpotent groups, that is, groups for which the upper central series
reaches `⊥`.

## Main definitions

Recall that if `H K : subgroup G` then `⁅H, K⁆ : subgroup G` is the subgroup of `G` generated
by the commutators. Recall also Lean's conventions that `⊤` denotes the subgroup `G` of `G`,
and `⊥` denotes the trivial subgroup `{1}`.

* `upper_central_series G : ℕ → subgroup G` : the upper central series of a group `G`.
     This is an increasing sequence of normal subgroups `H n` of `G` starting at `⊥` and
     with the property that `H (n + 1) / H n` is the centre of `G / H n`.
* `lower_central_series G : ℕ → subgroup G` : the lower central series of a group `G`.
     This is a decreasing sequence of subgroups `H n` of `G` starting at `⊤` and
     with the property that `H (n + 1) = ⁅H n, G⁆`.
* `is_nilpotent` : A group G is nilpotent if its upper central series reaches `⊤`, or
    equivalently if its lower central series reaches `⊥`.
* `nilpotency_class` : the length of the upper central series of a nilpotent group.
* `is_ascending_central_series (H : ℕ → subgroup G) : Prop` and
* `is_descending_central_series (H : ℕ → subgroup G) : Prop` : Note that in the literature
  a "central series" for a group is usually defined to be a *finite* sequence of normal subgroups
  `H 0`, `H 1`, ..., starting at `⊤`, finishing at `⊥`, and with each `H n / H (n + 1)`
  central in `G / H (n + 1)`. In this formalisation it is convenient to have two weaker predicates
  on an infinite sequence of subgroups `H n` of `G`: we say this sequence is a descending central
  series if it starts at `G` and `⁅H n, ⊤⁆ ⊆ H (n + 1)` for all `n`. Note that this series
  may not terminate at `⊥`, and the `H i` need not be normal. Similarly a sequence is an ascending
  central series if `H 0 = ⊥` and `⁅H (n + 1), ⊤⁆ ⊆ H n` for all `n`, with no requirement
  that the series reaches `⊤` or that the `H i` are normal.

## Main theorems

Recall that `G` is *defined* to be nilpotent if the upper central series reaches `⊤`.
* `nilpotent_iff_finite_ascending_central_series` : `G` is nilpotent iff some ascending central
    series reaches `⊤`.
* `nilpotent_iff_finite_descending_central_series` : `G` is nilpotent iff some descending central
    series reaches `⊥`.
* `nilpotent_iff_lower` : `G` is nilpotent iff the lower central series reaches `⊥`.

## Warning

A "central series" is usually defined to be a finite sequence of normal subgroups going
from `⊥` to `⊤` with the property that each subquotient is contained within the centre of
the associated quotient of `G`. This means that if `G` is not nilpotent, then
none of what we have called `upper_central_series G`, `lower_central_series G` or
the sequences satisfying `is_ascending_central_series` or `is_descending_central_series`
are actually central series.

-/
variables (G : Type*) [group G]

open subgroup

/-- `upper_central_series G n` is the `n`th term in the upper central series of `G`. -/
def upper_central_series : ℕ → subgroup G
| 0 := ⊥
| (n+1) := subgroup.normal_closure {x : G | ∀ y : G, x * y * x⁻¹ * y⁻¹ ∈ upper_central_series n}

instance (G : Type*) [group G] : ∀ (n : ℕ), normal (upper_central_series G n)
| 0 := subgroup.bot_normal
| (n+1) := subgroup.normal_closure_normal

lemma upper_central_series_zero_def (G : Type*) [group G] : upper_central_series G 0 = ⊥ := rfl

/-- An auxiliary definition, which ultimately will equal the upper central series. -/
private def upper_central_series_aux : ℕ → subgroup G
| 0 := ⊥
| (n+1) :=
  { carrier := {x : G | ∀ y : G, x * y * x⁻¹ * y⁻¹ ∈ upper_central_series G n},
    one_mem' := λ y, by simp [subgroup.one_mem],
    mul_mem' := λ a b ha hb y, begin
      rw mul_inv_rev,
      specialize ha (b * y * b⁻¹),
      specialize hb y,
      convert subgroup.mul_mem _ ha hb using 1,
      group,
    end,
    inv_mem' := λ x hx y,
    begin
      specialize hx y⁻¹,
      rw [mul_assoc, inv_inv] at ⊢ hx,
      exact subgroup.normal.mem_comm infer_instance hx,
    end }

private def upper_central_series_aux_normal (G : Type*) [group G] :
  ∀ (n : ℕ), normal (upper_central_series_aux G n)
| 0 := subgroup.bot_normal
| (n+1) := ⟨begin
  intros g hg h y,
  specialize hg (h⁻¹ * y * h),
  simp only [mul_assoc],
  refine subgroup.normal.mem_comm infer_instance _,
  convert hg using 1,
  group,
end⟩

local attribute [instance] upper_central_series_aux_normal

private lemma upper_central_series_eq_aux {G : Type*} [group G] (n : ℕ) :
  upper_central_series G n = upper_central_series_aux G n :=
begin
  cases n,
  { refl },
  { rw ← normal_closure_eq_self (upper_central_series_aux G n.succ),
    refl },
end

/-- The `n+1`st term of the upper central series `H i` has underlying set equal to the `x` such
that `⁅x,G⁆ ⊆ H n`-/
lemma mem_upper_central_series_succ_iff {G : Type*} [group G] (n : ℕ) (x : G) :
  x ∈ upper_central_series G (n + 1) ↔
  ∀ y : G, x * y * x⁻¹ * y⁻¹ ∈ upper_central_series G n :=
begin
  rw upper_central_series_eq_aux,
  refl,
end

/-- A group `G` is nilpotent if its upper central series is eventually `G`. -/
class is_nilpotent (G : Type*) [group G] : Prop :=
(nilpotent [] : ∃ n : ℕ, upper_central_series G n = ⊤)

section classical

open_locale classical

/-- The nilpotency class of a nilpotent group is the small natural `n` such that
the `n`'th term of the upper central series is `G`. -/
noncomputable def nilpotency_class (G : Type*) [group G] [is_nilpotent G] : ℕ :=
nat.find (is_nilpotent.nilpotent G)

end classical

variable {G}

/-- A sequence of subgroups of `G` is an ascending central series if `H 0` is trivial and
  `⁅H (n + 1), G⁆ ⊆ H n` for all `n`. Note that we do not require that `H n = G` for some `n`. -/
def is_ascending_central_series (H : ℕ → subgroup G) := H 0 = ⊥ ∧
  ∀ (x : G) (n : ℕ), x ∈ H (n + 1) → ∀ g, x * g * x⁻¹ * g⁻¹ ∈ H n

/-- A sequence of subgroups of `G` is a descending central series if `H 0` is `G` and
  `⁅H n, G⁆ ⊆ H (n + 1)` for all `n`. Note that we do not requre that `H n = {1}` for some `n`. -/
def is_descending_central_series (H : ℕ → subgroup G) := H 0 = ⊤ ∧
  ∀ (x : G) (n : ℕ), x ∈ H n → ∀ g, x * g * x⁻¹ * g⁻¹ ∈ H (n + 1)

/-- Any ascending central series for a group is bounded above by the upper central series. -/
lemma ascending_central_series_le_upper (H : ℕ → subgroup G) (hH : is_ascending_central_series H) :
  ∀ n : ℕ, H n ≤ upper_central_series G n
| 0 := hH.1.symm ▸ le_refl ⊥
| (n + 1) := begin
  specialize ascending_central_series_le_upper n,
  intros x hx,
  have := hH.2 x n hx,
  rw mem_upper_central_series_succ_iff,
  intro y,
  apply ascending_central_series_le_upper,
  apply this,
end

variable (G)

/-- The upper central series of a group is an ascending central series. -/
lemma upper_central_series_is_ascending_central_series :
  is_ascending_central_series (upper_central_series G) :=
begin
  split, refl,
  intros x n,
  rw upper_central_series_eq_aux,
  exact id,
end

/-- A group `G` is nilpotent iff there exists an ascending central series which reaches `G` in
  finitely many steps. -/
theorem nilpotent_iff_finite_ascending_central_series :
  is_nilpotent G ↔ ∃ H : ℕ → subgroup G, is_ascending_central_series H ∧ ∃ n : ℕ, H n = ⊤ :=
begin
  split,
  { intro h,
    use upper_central_series G,
    refine ⟨upper_central_series_is_ascending_central_series G, _⟩,
    exact h.1 },
  { rintro ⟨H, hH, n, hn⟩,
    use n,
    have := ascending_central_series_le_upper H hH n,
    rw hn at this,
    exact eq_top_iff.mpr this }
end

/-- A group `G` is nilpotent iff there exists a descending central series which reaches the
  trivial group in a finite time. -/
theorem nilpotent_iff_finite_descending_central_series :
  is_nilpotent G ↔ ∃ H : ℕ → subgroup G, is_descending_central_series H ∧ ∃ n : ℕ, H n = ⊥ :=
begin
  rw nilpotent_iff_finite_ascending_central_series,
  split,
  { rintro ⟨H, ⟨h0, hH⟩, n, hn⟩,
    use (λ m, H (n - m)),
    split,
    { refine ⟨hn, λ x m hx g, _⟩,
      dsimp at hx,
      by_cases hm : n ≤ m,
      { have hnm : n - m = 0 := nat.sub_eq_zero_of_le hm,
        rw [hnm, h0, subgroup.mem_bot] at hx,
        subst hx,
        convert subgroup.one_mem _,
        group },
      { push_neg at hm,
        apply hH,
        convert hx,
        rw nat.sub_succ,
        exact nat.succ_pred_eq_of_pos (nat.sub_pos_of_lt hm) } },
    { use n,
      rwa nat.sub_self } },
  { rintro ⟨H, ⟨h0, hH⟩, n, hn⟩,
    use (λ m, H (n - m)),
    split,
    { refine ⟨hn, λ x m hx g, _⟩,
      dsimp at hx,
      by_cases hm : n ≤ m,
      { have hnm : n - m = 0 := nat.sub_eq_zero_of_le hm,
        dsimp only,
        rw [hnm, h0],
        exact mem_top _ },
      { push_neg at hm,
        dsimp only,
        convert hH x _ hx g,
        rw nat.sub_succ,
        exact (nat.succ_pred_eq_of_pos (nat.sub_pos_of_lt hm)).symm } },
    { use n,
      rwa nat.sub_self } },
end

/-- The lower central series of a group `G` is a sequence `H n` of subgroups of `G`, defined
  by `H 0` is all of `G` and for `n≥1`, `H (n + 1) = ⁅H n, G⁆` -/
def lower_central_series (G : Type*) [group G] : ℕ → subgroup G
| 0 := ⊤
| (n+1) := ⁅lower_central_series n, ⊤⁆

variable {G}

/-- The lower central series of a group is a descending central series. -/
theorem lower_central_series_is_descending_central_series :
  is_descending_central_series (lower_central_series G) :=
begin
  split, refl,
  intros x n hxn g,
  exact general_commutator_containment _ _ hxn (subgroup.mem_top g),
end

/-- Any descending central series for a group is bounded below by the lower central series. -/
lemma descending_central_series_ge_lower (H : ℕ → subgroup G)
  (hH : is_descending_central_series H) : ∀ n : ℕ, lower_central_series G n ≤ H n
| 0 := hH.1.symm ▸ le_refl ⊤
| (n + 1) := begin
  specialize descending_central_series_ge_lower n,
  apply (general_commutator_le _ _ _).2,
  intros x hx q _,
  exact hH.2 x n (descending_central_series_ge_lower hx) q,
end

/-- A group is nilpotent if and only if its lower central series eventually reaches
  the trivial subgroup. -/
theorem nilpotent_iff_lower : is_nilpotent G ↔ ∃ n, lower_central_series G n = ⊥ :=
begin
  rw nilpotent_iff_finite_descending_central_series,
  split,
  { rintro ⟨H, ⟨h0, hs⟩, n, hn⟩,
    use n,
    have := descending_central_series_ge_lower H ⟨h0, hs⟩ n,
    rw hn at this,
    exact eq_bot_iff.mpr this },
  { intro h,
    use [lower_central_series G, lower_central_series_is_descending_central_series, h] },
end
