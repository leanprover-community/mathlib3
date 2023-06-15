/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Ines Wright, Joachim Breitner
-/

import group_theory.quotient_group
import group_theory.solvable
import group_theory.p_group
import group_theory.sylow
import data.nat.factorization.basic
import tactic.tfae

/-!

# Nilpotent groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

An API for nilpotent groups, that is, groups for which the upper central series
reaches `⊤`.

## Main definitions

Recall that if `H K : subgroup G` then `⁅H, K⁆ : subgroup G` is the subgroup of `G` generated
by the commutators `hkh⁻¹k⁻¹`. Recall also Lean's conventions that `⊤` denotes the
subgroup `G` of `G`, and `⊥` denotes the trivial subgroup `{1}`.

* `upper_central_series G : ℕ → subgroup G` : the upper central series of a group `G`.
     This is an increasing sequence of normal subgroups `H n` of `G` with `H 0 = ⊥` and
     `H (n + 1) / H n` is the centre of `G / H n`.
* `lower_central_series G : ℕ → subgroup G` : the lower central series of a group `G`.
     This is a decreasing sequence of normal subgroups `H n` of `G` with `H 0 = ⊤` and
     `H (n + 1) = ⁅H n, G⁆`.
* `is_nilpotent` : A group G is nilpotent if its upper central series reaches `⊤`, or
    equivalently if its lower central series reaches `⊥`.
* `nilpotency_class` : the length of the upper central series of a nilpotent group.
* `is_ascending_central_series (H : ℕ → subgroup G) : Prop` and
* `is_descending_central_series (H : ℕ → subgroup G) : Prop` : Note that in the literature
    a "central series" for a group is usually defined to be a *finite* sequence of normal subgroups
    `H 0`, `H 1`, ..., starting at `⊤`, finishing at `⊥`, and with each `H n / H (n + 1)`
    central in `G / H (n + 1)`. In this formalisation it is convenient to have two weaker predicates
    on an infinite sequence of subgroups `H n` of `G`: we say a sequence is a *descending central
    series* if it starts at `G` and `⁅H n, ⊤⁆ ⊆ H (n + 1)` for all `n`. Note that this series
    may not terminate at `⊥`, and the `H i` need not be normal. Similarly a sequence is an
    *ascending central series* if `H 0 = ⊥` and `⁅H (n + 1), ⊤⁆ ⊆ H n` for all `n`, again with no
    requirement that the series reaches `⊤` or that the `H i` are normal.

## Main theorems

`G` is *defined* to be nilpotent if the upper central series reaches `⊤`.
* `nilpotent_iff_finite_ascending_central_series` : `G` is nilpotent iff some ascending central
    series reaches `⊤`.
* `nilpotent_iff_finite_descending_central_series` : `G` is nilpotent iff some descending central
    series reaches `⊥`.
* `nilpotent_iff_lower` : `G` is nilpotent iff the lower central series reaches `⊥`.
* The `nilpotency_class` can likeways be obtained from these equivalent
  definitions, see `least_ascending_central_series_length_eq_nilpotency_class`,
  `least_descending_central_series_length_eq_nilpotency_class` and
  `lower_central_series_length_eq_nilpotency_class`.
* If `G` is nilpotent, then so are its subgroups, images, quotients and preimages.
  Binary and finite products of nilpotent groups are nilpotent.
  Infinite products are nilpotent if their nilpotent class is bounded.
  Corresponding lemmas about the `nilpotency_class` are provided.
* The `nilpotency_class` of `G ⧸ center G` is given explicitly, and an induction principle
  is derived from that.
* `is_nilpotent.to_is_solvable`: If `G` is nilpotent, it is solvable.


## Warning

A "central series" is usually defined to be a finite sequence of normal subgroups going
from `⊥` to `⊤` with the property that each subquotient is contained within the centre of
the associated quotient of `G`. This means that if `G` is not nilpotent, then
none of what we have called `upper_central_series G`, `lower_central_series G` or
the sequences satisfying `is_ascending_central_series` or `is_descending_central_series`
are actually central series. Note that the fact that the upper and lower central series
are not central series if `G` is not nilpotent is a standard abuse of notation.

-/

open subgroup

section with_group

variables {G : Type*} [group G] (H : subgroup G) [normal H]

/-- If `H` is a normal subgroup of `G`, then the set `{x : G | ∀ y : G, x*y*x⁻¹*y⁻¹ ∈ H}`
is a subgroup of `G` (because it is the preimage in `G` of the centre of the
quotient group `G/H`.)
-/
def upper_central_series_step : subgroup G :=
{ carrier := {x : G | ∀ y : G, x * y * x⁻¹ * y⁻¹ ∈ H},
  one_mem' := λ y, by simp [subgroup.one_mem],
  mul_mem' := λ a b ha hb y, begin
    convert subgroup.mul_mem _ (ha (b * y * b⁻¹)) (hb y) using 1,
    group,
  end,
  inv_mem' := λ x hx y, begin
    specialize hx y⁻¹,
    rw [mul_assoc, inv_inv] at ⊢ hx,
    exact subgroup.normal.mem_comm infer_instance hx,
  end }

lemma mem_upper_central_series_step (x : G) :
  x ∈ upper_central_series_step H ↔ ∀ y, x * y * x⁻¹ * y⁻¹ ∈ H := iff.rfl

open quotient_group

/-- The proof that `upper_central_series_step H` is the preimage of the centre of `G/H` under
the canonical surjection. -/
lemma upper_central_series_step_eq_comap_center :
  upper_central_series_step H = subgroup.comap (mk' H) (center (G ⧸ H)) :=
begin
  ext,
  rw [mem_comap, mem_center_iff, forall_coe],
  apply forall_congr,
  intro y,
  rw [coe_mk', ←quotient_group.coe_mul, ←quotient_group.coe_mul, eq_comm, eq_iff_div_mem,
    div_eq_mul_inv, mul_inv_rev, mul_assoc],
end

instance : normal (upper_central_series_step H) :=
begin
  rw upper_central_series_step_eq_comap_center,
  apply_instance,
end

variable (G)

/-- An auxiliary type-theoretic definition defining both the upper central series of
a group, and a proof that it is normal, all in one go. -/
def upper_central_series_aux : ℕ → Σ' (H : subgroup G), normal H
| 0 := ⟨⊥, infer_instance⟩
| (n + 1) := let un := upper_central_series_aux n, un_normal := un.2 in
   by exactI ⟨upper_central_series_step un.1, infer_instance⟩

/-- `upper_central_series G n` is the `n`th term in the upper central series of `G`. -/
def upper_central_series (n : ℕ) : subgroup G := (upper_central_series_aux G n).1

instance (n : ℕ) : normal (upper_central_series G n) := (upper_central_series_aux G n).2

@[simp] lemma upper_central_series_zero : upper_central_series G 0 = ⊥ := rfl

@[simp] lemma upper_central_series_one : upper_central_series G 1 = center G :=
begin
  ext,
  simp only [upper_central_series, upper_central_series_aux, upper_central_series_step, center,
    set.center, mem_mk, mem_bot, set.mem_set_of_eq],
  exact forall_congr (λ y, by rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul, eq_comm]),
end

/-- The `n+1`st term of the upper central series `H i` has underlying set equal to the `x` such
that `⁅x,G⁆ ⊆ H n`-/
lemma mem_upper_central_series_succ_iff (n : ℕ) (x : G) :
  x ∈ upper_central_series G (n + 1) ↔
  ∀ y : G, x * y * x⁻¹ * y⁻¹ ∈ upper_central_series G n := iff.rfl

-- is_nilpotent is already defined in the root namespace (for elements of rings).
/-- A group `G` is nilpotent if its upper central series is eventually `G`. -/
class group.is_nilpotent (G : Type*) [group G] : Prop :=
(nilpotent [] : ∃ n : ℕ, upper_central_series G n = ⊤)

open group

variable {G}

/-- A sequence of subgroups of `G` is an ascending central series if `H 0` is trivial and
  `⁅H (n + 1), G⁆ ⊆ H n` for all `n`. Note that we do not require that `H n = G` for some `n`. -/
def is_ascending_central_series (H : ℕ → subgroup G) : Prop :=
  H 0 = ⊥ ∧ ∀ (x : G) (n : ℕ), x ∈ H (n + 1) → ∀ g, x * g * x⁻¹ * g⁻¹ ∈ H n

/-- A sequence of subgroups of `G` is a descending central series if `H 0` is `G` and
  `⁅H n, G⁆ ⊆ H (n + 1)` for all `n`. Note that we do not requre that `H n = {1}` for some `n`. -/
def is_descending_central_series (H : ℕ → subgroup G) := H 0 = ⊤ ∧
  ∀ (x : G) (n : ℕ), x ∈ H n → ∀ g, x * g * x⁻¹ * g⁻¹ ∈ H (n + 1)

/-- Any ascending central series for a group is bounded above by the upper central series. -/
lemma ascending_central_series_le_upper (H : ℕ → subgroup G) (hH : is_ascending_central_series H) :
  ∀ n : ℕ, H n ≤ upper_central_series G n
| 0 := hH.1.symm ▸ le_refl ⊥
| (n + 1) := begin
  intros x hx,
  rw mem_upper_central_series_succ_iff,
  exact λ y, ascending_central_series_le_upper n (hH.2 x n hx y),
end

variable (G)

/-- The upper central series of a group is an ascending central series. -/
lemma upper_central_series_is_ascending_central_series :
  is_ascending_central_series (upper_central_series G) :=
⟨rfl, λ x n h, h⟩

lemma upper_central_series_mono : monotone (upper_central_series G) :=
begin
  refine monotone_nat_of_le_succ _,
  intros n x hx y,
  rw [mul_assoc, mul_assoc, ← mul_assoc y x⁻¹ y⁻¹],
  exact mul_mem hx (normal.conj_mem (upper_central_series.subgroup.normal G n) x⁻¹ (inv_mem hx) y)
end

/-- A group `G` is nilpotent iff there exists an ascending central series which reaches `G` in
  finitely many steps. -/
theorem nilpotent_iff_finite_ascending_central_series :
  is_nilpotent G ↔ ∃ n : ℕ, ∃ H : ℕ → subgroup G, is_ascending_central_series H ∧ H n = ⊤ :=
begin
  split,
  { rintro ⟨n, nH⟩,
    refine ⟨_, _, upper_central_series_is_ascending_central_series G, nH⟩ },
  { rintro ⟨n, H, hH, hn⟩,
    use n,
    rw [eq_top_iff, ←hn],
    exact ascending_central_series_le_upper H hH n }
end

lemma is_decending_rev_series_of_is_ascending
  {H: ℕ → subgroup G} {n : ℕ} (hn : H n = ⊤) (hasc : is_ascending_central_series H) :
  is_descending_central_series (λ (m : ℕ), H (n - m)) :=
begin
  cases hasc with h0 hH,
  refine ⟨hn, λ x m hx g, _⟩,
  dsimp at hx,
  by_cases hm : n ≤ m,
  { rw [tsub_eq_zero_of_le hm, h0, subgroup.mem_bot] at hx,
    subst hx,
    convert subgroup.one_mem _,
    group },
  { push_neg at hm,
    apply hH,
    convert hx,
    rw [tsub_add_eq_add_tsub (nat.succ_le_of_lt hm), nat.succ_sub_succ] },
end

lemma is_ascending_rev_series_of_is_descending
  {H: ℕ → subgroup G} {n : ℕ} (hn : H n = ⊥) (hdesc : is_descending_central_series H) :
  is_ascending_central_series (λ (m : ℕ), H (n - m)) :=
begin
  cases hdesc with h0 hH,
  refine ⟨hn, λ x m hx g, _⟩,
  dsimp only at hx ⊢,
  by_cases hm : n ≤ m,
  { have hnm : n - m = 0 := tsub_eq_zero_iff_le.mpr hm,
    rw [hnm, h0],
    exact mem_top _ },
  { push_neg at hm,
    convert hH x _ hx g,
    rw [tsub_add_eq_add_tsub (nat.succ_le_of_lt hm), nat.succ_sub_succ] },
end

/-- A group `G` is nilpotent iff there exists a descending central series which reaches the
  trivial group in a finite time. -/
theorem nilpotent_iff_finite_descending_central_series :
  is_nilpotent G ↔ ∃ n : ℕ, ∃ H : ℕ → subgroup G, is_descending_central_series H ∧ H n = ⊥ :=
begin
  rw nilpotent_iff_finite_ascending_central_series,
  split,
  { rintro ⟨n, H, hH, hn⟩,
    refine ⟨n, λ m, H (n - m), is_decending_rev_series_of_is_ascending G hn hH, _⟩,
    rw tsub_self,
    exact hH.1 },
  { rintro ⟨n, H, hH, hn⟩,
    refine ⟨n, λ m, H (n - m), is_ascending_rev_series_of_is_descending G hn hH, _⟩,
    rw tsub_self,
    exact hH.1 },
end

/-- The lower central series of a group `G` is a sequence `H n` of subgroups of `G`, defined
  by `H 0` is all of `G` and for `n≥1`, `H (n + 1) = ⁅H n, G⁆` -/
def lower_central_series (G : Type*) [group G] : ℕ → subgroup G
| 0 := ⊤
| (n+1) := ⁅lower_central_series n, ⊤⁆

variable {G}

@[simp] lemma lower_central_series_zero : lower_central_series G 0 = ⊤ := rfl

@[simp] lemma lower_central_series_one : lower_central_series G 1 = commutator G := rfl

lemma mem_lower_central_series_succ_iff (n : ℕ) (q : G) :
  q ∈ lower_central_series G (n + 1) ↔
  q ∈ closure {x | ∃ (p ∈ lower_central_series G n) (q ∈ (⊤ : subgroup G)), p * q * p⁻¹ * q⁻¹ = x}
:= iff.rfl

lemma lower_central_series_succ (n : ℕ) :
  lower_central_series G (n + 1) =
  closure {x | ∃ (p ∈ lower_central_series G n) (q ∈ (⊤ : subgroup G)), p * q * p⁻¹ * q⁻¹ = x} :=
rfl

instance (n : ℕ) : normal (lower_central_series G n) :=
begin
  induction n with d hd,
  { exact (⊤ : subgroup G).normal_of_characteristic },
  { exactI subgroup.commutator_normal (lower_central_series G d) ⊤ },
end

lemma lower_central_series_antitone :
  antitone (lower_central_series G) :=
begin
  refine antitone_nat_of_succ_le (λ n x hx, _),
  simp only [mem_lower_central_series_succ_iff, exists_prop, mem_top, exists_true_left, true_and]
    at hx,
  refine closure_induction hx _ (subgroup.one_mem _) (@subgroup.mul_mem _ _ _)
    (@subgroup.inv_mem _ _ _),
  rintros y ⟨z, hz, a, ha⟩,
  rw [← ha, mul_assoc, mul_assoc, ← mul_assoc a z⁻¹ a⁻¹],
  exact mul_mem hz (normal.conj_mem (lower_central_series.subgroup.normal n) z⁻¹ (inv_mem hz) a)
end

/-- The lower central series of a group is a descending central series. -/
theorem lower_central_series_is_descending_central_series :
  is_descending_central_series (lower_central_series G) :=
begin
  split, refl,
  intros x n hxn g,
  exact commutator_mem_commutator hxn (mem_top g),
end

/-- Any descending central series for a group is bounded below by the lower central series. -/
lemma descending_central_series_ge_lower (H : ℕ → subgroup G)
  (hH : is_descending_central_series H) : ∀ n : ℕ, lower_central_series G n ≤ H n
| 0 := hH.1.symm ▸ le_refl ⊤
| (n + 1) := commutator_le.mpr (λ x hx q _, hH.2 x n (descending_central_series_ge_lower n hx) q)

/-- A group is nilpotent if and only if its lower central series eventually reaches
  the trivial subgroup. -/
theorem nilpotent_iff_lower_central_series : is_nilpotent G ↔ ∃ n, lower_central_series G n = ⊥ :=
begin
  rw nilpotent_iff_finite_descending_central_series,
  split,
  { rintro ⟨n, H, ⟨h0, hs⟩, hn⟩,
    use n,
    rw [eq_bot_iff, ←hn],
    exact descending_central_series_ge_lower H ⟨h0, hs⟩ n },
  { rintro ⟨n, hn⟩,
    exact ⟨n, lower_central_series G, lower_central_series_is_descending_central_series, hn⟩ },
end

section classical

open_locale classical

variables [hG : is_nilpotent G]
include hG

variable (G)

/-- The nilpotency class of a nilpotent group is the smallest natural `n` such that
the `n`'th term of the upper central series is `G`. -/
noncomputable def group.nilpotency_class : ℕ :=
nat.find (is_nilpotent.nilpotent G)

variable {G}

@[simp]
lemma upper_central_series_nilpotency_class :
  upper_central_series G (group.nilpotency_class G) = ⊤ :=
nat.find_spec (is_nilpotent.nilpotent G)

lemma upper_central_series_eq_top_iff_nilpotency_class_le {n : ℕ} :
  (upper_central_series G n = ⊤) ↔ (group.nilpotency_class G ≤ n) :=
begin
  split,
  { intro h,
    exact (nat.find_le h), },
  { intro h,
    apply eq_top_iff.mpr,
    rw ← upper_central_series_nilpotency_class,
    exact (upper_central_series_mono _ h), }
end

/-- The nilpotency class of a nilpotent `G` is equal to the smallest `n` for which an ascending
central series reaches `G` in its `n`'th term. -/
lemma least_ascending_central_series_length_eq_nilpotency_class :
  nat.find ((nilpotent_iff_finite_ascending_central_series G).mp hG) = group.nilpotency_class G :=
begin
  refine le_antisymm (nat.find_mono _) (nat.find_mono _),
  { intros n hn,
    exact ⟨upper_central_series G, upper_central_series_is_ascending_central_series G, hn ⟩, },
  { rintros n ⟨H, ⟨hH, hn⟩⟩,
    rw [←top_le_iff, ←hn],
    exact ascending_central_series_le_upper H hH n, }
end

/-- The nilpotency class of a nilpotent `G` is equal to the smallest `n` for which the descending
central series reaches `⊥` in its `n`'th term. -/
lemma least_descending_central_series_length_eq_nilpotency_class :
  nat.find ((nilpotent_iff_finite_descending_central_series G).mp hG) = group.nilpotency_class G :=
begin
  rw ← least_ascending_central_series_length_eq_nilpotency_class,
  refine le_antisymm (nat.find_mono _) (nat.find_mono _),
  { rintros n ⟨H, ⟨hH, hn⟩⟩,
    refine ⟨(λ m, H (n - m)), is_decending_rev_series_of_is_ascending G hn hH, _⟩,
    rw tsub_self,
    exact hH.1 },
  { rintros n ⟨H, ⟨hH, hn⟩⟩,
    refine ⟨(λ m, H (n - m)), is_ascending_rev_series_of_is_descending G hn hH, _⟩,
    rw tsub_self,
    exact hH.1 },
end

/-- The nilpotency class of a nilpotent `G` is equal to the length of the lower central series. -/
lemma lower_central_series_length_eq_nilpotency_class :
  nat.find (nilpotent_iff_lower_central_series.mp hG) = @group.nilpotency_class G _ _ :=
begin
  rw ← least_descending_central_series_length_eq_nilpotency_class,
  refine le_antisymm (nat.find_mono _) (nat.find_mono _),
  { rintros n ⟨H, ⟨hH, hn⟩⟩,
    rw [←le_bot_iff, ←hn],
    exact (descending_central_series_ge_lower H hH n), },
  { rintros n h,
    exact ⟨lower_central_series G, ⟨lower_central_series_is_descending_central_series, h⟩⟩ },
end

@[simp]
lemma lower_central_series_nilpotency_class :
  lower_central_series G (group.nilpotency_class G) = ⊥ :=
begin
  rw ← lower_central_series_length_eq_nilpotency_class,
  exact (nat.find_spec (nilpotent_iff_lower_central_series.mp _))
end

lemma lower_central_series_eq_bot_iff_nilpotency_class_le {n : ℕ} :
  (lower_central_series G n = ⊥) ↔ (group.nilpotency_class G ≤ n) :=
begin
  split,
  { intro h,
    rw ← lower_central_series_length_eq_nilpotency_class,
    exact (nat.find_le h), },
  { intro h,
    apply eq_bot_iff.mpr,
    rw ← lower_central_series_nilpotency_class,
    exact (lower_central_series_antitone h), }
end

end classical

lemma lower_central_series_map_subtype_le (H : subgroup G) (n : ℕ) :
  (lower_central_series H n).map H.subtype ≤ lower_central_series G n :=
begin
  induction n with d hd,
  { simp },
  { rw [lower_central_series_succ, lower_central_series_succ, monoid_hom.map_closure],
    apply subgroup.closure_mono,
    rintros x1 ⟨x2, ⟨x3, hx3, x4, hx4, rfl⟩, rfl⟩,
    exact ⟨x3, (hd (mem_map.mpr ⟨x3, hx3, rfl⟩)), x4, by simp⟩ }
end

/-- A subgroup of a nilpotent group is nilpotent -/
instance subgroup.is_nilpotent (H : subgroup G) [hG : is_nilpotent G] :
  is_nilpotent H :=
begin
  rw nilpotent_iff_lower_central_series at *,
  rcases hG with ⟨n, hG⟩,
  use n,
  have := lower_central_series_map_subtype_le H n,
  simp only [hG, set_like.le_def, mem_map, forall_apply_eq_imp_iff₂, exists_imp_distrib] at this,
  exact eq_bot_iff.mpr (λ x hx, subtype.ext (this x hx)),
end

/-- A the nilpotency class of a subgroup is less or equal the the nilpotency class of the group -/
lemma subgroup.nilpotency_class_le (H : subgroup G) [hG : is_nilpotent G] :
  group.nilpotency_class H ≤ group.nilpotency_class G :=
begin
  repeat { rw ← lower_central_series_length_eq_nilpotency_class },
  apply nat.find_mono,
  intros n hG,
  have := lower_central_series_map_subtype_le H n,
  simp only [hG, set_like.le_def, mem_map, forall_apply_eq_imp_iff₂, exists_imp_distrib] at this,
  exact eq_bot_iff.mpr (λ x hx, subtype.ext (this x hx)),
end

@[priority 100]
instance is_nilpotent_of_subsingleton [subsingleton G] : is_nilpotent G :=
nilpotent_iff_lower_central_series.2 ⟨0, subsingleton.elim ⊤ ⊥⟩

lemma upper_central_series.map {H : Type*} [group H] {f : G →* H} (h : function.surjective f)
  (n : ℕ) : subgroup.map f (upper_central_series G n) ≤ upper_central_series H n :=
begin
  induction n with d hd,
  { simp },
  { rintros _ ⟨x, hx : x ∈ upper_central_series G d.succ, rfl⟩ y',
    rcases h y' with ⟨y, rfl⟩,
    simpa using hd (mem_map_of_mem f (hx y)) }
end

lemma lower_central_series.map {H : Type*} [group H] (f : G →* H) (n : ℕ) :
  subgroup.map f (lower_central_series G n) ≤ lower_central_series H n :=
begin
  induction n with d hd,
  { simp [nat.nat_zero_eq_zero] },
  { rintros a ⟨x, hx : x ∈ lower_central_series G d.succ, rfl⟩,
    refine closure_induction hx _ (by simp [f.map_one, subgroup.one_mem _])
      (λ y z hy hz, by simp [monoid_hom.map_mul, subgroup.mul_mem _ hy hz])
      (λ y hy, by simp [f.map_inv, subgroup.inv_mem _ hy]),
    rintros a ⟨y, hy, z, ⟨-, rfl⟩⟩,
    apply mem_closure.mpr,
    exact λ K hK, hK ⟨f y, hd (mem_map_of_mem f hy), by simp [commutator_element_def]⟩ }
end

lemma lower_central_series_succ_eq_bot {n : ℕ} (h : lower_central_series G n ≤ center G) :
  lower_central_series G (n + 1) = ⊥ :=
begin
  rw [lower_central_series_succ, closure_eq_bot_iff, set.subset_singleton_iff],
  rintro x ⟨y, hy1, z, ⟨⟩, rfl⟩,
  rw [mul_assoc, ←mul_inv_rev, mul_inv_eq_one, eq_comm],
  exact mem_center_iff.mp (h hy1) z,
end

/-- The preimage of a nilpotent group is nilpotent if the kernel of the homomorphism is contained
in the center -/
lemma is_nilpotent_of_ker_le_center {H : Type*} [group H] (f : G →* H)
  (hf1 : f.ker ≤ center G) (hH : is_nilpotent H) : is_nilpotent G :=
begin
  rw nilpotent_iff_lower_central_series at *,
  rcases hH with ⟨n, hn⟩,
  use (n + 1),
  refine lower_central_series_succ_eq_bot (le_trans ((subgroup.map_eq_bot_iff _).mp _) hf1),
  exact eq_bot_iff.mpr (hn ▸ (lower_central_series.map f n)),
end

lemma nilpotency_class_le_of_ker_le_center {H : Type*} [group H] (f : G →* H)
  (hf1 : f.ker ≤ center G) (hH : is_nilpotent H) :
  @group.nilpotency_class G _ (is_nilpotent_of_ker_le_center f hf1 hH) ≤
    group.nilpotency_class H + 1 :=
begin
  rw ← lower_central_series_length_eq_nilpotency_class,
  apply nat.find_min',
  refine lower_central_series_succ_eq_bot (le_trans ((subgroup.map_eq_bot_iff _).mp _) hf1),
  apply eq_bot_iff.mpr,
  apply (le_trans (lower_central_series.map f _)),
  simp only [lower_central_series_nilpotency_class, le_bot_iff],
end

/-- The range of a surjective homomorphism from a nilpotent group is nilpotent -/
lemma nilpotent_of_surjective {G' : Type*} [group G'] [h : is_nilpotent G]
  (f : G →* G') (hf : function.surjective f) :
  is_nilpotent G' :=
begin
  unfreezingI { rcases h with ⟨n, hn⟩ },
  use n,
  apply eq_top_iff.mpr,
  calc ⊤ = f.range : symm (f.range_top_of_surjective hf)
    ... = subgroup.map f ⊤ : monoid_hom.range_eq_map _
    ... = subgroup.map f (upper_central_series G n) : by rw hn
    ... ≤ upper_central_series G' n : upper_central_series.map hf n,
end

/-- The nilpotency class of the range of a surejctive homomorphism from a
nilpotent group is less or equal the nilpotency class of the domain -/
lemma nilpotency_class_le_of_surjective
  {G' : Type*} [group G'] (f : G →* G') (hf : function.surjective f) [h : is_nilpotent G] :
  @group.nilpotency_class G' _ (nilpotent_of_surjective _ hf) ≤
    group.nilpotency_class G :=
begin
  apply nat.find_mono,
  intros n hn,
  apply eq_top_iff.mpr,
  calc ⊤ = f.range : symm (f.range_top_of_surjective hf)
    ... = subgroup.map f ⊤ : monoid_hom.range_eq_map _
    ... = subgroup.map f (upper_central_series G n) : by rw hn
    ... ≤ upper_central_series G' n : upper_central_series.map hf n,
end

/-- Nilpotency respects isomorphisms -/
lemma nilpotent_of_mul_equiv {G' : Type*} [group G'] [h : is_nilpotent G] (f : G ≃* G') :
  is_nilpotent G' :=
nilpotent_of_surjective f.to_monoid_hom (mul_equiv.surjective f)

/-- A quotient of a nilpotent group is nilpotent -/
instance nilpotent_quotient_of_nilpotent (H : subgroup G) [H.normal] [h : is_nilpotent G] :
  is_nilpotent (G ⧸ H) :=
 nilpotent_of_surjective _ (show function.surjective (quotient_group.mk' H), by tidy)

/-- The nilpotency class of a quotient of `G` is less or equal the nilpotency class of `G` -/
lemma nilpotency_class_quotient_le (H : subgroup G) [H.normal] [h : is_nilpotent G] :
  group.nilpotency_class (G ⧸ H) ≤ group.nilpotency_class G := nilpotency_class_le_of_surjective _ _

-- This technical lemma helps with rewriting the subgroup, which occurs in indices
private lemma comap_center_subst {H₁ H₂ : subgroup G} [normal H₁] [normal H₂] (h : H₁ = H₂) :
  comap (mk' H₁) (center (G ⧸ H₁)) = comap (mk' H₂) (center (G ⧸ H₂)) :=
by unfreezingI { subst h }

lemma comap_upper_central_series_quotient_center (n : ℕ) :
  comap (mk' (center G)) (upper_central_series (G ⧸ center G) n) = upper_central_series G n.succ :=
begin
  induction n with n ih,
  { simp, },
  { let Hn := upper_central_series (G ⧸ center G) n,
    calc comap (mk' (center G)) (upper_central_series_step Hn)
        = comap (mk' (center G)) (comap (mk' Hn) (center ((G ⧸ center G) ⧸ Hn))) :
        by rw upper_central_series_step_eq_comap_center
    ... = comap (mk' (comap (mk' (center G)) Hn)) (center (G ⧸ (comap (mk' (center G)) Hn))) :
        quotient_group.comap_comap_center
    ... = comap (mk' (upper_central_series G n.succ)) (center (G ⧸ upper_central_series G n.succ)) :
        comap_center_subst ih
    ... = upper_central_series_step (upper_central_series G n.succ) :
        symm (upper_central_series_step_eq_comap_center _), }
end

lemma nilpotency_class_zero_iff_subsingleton [is_nilpotent G] :
  group.nilpotency_class G = 0 ↔ subsingleton G :=
by simp [group.nilpotency_class, nat.find_eq_zero, subsingleton_iff_bot_eq_top]

/-- Quotienting the `center G` reduces the nilpotency class by 1 -/
lemma nilpotency_class_quotient_center [hH : is_nilpotent G] :
  group.nilpotency_class (G ⧸ center G) = group.nilpotency_class G - 1 :=
begin
  generalize hn : group.nilpotency_class G = n,
  rcases n with rfl | n,
  { simp [nilpotency_class_zero_iff_subsingleton] at *,
    haveI := hn,
    apply_instance, },
  { suffices : group.nilpotency_class (G ⧸ center G) = n, by simpa,
    apply le_antisymm,
    { apply upper_central_series_eq_top_iff_nilpotency_class_le.mp,
      apply (@comap_injective G _ _ _ (mk' (center G)) (surjective_quot_mk _)),
      rw [ comap_upper_central_series_quotient_center, comap_top, ← hn],
      exact upper_central_series_nilpotency_class, },
    { apply le_of_add_le_add_right,
      calc n + 1 = n.succ : rfl
        ... = group.nilpotency_class G : symm hn
        ... ≤ group.nilpotency_class (G ⧸ center G) + 1
            : nilpotency_class_le_of_ker_le_center _ (le_of_eq (ker_mk _)) _, } }
end

/-- The nilpotency class of a non-trivial group is one more than its quotient by the center -/
lemma nilpotency_class_eq_quotient_center_plus_one [hH : is_nilpotent G] [nontrivial G] :
  group.nilpotency_class G = group.nilpotency_class (G ⧸ center G) + 1 :=
begin
  rw nilpotency_class_quotient_center,
  rcases h : group.nilpotency_class G,
  { exfalso,
    rw nilpotency_class_zero_iff_subsingleton at h, resetI,
    apply (false_of_nontrivial_of_subsingleton G), },
  { simp }
end

/-- If the quotient by `center G` is nilpotent, then so is G. -/
lemma of_quotient_center_nilpotent (h : is_nilpotent (G ⧸ center G)) : is_nilpotent G :=
begin
  obtain ⟨n, hn⟩ := h.nilpotent,
  use n.succ,
  simp [← comap_upper_central_series_quotient_center, hn],
end

/-- A custom induction principle for nilpotent groups. The base case is a trivial group
(`subsingleton G`), and in the induction step, one can assume the hypothesis for
the group quotiented by its center. -/
@[elab_as_eliminator]
lemma nilpotent_center_quotient_ind
  {P : Π G [group G], by exactI ∀ [is_nilpotent G], Prop}
  (G : Type*) [group G] [is_nilpotent G]
  (hbase : ∀ G [group G] [subsingleton G], by exactI P G)
  (hstep : ∀ G [group G], by exactI ∀ [is_nilpotent G], by exactI ∀ (ih : P (G ⧸ center G)), P G) :
  P G :=
begin
  obtain ⟨n, h⟩ : ∃ n, group.nilpotency_class G = n := ⟨ _, rfl⟩,
  unfreezingI { induction n with n ih generalizing G },
  { haveI := nilpotency_class_zero_iff_subsingleton.mp h,
    exact hbase _, },
  { have hn : group.nilpotency_class (G ⧸ center G) = n :=
      by simp [nilpotency_class_quotient_center, h],
    exact hstep _ (ih _ hn), },
end


lemma derived_le_lower_central (n : ℕ) : derived_series G n ≤ lower_central_series G n :=
by { induction n with i ih, { simp }, { apply commutator_mono ih, simp } }

/-- Abelian groups are nilpotent -/
@[priority 100]
instance comm_group.is_nilpotent {G : Type*} [comm_group G] : is_nilpotent G :=
begin
  use 1,
  rw upper_central_series_one,
  apply comm_group.center_eq_top,
end

/-- Abelian groups have nilpotency class at most one -/
lemma comm_group.nilpotency_class_le_one {G : Type*} [comm_group G] :
  group.nilpotency_class G ≤ 1 :=
begin
  apply upper_central_series_eq_top_iff_nilpotency_class_le.mp,
  rw upper_central_series_one,
  apply comm_group.center_eq_top,
end

/-- Groups with nilpotency class at most one are abelian -/
def comm_group_of_nilpotency_class [is_nilpotent G] (h : group.nilpotency_class G ≤ 1) :
  comm_group G :=
group.comm_group_of_center_eq_top $
begin
  rw ← upper_central_series_one,
  exact upper_central_series_eq_top_iff_nilpotency_class_le.mpr h,
end

section prod

variables {G₁ G₂ : Type*} [group G₁] [group G₂]

lemma lower_central_series_prod (n : ℕ):
  lower_central_series (G₁ × G₂) n = (lower_central_series G₁ n).prod (lower_central_series G₂ n) :=
begin
  induction n with n ih,
  { simp, },
  { calc lower_central_series (G₁ × G₂) n.succ
        = ⁅lower_central_series (G₁ × G₂) n, ⊤⁆  : rfl
    ... = ⁅(lower_central_series G₁ n).prod (lower_central_series G₂ n), ⊤⁆ : by rw ih
    ... = ⁅(lower_central_series G₁ n).prod (lower_central_series G₂ n), (⊤ : subgroup G₁).prod ⊤⁆ :
      by simp
    ... = ⁅lower_central_series G₁ n, (⊤ : subgroup G₁)⁆.prod ⁅lower_central_series G₂ n, ⊤⁆ :
      commutator_prod_prod _ _ _ _
    ... = (lower_central_series G₁ n.succ).prod (lower_central_series G₂ n.succ) : rfl }
end

/-- Products of nilpotent groups are nilpotent -/
instance is_nilpotent_prod [is_nilpotent G₁] [is_nilpotent G₂] :
  is_nilpotent (G₁ × G₂) :=
begin
  rw nilpotent_iff_lower_central_series,
  refine ⟨max (group.nilpotency_class G₁) (group.nilpotency_class G₂), _ ⟩,
  rw [lower_central_series_prod,
    lower_central_series_eq_bot_iff_nilpotency_class_le.mpr (le_max_left _ _),
    lower_central_series_eq_bot_iff_nilpotency_class_le.mpr (le_max_right _ _), bot_prod_bot],
end

/-- The nilpotency class of a product is the max of the nilpotency classes of the factors -/
lemma nilpotency_class_prod [is_nilpotent G₁] [is_nilpotent G₂] :
  group.nilpotency_class (G₁ × G₂) = max (group.nilpotency_class G₁) (group.nilpotency_class G₂) :=
begin
  refine eq_of_forall_ge_iff (λ k, _),
  simp only [max_le_iff, ← lower_central_series_eq_bot_iff_nilpotency_class_le,
    lower_central_series_prod, prod_eq_bot_iff ],
end

end prod

section bounded_pi

-- First the case of infinite products with bounded nilpotency class

variables {η : Type*} {Gs : η → Type*} [∀ i, group (Gs i)]

lemma lower_central_series_pi_le (n : ℕ):
  lower_central_series (Π i, Gs i) n ≤ subgroup.pi set.univ (λ i, lower_central_series (Gs i) n) :=
begin
  let pi := λ (f : Π i, subgroup (Gs i)), subgroup.pi set.univ f,
  induction n with n ih,
  { simp [pi_top] },
  { calc lower_central_series (Π i, Gs i) n.succ
        = ⁅lower_central_series (Π i, Gs i) n, ⊤⁆           : rfl
    ... ≤ ⁅pi (λ i, (lower_central_series (Gs i) n)), ⊤⁆    : commutator_mono ih (le_refl _)
    ... = ⁅pi (λ i, (lower_central_series (Gs i) n)), pi (λ i, ⊤)⁆ : by simp [pi, pi_top]
    ... ≤ pi (λ i, ⁅(lower_central_series (Gs i) n), ⊤⁆)    : commutator_pi_pi_le _ _
    ... = pi (λ i, lower_central_series (Gs i) n.succ)      : rfl }
end

/-- products of nilpotent groups are nilpotent if their nipotency class is bounded -/
lemma is_nilpotent_pi_of_bounded_class [∀ i, is_nilpotent (Gs i)]
  (n : ℕ) (h : ∀ i, group.nilpotency_class (Gs i) ≤ n) :
  is_nilpotent (Π i, Gs i) :=
begin
  rw nilpotent_iff_lower_central_series,
  refine ⟨n, _⟩,
  rw eq_bot_iff,
  apply le_trans (lower_central_series_pi_le _),
  rw [← eq_bot_iff, pi_eq_bot_iff],
  intros i,
  apply lower_central_series_eq_bot_iff_nilpotency_class_le.mpr (h i),
end

end bounded_pi

section finite_pi

-- Now for finite products

variables {η : Type*} {Gs : η → Type*} [∀ i, group (Gs i)]

lemma lower_central_series_pi_of_finite [finite η] (n : ℕ) :
  lower_central_series (Π i, Gs i) n = subgroup.pi set.univ (λ i, lower_central_series (Gs i) n) :=
begin
  let pi := λ (f : Π i, subgroup (Gs i)), subgroup.pi set.univ f,
  induction n with n ih,
  { simp [pi_top] },
  { calc lower_central_series (Π i, Gs i) n.succ
        = ⁅lower_central_series (Π i, Gs i) n, ⊤⁆          : rfl
    ... = ⁅pi (λ i, (lower_central_series (Gs i) n)), ⊤⁆   : by rw ih
    ... = ⁅pi (λ i, (lower_central_series (Gs i) n)), pi (λ i, ⊤)⁆ : by simp [pi, pi_top]
    ... = pi (λ i, ⁅(lower_central_series (Gs i) n), ⊤⁆)   : commutator_pi_pi_of_finite _ _
    ... = pi (λ i, lower_central_series (Gs i) n.succ)     : rfl }
end

/-- n-ary products of nilpotent groups are nilpotent -/
instance is_nilpotent_pi [finite η] [∀ i, is_nilpotent (Gs i)] : is_nilpotent (Π i, Gs i) :=
begin
  casesI nonempty_fintype η,
  rw nilpotent_iff_lower_central_series,
  refine ⟨finset.univ.sup (λ i, group.nilpotency_class (Gs i)), _⟩,
  rw [lower_central_series_pi_of_finite, pi_eq_bot_iff],
  intros i,
  apply lower_central_series_eq_bot_iff_nilpotency_class_le.mpr,
  exact @finset.le_sup _ _ _ _ finset.univ (λ i, group.nilpotency_class (Gs i)) _
    (finset.mem_univ i),
end

/-- The nilpotency class of an n-ary product is the sup of the nilpotency classes of the factors -/
lemma nilpotency_class_pi [fintype η] [∀ i, is_nilpotent (Gs i)] :
  group.nilpotency_class (Π i, Gs i) = finset.univ.sup (λ i, group.nilpotency_class (Gs i)) :=
begin
  apply eq_of_forall_ge_iff,
  intros k,
  simp only [finset.sup_le_iff, ← lower_central_series_eq_bot_iff_nilpotency_class_le,
    lower_central_series_pi_of_finite, pi_eq_bot_iff, finset.mem_univ, true_implies_iff ],
end

end finite_pi

/-- A nilpotent subgroup is solvable -/
@[priority 100]
instance is_nilpotent.to_is_solvable [h : is_nilpotent G]: is_solvable G :=
begin
  obtain ⟨n, hn⟩ := nilpotent_iff_lower_central_series.1 h,
  use n,
  rw [eq_bot_iff, ←hn],
  exact derived_le_lower_central n,
end

lemma normalizer_condition_of_is_nilpotent [h : is_nilpotent G] : normalizer_condition G :=
begin
  -- roughly based on https://groupprops.subwiki.org/wiki/Nilpotent_implies_normalizer_condition
  rw normalizer_condition_iff_only_full_group_self_normalizing,
  apply nilpotent_center_quotient_ind G; unfreezingI { clear_dependent G },
  { introsI G _ _ H _, apply subsingleton.elim, },
  { introsI G _ _ ih H hH,

    have hch : center G ≤ H := subgroup.center_le_normalizer.trans (le_of_eq hH),
    have hkh : (mk' (center G)).ker ≤ H, by simpa using hch,
    have hsur : function.surjective (mk' (center G)), by exact surjective_quot_mk _,

    let H' := H.map (mk' (center G)),
    have hH' : H'.normalizer = H',
    { apply comap_injective hsur,
      rw [comap_normalizer_eq_of_surjective _ hsur, comap_map_eq_self hkh],
      exact hH, },
    apply map_injective_of_ker_le (mk' (center G)) hkh le_top,
    exact (ih H' hH').trans (symm (map_top_of_surjective _ hsur)), },
end

end with_group

section with_finite_group

open group fintype

variables {G : Type*} [hG : group G]
include hG

/-- A p-group is nilpotent -/
lemma is_p_group.is_nilpotent [finite G] {p : ℕ} [hp : fact (nat.prime p)] (h : is_p_group p G) :
  is_nilpotent G :=
begin
  casesI nonempty_fintype G,
  classical,
  unfreezingI
  { revert hG,
    induction val using fintype.induction_subsingleton_or_nontrivial with G hG hS G hG hN ih },
  { apply_instance, },
  { introI _, intro h,
    have hcq : fintype.card (G ⧸ center G) < fintype.card G,
    { rw card_eq_card_quotient_mul_card_subgroup (center G),
      apply lt_mul_of_one_lt_right,
      exact (fintype.card_pos_iff.mpr has_one.nonempty),
      exact ((subgroup.one_lt_card_iff_ne_bot _).mpr (ne_of_gt h.bot_lt_center)), },
    have hnq : is_nilpotent (G ⧸ center G) := ih _ hcq (h.to_quotient (center G)),
    exact (of_quotient_center_nilpotent hnq), }
end

variables [fintype G]

/-- If a finite group is the direct product of its Sylow groups, it is nilpotent -/
theorem is_nilpotent_of_product_of_sylow_group
  (e : (Π p : (fintype.card G).factorization.support, Π P : sylow p G, (↑P : subgroup G)) ≃* G) :
  is_nilpotent G :=
begin
  classical,
  let ps := (fintype.card G).factorization.support,
  haveI : ∀ (p : ps) (P : sylow p G), is_nilpotent (↑P : subgroup G),
  { intros p P,
    haveI : fact (nat.prime ↑p) := fact.mk (nat.prime_of_mem_factorization (finset.coe_mem p)),
    exact P.is_p_group'.is_nilpotent, },
  exact nilpotent_of_mul_equiv e,
end

/-- A finite group is nilpotent iff the normalizer condition holds, and iff all maximal groups are
normal and iff all sylow groups are normal and iff the group is the direct product of its sylow
groups. -/
theorem is_nilpotent_of_finite_tfae : tfae
  [ is_nilpotent G,
    normalizer_condition G,
    ∀ (H : subgroup G), is_coatom H → H.normal,
    ∀ (p : ℕ) (hp : fact p.prime) (P : sylow p G), (↑P : subgroup G).normal,
    nonempty ((Π p : (card G).factorization.support, Π P : sylow p G, (↑P : subgroup G)) ≃* G) ] :=
begin
  tfae_have : 1 → 2, { exact @normalizer_condition_of_is_nilpotent _ _ },
  tfae_have : 2 → 3, { exact λ h H, normalizer_condition.normal_of_coatom H h },
  tfae_have : 3 → 4, { introsI h p _ P, exact sylow.normal_of_all_max_subgroups_normal h _ },
  tfae_have : 4 → 5, { exact λ h, nonempty.intro (sylow.direct_product_of_normal h) },
  tfae_have : 5 → 1, { rintros ⟨e⟩, exact is_nilpotent_of_product_of_sylow_group e },
  tfae_finish,
end

end with_finite_group
