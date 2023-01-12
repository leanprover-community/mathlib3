/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import order.conditionally_complete_lattice.basic
import data.set.intervals.ord_connected

/-! # Subtypes of conditionally complete linear orders

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we give conditions on a subset of a conditionally complete linear order, to ensure that
the subtype is itself conditionally complete.

We check that an `ord_connected` set satisfies these conditions.

## TODO

Add appropriate instances for all `set.Ixx`. This requires a refactor that will allow different
default values for `Sup` and `Inf`.
-/

open_locale classical
open set

variables {α : Type*} (s : set α)

section has_Sup
variables [has_Sup α]

/-- `has_Sup` structure on a nonempty subset `s` of an object with `has_Sup`. This definition is
non-canonical (it uses `default s`); it should be used only as here, as an auxiliary instance in the
construction of the `conditionally_complete_linear_order` structure. -/
noncomputable def subset_has_Sup [inhabited s] : has_Sup s := {Sup := λ t,
if ht : Sup (coe '' t : set α) ∈ s then ⟨Sup (coe '' t : set α), ht⟩ else default}

local attribute [instance] subset_has_Sup

@[simp] lemma subset_Sup_def [inhabited s] :
  @Sup s _ = λ t,
  if ht : Sup (coe '' t : set α) ∈ s then ⟨Sup (coe '' t : set α), ht⟩ else default := rfl

lemma subset_Sup_of_within [inhabited s] {t : set s} (h : Sup (coe '' t : set α) ∈ s) :
  Sup (coe '' t : set α) = (@Sup s _ t : α) :=
by simp [dif_pos h]

end has_Sup

section has_Inf
variables [has_Inf α]

/-- `has_Inf` structure on a nonempty subset `s` of an object with `has_Inf`. This definition is
non-canonical (it uses `default s`); it should be used only as here, as an auxiliary instance in the
construction of the `conditionally_complete_linear_order` structure. -/
noncomputable def subset_has_Inf [inhabited s] : has_Inf s := {Inf := λ t,
if ht : Inf (coe '' t : set α) ∈ s then ⟨Inf (coe '' t : set α), ht⟩ else default}

local attribute [instance] subset_has_Inf

@[simp] lemma subset_Inf_def [inhabited s] :
  @Inf s _ = λ t,
  if ht : Inf (coe '' t : set α) ∈ s then ⟨Inf (coe '' t : set α), ht⟩ else default := rfl

lemma subset_Inf_of_within [inhabited s] {t : set s} (h : Inf (coe '' t : set α) ∈ s) :
  Inf (coe '' t : set α) = (@Inf s _ t : α) :=
by simp [dif_pos h]

end has_Inf

variables [conditionally_complete_linear_order α]

local attribute [instance] subset_has_Sup
local attribute [instance] subset_has_Inf

/-- For a nonempty subset of a conditionally complete linear order to be a conditionally complete
linear order, it suffices that it contain the `Sup` of all its nonempty bounded-above subsets, and
the `Inf` of all its nonempty bounded-below subsets.
See note [reducible non-instances]. -/
@[reducible]
noncomputable def subset_conditionally_complete_linear_order [inhabited s]
  (h_Sup : ∀ {t : set s} (ht : t.nonempty) (h_bdd : bdd_above t), Sup (coe '' t : set α) ∈ s)
  (h_Inf : ∀ {t : set s} (ht : t.nonempty) (h_bdd : bdd_below t), Inf (coe '' t : set α) ∈ s) :
  conditionally_complete_linear_order s :=
{ le_cSup := begin
    rintros t c h_bdd hct,
    -- The following would be a more natural way to finish, but gives a "deep recursion" error:
    -- simpa [subset_Sup_of_within (h_Sup t)] using
    --   (strict_mono_coe s).monotone.le_cSup_image hct h_bdd,
    have := (subtype.mono_coe s).le_cSup_image hct h_bdd,
    rwa subset_Sup_of_within s (h_Sup ⟨c, hct⟩ h_bdd) at this,
  end,
  cSup_le := begin
    rintros t B ht hB,
    have := (subtype.mono_coe s).cSup_image_le ht hB,
    rwa subset_Sup_of_within s (h_Sup ht ⟨B, hB⟩) at this,
  end,
  le_cInf := begin
    intros t B ht hB,
    have := (subtype.mono_coe s).le_cInf_image ht hB,
    rwa subset_Inf_of_within s (h_Inf ht ⟨B, hB⟩) at this,
  end,
  cInf_le := begin
    rintros t c h_bdd hct,
    have := (subtype.mono_coe s).cInf_image_le hct h_bdd,
    rwa subset_Inf_of_within s (h_Inf ⟨c, hct⟩ h_bdd) at this,
  end,
  ..subset_has_Sup s,
  ..subset_has_Inf s,
  ..distrib_lattice.to_lattice s,
  ..(infer_instance : linear_order s) }

section ord_connected

/-- The `Sup` function on a nonempty `ord_connected` set `s` in a conditionally complete linear
order takes values within `s`, for all nonempty bounded-above subsets of `s`. -/
lemma Sup_within_of_ord_connected
  {s : set α} [hs : ord_connected s] ⦃t : set s⦄ (ht : t.nonempty) (h_bdd : bdd_above t) :
  Sup (coe '' t : set α) ∈ s :=
begin
  obtain ⟨c, hct⟩ : ∃ c, c ∈ t := ht,
  obtain ⟨B, hB⟩ : ∃ B, B ∈ upper_bounds t := h_bdd,
  refine hs.out c.2 B.2 ⟨_, _⟩,
  { exact (subtype.mono_coe s).le_cSup_image hct ⟨B, hB⟩ },
  { exact (subtype.mono_coe s).cSup_image_le ⟨c, hct⟩ hB },
end

/-- The `Inf` function on a nonempty `ord_connected` set `s` in a conditionally complete linear
order takes values within `s`, for all nonempty bounded-below subsets of `s`. -/
lemma Inf_within_of_ord_connected
  {s : set α} [hs : ord_connected s] ⦃t : set s⦄ (ht : t.nonempty) (h_bdd : bdd_below t) :
  Inf (coe '' t : set α) ∈ s :=
begin
  obtain ⟨c, hct⟩ : ∃ c, c ∈ t := ht,
  obtain ⟨B, hB⟩ : ∃ B, B ∈ lower_bounds t := h_bdd,
  refine hs.out B.2 c.2 ⟨_, _⟩,
  { exact (subtype.mono_coe s).le_cInf_image ⟨c, hct⟩ hB },
  { exact (subtype.mono_coe s).cInf_image_le hct ⟨B, hB⟩ },
end

/-- A nonempty `ord_connected` set in a conditionally complete linear order is naturally a
conditionally complete linear order. -/
noncomputable instance ord_connected_subset_conditionally_complete_linear_order
  [inhabited s] [ord_connected s] :
  conditionally_complete_linear_order s :=
subset_conditionally_complete_linear_order s Sup_within_of_ord_connected Inf_within_of_ord_connected

end ord_connected
