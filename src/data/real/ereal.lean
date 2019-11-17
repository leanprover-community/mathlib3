/-
Copyright (c) 2019 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/

import data.real.basic 

/-!
# The extended reals [-∞, ∞].

This file defines `ereal`, the real numbers together with a top and bottom element,
referred to as ⊤ and ⊥. 

Addition and multiplication are problematic in the presence of ±∞, but
negation is not, so we define negation. The main work is defining
Sup : set ereal → ereal and proving that it is a Sup in all cases.
Once we have, this, it is not hard to give a complete lattice
structure on `ereal`.

## Tags

real, ereal, complete lattice
-/

/-- ereal : The type $$[-\infty,+\infty]$$ or `[-∞, ∞]` -/
def ereal := with_bot (with_top ℝ)

instance : linear_order ereal := by unfold ereal; apply_instance
instance : lattice.order_bot ereal := by unfold ereal; apply_instance
instance : lattice.order_top ereal := by unfold ereal; apply_instance

/- neg -/

/-- negation on ereal -/
def ereal.neg : ereal → ereal
| none := ⊤
| (some none) := ⊥
| (some (some x)) := ((↑-x : with_top ℝ) : with_bot (with_top ℝ))

instance : has_neg ereal := ⟨ereal.neg⟩

/-- if -a ≤ b then -b ≤ a on ereal -/
theorem ereal.neg_le_of_neg_le : ∀ {a b : ereal} (h : -a ≤ b), -b ≤ a
| none none h := by cases (lattice.le_bot_iff.1 h)
| none (some b) h := by cases (lattice.top_le_iff.1 h); exact le_refl _
| (some none) b h := lattice.le_top
| (some (some a)) none h := by cases (lattice.le_bot_iff.1 h)
| (some (some a)) (some none) h := lattice.bot_le
| (some (some a)) (some (some b)) h := 
begin
  revert h,
  change (((-a : ℝ) : with_top ℝ) : with_bot (with_top ℝ)) ≤ _ →
    (((-b : ℝ) : with_top ℝ) : with_bot (with_top ℝ)) ≤ _,
  unfold_coes, simpa using neg_le_of_neg_le,
end

/-- -a ≤ b ↔ -b ≤ a on ereal-/
theorem ereal.neg_le {a b : ereal} : -a ≤ b ↔ -b ≤ a := ⟨ereal.neg_le_of_neg_le, ereal.neg_le_of_neg_le⟩

/-- - -a = a on ereal -/
theorem ereal.neg_neg : ∀ (a : ereal), - (- a) = a
| none := rfl
| (some none) := rfl
| (some (some a)) := show (((- -a : ℝ) : with_top ℝ) : with_bot (with_top ℝ)) = (((a : ℝ) : with_top ℝ) : with_bot (with_top ℝ)),
by simp [neg_neg a]

/-- a ≤ -b → b ≤ -a on ereal -/
theorem ereal.le_neg_of_le_neg {a b : ereal} (h : a ≤ -b) : b ≤ -a :=
by rwa [←ereal.neg_neg b, ereal.neg_le, ereal.neg_neg]

/-- The claim that a set of ereals has a supremum in ereal -/
def has_Sup (X : set ereal) : Prop := ∃ l : ereal, is_lub X l

local attribute [instance, priority 10] classical.prop_decidable

/-- A set of ereals has a Sup in ereal -/
theorem Sup_exists (X : set ereal) : has_Sup X :=
  let Xoc : set (with_top ℝ) := λ x, X (↑x : with_bot _) in
dite (Xoc = ∅) (λ h, ⟨⊥, ⟨
    by
    { rintro (⟨⟩|x) hx, exact le_refl none,
      exfalso,
      apply set.not_mem_empty x,
      rw ←h,
      exact hx,
    },
    λ u hu, lattice.bot_le⟩
  ⟩) (λ h, dite (⊤ ∈ Xoc) (λ h2, ⟨⊤, ⟨λ _ _, lattice.le_top, λ x hx, hx _ h2⟩⟩) $
    λ htop, 
    let Xoo : set ℝ := λ (x : ℝ), Xoc (↑ x) in
    begin
    by_cases h2 : nonempty (upper_bounds Xoo),
    { rcases h2 with ⟨b, hb⟩,
      use (↑(↑(real.Sup Xoo : real) : with_top ℝ) : with_bot (with_top ℝ)),
      split,
      { rintros (⟨⟩|⟨⟩|x) hx,
            exact lattice.bot_le,
          exact false.elim (htop hx),
        change (↑(↑x : with_top ℝ) : with_bot (with_top ℝ)) ≤ _,
        simp [real.le_Sup _ ⟨b, hb⟩ hx],
      },
      { intros c hc,
        cases c with c,
          cases (set.exists_mem_of_ne_empty h) with x hx,
          cases (lattice.le_bot_iff.1 (hc (↑x : with_bot _) hx)),
        cases c with c, {unfold_coes, simp},
        suffices : real.Sup Xoo ≤ c,
          unfold_coes, simp [this],
        refine (real.Sup_le Xoo _ ⟨b, hb⟩).2 _,
          rcases (set.exists_mem_of_ne_empty h) with ⟨⟨⟩ | ⟨x⟩, hx⟩,
            contradiction,
          exact ⟨x, hx⟩,
        intros x hx,
        replace hc := hc (↑(↑x : with_top ℝ) : with_bot (with_top ℝ)) hx,
        unfold_coes at hc,
        simpa using hc,
      }
    },
    { use ⊤,
      split, intros x hx, exact lattice.le_top,
      intros b hb,
      rw lattice.top_le_iff,
      cases b with b,
        exfalso,
        apply h,
        ext x,
        split, swap, rintro ⟨⟩,
        intro hx,
        cases (lattice.le_bot_iff.1 (hb (↑x : with_bot _) hx)),
      cases b with b, refl,
      exfalso,
      apply h2,
      use b,
      intros x hx,
      replace hb := hb (↑(↑x : with_top ℝ) : with_bot (with_top ℝ)) hx,
      unfold_coes at hb,
      simpa using hb,
    }
  end) 

noncomputable def ereal.Sup := λ X, classical.some (Sup_exists X)

noncomputable instance : lattice.has_Sup ereal := ⟨ereal.Sup⟩

/-- `ereal` is a complete lattice -/
noncomputable instance : lattice.complete_lattice (ereal) :=
{ top := ⊤,
  le_top := λ _, lattice.le_top,
  bot := ⊥,
  bot_le := @lattice.bot_le _ _,
  Sup := ereal.Sup,
  Inf := λ X, -classical.some (Sup_exists ({mx | ∃ x ∈ X, mx = -x})),
  le_Sup := λ X x hx, (classical.some_spec (Sup_exists X)).1 _ hx,
  Sup_le := λ X b hb, (classical.some_spec (Sup_exists X)).2 _ hb,
  Inf_le := λ X x hx, ereal.neg_le_of_neg_le $ (classical.some_spec (Sup_exists ({mx | ∃ x ∈ X, mx = -x}))).1 _ ⟨x, hx, rfl⟩,
  le_Inf := λ X b hb, ereal.le_neg_of_le_neg $ (classical.some_spec (Sup_exists ({mx | ∃ x ∈ X, mx = -x}))).2 _
    (λ mx ⟨x, hx, hmx⟩, ereal.le_neg_of_le_neg $ hb _ $ by rwa [hmx, ereal.neg_neg]),
  ..with_bot.lattice }
