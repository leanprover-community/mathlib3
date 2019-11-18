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

attribute [pattern] lattice.has_bot.bot lattice.has_top.top

/-- ereal : The type $$[-\infty,+\infty]$$ or `[-∞, ∞]` -/
@[derive [linear_order, lattice.order_bot, lattice.order_top]] def ereal := with_bot (with_top ℝ)

namespace ereal
instance : has_coe ℝ ereal := ⟨some ∘ some⟩
@[simp, elim_cast] protected lemma coe_real_le {x y : ℝ} : (x : ereal) ≤ (y : ereal) ↔ x ≤ y :=
by { unfold_coes, norm_num }
@[simp, elim_cast] protected lemma coe_real_lt {x y : ℝ} : (x : ereal) < (y : ereal) ↔ x < y :=
by { unfold_coes, norm_num }
@[simp, elim_cast] protected lemma coe_real_inj' {x y : ℝ} : (x : ereal) = (y : ereal) ↔ x = y :=
by { unfold_coes, simp [option.some_inj] }

/- neg -/
/-- negation on ereal -/
protected def neg : ereal → ereal
| ⊥       := ⊤
| ⊤       := ⊥
| (x : ℝ) := (-x : ℝ)

instance : has_neg ereal := ⟨ereal.neg⟩

@[move_cast] protected lemma neg_def (x : ℝ) : ((-x : ℝ) : ereal) = -x := rfl

/-- if -a ≤ b then -b ≤ a on ereal -/
protected theorem neg_le_of_neg_le : ∀ {a b : ereal} (h : -a ≤ b), -b ≤ a
| ⊥ ⊥ h := by cases (lattice.le_bot_iff.1 h)
| ⊥ (some b) h := by { cases (lattice.top_le_iff.1 h), exact le_refl _ }
| ⊤ b h := lattice.le_top
| (a : ℝ) ⊥ h := by cases (lattice.le_bot_iff.1 h)
| (a : ℝ) ⊤ h := lattice.bot_le
| (a : ℝ) (b : ℝ) h := by { norm_cast at h ⊢, exact _root_.neg_le_of_neg_le h }

/-- -a ≤ b ↔ -b ≤ a on ereal-/
protected theorem neg_le {a b : ereal} : -a ≤ b ↔ -b ≤ a :=
⟨ereal.neg_le_of_neg_le, ereal.neg_le_of_neg_le⟩

/-- - -a = a on ereal -/
protected theorem neg_neg : ∀ (a : ereal), - (- a) = a
| ⊥ := rfl
| ⊤ := rfl
| (a : ℝ) := by { norm_cast, simp [neg_neg a] }

/-- a ≤ -b → b ≤ -a on ereal -/
theorem le_neg_of_le_neg {a b : ereal} (h : a ≤ -b) : b ≤ -a :=
by rwa [←ereal.neg_neg b, ereal.neg_le, ereal.neg_neg]

/-- The claim that a set of ereals has a supremum in ereal -/
def has_Sup (X : set ereal) : Prop := ∃ l : ereal, is_lub X l

open_locale classical

/-- A set of ereals has a Sup in ereal -/
theorem Sup_exists (X : set ereal) : has_Sup X :=
  let Xoc : set (with_top ℝ) := some ⁻¹' X in
if h : Xoc = ∅ then ⟨⊥, ⟨
    by
    { rintro (⟨⟩|x) hx, exact le_refl ⊥,
      exfalso,
      apply set.not_mem_empty x,
      rw ←h,
      exact hx,
    },
    λ u hu, lattice.bot_le⟩
  ⟩ else if htop : ⊤ ∈ Xoc then ⟨⊤, ⟨λ _ _, lattice.le_top, λ x hx, hx htop⟩⟩ else
    let Xoo : set ℝ := some ⁻¹' Xoc in
    begin
    by_cases h2 : nonempty (upper_bounds Xoo),
    { rcases h2 with ⟨b, hb⟩,
      use (real.Sup Xoo : ereal),
      split,
      { rintros (⟨⟩|⟨⟩|x) hx,
        { exact lattice.bot_le},
        { exact false.elim (htop hx)},
        { change (x : ereal) ≤ _,
          simp [real.le_Sup _ ⟨b, hb⟩ hx]},
      },
      { intros c hc,
        cases c with c,
        { cases (set.exists_mem_of_ne_empty h) with x hx,
          cases (lattice.le_bot_iff.1 (hc hx))},
        cases c with c, {unfold_coes, simp},
        suffices : real.Sup Xoo ≤ c,
        { unfold_coes, simp [this]},
        refine (real.Sup_le Xoo _ ⟨b, hb⟩).2 _,
        { rcases (set.exists_mem_of_ne_empty h) with ⟨⟨⟩ | ⟨x⟩, hx⟩, contradiction,
          exact ⟨x, hx⟩},
        intros x hx,
        simpa using hc hx
      }
    },
    { use ⊤,
      split, intros x hx, exact lattice.le_top,
      intros b hb,
      rw lattice.top_le_iff,
      cases b with b,
      { exfalso,
        apply h,
        ext x,
        split, swap, rintro ⟨⟩,
        intro hx,
        cases (lattice.le_bot_iff.1 (hb hx))},
      { cases b with b, refl,
        exfalso,
        apply h2,
        use b,
        intros x hx,
        replace hb := hb hx,
        simpa using hb},
    }
  end

noncomputable def Sup := λ X, classical.some (Sup_exists X)

noncomputable instance : lattice.has_Sup ereal := ⟨Sup⟩

/-- `ereal` is a complete lattice -/
noncomputable instance : lattice.complete_lattice (ereal) :=
{ top := ⊤,
  le_top := λ _, lattice.le_top,
  bot := ⊥,
  bot_le := @lattice.bot_le _ _,
  Sup := ereal.Sup,
  Inf := λ X, -classical.some (Sup_exists ({mx | ∃ x ∈ X, mx = -x})),
  le_Sup := λ X x hx, (classical.some_spec (Sup_exists X)).1 hx,
  Sup_le := λ X b hb, (classical.some_spec (Sup_exists X)).2 hb,
  Inf_le := λ X x hx, ereal.neg_le_of_neg_le $ (classical.some_spec (Sup_exists ({mx | ∃ x ∈ X, mx = -x}))).1 ⟨x, hx, rfl⟩,
  le_Inf := λ X b hb, ereal.le_neg_of_le_neg $ (classical.some_spec (Sup_exists ({mx | ∃ x ∈ X, mx = -x}))).2
    (λ mx ⟨h, hx, hmx⟩, ereal.le_neg_of_le_neg $ hb _ $ by rwa [hmx, ereal.neg_neg]),
  ..with_bot.lattice }

  end ereal
