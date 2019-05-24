/-
  Copyright (c) 2019 Seul Baek. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Seul Baek

  First-order formulas.
-/

import tactic.vampire.term

universe u

variable {α : Type u}

namespace vampire

inductive form : Type
| lit : bool → term → form
| bin : bool → form → form → form

local notation `⟪` b `,` a `⟫₁` := form.lit b a
local notation p `∨₁` q         := form.bin tt p q
local notation p `∧₁` q         := form.bin ff p q

namespace form

def holds (M : model α) (v : nat → α) : form → Prop
| (form.lit tt a)   :=   (a.val M v []).snd
| (form.lit ff a)   := ¬ (a.val M v []).snd
| (form.bin tt p q) := p.holds ∨ q.holds
| (form.bin ff p q) := p.holds ∧ q.holds

lemma holds_bin_iff_holds_bin
  {M N : model α} {v w : nat → α} {p q r s : form} {b : bool} :
  (p.holds M v ↔ q.holds N w) → (r.holds M v ↔ s.holds N w) →
  ((form.bin b p r).holds M v ↔ (form.bin b q s).holds N w) :=
by { intros h0 h1,
     cases b; unfold form.holds;
     apply pred_mono_2; assumption }

def neg : form → form
| (form.lit b t)   := form.lit (bnot b) t
| (form.bin b p q) := form.bin (bnot b) (neg p) (neg q)

lemma holds_neg (M : model α) (v : vas α) :
  ∀ p : form, (neg p).holds M v ↔ ¬ p.holds M v
| (form.lit b t) :=
  by { cases b; simp only [form.holds,
       classical.not_not, term.val, neg, bnot] }
| (p ∨₁ q) :=
  begin
    unfold form.holds,
    rw not_or_distrib,
    apply pred_mono_2;
    apply holds_neg
  end
| (p ∧₁ q) :=
  begin
    unfold form.holds,
    rw @not_and_distrib _ _ (classical.dec _),
    apply pred_mono_2; apply holds_neg
  end

def tas (α : Type u) (p : form) : Prop :=
∀ M : model α, ∃ v : nat → α, p.holds M v

def sat (α : Type u) (p : form) : Prop :=
∃ M : model α, ∀ v : nat → α, p.holds M v

end form

end vampire
