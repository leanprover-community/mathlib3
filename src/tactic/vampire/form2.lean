/-
  Copyright (c) 2019 Seul Baek. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Seul Baek

  Second-order formulas.
-/

import tactic.vampire.sub2
import data.nat.basic

universe u

variables {α β : Type u}

open nat

namespace vampire

local notation f `₀↦` a := assign a f
local notation `#`      := term₂.var
local notation a `&` b  := term₂.app a b

postfix  `ₑ` : 1000 := evaluate
postfix  `ᵈ` : 1000 := denote
local infix `⬝` := value.app

@[derive has_reflect]
inductive form₂ : Type
| lit : bool → term₂ → form₂
| bin : bool → form₂ → form₂ → form₂
| qua : bool → form₂ → form₂

local notation `⟪` b `,` a `⟫` := form₂.lit b a
local notation p `∨*` q        := form₂.bin tt p q
local notation p `∧*` q        := form₂.bin ff p q
local notation `∃*`            := form₂.qua tt
local notation `∀*`            := form₂.qua ff

namespace form₂

meta def to_expr : form₂ → expr
| ⟪b, t⟫ := `(⟪%%`(b), %%(t.to_expr)⟫)
| (form₂.bin b p q) := `(form₂.bin %%`(b) %%p.to_expr %%q.to_expr)
| (form₂.qua b p)   := `(form₂.qua %%`(b) %%p.to_expr)

def repr : form₂ → string
| ⟪tt, t⟫  := t.repr
| ⟪ff, t⟫  := "¬" ++ t.repr
| (p ∨* q) := "(" ++ p.repr ++ " ∨ " ++ q.repr ++ ")"
| (p ∧* q) := "(" ++ p.repr ++ " ∧ " ++ q.repr ++ ")"
| (∀* p)   := "(∀ " ++ p.repr ++ ")"
| (∃* p)   := "(∃ " ++ p.repr ++ ")"

instance has_repr : has_repr form₂ := ⟨repr⟩
meta instance has_to_format : has_to_format form₂ := ⟨λ x, repr x⟩

def holds : model α → form₂ → Prop
| M ⟪tt, a⟫  :=   (a.val M []).snd
| M ⟪ff, a⟫  := ¬ (a.val M []).snd
| M (p ∨* q) := holds M p ∨ holds M q
| M (p ∧* q) := holds M p ∧ holds M q
| M (∀* p)   := ∀ x : value α, holds (M ₀↦ x) p
| M (∃* p)   := ∃ x : value α, holds (M ₀↦ x) p

def fholds (k : nat) (M : model α) (v : vas α) (p : form₂) : Prop :=
holds (fmodel k _ M v) p

infix `⊨` : 1000 := holds

@[reducible] def size_of : form₂ → nat
| ⟪_, _⟫           := 1
| (form₂.bin _ p q) := p.size_of + q.size_of + 1
| (form₂.qua _ p)   := p.size_of + 1

instance has_sizeof : has_sizeof form₂ := ⟨size_of⟩

/- Increment all variable indices equal to or greater than k by 1. -/
def incr_ge : nat → form₂ → form₂
| k ⟪b, a⟫           := ⟪b, a.incr_ge k⟫
| k (form₂.bin b p q) := form₂.bin b (incr_ge k p) (incr_ge k q)
| k (form₂.qua b p)   := form₂.qua b (incr_ge (k + 1) p)

def incr : form₂ → form₂ := incr_ge 0

def subst : sub₂ → form₂ → form₂
| σ ⟪b, a⟫           := ⟪b, a.subst σ⟫
| σ (form₂.bin b p q) := form₂.bin b (subst σ p) (subst σ q)
| σ (form₂.qua b p)   := form₂.qua b (subst σ.incr p)

lemma size_of_subst :
  ∀ p : form₂, ∀ σ : sub₂, (p.subst σ).size_of = p.size_of
| ⟪b, a⟫           σ := rfl
| (form₂.bin b p q) σ :=
  by simp only [size_of, subst, size_of_subst p, size_of_subst q]
| (form₂.qua b p)   σ :=
  by simp only [size_of, subst, size_of_subst p]

@[simp] lemma size_of_incr_ge :
  ∀ k : nat, ∀ p : form₂, (p.incr_ge k).size_of = p.size_of
| k ⟪b, a⟫           := rfl
| k (form₂.bin b p q) :=
  by simp only [ size_of, size_of_incr_ge k p,
     incr_ge, size_of_incr_ge k q ]
| k (form₂.qua b p)   :=
  by simp only [size_of, incr_ge, size_of_incr_ge _ p]

@[simp] lemma size_of_incr :
  ∀ p : form₂, p.incr.size_of = p.size_of :=
size_of_incr_ge _

def neg : form₂ → form₂
| ⟪b, a⟫           := ⟪bnot b, a⟫
| (form₂.bin b p q) := form₂.bin (bnot b) p.neg q.neg
| (form₂.qua b p)   := form₂.qua (bnot b) p.neg

def occ : nat → form₂ → Prop
| k ⟪_, a⟫           := a.occ k
| k (form₂.bin b p q) := p.occ k ∨ q.occ k
| k (form₂.qua b p)   := p.occ (k + 1)

lemma not_occ_incr_ge :
  ∀ k : nat, ∀ p : form₂, ¬ (p.incr_ge k).occ k
| k ⟪b, a⟫           := term₂.not_occ_incr_ge _ _
| k (form₂.bin b p q) :=
  by { intro h0, cases h0;
       apply not_occ_incr_ge k _ h0 }
| k (form₂.qua b p) := not_occ_incr_ge (k + 1) p

lemma holds_bin_iff_holds_bin
  {M N : model α} {p q r s : form₂} {b : bool} :
  (M ⊨ p ↔ N ⊨ q) → (M ⊨ r ↔ N ⊨ s) →
  (M ⊨ form₂.bin b p r ↔ N ⊨ form₂.bin b q s) :=
by { intros h0 h1, cases b;
     apply pred_mono_2; assumption }

end form₂

def fam (α : Type u) (p : form₂) : Prop :=
  ∀ M : model α, M ⊨ p

lemma fam_fa (α : Type u) (p : form₂) :
  fam α (∀* p) ↔ fam α p :=
begin
  constructor; intros h0 M,
  { have h1 := h0 M.decr_idxs (M 0),
    rwa assign_decr_idxs at h1 },
  intro v, apply h0
end

def eqv (α : Type u) (p q : form₂) : Prop :=
∀ M : model α, (M ⊨ p ↔ M ⊨ q)

notation p `<==` α `==>` q := eqv α p q

lemma eqv_trans {α : Type u} {p q r : form₂} :
  (p <==α==> q) → (q <==α==> r) → (p <==α==> r) :=
λ h0 h1 M, by rw [h0 M, h1 M]

lemma eqv_refl (α : Type u) (p : form₂) : p <==α==> p := λ M, by refl

lemma bin_eqv_bin {p q r s : form₂} {b : bool} :
  (p <==α==> q) → (r <==α==> s) →
  (form₂.bin b p r <==α==> form₂.bin b q s) :=
by { intros h0 h1 M,
     apply form₂.holds_bin_iff_holds_bin (h0 _) (h1 _) }

lemma bin_comm (b : bool) (p q : form₂) :
  form₂.bin b p q <==α==> form₂.bin b q p :=
by {intro M, cases b, apply and.comm, apply or.comm}

lemma holds_qua_iff_holds_qua {M N : model α} {p q : form₂} {b : bool} :
  (∀ v : value α, (M ₀↦ v) ⊨ p ↔ (N ₀↦ v) ⊨ q) →
  (M ⊨ form₂.qua b p ↔ N ⊨ form₂.qua b q) :=
begin
  intro h0, cases b,
  apply forall_congr h0,
  apply exists_congr h0
end

lemma qua_eqv_qua {p q : form₂} {b : bool} :
  (p <==α==> q) → (form₂.qua b p <==α==> form₂.qua b q) :=
by { intros h0 M,
     apply holds_qua_iff_holds_qua,
     intro v, apply h0 }

lemma holds_neg : ∀ {M : model α}, ∀ {p : form₂}, M ⊨ p.neg ↔ ¬ M ⊨ p
| M ⟪b, a⟫ :=
  by cases b;
     simp only [classical.not_not, form₂.neg,
     form₂.holds, bool.bnot_true, bool.bnot_false]
| M (p ∨* q) :=
  begin
    unfold form₂.holds,
    rw not_or_distrib,
    apply pred_mono_2;
    apply holds_neg
  end
| M (p ∧* q) :=
  begin
    unfold form₂.holds,
    rw @not_and_distrib _ _ (classical.dec _),
    apply pred_mono_2; apply holds_neg
  end
| M (∀* p)   :=
  begin
    unfold form₂.holds,
    rw @not_forall _ _ (classical.dec _) (classical.dec_pred _),
    apply exists_congr,
    intro v, apply holds_neg
  end
| M (∃* p)   :=
  begin
    unfold form₂.holds,
    rw @not_exists,
    apply forall_congr,
    intro v, apply holds_neg
  end

lemma holds_incr_ge :
  ∀ M N : model α, ∀ k : nat,
    (∀ m < k, M m = N m) →
    (∀ m ≥ k, M (m + 1) = N m) →
    ∀ p : form₂, M ⊨ p.incr_ge k ↔ N ⊨ p
| M N k h0 h1 ⟪b, a⟫ :=
  by cases b; simp [form₂.incr_ge,
     form₂.holds, val_incr_ge h0 h1 a]
| M N k h0 h1 (form₂.bin b p q) :=
  by { apply form₂.holds_bin_iff_holds_bin;
       apply holds_incr_ge _ _ _ h0 h1 }
| M N k h0 h1 (form₂.qua b p) :=
  begin
    apply holds_qua_iff_holds_qua, intro v,
    apply holds_incr_ge _ _ (k + 1);
    intros m h2; cases m,
    { refl },
    { apply h0 _ (lt_of_succ_lt_succ h2) },
    { cases (not_lt_zero _ (lt_of_succ_le h2)) },
    apply h1 _ (succ_le_succ_iff.elim_left h2)
  end

lemma holds_assign_incr {M : model α} {d : value α} :
  ∀ p : form₂, (M ₀↦ d) ⊨ p.incr ↔ M ⊨ p :=
holds_incr_ge (M ₀↦ d) M 0 (λ _ h, by cases h) (λ _ _, rfl)

lemma neg_subst :
  ∀ p : form₂, ∀ σ : sub₂, (p.subst σ).neg <==α==> (p.neg.subst σ)
| ⟪b, a⟫       σ := by apply eqv_refl
| (form₂.bin b p q) σ :=
  by { intro M, apply form₂.holds_bin_iff_holds_bin;
       apply neg_subst }
| (form₂.qua b p)   σ :=
  by { intro M, apply holds_qua_iff_holds_qua,
       intro v, apply neg_subst }

lemma neg_eqv_neg (p q : form₂) :
  (p.neg <==α==> q.neg) ↔ (p <==α==> q) :=
begin
  apply forall_congr, intro M,
  rw [holds_neg, holds_neg, @not_iff_not _ _ _ _],
  repeat {apply classical.dec _}
end

lemma neg_incr_ge :
  ∀ k : nat, ∀ p : form₂, (p.incr_ge k).neg = p.neg.incr_ge k
| k ⟪b, a⟫           := by cases b; refl
| k (form₂.bin b p q) :=
  by simp only [form₂.neg, form₂.incr_ge,
     eq_self_iff_true, neg_incr_ge, and_self ]
| k (form₂.qua b p) :=
  by simp only [form₂.neg, form₂.incr_ge,
     eq_self_iff_true, neg_incr_ge, and_self ]

lemma neg_incr (p : form₂) :
  p.incr.neg = p.neg.incr :=
neg_incr_ge 0 p

lemma holds_subst :
  ∀ (M : model α) (p : form₂) (σ : sub₂),
  M ⊨ (p.subst σ) ↔ M.subst σ ⊨ p
| M ⟪b, a⟫ σ :=
  by cases b; simp only [form₂.subst, form₂.holds, val_subst M σ a]
| M (form₂.bin b p q) σ :=
  by apply form₂.holds_bin_iff_holds_bin; apply holds_subst
| M (form₂.qua b p)   σ :=
  by { apply holds_qua_iff_holds_qua, intro v,
       simp only [model.assign_subst, holds_subst] }

namespace form₂

def F : form₂ → Prop
| ⟪_, _⟫           := true
| (form₂.bin _ p q) := F p ∧ F q
| (form₂.qua b p)   := false

def N (b : bool) : form₂ → Prop
| ⟪_, _⟫            := true
| (form₂.bin _ p q) := N p ∧ N q
| (form₂.qua c p)   := b ≠ c ∧ N p

def QN (b : bool) : form₂ → Prop
| (form₂.qua c p) := (b = c → QN p) ∧ (b ≠ c → N b p)
| p              := N b p

def QF (b : bool) : form₂ → Prop
| (form₂.qua c p) := b = c ∧ QF p
| p              := F p

def QDF (b : bool) : form₂ → Prop
| (form₂.qua c p) := (b = c → QDF p) ∧ (b ≠ c → QF (bnot b) p)
| p              := F p

lemma F_incr_ge :
  ∀ k : nat, ∀ {p : form₂}, p.F → (p.incr_ge k).F
| k (form₂.lit _ _)   _ := trivial
| k (form₂.bin _ p q) h := ⟨F_incr_ge _ h.left, F_incr_ge _ h.right⟩
| k (form₂.qua c p)   h := by cases h

lemma N_incr_ge {b : bool} :
  ∀ k : nat, ∀ {p : form₂}, p.N b → (p.incr_ge k).N b
| k (form₂.lit _ _)   _ := trivial
| k (form₂.bin _ p q) h := ⟨N_incr_ge _ h.left, N_incr_ge _ h.right⟩
| k (form₂.qua c p)   h := ⟨h.left, N_incr_ge _ h.right⟩

lemma QN_incr_ge {b : bool} :
  ∀ k : nat, ∀ {p : form₂}, p.QN b → (p.incr_ge k).QN b
| k (form₂.lit _ _)   _  := trivial
| k (form₂.bin _ p q) h0 :=
  ⟨ N_incr_ge _ h0.left,
    N_incr_ge _ h0.right ⟩
| k (form₂.qua c p)   h0 :=
  ⟨ λ h1, QN_incr_ge _ (h0.left h1),
    λ h1, N_incr_ge _ (h0.right h1) ⟩

lemma QF_incr_ge {b : bool} :
  ∀ k : nat, ∀ {p : form₂}, p.QF b → (p.incr_ge k).QF b
| k (form₂.lit _ _)   _  := trivial
| k (form₂.bin _ p q) h0 :=
  ⟨ F_incr_ge _ h0.left,
    F_incr_ge _ h0.right ⟩
| k (form₂.qua c p)   h0 :=
  ⟨ h0.left, QF_incr_ge _ h0.right ⟩

lemma QDF_of_QF_bnot {b : bool} :
  ∀ p : form₂, p.QF (bnot b) → p.QDF b
| (form₂.lit _ _)   _  := trivial
| (form₂.bin _ p q) h0 := h0
| (form₂.qua c p)   h0 :=
  ⟨ λ h1, absurd h1 (bnot_eq_iff_ne.elim_left h0.left),
    λ _, h0.right⟩

end form₂

end vampire
