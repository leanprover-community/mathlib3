/-
  Copyright (c) 2019 Seul Baek. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Seul Baek

  Translation of SOL formulas into FOL.
-/

import tactic.interactive
import tactic.spass.swap
import tactic.spass.form

universe u

variable {α : Type u}

open nat list

local notation f `₀↦` a := assign a f
postfix  `ₑ` : 1000 := evaluate
postfix  `ᵈ` : 1000 := denote
local infix `⬝` := value.app

local notation `&₁`     := term.sym
local notation a `&₁` b := term.app a b
local notation a `#₁` k := term.vpp a k

local notation `⟪` b `,` a `⟫₁` := form.lit b a
local notation p `∨₁` q        := form.bin tt p q
local notation p `∧₁` q        := form.bin ff p q

def term₂.folize (k : nat) : term₂ → term
| (term₂.var m) := (&₁ (m - k))
| (term₂.app a (term₂.var m)) :=
  if m < k
  then a.folize #₁ m
  else a.folize &₁ (&₁ (m - k))
| (term₂.app a (term₂.app b c)) :=
  a.folize &₁ (term₂.app b c).folize

def form₂.folize : nat → form₂ → form
| k (form₂.lit b t)   := ⟪b, t.folize k⟫₁
| k (form₂.bin b p q) := form.bin b (p.folize k) (q.folize k)
| k (form₂.qua tt p)  := p.folize k.succ
| k (form₂.qua ff p)  := p.folize k

def term₂.fov_lt (k : nat) (a : term₂) : Prop :=
∀ m < k, a.fov m

lemma fov_lt_of_fov_lt_app_left {k : nat} {a b : term₂} :
  (term₂.app a b).fov_lt k → a.fov_lt k :=
λ h0 m h1, (h0 m h1).left

lemma fov_lt_of_fov_lt_app_right {k : nat} {a b c : term₂} :
  (term₂.app a (term₂.app b c)).fov_lt k → (term₂.app b c).fov_lt k :=
λ h0 m h1, (h0 m h1).right

def form₂.fov_lt (k : nat) (p : form₂) : Prop :=
∀ m < k, p.fov m

lemma fov_lt_of_fov_lt_bin_left {b : bool} {k : nat} {p q : form₂} :
  (form₂.bin b p q).fov_lt k → p.fov_lt k :=
λ h0 m h1, (h0 m h1).left

lemma fov_lt_of_fov_lt_bin_right {b : bool} {k : nat} {p q : form₂} :
  (form₂.bin b p q).fov_lt k → q.fov_lt k :=
λ h0 m h1, (h0 m h1).right

def exs : nat → form₂ → form₂
| 0       p := p
| (k + 1) p := form₂.qua tt (exs k p)

lemma exs_ex :
  ∀ k : nat, ∀ p : form₂,
  exs k (form₂.qua tt p) = exs (k + 1) p
| 0       p := rfl
| (k + 1) p := by {unfold exs, rw exs_ex, refl}

lemma sub_eq_succ_sub_succ {k m : nat} :
  k + 1 ≤ m → m - k = succ (m - (k + 1)) :=
begin
  intro h0,
  rw succ_le_iff at h0,
  rw [← nat.sub_sub, ← pred_eq_sub_one, succ_pred_eq_of_pos _],
  simpa only [gt, nat.lt_sub_left_iff_add_lt] using h0
end

lemma val_folize_succ {k : nat} (M : model α) (v : nat → α) :
  ∀ {a : term₂}, a.fov_lt (k + 1) →
  (a.folize $ k + 1).val M v = (a.folize k).val (M ₀↦ (v k)ₑ) v
| (term₂.var m) h0 :=
  begin
    by_cases h1 : m < k + 1,
    { cases h0 m h1 rfl },
    rw not_lt at h1,
    simp only [term₂.folize, term.val],
    rw sub_eq_succ_sub_succ h1, refl,
  end
| (term₂.app a (term₂.var m)) h0 :=
  begin
    have h := val_folize_succ (fov_lt_of_fov_lt_app_left h0),
    unfold term₂.folize,
    by_cases h1 : m < k,
    { rw if_pos h1,
      rw if_pos (lt_trans h1 $ lt_succ_self _),
      unfold term.val, rw h },
    rw if_neg h1,
    rw not_lt at h1,
    by_cases h2 : m = k,
    { rw h2, rw if_pos (lt_succ_self _),
      unfold term.val,
      rw [h, nat.sub_self k], refl },
    have h3 : k + 1 ≤ m,
    { rw le_iff_eq_or_lt at h1,
      cases h1,
      { cases h2 h1.symm },
      rw succ_le_iff, exact h1 },
    rw if_neg (not_lt.elim_right h3),
    unfold term.val,
    rw [h, sub_eq_succ_sub_succ h3], refl
  end
| (term₂.app a (term₂.app b c)) h0 :=
  by simp only [term₂.folize, term.val,
     val_folize_succ (fov_lt_of_fov_lt_app_left h0),
     val_folize_succ (fov_lt_of_fov_lt_app_right h0)]

lemma holds_folize_succ {k : nat} (M : model α) (v : nat → α) :
  ∀ p : form₂, p.F → p.fov_lt (k + 1) →
  ((p.folize $ k + 1).holds M v ↔ (p.folize k).holds (M ₀↦ (v k)ₑ) v)
| (form₂.lit b a) h0 h1 :=
  by { cases b; --;
       simp only  [form₂.folize, term.val,
         form.holds, val_folize_succ M v h1] }
| (form₂.bin b p q) h0 h1 :=
  begin
    apply form.holds_bin_iff_holds_bin,
    { exact holds_folize_succ _ h0.left (fov_lt_of_fov_lt_bin_left h1) },
    exact holds_folize_succ _ h0.right (fov_lt_of_fov_lt_bin_right h1),
  end

lemma forall_lt_of_forall_lt_succ {k : nat} {p : nat → Prop} :
  (∀ m < (k + 1), p m) → (∀ m < k, p m) :=
λ h0 m h1, h0 _ (lt_trans h1 $ lt_succ_self _)

lemma forall_lt_zero {p : nat → Prop} : (∀ m < 0, p m) :=
λ m h, by cases h

lemma val_folize_zero (M : model α) (v : nat → α) :
  ∀ a : term₂, (a.folize 0).val M v = a.val M
| (term₂.var k) := rfl
| (term₂.app a (term₂.var k)) :=
  begin
    unfold term₂.folize,
    have h0 : ¬ k < 0,
    { rw not_lt, apply nat.zero_le },
    rw if_neg h0,
    simp only [term.val, term₂.val, nat.sub_zero,
      val_folize_zero a, eq_self_iff_true]
  end
| (term₂.app a (term₂.app b c)) :=
  by simp only [term.val, term₂.val, nat.sub_zero,
    val_folize_zero a, val_folize_zero (term₂.app b c),
    eq_self_iff_true, term₂.folize]

lemma holds_folize_zero (M : model α) (v : nat → α) :
  ∀ {p : form₂}, p.F → ((p.folize 0).holds M v ↔ p.holds M)
| (form₂.lit b a) h0 :=
  by cases b;
     simp only [form₂.holds, form.holds,
       form₂.folize, val_folize_zero]
| (form₂.bin b p q) h0 :=
  by { cases b; apply pred_mono_2;
       simp only [ form₂.holds, form.holds,
       form₂.folize, holds_folize_zero h0.left,
       holds_folize_zero h0.right ] }

lemma holds_exs_of_exv_folize :
  ∀ {p : form₂} (k : nat) {M : model α},
  foq tt p → p.QF tt → p.fov_lt k →
  (∃ v : nat → α, (p.folize k).holds M v) →
  (exs k p).holds M
| (form₂.lit b a) 0  :=
  by { intros M h0 h1 h2 h3,
       cases h3 with v h3,
       rwa holds_folize_zero _ _ h1 at h3 }
| (form₂.lit b a) (k + 1) :=
  begin
    intros M h0 h1 h2 h3,
    cases h3 with v h3,
    rw holds_folize_succ _ _ (form₂.lit b a) trivial h2 at h3,
    have h5 : (M ₀↦v k ₑ) ⊨exs k (form₂.lit b a) :=
      @holds_exs_of_exv_folize (form₂.lit b a) k _ trivial
        trivial (forall_lt_of_forall_lt_succ h2) ⟨v, h3⟩,
    refine ⟨(v k)ₑ, h5⟩
  end
| (form₂.bin b p q) 0 :=
  by { intros M h0 h1 h2 h3,
       cases h3 with v h3,
       rwa holds_folize_zero _ _ h1 at h3 }
| (form₂.bin b p q) (k + 1) :=
  begin
intros M h0 h1 h2 h3,
    cases h3 with v h3,
    rw holds_folize_succ _ _ (form₂.bin b p q) h1 h2 at h3,
    have h5 : (M ₀↦v k ₑ) ⊨ exs k (form₂.bin b p q) :=
      @holds_exs_of_exv_folize (form₂.bin b p q) k _ h0
        h1 (forall_lt_of_forall_lt_succ h2) ⟨v, h3⟩,
    refine ⟨(v k)ₑ, h5⟩,
  end
| (form₂.qua tt p) k :=
  begin
    intros M h0 h1 h2 h3,
    have h5 : p.fov_lt (k + 1),
    { rintro ⟨m⟩; intro h4,
      { exact h0.left rfl },
      rw succ_lt_succ_iff at h4,
      exact h2 _ h4 },
    rw exs_ex,
    exact @holds_exs_of_exv_folize p (k + 1)
      M h0.right h1.right h5 h3,
  end
| (form₂.qua ff p) k := λ _ _  h, by cases h.left

lemma fam_of_tas_folize_zero :
  ∀ {p : form₂}, foq tt p → p.QF tt →
  (p.folize 0).tas α → fam α p :=
λ p h0 h1 h2 M, @holds_exs_of_exv_folize
  α p 0 M h0 h1 forall_lt_zero (h2 M)

lemma fam_of_tas_folize :
  ∀ p : form₂, foq tt p → p.QDF ff →
  (p.folize 0).tas α → fam α p
| (form₂.lit b a)   := fam_of_tas_folize_zero
| (form₂.bin b p q) := fam_of_tas_folize_zero
| (form₂.qua tt p)  :=
  by { intros h0 h1 h2,
       apply fam_of_tas_folize_zero h0 _ h2,
       refine ⟨rfl, h1.right (λ h3, by cases h3)⟩ }
| (form₂.qua ff p)  :=
  λ h0 h1 h2, (fam_fa _ _).elim_right
    (fam_of_tas_folize p h0.right (h1.left rfl) h2)
