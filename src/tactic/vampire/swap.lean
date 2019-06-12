/-
  Copyright (c) 2019 Seul Baek. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Seul Baek

  Swapping adjacent quantifiers for Skolemization and Herbrandization.
-/

import tactic.vampire.pull

universe u

variables {α β : Type u}

open nat

namespace vampire

local notation f `₀↦` a := assign a f
local infix `⬝` := value.app

local notation `#` := term₂.var
local notation a `&` b := term₂.app a b

local notation `⟪` b `,` a `⟫` := form₂.lit b a
local notation p `∨*` q        := form₂.bin tt p q
local notation p `∧*` q        := form₂.bin ff p q
local notation `∃*`            := form₂.qua tt
local notation `∀*`            := form₂.qua ff

@[reducible] def swap (k : nat) : sub₂ :=
[(k, # (k + 1) & # k), (k + 1, # k)]

lemma subst_swap_var (k m : nat) :
(m = k ∧ (# m).subst (swap k) = (# (k + 1) & # k)) ∨
(m = k + 1 ∧ (# m).subst (swap k) = # k) ∨
(m ≠ k ∧ m ≠ k + 1 ∧ (# m).subst (swap k) = # m) :=
begin
  by_cases h0 : m = k,
  { left, refine ⟨h0, _⟩,
    simp only [ swap, term₂.subst, sub₂.get,
      if_true, h0, eq_self_iff_true ], refl },
  by_cases h1 : m = k + 1,
  { right, left,
    refine ⟨h1, _⟩,
    simp only [ swap, term₂.subst, sub₂.get,
      if_neg h0, if_pos h1 ], refl },
  right, right,
  refine ⟨h0, h1, _⟩,
  simp only [ swap, term₂.subst, sub₂.get,
    if_neg h0, if_neg h1 ], refl
end

namespace term₂

lemma fov_swap_of_ne {k m : nat} (hO : k ≠ m) (hS : k ≠ m + 1) :
  ∀ a : term₂, a.fov k → (a.subst $ swap m).fov k
| (# n) h1 :=
  begin
    rcases subst_swap_var m n
      with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, _, h2⟩; rw h2,
    { refine ⟨hS, trivial⟩ },
    { exact hO },
    exact h1,
  end
| (a & (# n)) h1 :=
  begin
    refine ⟨fov_swap_of_ne _ h1.left, _⟩,
    rcases subst_swap_var m n
      with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, _, h2⟩;
    rw h2; try {exact trivial},
    refine ⟨hS, trivial⟩
  end
| (a & (b & c)) h1 :=
  ⟨fov_swap_of_ne _ h1.left, fov_swap_of_ne (b &c) h1.right⟩

lemma fov_swap (k : nat) :
  ∀ a : term₂, a.fov (k + 1) → (a.subst $ swap k).fov k
| (# m) h0 :=
  begin
    rcases subst_swap_var k m
      with ⟨_, h1⟩ | ⟨h2, h1⟩ | ⟨h2, _, h1⟩;
    rw h1,
    { refine ⟨(succ_ne_self k).symm, trivial⟩ },
    { cases h0 h2.symm },
    exact h2.symm
  end
| (a & (# m)) h0 :=
  begin
    refine ⟨fov_swap _ h0.left, _⟩,
    rcases subst_swap_var k m
      with ⟨_, h1⟩ | ⟨h2, h1⟩ | ⟨h2, _, h1⟩;
    rw h1; try {exact trivial},
    refine ⟨(succ_ne_self _).symm, trivial⟩
  end
| (a & (b & c)) h0 :=
  ⟨fov_swap a h0.left, fov_swap (b &c) h0.right⟩

end term₂

def form₂.swap (k : nat) (p : form₂) : form₂ :=
p.subst (swap k)

lemma holds_swap {M : model α} {v w : value α} {p : form₂} :
  ((M ₀↦ v ₀↦ w) ⊨ p.swap 0) ↔ ((M ₀↦ w ₀↦ v ⬝ w) ⊨ p) :=
begin
  unfold form₂.swap,
  rw holds_subst,
  have h0 : model.subst (M ₀↦ v ₀↦ w) [(0, (# 1) & (# 0)), (1, # 0)] =
            (M ₀↦ w ₀↦ v ⬝ w),
  { rw function.funext_iff,
    intro k, cases k, refl,
    cases k; refl },
  rw h0,
end

def swap_val [inhabited α] (f : value α → value α) : value α
| []        := (default α, false)
| (a :: as) := f (a ₑ) as

lemma exists_swap_val [inhabited α] {M : model α} {p : form₂} :
  (M ⊨ ∀* (∃* p)) → ∃ f : value α, ∀ a : α, (M ₀↦ (a ₑ) ₀↦ f ⬝ a ₑ) ⊨ p :=
begin
  intro h0,
  cases classical.skolem.elim_left h0 with f h1,
  refine ⟨swap_val f, λ a, h1 (a ₑ)⟩,
end

def eq_except (M N : model α) (k : nat) : Prop :=
(∀ m : nat, m ≠ k → M m = N m) ∧ (M k)ᵈ = (N k)ᵈ

lemma assign_eq_except_assign
  {M N : model α} {k : nat} (v : value α) :
  eq_except M N k → eq_except (M ₀↦ v) (N ₀↦ v) (k + 1) :=
begin
  intro h0, constructor,
  { intros m h1, cases m, refl,
    apply h0.left _ (λ h2, h1 _),
    subst h2 },
  exact h0.right
end

lemma val_eq_val_of_eq_except {M N : model α} {k : nat} (h0 : eq_except M N k) :
  ∀ a : term₂, a.fov k → (a.val M = a.val N)
| (# m)   h1 := by apply h0.left _ (ne.symm h1)
| (a & (# m)) h1 :=
  begin
    have h2 : a.val M = a.val N,
    { rw term₂.fov_app_var at h1,
      apply val_eq_val_of_eq_except a h1 },
    have h3 : (M m []).fst  = (N m []).fst,
    { by_cases h4 : k = m,
      { subst h4, apply h0.right },
      rw h0.left _ (ne.symm h4) },
    simp only [term₂.val, h2, h3]
  end
| (a & (b & c)) h1 :=
  begin
    have h2 : a.val M = a.val N,
    { apply val_eq_val_of_eq_except a h1.left },
    have h3 : (b & c).val M = (b & c).val N,
    { apply val_eq_val_of_eq_except (b & c) h1.right },
    simp only [term₂.val, h2, h3]
  end

lemma holds_iff_holds_of_eq_except :
  ∀ {M N : model α} {k : nat} (p : form₂),
  eq_except M N k → p.fov k → (M ⊨ p ↔ N ⊨ p)
| M N k ⟪b, a⟫ h0 h1 :=
  by cases b; simp [form₂.holds, val_eq_val_of_eq_except h0 a h1]
| M N k (form₂.bin b p q) h0 h1 :=
  begin
    cases h1,
    apply form₂.holds_bin_iff_holds_bin;
    apply holds_iff_holds_of_eq_except;
    assumption
  end
| M N k (form₂.qua b p)   h0 h1 :=
  begin
    apply holds_qua_iff_holds_qua, intro v,
    apply holds_iff_holds_of_eq_except _
      (assign_eq_except_assign _ h0) h1
  end

def ex_fa_swap_eqv [inhabited α] (p : form₂) :
  p.fov 1 → (∃* (∀* $ p.swap 0) <==α==> ∀* (∃* p)) :=
begin
  intros h0 M,
  constructor; intro h1,
  { cases h1 with v h1,
    intro w,
    refine ⟨v ⬝ w, _⟩,
    rw ← holds_swap, apply h1 },
  cases exists_swap_val h1 with f h2,
  refine ⟨f, λ v, _⟩,
  have h3 : f ⬝ v = f ⬝ vᵈₑ := rfl,
  rw holds_swap,
  rw [ @holds_iff_holds_of_eq_except _
         (M ₀↦ v ₀↦ f⬝v) (M ₀↦ vᵈₑ ₀↦ f ⬝ v) 1 p _ h0, h3],
  { apply h2 },
  constructor,
  { rintros ⟨n⟩ h3, refl,
    cases m, cases (h3 rfl), refl },
  apply (denote_evaluate (vᵈ))
end

lemma neg_swap {p : form₂} : (p.swap 0).neg <==α==> p.neg.swap 0 :=
neg_subst _ _

def fa_ex_swap_eqv [inhabited α] (p : form₂) :
  p.fov 1 → (∀* (∃* $ p.swap 0) <==α==> ∃* (∀* p)) :=
begin
  intro h0,
  replace h0 := (fov_neg _ _).elim_right h0,
  have h1 : (∃* (∀* (p.swap 0).neg) <==α==> ∀* (∃* p.neg)) :=
  eqv_trans
    (qua_eqv_qua (qua_eqv_qua neg_swap))
    (@ex_fa_swap_eqv α _ _ h0),
  rw ← neg_eqv_neg,
  simp only [holds_neg.symm, form₂.neg, bnot, h1]
end

def swap_eqv [inhabited α] (ae : bool) {p : form₂} :
  p.fov 1 →
  (form₂.qua ae (form₂.qua (bnot ae) $ p.swap 0)
    <==α==> form₂.qua (bnot ae) (form₂.qua ae p)) :=
by { intro h0, cases ae,
     exact fa_ex_swap_eqv _ h0,
     exact ex_fa_swap_eqv _ h0 }

namespace form₂

open nat

lemma fov_swap :
  ∀ {k : nat} {p : form₂}, p.fov (k + 1) → (p.swap k).fov k
| k ⟪b, a⟫           h0 := term₂.fov_swap _ _ h0
| k (form₂.bin b p q) h0 :=
  by { cases h0, constructor;
       apply fov_swap; assumption }
| k (form₂.qua b p)   h0 := @fov_swap (k + 1) p h0

lemma fov_swap_of_ne :
  ∀ k m : nat, (k ≠ m) → (k ≠ m + 1) →
  ∀ p : form₂, p.fov k → (p.swap m).fov k
| k m hO hS ⟪b, a⟫ h1 := term₂.fov_swap_of_ne hO hS _ h1
| k m hO hS (form₂.bin b p q) h1 :=
  by { cases h1, constructor;
       apply fov_swap_of_ne; assumption }
| k m hO hS (form₂.qua b p)   h1 :=
  fov_swap_of_ne (k + 1) (m + 1)
    (succ_ne_succ hO) (succ_ne_succ hS) p h1

end form₂

lemma foq_swap (b : bool) :
  ∀ (k : nat) {p : form₂}, foq b p → foq b (p.swap k)
| k ⟪_, a⟫           h0 := trivial
| k (form₂.bin _ p q) h0 := ⟨foq_swap _ h0.left, foq_swap _ h0.right⟩
| k (form₂.qua c p)   h0 :=
  begin
    constructor,
    { intro h1,
      apply form₂.fov_swap_of_ne 0 (k + 1)
        (@zero_ne_succ _) (@zero_ne_succ _) p (h0.left h1) },
    apply foq_swap _ h0.right
  end

def swap_many (ae : bool) : form₂ → form₂
| (form₂.qua b p) :=
  have form₂.size_of (p.swap 0) < form₂.size_of (form₂.qua b p),
  { unfold form₂.swap,
    have h0 : form₂.size_of p < form₂.size_of (form₂.qua b p),
    { unfold form₂.size_of, apply nat.lt_succ_self },
    have h1 := form₂.size_of_subst p (swap 0),
    apply @eq.rec _ _ (λ x, x < form₂.size_of (form₂.qua b p)) h0 _ h1.symm },
  if ae = b
  then form₂.qua ae (swap_many $ p.swap 0)
  else form₂.qua (bnot ae) (form₂.qua b p)
| p := form₂.qua (bnot ae) p

lemma fov_swap_many (ae : bool) :
  ∀ {p : form₂} {k : nat},
  p.fov (k + 1) → (swap_many ae p).fov k
| ⟪b, a⟫           := λ _, id
| (form₂.bin b p q) := λ _, id
| (form₂.qua b p)   :=
  have form₂.size_of (p.swap 0) < form₂.size_of (form₂.qua b p),
  by { unfold form₂.swap,
       rw form₂.size_of_subst,
       form₂.show_size_lt},
  begin
    intros k h0,
    unfold swap_many,
    by_cases h1 : ae = b,
    { subst h1, rw if_pos rfl,
      have h2 : (p.swap 0).fov (k + 2) :=
      @form₂.fov_swap_of_ne (k + 2) 0 (ne.symm (@zero_ne_succ _))
        (succ_ne_succ $ ne.symm (@zero_ne_succ _)) _ h0,
    apply @fov_swap_many _ (k + 1) h2, },
    rw if_neg h1, exact h0
  end

lemma bnot_ne_self (b : bool) :
  bnot b ≠ b := by { cases b; rintro ⟨_⟩ }

lemma foq_swap_many (b : bool) :
  ∀ {p : form₂}, p.fov 0 → foq b p → foq b (swap_many (bnot b) p)
| (form₂.lit b a)   h0 h1 := ⟨λ _, h0, h1⟩
| (form₂.bin b p q) h0 h1 := ⟨λ _, h0, h1⟩
| (form₂.qua c p)   h0 h1 :=
  have form₂.size_of (form₂.swap 0 p) <
       form₂.size_of (form₂.qua c p),
  { unfold form₂.swap, rw form₂.size_of_subst, form₂.show_size_lt },
  begin
    unfold swap_many,
    by_cases h2 : bnot b = c,
    { rw if_pos h2,
      refine ⟨λ h3, absurd h3.symm (bnot_ne_self b), _⟩,
      apply @foq_swap_many (p.swap 0),
      apply form₂.fov_swap h0,
      apply foq_swap _ _ h1.right },
    rw if_neg h2,
    refine ⟨λ _, h0, h1⟩
  end

lemma swap_many_eqv (α : Type u) [inhabited α] (ae : bool) :
  ∀ {p : form₂}, p.fov 0 →
  (swap_many ae p <==α==> form₂.qua (bnot ae) p)
| ⟪b, a⟫           := λ _, eqv_refl _ _
| (form₂.bin b p q) := λ _, eqv_refl _ _
| (form₂.qua b p)   :=
  have form₂.size_of (p.swap 0) <
       form₂.size_of (form₂.qua b p) :=
  by { unfold form₂.swap,
       rw form₂.size_of_subst,
       form₂.show_size_lt },
  begin
    intro h0,
    unfold swap_many,
    by_cases h1 : ae = b,
    { subst h1, rw if_pos rfl,
      apply eqv_trans _ (@swap_eqv α _ ae _ h0),
      apply qua_eqv_qua,
      apply swap_many_eqv,
      apply form₂.fov_swap,
      apply h0 },
    rw if_neg h1, apply eqv_refl _
  end

def swap_all (ae : bool) : form₂ → form₂
| ⟪b, a⟫           := ⟪b, a⟫
| (form₂.bin b p q) :=
  pull (some ae) b (swap_all p) (swap_all q)
| (form₂.qua b p)   :=
  if ae = b
  then form₂.qua ae (swap_all p)
  else swap_many ae (swap_all p)

lemma fov_swap_all (ae : bool) :
  ∀ {k : nat} {p : form₂}, p.fov k → (swap_all ae p).fov k
| k ⟪b, a⟫           h0 := h0
| k (form₂.bin b p q) h0 :=
  by { cases h0, apply fov_pull;
       apply fov_swap_all; assumption }
| k (form₂.qua b p)   h0 :=
  begin
    unfold swap_all,
    by_cases h1 : ae = b,
    { subst h1, rw if_pos rfl,
      apply @fov_swap_all _ p h0 },
    rw if_neg h1,
    apply fov_swap_many,
    apply fov_swap_all,
    apply h0
  end

lemma foq_swap_all (b : bool) :
  ∀ {p : form₂}, (foq b p) → foq b (swap_all (bnot b) p)
| ⟪_, a⟫           h0 := trivial
| (form₂.bin _ p q) h0 :=
  begin
    unfold swap_all,
    have hp := foq_swap_all h0.left,
    have hq := foq_swap_all h0.right,
    apply foq_pull; assumption
  end
| (form₂.qua c p) h0 :=
  begin
    unfold swap_all,
    by_cases h1 : (bnot b = c),
    { rw if_pos h1,
      refine ⟨ λ h2, absurd h2.symm (bnot_ne_self b),
               foq_swap_all h0.right ⟩ },
    rw if_neg h1,
    have h2 : (swap_all (bnot b) p).fov 0,
    { apply fov_swap_all,
      apply h0.left _,
      rwa [bnot_eq_iff_ne, not_not] at h1 },
    apply foq_swap_many _ h2 (foq_swap_all h0.right)
  end

lemma swap_all_eqv [inhabited α] {ae : bool} :
  ∀ {p : form₂}, foq (bnot ae) p → (swap_all ae p <==α==> p)
| ⟪b, a⟫           h0 := eqv_refl _ _
| (form₂.bin b p q) h0 :=
  eqv_trans
    (pull_eqv ae _ _ _)
    (bin_eqv_bin
      (swap_all_eqv h0.left)
      (swap_all_eqv h0.right))
| (form₂.qua b p)   h0 :=
  begin
    unfold swap_all,
    by_cases h1 : ae = b,
    { subst h1, rw if_pos rfl,
      apply qua_eqv_qua (swap_all_eqv h0.right) },
    have h2 := bnot_eq_iff_ne.elim_right h1,
    rw [if_neg h1, ← h2],
    apply eqv_trans (swap_many_eqv α _
      (fov_swap_all _ (h0.left h2))),
    apply qua_eqv_qua (swap_all_eqv h0.right)
end

def prenexify : form₂ → form₂
| ⟪b, a⟫            := ⟪b, a⟫
| (form₂.bin b p q) := pull none b (prenexify p) (prenexify q)
| (form₂.qua b p)   := form₂.qua b (prenexify p)

lemma fov_prenexify :
  ∀ {k : nat} {p : form₂}, p.fov k → (prenexify p).fov k
| k ⟪_, a⟫           h0 := h0
| k (form₂.bin _ p q) h0 :=
  by { cases h0, apply fov_pull;
       apply fov_prenexify; assumption }
| k (form₂.qua c p)   h0 := @fov_prenexify (k + 1) p h0

lemma foq_prenexify (b : bool) :
  ∀ {p : form₂}, (foq b p) → foq b (prenexify p)
| ⟪_, a⟫           h0 := h0
| (form₂.bin _ p q) h0 :=
  by { cases h0, apply foq_pull;
       apply foq_prenexify; assumption }
| (form₂.qua c p)   h0 :=
  ⟨ λ h1, fov_prenexify (h0.left h1),
    foq_prenexify h0.right ⟩

lemma prenexify_eqv [inhabited α] :
  ∀ p : form₂, prenexify p <==α==> p
| ⟪b, a⟫            := eqv_refl _ _
| (form₂.bin b p q) :=
  begin
    apply eqv_trans (@pull_eqv α _ _ _ _ _),
    apply bin_eqv_bin;
    apply prenexify_eqv
  end
| (form₂.qua b p)   := qua_eqv_qua (prenexify_eqv _)

def QDFy (b : bool) : form₂ → form₂ := prenexify ∘ swap_all b

lemma N_subst {b : bool} :
  ∀ {p : form₂} (σ : sub₂), p.N b → (p.subst σ).N b
| ⟪_, a⟫           _ _ := trivial
| (form₂.bin c p q) _ h := ⟨N_subst _ h.left, N_subst _ h.right⟩
| (form₂.qua c p)   σ h := ⟨h.left, N_subst _ h.right⟩

lemma QN_subst {b : bool} :
  ∀ {p : form₂} (σ : sub₂), p.QN b → (p.subst σ).QN b
| ⟪_, a⟫           _ h0 := trivial
| (form₂.bin c p q) _ h0 :=
  by { cases h0, constructor;
       apply N_subst; assumption }
| (form₂.qua c p)   σ h0 :=
  ⟨ λ h1, QN_subst _ (h0.left h1),
    λ h1, N_subst _ (h0.right h1) ⟩

lemma QN_swap_many {b : bool} :
  ∀ {p : form₂}, p.QN b → (swap_many b p).QN b
| (form₂.lit c a) :=
  λ h0, ⟨ λ h1, absurd h1 (bnot_ne_self b).symm, λ _, h0⟩
| (form₂.bin c p q) :=
  λ h0, ⟨ λ h1, absurd h1 (bnot_ne_self b).symm, λ _, h0⟩
| (form₂.qua c p) :=
  have form₂.size_of (form₂.swap 0 p) <
       form₂.size_of (form₂.qua c p),
  by { unfold form₂.swap,
       rw form₂.size_of_subst,
       form₂.show_size_lt },
  begin
    intro h0, unfold swap_many,
    by_cases h1 : b = c,
    { rw if_pos h1,
      constructor; intro h2,
      { apply QN_swap_many,
        apply QN_subst _ (h0.left h1) },
      cases h2 rfl },
    rw if_neg h1,
    constructor; intro h2,
    { rw eq_bnot_iff_ne at h2,
      cases h2 rfl },
    refine ⟨h1, h0.right h1⟩
  end

lemma QN_swap_all (b : bool) :
  ∀ p : form₂, (swap_all b p).QN b
| ⟪_, a⟫           := trivial
| (form₂.bin c p q) :=
  by { unfold swap_all,
       apply QN_pull;
       apply QN_swap_all }
| (form₂.qua c p)   :=
  begin
    unfold swap_all,
    by_cases h0 : b = c,
    { rw if_pos h0,
      constructor; intro h1,
      { apply QN_swap_all },
      cases (h1 rfl) },
    rw if_neg h0,
    have h1 := QN_swap_all p,
    apply QN_swap_many h1
  end

lemma QF_prenexify {b : bool} :
  ∀ {p : form₂}, p.N b → (prenexify p).QF (bnot b)
| (form₂.lit c a)   h0 := trivial
| (form₂.bin c p q) h0 :=
  by { cases h0, apply QF_pull;
       apply QF_prenexify; assumption }
| (form₂.qua c p)   h0 :=
  by { constructor,
       { rw bnot_eq_iff_ne, apply h0.left },
       apply QF_prenexify h0.right }

lemma QDF_prenexify (b : bool) :
  ∀ p : form₂, p.QN b → (prenexify p).QDF b
| (form₂.lit c a)   h0 := trivial
| (form₂.qua c p)   h0 :=
  begin
    by_cases h1 : b = c,
    { constructor; intro h2,
      { apply QDF_prenexify _ (h0.left h1) },
      cases h2 h1 },
    constructor; intro h2,
    { cases h1 h2 },
    apply QF_prenexify (h0.right h2)
  end
| (form₂.bin c p q) h0 :=
  by { cases h0, apply form₂.QDF_of_QF_bnot,
       apply QF_pull; apply QF_prenexify; assumption }

lemma QDF_QDFy (b : bool) (p : form₂) : (QDFy b p).QDF b :=
by {apply QDF_prenexify, apply QN_swap_all}

end vampire
