/-
  Copyright (c) 2019 Seul Baek. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Seul Baek

  Pulling quantifiers for Skolemization and prenex normalization.
-/

import algebra.order
import tactic.rcases
import data.nat.basic
import tactic.vampire.form

namespace vampire

open nat

variables {α : Type}
variables {R R1 R2 : rls α} {F F1 F2 : fns α} {V V1 V2 : vas α}
variables {b : bool} (f f1 f2 g g1 g2 : form)

local notation f `₀↦` a := assign a f

local notation `#`      := term.fn
local notation t `&t` s := term.tp t s
local notation t `&v` k := term.vp t k

local notation `$`      := atom.rl
local notation a `^t` t := atom.tp a t
local notation a `^v` t := atom.vp a t

local notation `-*` := lit.neg
local notation `+*` := lit.pos

local notation `⟪` l `⟫`       := form.lit l
local notation p `∨*` q        := form.bin tt p q
local notation p `∧*` q        := form.bin ff p q
local notation `∃*`            := form.qua tt
local notation `∀*`            := form.qua ff

local notation R `;` F `;` V `⊨` f := form.holds R F V f

def pull_core (b : bool) : nat → form → form → form
| 0       f      g      := form.bin b f g
| (k + 1) (∀* f) g      := ∀* (pull_core k f (g.vinc 0))
| (k + 1) f      (∀* g) := ∀* (pull_core k (f.vinc 0) g)
| (k + 1) (∃* f) g      := ∃* (pull_core k f (g.vinc 0))
| (k + 1) f      (∃* g) := ∃* (pull_core k (f.vinc 0) g)
| (k + 1) _      _      := form.default

def pull (b : bool) (f g : form) : form :=
pull_core b (f.cons_qua_count + g.cons_qua_count) f g

lemma fa_pull_core (b : bool) (k : nat) (f g : form) :
  pull_core b (k + 1) (∀* f) g =
  ∀* (pull_core b k f (g.vinc 0)) :=
by cases g with l b f g b g; try { cases b }; refl

lemma holds_bin_iff_holds_bin
  {f1 f2 g1 g2 : form} {b : bool} :
  ((R1 ; F1; V1 ⊨ f1) ↔ (R2; F2; V2 ⊨ f2)) →
  ((R1 ; F1; V1 ⊨ g1) ↔ (R2; F2; V2 ⊨ g2)) →
  ( (R1 ; F1 ; V1 ⊨ form.bin b f1 g1) ↔
    (R2 ; F2 ; V2 ⊨ form.bin b f2 g2) ) :=
by { intros h0 h1, cases b;
     apply pred_mono_2; assumption }

def eqv (α : Type) (f g : form) : Prop :=
∀ R : rls α, ∀ F : fns α, ∀ V : vas α, ((R ; F ; V ⊨ f) ↔ (R ; F ; V ⊨ g))

notation p `<==` α `==>` q := eqv α p q

lemma bin_eqv_bin :
  (f1 <==α==> f2) →
  (g1 <==α==> g2) →
  (form.bin b f1 g1 <==α==> form.bin b f2 g2) :=
by { intros h0 h1 R F V,
     apply holds_bin_iff_holds_bin (h0 _ _ _) (h1 _ _ _) }

lemma eqv_refl (f : form) : f <==α==> f := λ _ _ _, iff.rfl

lemma eqv_trans {α : Type} {f g h : form} :
  (f <==α==> g) → (g <==α==> h) → (f <==α==> h) :=
λ h0 h1 R F V, iff.trans (h0 _ _ _) (h1 _ _ _)

lemma qua_eqv_qua {p q : form} {b : bool} :
  (p <==α==> q) → (form.qua b p <==α==> form.qua b q) :=
begin
  intros h0 R F V,
  cases b,
  { apply forall_congr,
    intro a, apply h0 },
  apply exists_congr,
  intro a, apply h0
end

def insert_result {α : Type} (k : nat) (V W : vas α) : Prop :=
  (∀ m < k, V m = W m) ∧ (∀ m ≥ k, V (m + 1) = W m)

def insert_result_succ {k : nat} {V W : vas α} {a : α} :
   insert_result k V W →
   insert_result (k + 1) (V ₀↦ a) (W ₀↦ a) :=
begin
  rintro ⟨h0, h1⟩,
  constructor; intros m h2; cases m,
  { refl },
  { apply h0 _ (lt_of_succ_lt_succ h2) },
  { cases (not_lt_zero _ (lt_of_succ_le h2)) },
  apply h1 _ (succ_le_succ_iff.elim_left h2)
end

lemma holds_qua_iff_holds_qua :
  (∀ a : α, (R1 ; F1; (V1 ₀↦ a) ⊨ f) ↔ (R2 ; F2 ; (V2 ₀↦ a) ⊨ g)) →
  ((R1 ; F1; V1 ⊨ form.qua b f) ↔ (R2 ; F2 ; V2 ⊨ form.qua b g)) :=
begin
  intro h0, cases b,
  apply forall_congr h0,
  apply exists_congr h0
end

lemma term.val_vinc (F : fns α)
  (k : nat) (V W : vas α) (h0 : insert_result k V W) :
    ∀ t : term, (t.vinc k).val F V = t.val F W
| (# m)    := by simp only [term.vinc, term.val]
| (t &t s) :=
  by simp only [term.vinc, term.val,
       term.val_vinc t, term.val_vinc s]
| (t &v m) :=
  begin
    unfold term.vinc,
    by_cases h1 : m < k,
    { rw if_pos h1,
      unfold term.val,
      rw [term.val_vinc t, h0.left _ h1] },
    rw if_neg h1,
    unfold term.val,
    rw not_lt at h1,
    rw [term.val_vinc t, h0.right _ h1],
  end

lemma atom.val_vinc {R : rls α} {F : fns α}
  {k : nat} {V W : vas α} (h0 : insert_result k V W) :
    ∀ a : atom, (a.vinc k).val R F V = a.val R F W
| ($ m)    := by simp only [atom.vinc, atom.val]
| (a ^t t) :=
  by simp only [atom.vinc, term.vinc, atom.val,
       term.val, atom.val_vinc a, term.val_vinc F k V W h0 t]
| (a ^v m) :=
  begin
    unfold atom.vinc,
    by_cases h1 : m < k,
    { rw if_pos h1,
      unfold atom.val,
      rw [atom.val_vinc a, h0.left _ h1] },
    rw if_neg h1,
    unfold atom.val,
    rw not_lt at h1,
    rw [atom.val_vinc a, h0.right _ h1],
  end

lemma holds_vinc :
  ∀ {k : nat}, ∀ {V W : vas α}, (insert_result k V W) →
  ∀ f : form, (f.vinc k).holds R F V ↔ f.holds R F W
| k V W h0 (form.lit l) :=
  by cases l with a a;
     simp only [form.vinc, lit.holds,
       lit.vinc, form.holds,
       atom.val_vinc h0 a]
| k V W h0 (form.bin b f g) :=
  by { apply holds_bin_iff_holds_bin;
       apply holds_vinc h0 _ }
| k V W h0 (form.qua b f) :=
  begin
    apply holds_qua_iff_holds_qua, intro v,
    apply @holds_vinc (k + 1) _ _
      (insert_result_succ h0)
  end

lemma insert_result_zero (V : vas α) (a : α) :
  insert_result 0 (V ₀↦ a) V :=
⟨λ _ h, by cases h, λ _ _, rfl⟩

lemma holds_vinc_zero (a : α) (f : form) :
  (R ; F ; (V ₀↦ a) ⊨ f.vinc 0) ↔ (R ; F ; V ⊨ f) :=
holds_vinc (insert_result_zero _ _) _

def fa_bin_vinc_zero [inhabited α] (b : bool) (f g : form) :
  ∀* (form.bin b f (g.vinc 0)) <==α==> form.bin b (∀* f) g :=
begin
  intros R F V,
  have a : α := (default α),
  constructor; intro h0; cases b,
  { constructor,
    { intro w, exact (h0 w).left },
    rw ← holds_vinc_zero a g,
    exact (h0 a).right },
  { cases classical.em (R ; F ; (V ₀↦ a) ⊨ g.vinc 0) with h2 h2,
    { rw holds_vinc_zero at h2,
      right, exact h2 },
    left, intro w,
    cases (h0 w) with h3 h3,
    { exact h3 },
    rw holds_vinc_zero at h2,
    rw holds_vinc_zero at h3,
    cases (h2 h3) },
  { intro w,
    refine ⟨h0.left _, _⟩,
    rw holds_vinc_zero,
    exact h0.right },
  { intro w,
    cases classical.em (R ; F ; (V ₀↦ w) ⊨ g.vinc 0) with h1 h1,
    { right, exact h1 },
    left, cases h0 with h2 h2,
    { apply h2 },
    rw holds_vinc_zero at h1,
    cases (h1 h2) }
end

lemma cons_qua_count_vinc :
  ∀ f : form, ∀ k : nat,
  (f.vinc k).cons_qua_count = f.cons_qua_count
| (form.lit l) k     := rfl
| (form.bin b f g) k := rfl
| (form.qua b f) k   :=
  by simp only [form.vinc,
      form.cons_qua_count,
      cons_qua_count_vinc _ (k + 1)]


lemma neg_eqv_neg (f g : form) :
  (f.neg <==α==> g.neg) ↔ (f <==α==> g) :=
begin
  apply forall_congr, intro R,
  apply forall_congr, intro F,
  apply forall_congr, intro V,
  rw [holds_neg, holds_neg, @not_iff_not _ _ _ _],
  repeat {apply classical.dec _}
end

lemma neg_vinc :
  ∀ k : nat, ∀ f : form, (f.vinc k).neg = f.neg.vinc k
| k (form.lit l) := by cases l; refl
| k (form.bin b p q) :=
  by simp only [form.neg, form.vinc,
     eq_self_iff_true, neg_vinc, and_self ]
| k (form.qua b p) :=
  by simp only [form.neg, form.vinc,
     eq_self_iff_true, neg_vinc, and_self ]

def ex_bin_vinc_zero [inhabited α] (b : bool) (f g : form) :
  ∃* (form.bin b f (g.vinc 0)) <==α==> (form.bin b (∃* f) g) :=
by { rw ← neg_eqv_neg,
     simp only [ form.neg, neg_vinc 0,
       bnot, fa_bin_vinc_zero ] }

def qua_bin_vinc_zero [inhabited α] (ae ao : bool) (p q : form) :
  form.qua ae (form.bin ao p (q.vinc 0)) <==α==>
  form.bin ao (form.qua ae p) q :=
by { cases ae,
     apply fa_bin_vinc_zero,
     apply ex_bin_vinc_zero }

lemma bin_comm (b : bool) (p q : form) :
  form.bin b p q <==α==> form.bin b q p :=
by { intros R F V, cases b, apply and.comm, apply or.comm }

def qua_vinc_zero_bin [inhabited α] (ae ao : bool) (p q : form) :
  form.qua ae (form.bin ao (p.vinc 0) q) <==α==>
  form.bin ao p (form.qua ae q) :=
begin
  have h0 : (form.qua ae (form.bin ao (p.vinc 0) q) <==α==>
             form.qua ae (form.bin ao q (p.vinc 0))),
  { apply qua_eqv_qua (bin_comm _ _ _) },
  intros R F V,
  simp only [ h0 R F V, qua_bin_vinc_zero ae ao q p R F V,
    bin_comm ao p (form.qua ae q) R F V ]
end

lemma pull_core_eqv [inhabited α] (b : bool) :
  ∀ (k : nat) {f g : form},
  k = f.cons_qua_count + g.cons_qua_count →
  (pull_core b k f g <==α==> form.bin b f g)
| 0       := λ f g h0, eqv_refl _
| (k + 1) :=
  begin
    intros f g h0,
    rcases f with lf | ⟨bf, f1, f2⟩ | ⟨_ | _, f⟩;
    rcases g with lg | ⟨bg, g1, g2⟩ | ⟨_ | _, g⟩;
    try { apply false.elim (succ_ne_zero _ h0) } ;
    { apply eqv_trans (qua_eqv_qua $ pull_core_eqv k _),
      try { apply qua_vinc_zero_bin },
      try { apply qua_bin_vinc_zero },
      simp only [ form.cons_qua_count, zero_add, add_zero,
        cons_qua_count_vinc, succ_add, add_def ] at *,
      apply succ_inj h0 },
  end

lemma F_of_QF_of_cons_qua_count_eq_zero :
  f.QF → f.cons_qua_count = 0 → f.F :=
by { intros h0 h1, cases f with l b f g b f;
     try { trivial }, apply h0 }


lemma F_vinc :
  ∀ f : form, ∀ m : nat,
  f.F → (f.vinc m).F
| (form.lit _)   m h0 := trivial
| (form.bin _ f g) m h0 :=
  by { cases h0, constructor;
       apply F_vinc; assumption }

lemma QF_vinc :
  ∀ f : form, ∀ m : nat,
  f.QF → (f.vinc m).QF
| (form.lit _)   m h0 := trivial
| (form.bin _ f g) m h0 :=
  by { cases h0, constructor;
       apply F_vinc; assumption }
| (form.qua _ f) m h0 := QF_vinc f _ h0

lemma QF_pull_core (b : bool) :
  ∀ (k : nat) {f g : form},
  f.QF → g.QF →
  k = f.cons_qua_count + g.cons_qua_count →
  (pull_core b k f g).QF
| 0 f g hf0 hg0 h1 :=
  begin
    cases eq_zero_of_add_eq_zero h1.symm with hf1 hg1,
    unfold pull_core, constructor;
    apply F_of_QF_of_cons_qua_count_eq_zero;
    assumption,
  end
| (k + 1) f g hf0 hg0 h1 :=
  begin
    rcases f with lf | ⟨bf, f1, f2⟩ | ⟨_ | _, f⟩;
    rcases g with lg | ⟨bg, g1, g2⟩ | ⟨_ | _, g⟩;
    try { trivial };
    try {
      try { cases hf0 with hf00 hf01 },
      try { cases hg0 with hg00 hg01 },
      apply QF_pull_core k;
      try { trivial };
      try { assumption };
      try { constructor;
            apply F_vinc;
            assumption };
      try { apply QF_vinc; assumption },
      try { simp only [form.cons_qua_count,
            cons_qua_count_vinc, add_assoc,
            succ_add] at * },
      apply succ_inj h1 }
  end

lemma QF_pull (b : bool) (f g : form) :
  f.QF → g.QF → (pull b f g).QF :=
begin
  intros h0 h1,
  apply QF_pull_core _ _ _ _ rfl;
  assumption,
end

lemma pull_eqv [inhabited α] (b : bool) (f g : form) :
  (pull b f g <==α==> form.bin b f g) := pull_core_eqv _ _ rfl

def pnf : form → form
| (form.lit l)     := form.lit l
| (form.bin b f g) := pull b (pnf f) (pnf g)
| (form.qua b f)   := form.qua b (pnf f)

lemma pnf_eqv [inhabited α] :
  ∀ f : form, pnf f <==α==> f
| (form.lit l) := eqv_refl _
| (form.bin b f g) :=
  begin
    apply eqv_trans (@pull_eqv α _ _ _ _),
    apply bin_eqv_bin;
    apply pnf_eqv,
  end
| (form.qua b f) := qua_eqv_qua (pnf_eqv _)

lemma QF_pnf :
  ∀ f : form, (pnf f).QF
| (form.lit l) := trivial
| (form.bin b f g) :=
  by { apply QF_pull; apply QF_pnf }
| (form.qua b f) := QF_pnf f

end vampire
