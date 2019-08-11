/-
  Copyright (c) 2019 Seul Baek. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Seul Baek

  Pulling quantifiers for Skolemization and prenex normalization.
-/

import algebra.order
import tactic.rcases
import data.nat.basic
import tactic.vampire.alt.form

namespace alt

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

def prenexify : form → form
| (form.lit l)     := form.lit l
| (form.bin b f g) := pull b (prenexify f) (prenexify g)
| (form.qua b f)   := form.qua b (prenexify f)

lemma prenexify_eqv [inhabited α] :
  ∀ f : form, prenexify f <==α==> f
| (form.lit l) := eqv_refl _
| (form.bin b f g) :=
  begin
    apply eqv_trans (@pull_eqv α _ _ _ _),
    apply bin_eqv_bin;
    apply prenexify_eqv,
  end
| (form.qua b f) := qua_eqv_qua (prenexify_eqv _)

lemma QF_prenexify :
  ∀ f : form, (prenexify f).QF
| (form.lit l) := trivial
| (form.bin b f g) :=
  by { apply QF_pull; apply QF_prenexify }
| (form.qua b f) := QF_prenexify f

#exit
lemma fresh_vdx_pull_core (b : bool) :
  ∀ {k : nat}, ∀ {f g : form},
  k = f.cons_qua_count + g.cons_qua_count →
  (pull_core b k f g).fresh_vdx = max f.fresh_vdx g.fresh_vdx
| 0 f g h0 :=
  by simp only [pull_core, form.fresh_vdx]
| (k + 1) f g h0 :=
  begin
    rcases f with lf | ⟨bf, f1, f2⟩ | ⟨_ | _, f⟩;
    rcases g with lg | ⟨bg, g1, g2⟩ | ⟨_ | _, g⟩;
    try { apply false.elim (succ_ne_zero _ h0) },
    { simp only [pull_core, form.fresh_vdx],
      rw fresh_vdx_pull_core,

    }

  end


lemma fresh_vdx_pull (b : bool) (f g : form) :
  (pull b f g).fresh_vdx = max f.fresh_vdx g.fresh_vdx :=
fresh_vdx_pull_core _ rfl

lemma fresh_vdx_prenexify :
  ∀ f : form, (prenexify f).fresh_vdx = f.fresh_vdx
| (form.lit l) := rfl
| (form.bin b f g) :=
  by simp only [ prenexify, form.fresh_vdx,
       fresh_vdx_pull, fresh_vdx_prenexify ]
| (form.qua b f) :=
   by simp [ prenexify, form.fresh_vdx,
        fresh_vdx_prenexify f ]




#exit

lemma holds_pull_core_ff [inhabited α]  :
  ∀ {k : nat} {V : vas α} {f g : pnf},
  k = f.qua_count + g.qua_count →
  f.holds R F V → g.holds R F V →
  (pull_core ff k f g).holds R F V
| 0 V (pnf.qf f)    (pnf.qf g)    h0 hf hg := ⟨hf, hg⟩
| 0 V (pnf.qua _ f) g             h0 hf hg :=
  by { simp only [pnf.qua_count, succ_add] at h0, cases h0 }
| 0 V f             (pnf.qua _ g) h0 hf hg :=
  by { simp only [pnf.qua_count, succ_add] at h0, cases h0 }
| (k + 1) V (pnf.qua ff f) g h0 hf hg :=
  begin

    -- cases g with g b g; try { cases b };
    -- { intro a,
    --   apply holds_pull_core_ff _ (hf a),
    --   { rw holds_vinc (insert_result_zero _ _),
    --     exact hg },
    --   simp only [pnf.qua_count, add_zero] at h0,
    --   rw (succ_inj h0),
    --   simp only [ pnf.qua_count, pnf.vinc,
    --     add_def, add_zero ] },


  end


  #exit

| (k + 1) f (pnf.qua ff g) h0 hf hg := sorry
| (k + 1) (pnf.qua tt f) g h0 hf hg := sorry
| (k + 1) f (pnf.qua tt g) h0 hf hg := sorry
| (k + 1) (pnf.qf f) (pnf.qf g) h0 hf hg := by cases h0



#exit
lemma holds_pull_ff [inhabited α] (b : bool) :
  ∀ {f g : pnf}, f.holds R F V → g.holds R F V →
  (pull ff f g).holds R F V := sorry
--

#exit

lemma holds_prenexify : -- [inhabited α] :
  ∀ f : form, f.holds R F V → (prenexify f).holds R F V
| ⟪l⟫              h0 := h0
| (form.bin b f g) h0 :=
  begin
    have hf := holds_prenexify f,
    have hg := holds_prenexify g,
    cases b; cases h0,
    { unfold prenexify,



     }
    -- apply eqv_trans (@pull_eqv α _ _ _ _ _ _ _),
    -- apply bin_eqv_bin;
    -- apply prenexify_eqv,
  end

#exit
#exit
def pull (b : bool) : form → form → list nat → list nat → form
| (∀* f) g ms ns :=
  ∀* (pull f g (ms.map nat.succ) (0 :: ns))
| f (∀* g) ms ns :=
  ∀* (pull f g (0 :: ms) (ns.map nat.succ))
| (∃* f) g ms ns :=
  ∃* (pull f g (ms.map nat.succ) (0 :: ns))
| f (∃* g) ms ns :=
  ∃* (pull f g (0 :: ms) (ns.map nat.succ))
| f g ms ns := form.bin b (f.vincs ms) (g.vincs ns)











def ex_bin_vinc_zero (b : bool) (f g : form) :
  ∃* (form.bin b f (g.vinc 0)) <==α==> (form.bin b (∃* f) g) :=
by { rw ← neg_eqv_neg,
     simp only [ form.neg, neg_vinc 0,
       bnot, fa_bin_vinc_zero_eqv ] }

def qua_bin_vinc_zero (ae ao : bool) (p q : form) :
  form.qua ae (form.bin ao p (q.vinc 0)) <==α==>
  form.bin ao (form.qua ae p) q :=
by { cases ae,
     apply fa_bin_vinc_zero_eqv,
     apply ex_bin_vinc_zero }

lemma bin_comm (b : bool) (p q : form) :
  form.bin b p q <==α==> form.bin b q p :=
by { intros R F V, cases b, apply and.comm, apply or.comm }

def qua_vinc_zero_bin (ae ao : bool) (p q : form) :
  form.qua ae (form.bin ao (p.vinc 0) q) <==α==>
  form.bin ao p (form.qua ae q) :=
begin
  have h0 : ( form.qua ae (form.bin ao (p.vinc 0) q) <==α==>
              form.qua ae (form.bin ao q (p.vinc 0)) ) :=
  qua_eqv_qua (bin_comm _ _ _),
  intros R F V,
  simp only [ h0 R F V, qua_bin_vinc_zero ae ao q p R F V,
    bin_comm ao p (form.qua ae q) R F V ]
end

lemma vincs_qua (b : bool) (f : form) :
  ∀ (ms : list nat),
  form.qua b (f.vincs $ ms.map nat.succ) =
  (form.qua b f).vincs ms
| []        := rfl
| (m :: ms) :=
  begin
    unfold form.vincs,
    rw ← vincs_qua ms,
    apply congr_arg,
    simp only [ form.vinc, form.vincs,
                and_self, list.map]
  end


lemma pull_eqv [inhabited α] (b : bool) :
  ∀ (f g : form) (ms ns : list nat),
  (pull b f g ms ns) <==α==>
  (form.bin b (f.vincs ms) (g.vincs ns))
| (form.lit _ _)   (form.lit _ _)   ms ns := by simp only [pull, eqv_refl]
| (form.lit _ _)   (form.bin _ _ _) ms ns := by simp only [pull, eqv_refl]
| (form.bin _ _ _) (form.lit _ _)   ms ns := by simp only [pull, eqv_refl]
| (form.bin _ _ _) (form.bin _ _ _) ms ns := by simp only [pull, eqv_refl]
| (form.qua bf f) (form.lit bg ag) ms ns :=
  begin
    cases bf;
    { unfold pull,
      apply eqv_trans (qua_eqv_qua $ pull_eqv _ _ _ _),
      rw ← vincs_qua,
      apply (qua_bin_vinc_zero _ _ _ _),
      assumption },
  end
| (form.qua bf f) (form.bin bg g1 g2) ms ns :=
  begin
    cases bf;
    { unfold pull,
      apply eqv_trans (qua_eqv_qua $ pull_eqv _ _ _ _),
      rw ← vincs_qua,
      apply (qua_bin_vinc_zero _ _ _ _),
      assumption },
  end
| (form.lit bf af) (form.qua bg g) ms ns :=
  begin
    cases bg;
    { unfold pull,
      apply eqv_trans (qua_eqv_qua $ pull_eqv _ _ _ _),
      rw ← vincs_qua,
      apply (qua_vinc_zero_bin _ _ _ _),
      assumption },
  end
| (form.bin bf f1 f2) (form.qua bg g) ms ns :=
  begin
    cases bg;
    { unfold pull,
      apply eqv_trans (qua_eqv_qua $ pull_eqv _ _ _ _),
      rw ← vincs_qua,
      apply (qua_vinc_zero_bin _ _ _ _),
      assumption },
  end
| (∀* f) (∀* g) ms ns :=
  begin
    unfold pull,
    apply eqv_trans (qua_eqv_qua $ pull_eqv _ _ _ _),
    apply eqv_trans (qua_bin_vinc_zero _ _ _ _),
    rw vincs_qua,
    apply eqv_refl,
    assumption
  end
| (∃* f) (∃* g) ms ns :=
  begin
    unfold pull,
    apply eqv_trans (qua_eqv_qua $ pull_eqv _ _ _ _),
    apply eqv_trans (qua_bin_vinc_zero _ _ _ _),
    rw vincs_qua,
    apply eqv_refl,
    assumption
  end
| (∀* f) (∃* g) ms ns :=
  begin
    unfold pull,
    apply eqv_trans (qua_eqv_qua $ pull_eqv _ _ _ _),
    apply eqv_trans (qua_bin_vinc_zero _ _ _ _),
    rw vincs_qua,
    apply eqv_refl,
    assumption
  end
| (∃* f) (∀* g) ms ns :=
  begin
    unfold pull,
    apply eqv_trans (qua_eqv_qua $ pull_eqv _ _ _ _),
    apply eqv_trans (qua_vinc_zero_bin _ _ _ _),
    rw vincs_qua,
    apply eqv_refl,
    assumption
  end

def prenexify : form → form
| (form.lit b a)   := form.lit b a
| (form.bin b f g) := pull b (prenexify f) (prenexify g) [] []
| (form.qua b f)   := form.qua b (prenexify f)



lemma F_vincs :
  ∀ f : form, ∀ ms : list nat,
  f.F → (f.vincs ms).F
| f []        h0 := h0
| f (m :: ms) h0 :=
  by { apply F_vinc,
       apply F_vincs _ _ h0 }

lemma QF_pull (b : bool) :
  ∀ {f g : form}, ∀ ms ns : list nat,
  f.QF → g.QF → (pull b f g ms ns).QF
| (form.lit _ _)   (form.lit _ _)   ms ns h0 h1 :=
  by { unfold pull, constructor;
       apply F_vincs; assumption }
| (form.lit _ _)   (form.bin b f g) ms ns h0 h1 :=
  by { unfold pull, constructor;
       apply F_vincs; assumption }
| (form.bin _ _ _) (form.lit _ _)   ms ns h0 h1:=
  by { unfold pull, constructor;
       apply F_vincs; assumption }
| (form.bin _ _ _) (form.bin _ _ _) ms ns h0 h1 :=
  by { unfold pull, constructor;
       apply F_vincs; assumption }
| (form.qua bf f) (form.lit bg ag)  ms ns h0 h1 :=
  by { cases bf; unfold pull;
       apply QF_pull; assumption }
| (form.qua bf f) (form.bin bg g1 g2) ms ns h0 h1:=
  by { cases bf; unfold pull;
       apply QF_pull; assumption }
| (form.lit bf af) (form.qua bg g) ms ns h0 h1 :=
  by { cases bg; unfold pull;
       apply QF_pull; assumption }
| (form.bin bf f1 f2) (form.qua bg g) ms ns h0 h1 :=
  by { cases bg; unfold pull;
       apply QF_pull; assumption }
| (∀* f) (∀* g) ms ns h0 h1 :=
  by { unfold pull, apply QF_pull; assumption }
| (∃* f) (∃* g) ms ns h0 h1:=
  by { unfold pull, apply QF_pull; assumption }
| (∀* f) (∃* g) ms ns h0 h1 :=
  by { unfold pull, apply QF_pull; assumption }
| (∃* f) (∀* g) ms ns h0 h1 :=
  by { unfold pull, apply QF_pull; assumption }


#check @max_succ_succ

lemma fresh_vdx_pull (b : bool) :
  ∀ f g : form, ∀ ms ns : list nat,
  (pull b f g ms ns).fresh_vdx =
  max (f.vincs ms).fresh_vdx (g.vincs ns).fresh_vdx
| (form.lit _ _) (form.lit _ _) ms ns :=
  by simp only [pull, form.fresh_vdx]
| (form.lit _ _) (form.bin _ _ _) ms ns :=
  by simp only [pull, form.fresh_vdx]
| (form.bin _ _ _) (form.lit _ _) ms ns :=
  by simp only [pull, form.fresh_vdx]
| (form.bin _ _ _) (form.bin _ _ _) ms ns :=
  by simp only [pull, form.fresh_vdx]
| (form.qua bf f)  (form.lit bg a) ms ns :=
  begin
    cases bf,
    { simp only [pull, form.fresh_vdx],
      rw fresh_vdx_pull,
      apply eq.trans _ (succ_sub_one _),
      rw [← max_succ_succ, ← vincs_qua],
      unfold form.fresh_vdx,
      cases (form.fresh_vdx (form.vincs (list.map succ ms) f)) with k,
      rw zero_max,
      unfold form.vincs,


      }



    -- apply congr_arg (λ x, x - 1),
    -- apply fun_mono_2,

  end
#exit
| (form.qua _ _)  (form.bin bg g1 g2) :=
| (form.lit _ _) (form.qua bg g)    :=
| (form.bin _ _ _) (form.qua bg g) :=
| (∀* f) (∀* g)                       :=
| (∃* f) (∃* g)                       :=
| (∀* f) (∃* g)                       :=
| (∃* f) (∀* g)                       :=
end alt
