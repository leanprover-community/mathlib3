/-
  Copyright (c) 2019 Seul Baek. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Seul Baek

  Pulling quantifiers for Skolemization and prenex normalization.
-/

import tactic.vampire.fov

universe u

variables {α β : Type u}

open nat

namespace vampire

local notation f `₀↦` a := assign a f
local notation `#` := term₂.var
local notation a `&` b := term₂.app a b

postfix  `ₑ` : 1000 := evaluate
postfix  `ᵈ` : 1000 := denote
local infix `⬝` := value.app

local notation `⟪` b `,` a `⟫` := form₂.lit b a
local notation p `∨*` q        := form₂.bin tt p q
local notation p `∧*` q        := form₂.bin ff p q
local notation `∃*`            := form₂.qua tt
local notation `∀*`            := form₂.qua ff

def pull_fa_left_eqv [inhabited α] (b : bool) (p q : form₂) :
  ∀* (form₂.bin b p q.incr) <==α==> form₂.bin b (∀* p) q :=
begin
  intro M,
  have v : value α := (default α)ₑ,
  constructor; intro h0; cases b,
  { constructor,
    { intro w, exact (h0 w).left },
    apply (holds_assign_incr _).elim_left (h0 v).right },
  { cases classical.em ((M ₀↦ v) ⊨ q.incr) with h2 h2,
    { rw holds_assign_incr at h2,
      right, exact h2 },
    left, intro w,
    cases (h0 w) with h3 h3,
    { exact h3 },
    rw holds_assign_incr at h2,
    rw holds_assign_incr at h3,
    cases (h2 h3) },
  { intro w,
    refine ⟨h0.left _, _⟩,
    rw holds_assign_incr,
    exact h0.right },
  { intro w,
    cases classical.em ((M ₀↦ w) ⊨ q.incr) with h1 h1,
    { right, exact h1 },
    left, cases h0 with h2 h2,
    { apply h2 },
    rw holds_assign_incr at h1,
    cases (h1 h2) }
end

def pull_ex_left_eqv [inhabited α] (b : bool) (p q : form₂) :
  ∃* (form₂.bin b p q.incr) <==α==> form₂.bin b (∃* p) q :=
by { rw ← neg_eqv_neg,
     simp only [form₂.neg, neg_incr,
     bnot, pull_fa_left_eqv] }

def pull_left_eqv [inhabited α] (ae ao : bool) (p q : form₂) :
  form₂.qua ae (form₂.bin ao p q.incr) <==α==>
  form₂.bin ao (form₂.qua ae p) q :=
by {cases ae, apply pull_fa_left_eqv, apply pull_ex_left_eqv }

def pull_right_eqv [inhabited α] (ae ao : bool) (p q : form₂) :
  form₂.qua ae (form₂.bin ao p.incr q) <==α==>
  form₂.bin ao p (form₂.qua ae q) :=
begin
  have h0 : ( form₂.qua ae (form₂.bin ao (form₂.incr p) q) <==α==>
              form₂.qua ae (form₂.bin ao q (form₂.incr p)) ) :=
  qua_eqv_qua (bin_comm _ _ _),
  intro M,
  simp only [ h0 M, pull_left_eqv ae ao q p M,
    bin_comm ao p (form₂.qua ae q) M ]
end

def pull' (o : option bool) (a : bool) : form₂ → form₂ → form₂
| p ⟪b, t⟫            := form₂.bin a p ⟪b, t⟫
| p (form₂.bin c q r) := form₂.bin a p (form₂.bin c q r)
| p (form₂.qua c q)   :=
  if (some $ bnot c) = o
  then form₂.bin a p (form₂.qua c q)
  else form₂.qua c (pull' p.incr q)

/- Pull quantifiers over a binary connective.
   'o' specifies the polairy of quantifiers being
   pulled, `b` specifies the binary connective. -/
def pull (o : option bool) (b : bool) : form₂ → form₂ → form₂
| ⟪c, t⟫            q := pull' o b ⟪c, t⟫ q
| (form₂.bin c p q) r := pull' o b (form₂.bin c p q) r
| (form₂.qua c p)   q :=
  if (some $ bnot c) = o
  then pull' o b (form₂.qua c p) q
  else form₂.qua c (pull p q.incr)

@[reducible] def form₂.size_of_ordered :
  (Σ' (b : bool), (Σ' (a : form₂), form₂)) → nat
| ⟨tt, p, q⟩ := p.size_of + q.size_of + 1
| ⟨ff, p, q⟩ := p.size_of + q.size_of

meta def form₂.show_size_lt : tactic unit :=
`[ simp only [form₂.size_of_ordered, form₂.size_of,
   nat.lt_succ_self, add_comm, add_lt_add_iff_left,
   add_left_comm, form₂.size_of_incr ] ]

lemma fov_pull' (o : option bool) (b : bool) :
  ∀ {p q : form₂} {k : nat},
  p.fov k → q.fov k → (pull' o b p q).fov k
| p ⟪b, t⟫            k h0 h1 := ⟨h0, h1⟩
| p (form₂.bin c q r) k h0 h1 := ⟨h0, h1⟩
| p (form₂.qua c q)   k h0 h1 :=
  by { apply ite_cases,
       refine ⟨h0, h1⟩,
       apply fov_pull' (fov_incr h0) h1 }

lemma fov_pull (o : option bool) (b : bool) :
  ∀ {p q : form₂} {k : nat},
  p.fov k → q.fov k → (pull o b p q).fov k
| ⟪c, t⟫            q k h0 h1 := fov_pull' _ _ h0 h1
| (form₂.bin c p q) r k h0 h1 := fov_pull' _ _ h0 h1
| (form₂.qua c p)   q k h0 h1 :=
  by { apply ite_cases,
       { apply fov_pull' _ _ h0 h1 },
       apply fov_pull _ (fov_incr h1),
       exact h0 }

lemma foq_pull' (o : option bool) (a b : bool) :
  ∀ {p q : form₂}, foq a p → foq a q → foq a (pull' o b p q)
| p ⟪b, t⟫            h0 h1 := ⟨h0, h1⟩
| p (form₂.bin b q r) h0 h1 := ⟨h0, h1⟩
| p (form₂.qua b q)   h0 h1 :=
  begin
    apply ite_cases,
    { refine ⟨h0, h1⟩ },
    constructor,
    { intro h2,
      apply fov_pull' _ _ _ (h1.left h2),
      apply form₂.fov_of_not_occ,
      apply form₂.not_occ_incr_ge },
    apply foq_pull' _ h1.right,
    apply foq_incr_ge h0,
  end

lemma foq_pull (o : option bool) (a b : bool) :
  ∀ {p q : form₂}, foq a p → foq a q → foq a (pull o b p q)
| ⟪c, t⟫            q h0 h1 := foq_pull' _ _ _ h0 h1
| (form₂.bin c p q) r h0 h1 := foq_pull' _ _ _ h0 h1
| (form₂.qua c p)   q h0 h1 :=
  begin
    apply ite_cases,
    { apply foq_pull' _ _ _ h0 h1 },
    constructor,
    { intro h2,
      apply fov_pull _ _  (h0.left h2),
      apply form₂.fov_of_not_occ,
      apply form₂.not_occ_incr_ge },
    apply foq_pull h0.right (foq_incr_ge h1),
  end

def pull'_eqv [inhabited α] (o : option bool) (a : bool) :
  ∀ p q : form₂, pull' o a p q <==α==> form₂.bin a p q
| p ⟪c, t⟫            := eqv_refl α _
| p (form₂.bin b q r) := eqv_refl α _
| p (form₂.qua b q)   :=
  begin
    unfold pull',
    apply @ite_cases _ (λ x, x <==α==> form₂.bin a p (form₂.qua b q)),
    { apply eqv_refl },
    apply eqv_trans
      (qua_eqv_qua $ pull'_eqv p.incr q)
      (pull_right_eqv _ _ _ _)
  end

def pull_eqv [inhabited α] (o : option bool) (a : bool) :
  ∀ p q : form₂, pull o a p q <==α==> form₂.bin a p q
| ⟪b, t⟫            q := pull'_eqv o a _ _
| (form₂.bin b p q) r := pull'_eqv o a _ _
| (form₂.qua b p)   q :=
  begin
    unfold pull,
    apply @ite_cases _ (λ x, x <==α==> form₂.bin a (form₂.qua b p) q),
    { apply pull'_eqv },
    apply eqv_trans
      (qua_eqv_qua $ pull_eqv p q.incr)
      (pull_left_eqv _ _ _ _)
  end

open form₂

lemma QN_pull' (a b : bool) :
  ∀ {p q : form₂}, p.N a → q.QN a →
  (pull' (some a) b p q).QN a
| p ⟪c, t⟫ h0 h1      := ⟨h0, h1⟩
| p (bin c q r) h0 h1 := ⟨h0, h1⟩
| p (qua c q)  h0 h1 :=
  begin
    unfold pull',
    by_cases h2 : a = bnot c,
    { rw [← h2, if_pos rfl],
      rw eq_bnot_iff_ne at h2,
      refine ⟨h0, ⟨h2, h1.right h2⟩⟩ },
    rw if_neg,
    { have h3 : a = c,
      { rw eq_bnot_iff_ne at h2,
        apply not_not.elim_left h2 },
      refine ⟨λ _, _, λ h4, absurd h3 h4⟩,
      apply QN_pull' _ (h1.left h3),
      apply N_incr_ge _ h0 },
    rw option.some_inj,
    intro h3, cases (h2 h3.symm)
  end

lemma QN_pull (a b : bool) :
  ∀ {p q : form₂}, p.QN a → q.QN a →
  (pull (some a) b p q).QN a
| ⟪c, t⟫ q h0 h1      := QN_pull' _ _ h0 h1
| (bin _ p q) r h0 h1 := QN_pull' _ _ h0 h1
| (qua c p) q h0 h1 :=
  begin
    unfold pull,
    by_cases h2 : a = bnot c,
    { rw [← h2, if_pos rfl],
      rw eq_bnot_iff_ne at h2,
      apply QN_pull' _ _ _ h1,
      refine ⟨h2, h0.right h2⟩ },
    rw if_neg,
    { rw [eq_bnot_iff_ne, not_not] at h2,
      refine ⟨λ _, _, λ h3, absurd h2 h3⟩,
      apply QN_pull (h0.left h2),
      apply form₂.QN_incr_ge _ h1 },
    rw option.some_inj,
    intro h3, cases h2 h3.symm
  end

lemma QF_pull' (a b : bool) :
  ∀ {p q : form₂}, p.F → q.QF a →
  (pull' none b p q).QF a
| p ⟪c, t⟫      h0 h1 := ⟨h0, h1⟩
| p (bin c q r) h0 h1 := ⟨h0, h1⟩
| p (qua c q)   h0 h1 :=
  begin
    unfold pull', rw if_neg,
    { refine ⟨h1.left, QF_pull' (F_incr_ge _ h0) h1.right⟩ },
    rintro ⟨_⟩
  end

lemma QF_pull {b : bool} (ao : bool) :
  ∀ {p q : form₂}, p.QF b → q.QF b →
  (pull none ao  p q).QF b
| ⟪_, _⟫      q h0 h1 := QF_pull' _ _ h0 h1
| (bin _ _ _) q h0 h1 := QF_pull' _ _ h0 h1
| (qua c p) q h0 h1 :=
  begin
    unfold pull, rw if_neg,
    { refine ⟨h0.left, QF_pull h0.right (form₂.QF_incr_ge _ h1)⟩ },
    intro h2, cases h2
  end

end vampire
