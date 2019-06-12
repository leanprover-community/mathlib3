/-
  Copyright (c) 2019 Seul Baek. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Seul Baek

  First-order terms and atoms.
-/

import tactic.vampire.model

universe u

variable {α : Type u}

namespace vampire

@[derive has_reflect, derive decidable_eq]
inductive term : Type
| sym : nat  → term
| app : term → term → term
| vpp : term → nat  → term

local notation `&`     := term.sym
local notation a `&` b := term.app a b
local notation a `#` k := term.vpp a k

open sum

namespace term

meta def to_expr : term → expr
| (& k)   := expr.app `(term.sym) k.to_expr
| (t & s) := expr.mk_app `(term.app) [t.to_expr, s.to_expr]
| (t # k) := expr.mk_app `(term.vpp) [t.to_expr, k.to_expr]

def vars : term → list nat
| (& _)   := []
| (t & s) := t.vars ∪ s.vars
| (t # k) := t.vars.insert k

def fresh_var : term → nat
| (& _)   := 0
| (t & s) := max t.fresh_var s.fresh_var
| (t # k) := max t.fresh_var (k + 1)

def repr : term → string
| (term.sym k)   := "S" ++ k.to_subs
| (term.app t s) := "(" ++ t.repr ++ " " ++ s.repr ++ ")"
| (term.vpp t k) := "(" ++ t.repr ++ " " ++ "X" ++ k.to_subs ++ ")"

def write : term → string
| (term.sym k)   := "S " ++ k.repr
| (term.app t s) := "( " ++ t.write ++ " "   ++ s.write ++ " )"
| (term.vpp t k) := "( " ++ t.write ++ " V " ++ k.repr  ++ " )"

-- def repr : term → string := repr_core tt

instance has_repr : has_repr term := ⟨repr⟩
meta instance has_to_format : has_to_format term := ⟨λ x, repr x⟩

def vdxs : term → list nat
| (term.sym _)   := []
| (term.app a b) := a.vdxs ∪ b.vdxs
| (term.vpp a m) := a.vdxs.insert m

def val (M : model α) (v : nat → α) : term → value α
| (term.sym k)   := M k
| (term.app a b) := a.val ∘ list.cons (b.val []).fst
| (term.vpp a k) := a.val ∘ list.cons (v k)

def holds (M : model α) (v : nat → α) (t : term) : Prop :=
(t.val M v []).snd

def rename (f : nat → nat) : term → term
| (& k) := & k
| (t & s) := t.rename & s.rename
| (t # k) := t.rename # (f k)

end term

@[reducible] def smap : Type := nat × (nat ⊕ term)

meta def smap.to_expr : smap → expr
| (k, sum.inl m) :=
  expr.mk_app
    `(@prod.mk nat (nat ⊕ term))
    [k.to_expr, expr.app `(@sum.inl nat term) m.to_expr]
| (k, sum.inr t) :=
  expr.mk_app
    `(@prod.mk nat (nat ⊕ term))
    [k.to_expr, expr.app `(@sum.inr nat term) t.to_expr]

instance smap.decidable_eq : decidable_eq smap := by apply_instance

@[reducible] def smaps : Type := list smap

meta def smaps.to_expr : smaps → expr
| []        := `(@list.nil smap)
| (m :: ms) := expr.mk_app `(@list.cons smap) [m.to_expr, smaps.to_expr ms]

def smaps.get (k : nat) : smaps → (nat ⊕ term)
| []            := sum.inl k
| ((m, t) :: μ) := if k = m then t else smaps.get μ

def term.subst (μ : smaps) : term → term
| (& k)   := & k
| (t & s) := t.subst & s.subst
| (t # k) :=
  match μ.get k with
  | (sum.inl m) := t.subst # m
  | (sum.inr s) := t.subst & s
  end

def smaps.compose (μ : smaps) : smaps → smaps
| []                    := μ
| ((k, sum.inr t) :: ν) := (k, sum.inr (t.subst μ)) :: smaps.compose ν
| ((k, sum.inl m) :: ν) := (k, μ.get m) :: smaps.compose ν

namespace vas

def subst (M : model α) (v : vas α) (μ : smaps) (k : nat) : α :=
match μ.get k with
| (inl m) := v m
| (inr t) := (t.val M v []).fst
end

lemma subst_eq_of_eq_inl (M : model α)
  (v : vas α) {μ : smaps} {k m : nat} :
μ.get k = inl m → v.subst M μ k = v m :=
by { intro h1, simp only [h1, subst] }

lemma subst_eq_of_eq_inr (M : model α)
  (v : vas α) {μ : smaps} {k : nat} {t : term} :
μ.get k = inr t → v.subst M μ k = (t.val M v []).fst :=
by { intro h1, simp only [h1, subst] }

end vas

namespace term

lemma subst_eq_of_eq_inl {μ : smaps} (t : term) {k m : nat} :
μ.get k = inl m → (t # k).subst μ = t.subst μ # m :=
by { intro h, simp only [h, subst, eq_self_iff_true, and_self] }

lemma subst_eq_of_eq_inr {μ : smaps} (t s : term) {k : nat} :
μ.get k = inr s → (t # k).subst μ = t.subst μ & s :=
by { intro h, simp only [h, subst, eq_self_iff_true, and_self] }

lemma val_rename (M : model α) (v : vas α) (f : nat → nat) :
  ∀ t : term, (t.rename f).val M v = t.val M (v ∘ f)
| (& k)   := rfl
| (t & s) := by simp only [val, rename, val_rename]
| (t # k) := by simp only [val, rename, val_rename]

lemma val_subst (M : model α) (v : vas α) (μ : smaps) :
  ∀ t : term, (t.subst μ).val M v = t.val M (v.subst M μ)
| (& k)   := rfl
| (t & s) := by simp only [val, subst, val_subst]
| (t # k) :=
  begin
    cases h1 : μ.get k with m s,
    { simp only [subst_eq_of_eq_inl t h1,
        vas.subst_eq_of_eq_inl M v h1,
        val_subst, val] },
    simp only [subst_eq_of_eq_inr t s h1,
      vas.subst_eq_of_eq_inr M v h1,
      val_subst, val]
  end

lemma holds_subst (M : model α) (v : vas α) (μ : smaps) (t : term) :
  (t.subst μ).holds M v ↔ t.holds M (v.subst M μ) :=
by {unfold holds, rw val_subst}

lemma holds_rename (M : model α) (v : vas α) (f : nat → nat) (t : term) :
  (t.rename f).holds M v ↔ t.holds M (v ∘ f) :=
by {unfold holds, rw val_rename}

end term

end vampire
