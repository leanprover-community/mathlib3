/-
  Copyright (c) 2019 Seul Baek. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Seul Baek

  CNF formulas.
-/

import tactic.vampire.list
import tactic.vampire.folize
import tactic.vampire.misc
import data.list.min_max

universe u

variable {α : Type u}

open list

namespace vampire

local notation `&`     := term.sym
local notation a `&` b := term.app a b
local notation a `#` k := term.vpp a k

local notation `⟪` b `,` a `⟫` := form.lit b a
local notation p `∨₁` q        := form.bin tt p q
local notation p `∧₁` q        := form.bin ff p q

@[reducible] def lit : Type := bool × term
@[reducible] def cla : Type := list lit
@[reducible] def mat : Type := list cla

namespace lit

meta def to_expr : lit → expr
| (b, t) := expr.mk_app `(@prod.mk bool term) [b.to_expr, t.to_expr]

def neg : lit → lit
| ⟨b, a⟩ := ⟨bnot b, a⟩

def repr : lit → string
| ⟨b, a⟩ := (if b then "" else "¬") ++ a.repr

instance has_repr : has_repr lit := ⟨repr⟩
meta instance has_to_format : has_to_format lit := ⟨λ x, repr x⟩

def vars : lit → list nat
| ⟨b, a⟩ := a.vars

def holds (M : model α) (v : nat → α) : lit → Prop
| (tt, a)  :=    (a.val M v []).snd
| (ff, a)  :=  ¬ (a.val M v []).snd

def subst (σ : smaps) : lit → lit
| (b, a) := (b, a.subst σ)

lemma holds_neg (M : model α) (v : nat → α) (l : lit) :
  holds M v l.neg ↔ ¬ holds M v l :=
by { cases l with b; cases b; simp only
     [bnot, neg, holds, list.map, classical.not_not] }

lemma holds_subst (M : model α) (v : vas α) (σ : smaps) (l : lit) :
  holds M v (l.subst σ) ↔ holds M (v.subst M σ) l :=
by { cases l with b a, cases b;
     simp only [holds, subst, vas.subst,
     list.map_map, term.val_subst] }

end lit

def cnf : form → mat
| ⟪b, t⟫   := [[(b, t)]]
| (p ∨₁ q) :=
  (list.product (cnf p) (cnf q)).map
    (λ x, append x.fst x.snd)
| (p ∧₁ q) := (cnf p) ++ (cnf q)

namespace cla

meta def to_expr : cla → expr
| []       := `(@list.nil lit)
| (l :: c) := expr.mk_app `(@list.cons lit) [l.to_expr, to_expr c]

def subst (π : smaps) : cla → cla :=
list.map (lit.subst π)

def holds (M : model α) (v : vas α) (c : cla) : Prop :=
∃ l ∈ c, lit.holds M v l

def fav (M : model α) (c : cla) : Prop :=
∀ v : vas α, holds M v c

def satisfies (M : model α) (c : cla) : Prop :=
∀ v : vas α, holds M v c

lemma holds_subst (M : model α) (v : vas α) (μ : smaps) (c : cla) :
  holds M v (c.subst μ) ↔ holds M (v.subst M μ) c :=
begin
  simp only [cla.subst, vas.subst, cla.holds],
  apply @list.exists_mem_iff_exists_mem_map lit lit _
  (lit.holds M v) (lit.subst μ) (lit.holds_subst _ _ _)
end

def vars : cla → list nat
| c := (c.map (term.vars ∘ prod.snd)).foldl list.union []

def fresh_var : cla → nat
| c := ((c.map prod.snd).map term.fresh_var).maximum

def tautology : cla := [(ff, & 0), (tt, & 0)]

end cla

namespace mat

meta def to_expr : mat → expr
| []       := `(@list.nil cla)
| (c :: m) := expr.mk_app `(@list.cons cla) [c.to_expr, to_expr m]

def holds (M : model α) (v : nat → α) (m : mat) : Prop :=
∀ c ∈ m, cla.holds M v c

def fav (M : model α) (m : mat) : Prop :=
∀ v : vas α, m.holds M v

def repr_core : nat → mat → string
| _ []  := ""
| k [c] := k.repr ++ ". " ++ c.repr
| k (c :: m) :=
  k.repr ++ ". " ++ c.repr ++ "\n" ++ repr_core (k + 1) m

def repr : mat → string := repr_core 1

instance has_repr : has_repr mat := ⟨repr⟩

def nth (m : mat) (k : nat) : cla :=
option.get_or_else (list.nth m k) cla.tautology

end mat

lemma holds_cnf_of_holds {M : model α} {v : nat → α} :
  ∀ p : form, p.holds M v → (cnf p).holds M v
| ⟪b, a⟫ h0 :=
  begin
    intros c h1, cases b;
    rw eq_of_mem_singleton h1;
    refine ⟨_, or.inl rfl, _⟩;
    apply h0
  end
| (p ∧₁ q) h0 :=
  begin
    cases h0 with hp hq,
    replace hp := holds_cnf_of_holds _ hp,
    replace hq := holds_cnf_of_holds _ hq,
    simp only [mat.holds, cnf],
    rw forall_mem_append, refine ⟨hp, hq⟩
  end
| (p ∨₁ q) h0 :=
  begin
    simp only [mat.holds, cnf, mem_map],
    rintros c ⟨⟨c1, c2⟩, h1, h2⟩,
    simp only [prod.fst, prod.snd] at h2, subst h2,
    rw mem_product at h1, cases h1 with hc1 hc2,
    simp only [cla.holds, exists_mem_append],
    cases h0; [left, right];
    apply holds_cnf_of_holds _ h0 _;
    assumption
  end

def term.to_tptp_core : term → list char
| (& k) := ('s' :: k.repr.data).reverse
| (t & s) :=
  match term.to_tptp_core t with
  | [] := []
  | (')' :: cs) :=
    ')' :: (term.to_tptp_core s ++ (',' :: cs))
  | (c :: cs) :=
    ')' :: (term.to_tptp_core s ++ ('(' :: c :: cs))
  end
| (t # k) :=
  match term.to_tptp_core t with
  | [] := []
  | (')' :: cs) :=
    ')' :: (('X' :: k.repr.data).reverse ++ (',' :: cs))
  | (c :: cs) :=
    ')' :: (('X' :: k.repr.data).reverse ++ ('(' :: c :: cs))
  end


/- Translation to TPTP format -/

def term.to_tptp (t : term) : string :=
⟨(term.to_tptp_core t).reverse⟩

def lit.to_tptp : lit → string
| (tt, t) := t.to_tptp
| (ff, t) := "~ " ++ t.to_tptp

def cla.to_tptp : nat → cla → string
| k c :=
  "cnf(c" ++ k.repr ++ ", negated_conjecture, (" ++
   ( match c.map lit.to_tptp with
     | []        := ""
     | (s :: ss) := ss.foldl (λ x y , x ++ " | " ++ y ) s
     end )
   ++ "))."

def mat.to_tptp_core : nat → mat → string
| _ []       := ""
| k (c :: m) := cla.to_tptp k c ++ " " ++ mat.to_tptp_core (k + 1) m

def mat.to_tptp (m : mat) : string := mat.to_tptp_core 1 m

end vampire
