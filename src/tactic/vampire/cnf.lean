/-
  Copyright (c) 2019 Seul Baek. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Seul Baek

  CNF formulas.
-/

import tactic.vampire.pnf
import tactic.vampire.list

namespace vampire

variables {α : Type}

local notation `$`      := atom.rl
local notation a `^t` t := atom.app a t
local notation a `^v` t := atom.vpp a t

local notation `-*` := lit.neg
local notation `+*` := lit.pos

local notation p `∨*` q := form.bin tt p q
local notation p `∧*` q := form.bin ff p q
local notation `∃*` p := form.qua tt p
local notation `∀*` p := form.qua ff p

@[reducible] def cla : Type := list lit
@[reducible] def mat : Type := list cla

open list

def map_app_prod_aux : cla → mat → mat
| lc []          := []
| lc (rc :: rcs) := (lc ++ rc) :: map_app_prod_aux lc rcs

def map_app_prod : mat → mat → mat
| []          rcs := []
| (lc :: lcs) rcs :=
  (list.map (list.append lc) rcs) ++ (map_app_prod lcs rcs)

lemma map_app_prod_nil :
  ∀ m : mat, map_app_prod m [] = []
| []       := rfl
| (c :: m) :=
  by simp only [map_app_prod, map, map_app_prod_nil m, nil_append]

def cnf : form → mat
| (form.lit l)   := [[l]]
| (f ∨* g)       := map_app_prod (cnf f) (cnf g)
| (f ∧* g)       := (cnf f) ++ (cnf g)
| (form.qua _ _) := []

namespace cla

def tautology : cla := [-* ($ 0), +* ($ 0)]

def substs (μ : mappings) : cla → cla :=
list.map (lit.substs μ)

meta def to_expr : cla → expr
| []       := `(@list.nil lit)
| (l :: c) := expr.mk_app `(@list.cons lit) [l.to_expr, to_expr c]

def holds (R : rls α) (F : fns α) (V : vas α) (c : cla) : Prop :=
∃ l ∈ c, lit.holds R F V l

end cla

namespace mat

def repr_core : nat → mat → string
| _ []  := ""
| k [c] := k.repr ++ ". " ++ c.repr
| k (c :: m) :=
  k.repr ++ ". " ++ c.repr ++ "" ++ repr_core (k + 1) m

def repr : mat → string := repr_core 0

instance has_repr : has_repr mat := ⟨repr⟩

def nth (m : mat) (k : nat) : cla :=
option.get_or_else (list.nth m k) cla.tautology

meta def to_expr : mat → expr
| []       := `(@list.nil cla)
| (c :: m) := expr.mk_app `(@list.cons cla) [c.to_expr, to_expr m]

def holds (R : rls α) (F : fns α) (V : vas α) (m : mat) : Prop :=
∀ c ∈ m, cla.holds R F V c

end mat

variables {R : rls α} {F : fns α} {V : vas α}

lemma holds_map_app_prod_left :
  ∀ m n : mat, m.holds R F V →
  (map_app_prod m n).holds R F V
| []       n h0 := list.forall_mem_nil _
| (c :: m) n h0 :=
  begin
    unfold mat.holds at h0,
    simp only [map_app_prod, mat.holds],
    rw forall_mem_append,
    constructor,
    { intros cd h1,
      rw list.mem_map at h1,
      rcases h1 with ⟨d, h1, h2⟩,
      rw ← h2, unfold cla.holds,
      apply exists_mem_append.elim_right,
      left, apply h0 _ (or.inl rfl) },
    apply holds_map_app_prod_left,
    apply forall_mem_of_forall_mem_cons h0
  end

lemma holds_map_app_prod_right :
  ∀ m n : mat, n.holds R F V →
  (map_app_prod m n).holds R F V
| []       n h0 := list.forall_mem_nil _
| (c :: m) n h0 :=
  begin
    unfold mat.holds at h0,
    simp only [map_app_prod, mat.holds],
    rw list.forall_mem_append,
    constructor,
    { intros cd h1,
      rw list.mem_map at h1,
      rcases h1 with ⟨d, h1, h2⟩,
      rw ← h2, unfold cla.holds,
      apply list.exists_mem_append.elim_right,
      right, apply h0 _ h1 },
    apply holds_map_app_prod_right _ _ h0
  end

lemma holds_cnf [inhabited α] :
  ∀ {f : form}, f.F → f.holds R F V → (cnf f).holds R F V
| (form.lit l) h0 h1 :=
  begin
    intros c h2,
    rw list.eq_of_mem_singleton h2,
    refine ⟨_, or.inl rfl, _⟩,
    exact h1,
  end
| (f ∧* g) h0 h1 :=
  begin
    cases h0 with h0p h0q,
    cases h1 with h1p h1q,
    replace hp := holds_cnf h0p h1p,
    replace hq := holds_cnf h0q h1q,
    simp only [mat.holds, cnf],
    rw list.forall_mem_append,
    refine ⟨hp, hq⟩,
  end
| (f ∨* g) h0 h1 :=
  begin
    cases h0 with h0f h0g,
    cases h1; unfold cnf,
    { apply holds_map_app_prod_left,
      apply holds_cnf h0f h1 },
    apply holds_map_app_prod_right,
    apply holds_cnf h0g h1,
  end

lemma not_holds_empty_cla :
  ¬ (cla.holds R F V []) :=
by rintro ⟨_, ⟨_⟩, _⟩

lemma holds_tautology :
  cla.tautology.holds R F V :=
begin
  simp only [cla.tautology, cla.holds],
  cases classical.em (lit.holds R F V (+* ($ 0))) with h0 h0,
  refine ⟨_, or.inr (or.inl rfl), h0⟩,
  refine ⟨_, or.inl rfl, h0⟩,
end

#exit


namespace cla

meta def to_expr : cla → expr
| []       := `(@list.nil lit)
| (l :: c) := expr.mk_app `(@list.cons lit) [l.to_expr, to_expr c]

def subst (π : mappings) : cla → cla :=
list.map (lit.subst π)

def holds (M : model α) (v : vas α) (c : cla) : Prop :=
∃ l ∈ c, lit.holds M v l

def fav (M : model α) (c : cla) : Prop :=
∀ v : vas α, holds M v c

def satisfies (M : model α) (c : cla) : Prop :=
∀ v : vas α, holds M v c

lemma holds_subst (M : model α) (v : vas α) (μ : mappings) (c : cla) :
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


def fav (M : model α) (m : mat) : Prop :=
∀ v : vas α, m.holds M v



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

  #exit

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
