/-
  Copyright (c) 2019 Seul Baek. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Seul Baek

  CNF formulas.
-/

import data.list.min_max
import tactic.spass.list
import tactic.spass.folize
import tactic.spass.misc

universe u

variable {α : Type u}

open list

local notation `&`     := term.sym
local notation a `&` b := term.app a b
local notation a `#` k := term.vpp a k

local notation `⟪` b `,` a `⟫` := form.lit b a
local notation p `∨₁` q        := form.bin tt p q
local notation p `∧₁` q        := form.bin ff p q

@[reducible] def cla : Type := list term × list term
@[reducible] def mat : Type := list cla

def cla.append : cla → cla → cla
| (nts1, pts1) (nts2, pts2) := (nts1 ++ nts2, pts1 ++ pts2)

def cnf : form → mat
| ⟪ff, t⟫   := [([t],[])]
| ⟪tt, t⟫   := [([],[t])]
| (p ∨₁ q) :=
  (list.product (cnf p) (cnf q)).map
    (λ x, cla.append x.fst x.snd)
| (p ∧₁ q) := (cnf p) ++ (cnf q)

namespace cla

def vars : cla → list nat
| (nc, pc) := ((nc ∪ pc).map term.vars).foldl list.union []

def fresh_var : cla → nat
| (nc, pc) := ((nc ++ pc).map term.fresh_var).maximum

def subst (π : smaps) : cla → cla
| (nts, pts) := (nts.map (term.subst π), pts.map (term.subst π))

def rename (f : nat → nat) : cla → cla
| (nts, pts) := (nts.map (term.rename f), pts.map (term.rename f))

def holds (M : model α) (v : vas α) : cla → Prop
| (nts, pts) :=
  (∃ t ∈ nts, ¬ term.holds M v t) ∨ (∃ t ∈ pts, term.holds M v t)

def fav (M : model α) (c : cla) : Prop :=
∀ v : vas α, holds M v c

def satisfies (M : model α) (c : cla) : Prop :=
∀ v : vas α, holds M v c

lemma holds_rename (M : model α) (v : vas α) (f : nat → nat) (c : cla) :
  holds M v (c.rename f) ↔ holds M (v ∘ f) c :=
begin
  cases c with nc pc,
  simp only [cla.rename, cla.holds],
  apply pred_mono_2; apply iff.symm;
  apply @list.exists_mem_iff_exists_mem_map
    term term _ _ (term.rename f) _ _;
  intro t; rw term.holds_rename
end

lemma holds_subst (M : model α) (v : vas α) (μ : smaps) (c : cla) :
  holds M v (c.subst μ) ↔ holds M (v.subst M μ) c :=
begin
  cases c with nc pc,
  simp only [cla.subst, vas.subst, cla.holds],
  apply pred_mono_2; apply iff.symm;
  apply @list.exists_mem_iff_exists_mem_map
    term term _ _ (term.subst μ) _ _;
  intro t; rw term.holds_subst
end

def repr_aux : list term → string
| []        := "⬝"
| [t]       := t.repr
| (t :: ts) := t.repr ++ "," ++ repr_aux ts

def repr : cla → string
| (nts, pts) :=
  repr_aux nts ++ " ⊢ " ++ repr_aux pts

instance has_repr : has_repr cla := ⟨repr⟩
meta instance has_to_format : has_to_format cla := ⟨λ x, repr x⟩

def get_ref : cla → nat → (bool × nat)
| (nc, pc) k :=
  if k < nc.length
  then (ff, k)
  else (tt, k - nc.length)

def nth : cla → bool → nat → option term
| (nc, pc) ff k := nc.nth k
| (nc, pc) tt k := pc.nth k

def length : cla → nat
| (nc, pc) := nc.length + pc.length

def permutations : cla → list cla
| (nc, pc) := list.product nc.permutations pc.permutations

def exteq : cla → cla → Prop
| (nc, pc) (nd, pd) := list.exteq nc nd ∧ list.exteq pc pd

lemma holds_of_exteq {M : model α} {v : vas α} {c d : cla} :
  c.holds M v → cla.exteq c d → d.holds M v :=
begin
  cases c with nc pc,
  cases d with nd pd,
  rintros (⟨t, h0, h1⟩ | ⟨t, h0, h1⟩) ⟨hc, hd⟩,
  { left, refine ⟨t, _, h1⟩,
    apply list.subset_of_exteq _ _ hc h0 },
  right, refine ⟨t, _, h1⟩,
  apply list.subset_of_exteq _ _ hd h0
end

instance decidable_exteq :
  ∀ c d : cla, decidable (cla.exteq c d)
| (nc, pc) (nd, pd) := and.decidable
end cla

namespace mat

def holds (M : model α) (v : nat → α) (m : mat) : Prop :=
∀ c ∈ m, cla.holds M v c

def fav (M : model α) (m : mat) : Prop :=
∀ v : vas α, m.holds M v

end mat

lemma holds_cnf_of_holds {M : model α} {v : nat → α} :
  ∀ p : form, p.holds M v → (cnf p).holds M v
| ⟪b, a⟫ h0 :=
  begin
    intros c h1, cases b;
    rw eq_of_mem_singleton h1;
    [left, right];
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
    cases c1 with nc1 pc1,
    cases c2 with nc2 pc2,
    simp only [cla.holds, cla.append, exists_mem_append],
    cases h0,
    { cases holds_cnf_of_holds _ h0 _ hc1 with h1 h1,
      { left, left, assumption },
      right, left, assumption },
    cases holds_cnf_of_holds _ h0 _ hc2 with h1 h1,
    { left, right, assumption },
    right, right, assumption
  end

def term.print_core : term → list char
| (& k) := ('s' :: k.repr.data).reverse
| (t & s) :=
  match term.print_core t with
  | [] := []
  | (')' :: cs) :=
    ')' :: (term.print_core s ++ (',' :: cs))
  | (c :: cs) :=
    ')' :: (term.print_core s ++ ('(' :: c :: cs))
  end
| (t # k) :=
  match term.print_core t with
  | [] := []
  | (')' :: cs) :=
    ')' :: (('X' :: k.repr.data).reverse ++ (',' :: cs))
  | (c :: cs) :=
    ')' :: (('X' :: k.repr.data).reverse ++ ('(' :: c :: cs))
  end

def term.print (t : term) : string :=
⟨(term.print_core t).reverse⟩

def cla.print : nat → cla → string
| k (nts, pts) :=
  "cnf(c" ++ k.repr ++ ", negated_conjecture, (" ++
   ( match nts.map (λ x, "~ " ++ term.print x)  ++ pts.map term.print with
     | []        := ""
     | (s :: ss) := ss.foldl (λ x y , x ++ " | " ++ y ) s
     end )
   ++ "))."

def mat.print_core : nat → mat → string
| _ []       := ""
| k (c :: m) := cla.print k c ++ " " ++ mat.print_core (k + 1) m

def mat.print (m : mat) : string := mat.print_core 1 m

def mat.repr_core : nat → mat → string
| _ [] := ""
| k (c :: m) := k.repr ++ ". " ++ c.repr ++ "\n" ++ mat.repr_core (k + 1) m

def mat.repr := mat.repr_core 1

instance mat.has_repr : has_repr mat := ⟨mat.repr⟩

def term.renumbering : term → smaps → smaps
| (term.sym _) := id
| (term.app t s) := s.renumbering ∘ t.renumbering
| (term.vpp t k) :=
  λ μ,
  let μ' := t.renumbering μ in
  if ∃ x ∈ μ', prod.fst x = k
  then μ'
  else (k, sum.inl μ'.length) :: μ'

def cla.renumbering : cla → smaps
| (nc, pc) := list.foldl (λ x y, term.renumbering y x) [] (nc ++ pc)

def cla.renumber (c : cla) : cla :=
c.subst c.renumbering

def mat.renumber (m : mat) : mat :=
m.map cla.renumber

lemma fav_renumber_of_fav
  (M : model α) (m : mat) :
  m.fav M → m.renumber.fav M :=
begin
  intros h0 v c h1,
  unfold mat.renumber at h1,
  rw mem_map at h1,
  rcases h1 with ⟨d, h2, h3⟩, subst h3,
  unfold cla.renumber,
  rw cla.holds_subst,
  apply h0 _ _ h2
end
