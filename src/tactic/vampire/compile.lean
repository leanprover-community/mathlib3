/-
  Copyright (c) 2019 Seul Baek. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Seul Baek

  Compilation of parsed Vampire proof output
  into inductively defined resolution proofs.
-/

import tactic.vampire.proof
import tactic.vampire.parse

open tactic

namespace vampire

open tactic

def disjoiner (c d : cla) : smaps :=
d.vars.map (λ k, (k, sum.inl $ k + c.fresh_var))

meta def unifier : term → term → tactic smaps
| (term.sym k) (term.sym m) :=
  guard (k = m) >> return []
| (term.app t1 t2) (term.app s1 s2) :=
  do μ ← unifier t2 s2,
     ν ← unifier (t1.subst μ) (s1.subst μ),
     return (smaps.compose ν μ)
| (term.app t1 t2) (term.vpp s k) :=
  do guard (¬ k ∈ t2.vars),
     μ ← unifier (t1.subst [(k, sum.inr t2)]) (s.subst [(k, sum.inr t2)]),
     return (smaps.compose μ [(k, sum.inr t2)])
| (term.vpp t k) (term.app s1 s2) :=
  do guard (¬ k ∈ s2.vars),
     μ ← unifier (t.subst [(k, sum.inr s2)]) (s1.subst [(k, sum.inr s2)]),
     return (smaps.compose μ [(k, sum.inr s2)])
| (term.vpp t k) (term.vpp s m) :=
  do μ ← unifier (t.subst [(m, sum.inl k)]) (s.subst [(m, sum.inl k)]),
     return (smaps.compose μ [(m, sum.inl k)])
| t s := fail ("Nonunifiable terms : " ++ t.repr ++ " " ++ s.repr)

meta def unifiers (δ : smaps) (t s : term) : tactic (smaps × smaps) :=
do μ ← unifier t (s.subst δ),
   return (μ, smaps.compose μ δ)

meta def instantiator.merge_core : smaps → smaps → smaps → tactic smaps
| [] μ ν             := return (μ ++ ν)
| ((m, t) :: ξ) μ ν  :=
  match ν.find (λ x, prod.fst x = m) with
  | none := instantiator.merge_core ξ ((m, t) :: μ) ν
  | some ns :=
    if t = ns.snd
    then instantiator.merge_core ξ μ ν
    else failed
  end

meta def instantiator.merge : smaps → smaps → tactic smaps
| μ ν := instantiator.merge_core μ [] ν

meta def term.instantiator : term → term → tactic smaps
| (term.sym k) (term.sym m) :=
  guard (k = m) >> return []
| (term.app t1 t2) (term.app s1 s2) :=
  do μ ← term.instantiator t2 s2,
     ν ← term.instantiator t1 s1,
     instantiator.merge μ ν
| (term.vpp t k) (term.app s1 s2) :=
  do μ ← term.instantiator t s1,
     instantiator.merge μ [(k, sum.inr s2)]
| (term.vpp t k) (term.vpp s m) :=
  do μ ← term.instantiator t s,
     instantiator.merge μ [(k, sum.inl m)]
| _ _ := fail "RHS is not an instance of LHS"

meta def cla.instantiator : cla → cla → tactic smaps
| [] [] := return []
| ((a, t) :: c) ((b, s) :: d) :=
  if a = b
  then do μ ← term.instantiator t s,
          ν ← cla.instantiator c d,
          instantiator.merge μ ν
  else failed
| _ _ := failed

meta def find_line (k : nat) : list line → tactic line
| []                := failed
| (⟨m, c, r⟩ :: ls) :=
  if k = m
  then return ⟨m, c, r⟩
  else find_line ls

def is_dup : cla → Prop
| (l1 :: l2 :: c) := l1 = l2
| _ := false

instance is_dup.decidable : decidable_pred is_dup
| []  := is_false (λ h, by cases h)
| [_] := is_false (λ h, by cases h)
| (_ :: _ :: _) := by {unfold is_dup, apply_instance}

meta def tactic.guard (p : Prop) [decidable p] (s : string) : tactic unit :=
if p then skip else trace s >> failed

meta def allign_premises (π1 π2 : expr) :
  cla → cla → tactic (expr × expr × term × term × cla × cla)
| ((ff, t1) :: c1) ((tt, t2) :: c2) := return (π1, π2, t1, t2, c1, c2)
| ((tt, t1) :: c1) ((ff, t2) :: c2) := return (π2, π1, t2, t1, c2, c1)
| _ _ := failed

meta def rots (mx πx : expr) (c : cla) : list (expr × cla) :=
(list.range c.length).map
  (λ x, (expr.mk_app `(@proof.rot) [mx, x.to_expr, c.to_expr, πx], c.rot x))

meta def lit.unifier : lit → lit → tactic smaps
| (a, t) (b, s) :=
  if a = b
  then unifier t s
  else failed

meta def lit.instantiator : lit → lit → tactic smaps
| (a, t) (b, s) :=
  if a = b
  then term.instantiator t s
  else failed

meta def compute_map (d : cla) :
  cla → smaps → list nat → nat → tactic (smaps × list nat)
| [] μ ns _ :=
  if ∀ x < d.length, x ∈ ns
  then return (μ, ns.reverse)
  else failed
| (_ :: _) _ _ 0 := failed
| (a :: c) μ ns (k + 1) :=
  ( do b ← d.nth k,
       ν ← lit.instantiator a b,
       ξ ← instantiator.merge μ ν,
       compute_map c ξ (k :: ns) d.length ) <|>
  ( compute_map (a :: c) μ ns k )

def index_of' {α : Type} [decidable_eq α] (a : α) : list α → option nat
| []        := none
| (b :: as) :=
  if a = b
  then some 0
  else do k ← index_of' as,
          some (k + 1)

def remove_nth' {α : Type} : list α → ℕ → option (list α)
| []      _       := none
| (x :: xs) 0       := xs
| (x :: xs) (k + 1) :=
  do xs' ← remove_nth' xs k,
     some (x :: xs')

meta def compile_cnts_aux (mx : expr) :
  expr → list nat → cla → tactic (expr × list nat × cla)
| πx (k :: ks) (l :: c) :=
  ( do n ← index_of' k ks,
       ks' ← remove_nth' ks n,
       c'  ← remove_nth' c n,
       let πx'  : expr := expr.mk_app `(@proof.rot) [mx, (n + 1).to_expr, cla.to_expr (l :: c), πx],
       let πx'' : expr := expr.mk_app `(@proof.con) [mx, l.to_expr, cla.to_expr c', πx'],
       compile_cnts_aux πx'' (k :: ks') (l :: c') ) <|>
  ( return (πx, k :: ks, l :: c))
| _ _ _ := failed

meta def compile_cnts (mx : expr) (d : cla)  :
  nat → expr → (list nat) → cla → tactic (expr × cla)
| 0 πx _ c :=
  do tactic.guard (list.exteq c d)
     "Contraction result not equivalent to target", -- To do : remove when compiler is reliable
     return (πx, c)
| (k + 1) πx ns c :=
  do i ← index_of' k ns,
     let πx' : expr := expr.mk_app `(@proof.rot) [mx, i.to_expr, c.to_expr, πx],
     (πx'', ns', c') ← compile_cnts_aux mx πx' (ns.rot i) (c.rot i),
     compile_cnts k πx'' ns' c'

meta def compile_map (mx πx : expr) (c d : cla) : tactic (expr × cla) :=
do let δ  := disjoiner d c,
   let cδ := c.subst δ,
   let σx := expr.mk_app `(@proof.sub) [mx, δ.to_expr, c.to_expr, πx],
   (μ, ns) ← compute_map d cδ [] [] d.length,
   let cδμ := cδ.subst μ,
   let τx : expr := expr.mk_app `(@proof.sub) [mx, μ.to_expr, cδ.to_expr, σx],
   compile_cnts mx d d.length τx ns cδμ

meta def compile_res (mx : expr) (c : cla) :
  list ((expr × cla) × (expr × cla)) → tactic (expr × cla)
| [] := failed
| (((π1, c1), (π2, c2)) :: l) :=
  ( do (σ1, σ2, t1, t2, d1, d2) ← allign_premises π1 π2 c1 c2,
       let e1 := ((ff, t1) :: d1),
       let e2 := ((tt, t2) :: d2),
       (μ, ν) ← unifiers (disjoiner e1 e2) t1 t2,
       let σ1' : expr := expr.mk_app `(@proof.sub) [mx, μ.to_expr, cla.to_expr e1, σ1],
       let σ2' : expr := expr.mk_app `(@proof.sub) [mx, ν.to_expr, cla.to_expr e2, σ2],
       let t   : term := t1.subst μ,
       let d1' : cla  := d1.subst μ,
       let d2' : cla  := d2.subst ν,
       let d   : cla  := d1' ++ d2',
       let σ   : expr := expr.mk_app `(@proof.res)
                         [mx, t.to_expr, d1'.to_expr, d2'.to_expr, σ1', σ2'],
       compile_map mx σ d c ) <|>
  ( compile_res l )

meta def compile_core : list line →
  mat → expr → nat → cla → rule → tactic (expr × cla)
| ls m mx k c rule.inp :=
  let d := m.nth (k - 1) in
  compile_map mx (expr.mk_app `(@proof.hyp) [mx, (k - 1).to_expr]) d c
| ls m mx k c (rule.map n) :=
  do ⟨k', c', r⟩ ← find_line n ls,
     (πx, d) ← compile_core ls m mx k' c' r,
     compile_map mx πx d c
| ls m mx k c (rule.res n1 n2) :=
  do ⟨k1, c1, r1⟩ ← find_line n1 ls,
     ⟨k2, c2, r2⟩ ← find_line n2 ls,
     (π1, d1) ← compile_core ls m mx k1 c1 r1,
     (π2, d2) ← compile_core ls m mx k2 c2 r2,
     let ccs := list.product (rots mx π1 d1) (rots mx π2 d2),
     compile_res mx c ccs

meta def compile (m : mat) (ls : list line) : tactic expr :=
do ⟨k, [], r⟩ ← list.find (λ l, line.c l = []) ls,
   (πx, _) ← compile_core ls m m.to_expr k [] r,
   return πx

end vampire
