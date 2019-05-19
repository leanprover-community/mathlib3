/-
  Copyright (c) 2019 Seul Baek. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Seul Baek

  Compilation of parsed SPASS proof output into detailed proof recipes.
-/

import tactic.spass.parse

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

meta def terms.instantiator : list term → list term → tactic smaps
| [] [] := return []
| (t :: ts) (s :: ss) :=
  do μ ← term.instantiator t s,
     ν ← terms.instantiator ts ss,
     instantiator.merge μ ν
| _ _ := failed

meta def cla.instantiator : cla → cla → tactic smaps
| (nc, pc) (nd, pd) :=
  do μ ← terms.instantiator nc nd,
     ν ← terms.instantiator pc pd,
     instantiator.merge μ ν

meta def find_line (k : nat) : list line → tactic line
| []                := failed
| (⟨m, r, c⟩ :: ls) :=
  if k = m
  then return ⟨m, r, c⟩
  else find_line ls

def ref_update (npad ppad nlen idx r : nat) : nat :=
let r' := if idx < r then r - 1 else r in
let padding := npad + (if r < nlen then 0 else ppad) in
r' + padding

meta def compare_return (s : string) (c d : cla) (ρx : expr) : tactic expr :=
if c = d
then return ρx
else do trace (s ++ "Derived clause not equal to target."),
        trace "Derived clause : ", trace c,
        trace "Target clause : ", trace d,
        failed

meta def term.find_dup (t : term) : nat → list term → tactic (nat × smaps)
| _ [] := failed
| k (s :: ts) :=
  ( do _ ← term.instantiator t s,
       μ ← term.instantiator s t,
       return (k, μ) ) <|> ( term.find_dup (k + 1) ts )

meta def side.find_dup : nat → list term → tactic (nat × smaps)
| k []        := failed
| k (t :: ts) :=
  ( do (m, μ) ← t.find_dup 1 ts, return (k + m, μ) ) <|>
  ( side.find_dup (k + 1) ts )

meta def cla.find_dup : cla → tactic (bool × nat × smaps)
| (nc, pc) :=
  (do (k, μ) ← side.find_dup 0 nc, return (ff, k, μ)) <|>
  (do (k, μ) ← side.find_dup 0 pc, return (tt, k, μ))

meta def extract_ems_refs_core (k : nat) :
  list (nat × nat) → (list nat × list (nat × nat))
| []            := ([], [])
| ((m, n) :: l) :=
  if k = m
  then let (ns, nns) := extract_ems_refs_core l in
       (n :: ns, nns)
  else ([], ((m, n) :: l))

meta def extract_ems_refs : list (nat × nat) → tactic (nat × list nat × list (nat × nat))
| [] := trace "Invalid ems refs" >> failed
| ((k, m) :: l) :=
  let (ns, nns) := extract_ems_refs_core k l in
  return (k, (m :: ns), nns)

meta mutual def compile_core, compile_ems,
  compile_sub, compile_psub, compile_res,
  compile_con, compile_obv, compile_obvs

with compile_core : mat → list line → nat → rule → cla → tactic expr
| A ls k rule.inp c :=
  ( do d ← A.nth (k - 1),
           compile_psub `(recipe.hyp $ %%`(k) - 1) d d.permutations c )
  <|> (trace "Inp fail" >> failed)
| A ls k (rule.res ln1 rf1 ln2 rf2) c :=
  ( do ⟨m, r, d⟩ ← find_line ln1 ls,
     ⟨n, s, e⟩ ← find_line ln2 ls,
     ρ ← compile_core A ls m r d,
     σ ← compile_core A ls n s e,
     (τ, f) ← compile_res ρ d (rf1 - d.fst.length) σ e rf2,
     compile_psub τ f f.permutations c )
  <|> (trace "Res fail" >> failed)
| A ls k (rule.unc ln1 rf1 ln2 rf2) c :=
  ( do ⟨m, r, d⟩ ← find_line ln1 ls,
     ⟨n, s, e⟩ ← find_line ln2 ls,
     ρ ← compile_core A ls m r d,
     σ ← compile_core A ls n s e,
     (τ, f) ← ( if rf1 < d.fst.length
                then compile_res σ e rf2 ρ d rf1
                else compile_res ρ d rf1 σ e rf2 ),
    compare_return "[UnC]" f ([], []) τ )
  <|> (trace "Unc fail" >> failed)
| A ls k (rule.obv ln rf) c :=
  ( do ⟨m, r, d⟩ ← find_line ln ls,
       ρ ← compile_core A ls m r d,
       let (b, rf') := if rf < d.fst.length
                       then (ff, rf)
                       else (tt, rf - d.fst.length),
       (σ, e) ← compile_obv ρ d b rf',
       compare_return "[Obv]" e c σ )
  <|> (trace "Obv fail" >> failed)
| A ls k (rule.fac ln rf1 rf2) c :=
  ( do ⟨m, r, d⟩ ← find_line ln ls,
     ρ ← compile_core A ls m r d,
     let (b1, i) := d.get_ref rf1,
     let (b2, j) := d.get_ref rf2,
     t ← d.nth b1 i,
     s ← d.nth b2 j,
     μ ← unifier t s,
     (σ, e) ← compile_obv `(recipe.sub %%`(μ) %%ρ) (d.subst μ) b1 i,
     compare_return "[Fac]" e c σ )
  <|> (trace "Fac fail" >> failed)
| A ls k (rule.con ln rf) c :=
  ( do ⟨m, r, (nd, pd)⟩ ← find_line ln ls,
     ρ ← compile_core A ls m r (nd, pd),
     if rf < nd.length
     then let nd' := nd.remove_nth rf in
          do t ← nd.nth rf,
             compile_con ρ (nd', pd) c rf ff nd' t
     else let rf' := rf - nd.length in
          let pd' := pd.remove_nth rf' in
          do t ← pd.nth rf',
             compile_con ρ (nd, pd') c rf' tt pd' t )
  <|> (trace "Con fail" >> failed)
| A ls k (rule.ems l) c :=
( do (m, ms, mms) ← extract_ems_refs l,
     ⟨n, s, d⟩ ← find_line m ls,
     ρ ← compile_core A ls n s d,
     (σ, e) ← compile_ems A ls ρ d ms [] mms,
     compile_obvs σ e c )
  <|> (trace ("EmS fail, line " ++ k.repr) >> failed)

with compile_ems : mat → list line → expr → cla →
  list nat → list (nat × nat) → list (nat × nat) → tactic (expr × cla)
| _ _ ρ c [] _ _ := return (ρ, c)
| _ _ ρ c _ _ [] := return (ρ, c)
| A ls ρ (nc, pc) (k :: ks) l ((m, n) :: mns) :=
( do ⟨i, s, (nd, pd)⟩ ← find_line m ls,
     σ ← compile_core A ls i s (nd, pd),
  if nc.length ≤ k
  then do (τ, e) ← compile_res ρ (nc, pc) (k - nc.length) σ (nd, pd) n,
          compile_ems A ls τ e (ks.map (ref_update 0 0 nc.length k)) [] (l ++ mns)
  else do (τ, e) ← compile_res σ (nd, pd) (n - nd.length) ρ (nc, pc) k,
          compile_ems A ls τ e (ks.map (ref_update nd.length (pd.length - 1) nc.length k)) [] (l ++ mns) )
<|> (compile_ems A ls ρ (nc, pc) (k :: ks) (l ++ [(m, n)]) mns)

with compile_sub : expr → cla → cla → tactic expr
| ρ c d :=
( do μ ← cla.instantiator c d,
     compare_return "[Instantiation]" (c.subst μ) d `(recipe.sub %%`(μ) %%ρ) )

with compile_psub : expr → cla → list cla → cla → tactic expr
| ρ c [] e := trace "No more permutations" >> failed
| ρ c (d :: ds) e :=
  (compile_sub `(recipe.prm %%`(d) %%ρ) d e) <|>
  (compile_psub ρ c ds e) <|>
  (trace "Fail C-psub-2" >> failed)

with compile_res : expr → cla → nat →
  expr → cla → nat → tactic (expr × cla)
| ρx (nc, pc) k σx (nd, pd) m :=
( do t ← pc.nth k | fail "Cannot retrieve positive term",
     s ← nd.nth m | fail "Cannot retrieve negative term",
     (μ, ν) ← unifiers (disjoiner (nc, pc) (nd, pd)) t s,
     let (nc', pc') := cla.subst μ (nc, pc.remove_nth k),
     let (nd', pd') := cla.subst ν (nd.remove_nth m, pd),
     return (`(recipe.res %%`(k) %%`(m) (recipe.sub %%`(μ) %%ρx) (recipe.sub %%`(ν) %%σx)),
       (nc' ++ nd', pc' ++ pd')) )
    <|> (do trace "Fail C-res.",
            trace ("Pos cla : " ++ cla.repr (nc, pc)),
            trace ("Pos idx : " ++ k.repr),
            trace ("Neg cla : " ++ cla.repr (nd, pd)),
            trace ("Neg idx : " ++ m.repr),
            failed)

with compile_con : expr → cla → cla → nat →
  bool → list term → term → tactic expr
| ρ d c rf b [] t        :=
  (trace "Fain C-con-1" >> failed)
| ρ d c rf b (s :: ts) t :=
  (do μ ← unifier s t,
      compile_sub `(recipe.con %%`(b) %%`(rf) $
      recipe.sub %%`(μ) %%ρ) (d.subst μ) c) <|>
  (compile_con ρ d c rf b ts t)
  <|> (trace "Fain C-con-2" >> failed)

with compile_obv : expr → cla → bool → nat → tactic (expr × cla)
| ρ (nc, pc) ff rf :=
  let nc' := nc.remove_nth rf in
( do t ← nc.nth rf,
     guard (t ∈ nc'),
     return (`(recipe.con ff %%`(rf) %%ρ), (nc', pc)) )
<|> (trace "fail C-obv-1" >> failed)
| ρ (nc, pc) tt rf :=
  let pc' := pc.remove_nth rf in
( do t ← pc.nth rf,
     guard (t ∈ pc'),
     return (`(recipe.con tt %%`(rf) %%ρ), (nc, pc')) )
<|> (trace "fail C-obv-2" >> failed)

with compile_obvs : expr → cla → cla → tactic expr
| ρ c d :=
( do
  if c.length = d.length
  then compile_psub ρ c c.permutations d
  else do (b, k, μ) ← c.find_dup,
          (σ, e) ← compile_obv `(recipe.sub %%`(μ) %%ρ) (c.subst μ) b k,
          compile_obvs σ e d ) <|> (trace "Fail compile_obvs" >> failed)

meta def compile (m : mat) (ls : list line) : tactic expr :=
do ⟨k, r, ([], [])⟩ ← list.find (λ l, line.c l = ([], [])) ls,
   compile_core m ls k r ([], [])
