/-
  Copyright (c) 2019 Seul Baek. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Seul Baek

 `vampire` uses proof output from Vampire discharge first-order goals.
-/

import system.io
import data.num.basic
import tactic.vampire.arifix
import tactic.vampire.reify
import tactic.vampire.proof

universe u

variables {α : Type} [inhabited α]

open tactic list

namespace vampire

local notation `#`     := term₂.var
local notation a `&` b := term₂.app a b

local notation `+₂`     := form₂.lit tt
local notation `-₂`     := form₂.lit ff
local notation p `∨₂` q := form₂.bin tt p q
local notation p `∧₂` q := form₂.bin ff p q
local notation `∃₂`     := form₂.qua tt
local notation `∀₂`     := form₂.qua ff

def clausify (p : form₂) : mat :=
cnf $ form.neg $ form₂.folize 0 $ prenexify $ swap_all ff p

/- Same as is.fs.read_to_end and io.cmd,
   except for configurable read length. -/
def io.fs.read_to_end' (h : io.handle) : io char_buffer :=
io.iterate mk_buffer $ λ r,
  do done ← io.fs.is_eof h,
    if done
    then return none
    else do
      c ← io.fs.read h 65536,
      return $ some (r ++ c)

def io.cmd' (args : io.process.spawn_args) : io string :=
do child ← io.proc.spawn { stdout := io.process.stdio.piped, ..args },
  buf ← io.fs.read_to_end' child.stdout,
  io.fs.close child.stdout,
  exitv ← io.proc.wait child,
  when (exitv ≠ 0) $ io.fail $ "process exited with status " ++ repr exitv,
  return buf.to_string

/- Change to desired location of temporary goal file -/
def temp_goal_file_path : string := "/var/tmp/temp_goal_file"

def normalize (p : form₂) : form₂ :=
prenexify $ swap_all ff p

def conditionalize : form₂ → list form₂ → form₂
| p []        := p
| p (q :: qs) := (conditionalize p qs) ∨₂ q.neg

lemma of_holds_conditionalize (M : model α) (p : form₂) :
  ∀ qs : list form₂, (conditionalize p qs).holds M →
  (p.holds M ∨ (∃ q ∈ qs, ¬ form₂.holds M q))
| []        h0 := or.inl h0
| (q :: qs) h0 :=
  begin
    cases h0,
    { rcases of_holds_conditionalize qs h0 with h1 | ⟨r, hr0, hr1⟩,
      { exact or.inl h1 },
      apply or.inr,
      refine ⟨r, or.inr hr0, hr1⟩ },
    apply or.inr,
    refine ⟨q, or.inl rfl, _⟩,
    rw ← holds_neg, exact h0
  end

lemma holds_of_holds_conditionalize
  (M : model α) (p : form₂) (qs : list form₂) :
  (∀ q ∈ qs, form₂.holds M q) →
  (conditionalize p qs).holds M →
  p.holds M :=
begin
  intros h0 h1,
  rcases of_holds_conditionalize M p qs h1 with h2 | ⟨q, hq0, hq1⟩ ,
  { exact h2 },
  exact false.elim (hq1 $ h0 _ hq0)
end

-- lemma arifix_of_holds_normalize
--   (α : Type) [inhabited α] (M : model α) (p : form₂) :
--   foq tt p → (normalize p).holds M → arifix M p :=
-- begin
--   intros h0 h1,
--   apply arifix_of_holds h0,
--   rw [ ← @swap_all_eqv α _ ff _ h0 M,
--        ← @prenexify_eqv α _ _ M ],
--   exact h1
-- end

lemma arifix_of_proof (α : Type) [inhabited α] (M : model α) (p : form₂) :
  foq tt p → proof (clausify p) [] → arifix M p :=
begin
  intros h0 hρ,
  apply arifix_of_holds h0,
  apply (@id (fam α p) _),
  apply (forall_congr (@swap_all_eqv α _ ff _ h0)).elim_left,
  apply (forall_congr (@prenexify_eqv α _ _)).elim_left,
  have h1 : foq tt (prenexify (swap_all ff p)),
  { apply foq_prenexify,
    apply foq_swap_all _ h0 },
  have h2 : form₂.QDF ff (prenexify (swap_all ff p)),
  { apply QDF_prenexify,
    apply QN_swap_all },
  apply fam_of_tas_folize _ h1 h2,
  apply @tas_of_proof α _ _ hρ
end

-- lemma arifix_of_proof (α : Type) [inhabited α] (p : form₂) :
--   foq tt p → proof (clausify p) [] → arifix (model.default α) p :=
-- begin
--   intros h0 hρ,
--   apply arifix_of_holds h0,
--   apply (@id (fam α p) _),
--   apply (forall_congr (@swap_all_eqv α _ ff _ h0)).elim_left,
--   apply (forall_congr (@prenexify_eqv α _ _)).elim_left,
--   have h1 : foq tt (prenexify (swap_all ff p)),
--   { apply foq_prenexify,
--     apply foq_swap_all _ h0 },
--   have h2 : form₂.QDF ff (prenexify (swap_all ff p)),
--   { apply QDF_prenexify,
--     apply QN_swap_all },
--   apply fam_of_tas_folize _ h1 h2,
--   apply @tas_of_proof α _ _ hρ
-- end

meta inductive item : Type
| nm  (n : nat)            : item
| trm (t : term)           : item
| mps (m : mappings)       : item
| prf (x : expr) (c : cla) : item

meta def build_proof_core (m : mat) (mx : expr) :
  list item → list char → tactic expr
| (item.prf x _ :: stk) [] := return x
| stk (' ' :: chs) :=
  build_proof_core stk chs
| stk ('\n' :: chs) :=
  build_proof_core stk chs
| stk ('n' :: chs) :=
  build_proof_core (item.nm 0 :: stk) chs
| (item.nm k :: stk) ('0' :: chs) :=
  build_proof_core (item.nm (k * 2) :: stk) chs
| (item.nm k :: stk) ('1' :: chs) :=
  build_proof_core (item.nm ((k * 2) + 1) :: stk) chs
| (item.mps μ :: item.nm k :: stk) ('a' :: infs) :=
  let πx0 := expr.mk_app `(@proof.hyp) [mx, k.to_expr] in
  let c0  := m.nth k in
  let πx1 := expr.mk_app `(@proof.sub) [mx, μ.to_expr, c0.to_expr, πx0] in
  let c1  := c0.subst μ in
  build_proof_core (item.prf πx1 c1 :: stk) infs
| ((item.prf σx ((tt, s) :: d)) :: (item.prf πx ((ff, t) :: c)) :: stk) ('r' :: infs) :=
  let πx := expr.mk_app `(@proof.res) [mx, t.to_expr, cla.to_expr c, cla.to_expr d, πx, σx] in
  build_proof_core (item.prf πx (c ++ d) :: stk) infs
| ((item.prf πx c) :: item.nm k :: stk) ('t' :: chs) :=
  let πx := expr.mk_app `(@proof.rot) [mx, k.to_expr, c.to_expr, πx] in
  build_proof_core (item.prf πx (c.rot k) :: stk) chs
| ((item.prf πx (l :: _ :: c)) :: stk) ('c' :: chs) :=
  let πx := expr.mk_app `(@proof.con) [mx, l.to_expr, cla.to_expr c, πx] in
  build_proof_core (item.prf πx (l :: c) :: stk) chs
| stk ('e' :: chs) :=
  build_proof_core (item.mps [] :: stk) chs
| (item.nm k :: stk) ('s' :: chs) :=
  build_proof_core (item.trm (term.sym k) :: stk) chs
| (item.trm s :: item.trm t :: stk) ('p' :: chs) :=
  build_proof_core (item.trm (term.app t s) :: stk) chs
| (item.trm t :: item.nm k :: item.mps μ :: stk) ('m' :: infs) :=
  build_proof_core (item.mps ((k, sum.inr t) :: μ) :: stk) infs
| _ _ := fail "invalid inference"

/- Return ⌜π : arifix (model.default ⟦αx⟧) p⌝ -/
meta def build_proof (chs : list char)
  (αx ix : expr) (p : form₂) (m : mat)
  : tactic expr :=
do πx ← build_proof_core m m.to_expr [] chs,
   Mx ← to_expr ``(model.default %%αx),
   let px   : expr := form₂.to_expr p,
   let foqx : expr := expr.mk_app `(foq) [`(tt), px],
   let decx : expr := expr.mk_app `(foq.decidable) [`(tt), px],
   let fx   : expr := expr.mk_app `(@of_as_true) [foqx, decx, `(trivial)],
   let x    : expr := expr.mk_app `(@arifix_of_proof) [αx, ix, Mx, px, fx],
   return (expr.app x πx)

def term.to_rr : term → string
| (term.sym k)   := k.repr ++  " fn"
| (term.app t s) := string.join [t.to_rr, " ", s.to_rr, " tp"]
| (term.vpp t k) := string.join [t.to_rr, " ", k.repr, " vp"]

def lit.to_rr : lit → string
| (tt, t) := t.to_rr ++ " ps"
| (ff, t) := t.to_rr ++ " ng"

def cla.to_rr : cla → string
| []       := "nl"
| (l :: c) := cla.to_rr c ++ " " ++ l.to_rr ++ " cs"

def mat.to_rr : mat → string
| []       := "nl"
| (c :: m) := mat.to_rr m ++ " " ++ c.to_rr ++ " cs"

meta def get_rr (m : mat) : tactic string :=
unsafe_run_io $ io.cmd'
{ cmd := "main.pl",
  args := [m.to_rr] }

meta def vampire (inp : option string) : tactic unit :=
do (dx, ix, p) ← reify,
   let m := clausify p,
   s ← (inp <|> get_rr m),
   x ← build_proof s.data dx ix p m,
   apply x,
   if inp = none
   then trace s
   else skip

--axiom quodlibet (p : Prop) : p
--
--def refl_ax : form₂ :=
--  ∀₂ (+₂ ((# 1 & # 0) & #0))
--
--def symm_ax : form₂ :=
--  ∀₂ (∀₂ (-₂ ((# 2 & # 0) & #1) ∨₂ +₂ ((# 2 & # 1) & #0)))
--
--meta def vampire_eq : tactic unit :=
--do (αx, ihx, p) ← reify_eq,
--   let px   : expr := form₂.to_expr p,
--   x ← to_expr ``(quodlibet (@arifix %%αx %%ihx (@model.eq %%αx %%ihx) %%px)),
--   apply x,
--   skip

end vampire

open lean.parser interactive vampire tactic

meta def tactic.interactive.vampire
  (ids : parse (many ident))
  (inp : option string := none) : tactic unit :=
( if `all ∈ ids
  then local_context >>= monad.filter is_proof >>=
       revert_lst >> skip
  else do hs ← mmap tactic.get_local ids,
               revert_lst hs, skip ) >>
vampire.vampire inp
