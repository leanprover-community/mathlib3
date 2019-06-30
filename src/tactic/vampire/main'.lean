/-
  Copyright (c) 2019 Seul Baek. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Seul Baek

 `vampire` uses proof output from Vampire discharge first-order goals.
-/

import system.io
import tactic.vampire.arifix
import tactic.vampire.reify
import tactic.vampire.compile'

universe u

variable {α : Type}

open tactic list

namespace vampire

local notation `#`     := term₂.var
local notation a `&` b := term₂.app a b

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

meta def vampire_output (gs : string) : tactic string :=
unsafe_run_io $ io.cmd'
{ cmd  := "vampire.sh",
  args := [gs, temp_goal_file_path] }

lemma arifix_of_proof (α : Type) [inhabited α] (p : form₂) :
  foq tt p → proof (clausify p) [] → arifix (model.default α) p :=
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

meta inductive item : Type
| nm  (n : nat)            : item
| trm (t : term)           : item
| mps (m : mappings)       : item
| prf (x : expr) (c : cla) : item

meta def build_proof_core (m : mat) (mx : expr) :
  list item → infs → tactic expr
| (item.prf x _ :: stk) [] := return x
| stk (inf.n k :: infs) :=
  build_proof_core (item.nm k :: stk) infs
| (item.nm k :: stk) (inf.h :: infs) :=
  build_proof_core
    (item.prf (expr.mk_app `(@proof.hyp) [mx, k.to_expr]) (m.nth k) :: stk)
    infs
| ((item.prf σx ((tt, s) :: d)) :: (item.prf πx ((ff, t) :: c)) :: stk) (inf.r :: infs) :=
  build_proof_core
    ( ( item.prf
        ( expr.mk_app `(@proof.res) [mx, t.to_expr, cla.to_expr c, cla.to_expr d, πx, σx] )
        (c ++ d) ) :: stk )
    infs
| (item.nm k :: (item.prf πx c) :: stk) (inf.t :: infs) :=
  build_proof_core
    ( ( item.prf
        ( expr.mk_app `(@proof.rot) [mx, k.to_expr, c.to_expr, πx] )
        ( c.rot k ) ) :: stk ) infs
| (item.mps μ :: item.prf πx c :: stk) (inf.s :: infs) :=
  build_proof_core
    ( ( item.prf
          (expr.mk_app `(@proof.sub) [mx, μ.to_expr, c.to_expr, πx])
          (c.subst μ) ) :: stk) infs
| ((item.prf πx (l :: _ :: c)) :: stk) (inf.c :: infs) :=
  build_proof_core
    ( ( item.prf
          (expr.mk_app `(@proof.con) [mx, l.to_expr, cla.to_expr c, πx])
          (l :: c) ) :: stk ) infs
| stk (inf.e :: is) :=
  build_proof_core (item.mps [] :: stk) is
| (item.nm k :: stk) (inf.y :: infs) :=
  build_proof_core (item.trm (term.sym k) :: stk) infs
| (item.trm s :: item.trm t :: stk) (inf.a :: infs) :=
  build_proof_core (item.trm (term.app t s) :: stk) infs
| (item.nm k :: item.trm t :: stk) (inf.v :: infs) :=
  build_proof_core (item.trm (term.vpp t k) :: stk) infs
| (item.nm m :: item.nm k :: item.mps μ :: stk) (inf.m :: infs) :=
  build_proof_core (item.mps ((k, sum.inl m) :: μ) :: stk) infs
| (item.trm t :: item.nm k :: item.mps μ :: stk) (inf.m :: infs) :=
  build_proof_core (item.mps ((k, sum.inr t) :: μ) :: stk) infs
| _ _ := fail "invalid inference"

/- Return ⌜π : arifix (model.default ⟦αx⟧) p⌝ -/
meta def build_proof (is : infs)
  (αx ix : expr) (p : form₂) (m : mat)
  : tactic expr :=
do πx ← build_proof_core m m.to_expr [] is,
   let px   : expr := form₂.to_expr p,
   let foqx : expr := expr.mk_app `(foq) [`(tt), px],
   let decx : expr := expr.mk_app `(foq.decidable) [`(tt), px],
   let fx   : expr := expr.mk_app `(@of_as_true) [foqx, decx, `(trivial)],
   let x    : expr := expr.mk_app `(@arifix_of_proof) [αx, ix, px, fx],
   return (expr.app x πx)

meta def script_output (s : string) : tactic string :=
unsafe_run_io $ io.cmd'
{ cmd := "rr.pl",
  args := [s] }

meta def get_infs_string' (m : mat) : tactic string :=
script_output m.to_rr --("\"" ++ m.to_rr ++ "\"")

meta def get_infs_string (m : mat) : tactic string :=
do s ← vampire_output (mat.to_tptp m),
   ss ← proof_line_strings s,
   ls ← monad.mapm proof_line ss,
   is ← compile m ls,
   trace is,
   return (infs.repr is)

meta def get_infs (s : string) : tactic infs :=
match parser.run_string parse_infs s with
| (sum.inl str) := fail str
| (sum.inr ss)  := return ss
end

meta def vampire : tactic unit :=
do (dx, ix, p) ← reify,
   let m := clausify p,
   get_infs_string m,
   iss' ← get_infs_string' m,
   trace iss',
   -- is ← get_infs iss,
   -- trace (infs.repr is),
   -- x ← build_proof is dx ix p m,
   -- apply x,
   skip

example (A B C : Prop) : ¬ A → A → C := by vampire

example (β : Type) [inhabited β] (p : β → Prop) (a : β) :
  (p a) → ∃ x, p x := by vampire

end vampire
