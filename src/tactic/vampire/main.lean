/-
  Copyright (c) 2019 Seul Baek. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Seul Baek

 `vampire` uses proof output from Vampire discharge first-order goals.
-/

import system.io
import tactic.vampire.arifix
import tactic.vampire.reify
import tactic.vampire.compile

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

/- Change to the location of vampire binary file -/
def vampire_path : string := "/home/user_name/projects/mathlib/src/tactic/vampire/vampire"

/- Change to the location of vampire.sh -/
def vampire_script_path : string := "./src/tactic/vampire"

/- Change to desired location of temporary goal file -/
def temp_goal_file_path : string := "/var/tmp/temp_goal_file"

meta def vampire_output (gs : string) : tactic string :=
unsafe_run_io $ io.cmd'
{ cmd  := "./vampire.sh",
  args := [gs, vampire_path, temp_goal_file_path],
  cwd  := vampire_script_path }

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

@[derive decidable_eq]
inductive config : Type
| default
| offline
| verbose

/- Return ⌜π : arifix (model.default ⟦αx⟧) p⌝ -/
meta def build_proof (ls : list line)
  (αx ix : expr) (p : form₂) (m : mat) : tactic expr :=
do πx ← compile m ls,
   let px   : expr := form₂.to_expr p,
   let foqx : expr := expr.mk_app `(foq) [`(tt), px],
   let decx : expr := expr.mk_app `(foq.decidable) [`(tt), px],
   let fx   : expr := expr.mk_app `(@of_as_true) [foqx, decx, `(trivial)],
   let x    : expr := expr.mk_app `(@arifix_of_proof) [αx, ix, px, fx],
   return (expr.app x πx)

meta def vampire (cfg : config) (inp : string) : tactic unit :=
do (dx, ix, p) ← reify,
   let m := clausify p,
   s ← if cfg = config.offline
       then return inp
       else vampire_output (mat.to_tptp m),
   ss ← proof_line_strings s,
   if cfg = config.verbose
   then trace (string.join $ ss.map (λ x, x ++ "\n"))
   else skip,
   ls ← monad.mapm proof_line ss,
   x ← build_proof ls dx ix p m,
   apply x, skip

end vampire

open lean.parser interactive vampire

meta def tactic.interactive.vampire
  (opt : parse (many ident))
  (inp : string := "") : tactic unit :=
let cfg := if `offline ∈ opt
           then config.offline
           else if `verbose ∈ opt
                then config.verbose
                else config.default in
vampire cfg inp
