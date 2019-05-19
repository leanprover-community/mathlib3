/-
  Copyright (c) 2019 Seul Baek. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Seul Baek

 `spass` uses proof output from SPASS to discharge first-order goals.
-/

import system.io
import tactic.spass.arifix
import tactic.spass.reify
import tactic.spass.compile

open tactic list

local notation `#`     := term₂.var
local notation a `&` b := term₂.app a b

def clausify (p : form₂) : mat :=
mat.renumber $ cnf $ form.neg $ form₂.folize 0 $ prenexify $ swap_all ff p

lemma arifix_of_run_eq_some_empty (α : Type) [inhabited α]
  (p : form₂) (ρ : recipe) :
  foq tt p → ρ.run (clausify p) = some ([], []) →
  arifix (model.default α) p :=
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
  apply @tas_of_run_empty α _ _ _ hρ
end

/- Same as regular read_to_end and cmd,
   except for configurable read length. -/

def io.fs.read_to_end_cfg (h : io.handle) (k : nat) : io char_buffer :=
io.iterate mk_buffer $ λ r,
  do done ← io.fs.is_eof h,
    if done
    then return none
    else do
      c ← io.fs.read h k,
      return $ some (r ++ c)

def io.cmd_cfg (args : io.process.spawn_args) (k : nat) : io string :=
do child ← io.proc.spawn { stdout := io.process.stdio.piped, ..args },
  buf ← io.fs.read_to_end_cfg child.stdout k,
  io.fs.close child.stdout,
  exitv ← io.proc.wait child,
  when (exitv ≠ 0) $ io.fail $ "process exited with status " ++ repr exitv,
  return buf.to_string

meta def spass_output (gs : string) : tactic string :=
unsafe_run_io $ io.cmd_cfg {
  cmd  := "./spass.sh",
  /- Change this path to the desired location of temporary goal file -/
  args := [gs, "/path/to/temp_goal_file"],
  /- Change this path to the location of spass.sh -/
  cwd  := "/path/to/spass.sh"
} 65536

/- Return ⌜π : arifix (model.default ⟦αx⟧) p⌝ -/
meta def prove_arifix (αx ix : expr) (p : form₂) : tactic expr :=
do s ← spass_output (mat.print $ clausify p),
   ls ← parse.lines s,
   ρx ← compile (clausify p) ls,
   to_expr ``(@arifix_of_run_eq_some_empty %%αx %%ix %%p.to_expr %%ρx
     dec_trivial (@eq.refl (option cla) (some ([], []))))

meta def spass : tactic unit :=
do (dx, ix, p) ← reify,
   y ← prove_arifix dx ix p,
   apply y, skip
