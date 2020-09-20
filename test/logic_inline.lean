/-
Copyright (c) 2019 Keeley Hoek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek, Floris van Doorn
-/

import logic.basic
meta def error_msg (s : string) : bool := @undefined_core bool $ s ++ ".decidable not inlined"

meta def examine (b : Prop) [decidable b] : bool := b

open tactic

run_cmd do e ← to_expr ```(examine (ff ∧ (error_msg "and"))) >>= eval_expr bool, guard (e = ff)
run_cmd do e ← to_expr ```(examine (tt ∨ (error_msg "or"))) >>= eval_expr bool, guard (e = tt)
