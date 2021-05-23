/-
Copyright (c) 2020 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import tactic.protected

open tactic

@[protect_proj without baz bar] structure foo : Type :=
(bar : unit) (baz : unit) (qux : unit)

open foo

run_cmd resolve_name `bar
run_cmd resolve_name `foo.qux
run_cmd success_if_fail $ resolve_name `qux

@[protect_proj] structure X : Type :=
(n : nat) (i : fin n)

open X

run_cmd resolve_name `X.i
run_cmd resolve_name `X.n
run_cmd success_if_fail $ resolve_name `n
