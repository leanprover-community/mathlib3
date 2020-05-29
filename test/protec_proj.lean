/-
Copyright (c) 2020 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import tactic.protected

@[protect_proj without baz bar] structure foo : Type :=
(bar : unit) (baz : unit) (qux : unit)

@[protect_proj] structure X : Type :=
(n : nat) (i : fin n)
