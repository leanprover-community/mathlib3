/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best
-/
import data.finsupp.defs
import data.fintype.basic

/-!

# Finiteness and infiniteness of `finsupp`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Some lemmas on the combination of `finsupp`, `fintype` and `infinite`.

-/

noncomputable instance finsupp.fintype {ι π : Sort*} [decidable_eq ι] [has_zero π]
  [fintype ι] [fintype π] :
  fintype (ι →₀ π) :=
fintype.of_equiv _ finsupp.equiv_fun_on_finite.symm

instance finsupp.infinite_of_left {ι π : Sort*} [nontrivial π] [has_zero π] [infinite ι] :
  infinite (ι →₀ π) :=
let ⟨m, hm⟩ := exists_ne (0 : π) in infinite.of_injective _ $ finsupp.single_left_injective hm

instance finsupp.infinite_of_right {ι π : Sort*} [infinite π] [has_zero π] [nonempty ι] :
  infinite (ι →₀ π) :=
infinite.of_injective (λ i, finsupp.single (classical.arbitrary ι) i)
  (finsupp.single_injective (classical.arbitrary ι))
