/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best
-/
import data.finsupp.defs
import data.fintype.basic

/-!

# Finiteness and infiniteness of `finsupp`

Some lemmas on the combination of `finsupp`, `fintype` and `infinite`.

-/

noncomputable instance finsupp.fintype {ι π : Sort*} [fintype ι] [fintype π] [has_zero π] :
  fintype (ι →₀ π) :=
by letI := classical.dec_eq ι; exact fintype.of_injective _ fun_like.coe_injective

instance finsupp.infinite_of_right {ι π : Sort*} [infinite π] [has_zero π] [nonempty ι] :
  infinite (ι →₀ π) :=
infinite.of_injective (λ i, finsupp.single (classical.arbitrary ι) i)
  (finsupp.single_injective (classical.arbitrary ι))
