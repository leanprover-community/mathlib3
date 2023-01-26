/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import data.fintype.card

/-!
# Lemmas about `finite` and `set`s

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove two lemmas about `finite` and `set`s.

## Tags

finiteness, finite sets
-/

open set

universes u v w x
variables {α : Type u} {β : Type v} {ι : Sort w}

lemma finite.set.finite_of_finite_image (s : set α)
  {f : α → β} (h : s.inj_on f) [finite (f '' s)] : finite s :=
finite.of_equiv _ (equiv.of_bijective _ h.bij_on_image.bijective).symm

lemma finite.of_injective_finite_range {f : ι → α}
  (hf : function.injective f) [finite (range f)] : finite ι :=
finite.of_injective (set.range_factorization f) (hf.cod_restrict _)
