/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import logic.equiv.basic

/-!
# Extra lemmas about `ulift` and `plift`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we provide `subsingleton`, `unique`, `decidable_eq`, and `is_empty` instances for
`ulift α` and `plift α`. We also prove `ulift.forall`, `ulift.exists`, `plift.forall`, and
`plift.exists`.
-/

universes u v
open function

namespace plift

variables {α : Sort u} {β : Sort v}

instance [subsingleton α] : subsingleton (plift α) := equiv.plift.subsingleton
instance [nonempty α] : nonempty (plift α) := equiv.plift.nonempty
instance [unique α] : unique (plift α) := equiv.plift.unique
instance [decidable_eq α] : decidable_eq (plift α) := equiv.plift.decidable_eq
instance [is_empty α] : is_empty (plift α) := equiv.plift.is_empty

lemma up_injective : injective (@up α) := equiv.plift.symm.injective
lemma up_surjective : surjective (@up α) := equiv.plift.symm.surjective
lemma up_bijective : bijective (@up α) := equiv.plift.symm.bijective

@[simp] lemma up_inj {x y : α} : up x = up y ↔ x = y := up_injective.eq_iff

lemma down_surjective : surjective (@down α) := equiv.plift.surjective
lemma down_bijective : bijective (@down α) := equiv.plift.bijective

@[simp] lemma «forall» {p : plift α → Prop} : (∀ x, p x) ↔ ∀ x : α, p (plift.up x) :=
up_surjective.forall

@[simp] lemma «exists» {p : plift α → Prop} : (∃ x, p x) ↔ ∃ x : α, p (plift.up x) :=
up_surjective.exists

end plift

namespace ulift

variables {α : Type u} {β : Type v}

instance [subsingleton α] : subsingleton (ulift α) := equiv.ulift.subsingleton
instance [nonempty α] : nonempty (ulift α) := equiv.ulift.nonempty
instance [unique α] : unique (ulift α) := equiv.ulift.unique
instance [decidable_eq α] : decidable_eq (ulift α) := equiv.ulift.decidable_eq
instance [is_empty α] : is_empty (ulift α) := equiv.ulift.is_empty

lemma up_injective : injective (@up α) := equiv.ulift.symm.injective
lemma up_surjective : surjective (@up α) := equiv.ulift.symm.surjective
lemma up_bijective : bijective (@up α) := equiv.ulift.symm.bijective

@[simp] lemma up_inj {x y : α} : up x = up y ↔ x = y := up_injective.eq_iff

lemma down_surjective : surjective (@down α) := equiv.ulift.surjective
lemma down_bijective : bijective (@down α) := equiv.ulift.bijective

@[simp] lemma «forall» {p : ulift α → Prop} : (∀ x, p x) ↔ ∀ x : α, p (ulift.up x) :=
up_surjective.forall

@[simp] lemma «exists» {p : ulift α → Prop} : (∃ x, p x) ↔ ∃ x : α, p (ulift.up x) :=
up_surjective.exists

end ulift
