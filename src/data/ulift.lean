/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import data.equiv.basic

/-!
# Extra lemmas about `ulift` and `plift`

In this file we provide `subsingleton`, `unique`, `decidable_eq`, and `is_empty` instances for
`ulift α` and `plift α`. We also prove `ulift.forall`, `ulift.exists`, `plift.forall`, and
`plift.exists`.
-/

universes u v

namespace plift

variables {α : Sort u} {β : Sort v}

instance [subsingleton α] : subsingleton (plift α) := equiv.plift.subsingleton
instance [unique α] : unique (plift α) := equiv.plift.unique
instance [decidable_eq α] : decidable_eq (plift α) := equiv.plift.decidable_eq
instance [is_empty α] : is_empty (plift α) := equiv.plift.is_empty

@[simp] lemma «forall» {p : plift α → Prop} : (∀ x, p x) ↔ ∀ x : α, p (plift.up x) :=
equiv.plift.forall_congr_left'

@[simp] lemma «exists» {p : plift α → Prop} : (∃ x, p x) ↔ ∃ x : α, p (plift.up x) :=
equiv.plift.exists_congr_left

end plift

namespace ulift

variables {α : Type u} {β : Type v}

instance [subsingleton α] : subsingleton (ulift α) := equiv.ulift.subsingleton
instance [unique α] : unique (ulift α) := equiv.ulift.unique
instance [decidable_eq α] : decidable_eq (ulift α) := equiv.ulift.decidable_eq
instance [is_empty α] : is_empty (ulift α) := equiv.ulift.is_empty

@[simp] lemma «forall» {p : ulift α → Prop} : (∀ x, p x) ↔ ∀ x : α, p (ulift.up x) :=
equiv.ulift.forall_congr_left'

@[simp] lemma «exists» {p : ulift α → Prop} : (∃ x, p x) ↔ ∃ x : α, p (ulift.up x) :=
equiv.ulift.exists_congr_left

end ulift
