/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import group_theory.perm.basic
import logic.equiv.set

/-!
# `equiv.perm.via_embedding`, a noncomputable analogue of `equiv.perm.via_fintype_embedding`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

variables {α β : Type*}

namespace equiv

namespace perm

variables (e : perm α) (ι : α ↪ β)

open_locale classical

/-- Noncomputable version of `equiv.perm.via_fintype_embedding` that does not assume `fintype` -/
noncomputable def via_embedding : perm β :=
extend_domain e (of_injective ι.1 ι.2)

lemma via_embedding_apply (x : α) : e.via_embedding ι (ι x) = ι (e x) :=
extend_domain_apply_image e (of_injective ι.1 ι.2) x

lemma via_embedding_apply_of_not_mem (x : β) (hx : x ∉ _root_.set.range ι) :
  e.via_embedding ι x = x :=
extend_domain_apply_not_subtype e (of_injective ι.1 ι.2) hx

/-- `via_embedding` as a group homomorphism -/
noncomputable def via_embedding_hom : perm α →* perm β:=
extend_domain_hom (of_injective ι.1 ι.2)

lemma via_embedding_hom_apply : via_embedding_hom ι e = via_embedding e ι := rfl

lemma via_embedding_hom_injective : function.injective (via_embedding_hom ι) :=
extend_domain_hom_injective (of_injective ι.1 ι.2)

end perm

end equiv
