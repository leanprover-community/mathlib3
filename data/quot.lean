/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Quotients -- extends the core library
-/
import data.set
open set

variables {α : Type*}

lemma forall_quotient_iff {α : Type*} [r : setoid α] {p : quotient r → Prop} :
  (∀a:quotient r, p a) ↔ (∀a:α, p ⟦a⟧) :=
⟨assume h x, h _, assume h a, a.induction_on h⟩

@[simp] lemma quot_mk_image_univ_eq [setoid α] : (λx : α, ⟦x⟧) '' univ = univ :=
set.ext $ assume x, quotient.induction_on x $ assume a, ⟨by simp, assume _, ⟨a, trivial, rfl⟩⟩
