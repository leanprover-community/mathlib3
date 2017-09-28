/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Quotients -- extends the core library
-/

variables {α : Type*} {p : α → Prop} {q : {a // p a} → Prop}

lemma forall_subtype : (∀x:{a // p a}, q x) ↔ (∀a (h : p a), q ⟨a, h⟩) :=
⟨assume h a ha, h ⟨_, _⟩, assume h ⟨a, ha⟩, h _ _⟩

theorem exists_subtype : (∃x : subtype p, q x) ↔ (∃x (h : p x), q ⟨x, h⟩) :=
⟨assume ⟨⟨x, h⟩, h'⟩, ⟨x, h, h'⟩, assume ⟨x, h, h'⟩, ⟨⟨x, h⟩, h'⟩⟩
