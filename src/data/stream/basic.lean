/-
Copyright (c) 2020 Gabriel Ebner, Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Simon Hudon
-/
import tactic.ext
import data.stream

/-!
# Additional instances and attributes for streams
-/

attribute [ext] stream.ext

instance {α} [inhabited α] : inhabited (stream α) :=
⟨stream.const (default _)⟩

namespace stream

variables {α : Type*}

lemma mem_def (s : stream α) (x : α) :
  x ∈ s ↔ ∃ i, x = s.nth i := iff.refl _

end stream
