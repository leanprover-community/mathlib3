
import tactic.ext data.stream

attribute [extensionality] stream.ext

namespace stream

variables {α : Type*}

lemma mem_def (s : stream α) (x : α) :
  x ∈ s ↔ ∃ i, x = s.nth i := iff.refl _

end stream
