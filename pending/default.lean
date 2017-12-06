/- Temporary space for definitions pending merges to the lean repository -/

attribute [simp] nat.div_self

@[simp] lemma of_to_bool_iff {p : Prop} [decidable p] : to_bool p ↔ p :=
⟨of_to_bool_true, to_bool_true⟩
