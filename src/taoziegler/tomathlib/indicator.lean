import algebra.indicator_function

lemma of_mul_comp_mul_indicator {α β : Type*} [monoid α] (s : set β) (f : β → α):
  additive.of_mul ∘ (set.mul_indicator s f) = set.indicator s (additive.of_mul ∘ f) := rfl
