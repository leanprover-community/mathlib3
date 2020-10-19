import data.finsupp.basic

open finset

/-- `mon` is the property of being monotone non-increasing. -/
def mon {α β : Type*} [linear_order α] [linear_order β] (f : α → β) :=
  ∀ ⦃x y : α⦄, x ≤ y → f y ≤ f x

lemma monotone_max'_min' {α β : Type*} [decidable_linear_order α] [decidable_linear_order β]
  {s : finset α} (hs : s.nonempty) {f : α → β} (mf : mon f) :
  max' (image f s) (hs.image f) = f (min' s hs) :=
begin
  apply le_antisymm _ (le_max' _ _ (mem_image_of_mem f (min'_mem s hs))),
  refine (image f s).max'_le (nonempty.image hs f) (f (min' s hs)) _,
  intros x hx,
  rw mem_image at hx,
  rcases hx with ⟨a, as, rfl⟩,
  exact mf (min'_le _ _ as),
end
