import order.filter.basic

open filter

/- Turn off trace messages so they don't pollute the test build: -/
set_option trace.silence_library_search true

example {α β γ : Type*} {A : filter α} {B : filter β} {C : filter γ} {f : α → β} {g : β → γ}
  (hf : tendsto f A B) (hg : tendsto g B C) : tendsto (g ∘ f) A C :=
calc
map (g ∘ f) A = map g (map f A) : by library_search
          ... ≤ map g B         : by library_search!
          ... ≤ C               : by library_search!
