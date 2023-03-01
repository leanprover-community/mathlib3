import order.filter.basic

open filter

/- Turn off trace messages so they don't pollute the test build: -/
set_option trace.silence_library_search true

-- The following fails with a deterministic timeout.
-- example {α β γ : Type*} {A : filter α} {B : filter β} {C : filter γ} {f : α → β} {g : β → γ}
--   (hf : tendsto f A B) (hg : tendsto g B C) : map (g ∘ f) A = map g (map f A) :=
-- by library_search

example {α β γ : Type*} {A : filter α} {B : filter β} {C : filter γ} {f : α → β} {g : β → γ}
  (hf : tendsto f A B) (hg : tendsto g B C) : map g (map f A) ≤ C :=
calc
map g (map f A) ≤ map g B       : by library_search!
          ... ≤ C               : by library_search!

-- this was the original version of the test, as of Dec 2022 it times out
-- example {α β γ : Type*} {A : filter α} {B : filter β} {C : filter γ} {f : α → β} {g : β → γ}
--   (hf : tendsto f A B) (hg : tendsto g B C) : tendsto (g ∘ f) A C :=
-- calc
-- map (g ∘ f) A = map g (map f A) : by library_search
--           ... ≤ map g B         : by library_search!
--           ... ≤ C               : by library_search!
