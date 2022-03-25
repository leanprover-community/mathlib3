/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import data.set.intervals.basic

/-!
# Intervals in dense orders

We show variants of the following theorem: open intervals in a dense order have neither minima nor
maxima. These are registered as instances.
-/

variables (α : Type*) [preorder α] [densely_ordered α]

instance {x y : α} : no_min_order (set.Ioo x y) :=
⟨λ ⟨a, ha₁, ha₂⟩, begin
  rcases exists_between ha₁ with ⟨b, hb₁, hb₂⟩,
  exact ⟨⟨b, hb₁, hb₂.trans ha₂⟩, hb₂⟩
end⟩

instance {x y : α} : no_min_order (set.Ioc x y) :=
⟨λ ⟨a, ha₁, ha₂⟩, begin
  rcases exists_between ha₁ with ⟨b, hb₁, hb₂⟩,
  exact ⟨⟨b, hb₁, hb₂.le.trans ha₂⟩, hb₂⟩
end⟩

instance {x : α} : no_min_order (set.Ioi x) :=
⟨λ ⟨a, ha⟩, begin
  rcases exists_between ha with ⟨b, hb₁, hb₂⟩,
  exact ⟨⟨b, hb₁⟩, hb₂⟩
end⟩

instance {x y : α} : no_max_order (set.Ioo x y) :=
⟨λ ⟨a, ha₁, ha₂⟩, begin
  rcases exists_between ha₂ with ⟨b, hb₁, hb₂⟩,
  exact ⟨⟨b, ha₁.trans hb₁, hb₂⟩, hb₁⟩
end⟩

instance {x y : α} : no_max_order (set.Ico x y) :=
⟨λ ⟨a, ha₁, ha₂⟩, begin
  rcases exists_between ha₂ with ⟨b, hb₁, hb₂⟩,
  exact ⟨⟨b, ha₁.trans hb₁.le, hb₂⟩, hb₁⟩
end⟩

instance {x : α} : no_max_order (set.Iio x) :=
⟨λ ⟨a, ha⟩, begin
  rcases exists_between ha with ⟨b, hb₁, hb₂⟩,
  exact ⟨⟨b, hb₂⟩, hb₁⟩
end⟩
