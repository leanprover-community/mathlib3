/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import .forced

/-!
# Bogdanov's lemma on perfect matchings
-/

open finset fintype

variables {α : Type*}

namespace simple_graph
variables [fintype α] (G : simple_graph α)

lemma bogdanov3 (hα : 4 ≤ card α) : card (G.forcings 1) ≤ 3 := sorry

lemma bogdanov2 (hα : 5 ≤ card α) : card (G.forcings 1) ≤ 2 := sorry

end simple_graph
