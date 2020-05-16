/-
Copyright (c) 2020 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton
-/

/-!
This file adds an axiom `todo`, and a corresponding tactic,
which can be used in place of `sorry`.
It is only intended for use inside the roadmap subdirectory.
-/

/--
Axiom used to skip proofs in formal roadmaps.
(When working on a roadmap, you may prefer to prove new lemmas,
rather than trying to solve an `exact todo` in-line.
The tactic `extract_goal` is useful for this.)
-/
axiom todo {p : Prop} : p

namespace tactic
namespace interactive

/--
An axiomatic alternative to `sorry`, used in formal roadmaps.
-/
meta def todo : tactic unit := `[exact todo]

end interactive
end tactic
