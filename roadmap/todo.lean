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
