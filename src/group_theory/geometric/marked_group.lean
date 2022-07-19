import analysis.normed.group.basic
import group_theory.free_group

/-! marked groups.
-/

noncomputable theory
open set function real

namespace geometric_group_theory

section marked_group

--  an S-generated group
structure marking (G : Type*) [group G] :=
(S : Type*)
(decidable : decidable_eq S) -- is this the right place to put it?
(marking : free_group S →* G)
(is_surjective : function.surjective marking)

def free_group_norm (S : Type*) (h : decidable_eq S) (f : free_group S) : ℕ := (free_group.to_word f).length

variables {G : Type*} [group G] {m : marking G}

def group_norm (g : G) : ℕ := nat.lt.is_well_order.wf.min
  (free_group_norm m.S m.decidable '' {x | m.marking x = g})
  (by { apply set.nonempty.image, exact m.is_surjective g })

lemma group_norm_one (x : G) : group_norm x = 0 ↔ x = 1 := begin
  split,
  { intro h, sorry -- the only free group element with length 0 is identity
  },
  { intro h, rw h, sorry -- the identity has length 0
  },
end

lemma group_norm_comm [decidable_eq S] (x : MG) : group_norm x = group_norm x⁻¹ := begin
  -- extract a rep of minimum for x, use inverse for x⁻¹
  sorry
end

lemma group_norm_ineq [decidable_eq S] (x y : MG) : group_norm (x*y) ≤ group_norm x + group_norm y := begin
  -- extract reps for x, y, use product for x*y
  sorry
end

end marked_group

end geometric_group_theory
