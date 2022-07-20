import analysis.normed.group.basic
import group_theory.free_group
import order.well_founded

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

lemma empty_list {α : Type*} (l : list α) : l.length = 0 → l = list.nil := begin
  intro h, ext1, finish
end

lemma free_group_norm_zero (S : Type*) (h : decidable_eq S) (f : free_group S) : free_group_norm S h f = 0 → f = 1 := begin
  intro h,
  have fempty : free_group.to_word f = list.nil, { exact empty_list (free_group.to_word f) h },
  have h : free_group.mk (free_group.to_word f) = free_group.mk list.nil, {
    rw fempty,
  },
  rw free_group.to_word.mk at h,
  exact h
end

variables {G : Type*} [group G] (m : marking G)

-- suggestion to use nat.find instead of nat.lt.is_well_order.wf.min
def group_norms (g : G) : set ℕ := (free_group_norm m.S m.decidable '' {x | m.marking x = g})

def group_norms_nonempty (g : G) : (group_norms m g).nonempty := 
  (by { apply set.nonempty.image, exact m.is_surjective g })

def group_norm (g : G) : ℕ := nat.lt.is_well_order.wf.min
  (group_norms m g) (group_norms_nonempty m g)

lemma group_norm_one (x : G) : group_norm m x = 0 ↔ x = 1 := begin
  split,
  { intro hzero,
    have h : (group_norm m x) ∈ (group_norms m x) := nat.lt.is_well_order.wf.min_mem (group_norms m x) (group_norms_nonempty m x),
    rw hzero at h,
    rcases h with ⟨y,ymem,normzero⟩,
    have yone : y = 1, { 
      exact free_group_norm_zero m.S m.decidable y normzero,
    },
    rw yone at ymem,
    finish -- can we replace it by a simple command?
  },
  { intro h, rw h,
    have h : 0 ∈ group_norms m 1 := begin
      rw group_norms,
      rw mem_image,
      use 1; finish
    end,
-- well_founded.min_le seems inaccessible
  let normzero := well_founded.not_lt_min nat.lt.is_well_order.wf (group_norms m 1) (group_norms_nonempty m 1) h,
  norm_num at normzero,
  exact normzero
  },
end

lemma group_norm_comm (x : G) : group_norm m x = group_norm m x⁻¹ := begin
  -- extract a rep of minimum for x, use inverse for x⁻¹
  sorry
end

lemma group_norm_ineq (x y : G) : group_norm m (x*y) ≤ group_norm m x + group_norm m y := begin
  -- extract reps for x, y, use product for x*y
  sorry
end

end marked_group

end geometric_group_theory

/- comments by Sébastien Gouëzel:

If you want to register your group as a metric space (where the distance depends on S), you will need to embrace the type synonym trick. Instead of a class, define a structure marking S G as you did. And then given a group G and a marking m, define a new type marked_group m G := G. On this new type, you can register the same group structure as on G, but you can also register a distance as m is now available to the system when you consider x y : marked_group m G.

A tentative scheme avoiding out_params would be the following:

    First, work with normed groups, and prove whatever you like here. Possibly adding new typeclass assumptions that say that the distance is proper or hyperbolic or whatever.
    Then, to construct instances of such normed groups, do it on type synonyms. For instance, given two types S and G with [group G], define marking S G as the space of markings of G parameterized by S. Then, given a group G and a marking m, define a typemarked_group G m := G as a copy of G, then define on it the group structure coming from G (with @[derive ...]) and the norm associated to m. Then marked_group G m will be an instance of a normed group.
-/
