import category_theory.sites.grothendieck
import topology.sheaves.presheaf
import topology.bases
import topology.category.Top.opens
import category_theory.full_subcategory
import category_theory.equivalence
import tactic.elementwise

universe u

open topological_space
open category_theory

namespace topological_space

-- variables {X : Top} {B : set (set X)} [H : is_topological_basis B]

-- include H

example (x y : Type) (P : Type → Prop) (H : x = y) (f : P x) : P y := H ▸ f
-- #check induced_category.category

def topological_basis (X : Top) := { B : set (set X) | is_topological_basis B }

def opens_basis (X : Top) : topological_basis X :=
⟨{ U : set X | is_open U }, is_topological_basis_opens⟩

namespace topological_basis
variables {X : Top} {B : topological_basis X}

def to_open (U : B) : opens X := ⟨U.val, is_topological_basis.is_open B.property U.property⟩

@[simp] lemma to_open_apply (U : B) : (to_open U).val = U := rfl

variable (B)

instance : category B := induced_category.category to_open

def to_open_functor : B ⥤ opens X := induced_functor to_open

@[simp] lemma to_open_functor_obj : (to_open_functor B).obj = to_open := rfl
@[simp] lemma to_open_functor_obj_apply (U : B) : ((to_open_functor B).obj U).val = U := rfl

-- set_option pp.universes true

def grothendieck_topology : grothendieck_topology B := {
  sieves := λ U s, ∀ x : U, ∃ (V : B) (i : @sieve.arrows _ _ _ s V), x.val ∈ V.val,
  pullback_stable' := λ U V s i hs, by {
    intro x,
    obtain ⟨W, hWU, hx⟩  := hs ⟨x.val, i.down.down x.property⟩,
    obtain ⟨W', hW', h⟩ := B.property.exists_subset_inter W.1 W.2 V.1 V.2 x ⟨hx, x.2⟩,
    use ⟨W', hW'⟩,
    let W'' : B := ⟨W', hW'⟩,
    have W''le : W'' ≤ W ∧ W'' ≤ V := (set.subset_inter_iff.mp h.2),
    use W''le.2,
    exact (s.downward_closed hWU.2 W''le.1.hom : s _),
    exact h.1
  },
  top_mem' := λ U x, exists.intro U $ exists.intro ⟨𝟙 U, trivial⟩ x.2,
  transitive' := λ U s₁ h₁ s₂ h₂ x, by {
    obtain ⟨V, hV, hx⟩ := h₁ x,
    obtain ⟨W, i, h₃⟩ := h₂ hV.2 ⟨x.1, hx⟩,
    use W,
    use ⟨i.1 ≫ hV.val, i.2⟩,
    exact h₃
  }
}


-- instance : ess_surj (to_open_functor (opens_basis X)) := {
--   mem_ess_image := λ U, by {
--     split, swap, exact U, cases U, exact nonempty.intro (as_iso (𝟙 _))
--   },
-- }

instance : full (to_open_functor B) := induced_category.full _
instance : faithful (to_open_functor B) := induced_category.faithful _


def opens_equiv : opens_basis X ≌ opens X :=
equivalence.mk (to_open_functor _) ({ obj := λ U, U, map := λ X Y f, f })
({ hom := { app := λ _, 𝟙 _ }, inv := { app := λ _, 𝟙 _ } })
({ hom := { app := λ U, 𝟙 U }, inv := { app := λ U, 𝟙 U } })


end topological_basis
end topological_space
