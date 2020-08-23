import topology.sheaves.local_predicate
import topology.sheaves.stalks

universes v

noncomputable theory

open Top
open topological_space
open opposite
open category_theory.limits

variables {X : Top.{v}}
variables (F : presheaf (Type v) X)

namespace sheafification

def stalks : Π x : X, Type v := λ x : X, F.stalk x

def is_germ : prelocal_predicate (stalks F) :=
{ pred := λ U f, ∀ x : U, ∃ (V : opens X) (m : x.1 ∈ V) (i : V ⟶ U) (g : F.obj (op V)),
    f x = colimit.ι ((open_nhds.inclusion x.1).op ⋙ F) (op ⟨V, m⟩) g, -- TODO define `germ`!
  res := λ V U i f w x,
  begin
    rcases w (i x) with ⟨V', m', i', g, p⟩,
    refine ⟨V ⊓ V', ⟨x.2, m'⟩, opens.inf_le_left _ _, F.map (opens.inf_le_right _ _).op g, _⟩,
    convert p,
    let j : (⟨V ⊓ V', ⟨x.2, m'⟩⟩ : open_nhds x.1) ⟶ (⟨V', m'⟩) := opens.inf_le_right _ _,
    exact congr_fun (colimit.w ((open_nhds.inclusion x.val).op ⋙ F) j.op) g,
  end, }

def is_locally_germ : local_predicate (stalks F) := (is_germ F).sheafify

end sheafification

def sheafification : sheaf (Type v) X :=
subsheaf_to_Types (sheafification.is_locally_germ F)

-- TODO check the stalks are correct
-- TODO functoriality
