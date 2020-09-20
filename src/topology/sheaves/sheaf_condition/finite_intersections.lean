import topology.sheaves.sheaf_condition.pairwise_intersections

universes v

namespace Top.cover

open topological_space
open opposite
open category_theory
open category_theory.limits
open category_theory.pairwise category_theory.pairwise.hom

variables {X : Top.{v}}
variables {ι : Type v}
variables (U : ι → opens X)

@[simps]
def finset_functor : finset ι ⥤ (opens X)ᵒᵖ :=
{ obj := λ s, op (Inf (U '' ↑s)),
  map := λ s s' f, op_hom_of_le (Inf_le_Inf (set.monotone_image (le_of_hom f))), }

def nonempty_finset_functor : { s : finset ι // s.nonempty } ⥤ (opens X)ᵒᵖ :=
full_subcategory_inclusion _ ⋙ finset_functor U

@[simp]
lemma nonempty_finset_functor_obj (s : { s : finset ι // s.nonempty }) :
  (nonempty_finset_functor U).obj s = op (Inf (U '' ↑s.val)) := rfl

def nonempty_finset_functor_cone : limits.cone (nonempty_finset_functor U) :=
{ X := op (supr U),
  π :=
  { app := λ s, op_hom_of_le
    begin
      dsimp,
      rcases s with ⟨s, ⟨i, m⟩⟩,
      have h₁ : Inf (U '' ↑s) ≤ U i := Inf_le ⟨i, ⟨m, rfl⟩⟩,
      have h₂ : U i ≤ supr U := le_supr U i,
      exact h₁.trans h₂,
    end }, }

def nonempty_finset_functor_cone_is_limit : is_limit (nonempty_finset_functor_cone U) :=
{ lift := λ s, op_hom_of_le (λ x h,
  begin
    simp [opens.mem_supr] at h,
    rcases h with ⟨_, ⟨⟨H, ⟨⟨i, rfl⟩, rfl⟩⟩, m⟩⟩,
    exact le_of_op_hom (s.π.app ⟨{i}, finset.singleton_nonempty i⟩) (by simpa using m),
  end) }

-- TODO yet another formulation of the sheaf condition

open_locale classical

@[simp]
noncomputable def pairwise_to_nonempty_finset_functor_obj :
  pairwise ι → { s : finset ι // s.nonempty }
| (single i) := ⟨[i].to_finset, ⟨i, by simp⟩⟩
| (pair i j) := ⟨[i,j].to_finset, ⟨i, by simp⟩⟩

@[simp]
noncomputable def pairwise_to_nonempty_finset_functor_map :
  Π {X Y : pairwise ι} (f : X ⟶ Y),
  pairwise_to_nonempty_finset_functor_obj X ⟶ pairwise_to_nonempty_finset_functor_obj Y
| _ _ (id_single i) := hom_of_le (le_refl _)
| _ _ (id_pair i j) := hom_of_le (le_refl _)
| _ _ (left i j) := hom_of_le (λ x h, by { simp, left, rcases h with ⟨rfl⟩|w, refl, cases w, })
| _ _ (right i j) := hom_of_le (λ x h, by { simp, right, rcases h with ⟨rfl⟩|w, refl, cases w, })

@[simps]
noncomputable def pairwise_to_nonempty_finset_functor :
  pairwise ι ⥤ { s : finset ι // s.nonempty } :=
{ obj := pairwise_to_nonempty_finset_functor_obj,
  map := λ X Y f, pairwise_to_nonempty_finset_functor_map f, }

-- TODO show this is initial?

end Top.cover
