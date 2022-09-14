import topology.sheaves.stalks
import topology.order
import category_theory.abelian.basic

section

open topological_space
open category_theory category_theory.limits
open Top Top.presheaf
open opposite

universes u v
variables {X : Top.{u}} (C : Type v) [category.{u} C]
variables [has_colimits C] [concrete_category C]
variables {𝓕 : sheaf C X}

local attribute [instance] concrete_category.has_coe_to_sort
local attribute [instance] concrete_category.has_coe_to_fun

local notation `stalks` := Σ x, 𝓕.presheaf.stalk x

instance topology_on_stalks : topological_space stalks :=
topological_space.generate_from $ λ S, ∃ (U : opens X) (s : 𝓕.1.obj (op U)), ∀ (x : U),
  (⟨x, germ 𝓕.presheaf x s⟩ : stalks) ∈ S

open_locale zero_object

lemma test [abelian C] : continuous (sigma.fst : stalks → X) :=
{ is_open_preimage := λ s hs,
  begin
    have : (sigma.fst : stalks → X) ⁻¹' s = set.sUnion (λ x, ∀ (y : stalks), y ∈ x → y.1 ∈ s),
    { ext x, rw [set.mem_preimage, set.mem_sUnion],
      split,
      { intros h, refine ⟨{x}, λ t ht, _, _⟩,
        rw set.mem_singleton_iff at ht, rwa ht,
        exact set.mem_singleton _, },
      { rintros ⟨t, ⟨ht1, ht2⟩⟩, exact ht1 x ht2, } },
    rw this, clear this,
    apply generate_open.sUnion,
    rintros S hS,

    have : sigma.fst '' S = s,
    { ext x, split; intros hx,
      { rw set.mem_image at hx, rcases hx with ⟨⟨x, t⟩, hx, rfl⟩,
        exact hS ⟨x, t⟩ hx, },
      { refine ⟨⟨x, _⟩, _, rfl⟩, }, },

    apply generate_open.basic,

    by_cases h : S = ∅,
    { subst h, refine ⟨∅, sorry, sorry⟩,  },
    { refine ⟨_, _, _⟩, },
    -- specialize hS ⟨default, default⟩,
    -- refine ⟨⟨_, hs⟩, _, λ x, _⟩,


    have := topological_space.generate_from,
  end }

end
