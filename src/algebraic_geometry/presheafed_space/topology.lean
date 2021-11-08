import algebraic_geometry.sheafed_space
import category_theory.sites.grothendieck
import algebraic_geometry.presheafed_space.open_immersion

universes v u

open category_theory algebraic_geometry category_theory.limits
namespace algebraic_geometry.SheafedSpace

variables {C : Type u} [category.{v} C] [has_limits C]

structure covers {X : SheafedSpace C} (R : sieve X) (x : X) :=
(obj : SheafedSpace C) (map : obj ⟶ X)
(covers : x ∈ set.range (map : obj ⟶ X).base) (mem : R map)

def zariski_topology : grothendieck_topology (SheafedSpace C) :=
{ sieves := λ X R, ∀ (x : X), ∃ (c : covers R x), PresheafedSpace.is_open_immersion c.map,
  top_mem' := λ X x, ⟨⟨X, 𝟙 X, by simp, trivial⟩, infer_instance⟩,
  pullback_stable' := λ X Y R f hf x,
  begin
    obtain ⟨⟨Z, g, hg₁, hg₂⟩, _⟩ := hf (f.base x),
    resetI,
    fsplit,
    use pullback f g,
    use pullback.fst,
    have := Top.pullback_iso_prod_subtype f.base g.base,
  end

}






end algebraic_geometry.SheafedSpace
