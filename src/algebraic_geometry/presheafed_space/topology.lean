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

noncomputable
def restrict_covers {X Y: SheafedSpace C} (f : Y ⟶ X) {R : sieve X} (x : Y)
  (c : covers R (f.base x)) [has_pullback f c.map]
  [preserves_limit (cospan f c.map) (SheafedSpace.forget C)] :
  covers (R.pullback f) x :=
{ obj := pullback f c.map,
  map := pullback.fst,
  covers :=
  begin
    have eq₁ : _ = (pullback.fst : pullback f c.map ⟶ Y).base :=
      preserves_limits_iso_hom_π (SheafedSpace.forget C)
        (cospan f c.map) walking_cospan.left,
    have eq₂ := lim_map_π (diagram_iso_cospan (cospan f c.map ⋙ SheafedSpace.forget C)).hom
      walking_cospan.left,
    erw category.comp_id at eq₂,
    change x ∈ set.range ⇑((pullback.fst : pullback f c.map ⟶ Y).base),
    rw [← eq₁, ← eq₂, ← category.assoc, coe_comp, set.range_comp],
    rw set.range_iff_surjective.mpr ((Top.epi_iff_surjective _).mp _),
    rw set.image_univ,
    change x ∈ set.range (pullback.fst : _ ⟶ (SheafedSpace.forget C).obj Y),
    rw Top.pullback_fst_range,
    tactic.unfreeze_local_instances,
    obtain ⟨a, eq⟩ := c.covers,
    exact ⟨a, eq.symm⟩,
    change epi (_ ≫ (limits.lim.map_iso _).hom),
    apply_instance
  end,
  mem := by { change R _, erw pullback.condition, exact R.downward_closed c.mem _ }
}

/--
The zariski to

-/
def zariski_topology : grothendieck_topology (SheafedSpace C) :=
{ sieves := λ X R, ∀ (x : X), ∃ (c : covers R x), PresheafedSpace.is_open_immersion c.map,
  top_mem' := λ X x, ⟨⟨X, 𝟙 X, by simp, trivial⟩, infer_instance⟩,
  pullback_stable' := λ X Y R f hf x,
  begin
    obtain ⟨c, _⟩ := hf (f.base x),
    resetI,
    use restrict_covers f x c,
    { exact PresheafedSpace.is_open_immersion.SheafedSpace_pullback_fst_of_right _ _ },
  end,
  transitive' := λ X R hR S fS x,
  begin
    obtain ⟨⟨Z, g, hg₁, hg₂⟩, _⟩ := hR x,
    obtain ⟨y, eq⟩ := hg₁,
    obtain ⟨⟨Z', g', hg₁', hg₂'⟩, _⟩ :=  fS hg₂ y,
    obtain ⟨y', eq'⟩ := hg₁',
    use Z',
    { exact g' ≫ g },
    { use y', rw [← eq, ← eq'], refl },
    { exact hg₂' },
    { exactI PresheafedSpace.is_open_immersion.comp _ _ },
  end }






end algebraic_geometry.SheafedSpace
