import topology.category.Profinite
import topology.stone_cech
import category_theory.preadditive.projective

noncomputable theory

open category_theory

variables (X : Type*)

-- move this
namespace ultrafilter

instance : totally_disconnected_space (ultrafilter X) :=
{ is_totally_disconnected_univ :=
  begin
    rintro s - hs,
    sorry
  end }

end ultrafilter

-- move this
namespace stone_cech

variables [topological_space X] [totally_disconnected_space X]

instance : totally_disconnected_space (stone_cech X) :=
{ is_totally_disconnected_univ := sorry }

end stone_cech

namespace Profinite

open function

-- def StoneCech : Type ⥤ Profinite :=
-- { obj := λ X, of $ @stone_cech X ⊥,
--   map := λ X Y f, (Top.discrete ⋙ Top_to_CompHaus).map f,
--   map_id' := (Top.discrete ⋙ Top_to_CompHaus).map_id,
--   map_comp' := (Top.discrete ⋙ Top_to_CompHaus).map_comp' }

-- move this, generalize?
def epi_iff_surjective {X Y : Profinite} (f : X ⟶ Y) : epi f ↔ surjective f :=
begin
  split,
  { contrapose!,
    rintros ⟨y, hy⟩ hf,
    sorry },
  { rw ← category_theory.epi_iff_surjective,
    apply faithful_reflects_epi (forget Profinite) },
end

instance projective_ultrafilter (X : Type*) :
  projective (of $ ultrafilter X) :=
{ factors := λ Y Z f g hg,
  begin
    rw epi_iff_surjective at hg,
    obtain ⟨g', hg'⟩ := hg.has_right_inverse,
    let t : X → Y := g' ∘ f ∘ (pure : X → ultrafilter X),
    let h : ultrafilter X → Y := ultrafilter.extend t,
    have hh : continuous h := continuous_ultrafilter_extend _,
    use ⟨h⟩,
    apply faithful.map_injective (forget Profinite),
    simp only [forget_map_eq_coe, continuous_map.coe_mk, coe_comp],
    refine dense_range_pure.equalizer (g.continuous.comp hh) f.continuous _,
    rw [comp.assoc, ultrafilter_extend_extends, ← comp.assoc, hg'.comp_eq_id, comp.left_id],
  end }

instance projective_stone_cech (X : Type*) [topological_space X] [discrete_topology X] :
  projective (of $ stone_cech X) :=
{ factors := λ Y Z f g hg,
  begin
    rw epi_iff_surjective at hg,
    obtain ⟨g', hg'⟩ := hg.has_right_inverse,
    let t := g' ∘ f ∘ stone_cech_unit,
    have ht : continuous t := continuous_of_discrete_topology,
    let h : stone_cech X → Y := stone_cech_extend ht,
    have hh : continuous h := continuous_stone_cech_extend ht,
    use ⟨h⟩,
    apply faithful.map_injective (forget Profinite),
    simp only [forget_map_eq_coe, continuous_map.coe_mk, coe_comp],
    refine dense_range_stone_cech_unit.equalizer (g.continuous.comp hh) f.continuous _,
    rw [comp.assoc, stone_cech_extend_extends ht, ← comp.assoc, hg'.comp_eq_id, comp.left_id],
  end }

def projective_presentation (X : Profinite) : projective_presentation X :=
{ P := of $ ultrafilter X,
  f :=
  { to_fun := ultrafilter.extend id,
    continuous_to_fun := continuous_ultrafilter_extend _ },
  projective := Profinite.projective_ultrafilter X,
  epi := concrete_category.epi_of_surjective _
  begin
    intro x,
    use (pure x : ultrafilter X),
    exact congr_fun (ultrafilter_extend_extends (𝟙 X)) x,
  end }

instance : enough_projectives Profinite :=
{ presentation := λ X, ⟨projective_presentation X⟩ }

end Profinite
