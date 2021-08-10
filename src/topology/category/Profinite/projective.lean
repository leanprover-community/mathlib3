import topology.category.Profinite
import topology.stone_cech
import topology.discrete_quotient
import category_theory.preadditive.projective

noncomputable theory

open category_theory function

namespace Profinite

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
