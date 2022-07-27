import algebraic_geometry.sheafed_space
import topology.sheaves.sheaf_condition.unique_gluing

section

open topological_space
open category_theory category_theory.limits
open Top
open opposite

universes u v w

variables {X : Top.{u}} (p₀ : X) {C : Type v} [category.{w} C] (S : C)
variables {star : C} (ts : is_terminal star)
variable [Π (U : (opens X)ᵒᵖ), decidable (p₀ ∈ unop U)]

instance : Π (U : opens X), decidable (p₀ ∈ U) :=
λ U, (infer_instance : decidable (p₀ ∈ unop (op U)))

@[simps]
def skyscraper_presheaf : presheaf C X :=
{ obj := λ U, ite (p₀ ∈ unop U) S star,
  map := λ U V i, dite (p₀ ∈ unop V)
    (λ h, eq_to_hom (if_pos (le_of_hom i.unop h)) ≫ 𝟙 S ≫ eq_to_hom (if_pos h).symm)
    (λ h, ts.from _ ≫ eq_to_hom (if_neg h).symm),
  map_id' := λ U,
  begin
    split_ifs,
    { simp, },
    { rw eq_comp_eq_to_hom,
      exact ts.hom_ext _ _, },
  end,
  map_comp' := λ U V W iVU iWV,
  begin
    by_cases hW : p₀ ∈ unop W,
    { have hV : p₀ ∈ unop V := le_of_hom iWV.unop hW,
      have hU : p₀ ∈ unop U := le_of_hom iVU.unop hV,
      split_ifs,
      simp },
    { split_ifs;
      rw eq_comp_eq_to_hom;
      exact ts.hom_ext _ _, }
  end }

section

variables {p₀}

lemma skyscraper_presheaf_obj_of_mem {U : opens X} (h : p₀ ∈ U) :
  (skyscraper_presheaf p₀ S ts).obj (op U) = S :=
if_pos h

lemma skyscraper_presheaf_obj_of_not_mem {U : opens X} (h : p₀ ∉ U) :
  (skyscraper_presheaf p₀ S ts).obj (op U) = star :=
if_neg h

end

def skyscraper_sheaf : sheaf C X :=
⟨skyscraper_presheaf p₀ S ts, λ c U s hs x hx,
  ⟨dite (p₀ ∈ U)
    (λ h, x (hs p₀ h).some_spec.some (hs p₀ h).some_spec.some_spec.1 ≫
        eq_to_hom ((skyscraper_presheaf_obj_of_mem S ts (hs p₀ h).some_spec.some_spec.2).trans
          (skyscraper_presheaf_obj_of_mem S ts h).symm))
    (λ h, ts.from c ≫ (eq_to_hom (skyscraper_presheaf_obj_of_not_mem S ts h).symm)),
    λ V inc h,
    begin
      by_cases hV : p₀ ∈ V,
      { have hU : p₀ ∈ U := le_of_hom inc hV,
        split_ifs,
        generalize_proofs h₁ h₂ h₃ h₄,
        dsimp,
        split_ifs,
        -- generalize_proofs h₅ h₆,
        rw [category.id_comp, eq_to_hom_trans, category.assoc, eq_to_hom_trans],
        generalize_proofs h₅,
        have := hx _ _ h₂.some_spec.1 h rfl,
        },
    end, _⟩⟩

/-

dite (p₀ ∈ U)
    (λ h, (begin
      have := x (𝟙 _) _,
      dsimp at this,
    end : c ⟶ S) ≫ (eq_to_hom (skyscraper_presheaf_obj_of_mem S ts h).symm))
    (λ h, ts.from c ≫ (eq_to_hom (skyscraper_presheaf_obj_of_not_mem S ts h).symm))
-/
end
