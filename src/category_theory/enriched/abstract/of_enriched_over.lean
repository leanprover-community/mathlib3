import category_theory.enriched.abstract.category
import category_theory.enriched.enriched_over

universes v u

namespace category_theory

variables (V : Type (v+1)) [𝒱 : concrete_monoidal_category.{v} V]
variables (C : Type u) [𝒞 : category.{v} C]
include 𝒱 𝒞

instance enriched_category_of_enriched_over [enriched_over.{v} V C] : enriched_category V C :=
{ hom  := enriched_over.e_hom V,
  id   := enriched_over.e_id V,
  comp := enriched_over.e_comp V,
  id_comp' := λ X Y,
  begin
    -- Use faithfulness of the forgetful functor to turn this into a question in `C`.
    apply (forget V).injectivity,
    ext,
    simp only [functor_to_types.map_comp],
    -- Transport the goal backwards through `e_hom_forget`, to obtain an equation in `C`.
    apply (enriched_over.e_hom_forget V X Y).injective,
    -- ... which hopefully just comes down to `id_comp`.

    -- We first transport `x` through `λ_ (enriched_over.e_hom V X Y)`.
    -- We really need a tactic to handle the next four lines:
    have t := congr_fun (((forget V).map_iso (λ_ (enriched_over.e_hom V X Y))).hom_inv_id) x,
    simp only [functor.map_iso_hom, functor.map_iso_inv, types_id, types_comp, id.def, function.comp_app] at t,
    generalize_hyp : (forget V).map ((λ_ (enriched_over.e_hom V X Y)).hom) x = y at t,
    subst t,

    simp only [functor_to_types.inv_hom_id],

    -- This is not really how I want to proceed, but okay:
    convert category.id_comp C _,
    rw ←enriched_over.e_id_forget V C X,
    rw enriched_over.e_comp_forget V C,
    simp,

    congr,
    dsimp [as_term],
    rw ←functor_to_types.map_comp,

    -- move the λ_ to the rhs, and then use left_unitality?

    -- We next transport `y` through `e_hom_forget`:
    -- have t := (enriched_over.e_hom_forget V X Y).left_inv y,
    -- generalize_hyp : (enriched_over.e_hom_forget V X Y).to_fun y = f at t,
    -- subst t,

    -- simp,
    -- ...

  end,
  comp_id' := sorry,
  assoc' := sorry, }

end category_theory
