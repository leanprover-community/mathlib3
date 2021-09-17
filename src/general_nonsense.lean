import category_theory.limits.filtered_colimit_commutes_finite_limit
import category_theory.limits.functor_category

open category_theory category_theory.limits opposite category_theory.functor

noncomputable theory

variables (I : Type)

/-- the function type `I → X` is naturally the categorical product of `I` copies of `X` -/
def key_nat_iso : coyoneda.obj (op I) ≅ const (discrete I) ⋙ lim :=
nat_iso.of_components
(λ X, {
  hom := limit.lift ((const (discrete I)).obj X) ⟨I → X, discrete.nat_trans ($<)⟩,
  inv := flip $ limit.π $ (const (discrete I)).obj X,
  hom_inv_id' := by ext; simp only [flip, discrete.nat_trans_app, types.limit.lift_π_apply,
      types_comp_apply, types_id_apply],
  inv_hom_id' := by ext; simp only [flip, discrete.nat_trans_app, types.limit.lift_π_apply,
      types_comp_apply, types_id_apply] })
begin
  intros,
  ext,
  simp only [const.map_app, functor.comp_map, limit.lift_map, discrete.nat_trans_app,
    coyoneda_obj_map, lim_map_eq_lim_map, functor_to_types.comp, types.limit.lift_π_apply,
    types_comp_apply, cones.postcompose_obj_π],
end

variables [fintype I] [decidable_eq I] (J : Type) [small_category J] [is_filtered J]

/-- this is a restatement of the main result of `filtered_colimit_commutes_finite_limit`.
probably the result should generalised, and the proof should be neater if you use the `limit` api
properly. -/
instance : preserves_colimits_of_shape J (lim : (discrete I ⥤ Type) ⥤ Type) :=
{ preserves_colimit :=
  begin
    suffices : ∀ F : discrete I × J ⥤ Type, preserves_colimit
      (category_theory.curry.obj $ category_theory.prod.swap _ _ ⋙ F) lim,
    { intro K,
      apply preserves_colimit_of_iso_diagram _ _,
      work_on_goal 2 { exact this (category_theory.prod.swap _ _ ⋙ category_theory.uncurry.obj K) },
      change (category_theory.uncurry ⋙ category_theory.curry).obj K ≅ (𝟭 _).obj K,
      apply iso.app,
      exact category_theory.currying.unit_iso.symm, },
    intro F,
    apply preserves_colimit_of_preserves_colimit_cocone,
    work_on_goal 2 {
      refine ⟨curry.obj F ⋙ colim,
        λ j, discrete.nat_trans (λ i, colimit.ι ((curry.obj F).obj i) _), _⟩,
      intros j j' f,
      apply category_theory.nat_trans.ext,
      funext i,
      simpa only using colimit.w ((curry.obj F).obj i) f, },
    { apply evaluation_jointly_reflects_colimits,
      intro i,
      refine is_colimit.of_iso_colimit (colimit.is_colimit _) _,
      refine @as_iso _ _ _ _ _ _,
      { exact ⟨𝟙 _, λ _, rfl⟩, },
      { apply cocones.cocone_iso_of_hom_iso _,
        exact is_iso.id _, }, },
    { refine is_colimit.of_iso_colimit (colimit.is_colimit _) _,
      refine @as_iso _ _ _ _ _ _,
      { refine ⟨colimit_limit_to_limit_colimit F, _⟩,
        intro j,
        ext,
        simp only [discrete.nat_trans_app, lim_map_eq_lim_map, ι_colimit_limit_to_limit_colimit_π_apply,
          colimit.w, map_cocone_ι_app, eq_self_iff_true, colimit.cocone_ι, lim_map_π,
          types_comp_apply, types.limit.map_π_apply, discrete.nat_trans_app], },
      { apply cocones.cocone_iso_of_hom_iso _,
        apply limits.colimit_limit_to_limit_colimit_is_iso, }, },
  end }

/-- the diagonal functor preserves colimits of any shape (basically since limits in the functor
category are computed pointwise)-/
instance const_preserves {C D} [category C] [category D] :
  preserves_colimits_of_shape J (category_theory.functor.const D : C ⥤ (D ⥤ C)) :=
{ preserves_colimit := λ K, { preserves := λ c hC,
  begin
    apply evaluation_jointly_reflects_colimits,
    intro d,
    cases K,
    apply is_colimit.of_iso_colimit hC,
    refine @as_iso _ _ _ _ _ _,
    { refine ⟨𝟙 _, _⟩,
      intro j,
      simp,
      apply category.comp_id, },
    { apply cocones.cocone_iso_of_hom_iso _,
      exact is_iso.id _ },
  end } }

/-- putting all the above together, we deduce that `X ↦ (I → X)` preserves filtered limits for
finite `I`. it might have been easier to prove this directly. -/
instance coyoneda_preserves_filtered_colimit : preserves_colimits_of_shape J
  (coyoneda.obj (opposite.op I)) :=
preserves_colimits_of_shape_of_nat_iso (key_nat_iso I).symm

variable (F : J ⥤ Type)
variables {I J}

/-- now we just transfer some of the `colimit` api to `Type` lingo -/
def cl : Type := colimit F

def cl_desc (c : cocone F) : cl F → c.X := colimit.desc F _

def cl_ι (j : J) (x : F.obj j) : cl F := colimit.ι F j x

@[ext] lemma ext_fun (X : Type) (f f' : cl F → X)
  (h : ∀ j (x : F.obj j), f (cl_ι F j x) = f' (cl_ι F j x)) : f = f' :=
begin
  let g : colimit F ⟶ X := f,
  let g' : colimit F ⟶ X := f',
  suffices : g = g',
  { convert this },
  apply colimit.hom_ext,
  intro j,
  ext x,
  exact h j x,
end

/-- the bijection `(colimit F)^I ≃ colimit F^I` induced by preservation of colimits -/
def cl_equiv : (I → cl F) ≃ cl (F ⋙ coyoneda.obj (opposite.op I)) :=
iso.to_equiv $ preserves_colimit_iso (coyoneda.obj $ opposite.op I) F

/-- the above bijection is a morphism of cocones -/
lemma cl_equiv_comm (j : J) (v : I → F.obj j) :
cl_equiv F (cl_ι F j ∘ v) = cl_ι (F ⋙ coyoneda.obj (opposite.op I)) j v
 :=
begin
  delta cl_ι,
  have := ι_preserves_colimits_iso_hom (coyoneda.obj $ opposite.op I) F j,
  rw ←this,
  refl,
end
