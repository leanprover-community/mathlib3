import algebraic_geometry.locally_ringed_space
import algebra.category.CommRing.constructions
import algebraic_geometry.open_immersion
import category_theory.limits.constructions.limits_of_products_and_equalizers

namespace algebraic_geometry

universes v u


open category_theory category_theory.limits opposite

namespace SheafedSpace

variables {C : Type u} [category.{v} C] [has_limits C]
variables {ι : Type v} (F : discrete ι ⥤ SheafedSpace C)

lemma sigma_ι_jointly_surjective (x : colimit F) :
  ∃ (i : ι) (y : F.obj i), (colimit.ι F i).base y = x :=
begin
  let e : (colimit F).carrier ≅ _ :=
    preserves_colimit_iso (SheafedSpace.forget _) _ ≪≫
      colim.map_iso discrete.nat_iso_functor ≪≫ Top.sigma_iso_sigma _,
  refine ⟨(e.hom x).1, (e.hom x).2, _⟩,
  apply (Top.mono_iff_injective e.hom).mp infer_instance,
  generalize : e.hom x = y,
  rw ← Top.comp_app,
  erw [ι_preserves_colimits_iso_hom_assoc (SheafedSpace.forget _), colimit.ι_map_assoc,
    Top.sigma_iso_sigma_hom_ι_apply],
  cases y,
  refl
end

instance {X Y : SheafedSpace C} (f g : X ⟶ Y) : epi (coequalizer.π f g).base :=
begin
  erw ← (show _ = (coequalizer.π f g).base, from
    ι_comp_coequalizer_comparison f g (SheafedSpace.forget C)),
  rw ← preserves_coequalizer.iso_hom,
  apply epi_comp
end

end SheafedSpace

namespace LocallyRingedSpace

section has_coproducts

variables {ι : Type u} (F : discrete ι ⥤ LocallyRingedSpace.{u})

noncomputable
def coproduct : LocallyRingedSpace :=
{ to_SheafedSpace := colimit (F ⋙ forget_to_SheafedSpace : _),
  local_ring := λ x, begin
    rcases SheafedSpace.sigma_ι_jointly_surjective (F ⋙ forget_to_SheafedSpace) x with ⟨i, y, ⟨⟩⟩,
    haveI : _root_.local_ring (((F ⋙ forget_to_SheafedSpace).obj i).to_PresheafedSpace.stalk y) :=
      (F.obj i).local_ring _,
    exact (as_iso (PresheafedSpace.stalk_map (colimit.ι (F ⋙ forget_to_SheafedSpace) i : _) y)
      ).symm.CommRing_iso_to_ring_equiv.local_ring
  end }

noncomputable
def coproduct_cofan : cocone F :=
{ X := coproduct F,
  ι := { app := λ j, ⟨colimit.ι (F ⋙ forget_to_SheafedSpace) j, infer_instance⟩ } }

section end

noncomputable
lemma coproduct_cofan_is_colimit : is_colimit (coproduct_cofan F) :=
{ desc := λ s, ⟨colimit.desc (F ⋙ forget_to_SheafedSpace) (forget_to_SheafedSpace.map_cocone s),
  begin
    intro x,
    rcases SheafedSpace.sigma_ι_jointly_surjective (F ⋙ forget_to_SheafedSpace) x with ⟨i, y, ⟨⟩⟩,
    have := PresheafedSpace.stalk_map.comp (colimit.ι (F ⋙ forget_to_SheafedSpace) i : _)
      (colimit.desc (F ⋙ forget_to_SheafedSpace) (forget_to_SheafedSpace.map_cocone s)) y,
    rw ← is_iso.comp_inv_eq at this,
    erw ← this,
    erw PresheafedSpace.stalk_map.congr_hom _ _
      (colimit.ι_desc (forget_to_SheafedSpace.map_cocone s) i : _),
    haveI : is_local_ring_hom (PresheafedSpace.stalk_map
      ((forget_to_SheafedSpace.map_cocone s).ι.app i) y) := (s.ι.app i).2 y,
    apply_instance
  end⟩,
  fac' := λ s j, subtype.eq (colimit.ι_desc _ _),
  uniq' := λ s f h, subtype.eq (is_colimit.uniq _ (forget_to_SheafedSpace.map_cocone s) f.1
    (λ j, congr_arg subtype.val (h j))) }


instance : has_coproducts LocallyRingedSpace.{u} :=
λ ι, ⟨λ F, ⟨⟨⟨_, coproduct_cofan_is_colimit F⟩⟩⟩⟩

noncomputable
instance (J : Type*) : preserves_colimits_of_shape (discrete J) forget_to_SheafedSpace :=
⟨λ G, preserves_colimit_of_preserves_colimit_cocone (coproduct_cofan_is_colimit G)
  ((colimit.is_colimit _).of_iso_colimit (cocones.ext (iso.refl _) (λ j, category.comp_id _)))⟩

end has_coproducts

section has_coequalizer

variables {X Y : LocallyRingedSpace.{u}} (f g : X ⟶ Y)

instance coequalizer_π_app_is_local_ring_hom
  (U : topological_space.opens ((coequalizer f.val g.val).carrier)) :
  is_local_ring_hom ((coequalizer.π f.val g.val : _).c.app (op U)) :=
begin
  have := ι_comp_coequalizer_comparison f.1 g.1 SheafedSpace.forget_to_PresheafedSpace,
  rw ← preserves_coequalizer.iso_hom at this,
  erw PresheafedSpace.congr_app this.symm (op U),
  rw PresheafedSpace.comp_c_app,
  rw ← PresheafedSpace.colimit_presheaf_obj_iso_componentwise_limit_hom_π,
  apply_instance
end

lemma _root_.category_theory.limits.types.preimage_image_eq_of_preimage_eq {X Y Z : Type*} (f g : X ⟶ Y) (π : Y ⟶ Z)
  (e : f ≫ π = g ≫ π) (h : is_colimit (cofork.of_π π e)) (U : set Y) (H : f ⁻¹' U = g ⁻¹' U) :
    π ⁻¹' (π '' U) = U :=
begin
  have lem : ∀ x y, (types.coequalizer_rel f g x y) → (x ∈ U ↔ y ∈ U),
  { rintros _ _ ⟨x⟩, change x ∈ f ⁻¹' U ↔ x ∈ g ⁻¹' U, congr' 2 },
  have eqv : _root_.equivalence (λ x y, x ∈ U ↔ y ∈ U) := by tidy,
  ext,
  split,
  { rw ← (show _ = π, from h.comp_cocone_point_unique_up_to_iso_inv
      (types.coequalizer_colimit f g).2 walking_parallel_pair.one),
    rintro ⟨y, hy, e'⟩,
    dsimp at e',
    replace e' := (mono_iff_injective (h.cocone_point_unique_up_to_iso
      (types.coequalizer_colimit f g).is_colimit).inv).mp infer_instance e',
    exact (eqv.eqv_gen_iff.mp (eqv_gen.mono lem (quot.exact _ e'))).mp hy },
  { exact λ hx, ⟨x, hx, rfl⟩ }
end

@[instance]
lemma coequalizer_π_stalk_is_local_ring_hom (x : Y) :
  is_local_ring_hom (PresheafedSpace.stalk_map (coequalizer.π f.val g.val : _) x) :=
begin
  constructor,
  rintros a ha,
  rcases Top.presheaf.germ_exist _ _ a with ⟨U, hU, s, rfl⟩,
  erw PresheafedSpace.stalk_map_germ_apply (coequalizer.π f.1 g.1 : _) U ⟨_, hU⟩ at ha,

  let V : topological_space.opens Y := (Y.to_RingedSpace.basic_open
    (show Y.presheaf.obj (op (unop _)), from ((coequalizer.π f.1 g.1).c.app (op U)) s)),
  have hV : (coequalizer.π f.1 g.1).base ⁻¹' ((coequalizer.π f.1 g.1).base '' V.1) = V.1,
  { fapply category_theory.limits.types.preimage_image_eq_of_preimage_eq f.1.base g.1.base,
    { ext,
      simp_rw [types_comp_apply, ← Top.comp_app, ← PresheafedSpace.comp_base],
      congr' 2,
      exact coequalizer.condition f.1 g.1 },
    { apply is_colimit_cofork_map_of_is_colimit (forget Top),
      apply is_colimit_cofork_map_of_is_colimit (SheafedSpace.forget _),
      exact coequalizer_is_coequalizer f.1 g.1 },
    { suffices : (topological_space.opens.map f.1.base).obj V =
        (topological_space.opens.map g.1.base).obj V,
      { injection this },
      rw preimage_basic_open f,
      rw preimage_basic_open g,
      dsimp only,
      rw ← comp_apply,
      erw ← PresheafedSpace.comp_c_app,
      rw ← comp_apply,
      erw ← PresheafedSpace.comp_c_app,
      erw PresheafedSpace.congr_app (coequalizer.condition f.1 g.1 : _) (op U),
      rw comp_apply,
      erw X.to_RingedSpace.basic_open_res,
      erw inf_eq_right,
      refine (RingedSpace.basic_open_subset _ _).trans _,
      dsimp only [functor.op, unop_op],
      rw coequalizer.condition f.1 g.1,
      exact λ _ h, h } },

  have hV' : V = ⟨(coequalizer.π f.1 g.1).base ⁻¹'
    ((coequalizer.π f.1 g.1).base '' V.1), hV.symm ▸ V.2⟩ := subtype.eq hV.symm,

  have V_open : is_open (((coequalizer.π f.val g.val).base) '' V.val),
  { rw ← (Top.homeo_of_iso (preserves_coequalizer.iso (SheafedSpace.forget _) f.1 g.1))
      .is_open_preimage,
    rw [Top.coequalizer_is_open_iff, ← set.preimage_comp], erw ← coe_comp,
    rw [preserves_coequalizer.iso_hom, ι_comp_coequalizer_comparison],
    erw hV,
    exact V.2 },
  have VleU :
    (⟨((coequalizer.π f.val g.val).base) '' V.val, V_open⟩ : topological_space.opens _) ≤ U,
  { exact set.image_subset_iff.mpr (Y.to_RingedSpace.basic_open_subset _) },
  have hxV : x ∈ V := ⟨⟨_, hU⟩, ha, rfl⟩,
  erw ← (coequalizer f.val g.val).presheaf.germ_res_apply (hom_of_le VleU)
    ⟨_, @set.mem_image_of_mem _ _ (coequalizer.π f.val g.val).base x V.1 hxV⟩ s,

  apply ring_hom.is_unit_map,
  rw [← is_unit_map_iff ((coequalizer.π f.val g.val : _).c.app _), ← comp_apply,
    nat_trans.naturality, comp_apply],
  rw Top.presheaf.pushforward_obj_map,
  rw ← is_unit_map_iff (Y.presheaf.map (eq_to_hom hV').op),
  rw ← comp_apply,
  rw ← functor.map_comp,
  convert @RingedSpace.is_unit_res_basic_open Y.to_RingedSpace (unop _)
    (((coequalizer.π f.val g.val).c.app (op U)) s),
  apply_instance
end

section end

lemma local_ring_hom_pre {R S : Type*} [comm_ring R] [comm_ring S] [H : _root_.local_ring S]
  (f : R →+* S)
  [is_local_ring_hom f] : _root_.local_ring R :=
begin
  haveI : nontrivial R := pullback_nonzero f f.map_zero f.map_one,
  constructor,
  intro x,
  rw [← is_unit_map_iff f, ← is_unit_map_iff f, f.map_sub, f.map_one],
  exact _root_.local_ring.is_local (f x)
end

lemma is_local_ring_hom_of_comp {R S T: Type*} [comm_ring R] [comm_ring S] [comm_ring T]
  (f : R →+* S) (g : S →+* T) [is_local_ring_hom g] [is_local_ring_hom (g.comp f)] :
    is_local_ring_hom f :=
⟨λ a ha, (is_unit_map_iff (g.comp f) _).mp (g.is_unit_map ha)⟩

noncomputable
def coequalizer : LocallyRingedSpace :=
{ to_SheafedSpace := coequalizer f.1 g.1,
  local_ring := λ x,
  begin
    rcases (Top.epi_iff_surjective (coequalizer.π f.val g.val).base).mp
        infer_instance x with ⟨y, rfl⟩,
    exact local_ring_hom_pre (PresheafedSpace.stalk_map (coequalizer.π f.val g.val : _) y)
  end }

noncomputable
def coequalizer_cofork : cofork f g :=
@cofork.of_π _ _ _ _ f g (coequalizer f g) ⟨coequalizer.π f.1 g.1, infer_instance⟩
  (subtype.eq (coequalizer.condition f.1 g.1))

section end

lemma is_local_ring_hom_stalk_map_congr {X Y : RingedSpace} (f g : X ⟶ Y) (H : f = g)
  (x) : is_local_ring_hom (PresheafedSpace.stalk_map f x) →
    is_local_ring_hom (PresheafedSpace.stalk_map g x) :=
begin
  intro h,
  resetI,
  rw PresheafedSpace.stalk_map.congr_hom _ _ H.symm x,
  apply_instance
end

noncomputable
lemma coequalizer_cofork_is_colimit : is_colimit (coequalizer_cofork f g) :=
begin
  apply cofork.is_colimit.mk',
  intro s,
  have e : f.val ≫ s.π.val = g.val ≫ s.π.val := by injection s.condition,
  use coequalizer.desc s.π.1 e,
  { intro x,
    rcases (Top.epi_iff_surjective (coequalizer.π f.val g.val).base).mp
      infer_instance x with ⟨y, rfl⟩,
    apply is_local_ring_hom_of_comp _ (PresheafedSpace.stalk_map (coequalizer_cofork f g).π.1 _),
    apply_instance,
    change is_local_ring_hom (_ ≫ PresheafedSpace.stalk_map (coequalizer_cofork f g).π.val y),
    erw ← PresheafedSpace.stalk_map.comp,
    apply is_local_ring_hom_stalk_map_congr _ _ (coequalizer.π_desc s.π.1 e).symm y,
    apply_instance },
  split,
  exact subtype.eq (coequalizer.π_desc _ _),
  intros m h,
  replace h : (coequalizer_cofork f g).π.1 ≫ m.1 = s.π.1 := by { rw ← h, refl },
  apply subtype.eq,
  apply (colimit.is_colimit (parallel_pair f.1 g.1)).uniq (cofork.of_π s.π.1 e) m.1,
  rintro ⟨⟩,
  { rw [← (colimit.cocone (parallel_pair f.val g.val)).w walking_parallel_pair_hom.left,
      category.assoc],
    change _ ≫ _ ≫ _ = _ ≫ _,
    congr,
    exact h },
  { exact h }
end

section end

instance : has_coequalizer f g := ⟨⟨⟨_, coequalizer_cofork_is_colimit f g⟩⟩⟩

instance : has_coequalizers LocallyRingedSpace := has_coequalizers_of_has_colimit_parallel_pair _

noncomputable
instance perserves_coequalizer :
  preserves_colimits_of_shape walking_parallel_pair forget_to_SheafedSpace :=
⟨λ F, begin
  apply preserves_colimit_of_iso_diagram _ (diagram_iso_parallel_pair F).symm,
  apply preserves_colimit_of_preserves_colimit_cocone (coequalizer_cofork_is_colimit _ _),
  apply (is_colimit_map_cocone_cofork_equiv _ _).symm _,
  dsimp only [forget_to_SheafedSpace],
  exact coequalizer_is_coequalizer _ _
end⟩

end has_coequalizer

instance : has_colimits LocallyRingedSpace := colimits_from_coequalizers_and_coproducts

noncomputable
instance : preserves_colimits LocallyRingedSpace.forget_to_SheafedSpace :=
preserves_colimits_of_preserves_coequalizers_and_coproducts _

end LocallyRingedSpace

end algebraic_geometry
