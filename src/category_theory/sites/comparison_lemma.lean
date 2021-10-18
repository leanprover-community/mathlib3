
import category_theory.sites.dense_subsite
import category_theory.sites.cover_lifting
import category_theory.adjunction.fully_faithful


namespace category_theory

universes v u

section
open limits
open opposite
open presieve
variables {C D : Type u} [category.{u} C] [category.{u} D] {G : C ⥤ D} [full G]
variables {J : grothendieck_topology C} {K : grothendieck_topology D}
variables {A : Type v} [category.{u} A]
variables (H : cover_dense K G)

-- variables (A) [faithful G]

-- noncomputable
-- instance sites.pullback.full :
--   full (sites.pullback A (compatible_preserving_of_dense_and_cover_preserving H H') H') :=
-- { preimage := λ ℱ ℱ' α, sheaf_hom H H' α,
--   witness' := λ ℱ ℱ' α, (sheaf_hom_restrict_eq H H' α).symm }

-- instance sites.pullback.faithful :
--   faithful (sites.pullback A (compatible_preserving_of_dense_and_cover_preserving H H') H') :=
-- { map_injective' := λ ℱ ℱ' α β (eq : whisker_left G.op α = whisker_left G.op β),
--   by rw [sheaf_hom_eq H H' α, sheaf_hom_eq H H' β, eq] }

-- variables {A} [has_limits A] (H'' : cover_lifting J K G)

-- @[simp] noncomputable
-- def counit_inverse_app_app (ℱ : Sheaf J A) (U) :
--   ℱ.val.obj (op U) ⟶ limit (Ran.diagram G.op ℱ.val (op (G.obj U))) :=
-- begin
--   refine limit.lift _ { X := _, π := { app := _, naturality' := _ } },
--   { intro X,
--     apply (ℱ.property (ℱ.val.obj (op U)) _ (H.map' X.hom.unop).property).amalgamate
--       (λ Y g hg, ℱ.val.map (H.map_fac_map' X.hom.unop hg).op),
--     rintros Z₁ Z₂ W g₁ g₂ f₁' f₂' H₁ H₂ eq,
--     change ℱ.val.map _ ≫ ℱ.val.map _ = ℱ.val.map _ ≫ ℱ.val.map _,
--     rw [←ℱ.val.map_comp, ←ℱ.val.map_comp, ←op_comp, ←op_comp],
--     congr' 2,
--     apply G.map_injective,
--     simpa[H.map_fac' X.hom.unop] using congr_arg (λ x, G.map x ≫ X.hom.unop) eq
--     },
--   intros X Y f, erw category.id_comp,
--   generalize_proofs hℱY _ hℱX _,
--   apply hℱY.is_separated_for,
--   apply presieve.is_sheaf_for.is_amalgamation,
--   intros Z g hg,
--   simp only [functor.comp_map, coyoneda_obj_map, structured_arrow.proj_map, category.assoc],
--   erw ← ℱ.val.map_comp,
--   have : H.map' X.hom.unop (g ≫ quiver.hom.unop f.right),
--   { use H.map_fac_map' _ hg,
--     rw [H.map_fac' _ hg, (category.id_comp Y.hom).symm.trans f.w],
--     simp },
--   refine (hℱX.valid_glue _ (g ≫ f.right.unop) this).trans _,
--   congr' 2,
--   apply G.map_injective,
--   rw [H.map_fac' X.hom.unop, H.map_fac' Y.hom.unop, (category.id_comp Y.hom).symm.trans f.w],
--   simp
-- end

-- lemma counit_inverse_app_app_left (ℱ : Sheaf J A) (U) :
--   limit.π (Ran.diagram G.op ℱ.val (G.op.obj (op U))) (mk (𝟙 (G.op.obj (op U)))) ≫
--     counit_inverse_app_app H H' ℱ U = 𝟙 _ :=
-- begin
--   ext,
--   simp only [category.id_comp, category.assoc],
--   erw limit.lift_π,
--   dsimp only,
--   generalize_proofs _ hℱ hx,
--   apply (ℱ.property (limit _) _ (H.map' j.hom.unop).property).is_separated_for.ext,
--   intros Y f hf,
--   simp only [functor.comp_map, coyoneda_obj_map, category.assoc],
--   erw (show _ ≫ ℱ.val.map f.op = _ , from hℱ.valid_glue hx f hf),
--   let k := mk (G.op.map (H.map_fac_map' j.hom.unop hf).op),
--   let f₁ : mk (𝟙 _) ⟶ k := hom_mk (H.map_fac_map' _ hf).op (by exact category.id_comp _),
--   let f₂ : j ⟶ k := hom_mk f.op (by simp[H.map_fac' j.hom.unop hf]),
--   exact ((limit.cone (Ran.diagram G.op ℱ.val (op (G.obj U)))).π.naturality f₁).symm.trans
--         ((limit.cone (Ran.diagram G.op ℱ.val (op (G.obj U)))).π.naturality f₂),
-- end

-- lemma counit_inverse_app_app_right (ℱ : Sheaf J A) (U) :
--   counit_inverse_app_app H H' ℱ U ≫
--     limit.π (Ran.diagram G.op ℱ.val (G.op.obj (op U))) (mk (𝟙 (G.op.obj (op U)))) = 𝟙 _ :=
-- begin
--   erw limit.lift_π,
--   dsimp only,
--   generalize_proofs hℱ hx,
--   apply hℱ.is_separated_for,
--   apply is_sheaf_for.is_amalgamation,
--   intros Y f hf,
--   change 𝟙 _ ≫ _ = _,
--   erw category.id_comp,
--   congr,
--   apply G.map_injective,
--   rw H.map_fac' _ hf,
--   erw category.comp_id
-- end

-- lemma counit_app_is_iso (ℱ : Sheaf J A) : is_iso ((Ran.adjunction A G.op).counit.app ℱ.val) :=
-- begin
--   haveI : ∀ (U), is_iso (((Ran.adjunction A G.op).counit.app ℱ.val).app U),
--   { intro U, dsimp,
--     simp only [Ran.adjunction, adjunction.adjunction_of_equiv_right_counit_app,
--       equiv.symm_symm, Ran.equiv_apply_app, nat_trans.id_app],
--       erw category.id_comp,
--       use counit_inverse_app_app H H' ℱ (unop U),
--       split,
--       exact counit_inverse_app_app_left H H' ℱ (unop U),
--       apply counit_inverse_app_app_right },
-- apply nat_iso.is_iso_of_is_iso_app,
-- end

-- include H''


-- -- (Ran.adjunction A G.op)
-- variable (A)

-- @[simps] noncomputable
-- def adjunction :
--   sites.pullback A (compatible_preserving_of_dense_and_cover_preserving H H') H' ⊣
--   sites.copullback A H'' :=
-- { hom_equiv := λ X Y, (Ran.adjunction A G.op).hom_equiv X.val Y.val,
--   unit := { app := λ X, (Ran.adjunction A G.op).unit.app X.val,
--     naturality' := λ _ _ f, (Ran.adjunction A G.op).unit.naturality f },
--   counit := { app := λ X, (Ran.adjunction A G.op).counit.app X.val,
--     naturality' := λ _ _ f, (Ran.adjunction A G.op).counit.naturality f },
--   hom_equiv_unit' := λ X Y f, (Ran.adjunction A G.op).hom_equiv_unit,
--   hom_equiv_counit' := λ X Y f, (Ran.adjunction A G.op).hom_equiv_counit }


-- lemma adjunction_counit_is_iso : is_iso (adjunction A H H' H'').counit :=
-- begin
--   haveI : ∀ (X : Sheaf J A), is_iso ((adjunction A H H' H'').counit.app X),
--   { intro ℱ,
--     obtain ⟨f, h₂, h₃⟩ := counit_app_is_iso H H' ℱ,
--     use ⟨f, h₂, h₃⟩ },
--   apply nat_iso.is_iso_of_is_iso_app,
-- end

-- -- set_option trace.class_instances true

-- lemma adjunction_unit_is_iso : is_iso (adjunction A H H' H'').unit :=
-- begin
--   haveI : ∀ (X : Sheaf K A), is_iso ((adjunction A H H' H'').unit.app X),
--   { intro ℱ,
--     rw ←is_iso_iff_is_presheaf_iso,
--     apply iso_of_restrict_iso H H',
--     let α := (adjunction A H H' H'').counit.app ((sites.pullback A _ H').obj ℱ),
--     haveI := adjunction_counit_is_iso A H H' H'',
--     have : inv α = (whisker_left G.op ((adjunction A H H' H'').unit.app ℱ) : G.op ⋙ ℱ.val ⟶ _),
--     { symmetry,
--       apply (comp_hom_eq_id α).mp,
--       erw (adjunction A H H' H'').left_triangle_components,
--       refl },
--     rw ← this,
--     rw is_iso_iff_is_presheaf_iso,
--     apply_instance },
-- apply nat_iso.is_iso_of_is_iso_app,
-- end

-- noncomputable
-- def Sheaf_iso_Sheaf_of_dense_subsite : Sheaf K A ≌ Sheaf J A :=
-- begin
--   haveI := adjunction_unit_is_iso A H H' H'',
--   haveI := adjunction_counit_is_iso A H H' H'',
-- exact { unit_iso := as_iso (adjunction A H H' H'').unit,
--   counit_iso := as_iso (adjunction A H H' H'').counit,
--   inverse := sites.copullback A H'',
--   functor := sites.pullback A (compatible_preserving_of_dense_and_cover_preserving H H') H',
--   functor_unit_iso_comp' := λ ℱ, by convert (adjunction A H H' H'').left_triangle_components }
-- end

-- end comparison_lemma
-- end
end category_theory
