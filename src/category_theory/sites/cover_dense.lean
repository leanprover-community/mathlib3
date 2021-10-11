import category_theory.sites.sheaf
import category_theory.flat_functors

universes v u

namespace category_theory
section cover_dense
variables {C : Type*} [category C] {D : Type*} [category D] {E : Type*} [category E]
variables (J : grothendieck_topology C) (K : grothendieck_topology D)
variables {L : grothendieck_topology E}

structure cover_dense (J : grothendieck_topology C) (K : grothendieck_topology D) (G : C ⥤ D) :=
(obj          : ∀ (U : D), K U)
(obj_fac_obj  : ∀ {U V} {f : V ⟶ U} (hf : obj U f), C)
(obj_fac_lift : ∀ {U V} {f : V ⟶ U} (hf : obj U f), G.obj (obj_fac_obj hf) ⟶ U)
(obj_fac_map  : ∀ {U V} {f : V ⟶ U} (hf : obj U f), V ⟶ G.obj (obj_fac_obj hf))
(obj_fac      : ∀ {U V} {f : V ⟶ U} (hf : obj U f), (obj_fac_map hf) ≫ (obj_fac_lift hf) = f)
(map          : ∀ {U V : C} (f : G.obj U ⟶ G.obj V), J U)
(map_fac_map  : ∀ {U V W} (f : G.obj U ⟶ G.obj V) {g : W ⟶ U} (hg : map f g), W ⟶ V)
(map_fac      : ∀ {U V W} (f : G.obj U ⟶ G.obj V) {g : W ⟶ U} (hg : map f g),
  G.map (map_fac_map f hg) = G.map g ≫ f)

attribute [simp] cover_dense.map_fac cover_dense.obj_fac


def cover_dense_mk_of_full (J : grothendieck_topology C) (K : grothendieck_topology D) (G : C ⥤ D)
  [full G] (create : ∀ (U : D), Σ (S : K U), ∀ {V : D} {f : V ⟶ U} (hf : S f),
    Σ' (W : C) (g : G.obj W ⟶ U) (h : V ⟶ G.obj W) , h ≫ g = f) : cover_dense J K G :=
{ obj := λ U, (create U).1,
  obj_fac_obj  := λ U V f hf, ((create U).2 hf).1,
  obj_fac_lift := λ U V f hf, ((create U).2 hf).2.1,
  obj_fac_map  := λ U V f hf, ((create U).2 hf).2.2.1,
  obj_fac      := λ U V f hf, ((create U).2 hf).2.2.2,
  map          := λ U V f, ⟨_, J.top_mem U⟩,
  map_fac_map  := λ U V W f g hg, g ≫ G.preimage f,
  map_fac      := λ U V W f g hg, by simp }

end cover_dense

section
open limits
open opposite
open presieve
variables {C D : Type u} [category.{u} C] [category.{u} D] (G : C ⥤ D)
variables {J : grothendieck_topology C} {K : grothendieck_topology D}
variables {A : Type v} [category.{u} A]

def family_of_elements.of_element {X : C} (P : Cᵒᵖ ⥤ Type u) (R : presieve X) (x : P.obj (op X)) :
  family_of_elements P R := λ Y f _, P.map f.op x

@[simp] lemma family_of_elements.of_element_apply {X : C} (P : Cᵒᵖ ⥤ Type u) (R : presieve X)
  (x : P.obj (op X)) {Y} {f : Y ⟶ X} (hf) :
  family_of_elements.of_element P R x f hf = P.map f.op x := rfl

def family_of_elements.of_element_compatible {X : C} (P : Cᵒᵖ ⥤ Type u) (R : presieve X)
  (x : P.obj (op X)) : (family_of_elements.of_element P R x).compatible :=
begin
  intros Z₁ Z₂ Y g₁ g₂ f₁ f₂ h₁ h₂ eq,
  simp only [family_of_elements.of_element_apply,
    ←types_comp_apply (P.map _) (P.map _), ←P.map_comp, ←op_comp, eq],
end

lemma lem [representably_flat G] (H : cover_dense J K G) (ℱ ℱ' : SheafOfTypes K) (eq : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) :
  ℱ.val ≅ ℱ'.val :=
begin
fapply nat_iso.of_components,
intro X,
refine { hom := _, inv := _, hom_inv_id' := _, inv_hom_id' := _ },
intro x,
let x' : family_of_elements ℱ'.val (H.obj (unop X)) := λ Y f hf,
  (ℱ.val.map (H.obj_fac_lift hf).op ≫
      (eq.app (op (H.obj_fac_obj hf))).hom ≫ ℱ'.val.map (H.obj_fac_map hf).op) x,
have : x'.compatible,
{ intros Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ e, dsimp only [x'],
  refine congr_fun _ x,
  change ℱ.val.map _ ≫ (eq.app (op _)).hom ≫ ℱ'.val.map _ ≫ ℱ'.val.map _ =
       (ℱ.val.map _ ≫ (eq.app (op _)).hom ≫ ℱ'.val.map _) ≫ ℱ'.val.map _,
  rw [←ℱ'.val.map_comp, ←op_comp, category.assoc, category.assoc, ←ℱ'.val.map_comp, ←op_comp],
  let X₁ : structured_arrow Z G := structured_arrow.mk (g₁ ≫ H.obj_fac_map h₁),
  let X₂ : structured_arrow Z G := structured_arrow.mk (g₂ ≫ H.obj_fac_map h₂),
  let X₀ := is_cofiltered.min X₁ X₂,
  rw (category.id_comp (g₁ ≫ _)).symm.trans (comma_morphism.w (is_cofiltered.min_to_left X₁ X₂)),
  rw (category.id_comp (g₂ ≫ _)).symm.trans (comma_morphism.w (is_cofiltered.min_to_right X₁ X₂)),
  simp only [op_comp, iso.app_hom,
    structured_arrow.mk_hom_eq_self, functor.map_comp, ←category.assoc],
  congr' 1,
  simp only [category.assoc],
  have eq₁ : _ = eq.hom.app _ ≫ ℱ'.val.map (G.map _).op :=
    eq.hom.naturality (comma_morphism.right (is_cofiltered.min_to_left X₁ X₂)).op,
  have eq₂ : _ = eq.hom.app _ ≫ ℱ'.val.map (G.map _).op :=
    eq.hom.naturality (comma_morphism.right (is_cofiltered.min_to_right X₁ X₂)).op,
  erw [←eq₁, ←eq₂],
  simp only [quiver.hom.unop_op, functor.comp_map, G.op_map, ←category.assoc, ←ℱ.val.map_comp, ←op_comp],
  congr' 3,
  -- let i₁ : X₀.right ⟶ H.obj_fac_obj h₁ := comma_morphism.right (is_cofiltered.min_to_left X₁ X₂),

-- have := eq.hom.naturality (op (H.obj_fac_obj h₁)),
-- erw ←types_comp_apply (ℱ'.val.map _) (ℱ'.val.map _),

}
-- have := (family_of_elements.of_element (G.op ⋙ ℱ.val) (this.val.functor_pullback G.op) x),
-- have := ℱ.property this.val this.property (family_of_elements.of_element ℱ.val this.val x)
--   (family_of_elements.of_element_compatible ℱ.val this.val x),
end

-- @[simps]
-- def sheaf_over (ℱ : Sheaf K A) (X : A) : SheafOfTypes K :=
-- ⟨ℱ.val ⋙ coyoneda.obj (op X), ℱ.property X⟩

-- lemma lem' (H : cover_dense J K G) (ℱ ℱ' : Sheaf K A) (eq : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) :
--   ℱ.val ≅ ℱ'.val :=
-- begin
-- let oo : ∀ (X : A), ℱ.val ⋙ coyoneda.obj (op X) ≅ ℱ'.val ⋙ coyoneda.obj (op X) :=
--   λ X, lem G H (sheaf_over ℱ X) (sheaf_over ℱ' X) (iso_whisker_right eq (coyoneda.obj (op X))),
-- fapply nat_iso.of_components,
-- intro Z,
-- apply @preimage_iso _ _ _ _ yoneda,
-- fapply nat_iso.of_components,
-- intro X, dsimp,
-- exact (oo (unop X)).app Z,
-- intros X Y f,
-- ext, dsimp[oo],
-- end
end
end category_theory
