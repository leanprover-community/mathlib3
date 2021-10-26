import category_theory.sites.sheaf
import category_theory.limits.preserves.filtered

namespace category_theory.presheaf

open category_theory category_theory.limits opposite

universes v u w
variables {C : Type u} [category.{v} C] (J : grothendieck_topology C)
variables {D : Type w} [category.{max v u} D]

noncomputable theory

def first_obj_index {B : C} (R : presieve B) : Type (max v u) :=
Σ (V : C), { f : V ⟶ B // R f }

namespace first_obj_index

def map {B : C} {R S : presieve B} (h : R ≤ S) :
  first_obj_index R → first_obj_index S :=
λ F, ⟨F.1, F.2.1, h _ F.2.2⟩

def pullback {X Y : C} {R : sieve Y} (f : X ⟶ Y) :
  first_obj_index (R.pullback f) → first_obj_index R :=
λ F, ⟨F.1, F.2.1 ≫ f, F.2.2⟩

end first_obj_index

structure second_obj_index {B : C} (R : presieve B) : Type (max v u) :=
(Y₁ Y₂ Z : C)
(g₁ : Z ⟶ Y₁)
(g₂ : Z ⟶ Y₂)
(f₁ : Y₁ ⟶ B)
(f₂ : Y₂ ⟶ B)
(h₁ : R f₁)
(h₂ : R f₂)
(w : g₁ ≫ f₁ = g₂ ≫ f₂)

namespace second_obj_index

def map {B : C} {R S : presieve B} (h : R ≤ S) :
  second_obj_index R → second_obj_index S :=
λ F, ⟨F.Y₁, F.Y₂, F.Z, F.g₁, F.g₂, F.f₁, F.f₂, h _ F.h₁, h _ F.h₂, F.w⟩

def pullback {X Y : C} {R : sieve Y} (f : X ⟶ Y) :
  second_obj_index (R.pullback f) → second_obj_index R :=
λ F, ⟨F.Y₁, F.Y₂, F.Z, F.g₁, F.g₂, F.f₁ ≫ f, F.f₂ ≫ f, F.h₁, F.h₂, by simp [reassoc_of F.w]⟩

end second_obj_index

def second_obj' [has_products D] {B : C} (R : presieve B) (P : Cᵒᵖ ⥤ D) : D :=
∏ (λ I : second_obj_index R, P.obj (op I.Z))

def first_map' [has_products D] {B : C} (R : presieve B) (P : Cᵒᵖ ⥤ D) :
  first_obj R P ⟶ second_obj' R P :=
pi.lift (λ I, pi.π _ ⟨_,_,I.h₁⟩ ≫ P.map I.g₁.op)

def second_map' [has_products D] {B : C} (R : presieve B) (P : Cᵒᵖ ⥤ D) :
  first_obj R P ⟶ second_obj' R P :=
pi.lift (λ I, pi.π _ ⟨_,_,I.h₂⟩ ≫ P.map I.g₂.op )

def matching [has_limits D] {B : C} (R : presieve B) (P : Cᵒᵖ ⥤ D) : D :=
  equalizer (first_map'.{v u} R P) (second_map'.{v u} R P)

def matching.map [has_limits D] {B : C} {R S : presieve B} (h : R ≤ S) (P : Cᵒᵖ ⥤ D) :
  matching S P ⟶ matching R P :=
equalizer.lift (equalizer.ι _ _ ≫
  pi.lift (λ (F : first_obj_index R), pi.π _ (first_obj_index.map h F)))
begin
  ext (I : second_obj_index R),
  change _ ≫ pi.π _ _ = _ ≫ pi.π _ _,
  have := equalizer.condition (first_map' S P) (second_map' S P),
  apply_fun (λ e, e ≫ pi.π _ (second_obj_index.map h I)) at this,
  convert this using 1,
  { dsimp [first_map'],
    simp only [limit.lift_π, limit.lift_π_assoc, fan.mk_π_app, category.assoc],
    congr },
  { dsimp [second_map'],
    simp only [limit.lift_π, limit.lift_π_assoc, fan.mk_π_app, category.assoc],
    congr }
end .

@[simp]
lemma matching.map_id [has_limits D] {B : C} {R : presieve B} (P : Cᵒᵖ ⥤ D) :
  matching.map (le_refl R) P = 𝟙 _ :=
begin
  ext ⟨X,f,hf⟩,
  dsimp [matching.map],
  simpa,
end

@[simp]
lemma matching.map_comp [has_limits D] {B : C} {R S T : presieve B} (P : Cᵒᵖ ⥤ D)
  (h₁ : R ≤ S) (h₂ : S ≤ T) : matching.map (le_trans h₁ h₂) P =
  matching.map h₂ P ≫ matching.map h₁ P :=
begin
  ext ⟨X,f,hf⟩,
  dsimp [matching.map],
  simpa,
end

def matching.pullback [has_limits D] {X Y : C} (R : sieve Y) (f : X ⟶ Y) (P : Cᵒᵖ ⥤ D) :
  matching R P ⟶ matching (R.pullback f) P :=
equalizer.lift (pi.lift $ λ (F : first_obj_index (R.pullback f)),
  equalizer.ι _ _ ≫ pi.π _ (first_obj_index.pullback f F))
begin
  ext (I : second_obj_index _),
  change _ ≫ pi.π _ _ = _ ≫ pi.π _ _,
  have := equalizer.condition (first_map' R P) (second_map' R P),
  apply_fun (λ e, e ≫ pi.π _ (second_obj_index.pullback f I)) at this,
  convert this using 1,
  { dsimp [first_map'],
    simp only [limit.lift_π, limit.lift_π_assoc, fan.mk_π_app, category.assoc],
    congr },
  { dsimp [second_map'],
    simp only [limit.lift_π, limit.lift_π_assoc, fan.mk_π_app, category.assoc],
    congr },
end

@[simp, reassoc]
lemma matching.map_pullback [has_limits D] {X Y : C} {R S : sieve Y} (h : R ≤ S) (f : X ⟶ Y)
  (P : Cᵒᵖ ⥤ D) :
  matching.map h P ≫ matching.pullback R f P = matching.pullback S f P ≫
    matching.map (sieve.pullback_monotone _ h) P :=
begin
  dsimp [matching.map, matching.pullback],
  ext,
  simp only [fan.mk_π_app, limit.lift_π, category.assoc,
    equalizer.lift_ι_assoc, equalizer.lift_ι],
  erw [equalizer.lift_ι_assoc, category.assoc, limits.limit.lift_π],
  simpa,
end

@[derive preorder]
def matching_diagram_index (B : C) : Type (max v u) :=
{ R : sieve B // R ∈ J B }

def matching_diagram_index.pullback {X Y : C} (f : X ⟶ Y) :
  matching_diagram_index J Y ⥤ matching_diagram_index J X :=
{ obj := λ I, ⟨I.val.pullback f, J.pullback_stable _ I.prop⟩,
  map := λ I₁ I₂ e, hom_of_le $ sieve.pullback_monotone _ (le_of_hom e) }

def matching_diagram_index.pullback_id (X : C) :
  matching_diagram_index.pullback J (𝟙 X) ≅ 𝟭 _ :=
nat_iso.of_components
(λ I, eq_to_iso begin
  cases I with I hI,
  dsimp,
  ext Y g,
  dsimp [matching_diagram_index.pullback],
  rw category.comp_id,
end) $ by tidy

def matching_diagram_index.pullback_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  matching_diagram_index.pullback J (f ≫ g) ≅
  matching_diagram_index.pullback J g ⋙ matching_diagram_index.pullback J f :=
nat_iso.of_components
(λ I, eq_to_iso begin
  cases I with I hI,
  dsimp,
  ext Y g,
  dsimp [matching_diagram_index.pullback],
  rw category.assoc,
end) $ by tidy

def matching_diagram [has_limits D] (B : C) (P : Cᵒᵖ ⥤ D) : (matching_diagram_index J B)ᵒᵖ ⥤ D :=
{ obj := λ R, matching R.unop.val P,
  map := λ R S h, matching.map (le_of_hom h.unop) P,
  map_comp' := λ X Y Z f g, matching.map_comp _ _ _ }

def matching_diagram.pullback [has_limits D] {X Y : C} (f : X ⟶ Y) (P : Cᵒᵖ ⥤ D) :
  matching_diagram J Y P ⟶ (matching_diagram_index.pullback J f).op ⋙ matching_diagram J X P :=
{ app := λ I, matching.pullback _ f _,
  naturality' := λ I J e, matching.map_pullback _ _ _ }

@[simp]
lemma matching_diagram.pullback_comp_app [has_limits D] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  (P : Cᵒᵖ ⥤ D) (I : (matching_diagram_index J Z)ᵒᵖ) :
  (matching_diagram.pullback J (f ≫ g) P).app I ≫ (matching_diagram J _ P).map
    ((nat_iso.op (matching_diagram_index.pullback_comp J f g)).app I).inv =
  (matching_diagram.pullback J g P).app I ≫
    (matching_diagram.pullback J f P).app ((matching_diagram_index.pullback J g).op.obj I) :=
begin
  ext ⟨j,ff,hff⟩,
  dsimp [matching_diagram.pullback, matching_diagram, matching.pullback,
    matching.map],
  simp,
  erw [equalizer.lift_ι_assoc, limit.lift_π],
  erw [equalizer.lift_ι_assoc, limit.lift_π],
  dsimp,
  erw [equalizer.lift_ι_assoc, limit.lift_π],
  dsimp [first_obj_index.pullback, first_obj_index.map],
  congr' 4,
  rw category.assoc,
end

def plus_obj [has_limits D] [has_colimits D] (B : C) (P : Cᵒᵖ ⥤ D) : D :=
colimit (matching_diagram J B P)

def plus_map [has_limits D] [has_colimits D] {X Y : C} (f : X ⟶ Y) (P : Cᵒᵖ ⥤ D) :
  plus_obj J Y P ⟶ plus_obj J X P :=
colim_map (matching_diagram.pullback J f P) ≫ colimit.pre _ _

def plus [has_limits D] [has_colimits D] (P : Cᵒᵖ ⥤ D) : Cᵒᵖ ⥤ D :=
{ obj := λ X, plus_obj J X.unop P,
  map := λ X Y f, plus_map _ f.unop _,
  map_id' := begin
    intros X,
    dsimp [plus_map],
    ext I,
    erw category.comp_id,
    simp only [matching_diagram.pullback, colimit.ι_pre, ι_colim_map_assoc],
    let e : I ≅ (matching_diagram_index.pullback J (𝟙 (unop X))).op.obj I :=
      (nat_iso.op (matching_diagram_index.pullback_id J X.unop)).app I,
    rw [← colimit.w (matching_diagram J (unop X) P) e.inv, ← category.assoc],
    conv_rhs { rw ← category.id_comp (colimit.ι (matching_diagram J (unop X) P) I) },
    congr' 1,
    ext ⟨A,ff,hff⟩,
    dsimp [matching.pullback, matching_diagram, matching.map],
    simp only [fan.mk_π_app, category.id_comp, limit.lift_π,
      category.assoc, equalizer.lift_ι],
    erw [equalizer.lift_ι_assoc, limit.lift_π],
    dsimp [first_obj_index.pullback],
    congr,
    rw category.comp_id,
    refl,
  end,
  map_comp' := begin
    intros X Y Z f g,
    dsimp [plus_map],
    ext I,
    simp,
    let e : (matching_diagram_index.pullback J g.unop).op.obj
      ((matching_diagram_index.pullback J f.unop).op.obj I) ≅
        (matching_diagram_index.pullback J (g.unop ≫ f.unop)).op.obj I :=
      (nat_iso.op (matching_diagram_index.pullback_comp J g.unop f.unop)).app I,
    rw [← colimit.w _ e.inv],
    simp_rw ← category.assoc,
    rw matching_diagram.pullback_comp_app,
  end }

section end

variables {E : Type*} [category.{max u v} E] [has_products D] [has_products E]
variables (P : Cᵒᵖ ⥤ D) (F : D ⥤ E) [preserves_limits F]

@[simps]
def first_obj_comp_preserves_limit {B : C} (R : presieve B) :
  F.obj (first_obj R P) ≅ (first_obj R (P ⋙ F) : _) :=
preserves_limit_iso F _ ≪≫ lim.map_iso
  (nat_iso.of_components (λ _, iso.refl _)
    (by { rintros ⟨_,_,_⟩ ⟨_,_,_⟩ ⟨⟨h⟩⟩, injection h with h₁ h₂,
          cases h₁, cases heq_iff_eq.mp h₂, simp }))

@[simps]
def second_obj'_comp_preserves_limit {B : C} (R : presieve B) :
  F.obj (second_obj' R P) ≅ (second_obj' R (P ⋙ F) : _) :=
preserves_limit_iso F _ ≪≫ lim.map_iso
  (nat_iso.of_components (λ _, iso.refl _)
    (by { rintros ⟨_,_,_⟩ ⟨_,_,_⟩ ⟨⟨h⟩⟩, injection h, subst_vars, simp }))

-- @[simps]
def matching_comp_preserves_limit {B : C} (R : presieve B) [has_limits D] [has_limits E] :
  F.obj (matching R P) ≅ (matching R (P ⋙ F) : _) :=
preserves_limit_iso F _ ≪≫ lim.map_iso
  (nat_iso.of_components (λ X, by { cases X,
    exacts [first_obj_comp_preserves_limit P F R, second_obj'_comp_preserves_limit P F R] })
    (λ X Y f,
    begin
      cases f,
      swap 3,
      simpa[-category.id_comp] using category.id_comp _,
      all_goals
      { ext,
        delta second_map'
          first_map' first_obj_comp_preserves_limit second_obj'_comp_preserves_limit,
        simp }
    end))

section end

def matching_diagram_comp_preserves_limit (B : C) [has_limits D] [has_limits E] :
  matching_diagram J B P ⋙ F ≅ matching_diagram J B (P ⋙ F) :=
begin
  fapply nat_iso.of_components,
  intro X, exact matching_comp_preserves_limit _ _ _,
  intros X Y f,
  delta matching_diagram,
  ext,
  unfold matching_comp_preserves_limit,
  simp[matching.map],
  erw lim_map_π,
  erw limit.lift_π,
  simpa
end

section end

@[simp]
lemma matching_diagram_comp_preserves_limit_hom_app (B : C) [has_limits D] [has_limits E] (A) :
  (matching_diagram_comp_preserves_limit J P F B).hom.app A =
    (matching_comp_preserves_limit P F _).hom := rfl

@[simp, reassoc]
lemma matching_comp_preserves_limit_hom_comp_pullback
 (X Y) (j : matching_diagram_index J Y) (f : X ⟶ Y) [has_limits D] [has_limits E] :
  (matching_comp_preserves_limit P F j.1).hom ≫
    matching.pullback j.val f (P ⋙ F) =
    F.map (matching.pullback j.val f P) ≫ (matching_comp_preserves_limit P F _).hom :=
begin
  unfold matching_comp_preserves_limit,
  erw ←iso.eq_inv_comp,
  ext,
  simp only [functor.map_iso_inv, iso.trans_inv, first_obj_comp_preserves_limit_hom,
    nat_iso.of_components.hom_app, lim_map_π, category.assoc, preserves_limits_iso_hom_π_assoc,
    lim_map_eq_lim_map, iso.trans_hom, functor.map_iso_hom, ←F.map_comp_assoc],
  erw [lim_map_π, limit.lift_π],
  simp only [nat_iso.of_components.hom_app, preserves_limits_iso_hom_π_assoc,
    fork.of_ι_π_app, ←F.map_comp_assoc, limit.lift_π],
  simp only [fan.mk_π_app, nat_iso.of_components.inv_app, preserves_limits_iso_inv_π_assoc,
    lim_map_π_assoc, first_obj_comp_preserves_limit_inv, category.assoc, functor.map_comp],
  erw [limit.lift_π_assoc, category.comp_id, category.comp_id, limit.lift_π],
  dsimp,
  congr
end


instance matching_diagram_index_is_cofiltered (B : C) :
  is_cofiltered (matching_diagram_index J B) :=
{ nonempty := ⟨⟨⊤, J.top_mem _⟩⟩,
  cocone_objs := λ X Y, ⟨⟨X.1 ⊓ Y.1, J.intersection_covering X.2 Y.2⟩,
    (hom_of_le inf_le_left : _ ⟶ X.1), (hom_of_le inf_le_right : _ ⟶ Y.1), trivial⟩,
  cocone_maps := λ _ _ _ _, ⟨_,𝟙 _, by tidy⟩ }

-- set_option trace.class_instances true
variables [has_limits D] [has_colimits D] [has_colimits E] [has_limits E] [preserves_filtered_colimits F]

def plus_obj_comp_preserves_limit_filtered_colimit (B : C) :
  F.obj (plus_obj J B P) ≅ plus_obj J B (P ⋙ F) :=
preserves_colimit_iso F _ ≪≫ colim.map_iso (matching_diagram_comp_preserves_limit J P F B)

set_option timeout 1000000

@[simp] lemma colimit_ι_plus_map (X Y : C) (j : (matching_diagram_index J Y)ᵒᵖ) (f : (op Y) ⟶ (op X)) :
  colimit.ι (matching_diagram J Y P) j ≫ (plus J P).map f =
    matching.pullback (unop j).1 f.unop P ≫ colimit.ι (matching_diagram J X P)
      (op ⟨(unop j).1.pullback f.unop, J.pullback_stable f.unop (unop j).2⟩) :=
begin
  delta plus plus_map matching.pullback matching_diagram.pullback,
  dsimp,
  simp,
  congr,
end

lemma plus_comp_preserves_limit_filtered_colimit [has_limits D] [has_colimits D] (P : Cᵒᵖ ⥤ D) :
  plus J P ⋙ F ≅ plus J (P ⋙ F) :=
begin
  fapply nat_iso.of_components,
  intro B, exact plus_obj_comp_preserves_limit_filtered_colimit J P F (unop B),
  intros X Y f,
  induction X using opposite.rec,
  induction Y using opposite.rec,
  rw functor.comp_map,
  erw category.assoc,
  rw ←iso.inv_comp_eq,
  ext j,
  induction j using opposite.rec,
  erw colimit.ι_map_assoc,
  rw colimit_ι_plus_map J,
  rw ι_preserves_colimits_iso_inv_assoc,
  rw ←F.map_comp_assoc,
  rw colimit_ι_plus_map J,
  delta plus_obj_comp_preserves_limit_filtered_colimit,
  simp only [category.assoc, functor.map_comp],
  erw ι_preserves_colimits_iso_hom_assoc,
  erw colimit.ι_map,
  rw matching_diagram_comp_preserves_limit_hom_app,
  rw matching_diagram_comp_preserves_limit_hom_app,
  dsimp only [unop_op],
  rw matching_comp_preserves_limit_hom_comp_pullback_assoc,
  apply_instance,
  apply_instance,
end

end category_theory.presheaf
