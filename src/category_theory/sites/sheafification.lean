import category_theory.sites.sheaf

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

end category_theory.presheaf
