import category_theory.bicategory.equivalence
import category_theory.bicategory.opposites
import category_theory.bicategory.pseudonat_trans
import category_theory.bicategory.Cat

open category_theory

universes w v u

open opposite

namespace category_theory

namespace bicategory

section

variables {B : Type u} [bicategory.{w v} B] (a b c d : B)

/--
Left composition of 1-morphisms as a functor.
-/
@[simps]
def lcomp : (a ⟶ b) ⥤ (b ⟶ c) ⥤ (a ⟶ c) :=
{ obj := λ f,
  { obj := λ g, f ≫ g,
    map := λ g h η, f ◁ η },
  map := λ f g η, { app := λ h, η ▷ h } }

/--
Right composition of 1-morphisms as a functor.
-/
@[simps]
def rcomp : (b ⟶ c) ⥤ (a ⟶ b) ⥤ (a ⟶ c) :=
{ obj := λ f,
  { obj := λ g, g ≫ f,
    map := λ g h η, η ▷ f },
  map := λ f g η, { app := λ h, h ◁ η } }

variables {a b c d}

/--
Left component of an associator as a natural isomorphism.
-/
@[simps]
def associator_nat_iso_left (a) (g : b ⟶ c) (h : c ⟶ d) :
  (rcomp a _ _).obj g ⋙ (rcomp a _ _).obj h
  ≅ (rcomp a _ _).obj (g ≫ h) :=
nat_iso.of_components
  (λ f, α_ f g h)
  (by { intros, apply associator_naturality_left })

/--
Middle component of an associator as a natural isomorphism.
-/
@[simps]
def associator_nat_iso_middle (f : a ⟶ b) (h : c ⟶ d) :
  (lcomp _ _ c).obj f ⋙ (rcomp a _ _).obj h
  ≅ (rcomp b _ _).obj h ⋙ (lcomp _ _ d).obj f :=
nat_iso.of_components
  (λ g, α_ f g h)
  (by { intros, apply associator_naturality_middle })

/--
Right component of an associator as a natural isomorphism.
-/
@[simps]
def associator_nat_iso_right (d) (f : a ⟶ b) (g : b ⟶ c) :
  (lcomp _ _ d).obj (f ≫ g)
  ≅ (lcomp _ _ d).obj g ⋙ (lcomp _ _ d).obj f :=
nat_iso.of_components
  (λ h, α_ f g h)
  (by { intros, apply associator_naturality_right })

/--
Left unitor as a natural isomorphism.
-/
@[simps]
def left_unitor_nat_iso (a b : B) : (lcomp _ _ b).obj (𝟙 a) ≅ 𝟭 (a ⟶ b) :=
nat_iso.of_components
  (λ f, λ_ f)
  (by { intros, apply left_unitor_naturality })

/--
Right unitor as a natural isomorphism.
-/
@[simps]
def right_unitor_nat_iso (a b : B): (rcomp a _ _).obj (𝟙 b) ≅ 𝟭 (a ⟶ b) :=
nat_iso.of_components
  (λ f, ρ_ f)
  (by { intros, apply right_unitor_naturality })

end

end bicategory

section
open bicategory

variables {B : Type u} [bicategory.{w v} B]

/--
The Yoneda embedding at the level of objects.
-/
@[simps]
def yoneda_map₀ (a : B) : pseudofunctor Bᵒᵖ Cat :=
{ map₀ := λ s, Cat.of ((unop s) ⟶ a),
  map₁ := λ s t f, (lcomp (unop t) (unop s) a).obj f,
  map₂ := λ s t f g β, (lcomp (unop t) (unop s) a).map β,
  map₁_id   := λ s, (left_unitor_nat_iso (unop s) a).symm,
  map₁_comp := λ s t r p q, (associator_nat_iso_right a q p).symm,
  map₁_comp_naturality_left'  := by { intros, ext, apply associator_inv_naturality_middle },
  map₁_comp_naturality_right' := by { intros, ext, apply associator_inv_naturality_left },
  map₂_id'    := by { intros, ext, apply bicategory.whisker_right_id },
  map₂_comp'  := by { intros, ext, apply bicategory.whisker_right_comp },
  map₂_associator'  := by { intros, ext, dsimp, erw pentagon_inv, simpa },
  map₂_left_unitor'   := by { intros, ext, dsimp, erw triangle_assoc_comp_right, simp },
  map₂_right_unitor'  := by { intros, ext, dsimp, simp,
                                erw [iso.hom_inv_id_assoc, inv_hom_whisker_right] } }

/--
The Yoneda embedding at the level of 1-morphisms.
-/
@[simps]
def yoneda_map₁ {a b : B} (f : a ⟶ b) : pseudonat_trans (yoneda_map₀ a) (yoneda_map₀ b) :=
{ app := λ s, (rcomp (unop s) a b).obj f,
  naturality := λ _ _ _, associator_nat_iso_middle _ f,
  naturality_naturality' := by { intros, ext, apply associator_naturality_left },
  naturality_id' := by { intros, ext, dsimp, simpa },
  naturality_comp' := by { intros, ext, dsimp, simp, erw pentagon_hom_hom_inv_inv_hom, refl } }

/--
The Yoneda embedding at the level of 2-morphisms.
-/
@[simps]
def yoneda_map₂ {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
  modification (yoneda_map₁ f) (yoneda_map₁ g) :=
{ app := λ s,
  { app := λ h, h ◁ η,
    naturality' := by { intros, dsimp, rw whisker_exchange } },
  naturality' := by { intros, ext, dsimp, apply associator_naturality_right } }

/--
The Yoneda embedding as a pseudofunctor from `B` into 2-presheaves on `B`.
-/
@[simps]
def yoneda : pseudofunctor B (pseudofunctor Bᵒᵖ Cat) :=
{ map₀ := yoneda_map₀,
  map₁ := λ _ _, yoneda_map₁,
  map₂ := λ _ _ _ _, yoneda_map₂,
  map₁_id := λ a, modification_iso.of_components
    (λ s : Bᵒᵖ, (right_unitor_nat_iso (unop s) a).symm)
    (by { intros, ext, dsimp, simp }),
  map₁_comp := λ (a b c : B) (f : a ⟶ b) (g : b ⟶ c), modification_iso.of_components
    (λ s : Bᵒᵖ, associator_nat_iso_left (unop s) f g)
    (by { intros, ext, dsimp, simp [pentagon] }),
  map₁_comp_naturality_left'  := by { intros, ext, dsimp, apply associator_naturality_middle },
  map₁_comp_naturality_right' := by { intros, ext, dsimp, apply associator_naturality_right },
  map₂_id'    := by { intros, ext, dsimp, apply bicategory.whisker_left_id },
  map₂_comp'  := by { intros, ext, dsimp, apply bicategory.whisker_left_comp },
  map₂_associator'  := by { intros, ext, dsimp, simp [pentagon] },
  map₂_left_unitor'   := by { intros, ext, dsimp, simp [triangle] },
  map₂_right_unitor'  := by { intros, ext, dsimp, simp [right_unitor_comp_inv] } }

end

section
open bicategory

variables
{B : Type u} [bicategory.{u u} B] (F : pseudofunctor Bᵒᵖ Cat.{u u})

@[simps]
def yoneda_lemma_hom : pseudonat_trans (yoneda.op.comp (yoneda_map₀ F)) F :=
{ app := λ a : Bᵒᵖ,
  { obj := λ σ, (σ.app a).obj (𝟙 (unop a)),
    map := λ σ τ (Γ : modification σ τ), (Γ.app a).app (𝟙 (unop a)),
    map_id' := by { intros, refl },
    map_comp' := by { intros, refl } },
  naturality := λ (a b : Bᵒᵖ) (f : a ⟶ b), nat_iso.of_components (λ σ,
    (σ.app b).map_iso (λ_ f)
    ≪≫ ((σ.app b).map_iso (ρ_ f)).symm
    ≪≫ (σ.naturality f).app (𝟙 (unop a)))
    begin
      intros σ τ Γ,
      dsimp, simp only [category.assoc],
      have naturality := congr_app (modification.naturality Γ f) (𝟙 (unop a)),
      dsimp at naturality,
      rw [←naturality, nat_trans.naturality_assoc, nat_trans.naturality_assoc]
    end,
  naturality_naturality' := λ (a b : Bᵒᵖ) (f g : a ⟶ b) (η : f ⟶ g),
  begin
    ext σ,
    dsimp, simp only [category.assoc],
    have naturality := congr_app (σ.naturality_naturality η) (𝟙 (unop a)),
    dsimp at naturality, rw [←naturality],
    simp only [←functor.map_comp_assoc],
    erw [left_unitor_naturality_assoc, left_unitor_inv_naturality],
    refl
  end,
  naturality_id' := λ a : Bᵒᵖ,
  begin
    ext σ, dsimp, simp,
    have naturality := congr_app (σ.naturality_id a) (𝟙 _),
    dsimp at naturality, simp only [category.id_comp] at naturality,
    simp only [←functor.map_comp_assoc],
    erw [unitors_equal, iso.inv_hom_id_assoc, ←unitors_inv_equal, naturality]
  end,
  naturality_comp' := λ (a b c : Bᵒᵖ) (f : a ⟶ b) (g : b ⟶ c),
  begin
    ext σ, dsimp, simp,
    have naturality := congr_app (σ.naturality_comp f g) (𝟙 _),
    dsimp at naturality, simp only [category_theory.category.id_comp] at naturality,
    simp only [←functor.map_comp_assoc],
    erw [left_unitor_comp_assoc, iso.hom_inv_id_assoc, right_unitor_comp_inv,
    triangle_assoc_comp_right_inv],
    simp only [category_theory.category.assoc, category_theory.functor.map_comp],
    rw naturality,
    erw ←nat_trans.naturality_assoc,
    erw ←nat_trans.naturality_assoc,
    dsimp,
    simp only [←functor.map_comp_assoc],
    erw [inv_hom_whisker_left_assoc],
  end }

variables {F}

@[simps]
def yoneda_lemma_inv_pseudonat_trans {a : Bᵒᵖ} (u : F.map₀ a) :
  pseudonat_trans (yoneda_map₀ (unop a)) F :=
{ app := λ s : Bᵒᵖ,
  { obj := λ g : a ⟶ s, (F.map₁ g).obj u,
    map := λ (g h : a ⟶ s) (β : g ⟶ h), (F.map₂ β).app u,
    map_id'     := by { intros, rw [F.map₂_id, nat_trans.id_app] },
    map_comp'   := by { intros, rw [F.map₂_comp, nat_trans.comp_app] } },
  naturality := λ (s t : Bᵒᵖ) (p : s ⟶ t), nat_iso.of_components
    (λ g : a ⟶ s, ((F.map₁_comp g p).app u).symm)
    (λ (g h : a ⟶ s) (β : g ⟶ h), by
    { dsimp, simp only [←whisker_right_app, ←nat_trans.comp_app],
      erw F.map₁_comp_inv_naturality_left, refl }),
  naturality_naturality' := λ (s t : Bᵒᵖ) (p q : s ⟶ t) (β : p ⟶ q), by
  { ext (g : a ⟶ s),
    dsimp, simp only [←whisker_left_app, ←nat_trans.comp_app],
    erw F.map₁_comp_inv_naturality_right, refl },
  naturality_id' := λ s : Bᵒᵖ, by
  { ext (g : a ⟶ s),
    dsimp, simp only [category.id_comp, ←whisker_left_app, ←nat_trans.comp_app],
    erw [F.map₂_right_unitor_inv_eq_assoc, iso.hom_inv_id], dsimp, simp },
  naturality_comp' := λ (s t r : Bᵒᵖ) (p : s ⟶ t) (q : t ⟶ r), by
  { ext (g : a ⟶ s), dsimp,
    simp only [category.id_comp, ←whisker_left_app, ←whisker_right_app, ←nat_trans.comp_app],
    erw F.map₂_associator_eq_assoc, dsimp, simp, erw category.comp_id, refl } }

@[simps]
def yoneda_lemma_inv_modification {a : Bᵒᵖ} {u v : F.map₀ a} (k : u ⟶ v) :
  modification (yoneda_lemma_inv_pseudonat_trans u) (yoneda_lemma_inv_pseudonat_trans v) :=
{ app := λ s : Bᵒᵖ,
  { app := λ g : a ⟶ s, (F.map₁ g).map k,
    naturality' := by { intros, dsimp, rw nat_trans.naturality } },
  naturality' := by { intros, ext, dsimp, rw nat_trans.naturality, refl } }

@[simps]
def yoneda_lemma_inv_functor (a : Bᵒᵖ) : F.map₀ a ⥤ pseudonat_trans (yoneda_map₀ (unop a)) F :=
{ obj := λ u : F.map₀ a, yoneda_lemma_inv_pseudonat_trans u,
  map := λ (u v : F.map₀ a) (k : u ⟶ v), yoneda_lemma_inv_modification k,
  map_id'     := by { intros, ext, dsimp, rw functor.map_id },
  map_comp'   := by { intros, ext, dsimp, rw functor.map_comp } }

@[simps]
def yoneda_lemma_inv_iso {a b : Bᵒᵖ} (f : a ⟶ b) (u : F.map₀ a) :
  ((yoneda.op.comp (yoneda_map₀ F)).map₁ f).obj (yoneda_lemma_inv_pseudonat_trans u) ≅
    yoneda_lemma_inv_pseudonat_trans ((F.map₁ f).obj u) := by
{ apply modification_iso.of_components (λ s : Bᵒᵖ, _) _,
  apply nat_iso.of_components (λ g : b ⟶ s, _) _,
  apply iso.app (F.map₁_comp f g).symm u,
  { intros g h β, dsimp, simp only [←whisker_left_app, ←nat_trans.comp_app],
    erw F.map₁_comp_inv_naturality_right, refl },
  { intros s t p, ext (g : b ⟶ s),
    dsimp, simp,
    simp only [←whisker_left_app, ←whisker_right_app, ←nat_trans.comp_app],
    erw [F.map₂_associator_inv_eq_assoc, iso.hom_inv_id_assoc],
    dsimp, simp only [←functor.map_comp, ←nat_trans.comp_app],
    erw [iso.hom_inv_id, functor.map_id], simp, refl } }

variables (F)

section aux
variables {a b c : Bᵒᵖ}

lemma yoneda_lemma_inv_aux₁ (f : unop b ⟶ unop a) (u : F.map₀ a)
  {s : Bᵒᵖ} {g h : unop s ⟶ unop b} (β : g ⟶ h) :
  (((yoneda_lemma_inv_functor b).obj ((F.map₁ f).obj u)).app s).map β ≫
      (F.map₁_comp f h).hom.app u =
    (F.map₁_comp f g).hom.app u ≫
      (((yoneda_lemma_inv_functor a).obj u).app s).map (β ▷ f) :=
begin
  dsimp [yoneda_lemma_inv_functor], simp only [←whisker_left_app, ←nat_trans.comp_app],
  erw F.map₁_comp_naturality_right, refl,
end

lemma yoneda_lemma_inv_aux₂ (f : unop b ⟶ unop a) (u : F.map₀ a)
  {s t : Bᵒᵖ} (p : unop t ⟶ unop s) (g : unop s ⟶ unop b) :
(F.map₁_comp f (g ≫ p)).hom.app u ≫
  ((((yoneda.op.comp (yoneda_map₀ F)).map₁ f).obj ((yoneda_lemma_inv_functor a).obj u)).naturality p).hom.app g
  = (((yoneda_lemma_inv_functor b).obj ((F.map₁ f).obj u)).naturality p).hom.app g ≫
      (F.map₁ p).map ((F.map₁_comp f g).hom.app u) :=
begin
  dsimp [yoneda_lemma_inv_functor], simp,
  simp only [←whisker_left_app, ←whisker_right_app, ←nat_trans.comp_app],
  erw [F.map₂_associator_inv_eq_assoc, iso.hom_inv_id_assoc,
      iso.hom_inv_id, category.comp_id],
  simp, erw category.id_comp
end

lemma yoneda_lemma_inv_aux₃ (f : unop b ⟶ unop a) {u v : F.map₀ a}
  (k : u ⟶ v) {s : Bᵒᵖ} (g : b ⟶ s) :
(((yoneda_lemma_inv_functor b).map ((F.map₁ f).map k)).app s).app g ≫
  (F.map₁_comp f g).hom.app v
  = (F.map₁_comp f g).hom.app u ≫
      (((yoneda_lemma_inv_functor a).map k).app s).app (g ≫ f) :=
begin
  erw ←nat_trans.naturality, refl
end

lemma yoneda_lemma_inv_aux₄ (f g : unop b ⟶ unop a) (β : f ⟶ g) (u : F.map₀ a)
  {s : Bᵒᵖ} (h : unop s ⟶ unop b) :
(((yoneda_lemma_inv_functor b).map ((F.map₂ β).app u)).app s).app h ≫
  (F.map₁_comp g h).hom.app u
  = (F.map₁_comp f h).hom.app u ≫
      (((yoneda_lemma_inv_functor a).obj u).app s).map (h ◁ β) :=
begin
  dsimp [yoneda_lemma_inv_functor],
  simp only [←whisker_right_app, ←nat_trans.comp_app],
  erw F.map₁_comp_naturality_left, refl
end

lemma yoneda_lemma_inv_aux₅ (u : F.map₀ a) {s : Bᵒᵖ} (g : unop s ⟶ unop a) :
(((yoneda_lemma_inv_functor a).map ((F.map₁_id a).hom.app u)).app s).app g ≫
  (F.map₁_comp (𝟙 a) g).hom.app u
  = 𝟙 _ ≫ 𝟙 _ ≫
    ((((yoneda.op.comp (yoneda_map₀ F)).map₁_id a).hom.app
      ((yoneda_lemma_inv_functor a).obj u)).app s).app g :=
begin
dsimp [yoneda_lemma_inv_functor],simp,
    simp only [←whisker_left_app, ←whisker_right_app, ←nat_trans.comp_app],
    erw F.map₂_left_unitor_inv_eq,
    dsimp, erw category.id_comp, refl
end

lemma yoneda_lemma_inv_aux₆ (f : unop b ⟶ unop a) (g : unop c ⟶ unop b)
  (u : F.map₀ a) {s : Bᵒᵖ} (h : unop s ⟶ unop c) :
(((yoneda_lemma_inv_functor c).map ((F.map₁_comp f g).hom.app u)).app s).app h ≫
  (F.map₁_comp (f ≫ g) h).hom.app u
= 𝟙 _ ≫ (F.map₁_comp g h).hom.app ((F.map₁ f).obj u) ≫
    𝟙 _ ≫ (F.map₁_comp f (g ≫ h)).hom.app u ≫
      𝟙 _ ≫ ((((yoneda.op.comp (yoneda_map₀ F)).map₁_comp f g).hom.app
                ((yoneda_lemma_inv_functor a).obj u)).app s).app h :=
begin
  dsimp [yoneda_lemma_inv_functor], simp,
  simp only [←whisker_left_app, ←whisker_right_app, ←nat_trans.comp_app],
  erw [F.map₂_associator_inv_eq, iso.hom_inv_id_assoc], simp,
  erw category.id_comp
end

end aux

@[simps]
def yoneda_lemma_inv : pseudonat_trans F (yoneda.op.comp (yoneda_map₀ F)) :=
{ app := λ a : Bᵒᵖ, yoneda_lemma_inv_functor a,
  naturality := λ (a b : Bᵒᵖ) (f : a ⟶ b), by
  { apply nat_iso.of_components (λ u : F.map₀ a, _) _,
    apply modification_iso.of_components (λ s : Bᵒᵖ, _) _,
    apply nat_iso.of_components (λ g : b ⟶ s, _) _,
    apply iso.app (F.map₁_comp f g) u,
    { intros, dsimp only [], apply yoneda_lemma_inv_aux₁ },
    { intros, ext, apply yoneda_lemma_inv_aux₂ },
    { intros, ext, apply yoneda_lemma_inv_aux₃ } },
  naturality_naturality' := by { intros, ext, apply yoneda_lemma_inv_aux₄ },
  naturality_id' := by { intros, ext, apply yoneda_lemma_inv_aux₅ },
  naturality_comp' := by { intros, ext, apply yoneda_lemma_inv_aux₆ } }

section aux
variables {a b : Bᵒᵖ} (f : unop b ⟶ unop a)
(σ : pseudonat_trans (yoneda_map₀ (unop a)) F)


lemma yoneda_lemma_aux₁ {s : Bᵒᵖ} {g h : unop s ⟶ unop a} (β : g ⟶ h) :
  (σ.app s).map β ≫ (σ.app s).map (ρ_ h).inv ≫ (σ.naturality h).hom.app (𝟙 (unop a))
  = ((σ.app s).map (ρ_ g).inv ≫ (σ.naturality g).hom.app (𝟙 (unop a))) ≫
      ((((yoneda_lemma_inv F).app a).obj (((yoneda_lemma_hom F).app a).obj σ)).app s).map β :=
begin
  dsimp, simp only [←functor.map_comp_assoc],
  rw right_unitor_inv_naturality,
  simp,
  have naturality := nat_trans.congr_app (σ.naturality_naturality β) (𝟙 _),
  dsimp at naturality,
  simp only [←whisker_left_app, ←whisker_right_app, ←nat_trans.comp_app,
    ←functor.map_comp],
  erw naturality, refl
end

lemma yoneda_lemma_aux₂ {s t : Bᵒᵖ} (p : unop t ⟶ unop s) (g : unop s ⟶ unop a) :
((σ.app t).map (ρ_ (p ≫ g)).inv ≫ (σ.naturality (g ≫ p)).hom.app (𝟙 (unop a))) ≫
  ((((yoneda_lemma_inv F).app a).obj
    (((yoneda_lemma_hom F).app a).obj σ)).naturality p).hom.app g
= (σ.naturality p).hom.app g ≫ (F.map₁ p).map ((σ.app s).map (ρ_ g).inv ≫
    (σ.naturality g).hom.app (𝟙 (unop a))) :=
begin
  dsimp, simp,
  have comp := nat_trans.congr_app (σ.naturality_comp g p) (𝟙 (unop a)),
  have naturality := ((σ.naturality p).hom.naturality _),
  dsimp at comp naturality, simp at comp,
  slice_rhs 1 2 { erw ←naturality },
  slice_lhs 2 3 { erw comp },
  simp, erw category.comp_id
end

lemma yoneda_lemma_aux₃ {σ τ : pseudonat_trans (yoneda_map₀ (unop a)) F}
  (Φ : σ ⟶ τ) {s : Bᵒᵖ} (g : unop s ⟶ unop a) :
(Φ.app s).app g ≫ (τ.app s).map (ρ_ g).inv ≫ (τ.naturality g).hom.app (𝟙 (unop a))
= ((σ.app s).map (ρ_ g).inv ≫ (σ.naturality g).hom.app (𝟙 (unop a))) ≫
    ((((yoneda_lemma_inv F).app a).map (((yoneda_lemma_hom F).app a).map Φ)).app s).app g :=
begin
  dsimp, simp,
  erw ←nat_trans.naturality_assoc,
  have naturality := nat_trans.congr_app (Φ.naturality g) (𝟙 _),
  dsimp at naturality,
  erw naturality
end

lemma yoneda_lemma_aux₄ {s : Bᵒᵖ} (g : unop s ⟶ unop b) :
((σ.app s).map ((ρ_ g).inv ▷ f) ≫
  ((((yoneda.op.comp (yoneda_map₀ F)).map₁ f).obj σ).naturality g).hom.app (𝟙 (unop b))) ≫ 𝟙 _ ≫
    ((((yoneda_lemma_inv F).app b).map
      (((yoneda_lemma_hom F).naturality f).hom.app σ)).app s).app g ≫ 𝟙 _ ≫
        ((((yoneda_lemma_inv F).naturality f).hom.app
          (((yoneda_lemma_hom F).app a).obj σ)).app s).app g ≫ 𝟙 _
= (𝟙 _ ≫ 𝟙 _) ≫
    (σ.app s).map (ρ_ (g ≫ f)).inv ≫
      (σ.naturality (f ≫ g)).hom.app (𝟙 (unop a)) :=
begin
  dsimp, simp,
  have comp := nat_trans.congr_app (σ.naturality_comp f g) (𝟙 (unop a)),
  dsimp at comp, simp at comp,
  erw comp,
  simp only [←category.assoc], congr' 2, simp only [category.assoc],
  simp only [←functor.map_comp],
  erw ←nat_trans.naturality,
  simp,
  simp only [←functor.map_comp_assoc],
  erw triangle_assoc,
  simp
end

lemma yoneda_lemma_aux₅ {u v : F.map₀ a} (k :u ⟶ v) :
((yoneda_lemma_hom F).app a).map (((yoneda_lemma_inv F).app a).map k) ≫ (F.map₁_id a).inv.app v
= (F.map₁_id a).inv.app u ≫ k :=
begin
  dsimp,
  simp [nat_trans.naturality]
end

lemma yoneda_lemma_aux₆ (f : unop b ⟶ unop a) (u : F.map₀ a) :
(F.map₁_id b).inv.app ((F.map₁ f).obj u) ≫ 𝟙 _ ≫ 𝟙 _
= (𝟙 _ ≫
  ((yoneda_lemma_hom F).app b).map
    (((yoneda_lemma_inv F).naturality f).hom.app u) ≫ 𝟙 _ ≫
      ((yoneda_lemma_hom F).naturality f).hom.app
        (((yoneda_lemma_inv F).app a).obj u) ≫ 𝟙 _) ≫
          (F.map₁ f).map ((F.map₁_id a).inv.app u) :=
begin
  dsimp, simp,
  simp only [←whisker_left_app, ←whisker_right_app, ←nat_trans.comp_app],
  erw [F.map₂_left_unitor_inv_eq_assoc, F.map₂_right_unitor_eq_assoc,
      iso.hom_inv_id_assoc, iso.hom_inv_id_assoc, iso.hom_inv_id_assoc],
  simp, simp only [←functor.map_comp, ←nat_trans.comp_app],
  erw iso.hom_inv_id,
  simp,
  erw category.comp_id
end

end aux

/--
The Yoneda lemma. It is a equivalence between `yoneda.op.comp (yoneda_map₀ F)` and `F` in
the bicategory `pseudofunctor Bᵒᵖ Cat`.
-/
def yoneda_lemma : bicategory.equivalence (yoneda.op.comp (yoneda_map₀ F)) F :=
{ hom := yoneda_lemma_hom F,
  inv := yoneda_lemma_inv F,
  unit_iso := by
  { apply modification_iso.of_components (λ a : Bᵒᵖ, _) _,
    apply nat_iso.of_components (λ σ : pseudonat_trans (yoneda_map₀ (unop a)) F, _) _,
    apply modification_iso.of_components (λ s : Bᵒᵖ, _) _,
    apply nat_iso.of_components (λ g : a ⟶ s, _) _,
    exact (σ.app s).map_iso (λ_ g).symm ≪≫ ((σ.naturality g).app (𝟙 (unop a))),
    { intros, dsimp only [], apply yoneda_lemma_aux₁, },
    { intros, ext, apply yoneda_lemma_aux₂ },
    { intros, ext, apply yoneda_lemma_aux₃ },
    { intros, ext, apply yoneda_lemma_aux₄ } },
  counit_iso := by
  { apply modification_iso.of_components (λ a : Bᵒᵖ, _) _,
    apply nat_iso.of_components (λ u : F.map₀ a, _) _,
    exact (F.map₁_id a).symm.app u,
    { intros, dsimp only [], apply yoneda_lemma_aux₅ },
    { intros, ext, apply yoneda_lemma_aux₆ } } }

end

end category_theory
