import category_theory.limits.limits
import category_theory.punit
import category_theory.comma
import category_theory.is_connected

noncomputable theory

universes v u

namespace category_theory
open category_theory.limits

variables {C : Type v} [small_category C]
variables {D : Type v} [small_category D]

def final (F : C ⥤ D) : Prop :=
∀ (d : D), is_connected (comma (functor.from_punit d) F)

attribute [class] final

instance (F : C ⥤ D) [ℱ : final F] (d : D) : is_connected (comma (functor.from_punit d) F) :=
ℱ d

namespace final

variables (F : C ⥤ D) [ℱ : final F]
include ℱ

instance (d : D) : nonempty (comma (functor.from_punit d) F) := (‹final F› d).is_nonempty

variables {E : Type u} [category.{v} E] (G : D ⥤ E)

def lift (d : D) : C :=
(classical.arbitrary (comma (functor.from_punit d) F)).right

def hom_to_lift (d : D) : d ⟶ F.obj (lift F d) :=
(classical.arbitrary (comma (functor.from_punit d) F)).hom

def induction {d : D} (Z : Π (X : C) (k : d ⟶ F.obj X), Sort*)
  (h₁ : Π X₁ X₂ (k₁ : d ⟶ F.obj X₁) (k₂ : d ⟶ F.obj X₂) (f : X₁ ⟶ X₂), (k₁ ≫ F.map f = k₂) → Z X₁ k₁ → Z X₂ k₂)
  (h₂ : Π X₁ X₂ (k₁ : d ⟶ F.obj X₁) (k₂ : d ⟶ F.obj X₂) (f : X₁ ⟶ X₂), (k₁ ≫ F.map f = k₂) → Z X₂ k₂ → Z X₁ k₁)
  {X₀ : C} {k₀ : d ⟶ F.obj X₀} (z : Z X₀ k₀) : Z (lift F d) (hom_to_lift F d) :=
begin
  apply @is_preconnected_induction _ _ _
    (λ (Y : comma (functor.from_punit d) F), Z Y.right Y.hom) _ _ { right := X₀, hom := k₀, } z,
  { intros, fapply h₁ _ _ _ _ f.right _ a, convert f.w.symm, dsimp, simp, },
  { intros, fapply h₂ _ _ _ _ f.right _ a, convert f.w.symm, dsimp, simp, },
end

def induction' {Y : C} (Z : Π (X : C) (k : F.obj Y ⟶ F.obj X), Sort*)
  (h₁ : Π X₁ X₂ (k₁ : F.obj Y ⟶ F.obj X₁) (k₂ : F.obj Y ⟶ F.obj X₂) (f : X₁ ⟶ X₂), (k₁ ≫ F.map f = k₂) → Z X₁ k₁ → Z X₂ k₂)
  (h₂ : Π X₁ X₂ (k₁ : F.obj Y ⟶ F.obj X₁) (k₂ : F.obj Y ⟶ F.obj X₂) (f : X₁ ⟶ X₂), (k₁ ≫ F.map f = k₂) → Z X₂ k₂ → Z X₁ k₁)
  (z : Z Y (𝟙 _)) : Z (lift F (F.obj Y)) (hom_to_lift F (F.obj Y)) :=
induction F Z h₁ h₂ z

variables {F G}

@[simps]
def extend_cocone (c : cocone (F ⋙ G)) : cocone G :=
{ X := c.X,
  ι :=
  { app := λ X, G.map (hom_to_lift F X) ≫ c.ι.app (lift F X),
    naturality' := λ X Y f,
    begin
      dsimp, simp,
      -- This would be true if we'd chosen `lift F X` to be `lift F Y`
      -- and `hom_to_lift F X` to be `f ≫ hom_to_lift F Y`.
      apply induction F (λ Z k, G.map f ≫ G.map (hom_to_lift F Y) ≫ c.ι.app (lift F Y) = G.map k ≫ c.ι.app Z),
      { intros Z₁ Z₂ k₁ k₂ g a z,
       rw [←a, functor.map_comp, category.assoc, ←functor.comp_map, c.w, z], },
      { intros Z₁ Z₂ k₁ k₂ g a z,
       rw [←a, functor.map_comp, category.assoc, ←functor.comp_map, c.w] at z,
       rw z, },
      { rw [←functor.map_comp_assoc], },
    end }}

variables (F)

@[simp]
lemma colimit_cocone_comp_aux (s : cocone (F ⋙ G)) (j : C) :
  G.map (hom_to_lift F (F.obj j)) ≫ s.ι.app (lift F (F.obj j)) =
    s.ι.app j :=
begin
  -- This point is that this would be true if we took `lift (F.obj j)` to just be `j`
  -- and `hom_to_lift (F.obj j)` to be `𝟙 (F.obj j)`.
  apply induction' F (λ X k, G.map k ≫ s.ι.app X = (s.ι.app j : _)),
  { intros j₁ j₂ k₁ k₂ f w h, rw ←w, rw ← s.w f at h, simpa using h, },
  { intros j₁ j₂ k₁ k₂ f w h, rw ←w at h, rw ← s.w f, simpa using h, },
  { simp, },
end

@[simps]
def colimit_cocone_comp (t : colimit_cocone G) :
  colimit_cocone (F ⋙ G) :=
{ cocone := t.cocone.whisker F,
  is_colimit :=
  { desc := λ s, t.is_colimit.desc (extend_cocone s),
    uniq' := λ s m w,
    begin
      apply t.is_colimit.hom_ext,
      intro d,
      simp [(w _).symm],
    end, }, }.

@[priority 100]
instance comp_has_colimit [has_colimit G] :
  has_colimit (F ⋙ G) :=
has_colimit.mk (colimit_cocone_comp F (get_colimit_cocone G))

lemma colimit_pre_is_iso_aux (t : colimit_cocone G) :
  (colimit_cocone_comp F t).is_colimit.desc (t.cocone.whisker F) = 𝟙 t.cocone.X :=
begin
  apply t.is_colimit.hom_ext,
  tidy,
end

instance colimit_pre_is_iso [has_colimit G] :
  is_iso (colimit.pre G F) :=
begin
  rw colimit.pre_eq (colimit_cocone_comp F (get_colimit_cocone G)) (get_colimit_cocone G),
  rw colimit_pre_is_iso_aux,
  dsimp,
  apply_instance,
end

def colimit_iso [has_colimit G] : colimit (F ⋙ G) ≅ colimit G := as_iso (colimit.pre G F)

@[simps]
def colimit_cocone_of_comp (t : colimit_cocone (F ⋙ G)) :
  colimit_cocone G :=
{ cocone := extend_cocone t.cocone,
  is_colimit :=
  { desc := λ s, t.is_colimit.desc (s.whisker F),
    uniq' := λ s m w,
    begin
      apply t.is_colimit.hom_ext,
      intro X,
      simp [(w _).symm],
    end, }, }

@[priority 10]
instance has_colimit_of_comp [has_colimit (F ⋙ G)] :
  has_colimit G :=
has_colimit.mk (colimit_cocone_of_comp F (get_colimit_cocone (F ⋙ G)))

def colimit_iso' [has_colimit (F ⋙ G)] : colimit (F ⋙ G) ≅ colimit G := as_iso (colimit.pre G F)

end final

end category_theory
