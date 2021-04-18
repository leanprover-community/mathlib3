import category_theory.monoidal.braided
import category_theory.reflects_isomorphisms

open category_theory
open category_theory.monoidal_category

universes v v₁ v₂ v₃ u u₁ u₂ u₃
noncomputable theory

namespace category_theory

variables {C : Type u₁} [category.{v₁} C] [monoidal_category C]

inductive monoidal_hom : C → C → Type u₁
| id {X} : monoidal_hom X X
| α_hom {X Y Z} : monoidal_hom ((X ⊗ Y) ⊗ Z) (X ⊗ (Y ⊗ Z))
| α_inv {X Y Z} : monoidal_hom (X ⊗ (Y ⊗ Z)) ((X ⊗ Y) ⊗ Z)
| l_hom {X} : monoidal_hom (𝟙_ C ⊗ X) X
| l_inv {X} : monoidal_hom X (𝟙_C ⊗ X)
| ρ_hom {X} : monoidal_hom (X ⊗ 𝟙_C) X
| ρ_inv {X} : monoidal_hom X (X ⊗ 𝟙_ C)
| comp {X Y Z} (f : monoidal_hom X Y) (g : monoidal_hom Y Z) : monoidal_hom X Z
| tensor {W X Y Z} (f : monoidal_hom W Y) (g : monoidal_hom X Z) : monoidal_hom (W ⊗ X) (Y ⊗ Z)

@[simp] def monoidal_to_hom : ∀ {X Y : C}, monoidal_hom X Y → (X ⟶ Y)
| _ _ monoidal_hom.id := 𝟙 _
| _ _ monoidal_hom.α_hom := (α_ _ _ _).hom
| _ _ monoidal_hom.α_inv := (α_ _ _ _).inv
| _ _ monoidal_hom.l_hom := (λ_ _).hom
| _ _ monoidal_hom.l_inv := (λ_ _).inv
| _ _ monoidal_hom.ρ_hom := (ρ_ _).hom
| _ _ monoidal_hom.ρ_inv := (ρ_ _).inv
| _ _ (monoidal_hom.comp f g) := monoidal_to_hom f ≫ monoidal_to_hom g
| _ _ (monoidal_hom.tensor f g) := monoidal_to_hom f ⊗ monoidal_to_hom g

instance monoidal_to_hom_is_iso : ∀ {X Y : C} (h : monoidal_hom X Y), is_iso (monoidal_to_hom h)
| _ _ monoidal_hom.id := is_iso.id _
| _ _ monoidal_hom.α_hom := is_iso.of_iso (α_ _ _ _)
| _ _ monoidal_hom.α_inv := is_iso.of_iso_inv (α_ _ _ _)
| _ _ monoidal_hom.l_hom := is_iso.of_iso (λ_ _)
| _ _ monoidal_hom.l_inv := is_iso.of_iso_inv (λ_ _)
| _ _ monoidal_hom.ρ_hom := is_iso.of_iso (ρ_ _)
| _ _ monoidal_hom.ρ_inv := is_iso.of_iso_inv (ρ_ _)
| _ _ (monoidal_hom.comp f g) :=
             @is_iso.comp_is_iso _ _ _ _ _ _ _ (monoidal_to_hom_is_iso f) (monoidal_to_hom_is_iso g)
| _ _ (monoidal_hom.tensor f g) :=
             @monoidal_category.tensor_is_iso _ _ _ _ _ _ _
                _ (monoidal_to_hom_is_iso _)
                _ (monoidal_to_hom_is_iso _)

-- The monoidal coherence theorem!
theorem coherence {X Y : C} (h h' : monoidal_hom X Y) : monoidal_to_hom h = monoidal_to_hom h' :=
sorry

/- We don't use `nonempty` here because `nonempty` is a class and we don't want a class here. -/
inductive monoidal_eq (X Y : C) : Prop
| intro (h : monoidal_hom X Y) : monoidal_eq

infixr ` =ᵐ `:50 := monoidal_eq

lemma nonempty_of_monoidal_eq {X Y : C} : X =ᵐ Y → nonempty (monoidal_hom X Y) :=
λ ⟨h⟩, ⟨h⟩

lemma monoidal_eq.trans {X Y Z : C} : X =ᵐ Y → Y =ᵐ Z → X =ᵐ Z :=
λ ⟨h⟩ ⟨h'⟩, ⟨monoidal_hom.comp h h'⟩

lemma monoidal_eq.tensor {W X Y Z : C} : W =ᵐ X → Y =ᵐ Z → W ⊗ Y =ᵐ X ⊗ Z :=
λ ⟨h⟩ ⟨h'⟩, ⟨monoidal_hom.tensor h h'⟩

def hom_of_monoidal_eq {X Y : C} (h : X =ᵐ Y) : X ⟶ Y :=
monoidal_to_hom (classical.choice (nonempty_of_monoidal_eq h))

lemma hom_of_monoidal_eq_eq {X Y : C} {h : X =ᵐ Y} (h' : monoidal_hom X Y) :
  hom_of_monoidal_eq h = monoidal_to_hom h' :=
coherence _ _

/- The reason why we choose the convoluted setup above is that this is true definitionally. -/
example {X Y : C} (h h' : X =ᵐ Y) : hom_of_monoidal_eq h = hom_of_monoidal_eq h' :=
rfl

def coherent_comp {W X Y Z : C} (h : X =ᵐ Y) (f : W ⟶ X) (g : Y ⟶ Z) : W ⟶ Z :=
f ≫ hom_of_monoidal_eq h ≫ g

notation f ` ≫ᵐ[`:80 h:80 `] `:0 g:80 := coherent_comp h f g
infixr ` ≫ᵐ `:80 := coherent_comp _

lemma coherent_comp_constructor {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) (h : monoidal_hom X Y) :
  f ≫ᵐ[⟨h⟩] g = f ≫ monoidal_to_hom h ≫ g :=
by rw [coherent_comp, hom_of_monoidal_eq_eq h]

lemma comp_eq_coherent_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  f ≫ g = f ≫ᵐ[⟨monoidal_hom.id⟩] g :=
by simp [coherent_comp_constructor]

@[simp] lemma coherent_assoc {U V W X Y Z : C} (f : U ⟶ V) {h : V =ᵐ W} (g : W ⟶ X) {h' : X =ᵐ Y}
  (i : Y ⟶ Z) : (f ≫ᵐ[h] g) ≫ᵐ[h'] i = f ≫ᵐ[h] (g ≫ᵐ[h'] i) :=
by { rcases h, rcases h', simp [coherent_comp_constructor] }

@[simp] lemma coherent_comp_id_coherent_comp {V W X Y Z : C} (f : V ⟶ W) {h : W =ᵐ X} {h' : X =ᵐ Y}
  (g : Y ⟶ Z) : f ≫ᵐ[h] 𝟙 X ≫ᵐ[h'] g = f ≫ᵐ[h.trans h'] g :=
begin
  cases h,
  cases h',
  rw coherent_comp_constructor _ _ (monoidal_hom.comp h h'),
  simp [coherent_comp, hom_of_monoidal_eq_eq h, hom_of_monoidal_eq_eq h']
end

@[simp] lemma coherent_comp_id_coherent_comp' {V W X Y Z : C} (f : V ⟶ W) {h : W =ᵐ X} {h' : X =ᵐ Y}
  (g : Y ⟶ Z) : f ≫ᵐ[h] (𝟙 X ≫ᵐ[h'] g) = f ≫ᵐ[h.trans h'] g :=
by rw [←coherent_assoc, coherent_comp_id_coherent_comp]

lemma coherent_comp_monoidal_to_hom {W X Y Z : C} (f : W ⟶ X) {h : X =ᵐ Y} (t : monoidal_hom Y Z) :
  f ≫ᵐ[h] monoidal_to_hom t = f ≫ᵐ[h.trans ⟨t⟩] 𝟙 Z :=
begin
  rcases h,
  rw coherent_comp_constructor _ _ (monoidal_hom.comp h t),
  simp [coherent_comp_constructor],
end

lemma monoidal_to_hom_coherent_comp {W X Y Z : C} (t : monoidal_hom W X) {h : X =ᵐ Y} (f : Y ⟶ Z) :
  monoidal_to_hom t ≫ᵐ[h] f = 𝟙 W ≫ᵐ[monoidal_eq.trans ⟨t⟩ h] f :=
begin
  rcases h,
  rw coherent_comp_constructor _ _ (monoidal_hom.comp t h),
  simp [coherent_comp_constructor]
end

@[simp] lemma coherent_comp_α_hom {V W X Y Z : C} (f : V ⟶ W) {h : W =ᵐ (X ⊗ Y) ⊗ Z} :
  f ≫ᵐ[h] (α_ X Y Z).hom = f ≫ᵐ[h.trans ⟨monoidal_hom.α_hom⟩] 𝟙 _ :=
by convert coherent_comp_monoidal_to_hom f monoidal_hom.α_hom

@[simp] lemma α_hom_coherent_comp {V W X Y Z : C} {h : X ⊗ Y ⊗ Z =ᵐ V} (f : V ⟶ W) :
  (α_ X Y Z).hom ≫ᵐ[h] f = 𝟙 _ ≫ᵐ[monoidal_eq.trans ⟨monoidal_hom.α_hom⟩ h] f :=
by convert monoidal_to_hom_coherent_comp monoidal_hom.α_hom f

@[simp] lemma coherent_comp_α_inv {V W X Y Z : C} (f : V ⟶ W) {h : W =ᵐ X ⊗ Y ⊗ Z} :
  f ≫ᵐ[h] (α_ X Y Z).inv = f ≫ᵐ[h.trans ⟨monoidal_hom.α_inv⟩] 𝟙 _ :=
by convert coherent_comp_monoidal_to_hom f monoidal_hom.α_inv

@[simp] lemma α_inv_coherent_comp {V W X Y Z : C} {h : (X ⊗ Y) ⊗ Z =ᵐ V} (f : V ⟶ W) :
  (α_ X Y Z).inv ≫ᵐ[h] f = 𝟙 _ ≫ᵐ[monoidal_eq.trans ⟨monoidal_hom.α_inv⟩ h] f :=
by convert monoidal_to_hom_coherent_comp monoidal_hom.α_inv f

@[simp] lemma coherent_comp_id_tensor_α_hom {U V W X Y Z : C} (f : U ⟶ V)
  {h : V =ᵐ W ⊗ ((X ⊗ Y) ⊗ Z)} :
  f ≫ᵐ[h] ((𝟙 W) ⊗ (α_ _ _ _).hom) =
    f ≫ᵐ[h.trans (monoidal_eq.tensor ⟨monoidal_hom.id⟩ ⟨monoidal_hom.α_hom⟩)] 𝟙 _ :=
by convert coherent_comp_monoidal_to_hom f (monoidal_hom.tensor monoidal_hom.id monoidal_hom.α_hom)

@[simp] lemma coherent_comp_α_hom_tensor_id {U V W X Y Z : C} (f : U ⟶ V)
  {h : V =ᵐ ((X ⊗ Y) ⊗ Z) ⊗ W} :
  f ≫ᵐ[h] ((α_ _ _ _).hom ⊗ (𝟙 W)) =
    f ≫ᵐ[h.trans (monoidal_eq.tensor ⟨monoidal_hom.α_hom⟩ ⟨monoidal_hom.id⟩)] 𝟙 _ :=
by convert coherent_comp_monoidal_to_hom f (monoidal_hom.tensor monoidal_hom.α_hom monoidal_hom.id)

@[simp] lemma id_tensor_α_hom_coherent_comp {U V W X Y Z : C} {h : U ⊗ (V ⊗ W ⊗ X) =ᵐ Y} (f : Y ⟶ Z) :
  ((𝟙 U) ⊗ (α_ _ _ _).hom) ≫ᵐ[h] f =
    𝟙 _ ≫ᵐ[(monoidal_eq.tensor ⟨monoidal_hom.id⟩ ⟨monoidal_hom.α_hom⟩).trans h] f :=
by convert monoidal_to_hom_coherent_comp (monoidal_hom.tensor monoidal_hom.id monoidal_hom.α_hom) f

@[simp] lemma α_hom_tensor_id_coherent_comp {U V W X Y Z : C} {h : (V ⊗ W ⊗ X) ⊗ U =ᵐ Y} (f : Y ⟶ Z) :
  ((α_ _ _ _).hom ⊗ (𝟙 U)) ≫ᵐ[h] f =
    𝟙 _ ≫ᵐ[(monoidal_eq.tensor ⟨monoidal_hom.α_hom⟩ ⟨monoidal_hom.id⟩).trans h] f :=
by convert monoidal_to_hom_coherent_comp (monoidal_hom.tensor monoidal_hom.α_hom monoidal_hom.id) f

@[simp] lemma coherent_comp_id_tensor_α_inv {U V W X Y Z : C} (f : U ⟶ V)
  {h : V =ᵐ W ⊗ (X ⊗ Y ⊗ Z)} :
  f ≫ᵐ[h] ((𝟙 W) ⊗ (α_ _ _ _).inv) =
    f ≫ᵐ[h.trans (monoidal_eq.tensor ⟨monoidal_hom.id⟩ ⟨monoidal_hom.α_inv⟩)] 𝟙 _ :=
by convert coherent_comp_monoidal_to_hom f (monoidal_hom.tensor monoidal_hom.id monoidal_hom.α_inv)

@[simp] lemma coherent_comp_α_inv_tensor_id {U V W X Y Z : C} (f : U ⟶ V)
  {h : V =ᵐ (X ⊗ Y ⊗ Z) ⊗ W} :
  f ≫ᵐ[h] ((α_ _ _ _).inv ⊗ (𝟙 W)) =
    f ≫ᵐ[h.trans (monoidal_eq.tensor ⟨monoidal_hom.α_inv⟩ ⟨monoidal_hom.id⟩)] 𝟙 _ :=
by convert coherent_comp_monoidal_to_hom f (monoidal_hom.tensor monoidal_hom.α_inv monoidal_hom.id)

@[simp] lemma id_tensor_α_inv_coherent_comp {U V W X Y Z : C} {h : U ⊗ ((V ⊗ W) ⊗ X) =ᵐ Y} (f : Y ⟶ Z) :
  ((𝟙 U) ⊗ (α_ _ _ _).inv) ≫ᵐ[h] f =
    𝟙 _ ≫ᵐ[(monoidal_eq.tensor ⟨monoidal_hom.id⟩ ⟨monoidal_hom.α_inv⟩).trans h] f :=
by convert monoidal_to_hom_coherent_comp (monoidal_hom.tensor monoidal_hom.id monoidal_hom.α_inv) f

@[simp] lemma α_inv_tensor_id_coherent_comp {U V W X Y Z : C} {h : ((V ⊗ W) ⊗ X) ⊗ U =ᵐ Y} (f : Y ⟶ Z) :
  ((α_ _ _ _).inv ⊗ (𝟙 U)) ≫ᵐ[h] f =
    𝟙 _ ≫ᵐ[(monoidal_eq.tensor ⟨monoidal_hom.α_inv⟩ ⟨monoidal_hom.id⟩).trans h] f :=
by convert monoidal_to_hom_coherent_comp (monoidal_hom.tensor monoidal_hom.α_inv monoidal_hom.id) f

lemma coherent_reassoc {U V W X Y : C} {f : U ⟶ V} {g : V ⟶ W} {fg : U ⟶ W}
  (q : f ≫ g = fg) (k : X ⟶ Y) {h₁} :
  f ≫ (g ≫ᵐ[h₁] k) = fg ≫ᵐ[h₁] k :=
by rw [comp_eq_coherent_comp, ←coherent_assoc, ←comp_eq_coherent_comp, q]

@[simp] lemma associate_morphisms {S₁ S₂ T₁ T₂ U V W X Y Z : C} {f : U ⟶ V} {g : W ⟶ X} {h : Y ⟶ Z}
  {k₁ : S₁ ⟶ T₁} {k₂ : S₂ ⟶ T₂} (h₁ : _) (h₂ : _) :
  k₁ ≫ᵐ[h₁] (((f ⊗ g) ⊗ h) ≫ᵐ[h₂] k₂) =
    k₁ ≫ᵐ[h₁.trans ⟨monoidal_hom.α_hom⟩] ((f ⊗ g ⊗ h) ≫ᵐ[monoidal_eq.trans ⟨monoidal_hom.α_inv⟩ h₂] k₂) :=
begin
  have := associator_naturality f g h,
  rw ←(α_ V X Z).eq_comp_inv at this,
  simp [this, comp_eq_coherent_comp],
end

@[simp] lemma tensor_id_assoc {S₁ S₂ T₁ T₂ U V X Y : C} {f : U ⟶ V}
  {k₁ : S₁ ⟶ T₁} {k₂ : S₂ ⟶ T₂} (h₁ h₂) :
  k₁ ≫ᵐ[h₁] ((𝟙 X ⊗ 𝟙 Y ⊗ f) ≫ᵐ[h₂] k₂) =
    k₁ ≫ᵐ[h₁.trans ⟨monoidal_hom.α_inv⟩] ((𝟙 (X ⊗ Y) ⊗ f) ≫ᵐ[monoidal_eq.trans ⟨monoidal_hom.α_hom⟩ h₂] k₂) :=
by rw [←associate_morphisms, tensor_id]

end category_theory
