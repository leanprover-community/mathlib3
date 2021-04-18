import category_theory.monoidal.braided
import category_theory.reflects_isomorphisms
import category_theory.monoidal.End

open category_theory
open category_theory.monoidal_category

universes v v₁ v₂ v₃ u u₁ u₂ u₃
noncomputable theory

namespace category_theory

variables (C : Type u₁) [category.{v₁} C] [monoidal_category C]

inductive monoidal_obj : Type u₁
| of : C → monoidal_obj
| unit : monoidal_obj
| tensor : monoidal_obj → monoidal_obj → monoidal_obj

variables {C}

def monoidal_obj.to : monoidal_obj C → C
| (monoidal_obj.of X) := X
| (monoidal_obj.unit) := 𝟙_ C
| (monoidal_obj.tensor X Y) := X.to ⊗ Y.to

inductive monoidal_hom : monoidal_obj C → monoidal_obj C → Type u₁
| id {X} : monoidal_hom X X
| α_hom {X Y Z : monoidal_obj C} : monoidal_hom ((X.tensor Y).tensor Z) (X.tensor (Y.tensor Z))
| α_inv {X Y Z} : monoidal_hom (monoidal_obj.tensor X (monoidal_obj.tensor Y Z)) (monoidal_obj.tensor (monoidal_obj.tensor X Y) Z)
| l_hom {X} : monoidal_hom (monoidal_obj.tensor monoidal_obj.unit X) X
| l_inv {X} : monoidal_hom X (monoidal_obj.tensor monoidal_obj.unit X)
| ρ_hom {X} : monoidal_hom (monoidal_obj.tensor X monoidal_obj.unit) X
| ρ_inv {X} : monoidal_hom X (monoidal_obj.tensor X monoidal_obj.unit)
| comp {X Y Z} (f : monoidal_hom X Y) (g : monoidal_hom Y Z) : monoidal_hom X Z
| tensor {W X Y Z} (f : monoidal_hom W Y) (g : monoidal_hom X Z) : monoidal_hom (monoidal_obj.tensor W X) (monoidal_obj.tensor Y Z)

@[simp] def monoidal_to_hom : ∀ {X Y : monoidal_obj C}, monoidal_hom X Y → (X.to ⟶ Y.to)
| _ _ monoidal_hom.id := 𝟙 _
| _ _ monoidal_hom.α_hom := (α_ _ _ _).hom
| _ _ monoidal_hom.α_inv := (α_ _ _ _).inv
| _ _ monoidal_hom.l_hom := (λ_ _).hom
| _ _ monoidal_hom.l_inv := (λ_ _).inv
| _ _ monoidal_hom.ρ_hom := (ρ_ _).hom
| _ _ monoidal_hom.ρ_inv := (ρ_ _).inv
| _ _ (monoidal_hom.comp f g) := monoidal_to_hom f ≫ monoidal_to_hom g
| _ _ (monoidal_hom.tensor f g) := monoidal_to_hom f ⊗ monoidal_to_hom g

instance monoidal_to_hom_is_iso : ∀ {X Y : monoidal_obj C} (h : monoidal_hom X Y), is_iso (monoidal_to_hom h)
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

section
/-local attribute [instance] endofunctor_monoidal_category
local attribute [reducible] endofunctor_monoidal_category
local attribute [ext] functor.ext

theorem endofunctor_coherence' {X Y : C ⥤ C} (h : monoidal_hom X Y) :
  Σ' (p : X = Y), monoidal_to_hom h = eq_to_hom p :=
begin
  induction h; dsimp [monoidal_to_hom]; tidy; simp *,
end.

theorem endofunctor_coherence {X Y : C ⥤ C} (h h' : monoidal_hom X Y) :
  monoidal_to_hom h = monoidal_to_hom h' :=
begin
  obtain ⟨p, w⟩ := endofunctor_coherence' h,
  obtain ⟨p', w'⟩ := endofunctor_coherence' h',
  rw [w, w'],
end

theorem coherence_of_faithful {D : Type u₂} [category.{v₂} D] [monoidal_category D]
  (F : monoidal_functor C D)
  (coh : ∀ {X Y : D} (h h' : monoidal_hom X Y), monoidal_to_hom h = monoidal_to_hom h') :
  ∀ {X Y : C} (h h' : monoidal_hom X Y), monoidal_to_hom h = monoidal_to_hom h' :=
sorry-/

-- The monoidal coherence theorem!
theorem coherence {X Y : monoidal_obj C} (h h' : monoidal_hom X Y) : monoidal_to_hom h = monoidal_to_hom h' :=
sorry

end

/- We don't use `nonempty` here because `nonempty` is a class and we don't want a class here. -/
inductive monoidal_eq (X Y : monoidal_obj C) : Prop
| intro (h : monoidal_hom X Y) : monoidal_eq

infixr ` =ᵐ `:50 := monoidal_eq

lemma nonempty_of_monoidal_eq {X Y : monoidal_obj C} : X =ᵐ Y → nonempty (monoidal_hom X Y) :=
λ ⟨h⟩, ⟨h⟩

lemma monoidal_eq.trans {X Y Z : monoidal_obj C} : X =ᵐ Y → Y =ᵐ Z → X =ᵐ Z :=
λ ⟨h⟩ ⟨h'⟩, ⟨monoidal_hom.comp h h'⟩

lemma monoidal_eq.tensor {W X Y Z : monoidal_obj C} : W =ᵐ X → Y =ᵐ Z → W.tensor Y =ᵐ X.tensor Z :=
λ ⟨h⟩ ⟨h'⟩, ⟨monoidal_hom.tensor h h'⟩

def hom_of_monoidal_eq {X Y : monoidal_obj C} (h : X =ᵐ Y) : X.to ⟶ Y.to :=
monoidal_to_hom (classical.choice (nonempty_of_monoidal_eq h))

lemma hom_of_monoidal_eq_eq {X Y : monoidal_obj C} {h : X =ᵐ Y} (h' : monoidal_hom X Y) :
  hom_of_monoidal_eq h = monoidal_to_hom h' :=
coherence _ _

/- The reason why we choose the convoluted setup above is that this is true definitionally. -/
example {X Y : monoidal_obj C} (h h' : X =ᵐ Y) : hom_of_monoidal_eq h = hom_of_monoidal_eq h' :=
rfl

def coherent_comp {W X Y Z : C} {X' Y' : monoidal_obj C} (h : X' =ᵐ Y')
  (hX : X = X'.to) (hY : Y = Y'.to) (f : W ⟶ X) (g : Y ⟶ Z) : W ⟶ Z :=
f ≫ eq_to_hom hX ≫ hom_of_monoidal_eq h ≫ eq_to_hom hY.symm ≫ g

meta def _root_.tactic.coherence_assumption : tactic unit :=
`[assumption <|> simp only [monoidal_obj.to]]

meta def _root_.tactic.interactive.coherence_assumption : tactic unit :=
tactic.coherence_assumption

notation f ` ≫ᵐ[`:80 h:80 `] `:0 g:80 := coherent_comp h (by coherence_assumption) (by coherence_assumption) f g
notation f ` ≫ᵐ[`:80 h:80 `, ` i:80 `, ` j:80 `]' `:0 g:80 := coherent_comp h i j f g -- I hope we never need this
--notation f ` ≫ᵐ[`:80 h:80 `]' `:0 g:80 := coherent_comp h _ _ f g
infixr ` ≫ᵐ `:80 := coherent_comp _ _ _

lemma coherent_comp_constructor {W X Y Z : C} {X' Y' : monoidal_obj C} (f : W ⟶ X) (g : Y ⟶ Z)
  (h : monoidal_hom X' Y') (hX : X = X'.to) (hY : Y = Y'.to) :
  f ≫ᵐ[⟨h⟩] g = f ≫ eq_to_hom hX ≫ monoidal_to_hom h ≫ eq_to_hom hY.symm ≫ g :=
by rw [coherent_comp, hom_of_monoidal_eq_eq h]

lemma comp_eq_coherent_comp {X Y Z : C} (Y' : monoidal_obj C)
  (h : Y = Y'.to . tactic.coherence_assumption) (f : X ⟶ Y) (g : Y ⟶ Z) :
  f ≫ g = f ≫ᵐ[⟨monoidal_hom.id⟩] g :=
by simp [coherent_comp_constructor]

@[simp] lemma coherent_assoc {U V W X Y Z : C} {V' W' X' Y' : monoidal_obj C}
  (f : U ⟶ V) {h : V' =ᵐ W'} (g : W ⟶ X) {h' : X' =ᵐ Y'} (i : Y ⟶ Z) (hV : V = V'.to)
  (hW : W = W'.to) (hX : X = X'.to) (hY : Y = Y'.to) :
  (f ≫ᵐ[h] g) ≫ᵐ[h'] i = f ≫ᵐ[h] (g ≫ᵐ[h'] i) :=
by { rcases h, rcases h', simp [coherent_comp_constructor] }

@[simp] lemma coherent_comp_id_coherent_comp {V W X Y Z : C} {W' X' Y' : monoidal_obj C} (f : V ⟶ W)
  {h : W' =ᵐ X'} {h' : X' =ᵐ Y'} (g : Y ⟶ Z)
  (hW : W = W'.to)
  (hX : X = X'.to)
  (hY : Y = Y'.to) :
  f ≫ᵐ[h, hW, hX]' 𝟙 X ≫ᵐ[h'] g = f ≫ᵐ[h.trans h', hW, hY]' g :=
begin
  cases h,
  cases h',
  rw coherent_comp_constructor _ _ (monoidal_hom.comp h h'),
  simp [coherent_comp, hom_of_monoidal_eq_eq h, hom_of_monoidal_eq_eq h']
end

@[simp] lemma coherent_comp_id_coherent_comp' {V W : C} (X : C) {Y Z : C} {W' X' Y' : monoidal_obj C} (f : V ⟶ W)
  {h : W' =ᵐ X'} {h' : X' =ᵐ Y'} (g : Y ⟶ Z)
  (hW : W = W'.to)
  (hX : X = X'.to)
  (hY : Y = Y'.to) :
  f ≫ᵐ[h] (𝟙 X ≫ᵐ[h'] g) = f ≫ᵐ[h.trans h'] g :=
by rw [←coherent_assoc, coherent_comp_id_coherent_comp]

/- Can these even be stated in the new setup? -/
/-lemma coherent_comp_monoidal_to_hom {W X Y Z : monoidal_obj C} (f : W.to ⟶ X.to) {h : X =ᵐ Y}
  (t : monoidal_hom Y Z) : f ≫ᵐ[h] monoidal_to_hom t = f ≫ᵐ[h.trans ⟨t⟩] 𝟙 Z.to :=
begin
  rcases h,
  rw coherent_comp_constructor _ _ (monoidal_hom.comp h t),
  simp [coherent_comp_constructor],
end

lemma monoidal_to_hom_coherent_comp {W X Y Z : monoidal_obj C} (t : monoidal_hom W X) {h : X =ᵐ Y}
  (f : Y.to ⟶ Z.to) : monoidal_to_hom t ≫ᵐ[h] f = 𝟙 W.to ≫ᵐ[monoidal_eq.trans ⟨t⟩ h] f :=
begin
  rcases h,
  rw coherent_comp_constructor _ _ (monoidal_hom.comp t h),
  simp [coherent_comp_constructor]
end-/

@[simp] lemma coherent_comp_α_hom {V W X Y Z : C} {W' X' Y' Z' : monoidal_obj C} (f : V ⟶ W)
  {h : W' =ᵐ (X'.tensor Y').tensor Z'}
  (hW : W = W'.to . tactic.coherence_assumption)
  (hX : X = X'.to . tactic.coherence_assumption)
  (hY : Y = Y'.to . tactic.coherence_assumption)
  (hZ : Z = Z'.to . tactic.coherence_assumption)
  -- the next two are redundant, but the coherence_assumption tactic is too weak to know this
  -- actually, they aren't so redundant after all, they guide `rw`.
  (hXYZ : (X ⊗ Y) ⊗ Z = (X'.to ⊗ Y'.to) ⊗ Z'.to . tactic.coherence_assumption)
  (hXYZ' : X ⊗ Y ⊗ Z = X'.to ⊗ Y'.to ⊗ Z'.to . tactic.coherence_assumption) :
  f ≫ᵐ[h] (α_ X Y Z).hom = f ≫ᵐ[h.trans ⟨monoidal_hom.α_hom⟩] 𝟙 _ :=
begin
  rcases h,
  rw coherent_comp_constructor _ _ (h.comp monoidal_hom.α_hom),
  cases hX, cases hY, cases hZ,
  simp [coherent_comp_constructor]
end

@[simp] lemma coherent_comp_α_inv {V W X Y Z : C} {W' X' Y' Z' : monoidal_obj C} (f : V ⟶ W)
  {h : W' =ᵐ X'.tensor (Y'.tensor Z') }
  (hW : W = W'.to . tactic.coherence_assumption)
  (hX : X = X'.to . tactic.coherence_assumption)
  (hY : Y = Y'.to . tactic.coherence_assumption)
  (hZ : Z = Z'.to . tactic.coherence_assumption)
  -- the next two are redundant, but the coherence_assumption tactic is too weak to know this
  -- actually, they aren't so redundant after all? The `assumption` in `tactic.coherence_assumption`
  -- instantiates metavariables, so it tells `≫ᵐ` what to do.
  (hXYZ : (X ⊗ Y) ⊗ Z = (X'.to ⊗ Y'.to) ⊗ Z'.to . tactic.coherence_assumption)
  (hXYZ' : X ⊗ Y ⊗ Z = X'.to ⊗ Y'.to ⊗ Z'.to . tactic.coherence_assumption) :
  f ≫ᵐ[h] (α_ X Y Z).inv = f ≫ᵐ[h.trans ⟨monoidal_hom.α_inv⟩] 𝟙 _ :=
begin
  rcases h,
  rw coherent_comp_constructor _ _ (h.comp monoidal_hom.α_inv),
  cases hX, cases hY, cases hZ,
  simp [coherent_comp_constructor]
end

@[simp] lemma α_hom_coherent_comp {V W X Y Z : C} {W' X' Y' Z' : monoidal_obj C} (f : W ⟶ V)
  {h : X'.tensor (Y'.tensor Z') =ᵐ W' }
  (hW : W = W'.to . tactic.coherence_assumption)
  (hX : X = X'.to . tactic.coherence_assumption)
  (hY : Y = Y'.to . tactic.coherence_assumption)
  (hZ : Z = Z'.to . tactic.coherence_assumption)
  (hXYZ : (X ⊗ Y) ⊗ Z = (X'.to ⊗ Y'.to) ⊗ Z'.to . tactic.coherence_assumption)
  (hXYZ' : X ⊗ Y ⊗ Z = X'.to ⊗ Y'.to ⊗ Z'.to . tactic.coherence_assumption) :
  (α_ X Y Z).hom ≫ᵐ[h] f = 𝟙 _ ≫ᵐ[monoidal_eq.trans ⟨monoidal_hom.α_hom⟩ h] f :=
begin
  rcases h,
  rw coherent_comp_constructor _ _ (monoidal_hom.α_hom.comp h),
  cases hX, cases hY, cases hZ,
  simp [coherent_comp_constructor]
end

@[simp] lemma α_inv_coherent_comp {V W X Y Z : C} {W' X' Y' Z' : monoidal_obj C} (f : W ⟶ V)
  {h : (X'.tensor Y').tensor Z' =ᵐ W' }
  (hW : W = W'.to . tactic.coherence_assumption)
  (hX : X = X'.to . tactic.coherence_assumption)
  (hY : Y = Y'.to . tactic.coherence_assumption)
  (hZ : Z = Z'.to . tactic.coherence_assumption)
  (hXYZ : (X ⊗ Y) ⊗ Z = (X'.to ⊗ Y'.to) ⊗ Z'.to . tactic.coherence_assumption)
  (hXYZ' : X ⊗ Y ⊗ Z = X'.to ⊗ Y'.to ⊗ Z'.to . tactic.coherence_assumption) :
  (α_ X Y Z).inv ≫ᵐ[h] f = 𝟙 _ ≫ᵐ[monoidal_eq.trans ⟨monoidal_hom.α_inv⟩ h] f :=
begin
  rcases h,
  rw coherent_comp_constructor _ _ (monoidal_hom.α_inv.comp h),
  cases hX, cases hY, cases hZ,
  simp [coherent_comp_constructor]
end

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

lemma coherent_reassoc {U V W X Y : C} {W' X' : monoidal_obj C} {f : U ⟶ V} {g : V ⟶ W} {fg : U ⟶ W}
  (q : f ≫ g = fg) (k : X ⟶ Y) {h₁ : W' =ᵐ X'} (hW : W = W'.to) (hX : X = X'.to) :
  f ≫ (g ≫ᵐ[h₁] k) = fg ≫ᵐ[h₁] k :=
have V = (monoidal_obj.of V).to, by refl,
by rw [comp_eq_coherent_comp, ←coherent_assoc, ←comp_eq_coherent_comp, q]

@[simp] lemma associate_morphisms {S₁ S₂ T₁ T₂ U V W X Y Z : C}
  {U' V' W' X' Y' Z' T₁' S₂' : monoidal_obj C}
  (hU : U = U'.to . tactic.coherence_assumption)
  (hV : V = V'.to . tactic.coherence_assumption)
  (hW : W = W'.to . tactic.coherence_assumption)
  (hX : X = X'.to . tactic.coherence_assumption)
  (hY : Y = Y'.to . tactic.coherence_assumption)
  (hZ : Z = Z'.to . tactic.coherence_assumption)
  (hT₁ : T₁ = T₁'.to . tactic.coherence_assumption)
  (hS₂ : S₂ = S₂'.to . tactic.coherence_assumption)
  (hUWY : ((U ⊗ W) ⊗ Y) = ((U'.tensor W').tensor Y').to . tactic.coherence_assumption)
  (hUWY' : (U ⊗ W ⊗ Y) = (U'.tensor (W'.tensor Y')).to . tactic.coherence_assumption)
  (hVXZ : ((V ⊗ X) ⊗ Z) = ((V'.tensor X').tensor Z').to . tactic.coherence_assumption)
  (hVXZ' : (V ⊗ X ⊗ Z) = (V'.tensor (X'.tensor Z')).to . tactic.coherence_assumption)
  {f : U ⟶ V} {g : W ⟶ X} {h : Y ⟶ Z}
  {k₁ : S₁ ⟶ T₁} {k₂ : S₂ ⟶ T₂} (h₁ : T₁' =ᵐ (U'.tensor W').tensor Y') (h₂ : (V'.tensor X').tensor Z' =ᵐ S₂') :
  k₁ ≫ᵐ[h₁] (((f ⊗ g) ⊗ h : (U ⊗ W) ⊗ Y ⟶ _) ≫ᵐ[h₂] k₂) =
    k₁ ≫ᵐ[h₁.trans ⟨monoidal_hom.α_hom⟩] ((f ⊗ g ⊗ h : _ ⟶ _) ≫ᵐ[monoidal_eq.trans ⟨monoidal_hom.α_inv⟩ h₂] k₂) :=
begin
  have := associator_naturality f g h,
  rw ←(α_ V X Z).eq_comp_inv at this,
  rw [this, comp_eq_coherent_comp, comp_eq_coherent_comp],
  simp, -- interesting: sequeeze_simp fails
end

@[simp] lemma tensor_id_assoc {S₁ S₂ T₁ T₂ U V X Y : C} {U' V' X' Y' T₁' S₂' : monoidal_obj C} {f : U ⟶ V}
  {k₁ : S₁ ⟶ T₁} {k₂ : S₂ ⟶ T₂}
  (hU : U = U'.to . tactic.coherence_assumption)
  (hV : V = V'.to . tactic.coherence_assumption)
  (hX : X = X'.to . tactic.coherence_assumption)
  (hY : Y = Y'.to . tactic.coherence_assumption)
  (hT₁ : T₁ = T₁'.to . tactic.coherence_assumption)
  (hS₂ : S₂ = S₂'.to . tactic.coherence_assumption)
  (hXYU : (X ⊗ Y ⊗ U) = (X'.tensor (Y'.tensor U')).to . tactic.coherence_assumption)
  (hXYV : (X ⊗ Y ⊗ V) = (X'.tensor (Y'.tensor V')).to . tactic.coherence_assumption)
  (hXYU' : ((X ⊗ Y) ⊗ U) = ((X'.tensor Y').tensor U').to . tactic.coherence_assumption)
  (hXYV' : ((X ⊗ Y) ⊗ V) = ((X'.tensor Y').tensor V').to . tactic.coherence_assumption)
  (h₁ : T₁' =ᵐ (X'.tensor (Y'.tensor U'))) (h₂ : (X'.tensor (Y'.tensor V')) =ᵐ S₂'):
  k₁ ≫ᵐ[h₁] ((𝟙 X ⊗ 𝟙 Y ⊗ f) ≫ᵐ[h₂] k₂) =
    k₁ ≫ᵐ[h₁.trans ⟨monoidal_hom.α_inv⟩] ((𝟙 (X ⊗ Y) ⊗ f) ≫ᵐ[monoidal_eq.trans ⟨monoidal_hom.α_hom⟩ h₂] k₂) :=
by rw [←associate_morphisms, tensor_id]

end category_theory
