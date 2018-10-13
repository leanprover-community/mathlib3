-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Reid Barton, Mario Carneiro

import category_theory.limits.shape

open category_theory

namespace category_theory.limits

universes u v w

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

section binary_product
structure is_binary_product {Y Z : C} (t : span Y Z) :=
(lift : ∀ (s : span Y Z), s.X ⟶ t.X)
(fac₁' : ∀ (s : span Y Z), (lift s) ≫ t.π₁ = s.π₁ . obviously)
(fac₂' : ∀ (s : span Y Z), (lift s) ≫ t.π₂ = s.π₂ . obviously)
(uniq' : ∀ (s : span Y Z) (m : s.X ⟶ t.X) (w₁ : m ≫ t.π₁ = s.π₁) (w₂ : m ≫ t.π₂ = s.π₂), m = lift s . obviously)

restate_axiom is_binary_product.fac₁'
attribute [simp] is_binary_product.fac₁
restate_axiom is_binary_product.fac₂'
attribute [simp] is_binary_product.fac₂
restate_axiom is_binary_product.uniq'

@[extensionality] lemma is_binary_product.ext {Y Z : C} {t : span Y Z} (P Q : is_binary_product t) : P = Q :=
begin
  tactic.unfreeze_local_instances,
  cases P, cases Q,
  congr,
  ext1,
  exact eq.symm (P_uniq' x (Q_lift x) (Q_fac₁' x) (Q_fac₂' x))
end

instance subsingleton_is_binary_product {Y Z : C} {t : span Y Z} : subsingleton (is_binary_product t) := by obviously

lemma is_binary_product.uniq'' {Y Z : C} {t : span Y Z} (h : is_binary_product t) {X' : C} (m : X' ⟶ t.X) :
  m = h.lift { X := X', π₁ := m ≫ t.π₁, π₂ := m ≫ t.π₂ } :=
h.uniq { X := X', π₁ := m ≫ t.π₁, π₂ := m ≫ t.π₂ } m rfl rfl

lemma is_binary_product.univ
  {Y Z : C} {t : span Y Z} (h : is_binary_product t) (s : span Y Z) (φ : s.X ⟶ t.X) :
  (φ ≫ t.π₁ = s.π₁ ∧ φ ≫ t.π₂ = s.π₂) ↔ (φ = h.lift s) :=
⟨ λ a, is_binary_product.uniq h s φ a.1 a.2,
  λ a, ⟨ by rw [a, is_binary_product.fac₁],
         by rw [a, is_binary_product.fac₂] ⟩ ⟩

def is_binary_product.of_lift_univ {Y Z : C} {t : span Y Z}
  (lift : Π (s : span Y Z), s.X ⟶ t.X)
  (univ : Π (s : span Y Z) (φ : s.X ⟶ t.X), (φ ≫ t.π₁ = s.π₁ ∧ φ ≫ t.π₂ = s.π₂) ↔ (φ = lift s)) :
  is_binary_product t :=
{ lift := lift,
  fac₁' := λ s, ((univ s (lift s)).mpr (eq.refl (lift s))).left,
  fac₂' := λ s, ((univ s (lift s)).mpr (eq.refl (lift s))).right,
  uniq' := λ s m w₁ w₂, ((univ s m).mp ⟨w₁, w₂⟩) }

end binary_product

section binary_coproduct
structure is_binary_coproduct {Y Z : C} (t : cospan Y Z) :=
(desc : ∀ (s : cospan Y Z), t.X ⟶ s.X)
(fac₁' : ∀ (s : cospan Y Z), t.ι₁ ≫ (desc s) = s.ι₁ . obviously)
(fac₂' : ∀ (s : cospan Y Z), t.ι₂ ≫ (desc s) = s.ι₂ . obviously)
(uniq' : ∀ (s : cospan Y Z) (m : t.X ⟶ s.X) (w₁ : t.ι₁ ≫ m = s.ι₁) (w₂ : t.ι₂ ≫ m = s.ι₂), m = desc s . obviously)

restate_axiom is_binary_coproduct.fac₁'
attribute [simp] is_binary_coproduct.fac₁
restate_axiom is_binary_coproduct.fac₂'
attribute [simp] is_binary_coproduct.fac₂
restate_axiom is_binary_coproduct.uniq'

@[extensionality] lemma is_binary_coproduct.ext {Y Z : C} {t : cospan Y Z} (P Q : is_binary_coproduct t) : P = Q :=
begin
  tactic.unfreeze_local_instances,
  cases P, cases Q,
  congr,
  ext1,
  exact eq.symm (P_uniq' x (Q_desc x) (Q_fac₁' x) (Q_fac₂' x))
end

instance subsingleton_is_binary_coproduct {Y Z : C} {t : cospan Y Z} : subsingleton (is_binary_coproduct t) := by obviously

lemma is_binary_coproduct.uniq'' {Y Z : C} {t : cospan Y Z} (h : is_binary_coproduct t) {X' : C} (m : t.X ⟶ X') :
  m = h.desc { X := X', ι₁ := t.ι₁ ≫ m, ι₂ := t.ι₂ ≫ m } :=
h.uniq { X := X', ι₁ := t.ι₁ ≫ m, ι₂ := t.ι₂ ≫ m } m rfl rfl

lemma is_binary_coproduct.univ
  {Y Z : C} {t : cospan Y Z} (h : is_binary_coproduct t) (s : cospan Y Z) (φ : t.X ⟶ s.X) :
  (t.ι₁ ≫ φ = s.ι₁ ∧ t.ι₂ ≫ φ = s.ι₂) ↔ (φ = h.desc s) :=
⟨ λ a, is_binary_coproduct.uniq h s φ a.1 a.2,
  λ a, ⟨ by rw [a, is_binary_coproduct.fac₁],
         by rw [a, is_binary_coproduct.fac₂] ⟩ ⟩

def is_binary_coproduct.of_desc_univ {Y Z : C} {t : cospan Y Z}
  (desc : Π (s : cospan Y Z), t.X ⟶ s.X)
  (univ : Π (s : cospan Y Z) (φ : t.X ⟶ s.X), (t.ι₁ ≫ φ = s.ι₁ ∧ t.ι₂ ≫ φ = s.ι₂) ↔ (φ = desc s)) :
  is_binary_coproduct t :=
{ desc := desc,
  fac₁' := λ s, ((univ s (desc s)).mpr (eq.refl (desc s))).left,
  fac₂' := λ s, ((univ s (desc s)).mpr (eq.refl (desc s))).right,
  uniq' := λ s m w₁ w₂, ((univ s m).mp ⟨w₁, w₂⟩) }

end binary_coproduct

variable (C)

class has_binary_products :=
(prod    : Π (Y Z : C), span Y Z)
(is_binary_product : Π (Y Z : C), is_binary_product (prod Y Z) . obviously)

class has_binary_coproducts :=
(coprod    : Π (Y Z : C), cospan Y Z)
(is_binary_coproduct : Π (Y Z : C), is_binary_coproduct (coprod Y Z) . obviously)

variable {C}

section
variables [has_binary_products.{u v} C]

def prod.span (Y Z : C) := has_binary_products.prod.{u v} Y Z
def prod (Y Z : C) : C := (prod.span Y Z).X
def prod.π₁ (Y Z : C) : prod Y Z ⟶ Y := (prod.span Y Z).π₁
def prod.π₂ (Y Z : C) : prod Y Z ⟶ Z := (prod.span Y Z).π₂
def prod.universal_property (Y Z : C) : is_binary_product (prod.span Y Z) :=
has_binary_products.is_binary_product.{u v} C Y Z

def prod.lift {P Q R : C} (f : P ⟶ Q) (g : P ⟶ R) : P ⟶ (prod Q R) :=
(prod.universal_property Q R).lift ⟨ ⟨ P ⟩, f, g ⟩

@[simp] lemma prod.lift_π₁ {P Q R : C} (f : P ⟶ Q) (g : P ⟶ R) :
  prod.lift f g ≫ prod.π₁ Q R = f :=
is_binary_product.fac₁ _ { X := P, π₁ := f, π₂ := g }
@[simp] lemma prod.lift_π₂ {P Q R : C} (f : P ⟶ Q) (g : P ⟶ R) :
  prod.lift f g ≫ prod.π₂ Q R = g :=
is_binary_product.fac₂ _ { X := P, π₁ := f, π₂ := g }

def prod.map {P Q R S : C} (f : P ⟶ Q) (g : R ⟶ S) : (prod P R) ⟶ (prod Q S) :=
prod.lift (prod.π₁ P R ≫ f) (prod.π₂ P R ≫ g)

@[simp] lemma prod.map_π₁ {P Q R S : C} (f : P ⟶ Q) (g : R ⟶ S) :
  prod.map f g ≫ prod.π₁ Q S = prod.π₁ P R ≫ f :=
by erw is_binary_product.fac₁
@[simp] lemma prod.map_π₂ {P Q R S : C} (f : P ⟶ Q) (g : R ⟶ S) :
  prod.map f g ≫ prod.π₂ Q S = prod.π₂ P R ≫ g :=
by erw is_binary_product.fac₂

def prod.swap (P Q : C) : prod P Q ⟶ prod Q P := prod.lift (prod.π₂ P Q) (prod.π₁ P Q)

@[simp] lemma prod.swap_π₁ (P Q : C) : prod.swap P Q ≫ prod.π₁ Q P = prod.π₂ P Q :=
by erw is_binary_product.fac₁
@[simp] lemma prod.swap_π₂ (P Q : C) : prod.swap P Q ≫ prod.π₂ Q P = prod.π₁ P Q :=
by erw is_binary_product.fac₂

section
variables {D : Type u} [𝒟 : category.{u v} D] [has_binary_products.{u v} D]
include 𝒟

def prod.post (P Q : C) (G : C ⥤ D) : G (prod P Q) ⟶ (prod (G P) (G Q)) :=
@is_binary_product.lift _ _ _ _ (prod.span (G P) (G Q)) (prod.universal_property _ _)
  { X := _, π₁ := G.map (prod.π₁ P Q), π₂ := G.map (prod.π₂ P Q) }

@[simp] lemma prod.post_π₁ (P Q : C) (G : C ⥤ D) :
  prod.post P Q G ≫ prod.π₁ (G P) (G Q) = G.map (prod.π₁ P Q) :=
by erw is_binary_product.fac₁
@[simp] lemma prod.post_π₂ (P Q : C) (G : C ⥤ D) :
  prod.post P Q G ≫ prod.π₂ (G P) (G Q) = G.map (prod.π₂ P Q) :=
by erw is_binary_product.fac₂
end

@[extensionality] lemma prod.hom_ext (Y Z : C) (X : C)
  (f g : X ⟶ prod Y Z)
  (w₁ : f ≫ prod.π₁ Y Z = g ≫ prod.π₁ Y Z)
  (w₂ : f ≫ prod.π₂ Y Z = g ≫ prod.π₂ Y Z) : f = g :=
begin
  rw (prod.universal_property Y Z).uniq'' f,
  rw (prod.universal_property Y Z).uniq'' g,
  congr ; assumption,
end

@[simp] lemma prod.swap_swap (P Q : C) : prod.swap P Q ≫ prod.swap Q P = 𝟙 _ :=
by obviously

@[simp] lemma prod.lift_swap {P Q R : C} (f : P ⟶ Q) (g : P ⟶ R) :
  prod.lift g f ≫ prod.swap R Q = prod.lift f g :=
by obviously

lemma prod.swap_map {P Q R S : C} (f : P ⟶ Q) (g : R ⟶ S) :
  prod.swap P R ≫ prod.map g f = prod.map f g ≫ prod.swap Q S :=
begin
/- `obviously` says -/
ext1,
{ simp,
  rw [←category.assoc, ←prod.swap_π₁] },
{ simp,
  rw [←category.assoc, ←prod.swap_π₂] }
end

@[simp] lemma prod.lift_map
  {P Q R S T : C} (f : P ⟶ Q) (g : P ⟶ R) (h : Q ⟶ T) (k : R ⟶ S) :
  prod.lift f g ≫ prod.map h k = prod.lift (f ≫ h) (g ≫ k) :=
begin
  /- `obviously` says -/
  ext1,
  { simp,
    rw [←category.assoc, prod.lift_π₁] },
  { simp,
    rw [←category.assoc, prod.lift_π₂] }
end

@[simp] lemma prod.map_map
  {P Q R S T U : C} (f : P ⟶ Q) (g : R ⟶ S) (h : Q ⟶ T) (k : S ⟶ U) :
  prod.map f g ≫ prod.map h k = prod.map (f ≫ h) (g ≫ k) :=
begin
  /- `obviously` says -/
  ext1,
  { simp,
    rw ←category.assoc,
    erw prod.lift_π₁,
    rw ←category.assoc },
  { simp,
    rw ←category.assoc,
    erw prod.lift_π₂,
    rw ←category.assoc }
end

section
variables {D : Type u} [category.{u v} D] [has_binary_products.{u v} D]

@[simp] lemma prod.lift_post {P Q R : C} (f : P ⟶ Q) (g : P ⟶ R) (G : C ⥤ D) :
  G.map (prod.lift f g) ≫ prod.post Q R G = prod.lift (G.map f) (G.map g) :=
begin
  /- `obviously` says -/
  ext1,
  { simp,
    rw ←functor.map_comp,
    rw prod.lift_π₁ },
  { simp,
    rw ←functor.map_comp,
    rw prod.lift_π₂ }
end.

lemma prod.map_post {Q R S T : C} (h : Q ⟶ S) (k : R ⟶ T) (H : C ⥤ D) :
  H.map (prod.map h k) ≫ prod.post S T H = prod.post Q R H ≫ prod.map (H.map h) (H.map k) :=
begin
  /- `tidy` says -/
  ext1,
  { simp at *,
    rw ←functor.map_comp,
    erw prod.lift_π₁,
    rw ←category.assoc,
    simp, },
  { simp at *,
    rw ←functor.map_comp,
    erw prod.lift_π₂,
    rw ←category.assoc,
    simp, }
end.

lemma prod.swap_post (Q R : C) (G : C ⥤ D) :
  G.map (prod.swap Q R) ≫ prod.post R Q G = prod.post Q R G ≫ prod.swap (G Q) (G R) :=
begin
  /- `obviously` says -/
  ext1,
  { simp,
    rw [←functor.map_comp, ←prod.swap_π₁] },
  { simp,
    rw [←functor.map_comp, ←prod.swap_π₂] }
end.

@[simp] lemma prod.post_post {E : Type u} [category.{u v} E] [has_binary_products.{u v} E]
  (Q R : C) (G : C ⥤ D) (H : D ⥤ E):
  H.map (prod.post Q R G) ≫ prod.post (G Q) (G R) H = prod.post Q R (G ⋙ H) :=
begin
  /- `obviously` says -/
  ext1,
  { simp at *,
    rw ←functor.map_comp,
    erw prod.lift_π₁,
    erw prod.post_π₁,
    simp },
  { simp at *,
    rw ←functor.map_comp,
    erw prod.lift_π₂,
    erw prod.post_π₂,
    simp }
end.
end

end

section
variables [has_binary_coproducts.{u v} C]

def coprod.cospan (Y Z : C) := has_binary_coproducts.coprod.{u v} Y Z
def coprod (Y Z : C) : C := (coprod.cospan Y Z).X
def coprod.ι₁ (Y Z : C) : Y ⟶ coprod Y Z := (coprod.cospan Y Z).ι₁
def coprod.ι₂ (Y Z : C) : Z ⟶ coprod Y Z := (coprod.cospan Y Z).ι₂
def coprod.universal_property (Y Z : C) : is_binary_coproduct (coprod.cospan Y Z) :=
has_binary_coproducts.is_binary_coproduct.{u v} C Y Z

def coprod.desc {P Q R : C} (f : Q ⟶ P) (g : R ⟶ P) : (coprod Q R) ⟶ P :=
(coprod.universal_property Q R).desc ⟨ ⟨ P ⟩, f, g ⟩

def coprod.map {P Q R S : C} (f : P ⟶ Q) (g : R ⟶ S) : (coprod P R) ⟶ (coprod Q S) :=
coprod.desc (f ≫ coprod.ι₁ Q S) (g ≫ coprod.ι₂ Q S)

def coprod.swap (P Q : C) : coprod P Q ⟶ coprod Q P := coprod.desc (coprod.ι₂ Q P) (coprod.ι₁ Q P)

@[simp] lemma coprod.ι₁_desc {P Q R : C} (f : Q ⟶ P) (g : R ⟶ P) : coprod.ι₁ Q R ≫ coprod.desc f g = f :=
is_binary_coproduct.fac₁ _ { X := P, ι₁ := f, ι₂ := g }
@[simp] lemma coprod.ι₂_desc {P Q R : C} (f : Q ⟶ P) (g : R ⟶ P) : coprod.ι₂ Q R ≫ coprod.desc f g = g :=
is_binary_coproduct.fac₂ _ { X := P, ι₁ := f, ι₂ := g }

@[simp] lemma coprod.ι₁_swap (P Q : C) : coprod.ι₁ P Q ≫ coprod.swap P Q = coprod.ι₂ Q P :=
by erw is_binary_coproduct.fac₁.
@[simp] lemma coprod.ι₂_swap (P Q : C) : coprod.ι₂ P Q ≫ coprod.swap P Q = coprod.ι₁ Q P :=
by erw is_binary_coproduct.fac₂.

@[simp] lemma coprod.ι₁_map {P Q R S : C} (f : P ⟶ Q) (g : R ⟶ S) : coprod.ι₁ P R ≫ coprod.map f g = f ≫ coprod.ι₁ Q S :=
by erw is_binary_coproduct.fac₁.
@[simp] lemma coprod.ι₂_map {P Q R S : C} (f : P ⟶ Q) (g : R ⟶ S) : coprod.ι₂ P R ≫ coprod.map f g = g ≫ coprod.ι₂ Q S :=
by erw is_binary_coproduct.fac₂.

section
variables {D : Type u} [𝒟 : category.{u v} D] [has_binary_coproducts.{u v} D]
include 𝒟

def coprod.post (P Q : C) (G : C ⥤ D) : (coprod (G P) (G Q)) ⟶ G (coprod P Q) :=
@is_binary_coproduct.desc _ _ _ _ (coprod.cospan (G P) (G Q)) (coprod.universal_property _ _)
  { X := _, ι₁ := G.map (coprod.ι₁ P Q), ι₂ := G.map (coprod.ι₂ P Q) }

@[simp] lemma coprod.ι₁_post (P Q : C) (G : C ⥤ D) :
  coprod.ι₁ (G P) (G Q) ≫ coprod.post P Q G = G.map (coprod.ι₁ P Q) :=
by erw is_binary_coproduct.fac₁
@[simp] lemma coprod.ι₂_post (P Q : C) (G : C ⥤ D) :
  coprod.ι₂ (G P) (G Q) ≫ coprod.post P Q G = G.map (coprod.ι₂ P Q) :=
by erw is_binary_coproduct.fac₂
end

@[extensionality] lemma coprod.hom_ext (Y Z : C) (X : C)
  (f g : coprod Y Z ⟶ X)
  (w₁ : coprod.ι₁ Y Z ≫ f = coprod.ι₁ Y Z ≫ g)
  (w₂ : coprod.ι₂ Y Z ≫ f = coprod.ι₂ Y Z ≫ g) : f = g :=
begin
  rw (coprod.universal_property Y Z).uniq'' f,
  rw (coprod.universal_property Y Z).uniq'' g,
  congr ; assumption,
end

@[simp] lemma coprod.swap_swap (P Q : C) : coprod.swap P Q ≫ coprod.swap Q P = 𝟙 _ :=
begin
  /- `tidy` says -/
  ext1,
  { simp,
    rw ←category.assoc,
    rw ←coprod.ι₂_swap,
    rw ←coprod.ι₁_swap,
    simp },
  { simp,
    rw ←category.assoc,
    rw ←coprod.ι₁_swap,
    rw ←coprod.ι₂_swap,
    simp }
end.

@[simp] lemma coprod.swap_desc {P Q R : C} (f : Q ⟶ P) (g : R ⟶ P) :
  coprod.swap Q R ≫ coprod.desc g f = coprod.desc f g :=
begin
  /- `obviously` says -/
  ext1,
  { simp,
    rw ←category.assoc,
    simp },
  { simp,
    rw ←category.assoc,
    simp }
end.

lemma coprod.swap_map {P Q R S : C} (f : P ⟶ Q) (g : R ⟶ S) :
  coprod.swap P R ≫ coprod.map g f = coprod.map f g ≫ coprod.swap Q S :=
begin
  /- `obviously` says -/
  ext1,
  { rw [←category.assoc, ←category.assoc],
    simp },
  { rw [←category.assoc, ←category.assoc],
    simp },
end

@[simp] lemma coprod.map_desc {P Q R S T : C} (f : P ⟶ Q) (g : R ⟶ S)  (h : Q ⟶ T) (k : S ⟶ T) :
  coprod.map f g ≫ coprod.desc h k = coprod.desc (f ≫ h) (g ≫ k) :=
begin
  /- `obviously` says -/
  ext1,
  { simp,
    rw ←category.assoc,
    simp },
  { simp,
    rw ←category.assoc,
    simp },
end.

@[simp] lemma coprod.map_map {P Q R S T U : C} (f : P ⟶ Q) (g : R ⟶ S) (h : Q ⟶ T) (k : S ⟶ U) :
  coprod.map f g ≫ coprod.map h k = coprod.map (f ≫ h) (g ≫ k) :=
begin
  /- `obviously` says -/
  ext1,
  { simp,
    rw ←category.assoc,
    simp },
  { simp,
    rw ←category.assoc,
    simp }
end.

section
variables {D : Type u} [category.{u v} D] [has_binary_coproducts.{u v} D]

@[simp] lemma coprod.post_desc {P Q R : C} (f : P ⟶ R) (g : Q ⟶ R) (G : C ⥤ D) :
  coprod.post P Q G ≫ G.map (coprod.desc f g) = coprod.desc (G.map f) (G.map g) :=
begin
  /- `obviously` says -/
  ext1,
  { simp,
    rw ←category.assoc,
    simp,
    rw [←functor.map_comp, coprod.ι₁_desc] },
  { simp,
    rw ←category.assoc,
    simp,
    rw [←functor.map_comp, coprod.ι₂_desc] }
end.

lemma coprod.map_post {Q R S T : C} (h : Q ⟶ S) (k : R ⟶ T) (H : C ⥤ D) :
  coprod.map (H.map h) (H.map k) ≫ coprod.post S T H = coprod.post Q R H ≫ H.map (coprod.map h k) :=
begin
  /- `obviously` says -/
  ext1,
  { rw ←category.assoc,
    simp,
    rw ←functor.map_comp,
    rw ←category.assoc,
    simp,
    rw [←functor.map_comp, ←functor.map_comp, coprod.ι₁_map], },
  { rw ←category.assoc,
    simp,
    rw ←functor.map_comp,
    rw ←category.assoc,
    simp,
    rw [←functor.map_comp, ←functor.map_comp, coprod.ι₂_map], }
end.

lemma coprod.swap_post (Q R : C) (G : C ⥤ D) :
  coprod.swap (G Q) (G R) ≫ coprod.post R Q G = coprod.post Q R G ≫ G.map (coprod.swap Q R) :=
begin
  /- `obviously` says -/
  ext1,
  rw [←category.assoc, coprod.ι₁_swap, coprod.ι₂_post, ←category.assoc,
        coprod.ι₁_post, ←functor.map_comp, coprod.ι₁_swap],
  rw [←category.assoc, coprod.ι₂_swap, coprod.ι₁_post, ←category.assoc,
        coprod.ι₂_post, ←functor.map_comp, coprod.ι₂_swap]
end.

@[simp] lemma coprod.post_post {E : Type u} [category.{u v} E] [has_binary_coproducts.{u v} E]
  (Q R : C) (G : C ⥤ D) (H : D ⥤ E):
  coprod.post (G Q) (G R) H ≫ H.map (coprod.post Q R G) = coprod.post Q R (G ⋙ H) :=
begin
  /- `obvious` says -/
  ext1,
  { rw ←category.assoc,
    simp,
    rw ←functor.map_comp,
    rw coprod.ι₁_post,
    erw coprod.ι₁_desc,
    simp },
  { rw ←category.assoc,
    simp,
    rw ←functor.map_comp,
    rw coprod.ι₂_post,
    erw coprod.ι₂_desc,
    simp }
end
end

end

end category_theory.limits
