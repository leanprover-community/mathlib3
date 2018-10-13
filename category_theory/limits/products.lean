-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Reid Barton, Mario Carneiro

import category_theory.limits.terminal
import category_theory.limits.binary_products

open category_theory

universes u v w

namespace category_theory.limits

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

section product
variables {β : Type v} {f : β → C}

structure is_product (t : fan f) :=
(lift : ∀ (s : fan f), s.X ⟶ t.X)
(fac'  : ∀ (s : fan f), ∀ b, (lift s) ≫ t.π b = s.π b . obviously)
(uniq' : ∀ (s : fan f) (m : s.X ⟶ t.X) (w : ∀ b, m ≫ t.π b = s.π b), m = lift s . obviously)

restate_axiom is_product.fac'
attribute [simp] is_product.fac
restate_axiom is_product.uniq'

@[extensionality] lemma is_product.ext {t : fan f} (P Q : is_product t) : P = Q :=
begin
  tactic.unfreeze_local_instances,
  cases P,
  cases Q,
  congr,
  ext1,
  exact eq.symm (P_uniq' x (Q_lift x) (Q_fac' x))
end

instance is_product_subsingleton {t : fan f}  : subsingleton (is_product t) := by split; ext1

lemma is_product.uniq'' {t : fan f} (h : is_product t) {X' : C} (m : X' ⟶ t.X) : m = h.lift { X := X', π := λ b, m ≫ t.π b } :=
h.uniq { X := X', π := λ b, m ≫ t.π b } m (λ b, rfl)

lemma is_product.univ {t : fan f} (h : is_product t) (s : fan f) (φ : s.X ⟶ t.X) : (∀ b, φ ≫ t.π b = s.π b) ↔ (φ = h.lift s) :=
⟨ is_product.uniq h s φ,
  λ a b, by rw [a, is_product.fac] ⟩

def is_product.of_lift_univ {t : fan f}
  (lift : Π (s : fan f), s.X ⟶ t.X)
  (univ : Π (s : fan f) (φ : s.X ⟶ t.X), (∀ b, φ ≫ t.π b = s.π b) ↔ (φ = lift s)) : is_product t :=
{ lift := lift,
  fac'  := λ s b, ((univ s (lift s)).mpr (eq.refl (lift s))) b,
  uniq' := λ s φ, (univ s φ).mp }

end product


section coproduct
variables {β : Type v} {f : β → C}

structure is_coproduct (t : cofan f) :=
(desc : ∀ (s : cofan f), t.X ⟶ s.X)
(fac'  : ∀ (s : cofan f), ∀ b, t.ι b ≫ (desc s) = s.ι b . obviously)
(uniq' : ∀ (s : cofan f) (m : t.X ⟶ s.X) (w : ∀ b, t.ι b ≫ m = s.ι b), m = desc s . obviously)

restate_axiom is_coproduct.fac'
attribute [simp] is_coproduct.fac
restate_axiom is_coproduct.uniq'

@[extensionality] lemma is_coproduct.ext {t : cofan f} (P Q : is_coproduct t) : P = Q :=
begin
  tactic.unfreeze_local_instances,
  cases P,
  cases Q,
  congr,
  ext1,
  exact eq.symm (P_uniq' x (Q_desc x) (Q_fac' x))

end

instance is_coproduct_subsingleton {t : cofan f}  : subsingleton (is_coproduct t) := by split; ext1

lemma is_coproduct.uniq'' {t : cofan f} (h : is_coproduct t) {X' : C} (m : t.X ⟶ X') : m = h.desc { X := X', ι := λ b, t.ι b ≫ m } :=
h.uniq { X := X', ι := λ b, t.ι b ≫ m } m (λ b, rfl)

lemma is_coproduct.univ {t : cofan f} (h : is_coproduct t) (s : cofan f) (φ : t.X ⟶ s.X) : (∀ b, t.ι b ≫ φ = s.ι b) ↔ (φ = h.desc s) :=
⟨ is_coproduct.uniq h s φ,
  λ a b, by rw [a, is_coproduct.fac] ⟩

def is_coproduct.of_desc_univ {t :cofan f}
  (desc : Π (s : cofan f), t.X ⟶ s.X)
  (univ : Π (s : cofan f) (φ : t.X ⟶ s.X), (∀ b, t.ι b ≫ φ = s.ι b) ↔ (φ = desc s)) : is_coproduct t :=
{ desc := desc,
  fac'  := λ s b, ((univ s (desc s)).mpr (eq.refl (desc s))) b,
  uniq' := λ s φ, (univ s φ).mp }

end coproduct

variable (C)

class has_products :=
(prod : Π {β : Type v} (f : β → C), fan.{u v} f)
(is_product : Π {β : Type v} (f : β → C), is_product (prod f) . obviously)

class has_coproducts :=
(coprod : Π {β : Type v} (f : β → C), cofan.{u v} f)
(is_coproduct : Π {β : Type v} (f : β → C), is_coproduct (coprod f) . obviously)

variable {C}

section
variables [has_products.{u v} C] {β : Type v}

def pi.fan (f : β → C) : fan f := has_products.prod.{u v} f
def pi (f : β → C) : C := (pi.fan f).X
def pi.π (f : β → C) (b : β) : pi f ⟶ f b := (pi.fan f).π b
def pi.universal_property (f : β → C) : is_product (pi.fan f) := has_products.is_product.{u v} C f

@[simp] lemma pi.fan_π (f : β → C) (b : β) : (pi.fan f).π b = @pi.π C _ _ _ f b := rfl

def pi.lift {f : β → C} {P : C} (p : Π b, P ⟶ f b) : P ⟶ pi f :=
(pi.universal_property f).lift ⟨ ⟨ P ⟩, p ⟩

@[simp] lemma pi.lift_π {f : β → C} {P : C} (p : Π b, P ⟶ f b) (b : β) : pi.lift p ≫ pi.π f b = p b :=
by erw is_product.fac

def pi.map {f : β → C} {g : β → C} (k : Π b, f b ⟶ g b) : (pi f) ⟶ (pi g) :=
pi.lift (λ b, pi.π f b ≫ k b)

@[simp] lemma pi.map_π {f : β → C} {g : β → C} (k : Π b, f b ⟶ g b) (b : β) : pi.map k ≫ pi.π g b = pi.π f b ≫ k b :=
by erw is_product.fac

def pi.pre {α} (f : α → C) (h : β → α) : pi f ⟶ pi (f ∘ h) :=
pi.lift (λ g, pi.π f (h g))

@[simp] lemma pi.pre_π {α} (f : α → C) (h : β → α) (b : β) : pi.pre f h ≫ pi.π (f ∘ h) b = pi.π f (h b) :=
by erw is_product.fac

section
variables {D : Type u} [𝒟 : category.{u v} D] [has_products.{u v} D]
include 𝒟

def pi.post (f : β → C) (G : C ⥤ D) : G (pi f) ⟶ (pi (G.obj ∘ f)) :=
@is_product.lift _ _ _ _ (pi.fan (G.obj ∘ f)) (pi.universal_property _) { X := _, π := λ b, G.map (pi.π f b) }

@[simp] lemma pi.post_π (f : β → C) (G : C ⥤ D) (b : β) : pi.post f G ≫ pi.π _ b = G.map (pi.π f b) :=
by erw is_product.fac
end

@[extensionality] lemma pi.hom_ext (f : β → C) {X : C} (g h : X ⟶ pi f) (w : ∀ b, g ≫ pi.π f b = h ≫ pi.π f b) : g = h :=
begin
  rw is_product.uniq (pi.universal_property f) { X := X, π := λ b, g ≫ pi.π f b } g,
  rw is_product.uniq (pi.universal_property f) { X := X, π := λ b, g ≫ pi.π f b } h,
  intro b, exact eq.symm (w b),
  intro b, refl,
end

@[simp] def pi.lift_map
  {f : β → C} {g : β → C} {P : C} (p : Π b, P ⟶ f b) (k : Π b, f b ⟶ g b) :
  pi.lift p ≫ pi.map k = pi.lift (λ b, p b ≫ k b) :=
begin
  /- `obviously` says -/
  ext1,
  simp,
  rw [←category.assoc, pi.lift_π]
end

@[simp] def pi.map_map {f1 : β → C} {f2 : β → C} {f3 : β → C}
  (k1 : Π b, f1 b ⟶ f2 b) (k2 : Π b, f2 b ⟶ f3 b) :
  pi.map k1 ≫ pi.map k2 = pi.map (λ b, k1 b ≫ k2 b) :=
begin
  /- `obviously` says -/
  ext1,
  simp,
  rw ←category.assoc,
  erw pi.lift_π,
  rw ←category.assoc
end

@[simp] def pi.lift_pre {α : Type v} {f : β → C} {P : C} (p : Π b, P ⟶ f b) (h : α → β) :
  pi.lift p ≫ pi.pre _ h = pi.lift (λ a, p (h a)) :=
by ext1; simp.

def pi.map_pre {α : Type v} {f g : β → C} (k : Π b : β, f b ⟶ g b) (e : α → β) :
  pi.map k ≫ pi.pre g e = pi.pre f e ≫ pi.map (λ a, k (e a)) :=
begin
  /- `obviously` says -/
  ext1,
  simp,
  rw ←category.assoc,
  erw pi.lift_π
end.

@[simp] lemma pi.pre_pre {γ δ : Type v} (f : β → C) (g : γ → β) (h : δ → γ) :
  pi.pre f g ≫ pi.pre (f ∘ g) h = pi.pre f (g ∘ h) :=
by ext1; simp.

section
variables {D : Type u} [category.{u v} D] [has_products.{u v} D]

@[simp] def pi.lift_post {f : β → C} {P : C} (k : Π b : β, P ⟶ f b) (G : C ⥤ D) :
  G.map (pi.lift k) ≫ pi.post f G = pi.lift (λ b, G.map (k b)) :=
begin
  /- `obvously` says -/
  ext1, simp,
  erw [←functor.map_comp, pi.lift_π]
end.

def pi.map_post {f g : β → C} (k : Π b : β, f b ⟶ g b) (H : C ⥤ D) :
  H.map (pi.map k) ≫ pi.post g H = pi.post f H ≫ pi.map (λ b, H.map (k b)) :=
begin
  /- `tidy` says -/
  ext1,
  simp,
  rw ←functor.map_comp,
  erw pi.lift_π,
  rw ←category.assoc,
  erw pi.lift_π,
  rw ←functor.map_comp
end.

def pi.pre_post {α} (f : β → C) (g : α → β) (G : C ⥤ D) :
  G.map (pi.pre f g) ≫ pi.post (f ∘ g) G = pi.post f G ≫ pi.pre (G.obj ∘ f) g :=
begin
  /- `tidy` says -/
  ext1,
  simp,
  rw ←functor.map_comp,
  erw pi.lift_π
end

@[simp] def pi.post_post {E : Type u} [category.{u v} E] [has_products.{u v} E] (f : β → C) (G : C ⥤ D) (H : D ⥤ E):
  H.map (pi.post f G) ≫ pi.post (G.obj ∘ f) H = pi.post f (G ⋙ H) :=
begin
  /- `obviously` says -/
  ext1,
  simp,
  rw ←functor.map_comp,
  rw pi.post_π,
  erw pi.post_π,
  refl,
end.
end


instance : has_terminal_object.{u v} C :=
{ terminal := pi.{u v} (@pempty.elim.{u+1} C),
  is_terminal := { lift := λ X, pi.lift (pempty.rec _) } }

instance : has_binary_products.{u v} C :=
{ prod := λ Y Z,
  begin
    let f : ulift bool → C := (λ b : ulift bool, cond b.down Y Z),
    exact { X := pi f, π₁ := pi.π f ⟨ tt ⟩, π₂ := pi.π f ⟨ ff ⟩ }
  end,
  is_binary_product := λ Y Z,
  { lift := λ s, pi.lift (λ b, bool.cases_on b.down s.π₂ s.π₁),
    uniq' := λ s m w₁ w₂,
    begin
      dsimp at *, ext1, cases b, cases b, tidy,
    end } }

end

section
variables [has_coproducts.{u v} C] {β : Type v}

def sigma.cofan (f : β → C) := has_coproducts.coprod.{u v} f
def sigma (f : β → C) : C := (sigma.cofan f).X
def sigma.ι (f : β → C) (b : β) : f b ⟶ sigma f := (sigma.cofan f).ι b
def sigma.universal_property (f : β → C) : is_coproduct (sigma.cofan f) := has_coproducts.is_coproduct.{u v} C f

@[simp] lemma sigma.cofan_ι (f : β → C) (b : β) : (sigma.cofan f).ι b = @sigma.ι C _ _ _ f b := rfl

def sigma.desc {f : β → C} {P : C} (p : Π b, f b ⟶ P) : sigma f ⟶ P :=
(sigma.universal_property f).desc ⟨ ⟨ P ⟩, p ⟩

@[simp] lemma sigma.ι_desc {f : β → C} {P : C} (p : Π b, f b ⟶ P) (b : β) : sigma.ι f b ≫ sigma.desc p = p b :=
by erw is_coproduct.fac

def sigma.map {f : β → C} {g : β → C} (k : Π b, f b ⟶ g b) : (sigma f) ⟶ (sigma g) :=
sigma.desc (λ b, k b ≫ sigma.ι g b)

@[simp] lemma sigma.ι_map {f : β → C} {g : β → C} (k : Π b, f b ⟶ g b) (b : β) : sigma.ι f b ≫ sigma.map k = k b ≫ sigma.ι g b :=
by erw is_coproduct.fac

def sigma.pre {α} (f : α → C) (h : β → α) : sigma (f ∘ h) ⟶ sigma f :=
sigma.desc (λ g, sigma.ι f (h g))

@[simp] lemma sigma.ι_pre {α} (f : α → C) (h : β → α) (b : β) : sigma.ι (f ∘ h) b ≫ sigma.pre f h = sigma.ι f (h b) :=
by erw is_coproduct.fac

section
variables {D : Type u} [𝒟 : category.{u v} D] [has_coproducts.{u v} D]
include 𝒟

def sigma.post (f : β → C) (G : C ⥤ D) : (sigma (G.obj ∘ f)) ⟶ G (sigma f) :=
@is_coproduct.desc _ _ _ _ (sigma.cofan (G.obj ∘ f)) (sigma.universal_property _) { X := _, ι := λ b, G.map (sigma.ι f b) }

@[simp] lemma sigma.ι_post (f : β → C) (G : C ⥤ D) (b : β) : sigma.ι _ b ≫ sigma.post f G = G.map (sigma.ι f b) :=
by erw is_coproduct.fac
end

@[extensionality] lemma sigma.hom_ext (f : β → C) {X : C} (g h : sigma f ⟶ X) (w : ∀ b, sigma.ι f b ≫ g = sigma.ι f b ≫ h) : g = h :=
begin
  rw is_coproduct.uniq (sigma.universal_property f) { X := X, ι := λ b, sigma.ι f b ≫ g } g,
  rw is_coproduct.uniq (sigma.universal_property f) { X := X, ι := λ b, sigma.ι f b ≫ g } h,
  intro b, exact eq.symm (w b),
  intro b, refl
end

@[simp] lemma sigma.map_desc
  {f : β → C} {g : β → C} {P : C} (k : Π b, f b ⟶ g b) (p : Π b, g b ⟶ P) :
  sigma.map k ≫ sigma.desc p = sigma.desc (λ b, k b ≫ p b) :=
begin
  /- `obviously` says -/
  ext1,
  simp,
  rw ←category.assoc,
  simp
end

@[simp] lemma sigma.map_map {f1 : β → C} {f2 : β → C} {f3 : β → C}
  (k1 : Π b, f1 b ⟶ f2 b) (k2 : Π b, f2 b ⟶ f3 b) :
  sigma.map k1 ≫ sigma.map k2 = sigma.map (λ b, k1 b ≫ k2 b) :=
begin
  /- `obviously` says -/
  ext1,
  simp,
  rw ←category.assoc,
  simp,
end.

@[simp] lemma sigma.pre_desc {α : Type v} {f : β → C} {P : C} (p : Π b, f b ⟶ P) (h : α → β) :
  sigma.pre _ h ≫ sigma.desc p = sigma.desc (λ a, p (h a)) :=
begin
  /- `obviously` says -/
  ext1,
  simp,
  rw ←category.assoc,
  simp,
end

def sigma.pre_map {α : Type v} {f g : β → C} (k : Π b : β, f b ⟶ g b) (e : α → β) :
  sigma.pre f e ≫ sigma.map k = sigma.map (λ a, k (e a)) ≫ sigma.pre g e :=
begin
  /- `obviously` says -/
  ext1,
  rw ←category.assoc,
  erw sigma.ι_desc,
  rw ←category.assoc,
  simp,
end.

@[simp] lemma sigma.pre_pre {γ δ : Type v} (f : β → C) (g : γ → β) (h : δ → γ) :
  sigma.pre (f ∘ g) h ≫ sigma.pre f g = sigma.pre f (g ∘ h) :=
begin
  ext1,
  rw ←category.assoc,
  simp,
  rw sigma.ι_pre f,
end.

section
variables {D : Type u} [category.{u v} D] [has_coproducts.{u v} D]

@[simp] def sigma.post_desc {f : β → C} {P : C} (k : Π b : β, f b ⟶ P) (G : C ⥤ D) :
  sigma.post f G ≫ G.map (sigma.desc k) = sigma.desc (λ b, G.map (k b)) :=
begin
  /- `obvously` says -/
  ext1, simp,
  rw ←category.assoc,
  rw sigma.ι_post,
  rw ←functor.map_comp,
  rw sigma.ι_desc,
end.

def sigma.map_post {f g : β → C} (k : Π b : β, f b ⟶ g b) (H : C ⥤ D) :
  @sigma.map _ _ _ _ (H.obj ∘ f) (H.obj ∘ g) (λ b, H.map (k b)) ≫ sigma.post g H = sigma.post f H ≫ H.map (sigma.map k) :=
begin
  /- `obviously` says -/
  ext1,
  dsimp at *,
  rw ←category.assoc,
  simp,
  rw ←functor.map_comp,
  rw ←category.assoc,
  simp,
  rw ←functor.map_comp,
  rw ←functor.map_comp,
  rw sigma.ι_map,
end.

def sigma.pre_post {α} (f : β → C) (g : α → β) (G : C ⥤ D) :
  sigma.pre (G.obj ∘ f) g ≫ sigma.post f G = sigma.post (f ∘ g) G ≫ G.map (sigma.pre f g) :=
begin
  /- `tidy` says -/
  ext1,
  dsimp at *,
  rw [←category.assoc, sigma.ι_pre, sigma.ι_post, ←category.assoc,
      sigma.ι_post, ←functor.map_comp, sigma.ι_pre]
end

@[simp] def sigma.post_post {E : Type u} [category.{u v} E] [has_coproducts.{u v} E] (f : β → C) (G : C ⥤ D) (H : D ⥤ E):
  sigma.post (G.obj ∘ f) H ≫ H.map (sigma.post f G) = sigma.post f (G ⋙ H) :=
begin
  /- `obviously` says -/
  ext1,
  rw ←category.assoc,
  rw sigma.ι_post,
  rw ←functor.map_comp,
  rw sigma.ι_post,
  erw sigma.ι_post f (G ⋙ H) b,
  refl
end.
end

instance : has_initial_object.{u v} C :=
{ initial := sigma.{u v} (@pempty.elim.{u+1} C),
  is_initial := { desc := λ X, sigma.desc (pempty.rec _) } }

instance : has_binary_coproducts.{u v} C :=
{ coprod := λ Y Z,
  begin
    let f : ulift bool → C := (λ b : ulift bool, cond b.down Y Z),
    exact { X := sigma f, ι₁ := sigma.ι f ⟨ tt ⟩, ι₂ := sigma.ι f ⟨ ff ⟩ }
  end,
  is_binary_coproduct := λ Y Z,
  { desc := λ s, sigma.desc (λ b, bool.cases_on b.down s.ι₂ s.ι₁),
    uniq' := λ s m w₁ w₂,
    begin
      dsimp at *, ext1, cases b, cases b, tidy,
    end } }

end

end category_theory.limits
