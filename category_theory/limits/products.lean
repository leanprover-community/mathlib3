import category_theory.limits.limits
import category_theory.discrete_category

open category_theory

namespace category_theory.limits

universes u v w

variables {β : Type v}
variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

section products
def fan (f : β → C) := cone (functor.of_function f)

variables {f : β → C}

def is_product (t : fan f) := is_limit t

variables {t : fan f}

instance is_product_subsingleton : subsingleton (is_product t) := by dsimp [is_product]; apply_instance

variable (C)

class has_products :=
(fan : Π {β : Type v} (f : β → C), fan.{u v} f)
(is_product : Π {β : Type v} (f : β → C), is_product (fan f) . obviously)

class has_products_of_shape (β : Type v) :=
(fan : Π f : β → C, fan f)
(is_product : Π f : β → C, is_product (fan f))

variable {C}

class has_product {β : Type v} (f : β → C) :=
(fan : fan.{u v} f)
(is_product : is_product fan)

instance has_product_of_has_products_of_shape
  {β : Type v} [has_products_of_shape.{u v} C β] (f : β → C) : has_product f :=
{ fan := has_products_of_shape.fan f,
  is_product := has_products_of_shape.is_product f }

instance has_products_of_shape_of_has_products
  {β : Type v} [has_products.{u v} C] : has_products_of_shape.{u v} C β :=
{ fan := λ f, has_products.fan f,
  is_product := λ f, has_products.is_product C f }

-- Special cases of this may be marked with [instance] as desired.
def has_products_of_has_limits [limits.has_limits.{u v} C] : has_products.{u v} C :=
{ fan := λ β f, limit.cone (functor.of_function f),
  is_product := λ β f, limit.universal_property (functor.of_function f) }

instance has_limit_of_has_product {β : Type v} (f : β → C) [has_product f] : limits.has_limit (functor.of_function f) :=
{ cone := has_product.fan f,
  is_limit := has_product.is_product f }

def cone.of_fan {β : Type v} {F : (discrete β) ⥤ C} (t : fan (F.obj)) : cone F :=
{ X := t.X,
  π :=
  { app := t.π.app,
    naturality' := λ j j' g,
    begin
      cases g, cases g, cases g,
      have h : ({down := {down := g}} : j ⟶ j) = 𝟙 j, ext1, ext1,
      rw h,
      simp,
      erw category.id_comp,
    end } }

def fan.of_cone {β : Type v} {F : (discrete β) ⥤ C} (t : cone F) : fan (F.obj) :=
{ X := t.X,
  π :=
  { app := t.π.app,
    naturality' := λ j j' g,
    begin
      cases g, cases g, cases g,
      have h : ({down := {down := g}} : j ⟶ j) = 𝟙 j, ext1, ext1,
      rw h,
      simp,
      erw category.id_comp,
    end } }

instance has_limits_of_shape_of_has_products_of_shape {β : Type v} [has_products_of_shape.{u v} C β] :
  limits.has_limits_of_shape.{u v} (discrete β) C :=
begin
  haveI : has_products_of_shape.{u v} C (discrete β) := (by apply_instance : has_products_of_shape.{u v} C β),
  exact
  { cone := λ F, cone.of_fan (has_products_of_shape.fan F.obj),
    is_limit := λ F, let is_product := has_product.is_product F.obj in
    { lift := λ s, is_product.lift (fan.of_cone s),
      fac' := λ s j, is_product.fac (fan.of_cone s) j,
      uniq' := λ s m j, is_product.uniq (fan.of_cone s) m j } }
end

section

def pi.fan (f : β → C) [has_product f] : fan f := has_product.fan.{u v} f
protected def pi (f : β → C) [has_product f] : C := (pi.fan f).X
def pi.π (f : β → C) [has_product f] (b : β) : limits.pi f ⟶ f b :=
((pi.fan f).π : Π b : β, limits.pi  f ⟶ f b) b
def pi.universal_property (f : β → C) [has_product f] : is_product (pi.fan f) :=
has_product.is_product.{u v} f

@[simp] lemma pi.fan_π (f : β → C) [has_product f] (b : β) : ((pi.fan f).π : Π b : β, limits.pi  f ⟶ f b) b = @pi.π _ C _ f _ b := rfl

@[simp] def cone.of_function {f : β → C} {P : C} (p : Π b, P ⟶ f b) : cone (functor.of_function f) :=
{ X := P,
  π := { app := p } }

def pi.lift {f : β → C} [has_product f] {P : C} (p : Π b, P ⟶ f b) : P ⟶ limits.pi f :=
limit.lift _ (cone.of_function p)

@[simp] lemma pi.lift_π {f : β → C} [has_product f] {P : C} (p : Π b, P ⟶ f b) (b : β) : pi.lift p ≫ pi.π f b = p b :=
limit.lift_π (cone.of_function p) b

def pi.map
  {f : β → C} [has_product f] {g : β → C} [has_product g] (k : Π b, f b ⟶ g b) : (limits.pi f) ⟶ (limits.pi g) :=
pi.lift (λ b, pi.π f b ≫ k b)

@[simp] lemma pi.map_π
  {f : β → C} [has_product f] {g : β → C} [has_product g] (k : Π b, f b ⟶ g b) (b : β) :
  pi.map k ≫ pi.π g b = pi.π f b ≫ k b :=
by erw is_limit.fac; refl

def pi.pre {α} (f : α → C) [has_product.{u v} f] (h : β → α) [has_product.{u v} (f ∘ h)] :
  limits.pi f ⟶ limits.pi (f ∘ h) :=
pi.lift (λ g, pi.π f (h g))

@[simp] lemma pi.pre_π {α} (f : α → C) [has_product.{u v} f] (h : β → α) [has_product.{u v} (f ∘ h)] (b : β) :
  pi.pre f h ≫ pi.π (f ∘ h) b = pi.π f (h b) :=
by erw is_limit.fac; refl

section
variables {D : Type u} [𝒟 : category.{u v} D]
include 𝒟

def pi.post (f : β → C) [has_product f] (G : C ⥤ D) [has_product (G.obj ∘ f)] :
  G (limits.pi f) ⟶ (limits.pi (G.obj ∘ f)) :=
@is_limit.lift _ _ _ _ _
  (pi.fan (G.obj ∘ f))
  (pi.universal_property _)
  { X := _,
    π := { app := λ b, G.map (pi.π f b) } }

@[simp] lemma pi.post_π (f : β → C) [has_product f] (G : C ⥤ D) [has_product (G.obj ∘ f)] (b : β) :
  pi.post f G ≫ pi.π _ b = G.map (pi.π f b) :=
by erw is_limit.fac; refl
end

@[extensionality] lemma pi.hom_ext
  {f : β → C} [has_product f] {X : C} {g h : X ⟶ limits.pi f} (w : ∀ b, g ≫ pi.π f b = h ≫ pi.π f b) : g = h :=
limit.hom_ext w

@[simp] def pi.lift_map
  [has_products_of_shape.{u v} C β] {f : β → C} {g : β → C} {P : C} (p : Π b, P ⟶ f b) (k : Π b, f b ⟶ g b) :
  pi.lift p ≫ pi.map k = pi.lift (λ b, p b ≫ k b) :=
limit.lift_map (cone.of_function p) (nat_trans.of_function k)

@[simp] def pi.map_map [has_products_of_shape.{u v} C β] {f1 : β → C} {f2 : β → C} {f3 : β → C}
  (k1 : Π b, f1 b ⟶ f2 b) (k2 : Π b, f2 b ⟶ f3 b) :
  pi.map (λ b, k1 b ≫ k2 b) = pi.map k1 ≫ pi.map k2 :=
lim.map_comp (nat_trans.of_function k1) (nat_trans.of_function k2)

@[simp] def pi.lift_pre
  {α : Type v} {f : β → C} [has_product f] {P : C} (p : Π b, P ⟶ f b) (h : α → β) [has_product (f ∘ h)]:
  pi.lift p ≫ pi.pre _ h = pi.lift (λ a, p (h a)) :=
by ext1; simp.

def pi.map_pre
  {α : Type v} [has_products_of_shape.{u v} C β] [has_products_of_shape.{u v} C α]
  {f g : β → C} (k : Π b : β, f b ⟶ g b)
  (e : α → β) :
  pi.map k ≫ pi.pre g e = pi.pre f e ≫ pi.map (λ a, k (e a)) :=
limit.map_pre (nat_trans.of_function k) (discrete.lift e)

@[simp] lemma pi.pre_pre {γ δ : Type v}
  [has_products_of_shape.{u v} C β] [has_products_of_shape.{u v} C γ] [has_products_of_shape.{u v} C δ]
  (f : β → C) (g : γ → β) (h : δ → γ) :
  pi.pre f g ≫ pi.pre (f ∘ g) h = pi.pre f (g ∘ h) :=
by ext1; simp.

section
variables {D : Type u} [category.{u v} D] [has_products.{u v} D]

@[simp] def pi.lift_post [has_products_of_shape.{u v} C β] {f : β → C} {P : C} (k : Π b : β, P ⟶ f b) (G : C ⥤ D) :
  G.map (pi.lift k) ≫ pi.post f G = pi.lift (λ b, G.map (k b)) :=
begin
  /- `obviously` says -/
  ext1, dsimp, simp,
  erw ←functor.map_comp,
  simp,
end


def pi.map_post [has_products_of_shape.{u v} C β] {f g : β → C} (k : Π b : β, f b ⟶ g b) (H : C ⥤ D) :
  H.map (pi.map k) ≫ pi.post g H = pi.post f H ≫ pi.map (λ b, H.map (k b)) :=
limit.map_post (nat_trans.of_function k) H

def pi.pre_post {α} [has_products_of_shape.{u v} C β] [has_products_of_shape.{u v} C α] (f : β → C) (g : α → β) (G : C ⥤ D) :
  G.map (pi.pre f g) ≫ pi.post (f ∘ g) G = pi.post f G ≫ pi.pre (G.obj ∘ f) g :=
limit.pre_post (functor.of_function f) (discrete.lift g) G

@[simp] def pi.post_post
  [has_products_of_shape.{u v} C β]
  {E : Type u} [category.{u v} E] [has_products.{u v} E] (f : β → C) (G : C ⥤ D) (H : D ⥤ E) :
  H.map (pi.post f G) ≫ pi.post (G.obj ∘ f) H = pi.post f (G ⋙ H) :=
limit.post_post (functor.of_function f) G H
end
end
end products

section coproducts
def cofan (f : β → C) := cocone (functor.of_function f)

variables {f : β → C}

def is_coproduct (t : cofan f) := is_colimit t

variables {t : cofan f}

instance is_coproduct_subsingleton : subsingleton (is_coproduct t) := by dsimp [is_coproduct]; apply_instance

variable (C)

class has_coproducts :=
(cofan : Π {β : Type v} (f : β → C), cofan.{u v} f)
(is_coproduct : Π {β : Type v} (f : β → C), is_coproduct (cofan f) . obviously)

class has_coproducts_of_shape (β : Type v) :=
(cofan : Π f : β → C, cofan f)
(is_coproduct : Π f : β → C, is_coproduct (cofan f))

variable {C}

class has_coproduct {β : Type v} (f : β → C) :=
(cofan : cofan.{u v} f)
(is_coproduct : is_coproduct cofan)

instance has_coproduct_of_has_coproducts_of_shape
  {β : Type v} [has_coproducts_of_shape.{u v} C β] (f : β → C) : has_coproduct f :=
{ cofan := has_coproducts_of_shape.cofan f,
  is_coproduct := has_coproducts_of_shape.is_coproduct f }

instance has_coproducts_of_shape_of_has_coproducts
  {β : Type v} [has_coproducts.{u v} C] : has_coproducts_of_shape.{u v} C β :=
{ cofan := λ f, has_coproducts.cofan f,
  is_coproduct := λ f, has_coproducts.is_coproduct C f }

-- Special cases of this may be marked with [instance] as desired.
def has_coproducts_of_has_colimits [limits.has_colimits.{u v} C] : has_coproducts.{u v} C :=
{ cofan := λ β f, colimit.cocone (functor.of_function f),
  is_coproduct := λ β f, colimit.universal_property (functor.of_function f) }

instance has_colimit_of_has_coproduct {β : Type v} (f : β → C) [has_coproduct f] :
  limits.has_colimit (functor.of_function f) :=
{ cocone := has_coproduct.cofan f,
  is_colimit := has_coproduct.is_coproduct f }

def cocone.of_cofan {β : Type v} {F : (discrete β) ⥤ C} (t : cofan (F.obj)) : cocone F :=
{ X := t.X,
  ι :=
  { app := t.ι.app,
    naturality' := λ j j' g,
    begin
      cases g, cases g, cases g,
      have h : ({down := {down := g}} : j ⟶ j) = 𝟙 j, ext1, ext1,
      rw h,
      simp,
      erw category.comp_id,
    end } }

def cofan.of_cocone {β : Type v} {F : (discrete β) ⥤ C} (t : cocone F) : cofan (F.obj) :=
{ X := t.X,
  ι :=
  { app := t.ι.app,
    naturality' := λ j j' g,
    begin
      cases g, cases g, cases g,
      have h : ({down := {down := g}} : j ⟶ j) = 𝟙 j, ext1, ext1,
      rw h,
      simp,
      erw category.comp_id,
    end } }

instance has_colimits_of_shape_of_has_coproducts_of_shape {β : Type v} [has_coproducts_of_shape.{u v} C β] :
  limits.has_colimits_of_shape.{u v} (discrete β) C :=
begin
  haveI : has_coproducts_of_shape.{u v} C (discrete β) := (by apply_instance : has_coproducts_of_shape.{u v} C β),
  exact
  { cocone := λ F, cocone.of_cofan (has_coproducts_of_shape.cofan F.obj),
    is_colimit := λ F, let is_coproduct := has_coproduct.is_coproduct F.obj in
    { desc := λ s, is_coproduct.desc (cofan.of_cocone s),
      fac' := λ s j, is_coproduct.fac (cofan.of_cocone s) j,
      uniq' := λ s m j, is_coproduct.uniq (cofan.of_cocone s) m j } }
end


-- FIXME restore these

-- def has_binary_products_from_has_products : has_binary_products.{u v} C :=
-- { span := λ Y Z,
--   begin
--     let f : ulift bool → C := (λ b : ulift bool, cond b.down Y Z),
--     exact { X := limits.pi f, π₁ := pi.π f ⟨ tt ⟩, π₂ := pi.π f ⟨ ff ⟩ }
--   end,
--   is_binary_product := λ Y Z,
--   { lift := λ s, pi.lift (λ b, bool.cases_on b.down s.π₂ s.π₁),
--     uniq' := λ s m w₁ w₂,
--     begin
--       dsimp at *, ext1, cases b, cases b, tidy,
--     end } }

section

def sigma.cofan (f : β → C) [has_coproduct f] := has_coproduct.cofan.{u v} f
protected def sigma (f : β → C) [has_coproduct f] : C := (sigma.cofan f).X
def sigma.ι (f : β → C) [has_coproduct f] (b : β) : f b ⟶ limits.sigma f :=
((sigma.cofan f).ι : Π b : β, f b ⟶ limits.sigma f) b
def sigma.universal_property (f : β → C) [has_coproduct f] : is_coproduct (sigma.cofan f) :=
has_coproduct.is_coproduct.{u v} f

@[simp] lemma sigma.cofan_ι (f : β → C) [has_coproduct f] (b : β) : ((sigma.cofan f).ι : Π b : β, f b ⟶ limits.sigma f) b = @sigma.ι _ C _ f _ b := rfl

@[simp] def cocone.of_function {f : β → C} {P : C} (p : Π b, f b ⟶ P) : cocone (functor.of_function f) :=
{ X := P,
  ι := { app := p } }

def sigma.desc {f : β → C} [has_coproduct f] {P : C} (p : Π b, f b ⟶ P) : limits.sigma f ⟶ P :=
colimit.desc _ (cocone.of_function p)

@[simp] lemma sigma.ι_desc {f : β → C} [has_coproduct f] {P : C} (p : Π b, f b ⟶ P) (b : β) :
  sigma.ι f b ≫ sigma.desc p = p b :=
colimit.ι_desc (cocone.of_function p) b

def sigma.map
  {f : β → C} [has_coproduct f] {g : β → C} [has_coproduct g] (k : Π b, f b ⟶ g b) :
  (limits.sigma f) ⟶ (limits.sigma g) :=
sigma.desc (λ b, k b ≫ sigma.ι g b)

@[simp] lemma sigma.ι_map {f : β → C} [has_coproduct f] {g : β → C} [has_coproduct g] (k : Π b, f b ⟶ g b) (b : β) :
  sigma.ι f b ≫ sigma.map k = k b ≫ sigma.ι g b :=
by erw is_colimit.fac; refl

def sigma.pre {α} (f : α → C) [has_coproduct.{u v} f] (h : β → α) [has_coproduct (f ∘ h)] :
  limits.sigma (f ∘ h) ⟶ limits.sigma f :=
sigma.desc (λ g, sigma.ι f (h g))

@[simp] lemma sigma.ι_pre {α} (f : α → C) [has_coproduct.{u v} f] (h : β → α) [has_coproduct (f ∘ h)] (b : β) :
  sigma.ι (f ∘ h) b ≫ sigma.pre f h = sigma.ι f (h b) :=
by erw is_colimit.fac; refl

section
variables {D : Type u} [𝒟 : category.{u v} D]
include 𝒟

def sigma.post (f : β → C) [has_coproduct f] (G : C ⥤ D) [has_coproduct (G.obj ∘ f)] :
  (limits.sigma (G.obj ∘ f)) ⟶ G (limits.sigma f) :=
@is_colimit.desc _ _ _ _ _
  (sigma.cofan (G.obj ∘ f))
  (sigma.universal_property _)
  { X := _,
    ι := { app := λ b, G.map (sigma.ι f b) } }

@[simp] lemma sigma.ι_post (f : β → C) [has_coproduct f] (G : C ⥤ D) [has_coproduct (G.obj ∘ f)] (b : β) :
  sigma.ι _ b ≫ sigma.post f G = G.map (sigma.ι f b) :=
by erw is_colimit.fac; refl
end

@[extensionality] lemma sigma.hom_ext
  (f : β → C) [has_coproduct f] {X : C} (g h : limits.sigma f ⟶ X) (w : ∀ b, sigma.ι f b ≫ g = sigma.ι f b ≫ h) :
  g = h :=
colimit.hom_ext w

@[simp] lemma sigma.map_desc
  [has_coproducts_of_shape.{u v} C β] {f : β → C} {g : β → C} {P : C} (k : Π b, f b ⟶ g b) (p : Π b, g b ⟶ P) :
  sigma.map k ≫ sigma.desc p = sigma.desc (λ b, k b ≫ p b) :=
colimit.map_desc (cocone.of_function p) (nat_trans.of_function k)

-- FIXME continue fixing the `has_coproduct` typeclass arguments.

-- @[simp] lemma sigma.map_map {f1 : β → C} {f2 : β → C} {f3 : β → C}
--   (k1 : Π b, f1 b ⟶ f2 b) (k2 : Π b, f2 b ⟶ f3 b) :
--   sigma.map k1 ≫ sigma.map k2 = sigma.map (λ b, k1 b ≫ k2 b) :=
-- begin
--   /- `obviously` says -/
--   ext1,
--   simp,
--   rw ←category.assoc,
--   simp,
-- end.

-- @[simp] lemma sigma.pre_desc {α : Type v} {f : β → C} {P : C} (p : Π b, f b ⟶ P) (h : α → β) :
--   sigma.pre _ h ≫ sigma.desc p = sigma.desc (λ a, p (h a)) :=
-- begin
--   /- `obviously` says -/
--   ext1,
--   simp,
--   rw ←category.assoc,
--   simp,
-- end

-- def sigma.pre_map {α : Type v} {f g : β → C} (k : Π b : β, f b ⟶ g b) (e : α → β) :
--   sigma.pre f e ≫ sigma.map k = sigma.map (λ a, k (e a)) ≫ sigma.pre g e :=
-- begin
--   /- `obviously` says -/
--   ext1,
--   rw ←category.assoc,
--   erw sigma.ι_desc,
--   rw ←category.assoc,
--   simp,
-- end.

-- @[simp] lemma sigma.pre_pre {γ δ : Type v} (f : β → C) (g : γ → β) (h : δ → γ) :
--   sigma.pre (f ∘ g) h ≫ sigma.pre f g = sigma.pre f (g ∘ h) :=
-- begin
--   ext1,
--   rw ←category.assoc,
--   simp,
--   rw sigma.ι_pre f,
-- end.

-- section
-- variables {D : Type u} [category.{u v} D] [has_coproducts.{u v} D]

-- @[simp] def sigma.post_desc {f : β → C} {P : C} (k : Π b : β, f b ⟶ P) (G : C ⥤ D) :
--   sigma.post f G ≫ G.map (sigma.desc k) = sigma.desc (λ b, G.map (k b)) :=
-- begin
--   /- `obvously` says -/
--   ext1, simp,
--   rw ←category.assoc,
--   rw sigma.ι_post,
--   rw ←functor.map_comp,
--   rw sigma.ι_desc,
-- end.

-- def sigma.map_post {f g : β → C} (k : Π b : β, f b ⟶ g b) (H : C ⥤ D) :
--   @sigma.map _ _ _ _ (H.obj ∘ f) (H.obj ∘ g) (λ b, H.map (k b)) ≫ sigma.post g H =
--     sigma.post f H ≫ H.map (sigma.map k) :=
-- begin
--   /- `obviously` says -/
--   ext1,
--   dsimp at *,
--   rw ←category.assoc,
--   simp,
--   rw ←functor.map_comp,
--   rw ←category.assoc,
--   simp,
--   rw ←functor.map_comp,
--   rw ←functor.map_comp,
--   rw sigma.ι_map,
-- end.

-- def sigma.pre_post {α} (f : β → C) (g : α → β) (G : C ⥤ D) :
--   sigma.pre (G.obj ∘ f) g ≫ sigma.post f G = sigma.post (f ∘ g) G ≫ G.map (sigma.pre f g) :=
-- begin
--   /- `tidy` says -/
--   ext1,
--   dsimp at *,
--   rw [←category.assoc, sigma.ι_pre, sigma.ι_post, ←category.assoc,
--       sigma.ι_post, ←functor.map_comp, sigma.ι_pre]
-- end

-- @[simp] def sigma.post_post
--   {E : Type u} [category.{u v} E] [has_coproducts.{u v} E] (f : β → C) (G : C ⥤ D) (H : D ⥤ E) :
--   sigma.post (G.obj ∘ f) H ≫ H.map (sigma.post f G) = sigma.post f (G ⋙ H) :=
-- begin
--   /- `obviously` says -/
--   ext1,
--   rw ←category.assoc,
--   rw sigma.ι_post,
--   rw ←functor.map_comp,
--   rw sigma.ι_post,
--   erw sigma.ι_post f (G ⋙ H) b,
--   refl
-- end.
end
end coproducts

-- FIXME restore these

-- def has_binary_coproducts_from_has_products : has_binary_coproducts.{u v} C :=
-- { cospan := λ Y Z,
--   begin
--     let f : ulift bool → C := (λ b : ulift bool, cond b.down Y Z),
--     exact { X := limits.sigma f, ι₁ := sigma.ι f ⟨ tt ⟩, ι₂ := sigma.ι f ⟨ ff ⟩ }
--   end,
--   is_binary_coproduct := λ Y Z,
--   { desc := λ s, sigma.desc (λ b, bool.cases_on b.down s.ι₂ s.ι₁),
--     uniq' := λ s m w₁ w₂,
--     begin
--       dsimp at *, ext1, cases b, cases b, tidy,
--     end } }

end category_theory.limits
