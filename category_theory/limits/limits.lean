-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Reid Barton, Mario Carneiro

import category_theory.whiskering
import category_theory.yoneda
import category_theory.limits.cones
import data.equiv.basic

open category_theory

namespace category_theory.limits

universes u v w

variables {J : Type v} [small_category J]
variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

section limit
variables {F : J ⥤ C}

structure is_limit (t : cone F) :=
(lift : ∀ (s : cone F), s.X ⟶ t.X)
(fac'  : ∀ (s : cone F) (j : J), (lift s ≫ t.π.app j) = s.π.app j . obviously)
(uniq' : ∀ (s : cone F) (m : s.X ⟶ t.X) (w : ∀ j : J, (m ≫ t.π.app j) = s.π.app j), 
  m = lift s . obviously)

restate_axiom is_limit.fac'
attribute [simp] is_limit.fac
restate_axiom is_limit.uniq'

@[simp] lemma is_limit.lift_self {t : cone F} (h : is_limit t) : h.lift t = 𝟙 t.X :=
begin
  symmetry,
  apply h.uniq,
  tidy,
end

def limit_cone.ext {s t : cone F} (P : is_limit s) (Q : is_limit t) : s ≅ t :=
{ hom :=
  { hom := Q.lift s,
    w' := λ j, Q.fac s j },
  inv := { hom := P.lift t },
  hom_inv_id' :=
  begin
    ext, simp,
    rw ← is_limit.lift_self P,
    apply P.uniq,
    tidy,
  end,
  inv_hom_id' :=
  begin
    ext, simp,
    rw ← is_limit.lift_self Q,
    apply Q.uniq,
    tidy,
  end }

def is_limit_invariance (r t : cone F) (i : r ≅ t) (P : is_limit r) : is_limit t :=
{ lift := λ s, P.lift s ≫ i.hom.hom,
  uniq' :=
  begin
    tidy,
    have h : m ≫ i.inv.hom = P.lift s,
    { apply P.uniq,
      intro j,
      rw category.assoc,
      rw i.inv.w,
      exact w j },
    replace h := congr_arg (λ p, p ≫ i.hom.hom) h,
    dsimp at h,
    rw category.assoc at h,
    have p := congr_arg cone_morphism.hom i.inv_hom_id,
    dsimp at p,
    rw p at h,
    simp at h,
    exact h
  end }

variables {t : cone F}

@[extensionality] lemma is_limit.ext (P Q : is_limit t) : P = Q :=
begin
  tactic.unfreeze_local_instances,
  cases P, cases Q,
  congr,
  ext1,
  solve_by_elim,
 end

instance is_limit_subsingleton : subsingleton (is_limit t) := by tidy

lemma is_limit.universal (h : is_limit t) (s : cone F) (φ : s.X ⟶ t.X) :
  (∀ j, φ ≫ t.π.app j = s.π.app j) ↔ (φ = is_limit.lift h s) :=
/- obviously says: -/
⟨ is_limit.uniq h s φ,
  begin
    intros a j,
    rw a,
    rw ←is_limit.fac h,
    simp at *,
  end ⟩

lemma is_limit.hom_lift (h : is_limit t) {X' : C} (m : X' ⟶ t.X) :
  m = h.lift { X := X', π := { app := λ b, m ≫ t.π.app b } } :=
h.uniq { X := X', π := { app := λ b, m ≫ t.π.app b } } m (λ b, rfl)

lemma is_limit.hom_ext (h : is_limit t) {W : C} {f g : W ⟶ t.X}
  (w : ∀ j, f ≫ t.π.app j = g ≫ t.π.app j) : f = g :=
by rw [h.hom_lift f, h.hom_lift g]; congr; exact funext w

def is_limit.of_lift_universal
  (lift : Π (s : cone F), s.X ⟶ t.X)
  (universal : Π (s : cone F) (φ : s.X ⟶ t.X),
    (∀ j : J, (φ ≫ t.π.app j) = s.π.app j) ↔ (φ = lift s)) : is_limit t :=
{ lift := lift,
  fac'  := λ s j, ((universal s (lift s)).mpr (eq.refl (lift s))) j,
  uniq' := λ s φ, (universal s φ).mp }

def is_limit.equiv (h : is_limit t) (X' : C) : (X' ⟶ t.X) ≅ ((functor.const J).obj X' ⟹ F) :=
{ hom := λ f, (t.extend f).π,
  inv := λ π, h.lift { X := X', π := π },
  hom_inv_id' := by ext f; apply h.hom_ext; intro j; erw h.fac; refl }

@[simp] lemma is_limit.equiv_hom (h : is_limit t) (X' : C) (f : X' ⟶ t.X) :
  (is_limit.equiv h X').hom f = (t.extend f).π := rfl

def is_limit.natural_equiv (h : is_limit t) : yoneda.obj t.X ≅ F.cones :=
nat_iso.of_components (is_limit.equiv h) (by tidy)

def is_limit.of_extensions_iso (h : is_iso t.extensions) : is_limit t :=
{ lift := λ s, (inv t.extensions).app s.X s.π,
  fac' := λ s j,
    show ((inv t.extensions ≫ t.extensions).app s.X s.π).app j = _,
    by erw @is_iso.inv_hom_id _ _ _ _ _ h; refl,
  uniq' := λ s m hm, begin
    have : m = (t.extensions ≫ inv t.extensions).app s.X m,
      by erw @is_iso.hom_inv_id _ _ _ _ _ h; refl,
    rw this,
    have : s.π = (functor.const J).map m ≫ t.π, by ext j; exact (hm j).symm,
    rw this,
    refl
  end }

def is_limit.of_equiv (e : Π Z, (Z ⟶ t.X) ≃ ((functor.const J).obj Z ⟹ F))
  (h : Π Z f j, (e Z f).app j = f ≫ t.π.app j) : is_limit t :=
⟨λ s, (e s.X).symm s.π,
 λ s j, by rw [←h, equiv.apply_inverse_apply],
 λ s m hm, by rw equiv.eq_symm_apply; ext j; rw [←hm, h]⟩

end limit

variables (J C)

class has_limits :=
(cone : Π {J : Type v} [small_category J] (F : J ⥤ C), cone F)
(is_limit : Π {J : Type v} [small_category J] (F : J ⥤ C), is_limit (cone F))

class has_limits_of_shape :=
(cone : Π F : J ⥤ C, cone F)
(is_limit : Π F : J ⥤ C, is_limit (cone F))

variables {J C}

class has_limit {J : Type v} [small_category J] (F : J ⥤ C) :=
(cone : cone F)
(is_limit : is_limit cone)

def cone.of_representable_cones (F : J ⥤ C) [r : representable F.cones] : cone F :=
{ X := r.X,
  π := r.w.hom.app r.X (𝟙 r.X) }

lemma cone.of_representable_cones_extension (F : J ⥤ C) (r : representable F.cones) :
  (cone.of_representable_cones F).extensions = r.w.hom :=
begin
  ext1 Z, ext1 f,
  have : ((yoneda.obj r.X).map f ≫ r.w.hom.app  Z) (𝟙 _) = _, by rw [r.w.hom.naturality f],
  simpa using this.symm
end

def extensions_iso_of_representable_cones (F : J ⥤ C) [r : representable F.cones] :
  is_iso (cone.of_representable_cones F).extensions :=
{ inv := r.w.inv,
  hom_inv_id' := by rw cone.of_representable_cones_extension; exact r.w.hom_inv_id',
  inv_hom_id' := by rw cone.of_representable_cones_extension; exact r.w.inv_hom_id' }

def has_limit_of_cones_representable (F : J ⥤ C) [r : representable F.cones] : has_limit F :=
{ cone := cone.of_representable_cones F,
  is_limit := is_limit.of_extensions_iso (extensions_iso_of_representable_cones F) }

def cones_representable_of_has_limit (F : J ⥤ C) [has_limit F] : representable F.cones :=
{ X := (has_limit.cone F).X,
  w := (has_limit.is_limit F).natural_equiv }

instance has_limit_of_has_limits_of_shape
  {J : Type v} [small_category J] [has_limits_of_shape.{u v} J C] (F : J ⥤ C) : has_limit F :=
{ cone := has_limits_of_shape.cone F,
  is_limit := has_limits_of_shape.is_limit F }

instance has_limits_of_shape_of_has_limits
  {J : Type v} [small_category J] [has_limits.{u v} C] : has_limits_of_shape.{u v} J C :=
{ cone := λ F, has_limits.cone F,
  is_limit := λ F, has_limits.is_limit F }

section colimit
variables {F : J ⥤ C}

structure is_colimit (t : cocone F) :=
(desc : ∀ (s : cocone F), t.X ⟶ s.X)
(fac'  : ∀ (s : cocone F) (j : J), (t.ι.app j ≫ desc s) = s.ι.app j . obviously)
(uniq' : ∀ (s : cocone F) (m : t.X ⟶ s.X) (w : ∀ j : J, (t.ι.app j ≫ m) = s.ι.app j),
  m = desc s . obviously)

restate_axiom is_colimit.fac'
attribute [simp] is_colimit.fac
restate_axiom is_colimit.uniq'

@[simp] lemma is_colimit.desc_self {t : cocone F} (h : is_colimit t) : h.desc t = 𝟙 t.X :=
begin
  symmetry,
  apply h.uniq,
  tidy,
end

def colimit_cocone.ext {s t : cocone F} (P : is_colimit s) (Q : is_colimit t) : s ≅ t :=
{ hom := { hom := P.desc t },
  inv := { hom := Q.desc s,
    w' := λ j, Q.fac s j },
  hom_inv_id' :=
  begin
    ext, simp,
    rw ← is_colimit.desc_self P,
    apply P.uniq,
    intro j,
    rw ← category.assoc,
    tidy,
  end,
  inv_hom_id' :=
  begin
    ext, simp,
    rw ← is_colimit.desc_self Q,
    apply Q.uniq,
    intro j,
    rw ← category.assoc,
    tidy,
  end }

def is_colimit_invariance (r t : cocone F) (i : r ≅ t) (P : is_colimit r) : is_colimit t :=
{ desc := λ s, i.inv.hom ≫ P.desc s,
  fac' := λ s j, begin rw [←category.assoc, ←i.hom.w], simp, end,
  uniq' :=
  begin
    tidy,
    have h : i.hom.hom ≫ m = P.desc s,
    { apply P.uniq,
      intro j,
      rw ← category.assoc,
      rw i.hom.w,
      exact w j },
    replace h := congr_arg (λ p, i.inv.hom ≫ p) h,
    dsimp at h,
    rw ← category.assoc at h,
    have p := congr_arg cocone_morphism.hom i.inv_hom_id,
    dsimp at p,
    rw p at h,
    simp at h,
    exact h
  end }

variables {t : cocone F}

@[extensionality] lemma is_colimit.ext (P Q : is_colimit t) : P = Q :=
begin
  tactic.unfreeze_local_instances,
  cases P, cases Q,
  congr,
  ext1,
  solve_by_elim,
end

instance is_colimit_subsingleton : subsingleton (is_colimit t) := by tidy

lemma is_colimit.universal (h : is_colimit t) (s : cocone F) (φ : t.X ⟶ s.X) :
  (∀ j, t.ι.app j ≫ φ = s.ι.app j) ↔ (φ = is_colimit.desc h s) :=
⟨ is_colimit.uniq h s φ,
  begin
    intros a j,
    rw a,
    rw ←is_colimit.fac h,
    simp at *,
  end ⟩

lemma is_colimit.hom_desc (h : is_colimit t) {X' : C} (m : t.X ⟶ X') :
  m = h.desc { X := X', ι := { app := λ b, t.ι.app b ≫ m,
    naturality' := by intros X Y f; rw ←category.assoc; dsimp; simp } } :=
h.uniq { X := X', ι := { app := λ b, t.ι.app b ≫ m, naturality' := _ } } m (λ b, rfl)

lemma is_colimit.hom_ext (h : is_colimit t) {W : C} {f g : t.X ⟶ W}
  (w : ∀ j, t.ι.app j ≫ f = t.ι.app j ≫ g) : f = g :=
by rw [h.hom_desc f, h.hom_desc g]; congr; exact funext w

def is_colimit.of_desc_universal
  (desc : Π (s : cocone F), t.X ⟶ s.X)
  (universal : Π (s : cocone F) (φ : t.X ⟶ s.X),
    (∀ j : J, (t.ι.app j ≫ φ) = s.ι.app j) ↔ (φ = desc s)) : is_colimit t :=
{ desc := desc,
  fac'  := λ s j, ((universal s (desc s)).mpr (eq.refl (desc s))) j,
  uniq' := λ s φ, (universal s φ).mp }

def is_colimit.equiv (h : is_colimit t) {W : C} : (t.X ⟶ W) ≃ (F ⟹ (functor.const J).obj W) :=
⟨λ f, t.ι ⊟ (functor.const J).map f,
 λ n, h.desc ⟨W, n⟩,
 λ f, by apply h.hom_ext; intro j; rw h.fac; refl,
 λ n, by ext j; exact h.fac ⟨_, n⟩ j⟩

def is_colimit.of_equiv (e : Π Z, (t.X ⟶ Z) ≃ (F ⟹ (functor.const J).obj Z))
  (h : Π Z f j, (e Z f).app j = t.ι.app j ≫ f) : is_colimit t :=
⟨λ s, (e s.X).symm s.ι,
 λ s j, by rw [←h, equiv.apply_inverse_apply],
 λ s m hm, by rw equiv.eq_symm_apply; ext j; rw [←hm, h]⟩

end colimit

variables (J C)

class has_colimits :=
(cocone : Π {J : Type v} [small_category J] (F : J ⥤ C), cocone F)
(is_colimit : Π {J : Type v} [small_category J] (F : J ⥤ C), is_colimit (cocone F))

class has_colimits_of_shape :=
(cocone : Π F : J ⥤ C, cocone F)
(is_colimit : Π F : J ⥤ C, is_colimit (cocone F))

variables {J C}

class has_colimit {J : Type v} [small_category J] (F : J ⥤ C) :=
(cocone : cocone F)
(is_colimit : is_colimit cocone)

instance has_colimit_of_has_colimits_of_shape
  {J : Type v} [small_category J] [has_colimits_of_shape.{u v} J C] (F : J ⥤ C) : has_colimit F :=
{ cocone := has_colimits_of_shape.cocone F,
  is_colimit := has_colimits_of_shape.is_colimit F }

instance has_colimits_of_shape_of_has_colimits
  {J : Type v} [small_category J] [has_colimits.{u v} C] : has_colimits_of_shape.{u v} J C :=
{ cocone := λ F, has_colimits.cocone F,
  is_colimit := λ F, has_colimits.is_colimit F }



section

def limit.cone (F : J ⥤ C) [has_limit F] : cone F := has_limit.cone.{u v} F
def limit (F : J ⥤ C) [has_limit F] := (limit.cone F).X
def limit.π (F : J ⥤ C) [has_limit F] (j : J) : limit F ⟶ F.obj j :=
(limit.cone F).π.app j
@[simp] lemma limit.w (F : J ⥤ C) [has_limit F] {j j' : J} (f : j ⟶ j') :
  limit.π F j ≫ F.map f = limit.π F j' := (limit.cone F).w f
def limit.universal_property (F : J ⥤ C) [has_limit F] : is_limit (limit.cone F) :=
has_limit.is_limit.{u v} F

-- We could make `F` an implicit argument here, but it seems to make usage more confusing.
def limit.lift (F : J ⥤ C) [has_limit F] (c : cone F) : c.X ⟶ limit F :=
(limit.universal_property F).lift c
@[simp] lemma limit.universal_property_lift {F : J ⥤ C} [has_limit F] (c : cone F) :
  (limit.universal_property F).lift c = limit.lift F c := rfl

@[simp] lemma limit.lift_π {F : J ⥤ C} [has_limit F] (c : cone F) (j : J) :
  limit.lift F c ≫ limit.π F j = c.π.app j :=
is_limit.fac _ c j

-- We need to be really explicit about the coercion we're simplifying here.
@[simp] lemma limit.cone_π {F : J ⥤ C} [has_limit F] (j : J) :
  (limit.cone F).π.app j = (@limit.π J _ C _ F _ j) := rfl

def limit.cone_morphism {F : J ⥤ C} [has_limit F] (c : cone F) : cone_morphism c (limit.cone F) :=
{ hom := (limit.lift F) c }

@[simp] lemma limit.cone_morphism_hom {F : J ⥤ C} [has_limit F] (c : cone F) :
  (limit.cone_morphism c).hom = limit.lift F c := rfl
@[simp] lemma limit.cone_morphism_π {F : J ⥤ C} [has_limit F] (c : cone F) (j : J) :
  (limit.cone_morphism c).hom ≫ (limit.π F j) = c.π.app j :=
by erw is_limit.fac

@[extensionality] lemma limit.hom_ext {F : J ⥤ C} [has_limit F] {X : C}
  {f g : X ⟶ limit F}
  (w : ∀ j, f ≫ limit.π F j = g ≫ limit.π F j) : f = g :=
(limit.universal_property F).hom_ext w

lemma limit.lift_extend {F : J ⥤ C} [has_limit F] (c : cone F) {X : C} (f : X ⟶ c.X) :
  limit.lift F (c.extend f) = f ≫ limit.lift F c :=
by obviously

/-- `limit F` is functorial in `F`. -/
def lim [has_limits_of_shape.{u v} J C] : (J ⥤ C) ⥤ C :=
{ obj := λ F, limit F,
  map := λ F F' t, limit.lift F' $
  { X := limit F,
    π :=
    { app := λ j, limit.π F j ≫ t.app j,
      naturality' :=
      begin
        /- `obviously` says -/
        intros j j' f, simp,
        erw [category.id_comp, ←t.naturality, ←category.assoc, limit.w],
      end } },
  map_comp' :=
  begin
    /- `obviously` says -/
    intros X Y Z f g, ext1, simp,
    conv { to_rhs, rw ←category.assoc },
    simp
  end }.

@[simp] lemma lim_map_π [has_limits_of_shape.{u v} J C] {F G : J ⥤ C} (α : F ⟹ G) (j : J) :
  lim.map α ≫ limit.π G j = limit.π F j ≫ α.app j :=
by erw is_limit.fac

@[simp] lemma limit.lift_map
  [has_limits_of_shape.{u v} J C] {F G : J ⥤ C} (c : cone F) (α : F ⟹ G) :
  limit.lift F c ≫ lim.map α = limit.lift G (c.postcompose α) :=
begin
  /- `obviously` says -/
  ext1, simp,
  erw ←category.assoc,
  simp,
  refl
end

section
variables {K : Type v} [𝒦 : small_category K]
include 𝒦

def limit.pre (F : J ⥤ C)
  [has_limit F] (E : K ⥤ J) [has_limit (E ⋙ F)] : limit F ⟶ limit (E ⋙ F) :=
limit.lift (E ⋙ F)
  { X := limit F,
    π := { app := λ k, limit.π F (E.obj k) } }

@[simp] lemma limit.pre_π (F : J ⥤ C) [has_limit F] (E : K ⥤ J) [has_limit (E ⋙ F)] (k : K) :
  limit.pre F E ≫ limit.π (E ⋙ F) k = limit.π F (E.obj k) :=
by erw is_limit.fac

@[simp] lemma limit.lift_pre
  {F : J ⥤ C} [has_limit F] (c : cone F) (E : K ⥤ J) [has_limit (E ⋙ F)] :
  limit.lift F c ≫ limit.pre F E = limit.lift (E ⋙ F) (c.whisker E) :=
by obviously

lemma limit.map_pre
  [has_limits_of_shape.{u v} J C] [has_limits_of_shape.{u v} K C]
  {F G : J ⥤ C} (α : F ⟹ G) (E : K ⥤ J) :
  lim.map α ≫ limit.pre G E = limit.pre F E ≫ lim.map (whisker_left E α) :=
begin
  /- `obviously` says -/
  ext1, dsimp at *, simp at *,
  erw [←category.assoc, is_limit.fac],
end

@[simp] lemma limit.pre_pre
  {L : Type v} [small_category L]
  (F : J ⥤ C) [has_limit F] (E : K ⥤ J) [has_limit (E ⋙ F)] (D : L ⥤ K) [has_limit (D ⋙ E ⋙ F)] :
  limit.pre F E ≫ limit.pre (E ⋙ F) D = limit.pre F (D ⋙ E) :=
begin
  /- `obviously` says -/
  ext1, dsimp, simp,
  erw limit.pre_π, -- isn't it sad this simp lemma isn't applied by simp?
  refl
end
end

section
variables {D : Type u} [𝒟 : category.{u v} D]
include 𝒟

def limit.post
  (F : J ⥤ C) [has_limit F] (G : C ⥤ D) [has_limit (F ⋙ G)] : G.obj (limit F) ⟶ limit (F ⋙ G) :=
limit.lift (F ⋙ G)
{ X := _,
  π :=
  { app := λ j, G.map (limit.π F j),
    naturality' :=
    begin
      /- `obviously` says -/
      intros j j' f, dsimp at *,
      erw [←functor.map_comp, limits.cone.w, category.id_comp],
      refl
    end } }

@[simp] lemma limit.post_π (F : J ⥤ C) [has_limit F] (G : C ⥤ D) [has_limit (F ⋙ G)] (j : J) :
  limit.post F G ≫ limit.π (F ⋙ G) j = G.map (limit.π F j) :=
by erw is_limit.fac

@[simp] lemma limit.lift_post
  {F : J ⥤ C} [has_limit F] (c : cone F) (G : C ⥤ D) [has_limit (F ⋙ G)] :
  G.map (limit.lift F c) ≫ limit.post F G = limit.lift (F ⋙ G) (G.map_cone c) :=
begin
  /- `obviously` says -/
  ext1, dsimp at *, simp at *,
  erw ←functor.map_comp,
  simp,
end

lemma limit.map_post
  [has_limits_of_shape.{u v} J C] [has_limits_of_shape.{u v} J D]
  {F G : J ⥤ C} (α : F ⟹ G) (H : C ⥤ D) :
/- H (limit F) ⟶ H (limit G) ⟶ limit (G ⋙ H) vs
   H (limit F) ⟶ limit (F ⋙ H) ⟶ limit (G ⋙ H) -/
  H.map (lim.map α) ≫ limit.post G H = limit.post F H ≫ lim.map (whisker_right α H) :=
begin
  /- `obviously` says -/
  ext1, dsimp, simp, dsimp,
  rw ← category.assoc,
  simp,
  rw ←functor.map_comp,
  rw ←functor.map_comp,
  simp,
end.

lemma limit.pre_post
  {K : Type v} [small_category K]
  (F : J ⥤ C) [has_limit F]
  (E : K ⥤ J) [has_limit (E ⋙ F)]
  (G : C ⥤ D) [has_limit (F ⋙ G)] [has_limit ((E ⋙ F) ⋙ G)]:
/- G (limit F) ⟶ G (limit (E ⋙ F)) ⟶ limit ((E ⋙ F) ⋙ G) vs -/
/- G (limit F) ⟶ limit F ⋙ G ⟶ limit (E ⋙ (F ⋙ G)) or -/
  G.map (limit.pre F E) ≫ limit.post (E ⋙ F) G = limit.post F G ≫ limit.pre (F ⋙ G) E :=
begin
  /- `obviously` says -/
  ext1, dsimp at *, simp at *, dsimp at *,
  erw [←functor.map_comp, limit.pre_π F E j, limit.pre_π],
  simp,
end.

@[simp] lemma limit.post_post
  {E : Type u} [category.{u v} E]
  (F : J ⥤ C) [has_limit F] (G : C ⥤ D) [has_limit (F ⋙ G)] (H : D ⥤ E) [has_limit ((F ⋙ G) ⋙ H)] :
/- H G (limit F) ⟶ H (limit (F ⋙ G)) ⟶ limit ((F ⋙ G) ⋙ H) vs -/
/- H G (limit F) ⟶ limit (F ⋙ (G ⋙ H)) or -/
  H.map (limit.post F G) ≫ limit.post (F ⋙ G) H = limit.post F (G ⋙ H) :=
begin
  /- `obviously` says -/
  ext1, dsimp at *, simp at *, dsimp at *,
  erw [←functor.map_comp, limit.post_π],
  conv { to_rhs, rw [limit.post_π] {md:=semireducible} },
  refl,
end
end

end

section

def colimit.cocone (F : J ⥤ C) [has_colimit F] : cocone F := has_colimit.cocone.{u v} F
def colimit (F : J ⥤ C) [has_colimit F] := (colimit.cocone F).X
def colimit.ι (F : J ⥤ C) [has_colimit F] (j : J) : F.obj j ⟶ colimit F :=
(colimit.cocone F).ι.app j
@[simp] lemma colimit.w
  (F : J ⥤ C) [has_colimit F] {j j' : J} (f : j ⟶ j') : F.map f ≫ colimit.ι F j' = colimit.ι F j :=
(colimit.cocone F).w f
def colimit.universal_property (F : J ⥤ C) [has_colimit F] : is_colimit (colimit.cocone F) :=
has_colimit.is_colimit.{u v} F

def colimit.desc (F : J ⥤ C) [has_colimit F] (c : cocone F) : colimit F ⟶ c.X :=
(colimit.universal_property F).desc c
@[simp] lemma colimit.universal_property_desc (F : J ⥤ C) [has_colimit F] (c : cocone F) :
  (colimit.universal_property F).desc c = colimit.desc F c := rfl

@[simp] lemma colimit.ι_desc {F : J ⥤ C} [has_colimit F] (c : cocone F) (j : J) :
  colimit.ι F j ≫ colimit.desc F c = c.ι.app j :=
is_colimit.fac _ c j

@[simp] lemma colimit.cone_ι {F : J ⥤ C} [has_colimit F] (j : J) :
  (colimit.cocone F).ι.app j = (@colimit.ι J _ C _ F _ j) := rfl

def colimit.cocone_morphism
  {F : J ⥤ C} [has_colimit F] (c : cocone F) : cocone_morphism (colimit.cocone F) c :=
{ hom := (colimit.desc F) c }

@[simp] lemma colimit.cocone_morphism_hom {F : J ⥤ C} [has_colimit F] (c : cocone F) :
  (colimit.cocone_morphism c).hom = colimit.desc F c := rfl
@[simp] lemma colimit.ι_cocone_morphism {F : J ⥤ C} [has_colimit F] (c : cocone F) (j : J) :
  (colimit.ι F j) ≫ (colimit.cocone_morphism c).hom = c.ι.app j :=
by erw is_colimit.fac

@[extensionality] lemma colimit.hom_ext {F : J ⥤ C} [has_colimit F] {X : C}
  {f g : colimit F ⟶ X}
  (w : ∀ j, colimit.ι F j ≫ f = colimit.ι F j ≫ g) : f = g :=
(colimit.universal_property F).hom_ext w

lemma colimit.desc_extend (F : J ⥤ C) [has_colimit F] (c : cocone F) {X : C} (f : c.X ⟶ X) :
  colimit.desc F (c.extend f) = colimit.desc F c ≫ f :=
begin
  /- obviously says: -/
  ext1, simp at *, erw ←category.assoc, simp, refl
end

/-- `colimit F` is functorial in `F`. -/
def colim [has_colimits_of_shape.{u v} J C] : (J ⥤ C) ⥤ C :=
{ obj := λ F, colimit F,
  map := λ F F' t, colimit.desc F $
  { X := colimit F',
    ι :=
    { app := λ j, t.app j ≫ colimit.ι F' j,
      naturality' :=
      begin
        /- `obviously` says -/
        intros j j' f,
        erw [←category.assoc,
              nat_trans.naturality,
              category.assoc,
              limits.cocone.w],
        dsimp,
        simp,
      end } },
  map_comp' :=
  begin
    /- `obviously` says -/
    intros X Y Z f g, ext1, dsimp at *, simp at *,
    conv { to_rhs, rw ←category.assoc },
    simp
  end }.

@[simp] lemma colim_ι_map [has_colimits_of_shape.{u v} J C] {F G : J ⥤ C} (α : F ⟹ G) (j : J) :
  colimit.ι F j ≫ colim.map α = α.app j ≫ colimit.ι G j :=
by erw is_colimit.fac

@[simp] lemma colimit.map_desc
  [has_colimits_of_shape.{u v} J C] {F G : J ⥤ C} (c : cocone G) (α : F ⟹ G) :
  colim.map α ≫ colimit.desc G c = colimit.desc F (c.precompose α) :=
begin
  /- `obviously` says -/
  ext1, simp,
  erw ←category.assoc,
  simp,
  refl
end

section
variables {K : Type v} [𝒦 : small_category K]
include 𝒦

def colimit.pre
  (F : J ⥤ C) [has_colimit F]
  (E : K ⥤ J) [has_colimit (E ⋙ F)] : colimit (E ⋙ F) ⟶ colimit F :=
colimit.desc (E ⋙ F)
{ X := colimit F,
  ι := { app := λ k, colimit.ι F (E.obj k) } }

@[simp] lemma colimit.ι_pre (F : J ⥤ C) [has_colimit F] (E : K ⥤ J) [has_colimit (E ⋙ F)] (k : K) :
  colimit.ι (E ⋙ F) k ≫ colimit.pre F E = colimit.ι F (E.obj k) :=
by erw is_colimit.fac

@[simp] lemma colimit.desc_pre
  {F : J ⥤ C} [has_colimit F] (c : cocone F) (E : K ⥤ J) [has_colimit (E ⋙ F)] :
  colimit.pre F E ≫ colimit.desc F c = colimit.desc (E ⋙ F) (c.whisker E) :=
begin
  /- `obviously` says -/
  ext1, dsimp at *, simp at *,
  rw ←category.assoc,
  simp,
end

lemma colimit.map_pre
  [has_colimits_of_shape.{u v} J C] [has_colimits_of_shape.{u v} K C]
  {F G : J ⥤ C} (α : F ⟹ G) (E : K ⥤ J) :
  colimit.pre F E ≫ colim.map α = colim.map (whisker_left E α) ≫ colimit.pre G E :=
begin
  /- `obviously` says -/
  ext1, dsimp,
  conv {to_rhs, rw ←category.assoc},
  simp,
  rw ←category.assoc,
  simp
end.

@[simp] lemma colimit.pre_pre
  {L : Type v} [small_category L]
  (F : J ⥤ C) [has_colimit F]
  (E : K ⥤ J) [has_colimit (E ⋙ F)]
  (D : L ⥤ K) [has_colimit (D ⋙ E ⋙ F)]:
  colimit.pre (E ⋙ F) D ≫ colimit.pre F E = colimit.pre F (D ⋙ E) :=
begin
  /- `obviously` says -/
  ext1, dsimp at *,
  conv { to_lhs, rw [←category.assoc, colimit.ι_pre, is_colimit.fac] {md:=semireducible} },
  conv { to_rhs, rw [is_colimit.fac] {md:=semireducible} },
refl
end

end

section
variables {D : Type u} [𝒟 : category.{u v} D]
include 𝒟

def colimit.post
  (F : J ⥤ C) [has_colimit F]
  (G : C ⥤ D) [has_colimit (F ⋙ G)] : colimit (F ⋙ G) ⟶ G.obj (colimit F) :=
colimit.desc (F ⋙ G)
{ X := _,
  ι :=
  { app := λ j, G.map (colimit.ι F j),
    naturality' :=
    begin
      /- `obviously` says -/
      intros j j' f, dsimp at *,
      erw [←functor.map_comp, limits.cocone.w],
      dsimp,
      simp,
    end } }

@[simp] lemma colimit.ι_post
  (F : J ⥤ C) [has_colimit F] (G : C ⥤ D) [has_colimit (F ⋙ G)] (j : J) :
  colimit.ι (F ⋙ G) j ≫ colimit.post F G = G.map (colimit.ι F j) :=
by erw is_colimit.fac

@[simp] lemma colimit.desc_post
  {F : J ⥤ C} [has_colimit F] (c : cocone F) (G : C ⥤ D) [has_colimit (F ⋙ G)] :
  colimit.post F G ≫ G.map (colimit.desc F c) = colimit.desc (F ⋙ G) (G.map_cocone c) :=
begin
  /- `obviously` says -/
  ext1, dsimp at *, simp at *,
  rw ←category.assoc,
  simp,
  rw ←functor.map_comp,
  simp,
end

lemma colimit.post_map [has_colimits_of_shape.{u v} J C] [has_colimits_of_shape.{u v} J D]
  {F G : J ⥤ C} (α : F ⟹ G) (H : C ⥤ D) :
  colimit.post F H ≫ H.map (colim.map α) = colim.map (whisker_right α H) ≫ colimit.post G H :=
begin
  /- `obviously` says -/
  ext1, dsimp,
  rw [←category.assoc],
  erw [is_colimit.fac],
  dsimp,
  rw [←category.assoc],
  simp,
  rw ← functor.map_comp,
  rw ← functor.map_comp,
  simp,
end

-- TODO, later, as needed
/-
lemma colimit.pre_post {K : Type v} [small_category K]
  (F : J ⥤ C) [has_colimit F] (E : K ⥤ J) [has_colimit (E ⋙ F)]
  (G : C ⥤ D) [has_colimit (F ⋙ G)] [has_colimit (E ⋙ F ⋙ G)] :
  colimit.pre (F ⋙ G) E ≫ colimit.post F G =
    colimit.post (E ⋙ F) G ≫ G.map (colimit.pre F E) := ...

@[simp] lemma colimit.post_post
  {E : Type u} [category.{u v} E]
  (F : J ⥤ C) [has_colimit F]
  (G : C ⥤ D) [has_colimit (F ⋙ G)]
  (H : D ⥤ E) [has_colimit ((F ⋙ G) ⋙ H)] :
  colimit.post (F ⋙ G) H ≫ H.map (colimit.post F G) = colimit.post F (G ⋙ H) := ...
-/

end
end

end category_theory.limits
