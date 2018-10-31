-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Reid Barton, Mario Carneiro

import category_theory.whiskering
import category_theory.limits.cones

open category_theory

namespace category_theory.limits

universes u v w

structure Small_Category :=
(J : Type v)
[𝒥 : small_category J]

instance Diagram_category (J : Small_Category.{v}) : small_category J.J := J.𝒥

variables {J : Type v} [small_category J]
variables (C : Type u) [𝒞 : category.{u v} C]
include 𝒞

structure Diagram extends Small_Category :=
(F : J ⥤ C)

variables {C}

section limit
variables {F : J ⥤ C}

structure is_limit (t : cone F) :=
(lift : ∀ (s : cone F), s.X ⟶ t.X)
(fac'  : ∀ (s : cone F) (j : J), (lift s ≫ t.π j) = s.π j . obviously)
(uniq' : ∀ (s : cone F) (m : s.X ⟶ t.X) (w : ∀ j : J, (m ≫ t.π j) = s.π j), m = lift s . obviously)

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

-- Somewhat awkward binders, so we can write `apply is_limit_invariance r`,
-- and get goals saying that `r ≅ t` and `r` is a limit cone.
def is_limit_invariance (r : cone F) {t : cone F} (i : r ≅ t) (P : is_limit r) : is_limit t :=
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
  (∀ j, φ ≫ t.π j = s.π j) ↔ (φ = is_limit.lift h s) :=
/- obviously says: -/
⟨ is_limit.uniq h s φ,
  begin
    intros a j,
    rw a,
    rw ←is_limit.fac h,
    simp at *,
  end ⟩

lemma is_limit.hom_lift (h : is_limit t) {X' : C} (m : X' ⟶ t.X) :
  m = h.lift { X := X', π := { app := λ b, m ≫ t.π b } } :=
h.uniq { X := X', π := { app := λ b, m ≫ t.π b } } m (λ b, rfl)

def is_limit.of_lift_universal
  (lift : Π (s : cone F), s.X ⟶ t.X)
  (universal : Π (s : cone F) (φ : s.X ⟶ t.X), (∀ j : J, (φ ≫ t.π j) = s.π j) ↔ (φ = lift s)) : is_limit t :=
{ lift := lift,
  fac'  := λ s j, ((universal s (lift s)).mpr (eq.refl (lift s))) j,
  uniq' := λ s φ, (universal s φ).mp }
end limit

class has_limits_of {A : Type v} (Q : A → Diagram.{u v} C) :=
(cone : Π a : A, cone (Q a).F)
(is_limit : Π a : A, is_limit (cone a))

variables (J C)

class has_limits_of_shapes {A : Type v} (D : A → Small_Category) :=
(cone : Π {a : A} (F : (D a).J ⥤ C), cone F)
(is_limit : Π {a : A} (F : (D a).J ⥤ C), is_limit (cone F))

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

instance has_limit_of_has_limits_of_shape
  {J : Type v} [small_category J] [has_limits_of_shape.{u v} J C] (F : J ⥤ C) : has_limit F :=
{ cone := has_limits_of_shape.cone F,
  is_limit := has_limits_of_shape.is_limit F }

instance has_limit_of_has_limits_of
  {A : Type v} {Q : A → Diagram.{u v} C} [has_limits_of.{u v} Q] (a : A) : has_limit (Q a).F :=
{ cone := has_limits_of.cone Q a,
  is_limit := has_limits_of.is_limit Q a }

instance has_limits_of_shape_of_has_limits
  {J : Type v} [small_category J] [has_limits.{u v} C] : has_limits_of_shape.{u v} J C :=
{ cone := λ F, has_limits.cone F,
  is_limit := λ F, has_limits.is_limit F }

section colimit
variables {F : J ⥤ C}

structure is_colimit (t : cocone F) :=
(desc : ∀ (s : cocone F), t.X ⟶ s.X)
(fac'  : ∀ (s : cocone F) (j : J), (t.ι j ≫ desc s) = s.ι j . obviously)
(uniq' : ∀ (s : cocone F) (m : t.X ⟶ s.X) (w : ∀ j : J, (t.ι j ≫ m) = s.ι j), m = desc s . obviously)

restate_axiom is_colimit.fac'
attribute [simp] is_colimit.fac
restate_axiom is_colimit.uniq'

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
  (∀ j, t.ι j ≫ φ = s.ι j) ↔ (φ = is_colimit.desc h s) :=
⟨ is_colimit.uniq h s φ,
  begin
    intros a j,
    rw a,
    rw ←is_colimit.fac h,
    simp at *,
  end ⟩

def is_colimit.of_desc_universal
  (desc : Π (s : cocone F), t.X ⟶ s.X)
  (universal : Π (s : cocone F) (φ : t.X ⟶ s.X), (∀ j : J, (t.ι j ≫ φ) = s.ι j) ↔ (φ = desc s)) : is_colimit t :=
{ desc := desc,
  fac'  := λ s j, ((universal s (desc s)).mpr (eq.refl (desc s))) j,
  uniq' := λ s φ, (universal s φ).mp }

end colimit

class has_colimits_of {A : Type v} (Q : A → Diagram.{u v} C) :=
(cocone : Π a : A, cocone (Q a).F)
(is_colimit : Π a : A, is_colimit (cocone a))

variables (J C)

class has_colimits_of_shapes {A : Type v} (D : A → Small_Category) :=
(cocone : Π {a : A} (F : (D a).J ⥤ C), cocone F)
(is_colimit : Π {a : A} (F : (D a).J ⥤ C), is_colimit (cocone F))

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

instance has_colimit_of_has_colimits_of
  {A : Type v} {Q : A → Diagram.{u v} C} [has_colimits_of.{u v} Q] (a : A) : has_colimit (Q a).F :=
{ cocone := has_colimits_of.cocone Q a,
  is_colimit := has_colimits_of.is_colimit Q a }

instance has_colimits_of_shape_of_has_colimits
  {J : Type v} [small_category J] [has_colimits.{u v} C] : has_colimits_of_shape.{u v} J C :=
{ cocone := λ F, has_colimits.cocone F,
  is_colimit := λ F, has_colimits.is_colimit F }



section

def limit.cone (F : J ⥤ C) [has_limit F] : cone F := has_limit.cone.{u v} F
def limit (F : J ⥤ C) [has_limit F] := (limit.cone F).X
def limit.π (F : J ⥤ C) [has_limit F] (j : J) : limit F ⟶ F j := (((limit.cone F).π) : Π j : J, limit F ⟶ F j) j
@[simp] lemma limit.w (F : J ⥤ C) [has_limit F] {j j' : J} (f : j ⟶ j') :
  limit.π F j ≫ F.map f = limit.π F j' := (limit.cone F).w f
def limit.universal_property (F : J ⥤ C) [has_limit F] : is_limit (limit.cone F) :=
has_limit.is_limit.{u v} F

-- We could make `F` an implicit argument here, but it seems to make usage more confusing.
def limit.lift (F : J ⥤ C) [has_limit F] (c : cone F) : c.X ⟶ limit F := (limit.universal_property F).lift c
@[simp] lemma limit.universal_property_lift {F : J ⥤ C} [has_limit F] (c : cone F) :
  (limit.universal_property F).lift c = limit.lift F c := rfl

@[simp] lemma limit.lift_π {F : J ⥤ C} [has_limit F] (c : cone F) (j : J) :
  limit.lift F c ≫ limit.π F j = c.π j :=
is_limit.fac _ c j

-- We need to be really explicit about the coercion we're simplifying here.
@[simp] lemma limit.cone_π {F : J ⥤ C} [has_limit F] (j : J) :
  (((limit.cone F).π) : Π j : J, ((limit.cone F).X ⟶ F j)) j = (@limit.π J _ C _ F _ j) := rfl

def limit.cone_morphism {F : J ⥤ C} [has_limit F] (c : cone F) : cone_morphism c (limit.cone F) :=
{ hom := (limit.lift F) c }

@[simp] lemma limit.cone_morphism_hom {F : J ⥤ C} [has_limit F] (c : cone F) :
  (limit.cone_morphism c).hom = limit.lift F c := rfl
@[simp] lemma limit.cone_morphism_π {F : J ⥤ C} [has_limit F] (c : cone F) (j : J) :
  (limit.cone_morphism c).hom ≫ (limit.π F j) = c.π j :=
by erw is_limit.fac

@[extensionality] lemma limit.hom_ext {F : J ⥤ C} [has_limit F] {X : C}
  {f g : X ⟶ limit F}
  (w : ∀ j, f ≫ limit.π F j = g ≫ limit.π F j) : f = g :=
begin
  let c : cone F :=
  { X := X,
    π := { app := λ j, f ≫ limit.π F j }},
  have p_f := (limit.universal_property F).uniq c f (λ j, by simp),
  have p_g := (limit.universal_property F).uniq c g (λ j, eq.symm (w j)),
  rw [p_f, p_g]
end

lemma limit.lift_extend {F : J ⥤ C} [has_limit F] (c : cone F) {X : C} (f : X ⟶ c.X) :
  limit.lift F (c.extend f) = f ≫ limit.lift F c :=
by obviously

/-- `limit F` is functorial in `F`. -/
@[simp] def lim [has_limits_of_shape.{u v} J C] : (J ⥤ C) ⥤ C :=
{ obj := λ F, limit F,
  map' := λ F F' t, limit.lift F' $
  { X := limit F,
    π :=
    { app := λ j, limit.π F j ≫ t j,
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
  lim.map α ≫ limit.π G j = limit.π F j ≫ α j :=
begin
  erw is_limit.fac,
  refl
end

@[simp] lemma limit.lift_map [has_limits_of_shape.{u v} J C] {F G : J ⥤ C} (c : cone F) (α : F ⟹ G) :
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

def limit.pre (F : J ⥤ C) [has_limit F] (E : K ⥤ J) [has_limit (E ⋙ F)] : limit F ⟶ limit (E ⋙ F) :=
limit.lift (E ⋙ F)
{ X := limit F,
  π := { app := λ k, limit.π F (E k) } }

@[simp] lemma limit.pre_π (F : J ⥤ C) [has_limit F] (E : K ⥤ J) [has_limit (E ⋙ F)] (k : K) :
  limit.pre F E ≫ limit.π (E ⋙ F) k = limit.π F (E k) :=
begin
  erw is_limit.fac,
  refl,
end

@[simp] lemma limit.lift_pre {F : J ⥤ C} [has_limit F] (c : cone F) (E : K ⥤ J) [has_limit (E ⋙ F)] :
  limit.lift F c ≫ limit.pre F E = limit.lift (E ⋙ F) (c.whisker E) :=
by obviously

lemma limit.map_pre
  [has_limits_of_shape.{u v} J C] [has_limits_of_shape.{u v} K C] {F G : J ⥤ C} (α : F ⟹ G) (E : K ⥤ J) :
  lim.map α ≫ limit.pre G E = limit.pre F E ≫ lim.map (whisker_left E α) :=
begin
  /- `obviously` says -/
  ext1, dsimp at *, simp at *,
  erw [←category.assoc, is_limit.fac],
  refl,
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

def limit.post (F : J ⥤ C) [has_limit F] (G : C ⥤ D) [has_limit (F ⋙ G)] : G (limit F) ⟶ limit (F ⋙ G) :=
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
begin
  erw is_limit.fac,
  refl
end

@[simp] lemma limit.lift_post {F : J ⥤ C} [has_limit F] (c : cone F) (G : C ⥤ D) [has_limit (F ⋙ G)] :
  G.map (limit.lift F c) ≫ limit.post F G = limit.lift (F ⋙ G) (G.map_cone c) :=
begin
  /- `obviously` says -/
  ext1, dsimp at *, simp at *,
  erw ←functor.map_comp,
  simp,
  erw category.id_comp,
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
  rw category.id_comp,
  rw ← category.assoc,
  simp,
end.

lemma limit.pre_post
  {K : Type v} [small_category K]
  (F : J ⥤ C) [has_limit F] (E : K ⥤ J) [has_limit (E ⋙ F)] (G : C ⥤ D) [has_limit (F ⋙ G)] [has_limit ((E ⋙ F) ⋙ G)]:
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
-- FIXME don't use has_colimits

def colimit.cocone (F : J ⥤ C) [has_colimit F] : cocone F := has_colimit.cocone.{u v} F
def colimit (F : J ⥤ C) [has_colimit F] := (colimit.cocone F).X
def colimit.ι (F : J ⥤ C) [has_colimit F] (j : J) : F j ⟶ colimit F := (((colimit.cocone F).ι) : Π j : J, F j ⟶ colimit F) j
@[simp] lemma colimit.w (F : J ⥤ C) [has_colimit F] {j j' : J} (f : j ⟶ j') : F.map f ≫ colimit.ι F j' = colimit.ι F j :=
(colimit.cocone F).w f
def colimit.universal_property (F : J ⥤ C) [has_colimit F] : is_colimit (colimit.cocone F) :=
has_colimit.is_colimit.{u v} F

def colimit.desc (F : J ⥤ C) [has_colimit F] (c : cocone F) : colimit F ⟶ c.X := (colimit.universal_property F).desc c
@[simp] lemma colimit.universal_property_desc (F : J ⥤ C) [has_colimit F] (c : cocone F) :
  (colimit.universal_property F).desc c = colimit.desc F c := rfl

@[simp] lemma colimit.ι_desc (F : J ⥤ C) [has_colimit F] (c : cocone F) (j : J) :
  colimit.ι F j ≫ colimit.desc F c = c.ι j :=
is_colimit.fac _ c j

@[simp] lemma colimit.cone_ι (F : J ⥤ C) [has_colimit F] (j : J) :
  (((colimit.cocone F).ι) : Π j : J, (F j ⟶ (colimit.cocone F).X)) j = (@colimit.ι J _ C _ F _ j) := rfl

def colimit.cocone_morphism (F : J ⥤ C) [has_colimit F] (c : cocone F) : cocone_morphism (colimit.cocone F) c :=
{ hom := (colimit.desc F) c }

@[simp] lemma colimit.cocone_morphism_hom {F : J ⥤ C} [has_colimit F] (c : cocone F) :
  (colimit.cocone_morphism F c).hom = colimit.desc F c := rfl
@[simp] lemma colimit.ι_cocone_morphism {F : J ⥤ C} [has_colimit F] (c : cocone F) (j : J) :
  (colimit.ι F j) ≫ (colimit.cocone_morphism F c).hom = c.ι j :=
by erw is_colimit.fac

@[extensionality] lemma colimit.hom_ext {F : J ⥤ C} [has_colimit F] {X : C}
  (f g : colimit F ⟶ X)
  (w : ∀ j, colimit.ι F j ≫ f = colimit.ι F j ≫ g) : f = g :=
begin
  let c : cocone F :=
  { X := X,
    ι :=
    { app := λ j, colimit.ι F j ≫ f,
      naturality' :=
      begin
        /- obviously says: -/
        intros j j' f_1,
        erw [← category.assoc, limits.cocone.w],
        simp,
        dsimp,
        simp,
      end } },
  have p_f := (colimit.universal_property F).uniq c f (λ j, by simp),
  have p_g := (colimit.universal_property F).uniq c g (λ j, eq.symm (w j)),
  rw [p_f, p_g],
end

lemma colimit.desc_extend (F : J ⥤ C) [has_colimit F] (c : cocone F) {X : C} (f : c.X ⟶ X) :
  colimit.desc F (c.extend f) = colimit.desc F c ≫ f :=
begin
  /- obviously says: -/
  ext1, simp at *, erw ←category.assoc, simp, refl
end

/-- `colimit F` is functorial in `F`. -/
@[simp] def colim [has_colimits_of_shape.{u v} J C] : (J ⥤ C) ⥤ C :=
{ obj := λ F, colimit F,
  map' := λ F F' t, colimit.desc F $
  { X := colimit F',
    ι :=
    { app := λ j, t j ≫ colimit.ι F' j,
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

@[simp] lemma colim_ι_map [has_colimits_of_shape.{u v} J C] {F G : J ⥤ C} (α : F ⟹ G) (j : J) : colimit.ι F j ≫ colim.map α = α j ≫ colimit.ι G j :=
begin
  erw is_colimit.fac,
  refl
end

@[simp] lemma colimit.map_desc [has_colimits_of_shape.{u v} J C] {F G : J ⥤ C} (c : cocone G) (α : F ⟹ G) :
  colim.map α ≫ colimit.desc G c = colimit.desc F (c.precompose α) :=
begin
  /- `obviously` says -/
  ext1, dsimp at *, simp at *,
  erw ←category.assoc,
  simp,
  refl
end

section
variables {K : Type v} [𝒦 : small_category K]
include 𝒦

def colimit.pre (F : J ⥤ C) [has_colimit F] (E : K ⥤ J) [has_colimit (E ⋙ F)] : colimit (E ⋙ F) ⟶ colimit F :=
colimit.desc (E ⋙ F)
{ X := colimit F,
  ι := { app := λ k, colimit.ι F (E k) } }

@[simp] lemma colimit.ι_pre (F : J ⥤ C) [has_colimit F] (E : K ⥤ J) [has_colimit (E ⋙ F)] (k : K) :
  colimit.ι (E ⋙ F) k ≫ colimit.pre F E = colimit.ι F (E k) :=
begin
  erw is_colimit.fac,
  refl
end

@[simp] lemma colimit.desc_pre {F : J ⥤ C} [has_colimit F] (c : cocone F) (E : K ⥤ J) [has_colimit (E ⋙ F)] :
  colimit.pre F E ≫ colimit.desc F c = colimit.desc (E ⋙ F) (c.whisker E) :=
begin
  /- `obviously` says -/
  ext1, dsimp at *, simp at *,
  rw ←category.assoc,
  simp,
  refl,
end

lemma colimit.map_pre
  [has_colimits_of_shape.{u v} J C] [has_colimits_of_shape.{u v} K C]
  {F G : J ⥤ C} (α : F ⟹ G) (E : K ⥤ J) :
  colimit.pre F E ≫ colim.map α = colim.map (whisker_left E α) ≫ colimit.pre G E :=
begin
  /- `obviously` says -/
  ext1, dsimp at *, simp at *,
  conv {to_rhs, rw ←category.assoc},
  simp,
  refl
end.

@[simp] lemma colimit.pre_pre
  {L : Type v} [small_category L]
  (F : J ⥤ C) [has_colimit F] (E : K ⥤ J) [has_colimit (E ⋙ F)] (D : L ⥤ K) [has_colimit (D ⋙ E ⋙ F)]:
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

def colimit.post (F : J ⥤ C) [has_colimit F] (G : C ⥤ D) [has_colimit (F ⋙ G)] : colimit (F ⋙ G) ⟶ G (colimit F) :=
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

@[simp] lemma colimit.ι_post (F : J ⥤ C) [has_colimit F] (G : C ⥤ D) [has_colimit (F ⋙ G)] (j : J) :
  colimit.ι (F ⋙ G) j ≫ colimit.post F G = G.map (colimit.ι F j) :=
begin
  erw is_colimit.fac,
  refl
end

-- @[simp] lemma colimit.desc_post {F : J ⥤ C} (c : cocone F) (G : C ⥤ D) :
--   colimit.post F G ≫ G.map (colimit.desc F c) = colimit.desc (F ⋙ G) (G.map_cocone c) :=
-- begin
--   /- `obviously` says -/
--   ext1, dsimp at *, simp at *,
--   rw ←category.assoc,
--   simp,
--   rw ←functor.map_comp,
--   simp,
--   refl,
-- end

-- lemma colimit.post_map {F G : J ⥤ C} (α : F ⟹ G) (H : C ⥤ D) :
--   colimit.post F H ≫ H.map (colim.map α) = colim.map (whisker_right α H) ≫ colimit.post G H :=
-- begin
--   /- `obviously` says -/
--   ext1, dsimp at *, simp at *,
--   erw [←category.assoc, is_colimit.fac, category.assoc, is_colimit.fac, ←functor.map_comp],
--   refl
-- end

-- lemma colimit.pre_post {K : Type v} [small_category K] (F : J ⥤ C) (E : K ⥤ J) (G : C ⥤ D) :
--   colimit.pre (F ⋙ G) E ≫ colimit.post F G = colimit.post (E ⋙ F) G ≫ G.map (colimit.pre F E) :=
-- begin
--   /- `obviously` says -/
--   ext1, dsimp at *,
--   rw ←category.assoc,
--   simp,
--   rw ←category.assoc,
--   erw colimit.ι_post (E ⋙ F) G,
--   rw ←functor.map_comp,
--   rw colimit.ι_pre,
-- end.

-- @[simp] lemma colimit.post_post
--   {E : Type u} [category.{u v} E] [has_colimits.{u v} E] (F : J ⥤ C) (G : C ⥤ D) (H : D ⥤ E) :
--   colimit.post (F ⋙ G) H ≫ H.map (colimit.post F G) = colimit.post F (G ⋙ H) :=
-- begin
--   /- `obviously` says -/
--   ext1, dsimp at *,
--   rw ←category.assoc,
--   simp,
--   rw ←functor.map_comp,
--   erw colimit.ι_post,
--   erw colimit.ι_post F (G ⋙ H),
--   simp,
-- end
-- end

end
end

end category_theory.limits