-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Reid Barton, Mario Carneiro

import category_theory.whiskering
import category_theory.limits.cones

open category_theory

namespace category_theory.limits

universes u v w

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

section limit
variables {J : Type v} [𝒥 : small_category J]
include 𝒥

structure is_limit {F : J ⥤ C} (t : cone F) :=
(lift : ∀ (s : cone F), s.X ⟶ t.X)
(fac'  : ∀ (s : cone F) (j : J), (lift s ≫ t.π j) = s.π j . obviously)
(uniq' : ∀ (s : cone F) (m : s.X ⟶ t.X) (w : ∀ j : J, (m ≫ t.π j) = s.π j), m = lift s . obviously)

restate_axiom is_limit.fac'
attribute [simp] is_limit.fac
restate_axiom is_limit.uniq'

@[extensionality] lemma is_limit.ext {F : J ⥤ C} {t : cone F} (P Q : is_limit t) : P = Q :=
begin
  tactic.unfreeze_local_instances,
  cases P, cases Q,
  congr,
  ext1,
  solve_by_elim,
 end

lemma is_limit.universal {F : J ⥤ C} {t : cone F} [h : is_limit t] (s : cone F) (φ : s.X ⟶ t.X) :
  (∀ j, φ ≫ t.π j = s.π j) ↔ (φ = is_limit.lift h s) :=
/- obviously says: -/
⟨ is_limit.uniq h s φ,
  begin
    intros a j,
    rw a,
    rw ←is_limit.fac h,
    simp at *,
  end ⟩

def is_limit.of_lift_universal {F : J ⥤ C} {t : cone F}
  (lift : Π (s : cone F), s.X ⟶ t.X)
  (universal : Π (s : cone F) (φ : s.X ⟶ t.X), (∀ j : J, (φ ≫ t.π j) = s.π j) ↔ (φ = lift s)) : is_limit t :=
{ lift := lift,
  fac'  := λ s j, ((universal s (lift s)).mpr (eq.refl (lift s))) j,
  uniq' := λ s φ, (universal s φ).mp }

end limit


section colimit
variables {J : Type v} [𝒥 : small_category J]
include 𝒥

structure is_colimit {F : J ⥤ C} (t : cocone F) :=
(desc : ∀ (s : cocone F), t.X ⟶ s.X)
(fac'  : ∀ (s : cocone F) (j : J), (t.ι j ≫ desc s) = s.ι j . obviously)
(uniq' : ∀ (s : cocone F) (m : t.X ⟶ s.X) (w : ∀ j : J, (t.ι j ≫ m) = s.ι j), m = desc s . obviously)

restate_axiom is_colimit.fac'
attribute [simp] is_colimit.fac
restate_axiom is_colimit.uniq'

@[extensionality] lemma is_colimit.ext {F : J ⥤ C} {t : cocone F} (P Q : is_colimit t) : P = Q :=
begin
  tactic.unfreeze_local_instances,
  cases P, cases Q,
  congr,
  ext1,
  solve_by_elim,
end

lemma is_colimit.universal {F : J ⥤ C} {t : cocone F} [h : is_colimit t] (s : cocone F) (φ : t.X ⟶ s.X) :
  (∀ j, t.ι j ≫ φ = s.ι j) ↔ (φ = is_colimit.desc h s) :=
⟨ is_colimit.uniq h s φ,
  begin
    intros a j,
    rw a,
    rw ←is_colimit.fac h,
    simp at *,
  end ⟩

def is_colimit.of_desc_universal {F : J ⥤ C} {t : cocone F}
  (desc : Π (s : cocone F), t.X ⟶ s.X)
  (universal : Π (s : cocone F) (φ : t.X ⟶ s.X), (∀ j : J, (t.ι j ≫ φ) = s.ι j) ↔ (φ = desc s)) : is_colimit t :=
{ desc := desc,
  fac'  := λ s j, ((universal s (desc s)).mpr (eq.refl (desc s))) j,
  uniq' := λ s φ, (universal s φ).mp }

end colimit

variable (C)

class has_limits :=
(cone : Π {J : Type v} [𝒥 : small_category J] (F : J ⥤ C), cone F)
(is_limit : Π {J : Type v} [𝒥 : small_category J] (F : J ⥤ C), is_limit (cone F) . obviously)

-- also do finite limits? filtered limits? can we do these without lots of repetition below?

variable {C}

section
variables [has_limits.{u v} C] {J : Type v} [𝒥 : small_category J]
include 𝒥

def limit.cone (F : J ⥤ C) : cone F := has_limits.cone.{u v} F
def limit (F : J ⥤ C) := (limit.cone F).X
def limit.π (F : J ⥤ C) (j : J) : limit F ⟶ F j := (limit.cone F).π j
@[simp] lemma limit.w (F : J ⥤ C) {j j' : J} (f : j ⟶ j') : limit.π F j ≫ F.map f = limit.π F j' := (limit.cone F).w f
def limit.universal_property (F : J ⥤ C) : is_limit (limit.cone F) :=
has_limits.is_limit.{u v} C F

def limit.lift (F : J ⥤ C) (c : cone F) : c.X ⟶ limit F := (limit.universal_property F).lift c
@[simp] lemma limit.universal_property_lift (F : J ⥤ C) (c : cone F) : (limit.universal_property F).lift c = limit.lift F c := rfl

@[simp] lemma limit.lift_π (F : J ⥤ C) (c : cone F) (j : J) : limit.lift F c ≫ limit.π F j = c.π j :=
is_limit.fac _ c j

@[simp] lemma limit.cone_π (F : J ⥤ C) (j : J) : (limit.cone F).π j = (@limit.π C _ _ J _ F j) := rfl

def limit.cone_morphism (F : J ⥤ C) (c : cone F) : cone_morphism c (limit.cone F) :=
{ hom := (limit.lift F) c }

@[simp] lemma limit.cone_morphism_hom {F : J ⥤ C} (c : cone F) : (limit.cone_morphism F c).hom = limit.lift F c := rfl
@[simp] lemma limit.cone_morphism_π {F : J ⥤ C} (c : cone F) (j : J) : (limit.cone_morphism F c).hom ≫ (limit.π F j) = c.π j :=
by erw is_limit.fac

@[extensionality] lemma limit.hom_ext {F : J ⥤ C} {X : C}
  (f g : X ⟶ limit F)
  (w : ∀ j, f ≫ limit.π F j = g ≫ limit.π F j) : f = g :=
begin
  let c : cone F :=
  { X := X,
    π := λ j, f ≫ limit.π F j },
  have p_f := (limit.universal_property F).uniq c f (λ j, by simp),
  have p_g := (limit.universal_property F).uniq c g (λ j, eq.symm (w j)),
  rw [p_f, p_g]
end

lemma limit.lift_extend (F : J ⥤ C) (c : cone F) {X : C} (f : X ⟶ c.X) :
  limit.lift F (c.extend f) = f ≫ limit.lift F c :=
by obviously

/-- `limit F` is functorial in `F`. -/
@[simp] def lim : (J ⥤ C) ⥤ C :=
{ obj := limit,
  map' := λ F F' t, limit.lift F' $
    { X := limit F,
      π := λ j, limit.π F j ≫ t j,
      w' :=
      begin
        /- `obviously` says -/
        intros j j' f, dsimp at *, simp at *,
        erw [←nat_trans.naturality, ←category.assoc, limits.cone.w],
        refl
      end },
  map_comp' :=
  begin
    /- `obviously` says -/
    intros X Y Z f g, ext1, dsimp at *, simp at *,
    conv { to_rhs, rw ←category.assoc },
    simp
  end }.

@[simp] lemma lim_map_π {F G : J ⥤ C} (α : F ⟹ G) (j : J) : lim.map α ≫ limit.π G j = limit.π F j ≫ α j :=
by erw is_limit.fac

@[simp] lemma limit.lift_map {F G : J ⥤ C} (c : cone F) (α : F ⟹ G) :
  limit.lift F c ≫ lim.map α = limit.lift G (c.postcompose α) :=
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

def limit.pre (F : J ⥤ C) (E : K ⥤ J) : limit F ⟶ limit (E ⋙ F) :=
limit.lift (E ⋙ F)
{ X := limit F,
  π := λ k, limit.π F (E k),
  w' :=
  begin
    /- `obviously` says -/
    intros j j' f, dsimp at *,
    erw limits.cone.w,
    refl
  end }

@[simp] lemma limit.pre_π (F : J ⥤ C) (E : K ⥤ J) (k : K) :
  limit.pre F E ≫ limit.π (E ⋙ F) k = limit.π F (E k) :=
by erw is_limit.fac

@[simp] lemma limit.lift_pre {F : J ⥤ C} (c : cone F) (E : K ⥤ J) :
  limit.lift F c ≫ limit.pre F E = limit.lift (E ⋙ F) (c.whisker E) :=
by obviously

lemma limit.map_pre {F G : J ⥤ C} (α : F ⟹ G) (E : K ⥤ J) :
  lim.map α ≫ limit.pre G E = limit.pre F E ≫ lim.map (whisker_left E α) :=
begin
  /- `obviously` says -/
  ext1, dsimp at *, simp at *,
  erw [←category.assoc, is_limit.fac],
  refl,
end

@[simp] lemma limit.pre_pre {L : Type v} [small_category L] (F : J ⥤ C) (E : K ⥤ J) (D : L ⥤ K) :
  limit.pre F E ≫ limit.pre (E ⋙ F) D = limit.pre F (D ⋙ E) :=
begin
  /- `obviously` says -/
  ext1, dsimp at *, simp at *,
  erw limit.pre_π, -- isn't it sad this simp lemma isn't applied by simp?
  refl
end
end

section
variables {D : Type u} [𝒟 : category.{u v} D] [has_limits.{u v} D]
include 𝒟

def limit.post (F : J ⥤ C) (G : C ⥤ D) : G (limit F) ⟶ limit (F ⋙ G) :=
limit.lift (F ⋙ G)
{ X := _,
  π := λ j, G.map (limit.π F j),
  w' :=
  begin
    /- `obviously` says -/
    intros j j' f, dsimp at *,
    erw [←functor.map_comp, limits.cone.w],
    refl
  end }

@[simp] lemma limit.post_π (F : J ⥤ C) (G : C ⥤ D) (j : J) :
  limit.post F G ≫ limit.π (F ⋙ G) j = G.map (limit.π F j) :=
by erw is_limit.fac

@[simp] lemma limit.lift_post {F : J ⥤ C} (c : cone F) (G : C ⥤ D) :
  G.map (limit.lift F c) ≫ limit.post F G = limit.lift (F ⋙ G) (G.map_cone c) :=
begin
  /- `obviously` says -/
  ext1, dsimp at *, simp at *,
  erw ←functor.map_comp,
  simp,
  refl
end

lemma limit.map_post {F G : J ⥤ C} (α : F ⟹ G) (H : C ⥤ D) :
/- H (limit F) ⟶ H (limit G) ⟶ limit (G ⋙ H) vs
   H (limit F) ⟶ limit (F ⋙ H) ⟶ limit (G ⋙ H) -/
  H.map (lim.map α) ≫ limit.post G H = limit.post F H ≫ lim.map (whisker_right α H) :=
begin
  /- `obviously` says -/
  ext1, dsimp at *, simp at *,
  erw [←category.assoc, is_limit.fac, ←functor.map_comp],
  refl
end

lemma limit.pre_post {K : Type v} [small_category K] (F : J ⥤ C) (E : K ⥤ J) (G : C ⥤ D) :
/- G (limit F) ⟶ G (limit (E ⋙ F)) ⟶ limit ((E ⋙ F) ⋙ G) vs -/
/- G (limit F) ⟶ limit F ⋙ G ⟶ limit (E ⋙ (F ⋙ G)) or -/
  G.map (limit.pre F E) ≫ limit.post (E ⋙ F) G = limit.post F G ≫ limit.pre (F ⋙ G) E :=
begin
  /- `obviously` says -/
  ext1, dsimp at *, simp at *, dsimp at *,
  erw [←functor.map_comp, limit.pre_π F E j, limit.pre_π],
  simp,
end.

@[simp] lemma limit.post_post {E : Type u} [category.{u v} E] [has_limits.{u v} E] (F : J ⥤ C) (G : C ⥤ D) (H : D ⥤ E):
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

variable (C)

class has_colimits :=
(cocone : Π {J : Type v} [𝒥 : small_category J] (F : J ⥤ C), cocone F)
(is_colimit : Π {J : Type v} [𝒥 : small_category J] (F : J ⥤ C), is_colimit (cocone F) . obviously)

variable {C}

section
variables [has_colimits.{u v} C] {J : Type v} [𝒥 : small_category J]
include 𝒥

def colimit.cocone (F : J ⥤ C) : cocone F := has_colimits.cocone.{u v} F
def colimit (F : J ⥤ C) := (colimit.cocone F).X
def colimit.ι (F : J ⥤ C) (j : J) : F j ⟶ colimit F := (colimit.cocone F).ι j
@[simp] lemma colimit.w (F : J ⥤ C) {j j' : J} (f : j ⟶ j') : F.map f ≫ colimit.ι F j' = colimit.ι F j := (colimit.cocone F).w f
def colimit.universal_property (F : J ⥤ C) : is_colimit (colimit.cocone F) :=
has_colimits.is_colimit.{u v} C F

def colimit.desc (F : J ⥤ C) (c : cocone F) : colimit F ⟶ c.X := (colimit.universal_property F).desc c
@[simp] lemma colimit.universal_property_desc (F : J ⥤ C) (c : cocone F) : (colimit.universal_property F).desc c = colimit.desc F c := rfl

@[simp] lemma colimit.ι_desc (F : J ⥤ C) (c : cocone F) (j : J) : colimit.ι F j ≫ colimit.desc F c = c.ι j :=
is_colimit.fac _ c j

@[simp] lemma colimit.cone_ι (F : J ⥤ C) (j : J) : (colimit.cocone F).ι j = (@colimit.ι C _ _ J _ F j) := rfl

def colimit.cocone_morphism (F : J ⥤ C) (c : cocone F) : cocone_morphism (colimit.cocone F) c :=
{ hom := (colimit.desc F) c }

@[simp] lemma colimit.cocone_morphism_hom {F : J ⥤ C} (c : cocone F) : (colimit.cocone_morphism F c).hom = colimit.desc F c := rfl
@[simp] lemma colimit.ι_cocone_morphism {F : J ⥤ C} (c : cocone F) (j : J) : (colimit.ι F j) ≫ (colimit.cocone_morphism F c).hom = c.ι j :=
by erw is_colimit.fac

@[extensionality] lemma colimit.hom_ext {F : J ⥤ C} {X : C}
  (f g : colimit F ⟶ X)
  (w : ∀ j, colimit.ι F j ≫ f = colimit.ι F j ≫ g) : f = g :=
begin
  let c : cocone F :=
  { X := X,
    ι := λ j, colimit.ι F j ≫ f,
    w' :=
    begin
      /- obviously says: -/
      intros j j' f_1, dsimp at *,
      erw [← category.assoc, limits.cocone.w],
      simp,
    end },
  have p_f := (colimit.universal_property F).uniq c f (λ j, by simp),
  have p_g := (colimit.universal_property F).uniq c g (λ j, eq.symm (w j)),
  rw [p_f, p_g],
end

lemma colimit.desc_extend (F : J ⥤ C) (c : cocone F) {X : C} (f : c.X ⟶ X) :
  colimit.desc F (c.extend f) = colimit.desc F c ≫ f :=
begin
  /- obviously says: -/
  ext1, simp at *, erw ←category.assoc, simp, refl
end

/-- `colimit F` is functorial in `F`. -/
@[simp] def colim : (J ⥤ C) ⥤ C :=
{ obj := colimit,
  map' := λ F F' t, colimit.desc F $
    { X := colimit F',
      ι := λ j, t j ≫ colimit.ι F' j,
      w' :=
      begin
        /- `obviously` says -/
        intros j j' f, dsimp at *,
        erw [←category.assoc,
             nat_trans.naturality,
             category.assoc,
             limits.cocone.w],
        refl,
      end },
  map_comp' :=
  begin
    /- `obviously` says -/
    intros X Y Z f g, ext1, dsimp at *, simp at *,
    conv { to_rhs, rw ←category.assoc },
    simp
  end }.

@[simp] lemma colim_ι_map {F G : J ⥤ C} (α : F ⟹ G) (j : J) : colimit.ι F j ≫ colim.map α = α j ≫ colimit.ι G j :=
by erw is_colimit.fac

@[simp] lemma colimit.map_desc {F G : J ⥤ C} (c : cocone G) (α : F ⟹ G) :
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

def colimit.pre (F : J ⥤ C) (E : K ⥤ J) : colimit (E ⋙ F) ⟶ colimit F :=
colimit.desc (E ⋙ F)
{ X := colimit F,
  ι := λ k, colimit.ι F (E k),
  w' :=
  begin
    /- `obviously` says -/
    intros j j' f, dsimp at *,
    erw limits.cocone.w,
    refl
  end }

@[simp] lemma colimit.ι_pre (F : J ⥤ C) (E : K ⥤ J) (k : K) :
  colimit.ι (E ⋙ F) k ≫ colimit.pre F E = colimit.ι F (E k) :=
by erw is_colimit.fac

@[simp] lemma colimit.desc_pre {F : J ⥤ C} (c : cocone F) (E : K ⥤ J) :
  colimit.pre F E ≫ colimit.desc F c = colimit.desc (E ⋙ F) (c.whisker E) :=
begin
  /- `obviously` says -/
  ext1, dsimp at *, simp at *,
  rw ←category.assoc,
  simp,
  refl,
end

lemma colimit.map_pre {F G : J ⥤ C} (α : F ⟹ G) (E : K ⥤ J) :
  colimit.pre F E ≫ colim.map α = colim.map (whisker_left E α) ≫ colimit.pre G E :=
begin
  /- `obviously` says -/
  ext1, dsimp at *, simp at *,
  conv {to_rhs, rw ←category.assoc},
  simp,
  refl
end.

@[simp] lemma colimit.pre_pre {L : Type v} [small_category L] (F : J ⥤ C) (E : K ⥤ J) (D : L ⥤ K) :
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
variables {D : Type u} [𝒟 : category.{u v} D] [has_colimits.{u v} D]
include 𝒟

def colimit.post (F : J ⥤ C) (G : C ⥤ D) : colimit (F ⋙ G) ⟶ G (colimit F) :=
colimit.desc (F ⋙ G)
{ X := _,
  ι := λ j, G.map (colimit.ι F j),
  w' :=
  begin
    /- `obviously` says -/
    intros j j' f, dsimp at *,
    erw [←functor.map_comp, limits.cocone.w],
    refl
  end }

@[simp] lemma colimit.ι_post (F : J ⥤ C) (G : C ⥤ D) (j : J) :
  colimit.ι (F ⋙ G) j ≫ colimit.post F G = G.map (colimit.ι F j) :=
by erw is_colimit.fac

@[simp] lemma colimit.desc_post {F : J ⥤ C} (c : cocone F) (G : C ⥤ D) :
  colimit.post F G ≫ G.map (colimit.desc F c) = colimit.desc (F ⋙ G) (G.map_cocone c) :=
begin
  /- `obviously` says -/
  ext1, dsimp at *, simp at *,
  rw ←category.assoc,
  simp,
  rw ←functor.map_comp,
  simp,
  refl,
end

lemma colimit.post_map {F G : J ⥤ C} (α : F ⟹ G) (H : C ⥤ D) :
  colimit.post F H ≫ H.map (colim.map α) = colim.map (whisker_right α H) ≫ colimit.post G H :=
begin
  /- `obviously` says -/
  ext1, dsimp at *, simp at *,
  erw [←category.assoc, is_colimit.fac, category.assoc, is_colimit.fac, ←functor.map_comp],
  refl
end

lemma colimit.pre_post {K : Type v} [small_category K] (F : J ⥤ C) (E : K ⥤ J) (G : C ⥤ D) :
  colimit.pre (F ⋙ G) E ≫ colimit.post F G = colimit.post (E ⋙ F) G ≫ G.map (colimit.pre F E) :=
begin
  /- `obviously` says -/
  ext1, dsimp at *,
  rw ←category.assoc,
  simp,
  rw ←category.assoc,
  erw colimit.ι_post (E ⋙ F) G,
  rw ←functor.map_comp,
  rw colimit.ι_pre,
end.

@[simp] lemma colimit.post_post {E : Type u} [category.{u v} E] [has_colimits.{u v} E] (F : J ⥤ C) (G : C ⥤ D) (H : D ⥤ E):
  colimit.post (F ⋙ G) H ≫ H.map (colimit.post F G) = colimit.post F (G ⋙ H) :=
begin
  /- `obviously` says -/
  ext1, dsimp at *,
  rw ←category.assoc,
  simp,
  rw ←functor.map_comp,
  erw colimit.ι_post,
  erw colimit.ι_post F (G ⋙ H),
  simp,
end
end

end

end category_theory.limits