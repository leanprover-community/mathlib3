-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Reid Barton, Mario Carneiro

import category_theory.whiskering
import category_theory.yoneda
import category_theory.limits.cones

open category_theory category_theory.category category_theory.functor

namespace category_theory.limits

universes u u' u'' v w

variables {J : Type v} [small_category J]
variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

section is_limit
variables {F : J ⥤ C}

/-- A cone `t` on `F` is a limit cone if each cone on `F` admits a unique
  cone morphism to `t`. -/
structure is_limit (t : cone F) :=
(lift  : Π (s : cone F), s.X ⟶ t.X)
(fac'  : ∀ (s : cone F) (j : J), lift s ≫ t.π.app j = s.π.app j . obviously)
(uniq' : ∀ (s : cone F) (m : s.X ⟶ t.X) (w : ∀ j : J, m ≫ t.π.app j = s.π.app j),
  m = lift s . obviously)

restate_axiom is_limit.fac'
attribute [simp] is_limit.fac
restate_axiom is_limit.uniq'

instance is_limit_subsingleton {t : cone F} : subsingleton (is_limit t) :=
⟨by intros P Q; cases P; cases Q; congr; ext; solve_by_elim⟩

/- Repackaging the definition in terms of cone morphisms. -/

def is_limit.lift_cone_morphism {t : cone F} (h : is_limit t) (s : cone F) : s ⟶ t :=
{ hom := h.lift s }

lemma is_limit.uniq_cone_morphism {s t : cone F} (h : is_limit t) {f f' : s ⟶ t} :
  f = f' :=
have ∀ {g : s ⟶ t}, g = h.lift_cone_morphism s, by intro g; ext; exact h.uniq _ _ g.w,
this.trans this.symm

def is_limit.mk_cone_morphism {t : cone F}
  (lift : Π (s : cone F), s ⟶ t)
  (uniq' : ∀ (s : cone F) (m : s ⟶ t), m = lift s) : is_limit t :=
{ lift := λ s, (lift s).hom,
  uniq' := λ s m w,
    have cone_morphism.mk m w = lift s, by apply uniq',
    congr_arg cone_morphism.hom this }

/-- Limit cones on `F` are unique up to isomorphism. -/
def is_limit.unique {s t : cone F} (P : is_limit s) (Q : is_limit t) : s ≅ t :=
{ hom := Q.lift_cone_morphism s,
  inv := P.lift_cone_morphism t,
  hom_inv_id' := P.uniq_cone_morphism,
  inv_hom_id' := Q.uniq_cone_morphism }

def is_limit.of_iso_limit {r t : cone F} (P : is_limit r) (i : r ≅ t) : is_limit t :=
is_limit.mk_cone_morphism
  (λ s, P.lift_cone_morphism s ≫ i.hom)
  (λ s m, by rw ←i.comp_inv_eq; apply P.uniq_cone_morphism)

variables {t : cone F}

lemma is_limit.hom_lift (h : is_limit t) {W : C} (m : W ⟶ t.X) :
  m = h.lift { X := W, π := { app := λ b, m ≫ t.π.app b } } :=
h.uniq { X := W, π := { app := λ b, m ≫ t.π.app b } } m (λ b, rfl)

/-- Two morphisms into a limit are equal if their compositions with
  each cone morphism are equal. -/
lemma is_limit.hom_ext (h : is_limit t) {W : C} {f f' : W ⟶ t.X}
  (w : ∀ j, f ≫ t.π.app j = f' ≫ t.π.app j) : f = f' :=
by rw [h.hom_lift f, h.hom_lift f']; congr; exact funext w

/-- The universal property of a limit cone: a map `W ⟶ X` is the same as
  a cone on `F` with vertex `W`. -/
def is_limit.hom_iso (h : is_limit t) (W : C) : (W ⟶ t.X) ≅ ((const J).obj W ⟹ F) :=
{ hom := λ f, (t.extend f).π,
  inv := λ π, h.lift { X := W, π := π },
  hom_inv_id' := by ext f; apply h.hom_ext; intro j; simp; dsimp; refl }

@[simp] lemma is_limit.hom_iso_hom (h : is_limit t) {W : C} (f : W ⟶ t.X) :
  (is_limit.hom_iso h W).hom f = (t.extend f).π := rfl

/-- The limit of `F` represents the functor taking `W` to
  the set of cones on `F` with vertex `W`. -/
def is_limit.nat_iso (h : is_limit t) : yoneda.obj t.X ≅ F.cones :=
nat_iso.of_components (is_limit.hom_iso h) (by tidy)

def is_limit.hom_iso' (h : is_limit t) (W : C) :
  (W ⟶ t.X) ≅ { p : Π j, W ⟶ F.obj j // ∀ {j j'} (f : j ⟶ j'), p j ≫ F.map f = p j' } :=
h.hom_iso W ≪≫
{ hom := λ π,
  ⟨λ j, π.app j, λ j j' f,
   by convert ←(π.naturality f).symm; apply id_comp⟩,
  inv := λ p,
  { app := λ j, p.1 j,
    naturality' := λ j j' f, begin dsimp, erw [id_comp], exact (p.2 f).symm end } }

end is_limit


section is_colimit
variables {F : J ⥤ C}

/-- A cocone `t` on `F` is a colimit cocone if each cocone on `F` admits a unique
  cocone morphism from `t`. -/
structure is_colimit (t : cocone F) :=
(desc  : Π (s : cocone F), t.X ⟶ s.X)
(fac'  : ∀ (s : cocone F) (j : J), t.ι.app j ≫ desc s = s.ι.app j . obviously)
(uniq' : ∀ (s : cocone F) (m : t.X ⟶ s.X) (w : ∀ j : J, t.ι.app j ≫ m = s.ι.app j),
  m = desc s . obviously)

restate_axiom is_colimit.fac'
attribute [simp] is_colimit.fac
restate_axiom is_colimit.uniq'

instance is_colimit_subsingleton {t : cocone F} : subsingleton (is_colimit t) :=
⟨by intros P Q; cases P; cases Q; congr; ext; solve_by_elim⟩

/- Repackaging the definition in terms of cone morphisms. -/

def is_colimit.desc_cocone_morphism {t : cocone F} (h : is_colimit t) (s : cocone F) : t ⟶ s :=
{ hom := h.desc s }

lemma is_colimit.uniq_cocone_morphism {s t : cocone F} (h : is_colimit t) {f f' : t ⟶ s} :
  f = f' :=
have ∀ {g : t ⟶ s}, g = h.desc_cocone_morphism s, by intro g; ext; exact h.uniq _ _ g.w,
this.trans this.symm

def is_colimit.mk_cocone_morphism {t : cocone F}
  (desc : Π (s : cocone F), t ⟶ s)
  (uniq' : ∀ (s : cocone F) (m : t ⟶ s), m = desc s) : is_colimit t :=
{ desc := λ s, (desc s).hom,
  uniq' := λ s m w,
    have cocone_morphism.mk m w = desc s, by apply uniq',
    congr_arg cocone_morphism.hom this }

/-- Limit cones on `F` are unique up to isomorphism. -/
def is_colimit.unique {s t : cocone F} (P : is_colimit s) (Q : is_colimit t) : s ≅ t :=
{ hom := P.desc_cocone_morphism t,
  inv := Q.desc_cocone_morphism s,
  hom_inv_id' := P.uniq_cocone_morphism,
  inv_hom_id' := Q.uniq_cocone_morphism }

def is_colimit.of_iso_colimit {r t : cocone F} (P : is_colimit r) (i : r ≅ t) : is_colimit t :=
is_colimit.mk_cocone_morphism
  (λ s, i.inv ≫ P.desc_cocone_morphism s)
  (λ s m, by rw i.eq_inv_comp; apply P.uniq_cocone_morphism)

variables {t : cocone F}

lemma is_colimit.hom_desc (h : is_colimit t) {W : C} (m : t.X ⟶ W) :
  m = h.desc { X := W, ι := { app := λ b, t.ι.app b ≫ m,
    naturality' := by intros; erw [←assoc, t.ι.naturality, comp_id, comp_id] } } :=
h.uniq { X := W, ι := { app := λ b, t.ι.app b ≫ m, naturality' := _ } } m (λ b, rfl)

/-- Two morphisms out of a colimit are equal if their compositions with
  each cocone morphism are equal. -/
lemma is_colimit.hom_ext (h : is_colimit t) {W : C} {f f' : t.X ⟶ W}
  (w : ∀ j, t.ι.app j ≫ f = t.ι.app j ≫ f') : f = f' :=
by rw [h.hom_desc f, h.hom_desc f']; congr; exact funext w

/-- The universal property of a colimit cocone: a map `X ⟶ W` is the same as
  a cocone on `F` with vertex `W`. -/
def is_colimit.hom_iso (h : is_colimit t) (W : C) : (t.X ⟶ W) ≅ (F ⟹ (const J).obj W) :=
{ hom := λ f, (t.extend f).ι,
  inv := λ ι, h.desc { X := W, ι := ι },
  hom_inv_id' := by ext f; apply h.hom_ext; intro j; simp; dsimp; refl }

@[simp] lemma is_colimit.hom_iso_hom (h : is_colimit t) {W : C} (f : t.X ⟶ W) :
  (is_colimit.hom_iso h W).hom f = (t.extend f).ι := rfl

/-- The colimit of `F` represents the functor taking `W` to
  the set of cocones on `F` with vertex `W`. -/
def is_colimit.nat_iso (h : is_colimit t) : coyoneda.obj t.X ≅ F.cocones :=
nat_iso.of_components (is_colimit.hom_iso h) (by intros; ext; dsimp; rw ←assoc; refl)

def is_colimit.hom_iso' (h : is_colimit t) (W : C) :
  (t.X ⟶ W) ≅ { p : Π j, F.obj j ⟶ W // ∀ {j j' : J} (f : j ⟶ j'), F.map f ≫ p j' = p j } :=
h.hom_iso W ≪≫
{ hom := λ ι,
  ⟨λ j, ι.app j, λ j j' f,
   by convert ←(ι.naturality f); apply comp_id⟩,
  inv := λ p,
  { app := λ j, p.1 j,
    naturality' := λ j j' f, begin dsimp, erw [comp_id], exact (p.2 f) end } }

end is_colimit


section limit

/-- `has_limit F` represents a particular chosen limit of the diagram `F`. -/
class has_limit (F : J ⥤ C) :=
(cone : cone F)
(is_limit : is_limit cone)

variables (J C)

/-- `C` has limits of shape `J` if we have chosen a particular limit of
  every functor `F : J ⥤ C`. -/
@[class] def has_limits_of_shape := Π F : J ⥤ C, has_limit F

/-- `C` has all (small) limits if it has limits of every shape. -/
@[class] def has_limits :=
Π {J : Type v} {𝒥 : small_category J}, by exactI has_limits_of_shape J C

variables {J C}

instance has_limit_of_has_limits_of_shape
  {J : Type v} [small_category J] [H : has_limits_of_shape J C] (F : J ⥤ C) : has_limit F :=
H F

instance has_limits_of_shape_of_has_limits
  {J : Type v} [small_category J] [H : has_limits.{u v} C] : has_limits_of_shape J C :=
H

/- Interface to the `has_limit` class. -/

def limit.cone (F : J ⥤ C) [has_limit F] : cone F := has_limit.cone F

def limit (F : J ⥤ C) [has_limit F] := (limit.cone F).X

def limit.π (F : J ⥤ C) [has_limit F] (j : J) : limit F ⟶ F.obj j :=
(limit.cone F).π.app j

@[simp] lemma limit.cone_π {F : J ⥤ C} [has_limit F] (j : J) :
  (limit.cone F).π.app j = limit.π _ j := rfl

@[simp] lemma limit.w (F : J ⥤ C) [has_limit F] {j j' : J} (f : j ⟶ j') :
  limit.π F j ≫ F.map f = limit.π F j' := (limit.cone F).w f

def limit.is_limit (F : J ⥤ C) [has_limit F] : is_limit (limit.cone F) :=
has_limit.is_limit.{u v} F

def limit.lift (F : J ⥤ C) [has_limit F] (c : cone F) : c.X ⟶ limit F :=
(limit.is_limit F).lift c

@[simp] lemma limit.is_limit_lift {F : J ⥤ C} [has_limit F] (c : cone F) :
  (limit.is_limit F).lift c = limit.lift F c := rfl

@[simp] lemma limit.lift_π {F : J ⥤ C} [has_limit F] (c : cone F) (j : J) :
  limit.lift F c ≫ limit.π F j = c.π.app j :=
is_limit.fac _ c j

def limit.cone_morphism {F : J ⥤ C} [has_limit F] (c : cone F) :
  cone_morphism c (limit.cone F) :=
(limit.is_limit F).lift_cone_morphism c

@[simp] lemma limit.cone_morphism_hom {F : J ⥤ C} [has_limit F] (c : cone F) :
  (limit.cone_morphism c).hom = limit.lift F c := rfl
@[simp] lemma limit.cone_morphism_π {F : J ⥤ C} [has_limit F] (c : cone F) (j : J) :
  (limit.cone_morphism c).hom ≫ limit.π F j = c.π.app j :=
by erw is_limit.fac

@[extensionality] lemma limit.hom_ext {F : J ⥤ C} [has_limit F] {X : C} {f f' : X ⟶ limit F}
  (w : ∀ j, f ≫ limit.π F j = f' ≫ limit.π F j) : f = f' :=
(limit.is_limit F).hom_ext w

def limit.hom_iso (F : J ⥤ C) [has_limit F] (W : C) : (W ⟶ limit F) ≅ (F.cones.obj W) :=
(limit.is_limit F).hom_iso W

@[simp] lemma limit.hom_iso_hom (F : J ⥤ C) [has_limit F] {W : C} (f : W ⟶ limit F):
  (limit.hom_iso F W).hom f = (const J).map f ≫ (limit.cone F).π :=
(limit.is_limit F).hom_iso_hom f

def limit.hom_iso' (F : J ⥤ C) [has_limit F] (W : C) :
  (W ⟶ limit F) ≅ { p : Π j, W ⟶ F.obj j // ∀ {j j' : J} (f : j ⟶ j'), p j ≫ F.map f = p j' } :=
(limit.is_limit F).hom_iso' W

section pre
variables {K : Type v} [small_category K]
variables (F : J ⥤ C) [has_limit F] (E : K ⥤ J) [has_limit (E ⋙ F)]

def limit.pre : limit F ⟶ limit (E ⋙ F) :=
limit.lift (E ⋙ F)
  { X := limit F,
    π := { app := λ k, limit.π F (E.obj k) } }

@[simp] lemma limit.pre_π (k : K) : limit.pre F E ≫ limit.π (E ⋙ F) k = limit.π F (E.obj k) :=
by erw is_limit.fac

@[simp] lemma limit.lift_pre (c : cone F) :
  limit.lift F c ≫ limit.pre F E = limit.lift (E ⋙ F) (c.whisker E) :=
by ext; simp

variables {L : Type v} [small_category L]
variables (D : L ⥤ K) [has_limit (D ⋙ E ⋙ F)]

@[simp] lemma limit.pre_pre : limit.pre F E ≫ limit.pre (E ⋙ F) D = limit.pre F (D ⋙ E) :=
by ext j; erw [assoc, limit.pre_π, limit.pre_π, limit.pre_π]; refl

end pre

section post
variables {D : Type u'} [𝒟 : category.{u' v} D]
include 𝒟

variables (F : J ⥤ C) [has_limit F] (G : C ⥤ D) [has_limit (F ⋙ G)]

def limit.post : G.obj (limit F) ⟶ limit (F ⋙ G) :=
limit.lift (F ⋙ G)
{ X := G.obj (limit F),
  π :=
  { app := λ j, G.map (limit.π F j),
    naturality' :=
      by intros j j' f; erw [←G.map_comp, limits.cone.w, id_comp]; refl } }

@[simp] lemma limit.post_π (j : J) : limit.post F G ≫ limit.π (F ⋙ G) j = G.map (limit.π F j) :=
by erw is_limit.fac

@[simp] lemma limit.lift_post (c : cone F) :
  G.map (limit.lift F c) ≫ limit.post F G = limit.lift (F ⋙ G) (G.map_cone c) :=
by ext; rw [assoc, limit.post_π, ←G.map_comp, limit.lift_π, limit.lift_π]; refl

@[simp] lemma limit.post_post
  {E : Type u''} [category.{u'' v} E] (H : D ⥤ E) [has_limit ((F ⋙ G) ⋙ H)] :
/- H G (limit F) ⟶ H (limit (F ⋙ G)) ⟶ limit ((F ⋙ G) ⋙ H) equals -/
/- H G (limit F) ⟶ limit (F ⋙ (G ⋙ H)) -/
  H.map (limit.post F G) ≫ limit.post (F ⋙ G) H = limit.post F (G ⋙ H) :=
by ext; erw [assoc, limit.post_π, ←H.map_comp, limit.post_π, limit.post_π]; refl

end post

lemma limit.pre_post {K : Type v} [small_category K] {D : Type u'} [category.{u' v} D]
  (E : K ⥤ J) (F : J ⥤ C) (G : C ⥤ D)
  [has_limit F] [has_limit (E ⋙ F)] [has_limit (F ⋙ G)] [has_limit ((E ⋙ F) ⋙ G)] :
/- G (limit F) ⟶ G (limit (E ⋙ F)) ⟶ limit ((E ⋙ F) ⋙ G) vs -/
/- G (limit F) ⟶ limit F ⋙ G ⟶ limit (E ⋙ (F ⋙ G)) or -/
  G.map (limit.pre F E) ≫ limit.post (E ⋙ F) G = limit.post F G ≫ limit.pre (F ⋙ G) E :=
by ext; erw [assoc, limit.post_π, ←G.map_comp, limit.pre_π, assoc, limit.pre_π, limit.post_π]; refl

section lim_functor

variables [has_limits_of_shape J C]

/-- `limit F` is functorial in `F`, when `C` has all limits of shape `J`. -/
def lim : (J ⥤ C) ⥤ C :=
{ obj := λ F, limit F,
  map := λ F G α, limit.lift G
    { X := limit F,
      π :=
      { app := λ j, limit.π F j ≫ α.app j,
        naturality' := λ j j' f,
          by erw [id_comp, assoc, ←α.naturality, ←assoc, limit.w] } },
  map_comp' := λ F G H α β,
    by ext; erw [assoc, is_limit.fac, is_limit.fac, ←assoc, is_limit.fac, assoc]; refl }

variables {F G : J ⥤ C} (α : F ⟹ G)

@[simp] lemma lim.map_π (j : J) : lim.map α ≫ limit.π G j = limit.π F j ≫ α.app j :=
by apply is_limit.fac

@[simp] lemma limit.lift_map (c : cone F) :
  limit.lift F c ≫ lim.map α = limit.lift G (c.postcompose α) :=
by ext; rw [assoc, lim.map_π, ←assoc, limit.lift_π, limit.lift_π]; refl

lemma limit.map_pre {K : Type v} [small_category K] [has_limits_of_shape K C] (E : K ⥤ J) :
  lim.map α ≫ limit.pre G E = limit.pre F E ≫ lim.map (whisker_left E α) :=
by ext; rw [assoc, limit.pre_π, lim.map_π, assoc, lim.map_π, ←assoc, limit.pre_π]; refl

lemma limit.map_post {D : Type u'} [category.{u' v} D] [has_limits_of_shape J D] (H : C ⥤ D) :
/- H (limit F) ⟶ H (limit G) ⟶ limit (G ⋙ H) vs
   H (limit F) ⟶ limit (F ⋙ H) ⟶ limit (G ⋙ H) -/
  H.map (lim.map α) ≫ limit.post G H = limit.post F H ≫ lim.map (whisker_right α H) :=
begin
  ext,
  rw [assoc, limit.post_π, ←H.map_comp, lim.map_π, H.map_comp],
  rw [assoc, lim.map_π, ←assoc, limit.post_π],
  refl
end

end lim_functor

end limit


section colimit

/-- `has_colimit F` represents a particular chosen colimit of the diagram `F`. -/
class has_colimit (F : J ⥤ C) :=
(cocone : cocone F)
(is_colimit : is_colimit cocone)

variables (J C)

/-- `C` has colimits of shape `J` if we have chosen a particular colimit of
  every functor `F : J ⥤ C`. -/
@[class] def has_colimits_of_shape := Π F : J ⥤ C, has_colimit F

/-- `C` has all (small) colimits if it has limits of every shape. -/
@[class] def has_colimits :=
Π {J : Type v} {𝒥 : small_category J}, by exactI has_colimits_of_shape J C

variables {J C}

instance has_colimit_of_has_colimits_of_shape
  {J : Type v} [small_category J] [H : has_colimits_of_shape J C] (F : J ⥤ C) : has_colimit F :=
H F

instance has_colimits_of_shape_of_has_colimits
  {J : Type v} [small_category J] [H : has_colimits.{u v} C] : has_colimits_of_shape J C :=
H

/- Interface to the `has_colimit` class. -/

def colimit.cocone (F : J ⥤ C) [has_colimit F] : cocone F := has_colimit.cocone F

def colimit (F : J ⥤ C) [has_colimit F] := (colimit.cocone F).X

def colimit.ι (F : J ⥤ C) [has_colimit F] (j : J) : F.obj j ⟶ colimit F :=
(colimit.cocone F).ι.app j

@[simp] lemma colimit.cocone_ι {F : J ⥤ C} [has_colimit F] (j : J) :
  (colimit.cocone F).ι.app j = colimit.ι _ j := rfl

@[simp] lemma colimit.w (F : J ⥤ C) [has_colimit F] {j j' : J} (f : j ⟶ j') :
  F.map f ≫ colimit.ι F j' = colimit.ι F j := (colimit.cocone F).w f

def colimit.is_colimit (F : J ⥤ C) [has_colimit F] : is_colimit (colimit.cocone F) :=
has_colimit.is_colimit.{u v} F

def colimit.desc (F : J ⥤ C) [has_colimit F] (c : cocone F) : colimit F ⟶ c.X :=
(colimit.is_colimit F).desc c

@[simp] lemma colimit.is_colimit_desc {F : J ⥤ C} [has_colimit F] (c : cocone F) :
  (colimit.is_colimit F).desc c = colimit.desc F c := rfl

@[simp] lemma colimit.ι_desc {F : J ⥤ C} [has_colimit F] (c : cocone F) (j : J) :
  colimit.ι F j ≫ colimit.desc F c = c.ι.app j :=
is_colimit.fac _ c j

def colimit.cocone_morphism {F : J ⥤ C} [has_colimit F] (c : cocone F) :
  cocone_morphism (colimit.cocone F) c :=
(colimit.is_colimit F).desc_cocone_morphism c

@[simp] lemma colimit.cocone_morphism_hom {F : J ⥤ C} [has_colimit F] (c : cocone F) :
  (colimit.cocone_morphism c).hom = colimit.desc F c := rfl
@[simp] lemma colimit.ι_cocone_morphism {F : J ⥤ C} [has_colimit F] (c : cocone F) (j : J) :
  colimit.ι F j ≫ (colimit.cocone_morphism c).hom = c.ι.app j :=
by erw is_colimit.fac

@[extensionality] lemma colimit.hom_ext {F : J ⥤ C} [has_colimit F] {X : C} {f f' : colimit F ⟶ X}
  (w : ∀ j, colimit.ι F j ≫ f = colimit.ι F j ≫ f') : f = f' :=
(colimit.is_colimit F).hom_ext w

def colimit.hom_iso (F : J ⥤ C) [has_colimit F] (W : C) : (colimit F ⟶ W) ≅ (F.cocones.obj W) :=
(colimit.is_colimit F).hom_iso W

@[simp] lemma colimit.hom_iso_hom (F : J ⥤ C) [has_colimit F] {W : C} (f : colimit F ⟶ W):
  (colimit.hom_iso F W).hom f = (colimit.cocone F).ι ≫ (const J).map f :=
(colimit.is_colimit F).hom_iso_hom f

def colimit.hom_iso' (F : J ⥤ C) [has_colimit F] (W : C) :
  (colimit F ⟶ W) ≅ { p : Π j, F.obj j ⟶ W // ∀ {j j'} (f : j ⟶ j'), F.map f ≫ p j' = p j } :=
(colimit.is_colimit F).hom_iso' W

section pre
variables {K : Type v} [small_category K]
variables (F : J ⥤ C) [has_colimit F] (E : K ⥤ J) [has_colimit (E ⋙ F)]

def colimit.pre : colimit (E ⋙ F) ⟶ colimit F :=
colimit.desc (E ⋙ F)
  { X := colimit F,
    ι := { app := λ k, colimit.ι F (E.obj k) } }

@[simp] lemma colimit.ι_pre (k : K) : colimit.ι (E ⋙ F) k ≫ colimit.pre F E = colimit.ι F (E.obj k) :=
by erw is_colimit.fac

@[simp] lemma colimit.pre_desc (c : cocone F) :
  colimit.pre F E ≫ colimit.desc F c = colimit.desc (E ⋙ F) (c.whisker E) :=
by ext; rw [←assoc, colimit.ι_pre]; simp

variables {L : Type v} [small_category L]
variables (D : L ⥤ K) [has_colimit (D ⋙ E ⋙ F)]

@[simp] lemma colimit.pre_pre : colimit.pre (E ⋙ F) D ≫ colimit.pre F E = colimit.pre F (D ⋙ E) :=
begin
  ext j,
  erw [←assoc, colimit.ι_pre, colimit.ι_pre],
  -- Why doesn't another erw [colimit.ι_pre] work here, like it did in limit.pre_pre?
  letI : has_colimit ((D ⋙ E) ⋙ F) := show has_colimit (D ⋙ E ⋙ F), by apply_instance,
  exact (colimit.ι_pre F (D ⋙ E) j).symm
end

end pre

section post
variables {D : Type u'} [𝒟 : category.{u' v} D]
include 𝒟

variables (F : J ⥤ C) [has_colimit F] (G : C ⥤ D) [has_colimit (F ⋙ G)]

def colimit.post : colimit (F ⋙ G) ⟶ G.obj (colimit F) :=
colimit.desc (F ⋙ G)
{ X := G.obj (colimit F),
  ι :=
  { app := λ j, G.map (colimit.ι F j),
    naturality' :=
      by intros j j' f; erw [←G.map_comp, limits.cocone.w, comp_id]; refl } }

@[simp] lemma colimit.ι_post (j : J) : colimit.ι (F ⋙ G) j ≫ colimit.post F G  = G.map (colimit.ι F j) :=
by erw is_colimit.fac

@[simp] lemma colimit.post_desc (c : cocone F) :
  colimit.post F G ≫ G.map (colimit.desc F c) = colimit.desc (F ⋙ G) (G.map_cocone c) :=
by ext; rw [←assoc, colimit.ι_post, ←G.map_comp, colimit.ι_desc, colimit.ι_desc]; refl

@[simp] lemma colimit.post_post
  {E : Type u''} [category.{u'' v} E] (H : D ⥤ E) [has_colimit ((F ⋙ G) ⋙ H)] :
/- H G (colimit F) ⟶ H (colimit (F ⋙ G)) ⟶ colimit ((F ⋙ G) ⋙ H) equals -/
/- H G (colimit F) ⟶ colimit (F ⋙ (G ⋙ H)) -/
  colimit.post (F ⋙ G) H ≫ H.map (colimit.post F G) = colimit.post F (G ⋙ H) :=
begin
  ext,
  erw [←assoc, colimit.ι_post, ←H.map_comp, colimit.ι_post],
  exact (colimit.ι_post F (G ⋙ H) j).symm
end

end post

lemma colimit.pre_post {K : Type v} [small_category K] {D : Type u'} [category.{u' v} D]
  (E : K ⥤ J) (F : J ⥤ C) (G : C ⥤ D)
  [has_colimit F] [has_colimit (E ⋙ F)] [has_colimit (F ⋙ G)] [has_colimit ((E ⋙ F) ⋙ G)] :
/- G (colimit F) ⟶ G (colimit (E ⋙ F)) ⟶ colimit ((E ⋙ F) ⋙ G) vs -/
/- G (colimit F) ⟶ colimit F ⋙ G ⟶ colimit (E ⋙ (F ⋙ G)) or -/
  colimit.post (E ⋙ F) G ≫ G.map (colimit.pre F E) = colimit.pre (F ⋙ G) E ≫ colimit.post F G :=
begin
  ext,
  erw [←assoc, colimit.ι_post, ←G.map_comp, colimit.ι_pre, ←assoc],
  letI : has_colimit (E ⋙ F ⋙ G) := show has_colimit ((E ⋙ F) ⋙ G), by apply_instance,
  erw [colimit.ι_pre (F ⋙ G) E j, colimit.ι_post]
end

section colim_functor

variables [has_colimits_of_shape J C]

/-- `colimit F` is functorial in `F`, when `C` has all colimits of shape `J`. -/
def colim : (J ⥤ C) ⥤ C :=
{ obj := λ F, colimit F,
  map := λ F G α, colimit.desc F
    { X := colimit G,
      ι :=
      { app := λ j, α.app j ≫ colimit.ι G j,
        naturality' := λ j j' f,
          by erw [comp_id, ←assoc, α.naturality, assoc, colimit.w] } },
  map_comp' := λ F G H α β,
    by ext; erw [←assoc, is_colimit.fac, is_colimit.fac, assoc, is_colimit.fac, ←assoc]; refl }

variables {F G : J ⥤ C} (α : F ⟹ G)

@[simp] lemma colim.ι_map (j : J) : colimit.ι F j ≫ colim.map α = α.app j ≫ colimit.ι G j :=
by apply is_colimit.fac

@[simp] lemma colimit.map_desc (c : cocone G) :
  colim.map α ≫ colimit.desc G c = colimit.desc F (c.precompose α) :=
by ext; rw [←assoc, colim.ι_map, assoc, colimit.ι_desc, colimit.ι_desc]; refl

lemma colimit.pre_map {K : Type v} [small_category K] [has_colimits_of_shape K C] (E : K ⥤ J) :
  colimit.pre F E ≫ colim.map α = colim.map (whisker_left E α) ≫ colimit.pre G E :=
by ext; rw [←assoc, colimit.ι_pre, colim.ι_map, ←assoc, colim.ι_map, assoc, colimit.ι_pre]; refl

lemma colimit.map_post {D : Type u'} [category.{u' v} D] [has_colimits_of_shape J D] (H : C ⥤ D) :
/- H (colimit F) ⟶ H (colimit G) ⟶ colimit (G ⋙ H) vs
   H (colimit F) ⟶ colimit (F ⋙ H) ⟶ colimit (G ⋙ H) -/
  colimit.post F H ≫ H.map (colim.map α) = colim.map (whisker_right α H) ≫ colimit.post G H:=
begin
  ext,
  rw [←assoc, colimit.ι_post, ←H.map_comp, colim.ι_map, H.map_comp],
  rw [←assoc, colim.ι_map, assoc, colimit.ι_post],
  refl
end

end colim_functor

end colimit

end category_theory.limits
