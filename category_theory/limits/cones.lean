-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import category_theory.types
import category_theory.isomorphism
import category_theory.natural_isomorphism
import category_theory.whiskering

namespace conv
open tactic

private meta def congr_aux : list congr_arg_kind → list expr → tactic (list expr × list expr)
| []      []      := return ([], [])
| (k::ks) (a::as) := do
  (gs, largs) ← congr_aux ks as,
  match k with
  | congr_arg_kind.fixed            := return $ (gs, a::largs)
  | congr_arg_kind.fixed_no_param   := return $ (gs, largs)
  | congr_arg_kind.eq               := do
      a_type  ← infer_type a,
      rhs     ← mk_meta_var a_type,
      g_type  ← mk_app `eq [a, rhs],
      g       ← mk_meta_var g_type,
      return (g::gs, a::rhs::g::largs)
  | congr_arg_kind.cast             := return $ (gs, a::largs)
  | congr_arg_kind.heq              := fail "congr tactic failed, unsupported congruence lemma (heq)"
  end
| ks      as := fail "congr tactic failed, unsupported congruence lemma"
  
meta def congr' : conv unit :=
do (r, lhs, rhs) ← target_lhs_rhs,
   guard (r = `eq),
   let fn   := lhs.get_app_fn,
   let args := lhs.get_app_args,
   (s, u) ← mk_simp_set ff [] [],
   fn ← (s.dsimplify [] fn) <|> pure (fn),
   trace fn,
   cgr_lemma ← mk_congr_lemma_simp fn (some args.length),
   trace "!",
   trace cgr_lemma.arg_kinds.length,
   trace args,
   g::gs ← get_goals,
   (new_gs, lemma_args) ← congr_aux cgr_lemma.arg_kinds args,
   let g_val := cgr_lemma.proof.mk_app lemma_args,
   unify g g_val,
   set_goals $ new_gs ++ gs,
   return ()

namespace interactive

meta def congr' : conv unit :=
conv.congr'

end interactive

end conv

universes u v
def isos (C : Type u) := C

open category_theory

instance category_isos {C : Type u} [category.{u v} C] : category (isos C) :=
{ hom := λ X Y, @iso C _ X Y,
  id := iso.refl,
  comp := λ X Y Z, iso.trans }

instance category_isos_type : large_category (isos (Type u)) :=
by apply_instance

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞
variables (J : Type v) [small_category J]

namespace category_theory.functor

def const : C ⥤ (J ⥤ C) :=
{ obj := λ X,
  { obj := λ j, X,
    map' := λ j j' f, 𝟙 X },
  map' := λ X Y f, { app := λ j, f } }

instance const_coe : has_coe C (J ⥤ C) := ⟨ @const C _ J _ ⟩

@[simp] lemma const_obj (X : C) (j : J) : (X : J ⥤ C) j = X := rfl
@[simp] lemma const_map (X : C) {j j' : J} (f : j ⟶ j') : (X : J ⥤ C).map f = 𝟙 X := rfl

section
variables {J}
variables {D : Type u} [𝒟 : category.{u v} D]
include 𝒟

@[simp] def const_compose (X : C) (F : C ⥤ D) : (F X : J ⥤ D) ≅ (X : J ⥤ C) ⋙ F :=
{ hom := { app := λ _, 𝟙 _ },
  inv := { app := λ _, 𝟙 _ } }

end

end category_theory.functor

open category_theory

namespace category_theory.nat_trans

instance const_coe {X Y : C} : has_coe (X ⟶ Y) ((X : J ⥤ C) ⟹ (Y : J ⥤ C)) := ⟨ (functor.const J).map ⟩

end category_theory.nat_trans

variables {J}

open category_theory

namespace category_theory.limits

/-- A `c : cone F` is an object `c.X` and a natural transformation `c.π : c.X ⟹ F` from the constant `c.X` functor to `F`. -/
structure cone (F : J ⥤ C) :=
(X : C)
(π : (X : J ⥤ C) ⟹ F)

namespace cone

@[extensionality] lemma evil_ext {F : J ⥤ C} {A B : cone F} (w : A.X = B.X) (h : (functor.const J).map (eq_to_iso w).hom ⊟ B.π = A.π) : A = B :=
begin
  /- obviously' say: -/
  induction A,
  induction B,
  dsimp at w,
  induction w,
  simp at h,
  congr,
  rw ← h,
  ext1,
  simp,
end

end cone



#print category_theory.functor.map
-- set_option pp.all true
def cone_f : isos (J ⥤ C) ⥤ isos (Type (max u v)) :=
{ obj  := cone,
  map' := λ F G α,
  { hom := λ c,
    { X := c.X,
      π := c.π ⊟ α },
    inv := λ c,
    { X := c.X,
      π := c.π ⊟ α.symm },
    hom_inv_id' :=
    begin
      tidy,
      conv {to_lhs, congr, congr', },
      rw functor.map_id, -- FIXME why doesn't simp do this?
      simp,
    end  } }

@[simp] lemma cone.w {F : J ⥤ C} (c : cone F) {j j' : J} (f : j ⟶ j') :
  c.π j ≫ F.map f = c.π j' :=
begin
  have h := eq.symm ((c.π).naturality f),
  simp at h,
  erw category.id_comp at h,
  exact h
end

/-- A `c : cocone F` is an object `c.X` and a natural transformation `c.π : F ⟹ c.X` from `F` to the constant `c.X` functor. -/
structure cocone (F : J ⥤ C) :=
(X : C)
(ι : F ⟹ (X : J ⥤ C))

@[simp] lemma cocone.w {F : J ⥤ C} (c : cocone F) {j j' : J} (f : j ⟶ j') :
  F.map f ≫ c.ι j' = c.ι j :=
begin
  have h := (c.ι).naturality f,
  simp at h,
  erw category.comp_id at h,
  exact h
end

variable {F : J ⥤ C}

namespace cone
def extend (c : cone F) {X : C} (f : X ⟶ c.X) : cone F :=
{ X := X,
  π := (f : (X : J ⥤ C) ⟹ (c.X : J ⥤ C)) ⊟ c.π }

def postcompose {G : J ⥤ C} (c : cone F) (α : F ⟹ G) : cone G :=
{ X := c.X,
  π := c.π ⊟ α }

def whisker (c : cone F) {K : Type v} [small_category K] (E : K ⥤ J) : cone (E ⋙ F) :=
{ X := c.X,
  π := whisker_left E c.π }
end cone

namespace cocone
def extend (c : cocone F) {X : C} (f : c.X ⟶ X) : cocone F :=
{ X := X,
  ι := c.ι ⊟ (f : (c.X : J ⥤ C) ⟹ (X : J ⥤ C)) }

def precompose {G : J ⥤ C} (c : cocone F) (α : G ⟹ F) : cocone G :=
{ X := c.X,
  ι := α ⊟ c.ι }

def whisker (c : cocone F) {K : Type v} [small_category K] (E : K ⥤ J) : cocone (E ⋙ F) :=
{ X := c.X,
  ι := whisker_left E c.ι }
end cocone

structure cone_morphism (A B : cone F) : Type v :=
(hom : A.X ⟶ B.X)
(w' : Π j : J, hom ≫ (B.π j) = (A.π j) . obviously)

restate_axiom cone_morphism.w'
attribute [simp] cone_morphism.w

namespace cone_morphism

@[extensionality] lemma ext {A B : cone F} {f g : cone_morphism A B} (w : f.hom = g.hom) : f = g :=
begin
  /- obviously' say: -/
  induction f,
  induction g,
  dsimp at w,
  induction w,
  refl,
end

end cone_morphism

instance cones (F : J ⥤ C) : category.{(max u v) v} (cone F) :=
{ hom  := λ A B, cone_morphism A B,
  comp := λ _ _ _ f g, { hom := f.hom ≫ g.hom },
  id   := λ B, { hom := 𝟙 B.X } }

namespace cones
@[simp] lemma id.hom   {F : J ⥤ C} (c : cone F) : (𝟙 c : cone_morphism c c).hom = 𝟙 (c.X) := rfl
@[simp] lemma comp.hom {F : J ⥤ C} {c d e : cone F} (f : c ⟶ d) (g : d ⟶ e) : ((f ≫ g) :
  cone_morphism c e).hom = (f : cone_morphism c d).hom ≫ (g : cone_morphism d e).hom := rfl

section
variables {D : Type u} [𝒟 : category.{u v} D]
include 𝒟

@[simp] def functoriality (F : J ⥤ C) (G : C ⥤ D) : (cone F) ⥤ (cone (F ⋙ G)) :=
{ obj      := λ A,
  { X := G A.X,
    π := (functor.const_compose _ _).hom ⊟ whisker_right A.π G },
  map'     := λ X Y f,
  { hom := G.map f.hom,
    w' := begin intros, dsimp, erw [category.id_comp, ←functor.map_comp, cone_morphism.w, category.id_comp] end } }
end
end cones

structure cocone_morphism (A B : cocone F) :=
(hom : A.X ⟶ B.X)
(w'  : Π j : J, (A.ι j) ≫ hom = (B.ι j) . obviously)

restate_axiom cocone_morphism.w'
attribute [simp] cocone_morphism.w

namespace cocone_morphism

@[extensionality] lemma ext {A B : cocone F} {f g : cocone_morphism A B} (w : f.hom = g.hom) : f = g :=
begin
  induction f,
  induction g,
  -- `obviously'` says:
  dsimp at w,
  induction w,
  refl,
end
end cocone_morphism

instance cocones (F : J ⥤ C) : category.{(max u v) v} (cocone F) :=
{ hom  := λ A B, cocone_morphism A B,
  comp := λ _ _ _ f g,
  { hom := f.hom ≫ g.hom,
    w' := begin intros j, rw ←category.assoc, rw ←cocone_morphism.w g, rw ←cocone_morphism.w f j end },
  id   := λ B, { hom := 𝟙 B.X } }

namespace cocones
@[simp] lemma id.hom   {F : J ⥤ C} (c : cocone F) : (𝟙 c : cocone_morphism c c).hom = 𝟙 (c.X) := rfl
@[simp] lemma comp.hom {F : J ⥤ C} {c d e : cocone F} (f : c ⟶ d) (g : d ⟶ e) : ((f ≫ g) :
  cocone_morphism c e).hom = (f : cocone_morphism c d).hom ≫ (g : cocone_morphism d e).hom := rfl

section
variables {D : Type u} [𝒟 : category.{u v} D]
include 𝒟

@[simp] def functoriality (F : J ⥤ C) (G : C ⥤ D) : (cocone F) ⥤ (cocone (F ⋙ G)) :=
{ obj := λ A,
  { X  := G A.X,
    ι  :=  whisker_right A.ι G ⊟ (functor.const_compose _ _).inv },
  map' := λ _ _ f,
  { hom := G.map f.hom,
    w'  := begin intros, dsimp, erw [category.comp_id, ←functor.map_comp, cocone_morphism.w, category.comp_id], end } }
end
end cocones

end category_theory.limits

namespace category_theory.functor

variables {D : Type u} [category.{u v} D]
variables {F : J ⥤ C} {G : J ⥤ C}

open category_theory.limits

def map_cone   (H : C ⥤ D) (c : cone F)   : cone (F ⋙ H)   := (cones.functoriality F H) c
def map_cocone (H : C ⥤ D) (c : cocone F) : cocone (F ⋙ H) := (cocones.functoriality F H) c
def map_cone_morphism   (H : C ⥤ D) {c c' : cone F}   (f : cone_morphism c c')   :
  cone_morphism   (H.map_cone c)   (H.map_cone c')   := (cones.functoriality F H).map f
def map_cocone_morphism (H : C ⥤ D) {c c' : cocone F} (f : cocone_morphism c c') :
  cocone_morphism (H.map_cocone c) (H.map_cocone c') := (cocones.functoriality F H).map f

end category_theory.functor