/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Reid Barton
-/
import category_theory.limits.shapes.images
import category_theory.filtered
import data.quot
import tactic.equiv_rw

universes u

open category_theory
open category_theory.limits

namespace category_theory.limits.types

variables {J : Type u} [small_category J]

/--
(internal implementation) the limit cone of a functor,
implemented as flat sections of a pi type
-/
def limit_cone (F : J ⥤ Type u) : cone F :=
{ X := F.sections,
  π := { app := λ j u, u.val j } }

local attribute [elab_simple] congr_fun
/-- (internal implementation) the fact that the proposed limit cone is the limit -/
def limit_cone_is_limit (F : J ⥤ Type u) : is_limit (limit_cone F) :=
{ lift := λ s v, ⟨λ j, s.π.app j v, λ j j' f, congr_fun (cone.w s f) _⟩,
  uniq' := by { intros, ext x j, exact congr_fun (w j) x } }

instance : has_limits (Type u) :=
{ has_limits_of_shape := λ J 𝒥, by exactI
  { has_limit := λ F,
    { cone := limit_cone F, is_limit := limit_cone_is_limit F } } }

/--
The equivalence between the abstract limit of `F` in `Type u`
and the "concrete" definition as the sections of `F`.
-/
def limit_equiv_sections (F : J ⥤ Type u) : (limit F : Type u) ≃ F.sections :=
(is_limit.cone_point_unique_up_to_iso (limit.is_limit F) (limit_cone_is_limit F)).to_equiv

@[simp]
lemma limit_equiv_sections_apply (F : J ⥤ Type u) (x : limit F) (j : J) :
  (((limit_equiv_sections F) x) : Π j, F.obj j) j = limit.π F j x :=
rfl

@[simp]
lemma limit_equiv_sections_symm_apply (F : J ⥤ Type u) (x : F.sections) (j : J) :
  limit.π F j ((limit_equiv_sections F).symm x) = (x : Π j, F.obj j) j :=
begin
  equiv_rw (limit_equiv_sections F).symm at x,
  simp,
end

-- PROJECT: prove this for concrete categories where the forgetful functor preserves limits
lemma limit_ext (F : J ⥤ Type u) (x y : limit F) (w : ∀ j, limit.π F j x = limit.π F j y) :
  x = y :=
begin
  apply (limit_equiv_sections F).injective,
  ext j,
  simp [w j],
end

-- TODO: are there other limits lemmas that should have `_apply` versions?
-- Can we generate these like with `@[reassoc]`?
-- PROJECT: prove these for any concrete category where the forgetful functor preserves limits?
@[simp]
lemma lift_π_apply (F : J ⥤ Type u) (s : cone F) (j : J) (x : s.X) :
  limit.π F j (limit.lift F s x) = s.π.app j x :=
congr_fun (limit.lift_π s j) x

/--
A quotient type implementing the colimit of a functor `F : J ⥤ Type u`,
as pairs `⟨j, x⟩` where `x : F.obj j`, modulo the equivalence relation generated by
`⟨j, x⟩ ~ ⟨j', x'⟩` whenever there is a morphism `f : j ⟶ j'` so `F.map f x = x'`.
-/
@[nolint has_inhabited_instance]
def quot (F : J ⥤ Type u) : Type u :=
@quot (Σ j, F.obj j) (λ p p', ∃ f : p.1 ⟶ p'.1, p'.2 = F.map f p.2)

/--
(internal implementation) the colimit cocone of a functor,
implemented as a quotient of a sigma type
-/
def colimit_cocone (F : J ⥤ Type u) : cocone F :=
{ X := quot F,
  ι :=
  { app := λ j x, quot.mk _ ⟨j, x⟩,
    naturality' := λ j j' f, funext $ λ x, eq.symm (quot.sound ⟨f, rfl⟩) } }

local attribute [elab_with_expected_type] quot.lift

/-- (internal implementation) the fact that the proposed colimit cocone is the colimit -/
def colimit_cocone_is_colimit (F : J ⥤ Type u) : is_colimit (colimit_cocone F) :=
{ desc := λ s, quot.lift (λ (p : Σ j, F.obj j), s.ι.app p.1 p.2)
    (assume ⟨j, x⟩ ⟨j', x'⟩ ⟨f, hf⟩, by rw hf; exact (congr_fun (cocone.w s f) x).symm) }

instance : has_colimits (Type u) :=
{ has_colimits_of_shape := λ J 𝒥, by exactI
  { has_colimit := λ F,
    { cocone := colimit_cocone F, is_colimit := colimit_cocone_is_colimit F } } }

/--
The equivalence between the abstract colimit of `F` in `Type u`
and the "concrete" definition as a quotient.
-/
def colimit_equiv_quot (F : J ⥤ Type u) : (colimit F : Type u) ≃ quot F :=
(is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit F) (colimit_cocone_is_colimit F)).to_equiv

@[simp]
lemma colimit_equiv_quot_symm_apply (F : J ⥤ Type u) (j : J) (x : F.obj j) :
  (colimit_equiv_quot F).symm (quot.mk _ ⟨j, x⟩) = colimit.ι F j x :=
rfl

@[simp]
lemma ι_desc_apply (F : J ⥤ Type u) (s : cocone F) (j : J) (x : F.obj j) :
  colimit.desc F s (colimit.ι F j x) = s.ι.app j x :=
congr_fun (colimit.ι_desc s j) x

lemma jointly_surjective (F : J ⥤ Type u) {t : cocone F} (h : is_colimit t)
  (x : t.X) : ∃ j y, t.ι.app j y = x :=
begin
  suffices : (λ (x : t.X), ulift.up (∃ j y, t.ι.app j y = x)) = (λ _, ulift.up true),
  { have := congr_fun this x,
    have H := congr_arg ulift.down this,
    dsimp at H,
    rwa eq_true at H },
  refine h.hom_ext _,
  intro j, ext y,
  erw iff_true,
  exact ⟨j, y, rfl⟩
end

namespace filtered_colimit
/- For filtered colimits of types, we can give an explicit description
  of the equivalence relation generated by the relation used to form
  the colimit.  -/

variables (F : J ⥤ Type u)

/--
An alternative relation on `Σ j, F.obj j`,
which generates the same equivalence relation as we use to define the colimit in `Type` above,
but that is more convenient when working with filtered colimits.

Elements in `F.obj j` and `F.obj j'` are equivalent if there is some `k : J` to the right
where their images are equal.
-/
protected def r (x y : Σ j, F.obj j) : Prop :=
∃ k (f : x.1 ⟶ k) (g : y.1 ⟶ k), F.map f x.2 = F.map g y.2

protected lemma r_ge (x y : Σ j, F.obj j) :
  (∃ f : x.1 ⟶ y.1, y.2 = F.map f x.2) → filtered_colimit.r F x y :=
λ ⟨f, hf⟩, ⟨y.1, f, 𝟙 y.1, by simp [hf]⟩

variables (t : cocone F)
local attribute [elab_simple] nat_trans.app

/-- Recognizing filtered colimits of types. -/
noncomputable def is_colimit_of (hsurj : ∀ (x : t.X), ∃ i xi, x = t.ι.app i xi)
  (hinj : ∀ i j xi xj, t.ι.app i xi = t.ι.app j xj →
   ∃ k (f : i ⟶ k) (g : j ⟶ k), F.map f xi = F.map g xj) : is_colimit t :=
-- Strategy: Prove that the map from "the" colimit of F (defined above) to t.X
-- is a bijection.
begin
  apply is_colimit.of_iso_colimit (colimit.is_colimit F),
  refine cocones.ext (equiv.to_iso (equiv.of_bijective _ _)) _,
  { exact colimit.desc F t },
  { split,
    { show function.injective _,
      intros a b h,
      rcases jointly_surjective F (colimit.is_colimit F) a with ⟨i, xi, rfl⟩,
      rcases jointly_surjective F (colimit.is_colimit F) b with ⟨j, xj, rfl⟩,
      change (colimit.ι F i ≫ colimit.desc F t) xi = (colimit.ι F j ≫ colimit.desc F t) xj at h,
      rw [colimit.ι_desc, colimit.ι_desc] at h,
      rcases hinj i j xi xj h with ⟨k, f, g, h'⟩,
      change colimit.ι F i xi = colimit.ι F j xj,
      rw [←colimit.w F f, ←colimit.w F g],
      change colimit.ι F k (F.map f xi) = colimit.ι F k (F.map g xj),
      rw h' },
    { show function.surjective _,
      intro x,
      rcases hsurj x with ⟨i, xi, rfl⟩,
      use colimit.ι F i xi,
      simp } },
  { intro j, apply colimit.ι_desc }
end

variables [is_filtered_or_empty J]

protected lemma r_equiv : equivalence (filtered_colimit.r F) :=
⟨λ x, ⟨x.1, 𝟙 x.1, 𝟙 x.1, rfl⟩,
 λ x y ⟨k, f, g, h⟩, ⟨k, g, f, h.symm⟩,
 λ x y z ⟨k, f, g, h⟩ ⟨k', f', g', h'⟩,
   let ⟨l, fl, gl, _⟩ := is_filtered_or_empty.cocone_objs k k',
       ⟨m, n, hn⟩ := is_filtered_or_empty.cocone_maps (g ≫ fl) (f' ≫ gl) in
   ⟨m, f ≫ fl ≫ n, g' ≫ gl ≫ n, calc
      F.map (f ≫ fl ≫ n) x.2
          = F.map (fl ≫ n) (F.map f x.2)  : by simp
      ... = F.map (fl ≫ n) (F.map g y.2)  : by rw h
      ... = F.map ((g ≫ fl) ≫ n) y.2      : by simp
      ... = F.map ((f' ≫ gl) ≫ n) y.2     : by rw hn
      ... = F.map (gl ≫ n) (F.map f' y.2) : by simp
      ... = F.map (gl ≫ n) (F.map g' z.2) : by rw h'
      ... = F.map (g' ≫ gl ≫ n) z.2       : by simp⟩⟩

protected lemma r_eq :
  filtered_colimit.r F = eqv_gen (λ x y, ∃ f : x.1 ⟶ y.1, y.2 = F.map f x.2) :=
begin
  apply le_antisymm,
  { rintros ⟨i, x⟩ ⟨j, y⟩ ⟨k, f, g, h⟩,
    exact eqv_gen.trans _ ⟨k, F.map f x⟩ _ (eqv_gen.rel _ _ ⟨f, rfl⟩)
      (eqv_gen.symm _ _ (eqv_gen.rel _ _ ⟨g, h⟩)) },
  { intros x y,
    convert relation.eqv_gen_mono (filtered_colimit.r_ge F),
    apply propext,
    symmetry,
    exact relation.eqv_gen_iff_of_equivalence (filtered_colimit.r_equiv F) }
end

lemma colimit_eq_iff {i j : J} {xi : F.obj i} {xj : F.obj j} :
  colimit.ι F i xi = colimit.ι F j xj ↔ ∃ k (f : i ⟶ k) (g : j ⟶ k), F.map f xi = F.map g xj :=
begin
  change quot.mk _ _ = quot.mk _ _ ↔ _,
  rw [quot.eq, ←filtered_colimit.r_eq],
  refl
end

variables {t} (ht : is_colimit t)
lemma is_colimit_eq_iff {i j : J} {xi : F.obj i} {xj : F.obj j} :
  t.ι.app i xi = t.ι.app j xj ↔ ∃ k (f : i ⟶ k) (g : j ⟶ k), F.map f xi = F.map g xj :=
let t' := colimit.cocone F,
    e : t' ≅ t := is_colimit.unique_up_to_iso (colimit.is_colimit F) ht,
    e' : t'.X ≅ t.X := (cocones.forget _).map_iso e in
begin
  refine iff.trans _ (colimit_eq_iff F),
  convert equiv.apply_eq_iff_eq e'.to_equiv _ _; rw ←e.hom.w; refl
end

end filtered_colimit

variables {α β : Type u} (f : α ⟶ β)

section -- implementation of `has_image`
/-- the image of a morphism in Type is just `set.range f` -/
def image : Type u := set.range f

instance [inhabited α] : inhabited (image f) :=
{ default := ⟨f (default α), ⟨_, rfl⟩⟩ }

/-- the inclusion of `image f` into the target -/
def image.ι : image f ⟶ β := subtype.val

instance : mono (image.ι f) :=
(mono_iff_injective _).2 subtype.val_injective

variables {f}

/-- the universal property for the image factorisation -/
noncomputable def image.lift (F' : mono_factorisation f) : image f ⟶ F'.I :=
(λ x, F'.e (classical.indefinite_description _ x.2).1 : image f → F'.I)

lemma image.lift_fac (F' : mono_factorisation f) : image.lift F' ≫ F'.m = image.ι f :=
begin
  ext x,
  change (F'.e ≫ F'.m) _ = _,
  rw [F'.fac, (classical.indefinite_description _ x.2).2],
  refl,
end
end

/-- the factorisation of any morphism in AddCommGroup through a mono. -/
def mono_factorisation : mono_factorisation f :=
{ I := image f,
  m := image.ι f,
  e := set.range_factorization f }

noncomputable instance : has_image f :=
{ F := mono_factorisation f,
  is_image :=
  { lift := image.lift,
    lift_fac' := image.lift_fac } }

noncomputable instance : has_images (Type u) :=
{ has_image := infer_instance }

noncomputable instance : has_image_maps (Type u) :=
{ has_image_map := λ f g st,
  { map := λ x, ⟨st.right x.1, ⟨st.left (classical.some x.2),
      begin
        have p := st.w,
        replace p := congr_fun p (classical.some x.2),
        simp only [functor.id_map, types_comp_apply, subtype.val_eq_coe] at p,
        erw [p, classical.some_spec x.2],
      end⟩⟩ } }

@[simp] lemma image_map {f g : arrow (Type u)} (st : f ⟶ g) (x : image f.hom) :
  (image.map st x).val = st.right x.1 :=
rfl

end category_theory.limits.types
