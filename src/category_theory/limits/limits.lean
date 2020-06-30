/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Mario Carneiro, Scott Morrison, Floris van Doorn
-/
import category_theory.limits.cones
import category_theory.adjunction.basic
import category_theory.reflect_isomorphisms

open category_theory category_theory.category category_theory.functor opposite

namespace category_theory.limits

universes v u u' u'' w -- declare the `v`'s first; see `category_theory.category` for an explanation

-- See the notes at the top of cones.lean, explaining why we can't allow `J : Prop` here.
variables {J K : Type v} [small_category J] [small_category K]
variables {C : Type u} [category.{v} C]

variables {F : J ⥤ C}

/-- A cone `t` on `F` is a limit cone if each cone on `F` admits a unique
  cone morphism to `t`. -/
@[nolint has_inhabited_instance]
structure is_limit (t : cone F) :=
(lift  : Π (s : cone F), s.X ⟶ t.X)
(fac'  : ∀ (s : cone F) (j : J), lift s ≫ t.π.app j = s.π.app j . obviously)
(uniq' : ∀ (s : cone F) (m : s.X ⟶ t.X) (w : ∀ j : J, m ≫ t.π.app j = s.π.app j),
  m = lift s . obviously)

restate_axiom is_limit.fac'
attribute [simp, reassoc] is_limit.fac
restate_axiom is_limit.uniq'

namespace is_limit

instance subsingleton {t : cone F} : subsingleton (is_limit t) :=
⟨by intros P Q; cases P; cases Q; congr; ext; solve_by_elim⟩

/- Repackaging the definition in terms of cone morphisms. -/

/-- The universal morphism from any other cone to a limit cone. -/
def lift_cone_morphism {t : cone F} (h : is_limit t) (s : cone F) : s ⟶ t :=
{ hom := h.lift s }

lemma uniq_cone_morphism {s t : cone F} (h : is_limit t) {f f' : s ⟶ t} :
  f = f' :=
have ∀ {g : s ⟶ t}, g = h.lift_cone_morphism s, by intro g; ext; exact h.uniq _ _ g.w,
this.trans this.symm

/--
Alternative constructor for `is_limit`,
providing a morphism of cones rather than a morphism between the cone points
and separately the factorisation condition.
-/
def mk_cone_morphism {t : cone F}
  (lift : Π (s : cone F), s ⟶ t)
  (uniq' : ∀ (s : cone F) (m : s ⟶ t), m = lift s) : is_limit t :=
{ lift := λ s, (lift s).hom,
  uniq' := λ s m w,
    have cone_morphism.mk m w = lift s, by apply uniq',
    congr_arg cone_morphism.hom this }

/-- Limit cones on `F` are unique up to isomorphism. -/
def unique_up_to_iso {s t : cone F} (P : is_limit s) (Q : is_limit t) : s ≅ t :=
{ hom := Q.lift_cone_morphism s,
  inv := P.lift_cone_morphism t,
  hom_inv_id' := P.uniq_cone_morphism,
  inv_hom_id' := Q.uniq_cone_morphism }

/-- Limits of `F` are unique up to isomorphism. -/
-- We may later want to prove the coherence of these isomorphisms.
def cone_point_unique_up_to_iso {s t : cone F} (P : is_limit s) (Q : is_limit t) : s.X ≅ t.X :=
(cones.forget F).map_iso (unique_up_to_iso P Q)

/-- Transport evidence that a cone is a limit cone across an isomorphism of cones. -/
def of_iso_limit {r t : cone F} (P : is_limit r) (i : r ≅ t) : is_limit t :=
is_limit.mk_cone_morphism
  (λ s, P.lift_cone_morphism s ≫ i.hom)
  (λ s m, by rw ←i.comp_inv_eq; apply P.uniq_cone_morphism)

/--
If the canonical morphism from a cone point to a limiting cone point is an iso, then the
first cone was limiting also.
-/
def of_point_iso {r t : cone F} (P : is_limit r) [i : is_iso (P.lift t)] : is_limit t :=
of_iso_limit P
begin
  haveI : is_iso (P.lift_cone_morphism t).hom := i,
  haveI : is_iso (P.lift_cone_morphism t) := cone_iso_of_hom_iso _,
  symmetry,
  apply as_iso (P.lift_cone_morphism t),
end

variables {t : cone F}

lemma hom_lift (h : is_limit t) {W : C} (m : W ⟶ t.X) :
  m = h.lift { X := W, π := { app := λ b, m ≫ t.π.app b } } :=
h.uniq { X := W, π := { app := λ b, m ≫ t.π.app b } } m (λ b, rfl)

/-- Two morphisms into a limit are equal if their compositions with
  each cone morphism are equal. -/
lemma hom_ext (h : is_limit t) {W : C} {f f' : W ⟶ t.X}
  (w : ∀ j, f ≫ t.π.app j = f' ≫ t.π.app j) : f = f' :=
by rw [h.hom_lift f, h.hom_lift f']; congr; exact funext w

/--
Given two functors which have equivalent categories of cones, we can transport a limiting cone across
the equivalence.
-/
def of_cone_equiv {D : Type u'} [category.{v} D] {G : K ⥤ D}
  (h : cone G ⥤ cone F) [is_right_adjoint h] {c : cone G} (t : is_limit c) :
  is_limit (h.obj c) :=
mk_cone_morphism
  (λ s, (adjunction.of_right_adjoint h).hom_equiv s c (t.lift_cone_morphism _))
  (λ s m, (adjunction.eq_hom_equiv_apply _ _ _).2 t.uniq_cone_morphism )

/--
The cone points of two limit cones for naturally isomorphic functors
are themselves isomorphic.
-/
@[simps]
def cone_points_iso_of_nat_iso {F G : J ⥤ C} {s : cone F} {t : cone G}
  (P : is_limit s) (Q : is_limit t) (w : F ≅ G) : s.X ≅ t.X :=
{ hom := Q.lift ((limits.cones.postcompose w.hom).obj s),
  inv := P.lift ((limits.cones.postcompose w.inv).obj t),
  hom_inv_id' := by { apply hom_ext P, tidy, },
  inv_hom_id' := by { apply hom_ext Q, tidy, }, }

section equivalence
open category_theory.equivalence

/--
If `s : cone F` is a limit cone, so is `s` whiskered by an equivalence `e`.
-/
def whisker_equivalence {s : cone F} (P : is_limit s) (e : K ≌ J) :
  is_limit (s.whisker e.functor) :=
of_cone_equiv (cones.whiskering_equivalence e).functor P

/--
We can prove two cone points `(s : cone F).X` and `(t.cone F).X` are isomorphic if
* both cones are limit cones
* their indexing categories are equivalent via some `e : J ≌ K`,
* the triangle of functors commutes up to a natural isomorphism: `e.functor ⋙ G ≅ F`.

This is the most general form of uniqueness of cone points,
allowing relabelling of both the indexing category (up to equivalence)
and the functor (up to natural isomorphism).
-/
@[simps]
def cone_points_iso_of_equivalence {F : J ⥤ C} {s : cone F} {G : K ⥤ C} {t : cone G}
  (P : is_limit s) (Q : is_limit t) (e : J ≌ K) (w : e.functor ⋙ G ≅ F) : s.X ≅ t.X :=
let w' : e.inverse ⋙ F ≅ G := (iso_whisker_left e.inverse w).symm ≪≫ inv_fun_id_assoc e G in
{ hom := Q.lift ((cones.equivalence_of_reindexing e.symm w').functor.obj s),
  inv := P.lift ((cones.equivalence_of_reindexing e w).functor.obj t),
  hom_inv_id' :=
  begin
    apply hom_ext P, intros j,
    dsimp,
    simp only [limits.cone.whisker_π, limits.cones.postcompose_obj_π, fac, whisker_left_app,
      assoc, id_comp, inv_fun_id_assoc_hom_app, fac_assoc, nat_trans.comp_app],
    rw [counit_functor, ←functor.comp_map, w.hom.naturality],
    simp,
  end,
  inv_hom_id' := by { apply hom_ext Q, tidy, }, }

end equivalence

/-- The universal property of a limit cone: a map `W ⟶ X` is the same as
  a cone on `F` with vertex `W`. -/
def hom_iso (h : is_limit t) (W : C) : (W ⟶ t.X) ≅ ((const J).obj W ⟶ F) :=
{ hom := λ f, (t.extend f).π,
  inv := λ π, h.lift { X := W, π := π },
  hom_inv_id' := by ext f; apply h.hom_ext; intro j; simp; dsimp; refl }

@[simp] lemma hom_iso_hom (h : is_limit t) {W : C} (f : W ⟶ t.X) :
  (is_limit.hom_iso h W).hom f = (t.extend f).π := rfl

/-- The limit of `F` represents the functor taking `W` to
  the set of cones on `F` with vertex `W`. -/
def nat_iso (h : is_limit t) : yoneda.obj t.X ≅ F.cones :=
nat_iso.of_components (λ W, is_limit.hom_iso h (unop W)) (by tidy).

/--
Another, more explicit, formulation of the universal property of a limit cone.
See also `hom_iso`.
-/
def hom_iso' (h : is_limit t) (W : C) :
  ((W ⟶ t.X) : Type v) ≅ { p : Π j, W ⟶ F.obj j // ∀ {j j'} (f : j ⟶ j'), p j ≫ F.map f = p j' } :=
h.hom_iso W ≪≫
{ hom := λ π,
  ⟨λ j, π.app j, λ j j' f,
   by convert ←(π.naturality f).symm; apply id_comp⟩,
  inv := λ p,
  { app := λ j, p.1 j,
    naturality' := λ j j' f, begin dsimp, rw [id_comp], exact (p.2 f).symm end } }

/-- If G : C → D is a faithful functor which sends t to a limit cone,
  then it suffices to check that the induced maps for the image of t
  can be lifted to maps of C. -/
def of_faithful {t : cone F} {D : Type u'} [category.{v} D] (G : C ⥤ D) [faithful G]
  (ht : is_limit (G.map_cone t)) (lift : Π (s : cone F), s.X ⟶ t.X)
  (h : ∀ s, G.map (lift s) = ht.lift (G.map_cone s)) : is_limit t :=
{ lift := lift,
  fac' := λ s j, by apply G.map_injective; rw [G.map_comp, h]; apply ht.fac,
  uniq' := λ s m w, begin
    apply G.map_injective, rw h,
    refine ht.uniq (G.map_cone s) _ (λ j, _),
    convert ←congr_arg (λ f, G.map f) (w j),
    apply G.map_comp
  end }

/--
If `F` and `G` are naturally isomorphic, then `F.map_cone c` being a limit implies
`G.map_cone c` is also a limit.
-/
def map_cone_equiv {D : Type u'} [category.{v} D] {K : J ⥤ C} {F G : C ⥤ D} (h : F ≅ G) {c : cone K}
  (t : is_limit (F.map_cone c)) : is_limit (G.map_cone c) :=
{ lift := λ s, t.lift ((cones.postcompose (iso_whisker_left K h).inv).obj s) ≫ h.hom.app c.X,
  fac' := λ s j,
  begin
    slice_lhs 2 3 {erw ← h.hom.naturality (c.π.app j)},
    slice_lhs 1 2 {erw t.fac ((cones.postcompose (iso_whisker_left K h).inv).obj s) j},
    dsimp,
    slice_lhs 2 3 {rw nat_iso.inv_hom_id_app},
    rw category.comp_id,
  end,
  uniq' := λ s m J,
  begin
    rw ← cancel_mono (h.inv.app c.X),
    apply t.hom_ext,
    intro j,
    dsimp,
    slice_lhs 2 3 {erw ← h.inv.naturality (c.π.app j)},
    slice_lhs 1 2 {erw J j},
    conv_rhs {congr, rw [category.assoc, nat_iso.hom_inv_id_app, comp_id]},
    apply (t.fac ((cones.postcompose (iso_whisker_left K h).inv).obj s) j).symm
  end }

/--
A cone is a limit cone exactly if
there is a unique cone morphism from any other cone.
-/
def iso_unique_cone_morphism {t : cone F} :
  is_limit t ≅ Π s, unique (s ⟶ t) :=
{ hom := λ h s,
  { default := h.lift_cone_morphism s,
    uniq := λ _, h.uniq_cone_morphism },
  inv := λ h,
  { lift := λ s, (h s).default.hom,
    uniq' := λ s f w, congr_arg cone_morphism.hom ((h s).uniq ⟨f, w⟩) } }

namespace of_nat_iso
variables {X : C} (h : yoneda.obj X ≅ F.cones)

/-- If `F.cones` is represented by `X`, each morphism `f : Y ⟶ X` gives a cone with cone point `Y`. -/
def cone_of_hom {Y : C} (f : Y ⟶ X) : cone F :=
{ X := Y, π := h.hom.app (op Y) f }

/-- If `F.cones` is represented by `X`, each cone `s` gives a morphism `s.X ⟶ X`. -/
def hom_of_cone (s : cone F) : s.X ⟶ X := h.inv.app (op s.X) s.π

@[simp] lemma cone_of_hom_of_cone (s : cone F) : cone_of_hom h (hom_of_cone h s) = s :=
begin
  dsimp [cone_of_hom, hom_of_cone], cases s, congr, dsimp,
  exact congr_fun (congr_fun (congr_arg nat_trans.app h.inv_hom_id) (op s_X)) s_π,
end

@[simp] lemma hom_of_cone_of_hom {Y : C} (f : Y ⟶ X) : hom_of_cone h (cone_of_hom h f) = f :=
congr_fun (congr_fun (congr_arg nat_trans.app h.hom_inv_id) (op Y)) f

/-- If `F.cones` is represented by `X`, the cone corresponding to the identity morphism on `X`
will be a limit cone. -/
def limit_cone : cone F :=
cone_of_hom h (𝟙 X)

/-- If `F.cones` is represented by `X`, the cone corresponding to a morphism `f : Y ⟶ X` is
the limit cone extended by `f`. -/
lemma cone_of_hom_fac {Y : C} (f : Y ⟶ X) :
cone_of_hom h f = (limit_cone h).extend f :=
begin
  dsimp [cone_of_hom, limit_cone, cone.extend],
  congr,
  ext j,
  have t := congr_fun (h.hom.naturality f.op) (𝟙 X),
  dsimp at t,
  simp only [comp_id] at t,
  rw congr_fun (congr_arg nat_trans.app t) j,
  refl,
end

/-- If `F.cones` is represented by `X`, any cone is the extension of the limit cone by the
corresponding morphism. -/
lemma cone_fac (s : cone F) : (limit_cone h).extend (hom_of_cone h s) = s :=
begin
  rw ←cone_of_hom_of_cone h s,
  conv_lhs { simp only [hom_of_cone_of_hom] },
  apply (cone_of_hom_fac _ _).symm,
end

end of_nat_iso

section
open of_nat_iso

/--
If `F.cones` is representable, then the cone corresponding to the identity morphism on
the representing object is a limit cone.
-/
def of_nat_iso {X : C} (h : yoneda.obj X ≅ F.cones) :
  is_limit (limit_cone h) :=
{ lift := λ s, hom_of_cone h s,
  fac' := λ s j,
  begin
    have h := cone_fac h s,
    cases s,
    injection h with h₁ h₂,
    simp only [heq_iff_eq] at h₂,
    conv_rhs { rw ← h₂ }, refl,
  end,
  uniq' := λ s m w,
  begin
    rw ←hom_of_cone_of_hom h m,
    congr,
    rw cone_of_hom_fac,
    dsimp, cases s, congr,
    ext j, exact w j,
  end }
end

end is_limit

/-- A cocone `t` on `F` is a colimit cocone if each cocone on `F` admits a unique
  cocone morphism from `t`. -/
@[nolint has_inhabited_instance]
structure is_colimit (t : cocone F) :=
(desc  : Π (s : cocone F), t.X ⟶ s.X)
(fac'  : ∀ (s : cocone F) (j : J), t.ι.app j ≫ desc s = s.ι.app j . obviously)
(uniq' : ∀ (s : cocone F) (m : t.X ⟶ s.X) (w : ∀ j : J, t.ι.app j ≫ m = s.ι.app j),
  m = desc s . obviously)

restate_axiom is_colimit.fac'
attribute [simp,reassoc] is_colimit.fac
restate_axiom is_colimit.uniq'

namespace is_colimit

instance subsingleton {t : cocone F} : subsingleton (is_colimit t) :=
⟨by intros P Q; cases P; cases Q; congr; ext; solve_by_elim⟩

/- Repackaging the definition in terms of cone morphisms. -/

/-- The universal morphism from a colimit cocone to any other cone. -/
def desc_cocone_morphism {t : cocone F} (h : is_colimit t) (s : cocone F) : t ⟶ s :=
{ hom := h.desc s }

lemma uniq_cocone_morphism {s t : cocone F} (h : is_colimit t) {f f' : t ⟶ s} :
  f = f' :=
have ∀ {g : t ⟶ s}, g = h.desc_cocone_morphism s, by intro g; ext; exact h.uniq _ _ g.w,
this.trans this.symm

/--
Alternative constructor for `is_colimit`,
providing a morphism of cocones rather than a morphism between the cocone points
and separately the factorisation condition.
-/
def mk_cocone_morphism {t : cocone F}
  (desc : Π (s : cocone F), t ⟶ s)
  (uniq' : ∀ (s : cocone F) (m : t ⟶ s), m = desc s) : is_colimit t :=
{ desc := λ s, (desc s).hom,
  uniq' := λ s m w,
    have cocone_morphism.mk m w = desc s, by apply uniq',
    congr_arg cocone_morphism.hom this }

/-- Limit cones on `F` are unique up to isomorphism. -/
def unique_up_to_iso {s t : cocone F} (P : is_colimit s) (Q : is_colimit t) : s ≅ t :=
{ hom := P.desc_cocone_morphism t,
  inv := Q.desc_cocone_morphism s,
  hom_inv_id' := P.uniq_cocone_morphism,
  inv_hom_id' := Q.uniq_cocone_morphism }

/-- Colimits of `F` are unique up to isomorphism. -/
-- We may later want to prove the coherence of these isomorphisms.
def cocone_point_unique_up_to_iso {s t : cocone F} (P : is_colimit s) (Q : is_colimit t) : s.X ≅ t.X :=
(cocones.forget F).map_iso (unique_up_to_iso P Q)

/-- Transport evidence that a cocone is a colimit cocone across an isomorphism of cocones. -/
def of_iso_colimit {r t : cocone F} (P : is_colimit r) (i : r ≅ t) : is_colimit t :=
is_colimit.mk_cocone_morphism
  (λ s, i.inv ≫ P.desc_cocone_morphism s)
  (λ s m, by rw i.eq_inv_comp; apply P.uniq_cocone_morphism)

/--
If the canonical morphism to a cocone point from a colimiting cocone point is an iso, then the
first cocone was colimiting also.
-/
def of_point_iso {r t : cocone F} (P : is_colimit r) [i : is_iso (P.desc t)] : is_colimit t :=
of_iso_colimit P
begin
  haveI : is_iso (P.desc_cocone_morphism t).hom := i,
  haveI : is_iso (P.desc_cocone_morphism t) := cocone_iso_of_hom_iso _,
  apply as_iso (P.desc_cocone_morphism t),
end

variables {t : cocone F}

lemma hom_desc (h : is_colimit t) {W : C} (m : t.X ⟶ W) :
  m = h.desc { X := W, ι := { app := λ b, t.ι.app b ≫ m,
    naturality' := by intros; erw [←assoc, t.ι.naturality, comp_id, comp_id] } } :=
h.uniq { X := W, ι := { app := λ b, t.ι.app b ≫ m, naturality' := _ } } m (λ b, rfl)

/-- Two morphisms out of a colimit are equal if their compositions with
  each cocone morphism are equal. -/
lemma hom_ext (h : is_colimit t) {W : C} {f f' : t.X ⟶ W}
  (w : ∀ j, t.ι.app j ≫ f = t.ι.app j ≫ f') : f = f' :=
by rw [h.hom_desc f, h.hom_desc f']; congr; exact funext w

/--
Given two functors which have equivalent categories of cocones, we can transport a limiting cocone
across the equivalence.
-/
def of_cocone_equiv {D : Type u'} [category.{v} D] {G : K ⥤ D}
  (h : cocone G ⥤ cocone F) [is_left_adjoint h] {c : cocone G} (t : is_colimit c) :
  is_colimit (h.obj c) :=
mk_cocone_morphism
  (λ s, ((adjunction.of_left_adjoint h).hom_equiv c s).symm (t.desc_cocone_morphism _))
  (λ s m, (adjunction.hom_equiv_apply_eq _ _ _).1 t.uniq_cocone_morphism)

/--
The cocone points of two colimit cocones for naturally isomorphic functors
are themselves isomorphic.
-/
@[simps]
def cocone_points_iso_of_nat_iso {F G : J ⥤ C} {s : cocone F} {t : cocone G}
  (P : is_colimit s) (Q : is_colimit t) (w : F ≅ G) : s.X ≅ t.X :=
{ hom := P.desc ((limits.cocones.precompose w.hom).obj t),
  inv := Q.desc ((limits.cocones.precompose w.inv).obj s),
  hom_inv_id' := by { apply hom_ext P, tidy, },
  inv_hom_id' := by { apply hom_ext Q, tidy, }, }

section equivalence
open category_theory.equivalence

/--
If `s : cone F` is a limit cone, so is `s` whiskered by an equivalence `e`.
-/
def whisker_equivalence {s : cocone F} (P : is_colimit s) (e : K ≌ J) :
  is_colimit (s.whisker e.functor) :=
of_cocone_equiv (cocones.whiskering_equivalence e).functor P

/--
We can prove two cocone points `(s : cocone F).X` and `(t.cocone F).X` are isomorphic if
* both cocones are colimit ccoones
* their indexing categories are equivalent via some `e : J ≌ K`,
* the triangle of functors commutes up to a natural isomorphism: `e.functor ⋙ G ≅ F`.

This is the most general form of uniqueness of cocone points,
allowing relabelling of both the indexing category (up to equivalence)
and the functor (up to natural isomorphism).
-/
@[simps]
def cocone_points_iso_of_equivalence {F : J ⥤ C} {s : cocone F} {G : K ⥤ C} {t : cocone G}
  (P : is_colimit s) (Q : is_colimit t) (e : J ≌ K) (w : e.functor ⋙ G ≅ F) : s.X ≅ t.X :=
let w' : e.inverse ⋙ F ≅ G := (iso_whisker_left e.inverse w).symm ≪≫ inv_fun_id_assoc e G in
{ hom := P.desc ((cocones.equivalence_of_reindexing e w).functor.obj t),
  inv := Q.desc ((cocones.equivalence_of_reindexing e.symm w').functor.obj s),
  hom_inv_id' :=
  begin
    apply hom_ext P, intros j,
    dsimp,
    simp only [limits.cocone.whisker_ι, fac, inv_fun_id_assoc_inv_app, whisker_left_app, assoc,
      comp_id, limits.cocones.precompose_obj_ι, fac_assoc, nat_trans.comp_app],
    rw [←functor_unit, ←functor.comp_map, ←w.inv.naturality_assoc],
    dsimp,
    simp,
  end,
  inv_hom_id' := by { apply hom_ext Q, tidy, }, }

end equivalence

/-- The universal property of a colimit cocone: a map `X ⟶ W` is the same as
  a cocone on `F` with vertex `W`. -/
def hom_iso (h : is_colimit t) (W : C) : (t.X ⟶ W) ≅ (F ⟶ (const J).obj W) :=
{ hom := λ f, (t.extend f).ι,
  inv := λ ι, h.desc { X := W, ι := ι },
  hom_inv_id' := by ext f; apply h.hom_ext; intro j; simp; dsimp; refl }

@[simp] lemma hom_iso_hom (h : is_colimit t) {W : C} (f : t.X ⟶ W) :
  (is_colimit.hom_iso h W).hom f = (t.extend f).ι := rfl

/-- The colimit of `F` represents the functor taking `W` to
  the set of cocones on `F` with vertex `W`. -/
def nat_iso (h : is_colimit t) : coyoneda.obj (op t.X) ≅ F.cocones :=
nat_iso.of_components (is_colimit.hom_iso h) (by intros; ext; dsimp; rw ←assoc; refl)

/--
Another, more explicit, formulation of the universal property of a colimit cocone.
See also `hom_iso`.
-/
def hom_iso' (h : is_colimit t) (W : C) :
  ((t.X ⟶ W) : Type v) ≅ { p : Π j, F.obj j ⟶ W // ∀ {j j' : J} (f : j ⟶ j'), F.map f ≫ p j' = p j } :=
h.hom_iso W ≪≫
{ hom := λ ι,
  ⟨λ j, ι.app j, λ j j' f,
   by convert ←(ι.naturality f); apply comp_id⟩,
  inv := λ p,
  { app := λ j, p.1 j,
    naturality' := λ j j' f, begin dsimp, rw [comp_id], exact (p.2 f) end } }

/-- If G : C → D is a faithful functor which sends t to a colimit cocone,
  then it suffices to check that the induced maps for the image of t
  can be lifted to maps of C. -/
def of_faithful {t : cocone F} {D : Type u'} [category.{v} D] (G : C ⥤ D) [faithful G]
  (ht : is_colimit (G.map_cocone t)) (desc : Π (s : cocone F), t.X ⟶ s.X)
  (h : ∀ s, G.map (desc s) = ht.desc (G.map_cocone s)) : is_colimit t :=
{ desc := desc,
  fac' := λ s j, by apply G.map_injective; rw [G.map_comp, h]; apply ht.fac,
  uniq' := λ s m w, begin
    apply G.map_injective, rw h,
    refine ht.uniq (G.map_cocone s) _ (λ j, _),
    convert ←congr_arg (λ f, G.map f) (w j),
    apply G.map_comp
  end }

/--
A cocone is a colimit cocone exactly if
there is a unique cocone morphism from any other cocone.
-/
def iso_unique_cocone_morphism {t : cocone F} :
  is_colimit t ≅ Π s, unique (t ⟶ s) :=
{ hom := λ h s,
  { default := h.desc_cocone_morphism s,
    uniq := λ _, h.uniq_cocone_morphism },
  inv := λ h,
  { desc := λ s, (h s).default.hom,
    uniq' := λ s f w, congr_arg cocone_morphism.hom ((h s).uniq ⟨f, w⟩) } }

namespace of_nat_iso
variables {X : C} (h : coyoneda.obj (op X) ≅ F.cocones)

/-- If `F.cocones` is corepresented by `X`, each morphism `f : X ⟶ Y` gives a cocone with cone point `Y`. -/
def cocone_of_hom {Y : C} (f : X ⟶ Y) : cocone F :=
{ X := Y, ι := h.hom.app Y f }

/-- If `F.cocones` is corepresented by `X`, each cocone `s` gives a morphism `X ⟶ s.X`. -/
def hom_of_cocone (s : cocone F) : X ⟶ s.X := h.inv.app s.X s.ι

@[simp] lemma cocone_of_hom_of_cocone (s : cocone F) : cocone_of_hom h (hom_of_cocone h s) = s :=
begin
  dsimp [cocone_of_hom, hom_of_cocone], cases s, congr, dsimp,
  exact congr_fun (congr_fun (congr_arg nat_trans.app h.inv_hom_id) s_X) s_ι,
end

@[simp] lemma hom_of_cocone_of_hom {Y : C} (f : X ⟶ Y) : hom_of_cocone h (cocone_of_hom h f) = f :=
congr_fun (congr_fun (congr_arg nat_trans.app h.hom_inv_id) Y) f

/-- If `F.cocones` is corepresented by `X`, the cocone corresponding to the identity morphism on `X`
will be a colimit cocone. -/
def colimit_cocone : cocone F :=
cocone_of_hom h (𝟙 X)

/-- If `F.cocones` is corepresented by `X`, the cocone corresponding to a morphism `f : Y ⟶ X` is
the colimit cocone extended by `f`. -/
lemma cocone_of_hom_fac {Y : C} (f : X ⟶ Y) :
cocone_of_hom h f = (colimit_cocone h).extend f :=
begin
  dsimp [cocone_of_hom, colimit_cocone, cocone.extend],
  congr,
  ext j,
  have t := congr_fun (h.hom.naturality f) (𝟙 X),
  dsimp at t,
  simp only [id_comp] at t,
  rw congr_fun (congr_arg nat_trans.app t) j,
  refl,
end

/-- If `F.cocones` is corepresented by `X`, any cocone is the extension of the colimit cocone by the
corresponding morphism. -/
lemma cocone_fac (s : cocone F) : (colimit_cocone h).extend (hom_of_cocone h s) = s :=
begin
  rw ←cocone_of_hom_of_cocone h s,
  conv_lhs { simp only [hom_of_cocone_of_hom] },
  apply (cocone_of_hom_fac _ _).symm,
end

end of_nat_iso

section
open of_nat_iso

/--
If `F.cocones` is corepresentable, then the cocone corresponding to the identity morphism on
the representing object is a colimit cocone.
-/
def of_nat_iso {X : C} (h : coyoneda.obj (op X) ≅ F.cocones) :
  is_colimit (colimit_cocone h) :=
{ desc := λ s, hom_of_cocone h s,
  fac' := λ s j,
  begin
    have h := cocone_fac h s,
    cases s,
    injection h with h₁ h₂,
    simp only [heq_iff_eq] at h₂,
    conv_rhs { rw ← h₂ }, refl,
  end,
  uniq' := λ s m w,
  begin
    rw ←hom_of_cocone_of_hom h m,
    congr,
    rw cocone_of_hom_fac,
    dsimp, cases s, congr,
    ext j, exact w j,
  end }
end

end is_colimit

section limit

/-- `has_limit F` represents a particular chosen limit of the diagram `F`. -/
class has_limit (F : J ⥤ C) :=
(cone : cone F)
(is_limit : is_limit cone)

variables (J C)

/-- `C` has limits of shape `J` if we have chosen a particular limit of
  every functor `F : J ⥤ C`. -/
class has_limits_of_shape :=
(has_limit : Π F : J ⥤ C, has_limit F)

/-- `C` has all (small) limits if it has limits of every shape. -/
class has_limits :=
(has_limits_of_shape : Π (J : Type v) [𝒥 : small_category J], has_limits_of_shape J C)

variables {J C}

@[priority 100] -- see Note [lower instance priority]
instance has_limit_of_has_limits_of_shape
  {J : Type v} [small_category J] [H : has_limits_of_shape J C] (F : J ⥤ C) : has_limit F :=
has_limits_of_shape.has_limit F

@[priority 100] -- see Note [lower instance priority]
instance has_limits_of_shape_of_has_limits
  {J : Type v} [small_category J] [H : has_limits C] : has_limits_of_shape J C :=
has_limits.has_limits_of_shape J

/- Interface to the `has_limit` class. -/

/-- The chosen limit cone of a functor. -/
def limit.cone (F : J ⥤ C) [has_limit F] : cone F := has_limit.cone

/-- The chosen limit object of a functor. -/
def limit (F : J ⥤ C) [has_limit F] := (limit.cone F).X

/-- The projection from the chosen limit object to a value of the functor. -/
def limit.π (F : J ⥤ C) [has_limit F] (j : J) : limit F ⟶ F.obj j :=
(limit.cone F).π.app j

@[simp] lemma limit.cone_π {F : J ⥤ C} [has_limit F] (j : J) :
  (limit.cone F).π.app j = limit.π _ j := rfl

@[simp] lemma limit.w (F : J ⥤ C) [has_limit F] {j j' : J} (f : j ⟶ j') :
  limit.π F j ≫ F.map f = limit.π F j' := (limit.cone F).w f

/-- Evidence that the chosen cone is a limit cone. -/
def limit.is_limit (F : J ⥤ C) [has_limit F] : is_limit (limit.cone F) :=
has_limit.is_limit

/-- The morphism from the cone point of any other cone to the chosen limit object. -/
def limit.lift (F : J ⥤ C) [has_limit F] (c : cone F) : c.X ⟶ limit F :=
(limit.is_limit F).lift c

@[simp] lemma limit.is_limit_lift {F : J ⥤ C} [has_limit F] (c : cone F) :
  (limit.is_limit F).lift c = limit.lift F c := rfl

@[simp, reassoc] lemma limit.lift_π {F : J ⥤ C} [has_limit F] (c : cone F) (j : J) :
  limit.lift F c ≫ limit.π F j = c.π.app j :=
is_limit.fac _ c j

/-- The cone morphism from any cone to the chosen limit cone. -/
def limit.cone_morphism {F : J ⥤ C} [has_limit F] (c : cone F) :
  c ⟶ (limit.cone F) :=
(limit.is_limit F).lift_cone_morphism c

@[simp] lemma limit.cone_morphism_hom {F : J ⥤ C} [has_limit F] (c : cone F) :
  (limit.cone_morphism c).hom = limit.lift F c := rfl
lemma limit.cone_morphism_π {F : J ⥤ C} [has_limit F] (c : cone F) (j : J) :
  (limit.cone_morphism c).hom ≫ limit.π F j = c.π.app j :=
by simp

@[ext] lemma limit.hom_ext {F : J ⥤ C} [has_limit F] {X : C} {f f' : X ⟶ limit F}
  (w : ∀ j, f ≫ limit.π F j = f' ≫ limit.π F j) : f = f' :=
(limit.is_limit F).hom_ext w

/--
The isomorphism (in `Type`) between
morphisms from a specified object `W` to the limit object,
and cones with cone point `W`.
-/
def limit.hom_iso (F : J ⥤ C) [has_limit F] (W : C) : (W ⟶ limit F) ≅ (F.cones.obj (op W)) :=
(limit.is_limit F).hom_iso W

@[simp] lemma limit.hom_iso_hom (F : J ⥤ C) [has_limit F] {W : C} (f : W ⟶ limit F) :
  (limit.hom_iso F W).hom f = (const J).map f ≫ (limit.cone F).π :=
(limit.is_limit F).hom_iso_hom f

/--
The isomorphism (in `Type`) between
morphisms from a specified object `W` to the limit object,
and an explicit componentwise description of cones with cone point `W`.
-/
def limit.hom_iso' (F : J ⥤ C) [has_limit F] (W : C) :
  ((W ⟶ limit F) : Type v) ≅ { p : Π j, W ⟶ F.obj j // ∀ {j j' : J} (f : j ⟶ j'), p j ≫ F.map f = p j' } :=
(limit.is_limit F).hom_iso' W

lemma limit.lift_extend {F : J ⥤ C} [has_limit F] (c : cone F) {X : C} (f : X ⟶ c.X) :
  limit.lift F (c.extend f) = f ≫ limit.lift F c :=
by obviously

/--
If we've chosen a limit for a functor `F`,
we can transport that choice across a natural isomorphism.
-/
def has_limit_of_iso {F G : J ⥤ C} [has_limit F] (α : F ≅ G) : has_limit G :=
{ cone := (cones.postcompose α.hom).obj (limit.cone F),
  is_limit :=
  { lift := λ s, limit.lift F ((cones.postcompose α.inv).obj s),
    fac' := λ s j,
    begin
      rw [cones.postcompose_obj_π, nat_trans.comp_app, limit.cone_π, ←category.assoc, limit.lift_π],
      simp
    end,
    uniq' := λ s m w,
    begin
      apply limit.hom_ext, intro j,
      rw [limit.lift_π, cones.postcompose_obj_π, nat_trans.comp_app, ←nat_iso.app_inv, iso.eq_comp_inv],
      simpa using w j
    end } }

/-- If a functor `G` has the same collection of cones as a functor `F`
which has a limit, then `G` also has a limit. -/
-- See the construction of limits from products and equalizers
-- for an example usage.
def has_limit.of_cones_iso {J K : Type v} [small_category J] [small_category K] (F : J ⥤ C) (G : K ⥤ C)
  (h : F.cones ≅ G.cones) [has_limit F] : has_limit G :=
⟨_, is_limit.of_nat_iso ((is_limit.nat_iso (limit.is_limit F)) ≪≫ h)⟩

/--
The chosen limits of `F : J ⥤ C` and `G : J ⥤ C` are isomorphic,
if the functors are naturally isomorphic.
-/
def has_limit.iso_of_nat_iso {F G : J ⥤ C} [has_limit F] [has_limit G] (w : F ≅ G) :
  limit F ≅ limit G :=
is_limit.cone_points_iso_of_nat_iso (limit.is_limit F) (limit.is_limit G) w

@[simp]
lemma has_limit.iso_of_nat_iso_hom_π {F G : J ⥤ C} [has_limit F] [has_limit G]
  (w : F ≅ G) (j : J) :
  (has_limit.iso_of_nat_iso w).hom ≫ limit.π G j = limit.π F j ≫ w.hom.app j :=
by simp [has_limit.iso_of_nat_iso, is_limit.cone_points_iso_of_nat_iso_hom]

/--
The chosen limits of `F : J ⥤ C` and `G : K ⥤ C` are isomorphic,
if there is an equivalence `e : J ≌ K` making the triangle commute up to natural isomorphism.
-/
def has_limit.iso_of_equivalence {F : J ⥤ C} [has_limit F] {G : K ⥤ C} [has_limit G]
   (e : J ≌ K) (w : e.functor ⋙ G ≅ F) : limit F ≅ limit G :=
is_limit.cone_points_iso_of_equivalence (limit.is_limit F) (limit.is_limit G) e w

@[simp]
lemma has_limit.iso_of_equivalence_π {F : J ⥤ C} [has_limit F] {G : K ⥤ C} [has_limit G]
   (e : J ≌ K) (w : e.functor ⋙ G ≅ F) (k : K) :
  (has_limit.iso_of_equivalence e w).hom ≫ limit.π G k =
    limit.π F (e.inverse.obj k) ≫ w.inv.app (e.inverse.obj k) ≫ G.map (e.counit.app k) :=
begin
  simp [has_limit.iso_of_equivalence, is_limit.cone_points_iso_of_equivalence_hom],
  dsimp,
  simp,
end

section pre
variables (F) [has_limit F] (E : K ⥤ J) [has_limit (E ⋙ F)]

/--
The canonical morphism
from the chosen limit of `F`
to the chosen limit of `E ⋙ F`.
-/
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
variables {D : Type u'} [category.{v} D]

variables (F) [has_limit F] (G : C ⥤ D) [has_limit (F ⋙ G)]

/--
The canonical morphism
from `G` applied to the chosen limit of `F`
to the chosen limit of `F ⋙ G`.
-/
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
  {E : Type u''} [category.{v} E] (H : D ⥤ E) [has_limit ((F ⋙ G) ⋙ H)] :
/- H G (limit F) ⟶ H (limit (F ⋙ G)) ⟶ limit ((F ⋙ G) ⋙ H) equals -/
/- H G (limit F) ⟶ limit (F ⋙ (G ⋙ H)) -/
  H.map (limit.post F G) ≫ limit.post (F ⋙ G) H = limit.post F (G ⋙ H) :=
by ext; erw [assoc, limit.post_π, ←H.map_comp, limit.post_π, limit.post_π]; refl

end post

lemma limit.pre_post {D : Type u'} [category.{v} D]
  (E : K ⥤ J) (F : J ⥤ C) (G : C ⥤ D)
  [has_limit F] [has_limit (E ⋙ F)] [has_limit (F ⋙ G)] [has_limit ((E ⋙ F) ⋙ G)] :
/- G (limit F) ⟶ G (limit (E ⋙ F)) ⟶ limit ((E ⋙ F) ⋙ G) vs -/
/- G (limit F) ⟶ limit F ⋙ G ⟶ limit (E ⋙ (F ⋙ G)) or -/
  G.map (limit.pre F E) ≫ limit.post (E ⋙ F) G = limit.post F G ≫ limit.pre (F ⋙ G) E :=
by ext; erw [assoc, limit.post_π, ←G.map_comp, limit.pre_π, assoc, limit.pre_π, limit.post_π]; refl

open category_theory.equivalence
instance has_limit_equivalence_comp (e : K ≌ J) [has_limit F] : has_limit (e.functor ⋙ F) :=
{ cone := cone.whisker e.functor (limit.cone F),
  is_limit := is_limit.whisker_equivalence (limit.is_limit F) e, }

local attribute [elab_simple] inv_fun_id_assoc -- not entirely sure why this is needed

/--
If a `E ⋙ F` has a chosen limit, and `E` is an equivalence, we can construct a chosen limit of `F`.
-/
def has_limit_of_equivalence_comp (e : K ≌ J) [has_limit (e.functor ⋙ F)] : has_limit F :=
begin
  haveI : has_limit (e.inverse ⋙ e.functor ⋙ F) := limits.has_limit_equivalence_comp e.symm,
  apply has_limit_of_iso (e.inv_fun_id_assoc F),
end

-- `has_limit_comp_equivalence` and `has_limit_of_comp_equivalence`
-- are proved in `category_theory/adjunction/limits.lean`.

section lim_functor

/--
Functoriality of limits.

Usually this morphism should be accessed through `lim.map`,
but may be needed separately when you have specified limits for the source and target functors,
but not necessarily for all functors of shape `J`.
-/
def lim_map {F G : J ⥤ C} [has_limit F] [has_limit G] (α : F ⟶ G) : limit F ⟶ limit G :=
limit.lift G
  { X := limit F,
    π :=
    { app := λ j, limit.π F j ≫ α.app j,
      naturality' := λ j j' f,
        by erw [id_comp, assoc, ←α.naturality, ←assoc, limit.w] } }

@[simp, reassoc] lemma lim_map_π {F G : J ⥤ C} [has_limit F] [has_limit G] (α : F ⟶ G) (j : J) :
  lim_map α ≫ limit.π G j = limit.π F j ≫ α.app j :=
by apply is_limit.fac

variables [has_limits_of_shape J C]

section
local attribute [simp] lim_map

/-- `limit F` is functorial in `F`, when `C` has all limits of shape `J`. -/
def lim : (J ⥤ C) ⥤ C :=
{ obj := λ F, limit F,
  map := λ F G α, lim_map α,
  map_comp' := λ F G H α β,
    by ext; erw [assoc, is_limit.fac, is_limit.fac, ←assoc, is_limit.fac, assoc]; refl }
end

variables {F} {G : J ⥤ C} (α : F ⟶ G)

@[simp, reassoc] lemma limit.map_π (j : J) : lim.map α ≫ limit.π G j = limit.π F j ≫ α.app j :=
by apply is_limit.fac

@[simp] lemma limit.lift_map (c : cone F) :
  limit.lift F c ≫ lim.map α = limit.lift G ((cones.postcompose α).obj c) :=
by ext; rw [assoc, limit.map_π, ←assoc, limit.lift_π, limit.lift_π]; refl

lemma limit.map_pre [has_limits_of_shape K C] (E : K ⥤ J) :
  lim.map α ≫ limit.pre G E = limit.pre F E ≫ lim.map (whisker_left E α) :=
by ext; rw [assoc, limit.pre_π, limit.map_π, assoc, limit.map_π, ←assoc, limit.pre_π]; refl

lemma limit.map_pre' [has_limits_of_shape K C]
  (F : J ⥤ C) {E₁ E₂ : K ⥤ J} (α : E₁ ⟶ E₂) :
  limit.pre F E₂ = limit.pre F E₁ ≫ lim.map (whisker_right α F) :=
by ext1; simp [← category.assoc]

lemma limit.id_pre (F : J ⥤ C) :
limit.pre F (𝟭 _) = lim.map (functor.left_unitor F).inv := by tidy

lemma limit.map_post {D : Type u'} [category.{v} D] [has_limits_of_shape J D] (H : C ⥤ D) :
/- H (limit F) ⟶ H (limit G) ⟶ limit (G ⋙ H) vs
   H (limit F) ⟶ limit (F ⋙ H) ⟶ limit (G ⋙ H) -/
  H.map (lim.map α) ≫ limit.post G H = limit.post F H ≫ lim.map (whisker_right α H) :=
begin
  ext,
  rw [assoc, limit.post_π, ←H.map_comp, limit.map_π, H.map_comp],
  rw [assoc, limit.map_π, ←assoc, limit.post_π],
  refl
end

/--
The isomorphism between
morphisms from `W` to the cone point of the limit cone for `F`
and cones over `F` with cone point `W`
is natural in `F`.
-/
def lim_yoneda : lim ⋙ yoneda ≅ category_theory.cones J C :=
nat_iso.of_components (λ F, nat_iso.of_components (λ W, limit.hom_iso F (unop W)) (by tidy))
  (by tidy)

end lim_functor

/--
We can transport chosen limits of shape `J` along an equivalence `J ≌ J'`.
-/
def has_limits_of_shape_of_equivalence {J' : Type v} [small_category J']
  (e : J ≌ J') [has_limits_of_shape J C] : has_limits_of_shape J' C :=
by { constructor, intro F, apply has_limit_of_equivalence_comp e, apply_instance }

end limit


section colimit

/-- `has_colimit F` represents a particular chosen colimit of the diagram `F`. -/
class has_colimit (F : J ⥤ C) :=
(cocone : cocone F)
(is_colimit : is_colimit cocone)

variables (J C)

/-- `C` has colimits of shape `J` if we have chosen a particular colimit of
  every functor `F : J ⥤ C`. -/
class has_colimits_of_shape :=
(has_colimit : Π F : J ⥤ C, has_colimit F)

/-- `C` has all (small) colimits if it has colimits of every shape. -/
class has_colimits :=
(has_colimits_of_shape : Π (J : Type v) [𝒥 : small_category J], has_colimits_of_shape J C)

variables {J C}

@[priority 100] -- see Note [lower instance priority]
instance has_colimit_of_has_colimits_of_shape
  {J : Type v} [small_category J] [H : has_colimits_of_shape J C] (F : J ⥤ C) : has_colimit F :=
has_colimits_of_shape.has_colimit F

@[priority 100] -- see Note [lower instance priority]
instance has_colimits_of_shape_of_has_colimits
  {J : Type v} [small_category J] [H : has_colimits C] : has_colimits_of_shape J C :=
has_colimits.has_colimits_of_shape J

/- Interface to the `has_colimit` class. -/

/-- The chosen colimit cocone of a functor. -/
def colimit.cocone (F : J ⥤ C) [has_colimit F] : cocone F := has_colimit.cocone

/-- The chosen colimit object of a functor. -/
def colimit (F : J ⥤ C) [has_colimit F] := (colimit.cocone F).X

/-- The coprojection from a value of the functor to the chosen colimit object. -/
def colimit.ι (F : J ⥤ C) [has_colimit F] (j : J) : F.obj j ⟶ colimit F :=
(colimit.cocone F).ι.app j

@[simp] lemma colimit.cocone_ι {F : J ⥤ C} [has_colimit F] (j : J) :
  (colimit.cocone F).ι.app j = colimit.ι _ j := rfl

@[simp] lemma colimit.w (F : J ⥤ C) [has_colimit F] {j j' : J} (f : j ⟶ j') :
  F.map f ≫ colimit.ι F j' = colimit.ι F j := (colimit.cocone F).w f

/-- Evidence that the chosen cocone is a colimit cocone. -/
def colimit.is_colimit (F : J ⥤ C) [has_colimit F] : is_colimit (colimit.cocone F) :=
has_colimit.is_colimit

/-- The morphism from the chosen colimit object to the cone point of any other cocone. -/
def colimit.desc (F : J ⥤ C) [has_colimit F] (c : cocone F) : colimit F ⟶ c.X :=
(colimit.is_colimit F).desc c

@[simp] lemma colimit.is_colimit_desc {F : J ⥤ C} [has_colimit F] (c : cocone F) :
  (colimit.is_colimit F).desc c = colimit.desc F c := rfl

/--
We have lots of lemmas describing how to simplify `colimit.ι F j ≫ _`,
and combined with `colimit.ext` we rely on these lemmas for many calculations.

However, since `category.assoc` is a `@[simp]` lemma, often expressions are
right associated, and it's hard to apply these lemmas about `colimit.ι`.

We thus use `reassoc` to define additional `@[simp]` lemmas, with an arbitrary extra morphism.
(see `tactic/reassoc_axiom.lean`)
 -/
@[simp, reassoc] lemma colimit.ι_desc {F : J ⥤ C} [has_colimit F] (c : cocone F) (j : J) :
  colimit.ι F j ≫ colimit.desc F c = c.ι.app j :=
is_colimit.fac _ c j

/-- The cocone morphism from the chosen colimit cocone to any cocone. -/
def colimit.cocone_morphism {F : J ⥤ C} [has_colimit F] (c : cocone F) :
  (colimit.cocone F) ⟶ c :=
(colimit.is_colimit F).desc_cocone_morphism c

@[simp] lemma colimit.cocone_morphism_hom {F : J ⥤ C} [has_colimit F] (c : cocone F) :
  (colimit.cocone_morphism c).hom = colimit.desc F c := rfl
lemma colimit.ι_cocone_morphism {F : J ⥤ C} [has_colimit F] (c : cocone F) (j : J) :
  colimit.ι F j ≫ (colimit.cocone_morphism c).hom = c.ι.app j :=
by simp

@[ext] lemma colimit.hom_ext {F : J ⥤ C} [has_colimit F] {X : C} {f f' : colimit F ⟶ X}
  (w : ∀ j, colimit.ι F j ≫ f = colimit.ι F j ≫ f') : f = f' :=
(colimit.is_colimit F).hom_ext w

/--
The isomorphism (in `Type`) between
morphisms from the colimit object to a specified object `W`,
and cocones with cone point `W`.
-/
def colimit.hom_iso (F : J ⥤ C) [has_colimit F] (W : C) : (colimit F ⟶ W) ≅ (F.cocones.obj W) :=
(colimit.is_colimit F).hom_iso W

@[simp] lemma colimit.hom_iso_hom (F : J ⥤ C) [has_colimit F] {W : C} (f : colimit F ⟶ W) :
  (colimit.hom_iso F W).hom f = (colimit.cocone F).ι ≫ (const J).map f :=
(colimit.is_colimit F).hom_iso_hom f

/--
The isomorphism (in `Type`) between
morphisms from the colimit object to a specified object `W`,
and an explicit componentwise description of cocones with cone point `W`.
-/
def colimit.hom_iso' (F : J ⥤ C) [has_colimit F] (W : C) :
  ((colimit F ⟶ W) : Type v) ≅ { p : Π j, F.obj j ⟶ W // ∀ {j j'} (f : j ⟶ j'), F.map f ≫ p j' = p j } :=
(colimit.is_colimit F).hom_iso' W

lemma colimit.desc_extend (F : J ⥤ C) [has_colimit F] (c : cocone F) {X : C} (f : c.X ⟶ X) :
  colimit.desc F (c.extend f) = colimit.desc F c ≫ f :=
begin
  ext1, rw [←category.assoc], simp
end

/--
If we've chosen a colimit for a functor `F`,
we can transport that choice across a natural isomorphism.
-/
-- This has the isomorphism pointing in the opposite direction than in `has_limit_of_iso`.
-- This is intentional; it seems to help with elaboration.
def has_colimit_of_iso {F G : J ⥤ C} [has_colimit F] (α : G ≅ F) : has_colimit G :=
{ cocone := (cocones.precompose α.hom).obj (colimit.cocone F),
  is_colimit :=
  { desc := λ s, colimit.desc F ((cocones.precompose α.inv).obj s),
    fac' := λ s j,
    begin
      rw [cocones.precompose_obj_ι, nat_trans.comp_app, colimit.cocone_ι],
      rw [category.assoc, colimit.ι_desc, ←nat_iso.app_hom, ←iso.eq_inv_comp], refl
    end,
    uniq' := λ s m w,
    begin
      apply colimit.hom_ext, intro j,
      rw [colimit.ι_desc, cocones.precompose_obj_ι, nat_trans.comp_app, ←nat_iso.app_inv,
        iso.eq_inv_comp],
      simpa using w j
    end } }

/-- If a functor `G` has the same collection of cocones as a functor `F`
which has a colimit, then `G` also has a colimit. -/
def has_colimit.of_cocones_iso {J K : Type v} [small_category J] [small_category K] (F : J ⥤ C) (G : K ⥤ C)
  (h : F.cocones ≅ G.cocones) [has_colimit F] : has_colimit G :=
⟨_, is_colimit.of_nat_iso ((is_colimit.nat_iso (colimit.is_colimit F)) ≪≫ h)⟩

/--
The chosen colimits of `F : J ⥤ C` and `G : J ⥤ C` are isomorphic,
if the functors are naturally isomorphic.
-/
def has_colimit.iso_of_nat_iso {F G : J ⥤ C} [has_colimit F] [has_colimit G] (w : F ≅ G) :
  colimit F ≅ colimit G :=
is_colimit.cocone_points_iso_of_nat_iso (colimit.is_colimit F) (colimit.is_colimit G) w

@[simp]
lemma has_colimit.iso_of_nat_iso_hom_π {F G : J ⥤ C} [has_colimit F] [has_colimit G]
  (w : F ≅ G) (j : J) :
  colimit.ι F j ≫ (has_colimit.iso_of_nat_iso w).hom = w.hom.app j ≫ colimit.ι G j :=
by simp [has_colimit.iso_of_nat_iso, is_colimit.cocone_points_iso_of_nat_iso_inv]

/--
The chosen colimits of `F : J ⥤ C` and `G : K ⥤ C` are isomorphic,
if there is an equivalence `e : J ≌ K` making the triangle commute up to natural isomorphism.
-/
def has_colimit.iso_of_equivalence {F : J ⥤ C} [has_colimit F] {G : K ⥤ C} [has_colimit G]
   (e : J ≌ K) (w : e.functor ⋙ G ≅ F) : colimit F ≅ colimit G :=
is_colimit.cocone_points_iso_of_equivalence (colimit.is_colimit F) (colimit.is_colimit G) e w

@[simp]
lemma has_colimit.iso_of_equivalence_π {F : J ⥤ C} [has_colimit F] {G : K ⥤ C} [has_colimit G]
   (e : J ≌ K) (w : e.functor ⋙ G ≅ F) (j : J) :
  colimit.ι F j ≫ (has_colimit.iso_of_equivalence e w).hom =
     F.map (e.unit.app j) ≫ w.inv.app _ ≫ colimit.ι G _ :=
begin
  simp [has_colimit.iso_of_equivalence, is_colimit.cocone_points_iso_of_equivalence_inv],
  dsimp,
  simp,
end

section pre
variables (F) [has_colimit F] (E : K ⥤ J) [has_colimit (E ⋙ F)]

/--
The canonical morphism
from the chosen colimit of `E ⋙ F`
to the chosen colimit of `F`.
-/
def colimit.pre : colimit (E ⋙ F) ⟶ colimit F :=
colimit.desc (E ⋙ F)
  { X := colimit F,
    ι := { app := λ k, colimit.ι F (E.obj k) } }

@[simp, reassoc] lemma colimit.ι_pre (k : K) : colimit.ι (E ⋙ F) k ≫ colimit.pre F E = colimit.ι F (E.obj k) :=
by erw is_colimit.fac

@[simp] lemma colimit.pre_desc (c : cocone F) :
  colimit.pre F E ≫ colimit.desc F c = colimit.desc (E ⋙ F) (c.whisker E) :=
by ext; rw [←assoc, colimit.ι_pre]; simp

variables {L : Type v} [small_category L]
variables (D : L ⥤ K) [has_colimit (D ⋙ E ⋙ F)]

@[simp] lemma colimit.pre_pre : colimit.pre (E ⋙ F) D ≫ colimit.pre F E = colimit.pre F (D ⋙ E) :=
begin
  ext j,
  rw [←assoc, colimit.ι_pre, colimit.ι_pre],
  letI : has_colimit ((D ⋙ E) ⋙ F) := show has_colimit (D ⋙ E ⋙ F), by apply_instance,
  exact (colimit.ι_pre F (D ⋙ E) j).symm
end

end pre

section post
variables {D : Type u'} [category.{v} D]

variables (F) [has_colimit F] (G : C ⥤ D) [has_colimit (F ⋙ G)]

/--
The canonical morphism
from `G` applied to the chosen colimit of `F ⋙ G`
to `G` applied to the chosen colimit of `F`.
-/
def colimit.post : colimit (F ⋙ G) ⟶ G.obj (colimit F) :=
colimit.desc (F ⋙ G)
{ X := G.obj (colimit F),
  ι :=
  { app := λ j, G.map (colimit.ι F j),
    naturality' :=
      by intros j j' f; erw [←G.map_comp, limits.cocone.w, comp_id]; refl } }

@[simp, reassoc] lemma colimit.ι_post (j : J) : colimit.ι (F ⋙ G) j ≫ colimit.post F G  = G.map (colimit.ι F j) :=
by erw is_colimit.fac

@[simp] lemma colimit.post_desc (c : cocone F) :
  colimit.post F G ≫ G.map (colimit.desc F c) = colimit.desc (F ⋙ G) (G.map_cocone c) :=
by ext; rw [←assoc, colimit.ι_post, ←G.map_comp, colimit.ι_desc, colimit.ι_desc]; refl

@[simp] lemma colimit.post_post
  {E : Type u''} [category.{v} E] (H : D ⥤ E) [has_colimit ((F ⋙ G) ⋙ H)] :
/- H G (colimit F) ⟶ H (colimit (F ⋙ G)) ⟶ colimit ((F ⋙ G) ⋙ H) equals -/
/- H G (colimit F) ⟶ colimit (F ⋙ (G ⋙ H)) -/
  colimit.post (F ⋙ G) H ≫ H.map (colimit.post F G) = colimit.post F (G ⋙ H) :=
begin
  ext,
  rw [←assoc, colimit.ι_post, ←H.map_comp, colimit.ι_post],
  exact (colimit.ι_post F (G ⋙ H) j).symm
end

end post

lemma colimit.pre_post {D : Type u'} [category.{v} D]
  (E : K ⥤ J) (F : J ⥤ C) (G : C ⥤ D)
  [has_colimit F] [has_colimit (E ⋙ F)] [has_colimit (F ⋙ G)] [has_colimit ((E ⋙ F) ⋙ G)] :
/- G (colimit F) ⟶ G (colimit (E ⋙ F)) ⟶ colimit ((E ⋙ F) ⋙ G) vs -/
/- G (colimit F) ⟶ colimit F ⋙ G ⟶ colimit (E ⋙ (F ⋙ G)) or -/
  colimit.post (E ⋙ F) G ≫ G.map (colimit.pre F E) = colimit.pre (F ⋙ G) E ≫ colimit.post F G :=
begin
  ext,
  rw [←assoc, colimit.ι_post, ←G.map_comp, colimit.ι_pre, ←assoc],
  letI : has_colimit (E ⋙ F ⋙ G) := show has_colimit ((E ⋙ F) ⋙ G), by apply_instance,
  erw [colimit.ι_pre (F ⋙ G) E j, colimit.ι_post]
end

open category_theory.equivalence
instance has_colimit_equivalence_comp (e : K ≌ J) [has_colimit F] : has_colimit (e.functor ⋙ F) :=
{ cocone := cocone.whisker e.functor (colimit.cocone F),
  is_colimit := is_colimit.whisker_equivalence (colimit.is_colimit F) e, }

/--
If a `E ⋙ F` has a chosen colimit, and `E` is an equivalence, we can construct a chosen colimit of `F`.
-/
def has_colimit_of_equivalence_comp (e : K ≌ J) [has_colimit (e.functor ⋙ F)] : has_colimit F :=
begin
  haveI : has_colimit (e.inverse ⋙ e.functor ⋙ F) := limits.has_colimit_equivalence_comp e.symm,
  apply has_colimit_of_iso (e.inv_fun_id_assoc F).symm,
end

section colim_functor

/--
Functoriality of colimits.

Usually this morphism should be accessed through `colim.map`,
but may be needed separately when you have specified colimits for the source and target functors,
but not necessarily for all functors of shape `J`.
-/
def colim_map {F G : J ⥤ C} [has_colimit F] [has_colimit G] (α : F ⟶ G) : colimit F ⟶ colimit G :=
colimit.desc F
  { X := colimit G,
    ι :=
    { app := λ j, α.app j ≫ colimit.ι G j,
      naturality' := λ j j' f,
        by erw [comp_id, ←assoc, α.naturality, assoc, colimit.w] } }

@[simp, reassoc]
lemma ι_colim_map {F G : J ⥤ C} [has_colimit F] [has_colimit G] (α : F ⟶ G) (j : J) :
  colimit.ι F j ≫ colim_map α = α.app j ≫ colimit.ι G j :=
by apply is_colimit.fac

variables [has_colimits_of_shape J C]

section
local attribute [simp] colim_map

/-- `colimit F` is functorial in `F`, when `C` has all colimits of shape `J`. -/
def colim : (J ⥤ C) ⥤ C :=
{ obj := λ F, colimit F,
  map := λ F G α, colim_map α,
  map_comp' := λ F G H α β,
    by ext; erw [←assoc, is_colimit.fac, is_colimit.fac, assoc, is_colimit.fac, ←assoc]; refl }

end

variables {F} {G : J ⥤ C} (α : F ⟶ G)

@[simp, reassoc] lemma colimit.ι_map (j : J) : colimit.ι F j ≫ colim.map α = α.app j ≫ colimit.ι G j :=
by apply is_colimit.fac

@[simp] lemma colimit.map_desc (c : cocone G) :
  colim.map α ≫ colimit.desc G c = colimit.desc F ((cocones.precompose α).obj c) :=
by ext; rw [←assoc, colimit.ι_map, assoc, colimit.ι_desc, colimit.ι_desc]; refl

lemma colimit.pre_map [has_colimits_of_shape K C] (E : K ⥤ J) :
  colimit.pre F E ≫ colim.map α = colim.map (whisker_left E α) ≫ colimit.pre G E :=
by ext; rw [←assoc, colimit.ι_pre, colimit.ι_map, ←assoc, colimit.ι_map, assoc, colimit.ι_pre]; refl

lemma colimit.pre_map' [has_colimits_of_shape K C]
  (F : J ⥤ C) {E₁ E₂ : K ⥤ J} (α : E₁ ⟶ E₂) :
  colimit.pre F E₁ = colim.map (whisker_right α F) ≫ colimit.pre F E₂ :=
by ext1; simp [← category.assoc]

lemma colimit.pre_id (F : J ⥤ C) :
colimit.pre F (𝟭 _) = colim.map (functor.left_unitor F).hom := by tidy

lemma colimit.map_post {D : Type u'} [category.{v} D] [has_colimits_of_shape J D] (H : C ⥤ D) :
/- H (colimit F) ⟶ H (colimit G) ⟶ colimit (G ⋙ H) vs
   H (colimit F) ⟶ colimit (F ⋙ H) ⟶ colimit (G ⋙ H) -/
  colimit.post F H ≫ H.map (colim.map α) = colim.map (whisker_right α H) ≫ colimit.post G H:=
begin
  ext,
  rw [←assoc, colimit.ι_post, ←H.map_comp, colimit.ι_map, H.map_comp],
  rw [←assoc, colimit.ι_map, assoc, colimit.ι_post],
  refl
end

/--
The isomorphism between
morphisms from the cone point of the chosen colimit cocone for `F` to `W`
and cocones over `F` with cone point `W`
is natural in `F`.
-/
def colim_coyoneda : colim.op ⋙ coyoneda ≅ category_theory.cocones J C :=
nat_iso.of_components (λ F, nat_iso.of_components (colimit.hom_iso (unop F)) (by tidy))
  (by tidy)

end colim_functor

/--
We can transport chosen colimits of shape `J` along an equivalence `J ≌ J'`.
-/
def has_colimits_of_shape_of_equivalence {J' : Type v} [small_category J']
  (e : J ≌ J') [has_colimits_of_shape J C] : has_colimits_of_shape J' C :=
by { constructor, intro F, apply has_colimit_of_equivalence_comp e, apply_instance }

end colimit

end category_theory.limits
