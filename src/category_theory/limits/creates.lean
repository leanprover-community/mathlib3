/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.limits.limits
import category_theory.limits.preserves
import category_theory.monad.adjunction
import category_theory.adjunction.limits
import category_theory.reflect_isomorphisms

open category_theory category_theory.limits

namespace category_theory

universes v u₁ u₂ u₃

variables {C : Type u₁} [𝒞 : category.{v} C]
include 𝒞

section creates
variables {D : Type u₂} [𝒟 : category.{v} D]
include 𝒟

variables {J : Type v} [small_category J] {K : J ⥤ C}

/--
Define the lift of a cone: For a cone `c` for `K ⋙ F`, give a cone for `K`
which is a lift of `c`, i.e. the image of it under `F` is (iso) to `c`.

We will then use this as part of the definition of creation of limits:
every limit cone has a lift.

Note this definition is really only useful when `c` is a limit already.
-/
structure liftable_cone (K : J ⥤ C) (F : C ⥤ D) (c : cone (K ⋙ F)) :=
(lifted_cone : cone K)
(valid_lift : F.map_cone lifted_cone ≅ c)

structure liftable_cocone (K : J ⥤ C) (F : C ⥤ D) (c : cocone (K ⋙ F)) :=
(lifted_cocone : cocone K)
(valid_lift : F.map_cocone lifted_cocone ≅ c)

/--
Definition 3.3.1 of [Riehl].
We say that `F` creates limits of `K` if, given any limit cone `c` for `K ⋙ F`
(i.e. below) we can lift it to a cone above, and further that `F` reflects
limits for `K`.

Note this is equivalent to Riehl's definition - the missing part here appears
to be that the lifted cone is not a limit, but the `extends reflects_limit K F`
is (proved in `lifted_limit_is_limit`).

If `F` reflects isomorphisms, it suffices to show only that the lifted cone is
a limit - see `creates_limit_of_reflects_iso`.
-/
class creates_limit (K : J ⥤ C) (F : C ⥤ D) extends reflects_limit K F : Type (max u₁ u₂ v) :=
(lifts : Π c, is_limit c → liftable_cone K F c)

class creates_limits_of_shape (J : Type v) [small_category J] (F : C ⥤ D) : Type (max u₁ u₂ v) :=
(creates_limit : Π {K : J ⥤ C}, creates_limit K F)

class creates_limits (F : C ⥤ D) : Type (max u₁ u₂ (v+1)) :=
(creates_limits_of_shape : Π {J : Type v} {𝒥 : small_category J}, by exactI creates_limits_of_shape J F)

class creates_colimit (K : J ⥤ C) (F : C ⥤ D) extends reflects_colimit K F : Type (max u₁ u₂ v) :=
(lifts : Π c, is_colimit c → liftable_cocone K F c)

class creates_colimits_of_shape (J : Type v) [small_category J] (F : C ⥤ D) : Type (max u₁ u₂ v) :=
(creates_colimit : Π {K : J ⥤ C}, creates_colimit K F)

class creates_colimits (F : C ⥤ D) : Type (max u₁ u₂ (v+1)) :=
(creates_colimits_of_shape : Π {J : Type v} {𝒥 : small_category J}, by exactI creates_colimits_of_shape J F)

def lift_limit {K : J ⥤ C} {F : C ⥤ D} [i : creates_limit K F] {c : cone (K ⋙ F)} (t : is_limit c) : cone K :=
(creates_limit.lifts c t).lifted_cone

def lifted_limit_maps_to_original {K : J ⥤ C} (F : C ⥤ D) [i : creates_limit K F] {c : cone (K ⋙ F)} (t : is_limit c) :
  F.map_cone (lift_limit t) ≅ c :=
(creates_limit.lifts c t).valid_lift

def lifted_limit_is_limit {K : J ⥤ C} {F : C ⥤ D} [i : creates_limit K F] {c : cone (K ⋙ F)} (t : is_limit c) :
  is_limit (lift_limit t) :=
reflects_limit.reflects (is_limit.of_iso_limit t (lifted_limit_maps_to_original F t).symm)

-- TODO: reflects iso is equivalent to reflecting limits of shape 1

def map_cone_equiv {F G : C ⥤ D} (h : F ≅ G) {c : cone K} (t : is_limit (F.map_cone c)) : is_limit (G.map_cone c) :=
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
    conv_rhs {congr, rw category.assoc, rw nat_iso.hom_inv_id_app},
    rw category.comp_id,
    erw t.fac ((cones.postcompose (iso_whisker_left K h).inv).obj s) j,
    refl
  end }

@[priority 100] -- see Note [lower instance priority]
instance is_equivalence_reflects_limits (H : D ⥤ C) [is_equivalence H] : reflects_limits H :=
{ reflects_limits_of_shape := λ J 𝒥, by exactI
  { reflects_limit := λ K,
    { reflects := λ c t,
      begin
        have l: is_limit (H.inv.map_cone (H.map_cone c)) := preserves_limit.preserves t,
        convert map_cone_equiv H.fun_inv_id l,
        rw functor.comp_id,
        cases c, cases c_π, dsimp [functor.map_cone, cones.functoriality],
        congr; rw functor.comp_id
      end } } }

/--
A helper to show a functor creates limits. In particular, if we can show
that for any limit cone `c` for `K ⋙ F`, there is a lift of it which is
a limit and `F` reflects isomorphisms, then `F` creates limits.
Usually, `F` creating limits says that _any_ lift of `c` is a limit, but
here we only need to show that our particular lift of `c` is a limit.
-/
structure lifts_to_limit (K : J ⥤ C) (F : C ⥤ D) (c : cone (K ⋙ F)) (t : is_limit c) :=
(lifted : liftable_cone K F c)
(makes_limit : is_limit lifted.lifted_cone)

/--
If `F` reflects isomorphisms and we can lift any limit cone to a limit cone,
then `F` creates limits.
-/
def creates_limit_of_reflects_iso {K : J ⥤ C} {F : C ⥤ D} [reflects_isomorphisms F]
  (h : Π c t, lifts_to_limit K F c t) :
  creates_limit K F :=
{ lifts := λ c t, (h c t).lifted,
  to_reflects_limit :=
  { reflects := λ (d : cone K) (hd : is_limit (F.map_cone d)),
    begin
      let d' : cone K := (h (F.map_cone d) hd).lifted.lifted_cone,
      let hd'₁ : F.map_cone d' ≅ F.map_cone d := (h (F.map_cone d) hd).lifted.valid_lift,
      let hd'₂ : is_limit d' := (h (F.map_cone d) hd).makes_limit,
      let f : d ⟶ d' := hd'₂.lift_cone_morphism d,
      have: F.map_cone_morphism f = hd'₁.inv := (hd.of_iso_limit hd'₁.symm).uniq_cone_morphism,
      have: @is_iso _ cone.category _ _ (functor.map_cone_morphism F f),
        rw this, apply_instance,
      haveI: is_iso ((cones.functoriality F).map f) := this,
      haveI := is_iso_of_reflects_iso f (cones.functoriality F),
      exact is_limit.of_iso_limit hd'₂ (as_iso f).symm,
    end } }

def map_cone_map_cone_inv (F : J ⥤ D) (H : D ⥤ C) [is_equivalence H] (c : cone (F ⋙ H)) :
  functor.map_cone H (functor.map_cone_inv H c) ≅ c :=
begin
  apply cones.ext _ (λ j, _),
  exact (functor.as_equivalence H).counit_iso.app c.X,
  dsimp [functor.map_cone_inv, functor.as_equivalence, functor.inv],
  erw category.comp_id,
  erw ← H.inv_fun_id.hom.naturality (c.π.app j),
  rw functor.comp_map, rw H.map_comp,
  congr' 1,
  rw ← cancel_epi (H.inv_fun_id.inv.app (H.obj (F.obj j))),
  erw nat_iso.inv_hom_id_app,
  erw ← (functor.as_equivalence H).functor_unit _,
  erw ← H.map_comp,
  erw nat_iso.hom_inv_id_app,
  rw H.map_id, refl
end

@[priority 100] -- see Note [lower instance priority]
instance is_equivalence_creates_limits (H : D ⥤ C) [is_equivalence H] : creates_limits H :=
{ creates_limits_of_shape := λ J 𝒥, by exactI
  { creates_limit := λ F,
    { lifts := λ c t,
      { lifted_cone := H.map_cone_inv c,
        valid_lift := map_cone_map_cone_inv F H c } } } }

section comp

variables {E : Type u₃} [ℰ : category.{v} E]
variables (F : C ⥤ D) (G : D ⥤ E)

instance comp_creates_limit [i₁ : creates_limit K F] [i₂ : creates_limit (K ⋙ F) G] :
  creates_limit K (F ⋙ G) :=
{ lifts := λ c t,
  { lifted_cone := lift_limit (lifted_limit_is_limit t),
    valid_lift := (cones.functoriality G).map_iso (lifted_limit_maps_to_original F (lifted_limit_is_limit t)) ≪≫ (lifted_limit_maps_to_original G t),
  } }

end comp

end creates

namespace monad

variables {T : C ⥤ C} [monad.{v} T]

namespace impl
variables {J : Type v} [𝒥 : small_category J]
include 𝒥

variables (D : J ⥤ algebra T) (c : cone (D ⋙ forget T)) (t : is_limit c)

@[simps] def γ : (D ⋙ forget T ⋙ T) ⟶ (D ⋙ forget T) := { app := λ j, (D.obj j).a }

@[simps] def new_cone : cone (D ⋙ forget T) :=
{ X := T.obj c.X,
  π := (functor.const_comp _ _ T).inv ≫ whisker_right c.π T ≫ (γ D) }

@[simps] def cone_point : algebra T :=
{ A := c.X,
  a := t.lift (new_cone D c),
  unit' :=
  begin
    apply t.hom_ext,
    intro j,
    rw [category.assoc], rw t.fac (new_cone D c),
    dsimp, rw category.id_comp, rw ← category.assoc,
    rw ← (η_ T).naturality, rw category.id_comp, rw functor.id_map,
    rw category.assoc, rw (D.obj j).unit, erw category.comp_id
  end,
  assoc' :=
  begin
    apply t.hom_ext,
    intro j,
    rw category.assoc,
    rw category.assoc,

    rw t.fac (new_cone D c),
    dsimp,
    erw [category.id_comp],
    slice_lhs 1 2 {rw ← (μ_ T).naturality},
    slice_lhs 2 3 {rw (D.obj j).assoc},
    slice_rhs 1 2 {rw ← T.map_comp},
    rw t.fac (new_cone D c),
    dsimp,
    erw category.id_comp,
    rw T.map_comp,
    simp
  end }

@[simps] def lifted_cone : cone D :=
{ X := cone_point D c t,
  π :=
  { app := λ j, { f := c.π.app j },
    naturality' := λ X Y f, by { ext1, dsimp, erw c.w f, simp } } }

@[simps]
def lifted_cone_is_limit : is_limit (lifted_cone D c t) :=
{ lift := λ s,
  { f := t.lift ((forget T).map_cone s),
    h' :=
    begin
      apply t.hom_ext, intro j,
      have := t.fac ((forget T).map_cone s),
      slice_rhs 2 3 {rw t.fac ((forget T).map_cone s) j},
      dsimp,
      slice_lhs 2 3 {rw t.fac (new_cone D c) j},
      dsimp,
      rw category.id_comp,
      slice_lhs 1 2 {rw ← T.map_comp},
      rw t.fac ((forget T).map_cone s) j,
      exact (s.π.app j).h
    end },
  uniq' := λ s m J,
  begin
    ext1,
    apply t.hom_ext,
    intro j,
    simpa [t.fac (functor.map_cone (forget T) s) j] using congr_arg algebra.hom.f (J j),
  end }

def lifted_cone_hits_original : (forget T).map_cone (lifted_cone D c t) = c :=
begin
  cases c,
  cases c_π,
  dsimp [functor.map_cone, cones.functoriality],
  congr
end

end impl

def forget_really_creates_limits : creates_limits (forget T) :=
{ creates_limits_of_shape := λ J 𝒥, by exactI
  { creates_limit := λ D,
    creates_limit_of_reflects_iso (λ c t,
    { lifted :=
      { lifted_cone := impl.lifted_cone D c t,
        valid_lift := eq_to_iso (impl.lifted_cone_hits_original _ _ _) },
      makes_limit := impl.lifted_cone_is_limit _ _ _} ) } }

end monad

end category_theory
