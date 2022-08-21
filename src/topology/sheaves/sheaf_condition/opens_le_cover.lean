/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import topology.sheaves.presheaf
import category_theory.limits.final
import topology.sheaves.sheaf_condition.pairwise_intersections

/-!
# Another version of the sheaf condition.

Given a family of open sets `U : ι → opens X` we can form the subcategory
`{ V : opens X // ∃ i, V ≤ U i }`, which has `supr U` as a cocone.

The sheaf condition on a presheaf `F` is equivalent to
`F` sending the opposite of this cocone to a limit cone in `C`, for every `U`.

This condition is particularly nice when checking the sheaf condition
because we don't need to do any case bashing
(depending on whether we're looking at single or double intersections,
or equivalently whether we're looking at the first or second object in an equalizer diagram).

## References
* This is the definition Lurie uses in [Spectral Algebraic Geometry][LurieSAG].
-/

universes v u

noncomputable theory

open category_theory
open category_theory.limits
open topological_space
open opposite
open topological_space.opens

namespace Top

variables {C : Type u} [category.{v} C]
variables {X : Top.{v}} (F : presheaf C X) {ι : Type v} (U : ι → opens X)

namespace presheaf

namespace sheaf_condition

/--
The category of open sets contained in some element of the cover.
-/
@[derive category]
def opens_le_cover : Type v := full_subcategory (λ (V : opens X), ∃ i, V ≤ U i)

instance [inhabited ι] : inhabited (opens_le_cover U) :=
⟨⟨⊥, default, bot_le⟩⟩

namespace opens_le_cover

variables {U}

/--
An arbitrarily chosen index such that `V ≤ U i`.
-/
def index (V : opens_le_cover U) : ι := V.property.some

/--
The morphism from `V` to `U i` for some `i`.
-/
def hom_to_index (V : opens_le_cover U) : V.obj ⟶ U (index V) :=
(V.property.some_spec).hom

end opens_le_cover

/--
`supr U` as a cocone over the opens sets contained in some element of the cover.

(In fact this is a colimit cocone.)
-/
def opens_le_cover_cocone : cocone (full_subcategory_inclusion _ : opens_le_cover U ⥤ opens X) :=
{ X := supr U,
  ι := { app := λ V : opens_le_cover U, V.hom_to_index ≫ opens.le_supr U _, } }

end sheaf_condition

open sheaf_condition

/--
An equivalent formulation of the sheaf condition
(which we prove equivalent to the usual one below as
`is_sheaf_iff_is_sheaf_opens_le_cover`).

A presheaf is a sheaf if `F` sends the cone `(opens_le_cover_cocone U).op` to a limit cone.
(Recall `opens_le_cover_cocone U`, has cone point `supr U`,
mapping down to any `V` which is contained in some `U i`.)
-/
def is_sheaf_opens_le_cover : Prop :=
∀ ⦃ι : Type v⦄ (U : ι → opens X), nonempty (is_limit (F.map_cone (opens_le_cover_cocone U).op))

namespace sheaf_condition

open category_theory.pairwise

/--
Implementation detail:
the object level of `pairwise_to_opens_le_cover : pairwise ι ⥤ opens_le_cover U`
-/
@[simp]
def pairwise_to_opens_le_cover_obj : pairwise ι → opens_le_cover U
| (single i) := ⟨U i, ⟨i, le_rfl⟩⟩
| (pair i j) := ⟨U i ⊓ U j, ⟨i, inf_le_left⟩⟩

open category_theory.pairwise.hom

/--
Implementation detail:
the morphism level of `pairwise_to_opens_le_cover : pairwise ι ⥤ opens_le_cover U`
-/
def pairwise_to_opens_le_cover_map :
  Π {V W : pairwise ι},
    (V ⟶ W) → (pairwise_to_opens_le_cover_obj U V ⟶ pairwise_to_opens_le_cover_obj U W)
| _ _ (id_single i) := 𝟙 _
| _ _ (id_pair i j) := 𝟙 _
| _ _ (left i j) := hom_of_le inf_le_left
| _ _ (right i j) := hom_of_le inf_le_right

/--
The category of single and double intersections of the `U i` maps into the category
of open sets below some `U i`.
-/
@[simps]
def pairwise_to_opens_le_cover : pairwise ι ⥤ opens_le_cover U :=
{ obj := pairwise_to_opens_le_cover_obj U,
  map := λ V W i, pairwise_to_opens_le_cover_map U i, }

instance (V : opens_le_cover U) :
  nonempty (structured_arrow V (pairwise_to_opens_le_cover U)) :=
⟨{ right := single (V.index), hom := V.hom_to_index }⟩

/--
The diagram consisting of the `U i` and `U i ⊓ U j` is cofinal in the diagram
of all opens contained in some `U i`.
-/
-- This is a case bash: for each pair of types of objects in `pairwise ι`,
-- we have to explicitly construct a zigzag.
instance : functor.final (pairwise_to_opens_le_cover U) :=
⟨λ V, is_connected_of_zigzag $ λ A B, begin
  rcases A with ⟨⟨⟨⟩⟩, ⟨i⟩|⟨i,j⟩, a⟩;
  rcases B with ⟨⟨⟨⟩⟩, ⟨i'⟩|⟨i',j'⟩, b⟩;
  dsimp at *,
  { refine ⟨[
    { left := ⟨⟨⟩⟩, right := pair i i',
      hom := (le_inf a.le b.le).hom, }, _], _, rfl⟩,
    exact
      list.chain.cons (or.inr ⟨{ left := 𝟙 _, right := left i i', }⟩)
        (list.chain.cons (or.inl ⟨{ left := 𝟙 _, right := right i i', }⟩) list.chain.nil) },
  { refine ⟨[
    { left := ⟨⟨⟩⟩, right := pair i' i,
      hom := (le_inf (b.le.trans inf_le_left) a.le).hom, },
    { left := ⟨⟨⟩⟩, right := single i',
      hom := (b.le.trans inf_le_left).hom, }, _], _, rfl⟩,
    exact
      list.chain.cons (or.inr ⟨{ left := 𝟙 _, right := right i' i, }⟩)
        (list.chain.cons (or.inl ⟨{ left := 𝟙 _, right := left i' i, }⟩)
          (list.chain.cons (or.inr ⟨{ left := 𝟙 _, right := left i' j', }⟩) list.chain.nil)) },
  { refine ⟨[
    { left := ⟨⟨⟩⟩, right := single i,
      hom := (a.le.trans inf_le_left).hom, },
    { left := ⟨⟨⟩⟩, right := pair i i', hom :=
      (le_inf (a.le.trans inf_le_left) b.le).hom, }, _], _, rfl⟩,
    exact
      list.chain.cons (or.inl ⟨{ left := 𝟙 _, right := left i j, }⟩)
        (list.chain.cons (or.inr ⟨{ left := 𝟙 _, right := left i i', }⟩)
          (list.chain.cons (or.inl ⟨{ left := 𝟙 _, right := right i i', }⟩) list.chain.nil)) },
  { refine ⟨[
    { left := ⟨⟨⟩⟩, right := single i,
      hom := (a.le.trans inf_le_left).hom, },
    { left := ⟨⟨⟩⟩, right := pair i i',
      hom := (le_inf (a.le.trans inf_le_left) (b.le.trans inf_le_left)).hom, },
    { left := ⟨⟨⟩⟩, right := single i',
      hom := (b.le.trans inf_le_left).hom, }, _], _, rfl⟩,
    exact
      list.chain.cons (or.inl ⟨{ left := 𝟙 _, right := left i j, }⟩)
      (list.chain.cons (or.inr ⟨{ left := 𝟙 _, right := left i i', }⟩)
      (list.chain.cons (or.inl ⟨{ left := 𝟙 _, right := right i i', }⟩)
      (list.chain.cons (or.inr ⟨{ left := 𝟙 _, right := left i' j', }⟩) list.chain.nil))), },
end⟩

/--
The diagram in `opens X` indexed by pairwise intersections from `U` is isomorphic
(in fact, equal) to the diagram factored through `opens_le_cover U`.
-/
def pairwise_diagram_iso :
  pairwise.diagram U ≅
  pairwise_to_opens_le_cover U ⋙ full_subcategory_inclusion _ :=
{ hom := { app := begin rintro (i|⟨i,j⟩); exact 𝟙 _, end, },
  inv := { app := begin rintro (i|⟨i,j⟩); exact 𝟙 _, end, }, }

/--
The cocone `pairwise.cocone U` with cocone point `supr U` over `pairwise.diagram U` is isomorphic
to the cocone `opens_le_cover_cocone U` (with the same cocone point)
after appropriate whiskering and postcomposition.
-/
def pairwise_cocone_iso :
  (pairwise.cocone U).op ≅
  (cones.postcompose_equivalence (nat_iso.op (pairwise_diagram_iso U : _) : _)).functor.obj
    ((opens_le_cover_cocone U).op.whisker (pairwise_to_opens_le_cover U).op) :=
cones.ext (iso.refl _) (by tidy)

end sheaf_condition

open sheaf_condition

/--
The sheaf condition
in terms of a limit diagram over all `{ V : opens X // ∃ i, V ≤ U i }`
is equivalent to the reformulation
in terms of a limit diagram over `U i` and `U i ⊓ U j`.
-/
lemma is_sheaf_opens_le_cover_iff_is_sheaf_pairwise_intersections (F : presheaf C X) :
  F.is_sheaf_opens_le_cover ↔ F.is_sheaf_pairwise_intersections :=
forall₂_congr $ λ ι U, equiv.nonempty_congr $
  calc is_limit (F.map_cone (opens_le_cover_cocone U).op)
    ≃ is_limit ((F.map_cone (opens_le_cover_cocone U).op).whisker (pairwise_to_opens_le_cover U).op)
        : (functor.initial.is_limit_whisker_equiv (pairwise_to_opens_le_cover U).op _).symm
... ≃ is_limit (F.map_cone ((opens_le_cover_cocone U).op.whisker (pairwise_to_opens_le_cover U).op))
        : is_limit.equiv_iso_limit F.map_cone_whisker.symm
... ≃ is_limit ((cones.postcompose_equivalence _).functor.obj
          (F.map_cone ((opens_le_cover_cocone U).op.whisker (pairwise_to_opens_le_cover U).op)))
        : (is_limit.postcompose_hom_equiv _ _).symm
... ≃ is_limit (F.map_cone ((cones.postcompose_equivalence _).functor.obj
          ((opens_le_cover_cocone U).op.whisker (pairwise_to_opens_le_cover U).op)))
        : is_limit.equiv_iso_limit (functor.map_cone_postcompose_equivalence_functor _).symm
... ≃ is_limit (F.map_cone (pairwise.cocone U).op)
        : is_limit.equiv_iso_limit
            ((cones.functoriality _ _).map_iso (pairwise_cocone_iso U : _).symm)

section

variables {Y : opens X} (hY : Y = supr U)

/-- Given a family of opens `U` and an open `Y` equal to the union of opens in `U`, we may
    take the presieve on `Y` associated to `U` and the sieve generated by it, and form the
    full subcategory (subposet) of opens contained in `Y` (`over Y`) consisting of arrows
    in the sieve. This full subcategory is equivalent to `opens_le_cover U`, the (poset)
    category of opens contained in some `U i`. -/
@[simps] def generate_equivalence_opens_le :
  full_subcategory (λ (f : over Y), (sieve.generate (presieve_of_covering_aux U Y)).arrows f.hom) ≌
  opens_le_cover U :=
{ functor :=
  { obj := λ f, ⟨f.1.left, let ⟨_,h,_,⟨i,hY⟩,_⟩ := f.2 in ⟨i, hY ▸ h.le⟩⟩,
    map := λ _ _ g, g.left },
  inverse :=
  { obj := λ V, ⟨over.mk (hY.substr (let ⟨i,h⟩ := V.2 in h.trans (le_supr U i))).hom,
      let ⟨i,h⟩ := V.2 in ⟨U i, h.hom, (hY.substr (le_supr U i)).hom, ⟨i, rfl⟩, rfl⟩⟩,
    map := λ _ _ g, over.hom_mk g },
  unit_iso := eq_to_iso $ category_theory.functor.ext
    (by {rintro ⟨⟨_,_⟩,_⟩, dsimp, congr; ext}) (by {intros, ext}),
  counit_iso := eq_to_iso $ category_theory.functor.hext
    (by {intro, ext, refl}) (by {intros, refl}) }

/-- Given a family of opens `opens_le_cover_cocone U` is essentially the natural cocone
    associated to the sieve generated by the presieve associated to `U` with indexing
    category changed using the above equivalence. -/
@[simps] def whisker_iso_map_generate_cocone :
  cone.whisker (generate_equivalence_opens_le U hY).op.functor
    (F.map_cone (opens_le_cover_cocone U).op) ≅
  F.map_cone (sieve.generate (presieve_of_covering_aux U Y)).arrows.cocone.op :=
{ hom :=
  { hom := F.map (eq_to_hom (congr_arg op hY.symm)),
    w' := λ j, by { erw ← F.map_comp, congr } },
  inv :=
  { hom := F.map (eq_to_hom (congr_arg op hY)),
    w' := λ j, by { erw ← F.map_comp, congr } },
  hom_inv_id' := by { ext, simp [eq_to_hom_map], },
  inv_hom_id' := by { ext, simp [eq_to_hom_map], } }

/-- Given a presheaf `F` on the topological space `X` and a family of opens `U` of `X`,
    the natural cone associated to `F` and `U` used in the definition of
    `F.is_sheaf_opens_le_cover` is a limit cone iff the natural cone associated to `F`
    and the sieve generated by the presieve associated to `U` is a limit cone. -/
def is_limit_opens_le_equiv_generate₁ :
  is_limit (F.map_cone (opens_le_cover_cocone U).op) ≃
  is_limit (F.map_cone (sieve.generate (presieve_of_covering_aux U Y)).arrows.cocone.op) :=
(is_limit.whisker_equivalence_equiv (generate_equivalence_opens_le U hY).op).trans
  (is_limit.equiv_iso_limit (whisker_iso_map_generate_cocone F U hY))

/-- Given a presheaf `F` on the topological space `X` and a presieve `R` whose generated sieve
    is covering for the associated Grothendieck topology (equivalently, the presieve is covering
    for the associated pretopology), the natural cone associated to `F` and the family of opens
    associated to `R` is a limit cone iff the natural cone associated to `F` and the generated
    sieve is a limit cone.
    Since only the existence of a 1-1 correspondence will be used, the exact definition does
    not matter, so tactics are used liberally. -/
def is_limit_opens_le_equiv_generate₂ (R : presieve Y)
  (hR : sieve.generate R ∈ opens.grothendieck_topology X Y) :
  is_limit (F.map_cone (opens_le_cover_cocone (covering_of_presieve Y R)).op) ≃
  is_limit (F.map_cone (sieve.generate R).arrows.cocone.op) :=
begin
  convert is_limit_opens_le_equiv_generate₁ F (covering_of_presieve Y R)
    (covering_of_presieve.supr_eq_of_mem_grothendieck Y R hR).symm using 2;
  rw covering_presieve_eq_self R,
end

/-- A presheaf `(opens X)ᵒᵖ ⥤ C` on a topological space `X` is a sheaf on the site `opens X` iff
    it satisfies the `is_sheaf_opens_le_cover` sheaf condition. The latter is not the
    official definition of sheaves on spaces, but has the advantage that it does not
    require `has_products C`. -/
lemma is_sheaf_iff_is_sheaf_opens_le_cover :
  F.is_sheaf ↔ F.is_sheaf_opens_le_cover :=
begin
  refine (presheaf.is_sheaf_iff_is_limit _ _).trans _,
  split,
  { intros h ι U, rw (is_limit_opens_le_equiv_generate₁ F U rfl).nonempty_congr,
    apply h, apply presieve_of_covering.mem_grothendieck_topology },
  { intros h Y S, rw ← sieve.generate_sieve S, intro hS,
    rw ← (is_limit_opens_le_equiv_generate₂ F S hS).nonempty_congr, apply h },
end

end

end presheaf

end Top
