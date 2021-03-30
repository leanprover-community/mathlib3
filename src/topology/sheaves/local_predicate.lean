/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison, Adam Topaz
-/
import topology.sheaves.sheaf_of_functions
import topology.sheaves.stalks

/-!
# Functions satisfying a local predicate form a sheaf.

At this stage, in `topology/sheaves/sheaf_of_functions.lean`
we've proved that not-necessarily-continuous functions from a topological space
into some type (or type family) form a sheaf.

Why do the continuous functions form a sheaf?
The point is just that continuity is a local condition,
so one can use the lifting condition for functions to provide a candidate lift,
then verify that the lift is actually continuous by using the factorisation condition for the lift
(which guarantees that on each open set it agrees with the functions being lifted,
which were assumed to be continuous).

This file abstracts this argument to work for
any collection of dependent functions on a topological space
satisfying a "local predicate".

As an application, we check that continuity is a local predicate in this sense, and provide
* `Top.sheaf_condition.to_Top`: continuous functions into a topological space form a sheaf

A sheaf constructed in this way has a natural map `stalk_to_fiber` from the stalks
to the types in the ambient type family.

We give conditions sufficient to show that this map is injective and/or surjective.
-/

universe v

noncomputable theory

variables {X : Top.{v}}
variables (T : X → Type v)

open topological_space
open opposite
open category_theory
open category_theory.limits
open category_theory.limits.types

namespace Top

/--
Given a topological space `X : Top` and a type family `T : X → Type`,
a `P : prelocal_predicate T` consists of:
* a family of predicates `P.pred`, one for each `U : opens X`, of the form `(Π x : U, T x) → Prop`
* a proof that if `f : Π x : V, T x` satisfies the predicate on `V : opens X`, then
  the restriction of `f` to any open subset `U` also satisfies the predicate.
-/
structure prelocal_predicate :=
(pred : Π {U : opens X}, (Π x : U, T x) → Prop)
(res : ∀ {U V : opens X} (i : U ⟶ V) (f : Π x : V, T x) (h : pred f), pred (λ x : U, f (i x)))

variables (X)
/--
Continuity is a "prelocal" predicate on functions to a fixed topological space `T`.
-/
@[simps]
def continuous_prelocal (T : Top.{v}) : prelocal_predicate (λ x : X, T) :=
{ pred := λ U f, continuous f,
  res := λ U V i f h, continuous.comp h (opens.open_embedding_of_le (le_of_hom i)).continuous, }

/-- Satisfying the inhabited linter. -/
instance inhabited_prelocal_predicate (T : Top.{v}) : inhabited (prelocal_predicate (λ x : X, T)) :=
⟨continuous_prelocal X T⟩

variables {X}

/--
Given a topological space `X : Top` and a type family `T : X → Type`,
a `P : local_predicate T` consists of:
* a family of predicates `P.pred`, one for each `U : opens X`, of the form `(Π x : U, T x) → Prop`
* a proof that if `f : Π x : V, T x` satisfies the predicate on `V : opens X`, then
  the restriction of `f` to any open subset `U` also satisfies the predicate, and
* a proof that given some `f : Π x : U, T x`,
  if for every `x : U` we can find an open set `x ∈ V ≤ U`
  so that the restriction of `f` to `V` satisfies the predicate,
  then `f` itself satisfies the predicate.
-/
structure local_predicate extends prelocal_predicate T :=
(locality : ∀ {U : opens X} (f : Π x : U, T x)
  (w : ∀ x : U, ∃ (V : opens X) (m : x.1 ∈ V) (i : V ⟶ U), pred (λ x : V, f (i x : U))), pred f)

variables (X)

/--
Continuity is a "local" predicate on functions to a fixed topological space `T`.
-/
def continuous_local (T : Top.{v}) : local_predicate (λ x : X, T) :=
{ locality := λ U f w,
   begin
     apply continuous_iff_continuous_at.2,
     intro x,
     specialize w x,
     rcases w with ⟨V, m, i, w⟩,
     dsimp at w,
     rw continuous_iff_continuous_at at w,
     specialize w ⟨x, m⟩,
     simpa using (opens.open_embedding_of_le (le_of_hom i)).continuous_at_iff.1 w,
   end,
  ..continuous_prelocal X T }

/-- Satisfying the inhabited linter. -/
instance inhabited_local_predicate (T : Top.{v}) : inhabited (local_predicate _) :=
⟨continuous_local X T⟩

variables {X T}

/--
Given a `P : prelocal_predicate`, we can always construct a `local_predicate`
by asking that the condition from `P` holds locally near every point.
-/
def prelocal_predicate.sheafify {T : X → Type v} (P : prelocal_predicate T) : local_predicate T :=
{ pred := λ U f, ∀ x : U, ∃ (V : opens X) (m : x.1 ∈ V) (i : V ⟶ U), P.pred (λ x : V, f (i x : U)),
  res := λ V U i f w x,
  begin
    specialize w (i x),
    rcases w with ⟨V', m', i', p⟩,
    refine ⟨V ⊓ V', ⟨x.2,m'⟩, opens.inf_le_left _ _, _⟩,
    convert P.res (opens.inf_le_right V V') _ p,
  end,
  locality := λ U f w x,
  begin
    specialize w x,
    rcases w with ⟨V, m, i, p⟩,
    specialize p ⟨x.1, m⟩,
    rcases p with ⟨V', m', i', p'⟩,
    exact ⟨V', m', i' ≫ i, p'⟩,
  end }

lemma prelocal_predicate.sheafify_of {T : X → Type v} {P : prelocal_predicate T}
  {U : opens X} {f : Π x : U, T x} (h : P.pred f) :
  P.sheafify.pred f :=
λ x, ⟨U, x.2, 𝟙 _, by { convert h, ext ⟨y, w⟩, refl, }⟩

/--
The subpresheaf of dependent functions on `X` satisfying the "pre-local" predicate `P`.
-/
@[simps]
def subpresheaf_to_Types (P : prelocal_predicate T) : presheaf (Type v) X :=
{ obj := λ U, { f : Π x : unop U, T x // P.pred f },
  map := λ U V i f, ⟨λ x, f.1 (i.unop x), P.res i.unop f.1 f.2⟩ }.

namespace subpresheaf_to_Types

variables (P : prelocal_predicate T)

/--
The natural transformation including the subpresheaf of functions satisfying a local predicate
into the presheaf of all functions.
-/
def subtype : subpresheaf_to_Types P ⟶ presheaf_to_Types X T :=
{ app := λ U f, f.1 }

open Top.presheaf
open Top.presheaf.sheaf_condition_equalizer_products

/--
The natural transformation
from the sheaf condition diagram for functions satisfying a local predicate
to the sheaf condition diagram for arbitrary functions,
given by forgetting that the local predicate holds.
-/
@[simps]
def diagram_subtype {ι : Type v} (U : ι → opens X) :
  diagram (subpresheaf_to_Types P) U ⟶ diagram (presheaf_to_Types X T) U :=
{ app := λ j, walking_parallel_pair.rec_on j (pi.map (λ i f, f.1)) (pi.map (λ p f, f.1)),
  naturality' :=
  begin
    rintro ⟨_|_⟩ ⟨_|_⟩ ⟨⟩,
    { refl, },
    { dsimp [left_res, subpresheaf_to_Types, presheaf_to_Types],
      rw [limit.lift_map],
      ext1 ⟨i₁,i₂⟩,
      rw [category.assoc, limit.lift_π, limit.lift_π, cones.postcompose_obj_π,
        nat_trans.comp_app, fan.mk_π_app, fan.mk_π_app,
        discrete.nat_trans_app, lim_map_π_assoc, discrete.nat_trans_app],
      ext,
      rw [types_comp_apply, types_comp_apply, types_comp_apply, types_comp_apply],
      refl, },
    { dsimp [right_res, subpresheaf_to_Types, presheaf_to_Types],
      rw [limit.lift_map],
      ext1 ⟨i₁,i₂⟩,
      rw [category.assoc, limit.lift_π, limit.lift_π, cones.postcompose_obj_π,
        nat_trans.comp_app, fan.mk_π_app, fan.mk_π_app,
        discrete.nat_trans_app, lim_map_π_assoc, discrete.nat_trans_app],
      ext,
      rw [types_comp_apply, types_comp_apply, types_comp_apply, types_comp_apply],
      refl, },
    { refl, },
  end}.

-- auxilliary lemma for `sheaf_condition` below
lemma sheaf_condition_fac
  {P : local_predicate T} {ι : Type v} {U : ι → opens X}
  {s : fork (left_res (subpresheaf_to_Types P.to_prelocal_predicate) U)
         (right_res (subpresheaf_to_Types P.to_prelocal_predicate) U)}
  (i : ι) (f : s.X) (h) :
  limit.π (discrete.functor (λ i, { f //  P.pred f })) i
    (res (subpresheaf_to_Types P.to_prelocal_predicate) U
      ⟨(to_Types X T U).lift ((cones.postcompose (diagram_subtype _ U)).obj s) f, h⟩) =
    limit.π (discrete.functor (λ i, { f //  P.pred f })) i (s.ι f) :=
begin
  apply subtype.coe_injective,
  convert congr_fun
    ((to_Types X T U).fac
      ((cones.postcompose (diagram_subtype P.to_prelocal_predicate U)).obj s)
      walking_parallel_pair.zero =≫
    pi.π (λ i, (X.presheaf_to_Types T).obj (op (U i))) i) f,
  { dsimp [res, presheaf_to_Types, subpresheaf_to_Types],
    simp only [pi_lift_π_apply, fan.mk_π_app, subtype.coe_mk, limit.lift_π_apply], },
  { dsimp,
    simp only [pi_map_π_apply, subtype.val_eq_coe], },
end

-- auxilliary lemma for `sheaf_condition` below
lemma sheaf_condition_uniq
  {P : local_predicate T} {ι : Type v} {U : ι → opens X}
  {s : fork (left_res (subpresheaf_to_Types P.to_prelocal_predicate) U)
         (right_res (subpresheaf_to_Types P.to_prelocal_predicate) U)}
  (m : s.X ⟶ (fork (subpresheaf_to_Types P.to_prelocal_predicate) U).X)
  (w : ∀ (j : walking_parallel_pair),
         m ≫ (fork (subpresheaf_to_Types P.to_prelocal_predicate) U).π.app j = s.π.app j)
  (f : s.X) (h) :
  m f = ⟨(to_Types X T U).lift ((cones.postcompose (diagram_subtype _ U)).obj s) f, h⟩ :=
begin
  apply subtype.coe_injective,
  let s' := (cones.postcompose (diagram_subtype P.to_prelocal_predicate U)).obj s,
  refine congr_fun ((to_Types X T U).uniq s' _ _) f,
  -- We "just" need to fix up our `w` to match the missing `w` argument.
  -- Unfortunately, it's still gross.
  intro j,
  specialize w j,
  dsimp [s'],
  rw ←w, clear w,
  simp only [category.assoc],
  rcases j with ⟨_|_⟩,
  { apply limit.hom_ext,
    intro i,
    simp only [category.assoc, lim_map_π],
    ext f' ⟨x, mem⟩,
    dsimp [res, subpresheaf_to_Types, presheaf_to_Types],
    simp only [discrete.nat_trans_app, limit.map_π_apply, fan.mk_π_app, limit.lift_π_apply], },
  { apply limit.hom_ext,
    intro i,
    simp only [category.assoc, lim_map_π],
    ext f' ⟨x, mem⟩,
    dsimp [res, left_res, subpresheaf_to_Types, presheaf_to_Types],
    simp only [discrete.nat_trans_app, limit.map_π_apply, pi_lift_π_apply, types_comp_apply,
      fan.mk_π_app, subtype.coe_mk, limit.lift_π_apply], },
end

/--
The functions satisfying a local predicate satisfy the sheaf condition.
-/
def sheaf_condition
  (P : local_predicate T) :
  sheaf_condition (subpresheaf_to_Types P.to_prelocal_predicate) :=
λ ι U,
begin
  refine fork.is_limit.mk _ _ _ _,
  { intros s f,
    fsplit,
    -- First, we use the fact that not necessarily continuous functions form a sheaf,
    -- to provide the lift.
    { let s' := (cones.postcompose (diagram_subtype P.to_prelocal_predicate U)).obj s,
      exact (to_Types X T U).lift s' f, },
    -- Second, we need to do the actual work, proving this lift satisfies the predicate.
    { dsimp,
      -- We work locally,
      apply P.locality,
      -- so that once we're at a particular point `x`, we can select some open set `x ∈ U i`.
      rintro ⟨x, mem⟩,
      change x ∈ (supr U).val at mem,
      simp at mem,
      choose i hi using mem,
      use U i,
      use hi,
      use (opens.le_supr U i),
      -- Now our goal is to show that the previously chosen lift,
      -- when restricted to that `U i`, satisfies the predicate.
      -- This follows from the factorisation condition, and
      -- the fact that the underlying presheaf is a presheaf of functions satisfying the predicate.
      let s' := (cones.postcompose (diagram_subtype P.to_prelocal_predicate U)).obj s,
      have fac_i := ((to_Types X T U).fac s' walking_parallel_pair.zero) =≫ pi.π _ i,
      simp only [sheaf_condition_equalizer_products.res, limit.lift_π, cones.postcompose_obj_π,
        sheaf_condition_equalizer_products.fork_π_app_walking_parallel_pair_zero, fan.mk_π_app,
        nat_trans.comp_app, category.assoc] at fac_i,
      have fac_i_f := congr_fun fac_i f,
      simp only [diagram_subtype, discrete.nat_trans_app, types_comp_apply,
        presheaf_to_Types_map, lim_map_π, subtype.val_eq_coe] at fac_i_f,
      erw fac_i_f,
      apply subtype.property, }, },
  { -- Proving the factorisation condition is straightforward:
    -- we observe that checking equality of functions satisfying a predicate reduces to
    -- checking equality of the underlying functions,
    -- and use the factorisation condition for the sheaf condition for functions.
    intros s,
    ext i f : 2,
    apply sheaf_condition_fac, },
  { -- Similarly for proving the uniqueness condition, after a certain amount of bookkeeping.
    intros s m w,
    ext f : 1,
    apply sheaf_condition_uniq m w, },
end

end subpresheaf_to_Types

/--
The subsheaf of the sheaf of all dependently typed functions satisfying the local predicate `P`.
-/
@[simps]
def subsheaf_to_Types (P : local_predicate T) : sheaf (Type v) X :=
{ presheaf := subpresheaf_to_Types P.to_prelocal_predicate,
  sheaf_condition := subpresheaf_to_Types.sheaf_condition P }.

/--
There is a canonical map from the stalk to the original fiber, given by evaluating sections.
-/
def stalk_to_fiber (P : local_predicate T) (x : X) :
  (subsheaf_to_Types P).presheaf.stalk x ⟶ T x :=
begin
  refine colimit.desc _
    { X := T x, ι := { app := λ U f, _, naturality' := _ } },
  { exact f.1 ⟨x, (unop U).2⟩, },
  { tidy, }
end

@[simp] lemma stalk_to_fiber_germ (P : local_predicate T) (U : opens X) (x : U) (f) :
  stalk_to_fiber P x ((subsheaf_to_Types P).presheaf.germ x f) = f.1 x :=
begin
  dsimp [presheaf.germ, stalk_to_fiber],
  cases x,
  simp,
  refl,
end

/--
The `stalk_to_fiber` map is surjective at `x` if
every point in the fiber `T x` has an allowed section passing through it.
-/
lemma stalk_to_fiber_surjective (P : local_predicate T) (x : X)
  (w : ∀ (t : T x), ∃ (U : open_nhds x) (f : Π y : U.1, T y) (h : P.pred f), f ⟨x, U.2⟩ = t) :
  function.surjective (stalk_to_fiber P x) :=
λ t,
begin
  rcases w t with ⟨U, f, h, rfl⟩,
  fsplit,
  { exact (subsheaf_to_Types P).presheaf.germ ⟨x, U.2⟩ ⟨f, h⟩, },
  { exact stalk_to_fiber_germ _ U.1 ⟨x, U.2⟩ ⟨f, h⟩, }
end

/--
The `stalk_to_fiber` map is injective at `x` if any two allowed sections which agree at `x`
agree on some neighborhood of `x`.
-/
lemma stalk_to_fiber_injective (P : local_predicate T) (x : X)
  (w : ∀ (U V : open_nhds x) (fU : Π y : U.1, T y) (hU : P.pred fU)
    (fV : Π y : V.1, T y) (hV : P.pred fV) (e : fU ⟨x, U.2⟩ = fV ⟨x, V.2⟩),
    ∃ (W : open_nhds x) (iU : W ⟶ U) (iV : W ⟶ V), ∀ (w : W.1), fU (iU w : U.1) = fV (iV w : V.1)) :
  function.injective (stalk_to_fiber P x) :=
λ tU tV h,
begin
  -- We promise to provide all the ingredients of the proof later:
  let Q :
    ∃ (W : (open_nhds x)ᵒᵖ) (s : Π w : (unop W).1, T w) (hW : P.pred s),
      tU = (subsheaf_to_Types P).presheaf.germ ⟨x, (unop W).2⟩ ⟨s, hW⟩ ∧
      tV = (subsheaf_to_Types P).presheaf.germ ⟨x, (unop W).2⟩ ⟨s, hW⟩ := _,
  { choose W s hW e using Q,
    exact e.1.trans e.2.symm, },
  -- Then use induction to pick particular representatives of `tU tV : stalk x`
  obtain ⟨U, ⟨fU, hU⟩, rfl⟩ := jointly_surjective' tU,
  obtain ⟨V, ⟨fV, hV⟩, rfl⟩ := jointly_surjective' tV,
  { -- Decompose everything into its constituent parts:
    dsimp,
    simp only [stalk_to_fiber, colimit.ι_desc_apply] at h,
    specialize w (unop U) (unop V) fU hU fV hV h,
    rcases w with ⟨W, iU, iV, w⟩,
    -- and put it back together again in the correct order.
    refine ⟨(op W), (λ w, fU (iU w : (unop U).1)), P.res _ _ hU, _⟩,
    rcases W with ⟨W, m⟩,
    exact ⟨colimit_sound iU.op (subtype.eq rfl),
           colimit_sound iV.op (subtype.eq (funext w).symm)⟩, },
end

/--
Some repackaging:
the presheaf of functions satisfying `continuous_prelocal` is just the same thing as
the presheaf of continuous functions.
-/
def subpresheaf_continuous_prelocal_iso_presheaf_to_Top (T : Top.{v}) :
  subpresheaf_to_Types (continuous_prelocal X T) ≅ presheaf_to_Top X T :=
nat_iso.of_components
  (λ X,
  { hom := by { rintro ⟨f, c⟩, exact ⟨f, c⟩, },
    inv := by { rintro ⟨f, c⟩, exact ⟨f, c⟩, },
    hom_inv_id' := by { ext ⟨f, p⟩ x, refl, },
    inv_hom_id' := by { ext ⟨f, p⟩ x, refl, }, })
  (by tidy)

/--
The sheaf of continuous functions on `X` with values in a space `T`.
-/
def sheaf_to_Top (T : Top.{v}) : sheaf (Type v) X :=
{ presheaf := presheaf_to_Top X T,
  sheaf_condition :=
    presheaf.sheaf_condition_equiv_of_iso (subpresheaf_continuous_prelocal_iso_presheaf_to_Top T)
      (subpresheaf_to_Types.sheaf_condition (continuous_local X T)), }

end Top
