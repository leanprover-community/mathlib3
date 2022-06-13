/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison, Adam Topaz
-/
import topology.sheaves.sheaf_of_functions
import topology.sheaves.stalks
import topology.local_homeomorph
import topology.sheaves.sheaf_condition.unique_gluing

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
* `Top.sheaf_to_Top`: continuous functions into a topological space form a sheaf

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
  res := λ U V i f h, continuous.comp h (opens.open_embedding_of_le i.le).continuous, }

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
     simpa using (opens.open_embedding_of_le i.le).continuous_at_iff.1 w,
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

/--
The functions satisfying a local predicate satisfy the sheaf condition.
-/
lemma is_sheaf (P : local_predicate T) :
  (subpresheaf_to_Types P.to_prelocal_predicate).is_sheaf :=
presheaf.is_sheaf_of_is_sheaf_unique_gluing_types _ $ λ ι U sf sf_comp, begin
  -- We show the sheaf condition in terms of unique gluing.
  -- First we obtain a family of sections for the underlying sheaf of functions,
  -- by forgetting that the prediacte holds
  let sf' : Π i : ι, (presheaf_to_Types X T).obj (op (U i)) := λ i, (sf i).val,
  -- Since our original family is compatible, this one is as well
  have sf'_comp : (presheaf_to_Types X T).is_compatible U sf' := λ i j,
    congr_arg subtype.val (sf_comp i j),
  -- So, we can obtain a unique gluing
  obtain ⟨gl,gl_spec,gl_uniq⟩ := (sheaf_to_Types X T).exists_unique_gluing U sf' sf'_comp,
  refine ⟨⟨gl,_⟩,_,_⟩,
  { -- Our first goal is to show that this chosen gluing satisfies the
    -- predicate. Of course, we use locality of the predicate.
    apply P.locality,
    rintros ⟨x, mem⟩,
    -- Once we're at a particular point `x`, we can select some open set `x ∈ U i`.
    choose i hi using opens.mem_supr.mp mem,
    -- We claim that the predicate holds in `U i`
    use [U i, hi, opens.le_supr U i],
    -- This follows, since our original family `sf` satisfies the predicate
    convert (sf i).property,
    exact gl_spec i },
  -- It remains to show that the chosen lift is really a gluing for the subsheaf and
  -- that it is unique. Both of which follow immediately from the corresponding facts
  -- in the sheaf of functions without the local predicate.
  { intro i,
    ext1,
    exact (gl_spec i) },
  { intros gl' hgl',
    ext1,
    exact gl_uniq gl'.1 (λ i, congr_arg subtype.val (hgl' i)) },
end

end subpresheaf_to_Types

/--
The subsheaf of the sheaf of all dependently typed functions satisfying the local predicate `P`.
-/
@[simps]
def subsheaf_to_Types (P : local_predicate T) : sheaf (Type v) X :=
⟨subpresheaf_to_Types P.to_prelocal_predicate, subpresheaf_to_Types.is_sheaf P⟩

/--
There is a canonical map from the stalk to the original fiber, given by evaluating sections.
-/
def stalk_to_fiber (P : local_predicate T) (x : X) :
  (subsheaf_to_Types P).1.stalk x ⟶ T x :=
begin
  refine colimit.desc _
    { X := T x, ι := { app := λ U f, _, naturality' := _ } },
  { exact f.1 ⟨x, (unop U).2⟩, },
  { tidy, }
end

@[simp] lemma stalk_to_fiber_germ (P : local_predicate T) (U : opens X) (x : U) (f) :
  stalk_to_fiber P x ((subsheaf_to_Types P).1.germ x f) = f.1 x :=
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
  { exact (subsheaf_to_Types P).1.germ ⟨x, U.2⟩ ⟨f, h⟩, },
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
      tU = (subsheaf_to_Types P).1.germ ⟨x, (unop W).2⟩ ⟨s, hW⟩ ∧
      tV = (subsheaf_to_Types P).1.germ ⟨x, (unop W).2⟩ ⟨s, hW⟩ := _,
  { choose W s hW e using Q,
    exact e.1.trans e.2.symm, },
  -- Then use induction to pick particular representatives of `tU tV : stalk x`
  obtain ⟨U, ⟨fU, hU⟩, rfl⟩ := jointly_surjective'.{v v} tU,
  obtain ⟨V, ⟨fV, hV⟩, rfl⟩ := jointly_surjective'.{v v} tV,
  { -- Decompose everything into its constituent parts:
    dsimp,
    simp only [stalk_to_fiber, types.colimit.ι_desc_apply'] at h,
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
⟨presheaf_to_Top X T,
  presheaf.is_sheaf_of_iso (subpresheaf_continuous_prelocal_iso_presheaf_to_Top T)
    (subpresheaf_to_Types.is_sheaf (continuous_local X T))⟩

end Top
