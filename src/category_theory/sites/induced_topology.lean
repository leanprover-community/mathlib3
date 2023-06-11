/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import category_theory.sites.dense_subsite

/-!
# Induced Topology

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We say that a functor `G : C ⥤ (D, K)` is locally dense if for each covering sieve `T` in `D` of
some `X : C`, `T ∩ mor(C)` generates a covering sieve of `X` in `D`. A locally dense fully faithful
functor then induces a topology on `C` via `{ T ∩ mor(C) | T ∈ K }`. Note that this is equal to
the collection of sieves on `C` whose image generates a covering sieve. This construction would
make `C` both cover-lifting and cover-preserving.

Some typical examples are full and cover-dense functors (for example the functor from a basis of a
topological space `X` into `opens X`). The functor `over X ⥤ C` is also locally dense, and the
induced topology can then be used to construct the big sites associated to a scheme.

Given a fully faithful cover-dense functor `G : C ⥤ (D, K)` between small sites, we then have
`Sheaf (H.induced_topology) A ≌ Sheaf K A`. This is known as the comparison lemma.

## References

* [Elephant]: *Sketches of an Elephant*, P. T. Johnstone: C2.2.
* https://ncatlab.org/nlab/show/dense+sub-site
* https://ncatlab.org/nlab/show/comparison+lemma

-/

namespace category_theory

universes v u

open limits opposite presieve

section

variables {C : Type*} [category C] {D : Type*} [category D] {G : C ⥤ D}
variables {J : grothendieck_topology C} {K : grothendieck_topology D}
variables (A : Type v) [category.{u} A]

-- variables (A) [full G] [faithful G]

/--
We say that a functor `C ⥤ D` into a site is "locally dense" if
for each covering sieve `T` in `D`, `T ∩ mor(C)` generates a covering sieve in `D`.
-/
def locally_cover_dense (K : grothendieck_topology D) (G : C ⥤ D) : Prop :=
∀ ⦃X⦄ (T : K (G.obj X)), (T.val.functor_pullback G).functor_pushforward G ∈ K (G.obj X)

namespace locally_cover_dense

variables [full G] [faithful G] (Hld : locally_cover_dense K G)

include Hld

lemma pushforward_cover_iff_cover_pullback {X : C} (S : sieve X) :
  K _ (S.functor_pushforward G) ↔ ∃ (T : K (G.obj X)), T.val.functor_pullback G = S :=
begin
  split,
  { intros hS,
    exact ⟨⟨_, hS⟩, (sieve.fully_faithful_functor_galois_coinsertion G X).u_l_eq S⟩ },
  { rintros ⟨T, rfl⟩,
    exact Hld T }
end

/--
If a functor `G : C ⥤ (D, K)` is fully faithful and locally dense,
then the set `{ T ∩ mor(C) | T ∈ K }` is a grothendieck topology of `C`.
-/
@[simps]
def induced_topology :
  grothendieck_topology C :=
{ sieves := λ X S, K _ (S.functor_pushforward G),
  top_mem' := λ X, by { change K _ _, rw sieve.functor_pushforward_top, exact K.top_mem _ },
  pullback_stable' := λ X Y S f hS,
  begin
    have : S.pullback f = ((S.functor_pushforward G).pullback (G.map f)).functor_pullback G,
    { conv_lhs { rw ← (sieve.fully_faithful_functor_galois_coinsertion G X).u_l_eq S },
      ext,
      change (S.functor_pushforward G) _ ↔ (S.functor_pushforward G) _,
      rw G.map_comp },
    rw this,
    change K _ _,
    apply Hld ⟨_, K.pullback_stable (G.map f) hS⟩
  end,
  transitive' := λ X S hS S' H',
  begin
    apply K.transitive hS,
    rintros Y _ ⟨Z, g, i, hg, rfl⟩,
    rw sieve.pullback_comp,
    apply K.pullback_stable i,
    refine K.superset_covering _ (H' hg),
    rintros W _ ⟨Z', g', i', hg, rfl⟩,
    use ⟨Z', g' ≫ g, i', hg, by simp⟩
  end }

/-- `G` is cover-lifting wrt the induced topology. -/
lemma induced_topology_cover_lifting :
  cover_lifting Hld.induced_topology K G := ⟨λ _ S hS, Hld ⟨S, hS⟩⟩

/-- `G` is cover-preserving wrt the induced topology. -/
lemma induced_topology_cover_preserving :
  cover_preserving Hld.induced_topology K G := ⟨λ _ S hS, hS⟩

end locally_cover_dense

lemma cover_dense.locally_cover_dense [full G] (H : cover_dense K G) : locally_cover_dense K G :=
begin
  intros X T,
  refine K.superset_covering _ (K.bind_covering T.property (λ Y f Hf, H.is_cover Y)),
  rintros Y _ ⟨Z, _, f, hf, ⟨W, g, f', (rfl : _ = _)⟩, rfl⟩,
  use W, use G.preimage (f' ≫ f), use g,
  split,
  simpa using T.val.downward_closed hf f',
  simp,
end

/--
Given a fully faithful cover-dense functor `G : C ⥤ (D, K)`, we may induce a topology on `C`.
-/
abbreviation cover_dense.induced_topology [full G] [faithful G] (H : cover_dense K G) :
  grothendieck_topology C := H.locally_cover_dense.induced_topology

variable (J)

lemma over_forget_locally_cover_dense (X : C) : locally_cover_dense J (over.forget X) :=
begin
  intros Y T,
  convert T.property,
  ext Z f,
  split,
  { rintros ⟨_, _, g', hg, rfl⟩,
    exact T.val.downward_closed hg g' },
  { intros hf,
    exact ⟨over.mk (f ≫ Y.hom), over.hom_mk f, 𝟙 _, hf, (category.id_comp _).symm⟩ }
end

end

section small_site

variables {C : Type v} [small_category C] {D : Type v} [small_category D] {G : C ⥤ D}
variables {J : grothendieck_topology C} {K : grothendieck_topology D}
variables (A : Type u) [category.{v} A]

/--
Cover-dense functors induces an equivalence of categories of sheaves.

This is known as the comparison lemma. It requires that the sites are small and the value category
is complete.
-/
noncomputable
def cover_dense.Sheaf_equiv [full G] [faithful G] (H : cover_dense K G) [has_limits A] :
  Sheaf H.induced_topology A ≌ Sheaf K A :=
H.Sheaf_equiv_of_cover_preserving_cover_lifting
  H.locally_cover_dense.induced_topology_cover_preserving
  H.locally_cover_dense.induced_topology_cover_lifting

end small_site

end category_theory
