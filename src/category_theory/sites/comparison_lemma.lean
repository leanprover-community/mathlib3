/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import category_theory.sites.dense_subsite
import category_theory.sites.cover_lifting
import category_theory.sites.cover_preserving
import category_theory.adjunction.fully_faithful

/-!
# Comparison lemma

Given a fully faithful functor `G : (C, J) ⥤ (D, K)`, that is cover-lifting, cover-preserving,
and cover-dense, `G` will induce an equivalence of categories of sheaves.

Given a fully faithful cover-dense functor `G : C ⥤ (D, K)`, we may define the induced topology on
`C` by letting the covering sieves be the preimages of the covering sieves in `K`. This would make
`G` both cover-lifting and cover-preserving, and in particular,
`Sheaf (H.induced_topology) A ≌ Sheaf K A`.

## Main results

- `category_theory.pullback_copullback_adjunction`: If `G : (C, J) ⥤ (D, K)` is cover-lifting,
  cover-preserving, and compatible-preserving, then `pullback G` and `copullback G` are adjoint.
- `category_theory.comparison_lemma.Sheaf_iso_of_dense_cover_preserving_cover_lifting`:
  If `G : (C, J) ⥤ (D, K)` is fully-faithful, cover-lifting, cover-preserving, and cover-dense,
  then it will induce an equivalence of categories of sheaves.
- `category_theory.cover_dense.induced_topology`: If `G : C ⥤ (D, K)` is fully-faithful and
  cover-dense, then the set `{ T ∩ mor(C) | T ∈ K }` is a grothendieck topology of `C`.
- `category_theory.cover_dense.Sheaf_iso`: : If `G : C ⥤ (D, K)` is fully-faithful and
  cover-dense, it will induce an equivalence of categories of sheaves wrt the induced topology.

## References

* [Elephant]: *Sketches of an Elephant*, ℱ. T. Johnstone: C2.2.
* https://ncatlab.org/nlab/show/dense+sub-site
* https://ncatlab.org/nlab/show/comparison+lemma

-/

namespace category_theory

universes v u

section
open limits
open opposite
open presieve
variables {C D : Type u} [category.{u} C] [category.{u} D] {G : C ⥤ D}
variables {J : grothendieck_topology C} {K : grothendieck_topology D}
variables (A : Type v) [category.{u} A]
variables (H : cover_dense K G) (H' : cover_preserving J K G) (H'' : cover_lifting J K G)


/--
Given a functor between sites that is cover-preserving, cover-lifting, and compatible-preserving,
the pullback and copullback along `G` is adjoint to each other
-/
@[simps] noncomputable
def pullback_copullback_adjunction [has_limits A] (H : compatible_preserving K G) :
  sites.pullback A H H' ⊣ sites.copullback A H'' :=
{ hom_equiv := λ X Y, (Ran.adjunction A G.op).hom_equiv X.val Y.val,
  unit := { app := λ X, (Ran.adjunction A G.op).unit.app X.val,
    naturality' := λ _ _ f, (Ran.adjunction A G.op).unit.naturality f },
  counit := { app := λ X, (Ran.adjunction A G.op).counit.app X.val,
    naturality' := λ _ _ f, (Ran.adjunction A G.op).counit.naturality f },
  hom_equiv_unit' := λ X Y f, (Ran.adjunction A G.op).hom_equiv_unit,
  hom_equiv_counit' := λ X Y f, (Ran.adjunction A G.op).hom_equiv_counit }


variables (A) [full G] [faithful G]

lemma cover_dense.compatible_preserving (H : cover_dense K G) : compatible_preserving K G :=
begin
  split,
  intros ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ eq,
  apply H.sheaf_ext,
  intros W i,
  simp only [←functor_to_types.map_comp_apply, ←op_comp],
  rw ← G.image_preimage (i ≫ f₁),
  rw ← G.image_preimage (i ≫ f₂),
  apply hx,
  apply G.map_injective,
  simp[eq]
end

lemma is_iso_iff_is_presheaf_iso {ℱ ℱ' : Sheaf K A} (α : ℱ ⟶ ℱ') :
  is_iso α ↔ @is_iso (Dᵒᵖ ⥤ A) _ _ _ α :=
begin
  split,
  all_goals { rintro ⟨a, b, c⟩, use ⟨a, b, c⟩ }
end


namespace comparison_lemma

noncomputable
instance sites.pullback.full :
  full (sites.pullback A H.compatible_preserving H') :=
{ preimage := λ ℱ ℱ' α, H.sheaf_hom α,
  witness' := λ ℱ ℱ' α, (H.sheaf_hom_restrict_eq α).symm }

instance sites.pullback.faithful :
  faithful (sites.pullback A H.compatible_preserving H') :=
{ map_injective' := λ ℱ ℱ' α β (eq : whisker_left G.op α = whisker_left G.op β),
  by rw [H.sheaf_hom_eq α, H.sheaf_hom_eq β, eq] }

include H H' H''
variable [has_limits A]

/--
Given a functor between sites that is cover-dense, cover-preserving, and cover-lifting,
it induces an equivalence of category of sheaves valued in a complete category.
-/
noncomputable
def Sheaf_iso_of_dense_cover_preserving_cover_lifting : Sheaf J A ≌ Sheaf K A :=
begin
  symmetry,
  let α := pullback_copullback_adjunction A H' H'' H.compatible_preserving,
  haveI : is_iso α.unit := infer_instance,
  haveI : ∀ (X : Sheaf J A), is_iso (α.counit.app X),
  { intro ℱ,
    rw is_iso_iff_is_presheaf_iso,
    exact is_iso.of_iso ((@as_iso _ _ _ _ _ (Ran.reflective A G.op)).app ℱ.val) },
  haveI : is_iso α.counit := nat_iso.is_iso_of_is_iso_app _,
  exact { unit_iso := as_iso α.unit,
    counit_iso := as_iso α.counit,
    inverse := sites.copullback A H'',
    functor := sites.pullback A H.compatible_preserving H',
    functor_unit_iso_comp' := λ ℱ, by convert α.left_triangle_components }
end

omit H H' H''

variables (K) (G)
  (hyp : ∀ ⦃X⦄ (T : K (G.obj X)), (T.val.functor_pullback G).functor_pushforward G ∈ K (G.obj X))

include hyp

/--
If a fully faithful functor `G : C ⥤ (D, K)` satisfies
"for each covering sieve `T` in `D`, `T ∩ mor(C)` generates a covering sieve in `D`",
then the set `{ T ∩ mor(C) | T ∈ K }` is a grothendieck topology of `C`.
-/
@[simps]
def induced_topology_of_fully_faithful_locally_dense :
  grothendieck_topology C :=
{ sieves := λ X S, K _ (S.functor_pushforward G),
  top_mem' := λ X, by { change K _ _, rw sieve.functor_pushforward_top, exact K.top_mem _ },
  pullback_stable' := λ X Y S f hS,
  begin
    have : S.pullback f = ((S.functor_pushforward G).pullback (G.map f)).functor_pullback G,
    { conv_lhs { rw ←(sieve.fully_faithful_functor_galois_coinsertion G X).u_l_eq S },
      ext,
      change (S.functor_pushforward G) _ ↔ (S.functor_pushforward G) _,
      rw G.map_comp },
    rw this,
    change K _ _,
    apply hyp ⟨_, K.pullback_stable (G.map f) hS⟩
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
def induced_topology_cover_lifting :
  cover_lifting (induced_topology_of_fully_faithful_locally_dense G K hyp) K G :=
⟨λ _ S hS, hyp ⟨S, hS⟩⟩

/-- `G` is cover-preserving wrt the induced topology. -/
lemma induced_topology_cover_preserving :
  cover_preserving (induced_topology_of_fully_faithful_locally_dense G K hyp) K G :=
⟨λ _ S hS, hS⟩

end comparison_lemma
open comparison_lemma

/-- Given a cover-dense functor `G : C ⥤ (D, K)`, we may induce a topology on `C`. -/
abbreviation cover_dense.induced_topology (H : cover_dense K G) :
  grothendieck_topology C :=
induced_topology_of_fully_faithful_locally_dense G K
  (λ _ T, H.functor_pullback_pushforward_covering T)

/--
Cover-dense functors induces an equivalence of categories of sheaves.

This is known as the comparison lemma. It requires that the sites are small and the target category
is complete.
-/
noncomputable
def Sheaf_iso (H : cover_dense K G) [has_limits A] : Sheaf (H.induced_topology) A ≌ Sheaf K A :=
Sheaf_iso_of_dense_cover_preserving_cover_lifting A H
  (induced_topology_cover_preserving G K (λ _ T, H.functor_pullback_pushforward_covering T))
  (induced_topology_cover_lifting G K (λ _ T, H.functor_pullback_pushforward_covering T))

end
end category_theory
