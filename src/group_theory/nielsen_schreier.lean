/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import category_theory.action
import combinatorics.quiver.arborescence
import combinatorics.quiver.connected_component
import group_theory.is_free_group
/-!
# The Nielsen-Schreier theorem

This file proves that a subgroup of a free group is itself free.

## Main result

- `subgroup_is_free_of_is_free H`: an instance saying that a subgroup of a free group is free.

## Proof overview

The proof is analogous to the proof using covering spaces and fundamental groups of graphs,
but we work directly with groupoids instead of topological spaces. Under this analogy,

- `is_free_groupoid G` corresponds to saying that a space is a graph.
- `End_mul_equiv_subgroup H` plays the role of replacing 'subgroup of fundamental group' with
  'fundamental group of covering space'.
- `action_groupoid_is_free G A` corresponds to the fact that a covering of a (single-vertex)
  graph is a graph.
- `End_is_free T` corresponds to the fact that, given a spanning tree `T` of a
  graph, its fundamental group is free (generated by loops from the complement of the tree).

## Implementation notes

Our definition of `is_free_groupoid` is nonstandard. Normally one would require that functors
`G ⥤ X` to any _groupoid_ `X` are given by graph homomorphisms from the generators, but we only
consider _groups_ `X`. This simplifies the argument since functor equality is complicated in
general, but simple for functors to single object categories.

## References

https://ncatlab.org/nlab/show/Nielsen-Schreier+theorem

## Tags

free group, free groupoid, Nielsen-Schreier

-/

noncomputable theory
open_locale classical
universes v u

open category_theory category_theory.action_category category_theory.single_obj quiver
  is_free_group as fgp

/-- `is_free_groupoid.generators G` is a type synonym for `G`. We think of this as
the vertices of the generating quiver of `G` when `G` is free. We can't use `G` directly,
since `G` already has a quiver instance from being a groupoid. -/
@[nolint unused_arguments has_inhabited_instance]
def is_free_groupoid.generators (G) [groupoid G] := G

/-- A groupoid `G` is free when we have the following data:
 - a quiver on `is_free_groupoid.generators G` (a type synonym for `G`)
 - a function `of` taking a generating arrow to a morphism in `G`
 - such that a functor from `G` to any group `X` is uniquely determined
   by assigning labels in `X` to the generating arrows.

   This definition is nonstandard. Normally one would require that functors `G ⥤ X`
   to any _groupoid_ `X` are given by graph homomorphisms from `generators`. -/
class is_free_groupoid (G) [groupoid.{v} G] :=
(quiver_generators : quiver.{v+1} (is_free_groupoid.generators G))
(of : Π {a b : is_free_groupoid.generators G}, (a ⟶ b) → ((show G, from a) ⟶ b))
(unique_lift : ∀ {X : Type v} [group X] (f : labelling (is_free_groupoid.generators G) X),
                ∃! F : G ⥤ single_obj X, ∀ a b (g : a ⟶ b),
                  F.map (of g) = f g)

namespace is_free_groupoid

attribute [instance] quiver_generators

/-- Two functors from a free groupoid to a group are equal when they agree on the generating
quiver. -/
@[ext]
lemma ext_functor {G} [groupoid.{v} G] [is_free_groupoid G] {X : Type v} [group X]
  (f g : G ⥤ single_obj X)
  (h : ∀ a b (e : a ⟶ b), f.map (of e) = g.map (of e)) :
  f = g :=
let ⟨_, _, u⟩ := @unique_lift G _ _ X _ (λ (a b : generators G) (e : a ⟶ b), g.map (of e)) in
trans (u _ h) (u _ (λ _ _ _, rfl)).symm

/-- An action groupoid over a free froup is free. More generally, one could show that the groupoid
of elements over a free groupoid is free, but this version is easier to prove and suffices for our
purposes.

Analogous to the fact that a covering space of a graph is a graph. (A free groupoid is like a graph,
and a groupoid of elements is like a covering space.) -/
instance action_groupoid_is_free {G A : Type u} [group G] [is_free_group G] [mul_action G A] :
  is_free_groupoid (action_category G A) :=
{ quiver_generators := ⟨λ a b, { e : fgp.generators G // fgp.of e • a.back = b.back }⟩,
  of := λ a b e, ⟨fgp.of e, e.property⟩,
  unique_lift := begin
    introsI X _ f,
    let f' : fgp.generators G → (A → X) ⋊[mul_aut_arrow] G :=
      λ e, ⟨λ b, @f ⟨(), _⟩ ⟨(), b⟩ ⟨e, smul_inv_smul _ b⟩, fgp.of e⟩,
    rcases fgp.unique_lift f' with ⟨F', hF', uF'⟩,
    refine ⟨uncurry F' _, _, _⟩,
    { suffices : semidirect_product.right_hom.comp F' = monoid_hom.id _,
      { exact monoid_hom.ext_iff.mp this },
      ext,
      rw [monoid_hom.comp_apply, hF'],
      refl },
    { rintros ⟨⟨⟩, a : A⟩ ⟨⟨⟩, b⟩ ⟨e, h : fgp.of e • a = b⟩,
      change (F' (fgp.of _)).left _ = _,
      rw hF',
      cases (inv_smul_eq_iff.mpr h.symm),
      refl },
    { intros E hE,
      have : curry E = F',
      { apply uF',
        intro e,
        ext,
        { convert hE _ _ _, refl },
        { refl } },
      apply functor.hext,
      { intro, apply unit.ext },
      { refine action_category.cases _, intros,
        simp only [←this, uncurry_map, curry_apply_left, coe_back, hom_of_pair.val] } },
  end }

namespace spanning_tree
/- In this section, we suppose we have a free groupoid with a spanning tree for its generating
quiver. The goal is to prove that the vertex group at the root is free. A picture to have in mind
is that we are 'pulling' the endpoints of all the edges of the quiver along the spanning tree to
the root. -/
variables {G : Type u} [groupoid.{u} G] [is_free_groupoid G]
  (T : wide_subquiver (symmetrify $ generators G)) [arborescence T]

/-- The root of `T`, except its type is `G` instead of the type synonym `T`. -/
private def root' : G := show T, from root T

/-- A path in the tree gives a hom, by composition. -/
-- this has to be marked noncomputable, see issue #451.
-- It might be nicer to define this in terms of `compose_path`
noncomputable def hom_of_path : Π {a : G}, path (root T) a → (root' T ⟶ a)
| _ path.nil := 𝟙 _
| a (path.cons p f) := hom_of_path p ≫ sum.rec_on f.val (λ e, of e) (λ e, inv (of e))

/-- For every vertex `a`, there is a canonical hom from the root, given by the path in the tree. -/
def tree_hom (a : G) : root' T ⟶ a := hom_of_path T default

/-- Any path to `a` gives `tree_hom T a`, since paths in the tree are unique. -/
lemma tree_hom_eq {a : G} (p : path (root T) a) : tree_hom T a = hom_of_path T p :=
by rw [tree_hom, unique.default_eq]

@[simp] lemma tree_hom_root : tree_hom T (root' T) = 𝟙 _ :=
-- this should just be `tree_hom_eq T path.nil`, but Lean treats `hom_of_path` with suspicion.
trans (tree_hom_eq T path.nil) rfl

/-- Any hom in `G` can be made into a loop, by conjugating with `tree_hom`s. -/
def loop_of_hom {a b : G} (p : a ⟶ b) : End (root' T) :=
tree_hom T a ≫ p ≫ inv (tree_hom T b)

/-- Turning an edge in the spanning tree into a loop gives the indentity loop. -/
lemma loop_of_hom_eq_id {a b : generators G} (e ∈ wide_subquiver_symmetrify T a b) :
  loop_of_hom T (of e) = 𝟙 (root' T) :=
begin
  rw [loop_of_hom, ←category.assoc, is_iso.comp_inv_eq, category.id_comp],
  cases H,
  { rw [tree_hom_eq T (path.cons default ⟨sum.inl e, H⟩), hom_of_path], refl },
  { rw [tree_hom_eq T (path.cons default ⟨sum.inr e, H⟩), hom_of_path],
    simp only [is_iso.inv_hom_id, category.comp_id, category.assoc, tree_hom] }
end

/-- Since a hom gives a loop, any homomorphism from the vertex group at the root
    extends to a functor on the whole groupoid. -/
@[simps] def functor_of_monoid_hom {X} [monoid X] (f : End (root' T) →* X) :
  G ⥤ single_obj X :=
{ obj := λ _, (),
  map := λ a b p, f (loop_of_hom T p),
  map_id' := begin
    intro a,
    rw [loop_of_hom, category.id_comp, is_iso.hom_inv_id, ←End.one_def, f.map_one, id_as_one],
 end,
  map_comp' := begin
    intros,
    rw [comp_as_mul, ←f.map_mul],
    simp only [is_iso.inv_hom_id_assoc, loop_of_hom, End.mul_def, category.assoc]
  end }

/-- Given a free groupoid and an arborescence of its generating quiver, the vertex
    group at the root is freely generated by loops coming from generating arrows
    in the complement of the tree. -/
def End_is_free : is_free_group (End (root' T)) :=
{ generators := set.compl (wide_subquiver_equiv_set_total $ wide_subquiver_symmetrify T),
  of := λ e, loop_of_hom T (of e.val.hom),
  unique_lift' := begin
    introsI X _ f,
    let f' : labelling (generators G) X := λ a b e,
      if h : e ∈ wide_subquiver_symmetrify T a b then 1
      else f ⟨⟨a, b, e⟩, h⟩,
    rcases unique_lift f' with ⟨F', hF', uF'⟩,
    refine ⟨F'.map_End _, _, _⟩,
    { suffices : ∀ {x y} (q : x ⟶ y), F'.map (loop_of_hom T q) = (F'.map q : X),
      { rintro ⟨⟨a, b, e⟩, h⟩,
        rw [functor.map_End_apply, this, hF'],
        exact dif_neg h },
      intros,
      suffices : ∀ {a} (p : path (root' T) a), F'.map (hom_of_path T p) = 1,
      { simp only [this, tree_hom, comp_as_mul, inv_as_inv, loop_of_hom,
        one_inv, mul_one, one_mul, functor.map_inv, functor.map_comp] },
      intros a p, induction p with b c p e ih,
      { rw [hom_of_path, F'.map_id, id_as_one] },
      rw [hom_of_path, F'.map_comp, comp_as_mul, ih, mul_one],
      rcases e with ⟨e | e, eT⟩,
      { rw hF', exact dif_pos (or.inl eT) },
      { rw [F'.map_inv, inv_as_inv, inv_eq_one, hF'], exact dif_pos (or.inr eT) } },
    { intros E hE,
      ext,
      suffices : (functor_of_monoid_hom T E).map x = F'.map x,
      { simpa only [loop_of_hom, functor_of_monoid_hom_map, is_iso.inv_id, tree_hom_root,
          category.id_comp, category.comp_id] using this },
      congr,
      apply uF',
      intros a b e,
      change E (loop_of_hom T _) = dite _ _ _,
      split_ifs,
      { rw [loop_of_hom_eq_id T e h, ←End.one_def, E.map_one] },
      { exact hE ⟨⟨a, b, e⟩, h⟩ } }
  end }

end spanning_tree

/-- Another name for the identity function `G → G`, to help type checking. -/
private def symgen {G : Type u} [groupoid.{v} G] [is_free_groupoid G] :
  G → symmetrify (generators G) := id

/-- If there exists a morphism `a → b` in a free groupoid, then there also exists a zigzag
from `a` to `b` in the generating quiver. -/
lemma path_nonempty_of_hom {G} [groupoid.{u u} G] [is_free_groupoid G] {a b : G} :
  nonempty (a ⟶ b) → nonempty (path (symgen a) (symgen b)) :=
begin
  rintro ⟨p⟩,
  rw [←@weakly_connected_component.eq (generators G), eq_comm,
    ←free_group.of_injective.eq_iff, ←mul_inv_eq_one],
  let X := free_group (weakly_connected_component $ generators G),
  let f : G → X := λ g, free_group.of (weakly_connected_component.mk g),
  let F : G ⥤ single_obj X := single_obj.difference_functor f,
  change F.map p = ((category_theory.functor.const G).obj ()).map p,
  congr, ext,
  rw [functor.const.obj_map, id_as_one, difference_functor_map, mul_inv_eq_one],
  apply congr_arg free_group.of,
  apply (weakly_connected_component.eq _ _).mpr,
  exact ⟨hom.to_path (sum.inr e)⟩,
end

/-- Given a connected free groupoid, its generating quiver is rooted-connected. -/
instance generators_connected (G) [groupoid.{u u} G] [is_connected G] [is_free_groupoid G]
  (r : G) : rooted_connected (symgen r) :=
⟨λ b, path_nonempty_of_hom (category_theory.nonempty_hom_of_connected_groupoid r b)⟩

/-- A vertex group in a free connected groupoid is free. With some work one could drop the
connectedness assumption, by looking at connected components. -/
instance End_is_free_of_connected_free {G} [groupoid G] [is_connected G] [is_free_groupoid G]
  (r : G) : is_free_group (End r) :=
spanning_tree.End_is_free $ geodesic_subtree (symgen r)

end is_free_groupoid

/-- The Nielsen-Schreier theorem: a subgroup of a free group is free. -/
instance subgroup_is_free_of_is_free {G : Type u} [group G] [is_free_group G]
  (H : subgroup G) : is_free_group H :=
is_free_group.of_mul_equiv (End_mul_equiv_subgroup H)
