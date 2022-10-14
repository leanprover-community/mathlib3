/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli, Junyan Xu
-/
import category_theory.groupoid.vertex_group
import category_theory.groupoid
import algebra.group.defs
import algebra.hom.group
import algebra.hom.equiv
import data.set.lattice
import combinatorics.quiver.connected_component
import group_theory.subgroup.basic
/-!
# Subgroupoid

This file defines subgroupoids as `structure`s containing the subsets of arrows and their
stability under composition and inversion.
Also defined are

* containment of subgroupoids is a complete lattice;
* images and preimages of subgroupoids under a functor;
* the notion of normality of subgroupoids and its stability under intersection and preimage;
* compatibility of the above with `groupoid.vertex_group`.


## Main definitions

Given a type `C` with associated `groupoid C` instance.

* `subgroupoid C` is the type of subgroupoids of `C`
* `subgroupoid.is_normal` is the property that the subgroupoid is stable under conjugation
  by arbitrary arrows, _and_ that all identity arrows are contained in the subgroupoid.
* `subgroupoid.comap` is the "preimage" map of subgroupoids along a functor.
* `subgroupoid.map` is the "image" map of subgroupoids along a functor _injective on objects_.
* `subgroupoid.vertex_subgroup` is the subgroup of the `vertex group` at a given vertex `v`,
  assuming `v` is contained in the `subgroupoid` (meaning, by definition, that the arrow `𝟙 v`
  is contained in the subgroupoid).

## Implementation details

The structure of this file is copied from/inspired by `group_theory.subgroup.basic`
and `combinatorics.simple_graph.subgraph`.

## TODO

* Equivalent inductive characterization of generated (normal) subgroupoids.
* Characterization of normal subgroupoids as kernels.

## Tags

subgroupoid

-/

namespace category_theory

open set groupoid

local attribute [protected] category_theory.inv

universes u v

variables {C : Type u} [groupoid C]

/--
A sugroupoid of `C` consists of a choice of arrows for each pair of vertices, closed
under composition and inverses.
-/
@[ext] structure subgroupoid (C : Type u) [groupoid C] :=
(arrows : ∀ (c d : C), set (c ⟶ d))
(inv : ∀ {c d} {p : c ⟶ d} (hp : p ∈ arrows c d),
          inv p ∈ arrows d c)
(mul : ∀ {c d e} {p} (hp : p ∈ arrows c d) {q} (hq : q ∈ arrows d e),
          p ≫ q ∈ arrows c e)

attribute [protected] subgroupoid.inv subgroupoid.mul

namespace subgroupoid

variable (S : subgroupoid C)

/-- The vertices of `C` on which `S` has non-trivial isotropy -/
def objs : set C := {c : C | (S.arrows c c).nonempty}

lemma id_mem_of_nonempty_isotropy (c : C) :
  c ∈ objs S → 𝟙 c ∈ S.arrows c c :=
begin
  rintro ⟨γ,hγ⟩,
  convert S.mul hγ (S.inv hγ),
  simp only [inv_eq_inv, is_iso.hom_inv_id],
end

/-- A subgroupoid seen as a quiver on vertex set `C` -/
def as_wide_quiver : quiver C := ⟨λ c d, subtype $ S.arrows c d⟩

/-- The coercion of a subgroupoid as a groupoid -/
instance coe : groupoid S.objs :=
{ hom := λ a b, S.arrows a.val b.val,
  id := λ a, ⟨𝟙 a.val, id_mem_of_nonempty_isotropy S a.val a.prop⟩,
  comp := λ a b c p q, ⟨p.val ≫ q.val, S.mul p.prop q.prop⟩,
  id_comp' := λ a b ⟨p,hp⟩, by simp only [category.id_comp],
  comp_id' := λ a b ⟨p,hp⟩, by simp only [category.comp_id],
  assoc' := λ a b c d ⟨p,hp⟩ ⟨q,hq⟩ ⟨r,hr⟩, by simp only [category.assoc],
  inv := λ a b p, ⟨inv p.val, S.inv p.prop⟩,
  inv_comp' := λ a b ⟨p,hp⟩, by simp only [inv_comp],
  comp_inv' := λ a b ⟨p,hp⟩, by simp only [comp_inv] }

/-- The embedding of the coerced subgroupoid to its parent-/
def hom : S.objs ⥤ C :=
{ obj := λ c, c.val,
  map := λ c d f, f.val,
  map_id' := λ c, rfl,
  map_comp' := λ c d e f g, rfl }

lemma hom.inj_on_objects : function.injective (hom S).obj :=
by { rintros ⟨c,hc⟩ ⟨d,hd⟩ hcd, simp only [subtype.mk_eq_mk], exact hcd }

lemma hom.faithful :
  ∀ c d, function.injective (λ (f : c ⟶ d), (hom S).map f) :=
by { rintros ⟨c,hc⟩ ⟨d,hd⟩ ⟨f,hf⟩ ⟨g,hg⟩ hfg, simp only [subtype.mk_eq_mk], exact hfg, }

/-- The subgroup of the vertex group at `c` given by the subgroupoid -/
def vertex_subgroup {c : C} (hc : c ∈ S.objs) : subgroup (c ⟶ c) :=
{ carrier  := S.arrows c c,
  mul_mem' := λ f g hf hg, S.mul hf hg,
  one_mem' := id_mem_of_nonempty_isotropy _ _ hc,
  inv_mem' := λ f hf, S.inv hf }

instance : set_like (subgroupoid C) (Σ (c d : C), c ⟶ d) :=
{ coe := λ S, {F | F.2.2 ∈ S.arrows F.1 F.2.1},
  coe_injective' := λ ⟨S, _, _⟩ ⟨T, _, _⟩ h, by { ext c d f, apply set.ext_iff.1 h ⟨c, d, f⟩ } }

lemma mem_iff (S : subgroupoid C) (F : Σ c d, c ⟶ d) :
  F ∈ S ↔ F.2.2 ∈ S.arrows F.1 F.2.1 := iff.rfl

lemma le_iff (S T : subgroupoid C) : (S ≤ T) ↔ (∀ {c d}, (S.arrows c d) ⊆ (T.arrows c d)) :=
by { rw [set_like.le_def, sigma.forall], exact forall_congr (λ c, sigma.forall) }

instance : has_top (subgroupoid C) :=
⟨ { arrows := (λ _ _, set.univ),
    mul    := by { rintros, trivial, },
    inv    := by { rintros, trivial, } } ⟩

instance : has_bot (subgroupoid C) :=
⟨ { arrows := (λ _ _, ∅),
    mul    := λ _ _ _ _, false.elim,
    inv    := λ _ _ _, false.elim } ⟩

instance : inhabited (subgroupoid C) := ⟨⊤⟩

instance : has_inf (subgroupoid C) :=
⟨ λ S T,
  { arrows := (λ c d, (S.arrows c d) ∩ (T.arrows c d)),
    inv    := by { rintros, exact ⟨S.inv hp.1, T.inv hp.2⟩, },
    mul    := by { rintros, exact ⟨S.mul hp.1 hq.1, T.mul hp.2 hq.2⟩, } } ⟩

instance : has_Inf (subgroupoid C) :=
⟨ λ s,
  { arrows := λ c d, ⋂ S ∈ s, (subgroupoid.arrows S c d),
    inv := by { intros, rw mem_Inter₂ at hp ⊢, exact λ S hS, S.inv (hp S hS) },
    mul := by { intros, rw mem_Inter₂ at hp hq ⊢,exact λ S hS, S.mul (hp S hS) (hq S hS) } } ⟩

instance : complete_lattice (subgroupoid C) :=
{ bot          := (⊥),
  bot_le       := λ S, empty_subset _,
  top          := (⊤),
  le_top       := λ S, subset_univ _,
  inf          := (⊓),
  le_inf       := λ R S T RS RT _ pR, ⟨RS pR, RT pR⟩,
  inf_le_left  := λ R S _, and.left,
  inf_le_right := λ R S _, and.right,
  .. complete_lattice_of_Inf (subgroupoid C)
  begin
    refine (λ s, ⟨λ S Ss F, _, λ T Tl F fT, _⟩);
      simp only [Inf, mem_iff, mem_Inter],
    exacts [λ hp, hp S Ss, λ S Ss, Tl Ss fT],
  end }

lemma le_objs {S T : subgroupoid C} (h : S ≤ T) : S.objs ⊆ T.objs :=
λ s ⟨γ, hγ⟩, ⟨γ, @h ⟨s, s, γ⟩ hγ⟩

/-- The functor associated to the embedding of subgroupoids -/
def inclusion {S T : subgroupoid C} (h : S ≤ T) : S.objs ⥤ T.objs :=
{ obj := λ s, ⟨s.val, le_objs h s.prop⟩,
  map := λ s t f, ⟨f.val, @h ⟨s, t, f.val⟩ f.prop⟩,
  map_id' := λ _, rfl,
  map_comp' := λ _ _ _ _ _, rfl }

lemma inclusion_inj_on_objects {S T : subgroupoid C} (h : S ≤ T) :
  function.injective (inclusion h).obj :=
λ ⟨s,hs⟩ ⟨t,ht⟩, by simpa only [inclusion, subtype.mk_eq_mk] using id

lemma inclusion_faithful {S T : subgroupoid C} (h : S ≤ T) (s t : S.objs):
  function.injective (λ (f : s ⟶ t), (inclusion h).map f) :=
λ ⟨f,hf⟩ ⟨g,hg⟩, by { dsimp only [inclusion], simpa only [subtype.mk_eq_mk] using id }

lemma inclusion_refl {S : subgroupoid C} : inclusion (le_refl S) = 𝟭 S.objs :=
functor.hext (λ ⟨s,hs⟩, rfl) (λ ⟨s,hs⟩ ⟨t,ht⟩ ⟨f,hf⟩, heq_of_eq rfl)

lemma inclusion_trans {R S T : subgroupoid C} (k : R ≤ S) (h : S ≤ T) :
  inclusion (k.trans h) = (inclusion k) ⋙ (inclusion h) := rfl

lemma inclusion_comp_embedding {S T : subgroupoid C} (h : S ≤ T) :
  (inclusion h) ⋙ T.hom = S.hom := rfl

/-- The family of arrows of the discrete groupoid -/
inductive discrete.arrows : Π (c d : C), (c ⟶ d) → Prop
| id (c : C) : discrete.arrows c c (𝟙 c)

/-- The only arrows of the discrete groupoid are the identity arrows. -/
def discrete : subgroupoid C :=
{ arrows := discrete.arrows,
  inv := by { rintros _ _ _ ⟨⟩, simp only [inv_eq_inv, is_iso.inv_id], split, },
  mul := by { rintros _ _ _ _ ⟨⟩ _ ⟨⟩, rw category.comp_id, split, } }

lemma mem_discrete_iff {c d : C} (f : c ⟶ d):
  (f ∈ (discrete).arrows c d) ↔ (∃ (h : c = d), f = eq_to_hom h) :=
⟨by { rintro ⟨⟩, exact ⟨rfl, rfl⟩ }, by { rintro ⟨rfl, rfl⟩, split }⟩

/-- A subgroupoid is normal if it is “wide” (meaning that its carrier set is all of `C`)
    and satisfies the expected stability under conjugacy. -/
structure is_normal : Prop :=
(wide : ∀ c, (𝟙 c) ∈ (S.arrows c c))
(conj : ∀ {c d} (p : c ⟶ d) {γ : c ⟶ c} (hs : γ ∈ S.arrows c c),
              ((inv p) ≫ γ ≫ p) ∈ (S.arrows d d))

lemma is_normal.conj' {S : subgroupoid C} (Sn : is_normal S) :
  ∀ {c d} (p : d ⟶ c) {γ : c ⟶ c} (hs : γ ∈ S.arrows c c), (p ≫ γ ≫ (inv p)) ∈ (S.arrows d d) :=
λ c d p γ hs, by { convert Sn.conj (inv p) hs, simp, }

lemma is_normal.conjugation_bij (Sn : is_normal S) {c d} (p : c ⟶ d) :
  set.bij_on (λ γ : c ⟶ c, (inv p) ≫ γ ≫ p) (S.arrows c c) (S.arrows d d) :=
begin
  refine ⟨λ γ γS, Sn.conj p γS, λ γ₁ γ₁S γ₂ γ₂S h, _, λ δ δS, ⟨p ≫ δ ≫ (inv p), Sn.conj' p δS, _⟩⟩,
  { simpa only [inv_eq_inv, category.assoc, is_iso.hom_inv_id,
                category.comp_id, is_iso.hom_inv_id_assoc] using p ≫= h =≫ inv p },
  { simp only [inv_eq_inv, category.assoc, is_iso.inv_hom_id,
               category.comp_id, is_iso.inv_hom_id_assoc] },
end

lemma top_is_normal : is_normal (⊤ : subgroupoid C) :=
{ wide := (λ c, trivial),
  conj := (λ a b c d e, trivial) }

lemma Inf_is_normal (s : set $ subgroupoid C) (sn : ∀ S ∈ s, is_normal S) : is_normal (Inf s) :=
{ wide := by { simp_rw [Inf, mem_Inter₂], exact λ c S Ss, (sn S Ss).wide c },
  conj := by { simp_rw [Inf, mem_Inter₂], exact λ c d p γ hγ S Ss, (sn S Ss).conj p (hγ S Ss) } }

lemma is_normal.vertex_subgroup (Sn : is_normal S) (c : C) (cS : c ∈ S.objs) :
  (S.vertex_subgroup cS).normal :=
{ conj_mem := λ x hx y, by { rw mul_assoc, exact Sn.conj' y hx } }

section generated_subgroupoid

-- TODO: proof that generated is just "words in X" and generated_normal is similarly
variable (X : ∀ c d : C, set (c ⟶ d))

/-- The subgropoid generated by the set of arrows `X` -/
def generated : subgroupoid C :=
Inf {S : subgroupoid C | ∀ c d, X c d ⊆ S.arrows c d}

/-- The normal sugroupoid generated by the set of arrows `X` -/
def generated_normal : subgroupoid C :=
Inf {S : subgroupoid C | (∀ c d, X c d ⊆ S.arrows c d) ∧ S.is_normal}

lemma generated_normal_is_normal : (generated_normal X).is_normal :=
Inf_is_normal _ (λ S h, h.right)

end generated_subgroupoid

section hom

variables {D : Type*} [groupoid D] (φ : C ⥤ D)

/--
A functor between groupoid defines a map of subgroupoids in the reverse direction
by taking preimages.
 -/
def comap (S : subgroupoid D) : subgroupoid C :=
{ arrows := λ c d, {f : c ⟶ d | φ.map f ∈ S.arrows (φ.obj c) (φ.obj d)},
  inv := λ c d p hp, by { rw [mem_set_of, inv_eq_inv, φ.map_inv p, ← inv_eq_inv], exact S.inv hp },
  mul := begin
    rintros,
    simp only [mem_set_of, functor.map_comp],
    apply S.mul; assumption,
  end }

lemma comap_mono (S T : subgroupoid D) :
  S ≤ T → comap φ S ≤ comap φ T := λ ST ⟨c,d,p⟩, @ST ⟨_,_,_⟩

lemma is_normal_comap {S : subgroupoid D} (Sn : is_normal S) : is_normal (comap φ S) :=
{ wide := λ c, by { rw [comap, mem_set_of, functor.map_id], apply Sn.wide, },
  conj := λ c d f γ hγ, begin
    simp only [comap, mem_set_of, functor.map_comp, functor.map_inv, inv_eq_inv],
    rw [←inv_eq_inv],
    exact Sn.conj _ hγ,
  end }

/-- The kernel of a functor between subgroupoid is the preimage. -/
def ker : subgroupoid C := comap φ discrete

lemma mem_ker_iff {c d : C} (f : c ⟶ d) :
  f ∈ (ker φ).arrows c d ↔ ∃ (h : φ.obj c = φ.obj d), φ.map f = eq_to_hom h :=
mem_discrete_iff (φ.map f)

/-- The family of arrows of the image of a subgroupoid under a functor injective on objects -/
inductive map.arrows (hφ : function.injective φ.obj) (S : subgroupoid C) :
  Π (c d : D), (c ⟶ d) → Prop
| im {c d : C} (f : c ⟶ d) (hf : f ∈ S.arrows c d) : map.arrows (φ.obj c) (φ.obj d) (φ.map f)

lemma map.mem_arrows_iff (hφ : function.injective φ.obj) (S : subgroupoid C) {c d : D} (f : c ⟶ d):
  map.arrows φ hφ S c d f ↔
  ∃ (a b : C) (g : a ⟶ b) (ha : φ.obj a = c) (hb : φ.obj b = d) (hg : g ∈ S.arrows a b),
    f = (eq_to_hom ha.symm) ≫ φ.map g ≫ (eq_to_hom hb) :=
begin
  split,
  { rintro ⟨a,b,g,hg⟩, exact ⟨a,b,g,rfl,rfl,hg, eq_conj_eq_to_hom _⟩ },
  { rintro ⟨a,b,g,rfl,rfl,hg,rfl⟩, rw ← eq_conj_eq_to_hom, split, exact hg },
end

/-- The "forward" image of a subgroupoid under a functor injective on objects -/
def map (hφ : function.injective φ.obj) (S : subgroupoid C) : subgroupoid D :=
{ arrows := map.arrows φ hφ S,
  inv := begin
    rintro _ _ _ ⟨⟩,
    rw [inv_eq_inv, ←functor.map_inv, ←inv_eq_inv],
    split, apply S.inv, assumption,
  end,
  mul := begin
    rintro _ _ _ _ ⟨c₁,c₂,f,hf⟩ q hq,
    obtain ⟨c₃,c₄,g,he,rfl,hg,gq⟩ := (map.mem_arrows_iff φ hφ S q).mp hq,
    cases hφ he, rw [gq, ← eq_conj_eq_to_hom, ← φ.map_comp],
    split, exact S.mul hf hg,
  end }

lemma map_mono (hφ : function.injective φ.obj) (S T : subgroupoid C) :
  S ≤ T → map φ hφ S ≤ map φ hφ T :=
by { rintros ST ⟨c,d,f⟩ ⟨_,_,_,h⟩, split, exact @ST ⟨_,_,_⟩ h }

/-- The image of a functor injective on objects -/
def im (hφ : function.injective φ.obj) := map φ hφ (⊤)

lemma mem_im_iff (hφ : function.injective φ.obj) {c d : D} (f : c ⟶ d) :
  f ∈ (im φ hφ).arrows c d ↔
  ∃ (a b : C) (g : a ⟶ b) (ha : φ.obj a = c) (hb : φ.obj b = d),
    f = (eq_to_hom ha.symm) ≫ φ.map g ≫ (eq_to_hom hb) :=
by { convert map.mem_arrows_iff φ hφ ⊤ f, simp only [has_top.top, mem_univ, exists_true_left] }

end hom

end subgroupoid

end category_theory
