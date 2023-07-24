/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli, Junyan Xu
-/
import category_theory.groupoid.vertex_group
import category_theory.groupoid.basic
import category_theory.groupoid
import algebra.group.defs
import data.set.lattice
import group_theory.subgroup.basic
import order.galois_connection
/-!
# Subgroupoid

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines subgroupoids as `structure`s containing the subsets of arrows and their
stability under composition and inversion.
Also defined are:

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
* Prove that `full` and `disconnect` preserve intersections (and `disconnect` also unions)

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

lemma inv_mem_iff {c d : C} (f : c ⟶ d) : inv f ∈ S.arrows d c ↔ f ∈ S.arrows c d :=
begin
  split,
  { rintro h,
    suffices : inv (inv f) ∈ S.arrows c d,
    { simpa only [inv_eq_inv, is_iso.inv_inv] using this, },
    { apply S.inv h, }, },
  { apply S.inv, },
end

lemma mul_mem_cancel_left {c d e : C} {f : c ⟶ d} {g : d ⟶ e} (hf : f ∈ S.arrows c d) :
  f ≫ g ∈ S.arrows c e ↔ g ∈ S.arrows d e :=
begin
  split,
  { rintro h,
    suffices : (inv f) ≫ f ≫ g ∈ S.arrows d e,
    { simpa only [inv_eq_inv, is_iso.inv_hom_id_assoc] using this, },
    { apply S.mul (S.inv hf) h, }, },
  { apply S.mul hf, },
end

lemma mul_mem_cancel_right {c d e : C} {f : c ⟶ d} {g : d ⟶ e} (hg : g ∈ S.arrows d e) :
  f ≫ g ∈ S.arrows c e ↔ f ∈ S.arrows c d :=
begin
  split,
  { rintro h,
    suffices : (f ≫ g) ≫ (inv g) ∈ S.arrows c d,
    { simpa only [inv_eq_inv, is_iso.hom_inv_id, category.comp_id, category.assoc] using this, },
    { apply S.mul h (S.inv hg), }, },
  { exact λ hf, S.mul hf hg, },
end

/-- The vertices of `C` on which `S` has non-trivial isotropy -/
def objs : set C := {c : C | (S.arrows c c).nonempty}

lemma mem_objs_of_src {c d : C} {f : c ⟶ d} (h : f ∈ S.arrows c d) : c ∈ S.objs :=
⟨f ≫ inv f, S.mul h (S.inv h)⟩

lemma mem_objs_of_tgt {c d : C} {f : c ⟶ d} (h : f ∈ S.arrows c d) : d ∈ S.objs :=
⟨(inv f) ≫ f, S.mul (S.inv h) h⟩

lemma id_mem_of_nonempty_isotropy (c : C) :
  c ∈ objs S → 𝟙 c ∈ S.arrows c c :=
begin
  rintro ⟨γ,hγ⟩,
  convert S.mul hγ (S.inv hγ),
  simp only [inv_eq_inv, is_iso.hom_inv_id],
end

lemma id_mem_of_src {c d : C} {f : c ⟶ d} (h : f ∈ S.arrows c d) : (𝟙 c) ∈ S.arrows c c :=
id_mem_of_nonempty_isotropy S c (mem_objs_of_src S h)

lemma id_mem_of_tgt {c d : C} {f : c ⟶ d} (h : f ∈ S.arrows c d) : (𝟙 d) ∈ S.arrows d d :=
id_mem_of_nonempty_isotropy S d (mem_objs_of_tgt S h)

/-- A subgroupoid seen as a quiver on vertex set `C` -/
def as_wide_quiver : quiver C := ⟨λ c d, subtype $ S.arrows c d⟩

/-- The coercion of a subgroupoid as a groupoid -/
@[simps to_category_comp_coe, simps inv_coe (lemmas_only)]
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

@[simp] lemma coe_inv_coe' {c d : S.objs} (p : c ⟶ d) :
  (category_theory.inv p).val = category_theory.inv p.val :=
by { simp only [subtype.val_eq_coe, ←inv_eq_inv, coe_inv_coe], }

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

lemma mem_top {c d : C} (f : c ⟶ d) : f ∈ (⊤ : subgroupoid C).arrows c d := trivial

lemma mem_top_objs (c : C) : c ∈ (⊤ : subgroupoid C).objs :=
by { dsimp [has_top.top,objs], simp only [univ_nonempty], }

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

lemma inclusion_faithful {S T : subgroupoid C} (h : S ≤ T) (s t : S.objs) :
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

lemma mem_discrete_iff {c d : C} (f : c ⟶ d) :
  (f ∈ (discrete).arrows c d) ↔ (∃ (h : c = d), f = eq_to_hom h) :=
⟨by { rintro ⟨⟩, exact ⟨rfl, rfl⟩ }, by { rintro ⟨rfl, rfl⟩, split }⟩

/-- A subgroupoid is wide if its carrier set is all of `C`-/
structure is_wide : Prop :=
(wide : ∀ c, (𝟙 c) ∈ (S.arrows c c))

lemma is_wide_iff_objs_eq_univ : S.is_wide ↔ S.objs = set.univ :=
begin
  split,
  { rintro h,
    ext, split; simp only [top_eq_univ, mem_univ, implies_true_iff, forall_true_left],
    apply mem_objs_of_src S (h.wide x), },
  { rintro h,
    refine ⟨λ c, _⟩,
    obtain ⟨γ,γS⟩ := (le_of_eq h.symm : ⊤ ⊆ S.objs) (set.mem_univ c),
    exact id_mem_of_src S γS, },
end

lemma is_wide.id_mem {S : subgroupoid C} (Sw : S.is_wide) (c : C) :
  (𝟙 c) ∈ S.arrows c c := Sw.wide c

lemma is_wide.eq_to_hom_mem {S : subgroupoid C} (Sw : S.is_wide) {c d : C} (h : c = d) :
  (eq_to_hom h) ∈ S.arrows c d := by
{ cases h, simp only [eq_to_hom_refl], apply Sw.id_mem c, }

/-- A subgroupoid is normal if it is wide and satisfies the expected stability under conjugacy. -/
structure is_normal extends (is_wide S) : Prop :=
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

lemma discrete_is_normal : (@discrete C _).is_normal :=
{ wide := λ c, by { constructor, },
  conj := λ c d f γ hγ, by
  { cases hγ, simp only [inv_eq_inv, category.id_comp, is_iso.inv_hom_id], constructor, } }

lemma is_normal.vertex_subgroup (Sn : is_normal S) (c : C) (cS : c ∈ S.objs) :
  (S.vertex_subgroup cS).normal :=
{ conj_mem := λ x hx y, by { rw mul_assoc, exact Sn.conj' y hx } }

section generated_subgroupoid

-- TODO: proof that generated is just "words in X" and generated_normal is similarly
variable (X : ∀ c d : C, set (c ⟶ d))

/-- The subgropoid generated by the set of arrows `X` -/
def generated : subgroupoid C :=
Inf {S : subgroupoid C | ∀ c d, X c d ⊆ S.arrows c d}

lemma subset_generated (c d : C) : X c d ⊆ (generated X).arrows c d :=
begin
  dsimp only [generated, Inf],
  simp only [subset_Inter₂_iff],
  exact λ S hS f fS, hS _ _ fS,
end

/-- The normal sugroupoid generated by the set of arrows `X` -/
def generated_normal : subgroupoid C :=
Inf {S : subgroupoid C | (∀ c d, X c d ⊆ S.arrows c d) ∧ S.is_normal}

lemma generated_le_generated_normal : generated X ≤ generated_normal X :=
begin
  apply @Inf_le_Inf (subgroupoid C) _,
  exact λ S ⟨h,_⟩, h,
end

lemma generated_normal_is_normal : (generated_normal X).is_normal :=
Inf_is_normal _ (λ S h, h.right)

lemma is_normal.generated_normal_le {S : subgroupoid C} (Sn : S.is_normal) :
  generated_normal X ≤ S ↔ ∀ c d, X c d ⊆ S.arrows c d :=
begin
  split,
  { rintro h c d,
    let h' := generated_le_generated_normal X,
    rw le_iff at h h',
    exact ((subset_generated X c d).trans (@h' c d)).trans (@h c d), },
  { rintro h,
    apply @Inf_le (subgroupoid C) _,
    exact ⟨h,Sn⟩, },
end

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
  conj := λ c d f γ hγ, by
  { simp_rw [inv_eq_inv f, comap, mem_set_of, functor.map_comp, functor.map_inv, ←inv_eq_inv],
    exact Sn.conj _ hγ, } }

@[simp] lemma comap_comp {E : Type*} [groupoid E] (ψ : D ⥤ E) :
  comap (φ ⋙ ψ) = (comap φ) ∘ (comap ψ) := rfl

/-- The kernel of a functor between subgroupoid is the preimage. -/
def ker : subgroupoid C := comap φ discrete

lemma mem_ker_iff {c d : C} (f : c ⟶ d) :
  f ∈ (ker φ).arrows c d ↔ ∃ (h : φ.obj c = φ.obj d), φ.map f = eq_to_hom h :=
mem_discrete_iff (φ.map f)

lemma ker_is_normal : (ker φ).is_normal := is_normal_comap φ (discrete_is_normal)

@[simp]
lemma ker_comp {E : Type*} [groupoid E] (ψ : D ⥤ E) : ker (φ ⋙ ψ) = comap φ (ker ψ) := rfl

/-- The family of arrows of the image of a subgroupoid under a functor injective on objects -/
inductive map.arrows (hφ : function.injective φ.obj) (S : subgroupoid C) :
  Π (c d : D), (c ⟶ d) → Prop
| im {c d : C} (f : c ⟶ d) (hf : f ∈ S.arrows c d) : map.arrows (φ.obj c) (φ.obj d) (φ.map f)

lemma map.arrows_iff (hφ : function.injective φ.obj) (S : subgroupoid C) {c d : D} (f : c ⟶ d) :
  map.arrows φ hφ S c d f ↔
  ∃ (a b : C) (g : a ⟶ b) (ha : φ.obj a = c) (hb : φ.obj b = d) (hg : g ∈ S.arrows a b),
    f = (eq_to_hom ha.symm) ≫ φ.map g ≫ (eq_to_hom hb) :=
begin
  split,
  { rintro ⟨g,hg⟩, exact ⟨_,_,g,rfl,rfl,hg, eq_conj_eq_to_hom _⟩ },
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
    rintro _ _ _ _ ⟨f,hf⟩ q hq,
    obtain ⟨c₃,c₄,g,he,rfl,hg,gq⟩ := (map.arrows_iff φ hφ S q).mp hq,
    cases hφ he, rw [gq, ← eq_conj_eq_to_hom, ← φ.map_comp],
    split, exact S.mul hf hg,
  end }

lemma mem_map_iff (hφ : function.injective φ.obj) (S : subgroupoid C) {c d : D} (f : c ⟶ d) :
  f ∈ (map φ hφ S).arrows c d ↔
  ∃ (a b : C) (g : a ⟶ b) (ha : φ.obj a = c) (hb : φ.obj b = d) (hg : g ∈ S.arrows a b),
    f = (eq_to_hom ha.symm) ≫ φ.map g ≫ (eq_to_hom hb) := map.arrows_iff φ hφ S f

lemma galois_connection_map_comap (hφ : function.injective φ.obj) :
  galois_connection (map φ hφ) (comap φ) :=
begin
  rintro S T, simp_rw [le_iff], split,
  { exact λ h c d f fS, h (map.arrows.im f fS), },
  { rintros h _ _ g ⟨a,gφS⟩,
    exact h gφS, },
end

lemma map_mono (hφ : function.injective φ.obj) (S T : subgroupoid C) :
  S ≤ T → map φ hφ S ≤ map φ hφ T :=
λ h, (galois_connection_map_comap φ hφ).monotone_l h

lemma le_comap_map (hφ : function.injective φ.obj) (S : subgroupoid C) :
  S ≤ comap φ (map φ hφ S) := (galois_connection_map_comap φ hφ).le_u_l S

lemma map_comap_le (hφ : function.injective φ.obj) (T : subgroupoid D) :
  map φ hφ (comap φ T) ≤ T := (galois_connection_map_comap φ hφ).l_u_le T

lemma map_le_iff_le_comap (hφ : function.injective φ.obj)
  (S : subgroupoid C) (T : subgroupoid D) :
  map φ hφ S ≤ T ↔ S ≤ comap φ T := (galois_connection_map_comap φ hφ).le_iff_le

lemma mem_map_objs_iff (hφ : function.injective φ.obj) (d : D) :
  d ∈ (map φ hφ S).objs ↔ ∃ c ∈ S.objs, φ.obj c = d :=
begin
  dsimp [objs, map],
  split,
  { rintro ⟨f,hf⟩,
    change map.arrows φ hφ S d d f at hf, rw map.arrows_iff at hf,
    obtain ⟨c,d,g,ec,ed,eg,gS,eg⟩ := hf,
    exact ⟨c, ⟨mem_objs_of_src S eg, ec⟩⟩, },
  { rintros ⟨c,⟨γ,γS⟩,rfl⟩,
    exact ⟨φ.map γ,⟨γ,γS⟩⟩, }
end

@[simp]
lemma map_objs_eq (hφ : function.injective φ.obj) : (map φ hφ S).objs = φ.obj '' S.objs :=
by { ext, convert mem_map_objs_iff S φ hφ x, simp only [mem_image, exists_prop], }

/-- The image of a functor injective on objects -/
def im (hφ : function.injective φ.obj) := map φ hφ (⊤)

lemma mem_im_iff (hφ : function.injective φ.obj) {c d : D} (f : c ⟶ d) :
  f ∈ (im φ hφ).arrows c d ↔
  ∃ (a b : C) (g : a ⟶ b) (ha : φ.obj a = c) (hb : φ.obj b = d),
    f = (eq_to_hom ha.symm) ≫ φ.map g ≫ (eq_to_hom hb) :=
by { convert map.arrows_iff φ hφ ⊤ f, simp only [has_top.top, mem_univ, exists_true_left] }

lemma mem_im_objs_iff (hφ : function.injective φ.obj) (d : D) :
  d ∈ (im φ hφ).objs ↔ ∃ c : C, φ.obj c = d := by
{ simp only [im, mem_map_objs_iff, mem_top_objs, exists_true_left], }

lemma obj_surjective_of_im_eq_top (hφ : function.injective φ.obj) (hφ' : im φ hφ = ⊤) :
  function.surjective φ.obj :=
begin
  rintro d,
  rw [←mem_im_objs_iff, hφ'],
  apply mem_top_objs,
end

lemma is_normal_map (hφ : function.injective φ.obj) (hφ' : im φ hφ = ⊤) (Sn : S.is_normal) :
  (map φ hφ S).is_normal :=
{ wide := λ d, by
  { obtain ⟨c,rfl⟩ := obj_surjective_of_im_eq_top φ hφ hφ' d,
    change map.arrows φ hφ S _ _ (𝟙 _), rw ←functor.map_id,
    constructor, exact Sn.wide c, },
  conj := λ d d' g δ hδ, by
  { rw mem_map_iff at hδ,
    obtain ⟨c,c',γ,cd,cd',γS,hγ⟩ := hδ, subst_vars, cases hφ cd',
    have : d' ∈ (im φ hφ).objs, by { rw hφ', apply mem_top_objs, },
    rw mem_im_objs_iff at this,
    obtain ⟨c',rfl⟩ := this,
    have : g ∈ (im φ hφ).arrows (φ.obj c) (φ.obj c'), by
    { rw hφ', trivial, },
    rw mem_im_iff at this,
    obtain ⟨b,b',f,hb,hb',_,hf⟩ := this, subst_vars, cases hφ hb, cases hφ hb',
    change map.arrows φ hφ S (φ.obj c') (φ.obj c') _,
    simp only [eq_to_hom_refl, category.comp_id, category.id_comp, inv_eq_inv],
    suffices : map.arrows φ hφ S (φ.obj c') (φ.obj c') (φ.map $ inv f ≫ γ ≫ f),
    { simp only [inv_eq_inv, functor.map_comp, functor.map_inv] at this, exact this, },
    { constructor, apply Sn.conj f γS, } } }

end hom

section thin

/-- A subgroupoid `is_thin` if it has at most one arrow between any two vertices. -/
abbreviation is_thin := quiver.is_thin S.objs

lemma is_thin_iff : S.is_thin ↔ ∀ (c : S.objs), subsingleton (S.arrows c c) :=
by apply is_thin_iff

end thin

section disconnected

/-- A subgroupoid `is_totally_disconnected` if it has only isotropy arrows. -/
abbreviation is_totally_disconnected := is_totally_disconnected S.objs

lemma is_totally_disconnected_iff :
  S.is_totally_disconnected ↔ ∀ c d, (S.arrows c d).nonempty → c = d :=
begin
  split,
  { rintro h c d ⟨f,fS⟩,
    rw ←@subtype.mk_eq_mk _ _ c (mem_objs_of_src S fS) d (mem_objs_of_tgt S fS),
    exact h ⟨c, mem_objs_of_src S fS⟩ ⟨d, mem_objs_of_tgt S fS⟩ ⟨f, fS⟩, },
  { rintros h ⟨c, hc⟩ ⟨d, hd⟩ ⟨f, fS⟩,
    simp only [subtype.mk_eq_mk],
    exact h c d ⟨f, fS⟩, },
end

/-- The isotropy subgroupoid of `S` -/
def disconnect : subgroupoid C :=
{ arrows := λ c d f, c = d ∧ f ∈ S.arrows c d,
  inv := by { rintros _ _ _ ⟨rfl, h⟩, exact ⟨rfl, S.inv h⟩, },
  mul := by { rintros _ _ _ _ ⟨rfl, h⟩ _ ⟨rfl, h'⟩, exact ⟨rfl, S.mul h h'⟩, } }

lemma disconnect_le : S.disconnect ≤ S :=
by { rw le_iff, rintros _ _ _ ⟨⟩, assumption, }

lemma disconnect_normal (Sn : S.is_normal) : S.disconnect.is_normal :=
{ wide := λ c, ⟨rfl, Sn.wide c⟩,
  conj := λ c d p γ ⟨_,h'⟩, ⟨rfl, Sn.conj _ h'⟩ }

@[simp] lemma mem_disconnect_objs_iff {c : C} : c ∈ S.disconnect.objs ↔ c ∈ S.objs :=
⟨λ ⟨γ, h, γS⟩, ⟨γ, γS⟩, λ ⟨γ, γS⟩, ⟨γ, rfl, γS⟩⟩

lemma disconnect_objs : S.disconnect.objs = S.objs :=
by { apply set.ext, apply mem_disconnect_objs_iff, }

lemma disconnect_is_totally_disconnected : S.disconnect.is_totally_disconnected :=
by { rw is_totally_disconnected_iff, exact λ c d ⟨f, h, fS⟩, h }

end disconnected

section full

variable (D : set C)

/-- The full subgroupoid on a set `D : set C` -/
def full : subgroupoid C :=
{ arrows := λ c d _, c ∈ D ∧ d ∈ D,
  inv := by { rintros _ _ _ ⟨⟩, constructor; assumption, },
  mul := by { rintros _ _ _ _ ⟨⟩ _ ⟨⟩, constructor; assumption,} }

lemma full_objs : (full D).objs = D :=
set.ext $ λ _, ⟨λ ⟨f, h, _⟩, h , λ h, ⟨𝟙 _, h, h⟩⟩

@[simp] lemma mem_full_iff {c d : C} {f : c ⟶ d} : f ∈ (full D).arrows c d ↔ c ∈ D ∧ d ∈ D :=
iff.rfl

@[simp] lemma mem_full_objs_iff {c : C} : c ∈ (full D).objs ↔ c ∈ D :=
by rw full_objs

@[simp] lemma full_empty : full ∅ = (⊥ : subgroupoid C) :=
by { ext, simp only [has_bot.bot, mem_full_iff, mem_empty_iff_false, and_self], }

@[simp] lemma full_univ : full set.univ = (⊤ : subgroupoid C) :=
by { ext, simp only [mem_full_iff, mem_univ, and_self, true_iff], }

lemma full_mono {D E : set C} (h : D ≤ E) : full D ≤ full E :=
begin
  rw le_iff,
  rintro c d f,
  simp only [mem_full_iff],
  exact λ ⟨hc, hd⟩, ⟨h hc, h hd⟩,
end

lemma full_arrow_eq_iff {c d : (full D).objs} {f g : c ⟶ d} :
  f = g ↔ (↑f : c.val ⟶ d.val) = ↑g :=
by apply subtype.ext_iff

end full

end subgroupoid

end category_theory
