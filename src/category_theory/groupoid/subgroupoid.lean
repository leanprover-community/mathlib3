/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
import category_theory.groupoid.vertex_group
import category_theory.groupoid
import category_theory.groupoid.basic
--import category_theory.groupoid.free_groupoid
import algebra.group.defs
import algebra.hom.group
import algebra.hom.equiv
import data.set.lattice
import combinatorics.quiver.connected_component
import combinatorics.quiver.subquiver
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

open set classical function
local attribute [instance] prop_decidable

namespace category_theory

namespace groupoid

universes u v

variables {C : Type u} [groupoid C]

/--
A sugroupoid of `C` consists of a choice of arrows for each pair of vertices, closed
under composition and inverses
-/
@[ext] structure subgroupoid (C : Type u) [groupoid C] :=
(arrows : ∀ (c d : C), set (c ⟶ d))
(inv' : ∀ {c d} {p : c ⟶ d} (hp : p ∈ arrows c d),
          groupoid.inv p ∈ arrows d c)
(mul' : ∀ {c d e} {p} (hp : p ∈ arrows c d) {q} (hq : q ∈ arrows d e),
          p ≫ q ∈ arrows c e)


namespace subgroupoid

abbreviation mem_subgroupoid {c d : C} (f : c ⟶ d) (S : subgroupoid C) : Prop := f ∈ S.arrows c d
infix ` ∈ₐ `:50 := mem_subgroupoid

@[simp] lemma mem_subgroupoid_iff {c d : C} (f : c ⟶ d) (S : subgroupoid C) :
  (f ∈ₐ S) = (f ∈ S.arrows c d) := rfl

variable (S : subgroupoid C)

/-- The vertices of `C` on which `S` has non-trivial isotropy -/
def objs : set C := {c : C | (S.arrows c c).nonempty}

lemma id_mem_of_nonempty_isotropy (c : C) :
  c ∈ S.objs → 𝟙 c ∈ₐ S :=
begin
  rintro ⟨γ,hγ⟩,
  convert S.mul' hγ (S.inv' hγ),
  simp only [inv_eq_inv, is_iso.hom_inv_id],
end

/-- A subgroupoid seen as a quiver on vertex set `C` -/
def as_wide_quiver : quiver C := ⟨λ c d, subtype $ S.arrows c d⟩

/-- A subgroupoid as a groupoid -/
instance subgroupoid_groupoid : groupoid S.objs :=
{ hom := λ a b, S.arrows a.val b.val,
  id := λ a, ⟨𝟙 a.val, id_mem_of_nonempty_isotropy S a.val a.prop⟩,
  comp := λ a b c p q, ⟨p.val ≫ q.val, S.mul' p.prop q.prop⟩,
  id_comp' := λ a b ⟨p,hp⟩, by simp only [category.id_comp],
  comp_id' := λ a b ⟨p,hp⟩, by simp only [category.comp_id],
  assoc' := λ a b c d ⟨p,hp⟩ ⟨q,hq⟩ ⟨r,hr⟩, by simp only [category.assoc],
  inv := λ a b p, ⟨inv p.val, S.inv' p.prop⟩,
  inv_comp' := λ a b ⟨p,hp⟩, by simp only [inv_comp],
  comp_inv' := λ a b ⟨p,hp⟩, by simp only [comp_inv] }

/-- There is an embedding of the coerced subgroupoid to its parent-/
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
  mul_mem' := λ f g hf hg, S.mul' hf hg,
  one_mem' := id_mem_of_nonempty_isotropy _ _ hc,
  inv_mem' := λ f hf, S.inv' hf }

/-- A subgroupoid seen as a set of arrows -/
def coe_set (S : subgroupoid C) : set (Σ (c d : C), c ⟶ d) := {F | F.2.2 ∈ S.arrows F.1 F.2.1 }

private lemma mem_coe_set_iff' (S : subgroupoid C) {c d : C} (f : c ⟶ d) :
  (⟨c,d,f⟩ : Σ (c d : C), c ⟶ d) ∈ S.coe_set ↔ f ∈ S.arrows c d := by refl

instance : set_like (subgroupoid C) (Σ (c d : C), c ⟶ d) :=
{ coe := coe_set,
  coe_injective' := λ S T h, by
  { ext c d f, simp_rw [←mem_coe_set_iff',h], } }

@[simp] lemma mem_coe_set_iff (S : subgroupoid C) {c d : C} (f : c ⟶ d) :
  (⟨c,d,f⟩ : Σ (c d : C), c ⟶ d) ∈ S ↔ f ∈ S.arrows c d := mem_coe_set_iff' S f

@[simp] lemma le_iff (S T : subgroupoid C) : (S ≤ T) ↔ (∀ {c d}, (S.arrows c d) ⊆ (T.arrows c d)) :=
begin
  split,
  { rintro h c d f, simp only [←mem_coe_set_iff], apply h, },
  { rintro h ⟨c,d,f⟩, simp only [mem_coe_set_iff], apply h, },
end

instance : has_top (subgroupoid C) :=
⟨ { arrows := (λ _ _, set.univ),
    mul'   := by { rintros, trivial, },
    inv'   := by { rintros, trivial, } } ⟩
instance : has_bot (subgroupoid C) :=
⟨ { arrows := (λ _ _, ∅),
    mul'   := by { rintros, exfalso, assumption, },
    inv'   := by { rintros, exfalso, assumption, } } ⟩

instance : inhabited (subgroupoid C) := ⟨⊤⟩

instance : has_inf (subgroupoid C) :=
⟨ λ S T,
  { arrows := (λ c d, (S.arrows c d) ∩ (T.arrows c d)),
    inv'   := by { rintros, exact ⟨S.inv' hp.1, T.inv' hp.2⟩, },
    mul'   := by { rintros, exact ⟨S.mul' hp.1 hq.1, T.mul' hp.2 hq.2⟩, } } ⟩

instance : has_Inf (subgroupoid C) :=
⟨ λ s,
{ arrows := λ c d, ⋂ S ∈ s, (subgroupoid.arrows S c d),
  inv' := by { intros, rw mem_Inter₂ at hp ⊢, exact λ S hS, S.inv' (hp S hS) },
  mul' := by { intros, rw mem_Inter₂ at hp hq ⊢,exact λ S hS, S.mul' (hp S hS) (hq S hS) } } ⟩


instance : complete_lattice (subgroupoid C) :=
{ bot          := (⊥),
  bot_le       := λ S, empty_subset _,
  top          := (⊤),
  le_top       := λ S, subset_univ _,
  inf          := (⊓),
  le_inf       := λ R S T RS RT _ h, ⟨RS h, RT h⟩,
  inf_le_left  := λ R S _ pRS, pRS.left,
  inf_le_right := λ R S _ pRS, pRS.right,
  .. complete_lattice_of_Inf (subgroupoid C)
       ( by
        { dsimp only [Inf], rintro s, constructor,
          { rintro S Ss ⟨c,d,f⟩,
            simp only [Inter_coe_set, mem_Inter, mem_coe_set_iff],
            exact λ hp, hp S Ss, },
          { rintro T Tl ⟨c,d,f⟩ fT,
            simp only [Inter_coe_set, mem_Inter, mem_coe_set_iff],
            exact λ S Ss, (Tl Ss) fT, }}) }

lemma le_objs {S T : subgroupoid C} (h : S ≤ T) : S.objs ⊆ T.objs :=
λ s ⟨γ, hγ⟩, ⟨γ, by { rw ←mem_coe_set_iff at hγ ⊢, exact h hγ, }⟩

/-- The functor associated to the embedding of subgroupoids -/
def inclusion {S T : subgroupoid C} (h : S ≤ T) : S.objs ⥤ T.objs :=
{ obj := λ s, ⟨s.val, le_objs h s.prop⟩,
  map := λ s t f, ⟨f.val, by { rw ←mem_coe_set_iff, apply h, rw mem_coe_set_iff, exact f.prop, } ⟩,
  map_id' := λ _, rfl,
  map_comp' := λ _ _ _ _ _, rfl }

lemma inclusion_inj_on_objects {S T : subgroupoid C} (h : S ≤ T) :
  function.injective (inclusion h).obj :=
begin
  rintros ⟨s,hs⟩ ⟨t,ht⟩ he,
  simp only [inclusion, subtype.mk_eq_mk] at he ⊢,
  exact he,
end

lemma inclusion_faithful {S T : subgroupoid C} (h : S ≤ T) (s t : S.objs):
  function.injective (λ (f : s ⟶ t), (inclusion h).map f) :=
begin
  dsimp only [inclusion],
  rintros ⟨f,hf⟩ ⟨g,hg⟩ he,
  simp only [subtype.mk_eq_mk] at he ⊢,
  exact he,
end

lemma inclusion_refl {S : subgroupoid C} : inclusion (le_refl S) = 𝟭 S.objs :=
begin
  dsimp only [inclusion],
  fapply functor.ext,
  { rintros,
    simp only [subtype.val_eq_coe, subtype.coe_eta, functor.id_obj], },
  { rintros ⟨s,hs⟩ ⟨t,ht⟩ ⟨f,hf⟩,
    simp only [eq_to_hom_refl, functor.id_map, category.comp_id, category.id_comp,
               subtype.mk_eq_mk], }
end

lemma inclusion_trans {R S T : subgroupoid C} (k : R ≤ S) (h : S ≤ T) :
  inclusion (k.trans h) = (inclusion k) ⋙ (inclusion h) := rfl

lemma inclusion_comp_embedding {S T : subgroupoid C} (h : S ≤ T) :
  (inclusion h) ⋙ T.hom = S.hom := rfl

/-- The family of arrows of the full subgroupoid on vertex set `V` -/
inductive full_on.arrows (V : set C) : Π (c d : C), (c ⟶ d) → Prop
| intro {c : C} (hc : c ∈ V) {d : C} (hd : d ∈ V) (f : c ⟶ d) : full_on.arrows c d f

@[simp] lemma full_on.mem_arrows_iff (V : set C) {c d : C} (f : c ⟶ d) :
  full_on.arrows V c d f ↔ c ∈ V ∧ d ∈ V :=
begin
  split,
  { rintros ⟨c,hc,d,hd,f⟩, exact ⟨hc,hd⟩, },
  { rintros ⟨hc,hd⟩, constructor; assumption, },
end

/-- The full subgroupoid on vertex set `V` -/
def full_on (V : set C) : subgroupoid C :=
⟨ full_on.arrows V,
  by { rintros, induction hp, constructor; assumption, },
  by { rintros, induction hp, induction hq, constructor; assumption } ⟩

/-- The family of arrows of the discrete groupoid -/
inductive discrete.arrows : Π (c d : C), (c ⟶ d) → Prop
| id (c : C) : discrete.arrows c c (𝟙 c)

/-- The only arrows of the discrete subgroupoid are the identity arrows-/
def discrete : subgroupoid C :=
{ arrows := discrete.arrows,
  inv' := by
  { rintros _ _ _ hp, induction hp, simp only [inv_eq_inv, is_iso.inv_id], constructor, },
  mul' := by
  { rintros _ _ _ _ hp _ hq, induction hp, induction hq, rw category.comp_id, constructor,} }

lemma mem_discrete_iff {c d : C} (f : c ⟶ d):
  (f ∈ (discrete).arrows c d) ↔ (∃ (h : c = d), f = eq_to_hom h) :=
begin
  split,
  { intro hf, induction hf, simp only [eq_self_iff_true, exists_true_left, eq_to_hom_refl], },
  { rintro ⟨h,he⟩, subst_vars, constructor, }
end

section normal

/-- A subgroupoid is normal if it is “wide” (meaning that its.obj set is all of `C`)
    and satisfies the expected stability under conjugacy -/
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
  split,
  { rintro γ γS, apply Sn.conj, exact γS },
  split,
  { rintro γ₁ γ₁S γ₂ γ₂S h,
    let := p ≫=(h =≫ (inv p)),
    simp only [inv_eq_inv, category.assoc, is_iso.hom_inv_id, category.comp_id,
               is_iso.hom_inv_id_assoc] at this ⊢,
    exact this, }, -- what's the quickest way here?
  { rintro δ δS, use (p ≫ δ ≫ (inv p)), split,
    { have : p = inv (inv p), by {simp only [inv_eq_inv, is_iso.inv_inv]},
      nth_rewrite 0 this,
      apply Sn.conj, exact δS, },
    { simp only [category.assoc, inv_comp, category.comp_id],
      simp only [←category.assoc, inv_comp, category.id_comp], }}
end

lemma top_is_normal : is_normal (⊤ : subgroupoid C) :=
{ wide := (λ c, trivial),
  conj := (λ a b c d e, trivial) }

lemma discrete_is_normal : is_normal (discrete : subgroupoid C) :=
{ wide := (λ c, discrete.arrows.id c),
  conj := (λ a b f d e , by
  { simp only [mem_discrete_iff, eq_self_iff_true, inv_eq_inv, is_iso.inv_comp_eq,
               category.comp_id, exists_true_left] at e ⊢,
    simp only [e, category.id_comp, eq_to_hom_refl, category.comp_id], }) }

lemma Inf_is_normal (s : set $ subgroupoid C) (sn : ∀ S ∈ s, is_normal S) : is_normal (Inf s) :=
{ wide := by
  { simp only [Inf, mem_Inter],
    exact λ c S Ss, (sn S Ss).wide c, },
  conj := by
  { simp only [Inf, mem_Inter],
    exact λ c d p γ hγ S Ss, (sn S Ss).conj p (hγ S Ss), } }

lemma is_normal.vertex_subgroup (Sn : is_normal S) (c : C) (cS : c ∈ S.objs) :
  (S.vertex_subgroup cS).normal :=
begin
  constructor,
  rintros x hx y,
  simp only [vertex_group_mul, vertex_group.inv_eq_inv, category.assoc],
  have : y = inv (inv y), by { simp only [inv_eq_inv, is_iso.inv_inv], },
  nth_rewrite 0 this,
  simp only [←inv_eq_inv],
  apply Sn.conj, exact hx,
end

end normal


section graph_like

abbreviation is_graph_like := is_graph_like S.objs

lemma is_graph_like_iff : S.is_graph_like ↔ ∀ c d, subsingleton (S.arrows c d) := sorry

end graph_like

section disconnected

abbreviation is_disconnected := is_disconnected S.objs

lemma is_disconnected_iff : S.is_disconnected ↔ ∀ c d, c ≠ d → is_empty (S.arrows c d) := sorry

/-- The arrow set of `disconnect`, which drops all arrows but the loops -/
inductive disconnect.arrows : Π  (c d : C), (c ⟶ d) → Prop
| vert {c : C} {γ : c ⟶ c} :  disconnect.arrows c c γ

lemma disconnect.mem_arrows_iff {c d : C} (f : c ⟶ d) :
  disconnect.arrows c d f ↔  c = d :=
begin
  split,
  { rintros ⟨c,γ⟩, simp only [eq_self_iff_true, exists_true_left], },
  { rintro rfl, constructor, },
end

/-- Only keep the loops of `S` -/
def _root_.category_theory.groupoid.disconnect (C) [groupoid C] : subgroupoid C :=
⟨ disconnect.arrows,
  λ _ _ f hf, by {induction hf, constructor, },
  λ _ _ _ f hf g hg, by
  { induction hf, induction hg, constructor, }⟩

lemma disconnect_is_disconnected : groupoid.is_disconnected (disconnect C).objs :=
begin
  rintro c d ne, by_contradiction,
  simp only [coe_groupoid_to_category_hom, is_empty_coe_sort] at h,
  sorry,
end

lemma disconnect_is_normal_of_normal (Sn : is_normal S) : (disconnect S.objs).is_normal := sorry

end disconnected

section hom

variables {D : Type*} [groupoid D] (φ : C ⥤ D)

section comap

variables (T U : subgroupoid D)

/--
A functor between groupoid defines a map of subgroupoids in the reverse direction
by taking preimages.
 -/
def comap (S : subgroupoid D) : subgroupoid C :=
{ arrows := λ c d, {f : c ⟶ d | φ.map f ∈ S.arrows (φ.obj c) (φ.obj d)},
  inv'   := by
  { rintros,
    simp only [inv_eq_inv, mem_set_of_eq, functor.map_inv],
    simp only [←inv_eq_inv],
    simp only [mem_set_of_eq] at hp,
    apply S.inv', assumption, },
  mul'   := by
  { rintros,
    simp only [mem_set_of_eq, functor.map_comp],
    apply S.mul';
    assumption, } }


lemma comap_mono (S T : subgroupoid D) :
  S ≤ T → comap φ S ≤ comap φ T :=
λ ST ⟨c,d,p⟩, by { simp only [mem_coe_set_iff, le_iff] at ST ⊢, exact λ h, ST h, }

lemma is_normal_comap {T} (Tn : is_normal T) : is_normal (comap φ T) :=
{ wide := by
  { rintro c,
    dsimp only [comap],
    simp only [mem_set_of_eq, functor.map_id],
    apply Tn.wide, },
  conj := by
  { rintros c d f γ hγ,
    dsimp only [comap],
    simp only [mem_set_of_eq, functor.map_comp, functor.map_inv, inv_eq_inv],
    rw [←inv_eq_inv],
    apply Tn.conj, exact hγ, } }

/-- The kernel of a functor between subgroupoid is the preimage. -/
def ker : subgroupoid C := comap φ (discrete)

lemma ker_is_normal : (ker φ).is_normal :=
begin
  apply is_normal_comap,
  exact discrete_is_normal,
end

lemma mem_ker_iff {c d : C} (f : c ⟶ d) :
  f ∈ (ker φ).arrows c d ↔ ∃ (h : φ.obj c = φ.obj d), φ.map f = eq_to_hom h :=
mem_discrete_iff (φ.map f)

end comap

section map

variables (hφ : function.injective φ.obj) (S)

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
  { rintro ⟨a,b,g,hg⟩,
    use [a,b,g,rfl,rfl,hg],
    simp only [eq_to_hom_refl, category.comp_id, category.id_comp], },
  { rintro ⟨a,b,g,ha,hb,hg,he⟩, subst_vars,
    simp only [eq_to_hom_refl, category.comp_id, category.id_comp],
    constructor, exact hg, },
end

/-- The "forward" image of a subgroupoid under a functor injective on objects -/
def map (hφ : function.injective φ.obj) (S : subgroupoid C) : subgroupoid D :=
{ arrows := map.arrows φ hφ S,
  inv'   := by
  { rintro _ _ _ hp, induction hp,
    rw [inv_eq_inv,←functor.map_inv], constructor,
    rw ←inv_eq_inv, apply S.inv', assumption, },
  mul'   := by -- Is there no way to prove this ↓ directly without the help of `map.mem_arrows_iff`?
  { rintro _ _ _ _ hp _ hq,
    obtain ⟨f₀,f₁,f,hf₀,hf₁,hf,fp⟩ := (map.mem_arrows_iff φ hφ S p).mp hp,
    obtain ⟨g₀,g₁,g,hg₀,hg₁,hg,gq⟩ := (map.mem_arrows_iff φ hφ S q).mp hq,
    simp only [has_mem.mem, map.mem_arrows_iff],
    have : f₁ = g₀, by {apply hφ, exact hf₁.trans hg₀.symm, },
    induction this,
    refine ⟨f₀,g₁,f ≫ g,hf₀,hg₁,S.mul' hf hg,_⟩,
    subst_vars,
    simp only [eq_to_hom_refl, category.id_comp, category.assoc, functor.map_comp], } }

lemma map_mono (S T : subgroupoid C) :
  S ≤ T → map φ hφ S ≤ map φ hφ T :=
begin
  rintros ST ⟨c,d,f⟩,
  simp only [mem_coe_set_iff, le_iff] at ST ⊢,
  rintro ⟨_,_,_,h⟩,
  constructor,
  exact ST h,
end

/-- The image of a functor injective on objects -/
def im (hφ : function.injective φ.obj) := map φ hφ (⊤)

lemma mem_im_iff (hφ : function.injective φ.obj) {c d : D} (f : c ⟶ d) :
  f ∈ (im φ hφ).arrows c d ↔
  ∃ (a b : C) (g : a ⟶ b) (ha : φ.obj a = c) (hb : φ.obj b = d),
    f = (eq_to_hom ha.symm) ≫ φ.map g ≫ (eq_to_hom hb) :=
begin
  convert map.mem_arrows_iff φ hφ ⊤ f,
  dsimp [⊤,has_top.top],
  simp only [mem_univ, exists_true_left],
end

lemma is_normal_map (hφs : im φ hφ = ⊤) :  S.is_normal → (map φ hφ S).is_normal := sorry

lemma is_graph_like_im : groupoid.is_graph_like C →  (im φ hφ).is_graph_like := sorry

lemma is_disconnected_im : groupoid.is_disconnected C → (im φ hφ).is_disconnected := sorry

end map

end hom

section generated_subgroupoid

-- TODO: proof that generated is just "words in X" and generated_normal is similarly
variable (X : ∀ (c d : C), set (c ⟶ d))

/-- The subgropoid generated by the set of arrows `X` -/
def generated : subgroupoid C :=
  Inf {S : subgroupoid C | ∀ c d, X c d ⊆ S.arrows c d}

lemma generated_contains : ∀ c d, X c d ⊆ (generated X).arrows c d := sorry

lemma generated_le_of_containing : (∀ c d, X c d ⊆ S.arrows c d) → (generated X) ≤ S :=
  @Inf_le (subgroupoid C) _ {S : subgroupoid C | ∀ c d, X c d ⊆ S.arrows c d} S


def as_quiver := {c : C // ∃ d, (X c d).nonempty ∨ (X d c).nonempty }
instance as_quiver_quiver : quiver (as_quiver X) := ⟨λ c d, subtype $ X c.val d.val⟩
def incl : prefunctor (as_quiver X) C :=
{ obj := λ c, c.val,
  map := λ c d f, f.val }

lemma incl_injective : function.injective (incl X).obj := by
{ rintros x y he, ext, exact he, }
lemma incl_faithful {x y : as_quiver X} : function.injective (λ (f : x ⟶ y), (incl X).map f) := by
{ rintros f g he, ext, exact he, }

/-
lemma generated_is_lift_free_groupoid :
  (generated X) = im (free.lift (incl X)) (free.lift_of_injective (incl X) $ incl_injective X) :=
begin
  apply le_antisymm,
  { apply generated_le_of_containing,
    rintro c d f hf, dsimp [im, map],
    let cc := (@free.of (as_quiver X) _).obj (⟨c, ⟨d, by {left, constructor, exact hf}⟩⟩ : as_quiver X),
    let dd := (@free.of (as_quiver X) _).obj (⟨d, ⟨c, by {right, constructor, exact hf}⟩⟩ : as_quiver X),
    let ff : cc ⟶ dd :=  (@free.of (as_quiver X) _).map ⟨f,hf⟩,

    have ccc : c = (free.lift $ incl X).obj cc, by sorry,
    have ddd : d = (free.lift $ incl X).obj dd, by sorry,
    have fff : f = (free.lift $ incl X).map ff, by sorry,
    rw fff,
    dsimp [free.lift,incl,quotient.lift,paths.lift,quiver.symmetrify.lift,⊤] at *,
    sorry




     }
end
-/

/-- The normal sugroupoid generated by the set of arrows `X` -/
def generated_normal : subgroupoid C :=
  Inf {S : subgroupoid C | (∀ c d, X c d ⊆ S.arrows c d) ∧ S.is_normal }

lemma generated_normal_is_normal : (generated_normal X).is_normal :=
Inf_is_normal _ (λ S h, h.right)

lemma generated_normal_le_of_containing_normal (Sn : S.is_normal) :
  (∀ c d, X c d ⊆ S.arrows c d) → (generated_normal X) ≤ S :=
begin
  rintro h,
  apply @Inf_le (subgroupoid C) _,
  exact ⟨h,Sn⟩,
end


end generated_subgroupoid


end subgroupoid

end groupoid

end category_theory
