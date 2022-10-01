/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
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
* preimages of subgroupoids under a functor;
* the notion of normality of subgroupoids and its stability under intersection and preimage;
* compatibility of the above with `groupoid.vertex_group`.


## Main definitions

Given a type `C` with associated `groupoid C` instance.

* `subgroupoid C` is the type of subgroupoids of `C`
* `subgroupoid.is_normal` is the property that the subgroupoid is stable under conjugation
  by arbitrary arrows, _and_ that all identity arrows are contained in the subgroupoid.
* `subgroupoid.comap` is the "preimage" map of subgroupoids along a functor.
* `subgroupoid.vertex_subgroup` is the subgroup of the `vertex group` at a given vertex `v`,
  assuming `v` is contained in the `subgroupoid` (meaning, by definition, that the arrow `𝟙 v`
  is contained in the subgroupoid).

## Implementation details

The structure of this file is copied from/inspired by `group_theory.subgroup.basic`
and `combinatorics.simple_graph.subgraph`.

## TODO

* Equivalent inductive characterization of generated (normal) subgroupoids.
* A "forward" image map of subgroupoids (similar to `subgroup.map`) under the hypothesis that
  the functor at hand is injective on vertices.
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
  (arrws : ∀ (c d : C), set (c ⟶ d))
  (inv' : ∀ {c d} {p : c ⟶ d} (hp : p ∈ arrws c d),
            inv p ∈ arrws d c)
  (mul' : ∀ {c d e} {p} (hp : p ∈ arrws c d) {q} (hq : q ∈ arrws d e),
            p ≫ q ∈ arrws c e)

namespace subgroupoid

variable (S : subgroupoid C)

/-- The vertices of `C` on which `S` has non-trivial isotropy -/
def carrier : set C := {c : C | (S.arrws c c).nonempty }

lemma id_mem_of_nonempty_isotropy (c : C) :
  c ∈ carrier S → 𝟙 c ∈ S.arrws c c :=
begin
  rintro ⟨γ,hγ⟩,
  have : 𝟙 c = γ * (inv γ), by simp only [vertex_group_mul, comp_inv],
  rw this,
  apply S.mul' hγ (S.inv' hγ),
end

/-- A subgroupoid seen as a quiver on vertex set `C` -/
def as_wide_quiver : quiver C := ⟨λ c d, subtype $ S.arrws c d⟩

/-- The coercion of a subgroupoid as a groupoid -/
def coe : groupoid (S.carrier) :=
{ to_category :=
  { to_category_struct :=
    { to_quiver :=
      { hom := λ a b, S.arrws a.val b.val }
    , id := λ a, ⟨𝟙 a.val, id_mem_of_nonempty_isotropy S a.val a.prop⟩
    , comp := λ a b c p q, ⟨p.val ≫ q.val, S.mul' p.prop q.prop⟩, }
  , id_comp' := λ a b ⟨p,hp⟩, by simp only [category.id_comp]
  , comp_id' := λ a b ⟨p,hp⟩, by simp only [category.comp_id]
  , assoc' := λ a b c d ⟨p,hp⟩ ⟨q,hq⟩ ⟨r,hr⟩, by simp only [category.assoc] }
, inv := λ a b p, ⟨inv p.val, S.inv' p.prop⟩
, inv_comp' := λ a b ⟨p,hp⟩, by simp only [inv_comp]
, comp_inv' := λ a b ⟨p,hp⟩, by simp only [comp_inv] }

/-- The subgroup of the vertex group at `c` given by the subgroupoid -/
def vertex_subgroup {c : C} (hc : c ∈ S.carrier) : subgroup (c ⟶ c) :=
⟨ S.arrws c c
, λ f g hf hg, S.mul' hf hg
, by {apply id_mem_of_nonempty_isotropy, use hc,}
, λ f hf, S.inv' hf⟩

/-- `S` is a subgroupoid of `T` if it is contained in it -/
def is_subgroupoid (S T : subgroupoid C) : Prop :=
  ∀ {c d}, S.arrws c d ⊆ T.arrws c d

instance subgroupoid_le : has_le (subgroupoid C) := ⟨is_subgroupoid⟩

lemma le_refl (S : subgroupoid C) : S ≤ S :=
by {rintro c d p, exact id,}

lemma le_trans (R S T : subgroupoid C) : R ≤ S → S ≤ T → R ≤ T :=
by {rintro RS ST c d, exact (@RS c d).trans (@ST c d), }

lemma le_antisymm (R S : subgroupoid C) : R ≤ S → S ≤ R → R = S :=
by {rintro RS SR, ext c d p, exact ⟨(@RS c d p), (@SR c d p)⟩,}

instance : partial_order (subgroupoid C) :=
{ le := is_subgroupoid,
  le_refl := le_refl,
  le_trans := le_trans,
  le_antisymm := le_antisymm}

instance : has_top (subgroupoid C) :=
⟨⟨(λ _ _, set.univ), by { rintros, trivial, }, by { rintros, trivial, }⟩⟩
instance : has_bot (subgroupoid C) :=
⟨⟨(λ _ _, ∅), by { rintros, exfalso, assumption, }, by { rintros, exfalso, assumption, }⟩⟩

instance : inhabited (subgroupoid C) := ⟨⊤⟩

instance : has_inf (subgroupoid C) :=
⟨ λ S T,
  ⟨(λ c d, (S.arrws c d)∩(T.arrws c d))
  , by { rintros, exact ⟨S.inv' hp.1,T.inv' hp.2⟩, }
  , by { rintros, exact ⟨S.mul' hp.1 hq.1, T.mul' hp.2 hq.2⟩, }⟩⟩

instance : has_Inf (subgroupoid C) :=
⟨ λ s,
  ⟨(λ c d, set.Inter (λ (S : s), S.val.arrws c d))
  , by
    { rintros,
      simp only [Inter_coe_set, mem_Inter] at hp ⊢,
      rintro S Ss,
      exact S.inv' (hp S Ss)}
  , by
    { rintros,
      simp only [Inter_coe_set, mem_Inter] at hp hq ⊢,
      rintro S Ss,
      apply S.mul' (hp S Ss) (hq S Ss), }⟩⟩

instance : complete_lattice (subgroupoid C) :=
{ bot          := (⊥),
  bot_le       := λ S c d, by {apply empty_subset,},
  top          := (⊤),
  le_top       := λ S c d, by {apply subset_univ,},
  inf          := (⊓),
  le_inf       := λ R S T RS RT c d p pR, ⟨RS pR, RT pR⟩,
  inf_le_left  := λ R S c d p pRS, pRS.left,
  inf_le_right := λ R S c d p pRS, pRS.right,
  .. complete_lattice_of_Inf (subgroupoid C)
       ( by
        { dsimp only [Inf], rintro s, constructor,
          { rintro S Ss c d p hp,
            simp only [Inter_coe_set, mem_Inter] at hp,
            exact hp S Ss, },
          { rintro T Tl c d p pT,
            simp only [Inter_coe_set, mem_Inter],
            rintros S Ss, apply Tl Ss, exact pT,}}) }

/-- The discrete subgroupoid has only the `𝟙 _` arrows -/
def discrete [decidable_eq C] : subgroupoid C :=
⟨ λ c d, if h : c = d then {h.rec_on (𝟙 c)} else ∅
, by
  { rintros c d p hp,
    by_cases h : d = c,
    { subst_vars,
      simp only [eq_self_iff_true, congr_arg_mpr_hom_right, eq_to_hom_refl, category.comp_id,
                 dite_eq_ite, if_true, mem_singleton_iff] at hp ⊢,
      rw hp, apply inv_one, },
    { rw dif_neg (λ l : c = d, h l.symm) at hp, exact hp.elim, }, }
, by
  { rintros c d e p hp q hq,
    by_cases h : d = c,
    { by_cases k : e = d; subst_vars,
      { simp only [eq_self_iff_true, dite_eq_ite, if_true, mem_singleton_iff] at ⊢ hp hq,
        rw [hp, hq], simp only [category.comp_id], },
      { simp only [eq_self_iff_true, dite_eq_ite, if_true, mem_singleton_iff] at ⊢ hp hq,
        rw dif_neg (λ l : d = e, k l.symm) at hq, exact hq.elim, }, },
    { rw dif_neg (λ l : c = d, h l.symm) at hp, exact hp.elim, }
  }⟩

/-- A subgroupoid is normal if it is “wide” (meaning that its carrier set is all of `C`)
    and satisfies the expected stability under conjugacy -/
structure is_normal : Prop :=
  (wide : ∀ c, (𝟙 c) ∈ (S.arrws c c))
  (conj : ∀ {c d} (p : c ⟶ d) (γ : c ⟶ c) (hs : γ ∈ S.arrws c c),
                ((inv p) ≫ γ ≫ p) ∈ (S.arrws d d))
  (conj' : ∀ {c d} (p : d ⟶ c) (γ : c ⟶ c) (hs : γ ∈ S.arrws c c),
                (p ≫ γ ≫ (inv p)) ∈ (S.arrws d d)
         := λ c d p γ hs, by { convert conj (inv p) γ hs, simp, })


lemma is_normal.conjugation_eq (Sn : is_normal S) {c d} (p : c ⟶ d) :
  set.bij_on (λ γ : c ⟶ c, (inv p) ≫ γ ≫ p) (S.arrws c c) (S.arrws d d) :=
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
{ wide := (λ c, trivial)
, conj := (λ a b c d e, trivial) }


lemma Inf_is_normal (s : set $ subgroupoid C) (sn : ∀ S ∈ s, is_normal S) : is_normal (Inf s) :=
{ wide := by
  { rintro c _ ⟨⟨S,Ss⟩,rfl⟩,
    exact (sn S Ss).wide c, },
  conj := by
  { rintros c d p γ hγ _ ⟨⟨S,Ss⟩,rfl⟩,
    apply (sn S Ss).conj p γ,
    apply hγ,
    use ⟨S,Ss⟩, } }

lemma is_normal.vertex_subgroup (Sn : is_normal S) (c : C) (cS : c ∈ S.carrier) :
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

section generated_subgroupoid

-- TODO: proof that generated is just "words in X" and generated_normal is similarly
variable (X : ∀ c d : C, set (c ⟶ d))

/-- The subgropoid generated by the set of arrows `X` -/
def generated : subgroupoid C :=
  Inf {S : subgroupoid C | ∀ c d, X c d ⊆ S.arrws c d}

/-- The normal sugroupoid generated by the set of arrows `X` -/
def generated_normal : subgroupoid C :=
  Inf {S : subgroupoid C | (∀ c d, X c d ⊆ S.arrws c d) ∧ S.is_normal }

lemma generated_normal_is_normal : (generated_normal X).is_normal :=
Inf_is_normal _ (λ S h, h.right)

end generated_subgroupoid

section hom

variables {D : Type*}
variables [groupoid D] (φ : C ⥤ D)

/--
A functor between groupoid defines a map of subgroupoids in the reverse direction
by taking preimages.
 -/

def comap (S : subgroupoid D) : subgroupoid C :=
⟨ λ c d, {f : c ⟶ d | φ.map f ∈ S.arrws (φ.obj c) (φ.obj d)}
, by
  { rintros,
    simp only [inv_eq_inv, mem_set_of_eq, functor.map_inv],
    simp only [←inv_eq_inv],
    simp only [mem_set_of_eq] at hp,
    apply S.inv', assumption, }
, by
  { rintros,
    simp only [mem_set_of_eq, functor.map_comp],
    apply S.mul';
    assumption, }⟩


lemma comap_mono (S T : subgroupoid D) :
  S ≤ T → comap φ S ≤ comap φ T :=
begin
  rintro ST,
  dsimp only [subgroupoid.comap],
  rintro c d p hp,
  exact ST hp,
end

lemma is_normal_comap {S : subgroupoid D} (Sn : is_normal S) : is_normal (comap φ S) :=
{ wide := by
  { rintro c,
    dsimp only [comap],
    simp only [mem_set_of_eq, functor.map_id],
    apply Sn.wide, }
, conj := by
  { rintros c d f γ hγ,
    dsimp only [comap],
    simp only [mem_set_of_eq, functor.map_comp, functor.map_inv, inv_eq_inv],
    rw [←inv_eq_inv],
    apply Sn.conj, exact hγ, } }

/-- The kernel of a functor between subgroupoid is the preimage. -/
noncomputable def ker : subgroupoid C := comap φ (discrete)

lemma mem_ker_iff {c d : C} (f : c ⟶ d) :
  f ∈ (ker φ).arrws c d ↔ ∃ (h : φ.obj c = φ.obj d), φ.map f = h.rec_on (𝟙 $ φ.obj c) :=
begin
  dsimp only [ker, discrete, subgroupoid.comap],
  by_cases h : φ.obj c = φ.obj d,
  { simp only [dif_pos h, mem_singleton_iff, mem_set_of_eq],
    split,
    { rintro e, use h, exact e, },
    { rintro ⟨_,e⟩, exact e, }, },
  { simp only [dif_neg h, set_of_false, false_iff, not_exists, mem_empty_iff_false],
    rintro e, exact (h e).elim, },
end

end hom

end subgroupoid

end groupoid

end category_theory
