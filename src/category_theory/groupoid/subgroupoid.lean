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

/-- Type synonym to coerce a subgroupoid into a groupoid -/
def coe := subtype $ S.carrier

/-- A subgroupoid as a groupoid -/
@[simps] def coe_groupoid : groupoid (coe S) :=
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

/-- The `groupoid` instance for `subgroupoid.coe` -/
instance (S : subgroupoid C) : groupoid S.coe := coe_groupoid S

/-- There is an embedding of the coerced subgroupoid to its parent-/
def coe_embedding : (coe S) ⥤ C :=
{ obj := λ c, c.val,
  map := λ c d f, f.val,
  map_id' := λ c, by simp only [subtype.val_eq_coe, coe_groupoid_to_category_id_coe],
  map_comp' := λ c d e f g, by simp only [subtype.val_eq_coe, coe_groupoid_to_category_comp_coe] }

lemma coe_embedding.inj_on_objects : function.injective (coe_embedding S).obj := by
{ rintros ⟨c,hc⟩ ⟨d,hd⟩ hcd, simp only [subtype.mk_eq_mk], exact hcd }

lemma coe_embedding.faithful :
  ∀ c d, function.injective (λ (f : c ⟶ d), (coe_embedding S).map f) := by
{ rintros ⟨c,hc⟩ ⟨d,hd⟩ ⟨f,hf⟩ ⟨g,hg⟩ hfg, simp only [subtype.mk_eq_mk], exact hfg, }

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

/-- The family of arrows of the full subgroupoid on vertex set `V` -/
inductive full_on.arrws (V : set C) : Π (c d : C), (c ⟶ d) → Prop
| intro {c : C} (hc : c ∈ V) {d : C} (hd : d ∈ V) (f : c ⟶ d) : full_on.arrws c d f

@[simp] lemma full_on.mem_arrws_iff (V : set C) {c d : C} (f : c ⟶ d) :
  full_on.arrws V c d f ↔ c ∈ V ∧ d ∈ V :=
begin
  split,
  { rintros ⟨c,hc,d,hd,f⟩, exact ⟨hc,hd⟩, },
  { rintros ⟨hc,hd⟩, constructor; assumption, },
end

/-- The full subgroupoid on vertex set `V` -/
def full_on (V : set C) : subgroupoid C :=
⟨ full_on.arrws V
, by { rintros, induction hp, constructor; assumption, }
, by { rintros, induction hp, induction hq, constructor; assumption } ⟩

/-- The family of arrows of the discrete subgroupoid -/
inductive discrete.arrws : Π (c d : C), (c ⟶ d) → Prop
| id (c : C) : discrete.arrws c c (𝟙 c)

/-- The only arrows of the discrete subgroupoid are the identity arrows-/
def discrete : subgroupoid C :=
⟨ discrete.arrws
, by { rintros _ _ _ hp, induction hp, simp only [inv_eq_inv, is_iso.inv_id], constructor, }
, by { rintros _ _ _ _ hp _ hq, induction hp, induction hq, rw category.comp_id, constructor,} ⟩

lemma mem_discrete_iff {c d : C} (f : c ⟶ d):
  (f ∈ (discrete).arrws c d) ↔ (∃ (h : c = d), f = h.rec_on (𝟙 c)) :=
begin
  split,
  { intro hf, induction hf, simp only [eq_self_iff_true, exists_true_left], },
  { rintro ⟨h,he⟩, subst_vars, constructor, }
end

section normal

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

lemma discrete_is_normal : is_normal (discrete : subgroupoid C) :=
{ wide := (λ c, discrete.arrws.id c)
, conj := (λ a b f d e , by
  { simp only [mem_discrete_iff, eq_self_iff_true, inv_eq_inv, is_iso.inv_comp_eq,
               category.comp_id, exists_true_left] at e ⊢,
    simp only [e, category.id_comp], }) }

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

end normal

section graph_like

def is_graph_like := ∀ (c d : C), subsingleton (S.arrws c d)

lemma is_graph_like_iff : (is_graph_like S) ↔ ∀ (c : C), subsingleton (S.arrws c c) :=
begin
  split,
  { rintro h c, exact h c c,},
  { rintros h c d, constructor, rintro ⟨f,fS⟩ ⟨g,gS⟩,
    ext,
    simp only [subtype.coe_mk],
    have ifgS : inv f ≫ g ∈ S.arrws d d := S.mul' (S.inv' fS) gS,
    have idS : 𝟙 d ∈ S.arrws d d := id_mem_of_nonempty_isotropy S d ⟨_,ifgS⟩,
    obtain ⟨ss⟩ := h d,
    have : inv f ≫ g = 𝟙 _, by
    { rw ←@subtype.mk_eq_mk _ (S.arrws d d) (inv f ≫ g) ifgS (𝟙 d) (idS),
      apply ss, },
    calc f
       = f ≫ (inv g ≫ g) : by simp
    ...= f ≫ (inv f ≫ g) : by { apply congr_arg2, refl, rw this, simp, }
    ...= g                : by simp, }
end

abbreviation maximal_graph_like (T : subgroupoid C) :=
  (T.is_graph_like ∧ T ≤ S) ∧ ∀ (T' : subgroupoid C), (T'.is_graph_like ∧ T' ≤ S) → T ≤ T' → T = T'

lemma is_graph_like.maximal_iff_full (T : subgroupoid C) (Tg : T.is_graph_like)  (TS : T ≤ S) :
  maximal_graph_like S T ↔ (∀ c d, (S.arrws c d).nonempty → (T.arrws c d).nonempty) := sorry
-- should use the fact that a graph_like has a generating forest, and then it's graph-theoretic
-- arguments…

lemma is_graph_like.exists_maximal :
  ∃ (T : subgroupoid C), maximal_graph_like S T := sorry

end graph_like

section disconnected

/-- A subgroupoid is disconnected if it only has loops -/
def is_disconnected := ∀ (c d : C), c ≠ d → is_empty (S.arrws c d)

/-- The arrow set of `S.disconnect`, which drops all arrows but the loops -/
inductive disconnect.arrws : Π  (c d : C), (c ⟶ d) → Prop
| vert {c : C} {γ : c ⟶ c} : γ ∈ S.arrws c c →  disconnect.arrws c c γ

lemma disconnect.mem_arrws_iff {c d : C} (f : c ⟶ d) :
  disconnect.arrws S c d f ↔ ∃ (h : c = d), (h.symm.rec_on f) ∈ S.arrws c c :=
begin
  split,
  { rintros ⟨c,γ,hγ⟩, simp only [eq_self_iff_true, exists_true_left], exact hγ },
  { rintro ⟨rfl,h⟩, constructor, simp only at h, exact h, },
end

/-- Only keep the loops of `S` -/
def disconnect : subgroupoid C :=
⟨ disconnect.arrws S
, λ _ _ f hf, by {induction hf, constructor, apply S.inv', assumption, }
, λ _ _ _ f hf g hg, by
  { obtain ⟨hf,ef⟩ := (disconnect.mem_arrws_iff S f).mp hf,
    obtain ⟨hg,eg⟩ := (disconnect.mem_arrws_iff S g).mp hg,
    subst_vars, constructor, apply S.mul' ef eg, }⟩

lemma disconnect_is_normal_of_normal (Sn : is_normal S) : S.disconnect.is_normal :=
{ wide := λ c, disconnect.arrws.vert $ Sn.wide c
, conj := λ _ _ f _ h, by {cases h, constructor, apply Sn.conj, assumption, } }

end disconnected

section generated_subgroupoid

-- TODO: proof that generated is just "words in X" and generated_normal is similarly
variable (X : ∀ (c d : C), set (c ⟶ d))

/-- The subgropoid generated by the set of arrows `X` -/
def generated : subgroupoid C :=
  Inf {S : subgroupoid C | ∀ c d, X c d ⊆ S.arrws c d}

/- TODO to prove this:
* Define the “forest” property below properly on quivers: this is equivalent to the symmetrification
  containing only subsingletons
* Show that the free groupoid on a “forest” quiver is graph_like, and conversely
  that if the free groupoid is graph_like, then it is generated by a “forest” quiver.
* Prove that `generated X` is just words in `X` by using the free groupoid on `X`.
  (need to be careful about only keeping the strictly necessary vertices : only those incident to
   arrows of `X` need appear in the quiver defined by `X` and in the free groupoid).

Now for the actual statement:

* If S is graph_like, take a maximal forest contained in S.
-/

--lemma is_graph_like.is_free_groupoid_on_maximal_forest := sorry

lemma generated.is_graph_like_iff_generating_forest :
  S.is_graph_like ↔
  ∃ (X : ∀ (c d : C), set $ c ⟶ d),
      (generated X) = S
    ∧ (∀ c d : C, subsingleton
        ((@quiver.path C ⟨λ c d, subtype $ X c d⟩ d c) ⊕ (@quiver.path C ⟨λ c d, subtype $ X c d⟩ d c)))   := sorry


/-- The normal sugroupoid generated by the set of arrows `X` -/
def generated_normal : subgroupoid C :=
  Inf {S : subgroupoid C | (∀ c d, X c d ⊆ S.arrws c d) ∧ S.is_normal }

lemma generated_normal_is_normal : (generated_normal X).is_normal :=
Inf_is_normal _ (λ S h, h.right)

end generated_subgroupoid

section hom

variables {D : Type*}
variables [groupoid D] (φ : C ⥤ D)

section comap

variables (T U : subgroupoid D)

/--
A functor between groupoid defines a map of subgroupoids in the reverse direction
by taking preimages.
 -/
def comap : subgroupoid C :=
⟨ λ c d, {f : c ⟶ d | φ.map f ∈ T.arrws (φ.obj c) (φ.obj d)}
, by
  { rintros,
    simp only [inv_eq_inv, mem_set_of_eq, functor.map_inv],
    simp only [←inv_eq_inv],
    simp only [mem_set_of_eq] at hp,
    apply T.inv', assumption, }
, by
  { rintros,
    simp only [mem_set_of_eq, functor.map_comp],
    apply T.mul';
    assumption, }⟩


lemma comap_mono {T U} :
  T ≤ U → comap φ T ≤ comap φ U :=
begin
  rintro TU,
  dsimp only [subgroupoid.comap],
  rintro c d p hp,
  exact TU hp,
end

lemma is_normal_comap {T} (Tn : is_normal T) : is_normal (comap φ T) :=
{ wide := by
  { rintro c,
    dsimp only [comap],
    simp only [mem_set_of_eq, functor.map_id],
    apply Tn.wide, }
, conj := by
  { rintros c d f γ hγ,
    dsimp only [comap],
    simp only [mem_set_of_eq, functor.map_comp, functor.map_inv, inv_eq_inv],
    rw [←inv_eq_inv],
    apply Tn.conj, exact hγ, } }

/-- The kernel of a functor between subgroupoid is the preimage. -/
def ker : subgroupoid C := comap φ (discrete)

lemma mem_ker_iff {c d : C} (f : c ⟶ d) :
  f ∈ (ker φ).arrws c d ↔ ∃ (h : φ.obj c = φ.obj d), φ.map f = h.rec_on (𝟙 $ φ.obj c) :=
mem_discrete_iff (φ.map f)

end comap

section map

variables (hφ : function.injective φ.obj) (S)

/-- The family of arrows of the image of a subgroupoid under a functor injective on objects -/
inductive map.arrws :
  Π (c d : D), (c ⟶ d) → Prop
| im {c d : C} (f : c ⟶ d) (hf : f ∈ S.arrws c d) : map.arrws (φ.obj c) (φ.obj d) (φ.map f)

lemma map.mem_arrws_iff {c d : D} (f : c ⟶ d) :
  map.arrws S φ c d f ↔
  ∃ (a b : C) (g : a ⟶ b) (ha : φ.obj a = c) (hb : φ.obj b = d) (hg : g ∈ S.arrws a b),
    f = @eq.rec_on _ (φ.obj a) (λ x, x ⟶ d) (c) ha (hb.rec_on $ φ.map g) :=
begin
  split,
  { rintro ⟨a,b,g,hg⟩, use [a,b,g,rfl,rfl,hg,rfl], },
  { rintro ⟨a,b,g,ha,hb,hg,he⟩, subst_vars,
    simp only [congr_arg_mpr_hom_right, eq_to_hom_refl, category.comp_id],
    constructor, exact hg, },
end

/-- The "forward" image of a subgroupoid under a functor injective on objects -/
def map (hφ : function.injective φ.obj) (S) : subgroupoid D :=
⟨ map.arrws S φ
, by
  { rintro _ _ _ hp, induction hp,
    rw [inv_eq_inv,←functor.map_inv], constructor,
    rw ←inv_eq_inv, apply S.inv', assumption, }
, by -- Is there no way to prove this ↓ directly without the help of `map.mem_arrws_iff` ?
  { rintro _ _ _ _ hp _ hq,
    obtain ⟨f₀,f₁,f,hf₀,hf₁,hf,fp⟩ := (map.mem_arrws_iff S φ p).mp hp,
    obtain ⟨g₀,g₁,g,hg₀,hg₁,hg,gq⟩ := (map.mem_arrws_iff S φ q).mp hq,
    simp only [has_mem.mem, map.mem_arrws_iff],
    have : f₁ = g₀, by {apply hφ, exact hf₁.trans hg₀.symm, },
    induction this,
    refine ⟨f₀,g₁,f ≫ g,hf₀,hg₁,S.mul' hf hg,_⟩,
    simp only [functor.map_comp],
    subst_vars } ⟩

lemma map_mono (S T : subgroupoid C) :
  S ≤ T → map φ hφ S ≤ map φ hφ T :=
begin
  rintros le _ _ _ ⟨a,b,f,h⟩,
  constructor,
  apply le h,
end

/-- The image of a functor injective on objects -/
def im := map φ hφ (⊤)

lemma mem_im_iff {c d : D} (f : c ⟶ d) :
  f ∈ (im φ hφ).arrws c d ↔
  ∃ (a b : C) (g : a ⟶ b) (ha : φ.obj a = c) (hb : φ.obj b = d),
    f = @eq.rec_on _ (φ.obj a) (λ x, x ⟶ d) (c) ha (hb.rec_on $ φ.map g) :=
begin
  convert map.mem_arrws_iff ⊤ φ f,
  dsimp [⊤,has_top.top],
  simp only [mem_univ, exists_true_left],
end

lemma is_normal_map (hφs : im φ hφ = ⊤) :
  S.is_normal → (map φ hφ S).is_normal :=
begin
  rintro ⟨Swide,Sconj⟩,
  sorry
end

lemma is_graph_like_map : S.is_graph_like → (map φ hφ S).is_graph_like := sorry

lemma is_disconnected_map : S.is_disconnected → (map φ hφ S).is_disconnected := sorry

end map

end hom

end subgroupoid

end groupoid

end category_theory
