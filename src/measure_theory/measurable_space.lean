/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/

import algebra.indicator_function
import data.prod.tprod
import group_theory.coset
import logic.equiv.fin
import measure_theory.measurable_space_def
import measure_theory.tactic
import order.filter.lift

/-!
# Measurable spaces and measurable functions

This file provides properties of measurable spaces and the functions and isomorphisms
between them. The definition of a measurable space is in `measure_theory.measurable_space_def`.

A measurable space is a set equipped with a σ-algebra, a collection of
subsets closed under complementation and countable union. A function
between measurable spaces is measurable if the preimage of each
measurable subset is measurable.

σ-algebras on a fixed set `α` form a complete lattice. Here we order
σ-algebras by writing `m₁ ≤ m₂` if every set which is `m₁`-measurable is
also `m₂`-measurable (that is, `m₁` is a subset of `m₂`). In particular, any
collection of subsets of `α` generates a smallest σ-algebra which
contains all of them. A function `f : α → β` induces a Galois connection
between the lattices of σ-algebras on `α` and `β`.

A measurable equivalence between measurable spaces is an equivalence
which respects the σ-algebras, that is, for which both directions of
the equivalence are measurable functions.

We say that a filter `f` is measurably generated if every set `s ∈ f` includes a measurable
set `t ∈ f`. This property is useful, e.g., to extract a measurable witness of `filter.eventually`.

## Notation

* We write `α ≃ᵐ β` for measurable equivalences between the measurable spaces `α` and `β`.
  This should not be confused with `≃ₘ` which is used for diffeomorphisms between manifolds.

## Implementation notes

Measurability of a function `f : α → β` between measurable spaces is
defined in terms of the Galois connection induced by f.

## References

* <https://en.wikipedia.org/wiki/Measurable_space>
* <https://en.wikipedia.org/wiki/Sigma-algebra>
* <https://en.wikipedia.org/wiki/Dynkin_system>

## Tags

measurable space, σ-algebra, measurable function, measurable equivalence, dynkin system,
π-λ theorem, π-system
-/

open set encodable function equiv
open_locale filter measure_theory


variables {α β γ δ δ' : Type*} {ι : Sort*} {s t u : set α}


namespace measurable_space

section functors
variables {m m₁ m₂ : measurable_space α} {m' : measurable_space β} {f : α → β} {g : β → α}

/-- The forward image of a measurable space under a function. `map f m` contains the sets
  `s : set β` whose preimage under `f` is measurable. -/
protected def map (f : α → β) (m : measurable_space α) : measurable_space β :=
{ measurable_set'      := λ s, m.measurable_set' $ f ⁻¹' s,
  measurable_set_empty := m.measurable_set_empty,
  measurable_set_compl := assume s hs, m.measurable_set_compl _ hs,
  measurable_set_Union := assume f hf, by { rw preimage_Union, exact m.measurable_set_Union _ hf }}

@[simp] lemma map_id : m.map id = m :=
measurable_space.ext $ assume s, iff.rfl

@[simp] lemma map_comp {f : α → β} {g : β → γ} : (m.map f).map g = m.map (g ∘ f) :=
measurable_space.ext $ assume s, iff.rfl

/-- The reverse image of a measurable space under a function. `comap f m` contains the sets
  `s : set α` such that `s` is the `f`-preimage of a measurable set in `β`. -/
protected def comap (f : α → β) (m : measurable_space β) : measurable_space α :=
{ measurable_set'      := λ s, ∃s', m.measurable_set' s' ∧ f ⁻¹' s' = s,
  measurable_set_empty := ⟨∅, m.measurable_set_empty, rfl⟩,
  measurable_set_compl := assume s ⟨s', h₁, h₂⟩, ⟨s'ᶜ, m.measurable_set_compl _ h₁, h₂ ▸ rfl⟩,
  measurable_set_Union := assume s hs,
    let ⟨s', hs'⟩ := classical.axiom_of_choice hs in
    ⟨⋃ i, s' i, m.measurable_set_Union _ (λ i, (hs' i).left), by simp [hs'] ⟩ }

@[simp] lemma comap_id : m.comap id = m :=
measurable_space.ext $ assume s, ⟨assume ⟨s', hs', h⟩, h ▸ hs', assume h, ⟨s, h, rfl⟩⟩

@[simp] lemma comap_comp {f : β → α} {g : γ → β} : (m.comap f).comap g = m.comap (f ∘ g) :=
measurable_space.ext $ assume s,
  ⟨assume ⟨t, ⟨u, h, hu⟩, ht⟩, ⟨u, h, ht ▸ hu ▸ rfl⟩, assume ⟨t, h, ht⟩, ⟨f ⁻¹' t, ⟨_, h, rfl⟩, ht⟩⟩

lemma comap_le_iff_le_map {f : α → β} : m'.comap f ≤ m ↔ m' ≤ m.map f :=
⟨assume h s hs, h _ ⟨_, hs, rfl⟩, assume h s ⟨t, ht, heq⟩, heq ▸ h _ ht⟩

lemma gc_comap_map (f : α → β) :
  galois_connection (measurable_space.comap f) (measurable_space.map f) :=
assume f g, comap_le_iff_le_map

lemma map_mono (h : m₁ ≤ m₂) : m₁.map f ≤ m₂.map f := (gc_comap_map f).monotone_u h
lemma monotone_map : monotone (measurable_space.map f) := assume a b h, map_mono h
lemma comap_mono (h : m₁ ≤ m₂) : m₁.comap g ≤ m₂.comap g := (gc_comap_map g).monotone_l h
lemma monotone_comap : monotone (measurable_space.comap g) := assume a b h, comap_mono h

@[simp] lemma comap_bot : (⊥ : measurable_space α).comap g = ⊥ := (gc_comap_map g).l_bot
@[simp] lemma comap_sup : (m₁ ⊔ m₂).comap g = m₁.comap g ⊔ m₂.comap g := (gc_comap_map g).l_sup
@[simp] lemma comap_supr {m : ι → measurable_space α} : (⨆i, m i).comap g = (⨆i, (m i).comap g) :=
(gc_comap_map g).l_supr

@[simp] lemma map_top : (⊤ : measurable_space α).map f = ⊤ := (gc_comap_map f).u_top
@[simp] lemma map_inf : (m₁ ⊓ m₂).map f = m₁.map f ⊓ m₂.map f := (gc_comap_map f).u_inf
@[simp] lemma map_infi {m : ι → measurable_space α} : (⨅i, m i).map f = (⨅i, (m i).map f) :=
(gc_comap_map f).u_infi

lemma comap_map_le : (m.map f).comap f ≤ m := (gc_comap_map f).l_u_le _
lemma le_map_comap : m ≤ (m.comap g).map g := (gc_comap_map g).le_u_l _

end functors

@[mono] lemma generate_from_mono {s t : set (set α)} (h : s ⊆ t) :
  generate_from s ≤ generate_from t :=
gi_generate_from.gc.monotone_l h

lemma generate_from_sup_generate_from {s t : set (set α)} :
  generate_from s ⊔ generate_from t = generate_from (s ∪ t) :=
(@gi_generate_from α).gc.l_sup.symm

lemma comap_generate_from {f : α → β} {s : set (set β)} :
  (generate_from s).comap f = generate_from (preimage f '' s) :=
le_antisymm
  (comap_le_iff_le_map.2 $ generate_from_le $ assume t hts,
    generate_measurable.basic _ $ mem_image_of_mem _ $ hts)
  (generate_from_le $ assume t ⟨u, hu, eq⟩, eq ▸ ⟨u, generate_measurable.basic _ hu, rfl⟩)

end measurable_space

section measurable_functions
open measurable_space

lemma measurable_iff_le_map {m₁ : measurable_space α} {m₂ : measurable_space β} {f : α → β} :
  measurable f ↔ m₂ ≤ m₁.map f :=
iff.rfl

alias measurable_iff_le_map ↔ measurable.le_map measurable.of_le_map

lemma measurable_iff_comap_le {m₁ : measurable_space α} {m₂ : measurable_space β} {f : α → β} :
  measurable f ↔ m₂.comap f ≤ m₁ :=
comap_le_iff_le_map.symm

alias measurable_iff_comap_le ↔ measurable.comap_le measurable.of_comap_le

lemma measurable.mono {ma ma' : measurable_space α} {mb mb' : measurable_space β} {f : α → β}
  (hf : @measurable α β ma mb f) (ha : ma ≤ ma') (hb : mb' ≤ mb) :
  @measurable α β ma' mb' f :=
λ t ht, ha _ $ hf $ hb _ ht

@[measurability]
lemma measurable_from_top [measurable_space β] {f : α → β} : measurable[⊤] f :=
λ s hs, trivial

lemma measurable_generate_from [measurable_space α] {s : set (set β)} {f : α → β}
  (h : ∀ t ∈ s, measurable_set (f ⁻¹' t)) : @measurable _ _ _ (generate_from s) f :=
measurable.of_le_map $ generate_from_le h

variables {f g : α → β}

section typeclass_measurable_space
variables [measurable_space α] [measurable_space β] [measurable_space γ]

@[nontriviality, measurability]
lemma subsingleton.measurable [subsingleton α] : measurable f :=
λ s hs, @subsingleton.measurable_set α _ _ _

@[nontriviality, measurability]
lemma measurable_of_subsingleton_codomain [subsingleton β] (f : α → β) :
  measurable f :=
λ s hs, subsingleton.set_cases measurable_set.empty measurable_set.univ s

@[to_additive]
lemma measurable_one [has_one α] : measurable (1 : β → α) := @measurable_const _ _ _ _ 1

lemma measurable_of_empty [is_empty α] (f : α → β) : measurable f :=
subsingleton.measurable

lemma measurable_of_empty_codomain [is_empty β] (f : α → β) : measurable f :=
by { haveI := function.is_empty f, exact measurable_of_empty f }

/-- A version of `measurable_const` that assumes `f x = f y` for all `x, y`. This version works
for functions between empty types. -/
lemma measurable_const' {f : β → α} (hf : ∀ x y, f x = f y) : measurable f :=
begin
  casesI is_empty_or_nonempty β,
  { exact measurable_of_empty f },
  { convert measurable_const, exact funext (λ x, hf x h.some) }
end

lemma measurable_of_fintype [fintype α] [measurable_singleton_class α] (f : α → β) :
  measurable f :=
λ s hs, (finite.of_fintype (f ⁻¹' s)).measurable_set

end typeclass_measurable_space

variables {m : measurable_space α}
include m

@[measurability] lemma measurable.iterate {f : α → α} (hf : measurable f) : ∀ n, measurable (f^[n])
| 0 := measurable_id
| (n+1) := (measurable.iterate n).comp hf

variables {mβ : measurable_space β}
include mβ

@[measurability]
lemma measurable_set_preimage {t : set β} (hf : measurable f) (ht : measurable_set t) :
  measurable_set (f ⁻¹' t) :=
hf ht

@[measurability]
lemma measurable.piecewise {_ : decidable_pred (∈ s)} (hs : measurable_set s)
  (hf : measurable f) (hg : measurable g) :
  measurable (piecewise s f g) :=
begin
  intros t ht,
  rw piecewise_preimage,
  exact hs.ite (hf ht) (hg ht)
end

/-- this is slightly different from `measurable.piecewise`. It can be used to show
`measurable (ite (x=0) 0 1)` by
`exact measurable.ite (measurable_set_singleton 0) measurable_const measurable_const`,
but replacing `measurable.ite` by `measurable.piecewise` in that example proof does not work. -/
lemma measurable.ite {p : α → Prop} {_ : decidable_pred p}
  (hp : measurable_set {a : α | p a}) (hf : measurable f) (hg : measurable g) :
  measurable (λ x, ite (p x) (f x) (g x)) :=
measurable.piecewise hp hf hg

@[measurability]
lemma measurable.indicator [has_zero β] (hf : measurable f) (hs : measurable_set s) :
  measurable (s.indicator f) :=
hf.piecewise hs measurable_const

@[measurability, to_additive] lemma measurable_set_mul_support [has_one β]
  [measurable_singleton_class β] (hf : measurable f) :
  measurable_set (mul_support f) :=
hf (measurable_set_singleton 1).compl

/-- If a function coincides with a measurable function outside of a countable set, it is
measurable. -/
lemma measurable.measurable_of_countable_ne [measurable_singleton_class α]
  (hf : measurable f) (h : countable {x | f x ≠ g x}) : measurable g :=
begin
  assume t ht,
  have : g ⁻¹' t = (g ⁻¹' t ∩ {x | f x = g x}ᶜ) ∪ (g ⁻¹' t ∩ {x | f x = g x}),
    by simp [← inter_union_distrib_left],
  rw this,
  apply measurable_set.union (h.mono (inter_subset_right _ _)).measurable_set,
  have : g ⁻¹' t ∩ {x : α | f x = g x} = f ⁻¹' t ∩ {x : α | f x = g x},
    by { ext x, simp {contextual := tt} },
  rw this,
  exact (hf ht).inter h.measurable_set.of_compl,
end


end measurable_functions

section constructions

instance : measurable_space empty := ⊤
instance : measurable_space punit := ⊤ -- this also works for `unit`
instance : measurable_space bool := ⊤
instance : measurable_space ℕ := ⊤
instance : measurable_space ℤ := ⊤
instance : measurable_space ℚ := ⊤

instance : measurable_singleton_class empty := ⟨λ _, trivial⟩
instance : measurable_singleton_class punit := ⟨λ _, trivial⟩
instance : measurable_singleton_class bool := ⟨λ _, trivial⟩
instance : measurable_singleton_class ℕ := ⟨λ _, trivial⟩
instance : measurable_singleton_class ℤ := ⟨λ _, trivial⟩
instance : measurable_singleton_class ℚ := ⟨λ _, trivial⟩

lemma measurable_to_encodable [measurable_space α] [encodable α] [measurable_space β] {f : β → α}
  (h : ∀ y, measurable_set (f ⁻¹' {f y})) :
  measurable f :=
begin
  assume s hs,
  rw [← bUnion_preimage_singleton],
  refine measurable_set.Union (λ y, measurable_set.Union_Prop $ λ hy, _),
  by_cases hyf : y ∈ range f,
  { rcases hyf with ⟨y, rfl⟩,
    apply h },
  { simp only [preimage_singleton_eq_empty.2 hyf, measurable_set.empty] }
end

@[measurability] lemma measurable_unit [measurable_space α] (f : unit → α) : measurable f :=
measurable_from_top

section nat
variables [measurable_space α]

@[measurability] lemma measurable_from_nat {f : ℕ → α} : measurable f :=
measurable_from_top

lemma measurable_to_nat {f : α → ℕ} : (∀ y, measurable_set (f ⁻¹' {f y})) → measurable f :=
measurable_to_encodable

lemma measurable_find_greatest' {p : α → ℕ → Prop} [∀ x, decidable_pred (p x)]
  {N : ℕ} (hN : ∀ k ≤ N, measurable_set {x | nat.find_greatest (p x) N = k}) :
  measurable (λ x, nat.find_greatest (p x) N) :=
measurable_to_nat $ λ x, hN _ N.find_greatest_le

lemma measurable_find_greatest {p : α → ℕ → Prop} [∀ x, decidable_pred (p x)]
  {N} (hN : ∀ k ≤ N, measurable_set {x | p x k}) :
  measurable (λ x, nat.find_greatest (p x) N) :=
begin
  refine measurable_find_greatest' (λ k hk, _),
  simp only [nat.find_greatest_eq_iff, set_of_and, set_of_forall, ← compl_set_of],
  repeat { apply_rules [measurable_set.inter, measurable_set.const, measurable_set.Inter,
    measurable_set.Inter_Prop, measurable_set.compl, hN]; try { intros } }
end

lemma measurable_find {p : α → ℕ → Prop} [∀ x, decidable_pred (p x)]
  (hp : ∀ x, ∃ N, p x N) (hm : ∀ k, measurable_set {x | p x k}) :
  measurable (λ x, nat.find (hp x)) :=
begin
  refine measurable_to_nat (λ x, _),
  rw [preimage_find_eq_disjointed],
  exact measurable_set.disjointed hm _
end

end nat

section quotient
variables [measurable_space α] [measurable_space β]

instance {α} {r : α → α → Prop} [m : measurable_space α] : measurable_space (quot r) :=
m.map (quot.mk r)

instance {α} {s : setoid α} [m : measurable_space α] : measurable_space (quotient s) :=
m.map quotient.mk'

@[to_additive]
instance _root_.quotient_group.measurable_space {G} [group G] [measurable_space G]
  (S : subgroup G) : measurable_space (G ⧸ S) :=
quotient.measurable_space

lemma measurable_set_quotient {s : setoid α} {t : set (quotient s)} :
  measurable_set t ↔ measurable_set (quotient.mk' ⁻¹' t) :=
iff.rfl

lemma measurable_from_quotient {s : setoid α} {f : quotient s → β} :
  measurable f ↔ measurable (f ∘ quotient.mk') :=
iff.rfl

@[measurability] lemma measurable_quotient_mk [s : setoid α] :
  measurable (quotient.mk : α → quotient s) :=
λ s, id

@[measurability] lemma measurable_quotient_mk' {s : setoid α} :
  measurable (quotient.mk' : α → quotient s) :=
λ s, id

@[measurability] lemma measurable_quot_mk {r : α → α → Prop} :
  measurable (quot.mk r) :=
λ s, id

@[to_additive] lemma quotient_group.measurable_coe {G} [group G] [measurable_space G]
  {S : subgroup G} : measurable (coe : G → G ⧸ S) :=
measurable_quotient_mk'

attribute [measurability] quotient_group.measurable_coe quotient_add_group.measurable_coe

@[to_additive] lemma quotient_group.measurable_from_quotient {G} [group G] [measurable_space G]
  {S : subgroup G} {f : G ⧸ S → α} :
  measurable f ↔ measurable (f ∘ (coe : G → G ⧸ S)) :=
measurable_from_quotient

end quotient

section subtype

instance {α} {p : α → Prop} [m : measurable_space α] : measurable_space (subtype p) :=
m.comap (coe : _ → α)

section
variables [measurable_space α]

@[measurability] lemma measurable_subtype_coe {p : α → Prop} : measurable (coe : subtype p → α) :=
measurable_space.le_map_comap

instance {p : α → Prop} [measurable_singleton_class α] : measurable_singleton_class (subtype p) :=
{ measurable_set_singleton := λ x,
  begin
    have : measurable_set {(x : α)} := measurable_set_singleton _,
    convert @measurable_subtype_coe α _ p _ this,
    ext y,
    simp [subtype.ext_iff],
  end }

end

variables {m : measurable_space α} {mβ : measurable_space β}

include m

lemma measurable_set.subtype_image {s : set α} {t : set s}
  (hs : measurable_set s) : measurable_set t → measurable_set ((coe : s → α) '' t)
| ⟨u, (hu : measurable_set u), (eq : coe ⁻¹' u = t)⟩ :=
  begin
    rw [← eq, subtype.image_preimage_coe],
    exact hu.inter hs
  end

include mβ

@[measurability] lemma measurable.subtype_coe {p : β → Prop} {f : α → subtype p}
  (hf : measurable f) :
  measurable (λ a : α, (f a : β)) :=
measurable_subtype_coe.comp hf

@[measurability]
lemma measurable.subtype_mk {p : β → Prop} {f : α → β} (hf : measurable f) {h : ∀ x, p (f x)} :
  measurable (λ x, (⟨f x, h x⟩ : subtype p)) :=
λ t ⟨s, hs⟩, hs.2 ▸ by simp only [← preimage_comp, (∘), subtype.coe_mk, hf hs.1]

lemma measurable_of_measurable_union_cover
  {f : α → β} (s t : set α) (hs : measurable_set s) (ht : measurable_set t) (h : univ ⊆ s ∪ t)
  (hc : measurable (λ a : s, f a)) (hd : measurable (λ a : t, f a)) :
  measurable f :=
begin
  intros u hu,
  convert (hs.subtype_image (hc hu)).union (ht.subtype_image (hd hu)),
  change f ⁻¹' u = coe '' (coe ⁻¹' (f ⁻¹' u) : set s) ∪ coe '' (coe ⁻¹' (f ⁻¹' u) : set t),
  rw [image_preimage_eq_inter_range, image_preimage_eq_inter_range, subtype.range_coe,
      subtype.range_coe, ← inter_distrib_left, univ_subset_iff.1 h, inter_univ],
end

lemma measurable_of_restrict_of_restrict_compl {f : α → β} {s : set α}
  (hs : measurable_set s) (h₁ : measurable (s.restrict f)) (h₂ : measurable (sᶜ.restrict f)) :
  measurable f :=
measurable_of_measurable_union_cover s sᶜ hs hs.compl (union_compl_self s).ge h₁ h₂

lemma measurable.dite [∀ x, decidable (x ∈ s)] {f : s → β} (hf : measurable f)
  {g : sᶜ → β} (hg : measurable g) (hs : measurable_set s) :
  measurable (λ x, if hx : x ∈ s then f ⟨x, hx⟩ else g ⟨x, hx⟩) :=
measurable_of_restrict_of_restrict_compl hs (by simpa) (by simpa)

lemma measurable_of_measurable_on_compl_finite [measurable_singleton_class α]
  {f : α → β} (s : set α) (hs : finite s) (hf : measurable (sᶜ.restrict f)) :
  measurable f :=
begin
  letI : fintype s := finite.fintype hs,
  exact measurable_of_restrict_of_restrict_compl hs.measurable_set
    (measurable_of_fintype _) hf
end

lemma measurable_of_measurable_on_compl_singleton [measurable_singleton_class α]
  {f : α → β} (a : α) (hf : measurable ({x | x ≠ a}.restrict f)) :
  measurable f :=
measurable_of_measurable_on_compl_finite {a} (finite_singleton a) hf


end subtype

section prod

/-- A `measurable_space` structure on the product of two measurable spaces. -/
def measurable_space.prod {α β} (m₁ : measurable_space α) (m₂ : measurable_space β) :
  measurable_space (α × β) :=
m₁.comap prod.fst ⊔ m₂.comap prod.snd

instance {α β} [m₁ : measurable_space α] [m₂ : measurable_space β] : measurable_space (α × β) :=
m₁.prod m₂

@[measurability] lemma measurable_fst {ma : measurable_space α} {mb : measurable_space β} :
  measurable (prod.fst : α × β → α) :=
measurable.of_comap_le le_sup_left

@[measurability] lemma measurable_snd {ma : measurable_space α} {mb : measurable_space β} :
  measurable (prod.snd : α × β → β) :=
measurable.of_comap_le le_sup_right

variables {m : measurable_space α} {mβ : measurable_space β} {mγ : measurable_space γ}

include m mβ mγ

lemma measurable.fst {f : α → β × γ} (hf : measurable f) :
  measurable (λ a : α, (f a).1) :=
measurable_fst.comp hf

lemma measurable.snd {f : α → β × γ} (hf : measurable f) :
  measurable (λ a : α, (f a).2) :=
measurable_snd.comp hf

@[measurability] lemma measurable.prod {f : α → β × γ}
  (hf₁ : measurable (λ a, (f a).1)) (hf₂ : measurable (λ a, (f a).2)) : measurable f :=
measurable.of_le_map $ sup_le
  (by { rw [measurable_space.comap_le_iff_le_map, measurable_space.map_comp], exact hf₁ })
  (by { rw [measurable_space.comap_le_iff_le_map, measurable_space.map_comp], exact hf₂ })

lemma measurable.prod_mk {β γ} {mβ : measurable_space β}
  {mγ : measurable_space γ} {f : α → β} {g : α → γ} (hf : measurable f) (hg : measurable g) :
  measurable (λ a : α, (f a, g a)) :=
measurable.prod hf hg

lemma measurable.prod_map [measurable_space δ] {f : α → β} {g : γ → δ} (hf : measurable f)
  (hg : measurable g) : measurable (prod.map f g) :=
(hf.comp measurable_fst).prod_mk (hg.comp measurable_snd)

omit mγ

lemma measurable_prod_mk_left {x : α} : measurable (@prod.mk _ β x) :=
measurable_const.prod_mk measurable_id

lemma measurable_prod_mk_right {y : β} : measurable (λ x : α, (x, y)) :=
measurable_id.prod_mk measurable_const

include mγ

lemma measurable.of_uncurry_left {f : α → β → γ} (hf : measurable (uncurry f)) {x : α} :
  measurable (f x) :=
hf.comp measurable_prod_mk_left

lemma measurable.of_uncurry_right {f : α → β → γ} (hf : measurable (uncurry f)) {y : β} :
  measurable (λ x, f x y) :=
hf.comp measurable_prod_mk_right

lemma measurable_prod {f : α → β × γ} : measurable f ↔
  measurable (λ a, (f a).1) ∧ measurable (λ a, (f a).2) :=
⟨λ hf, ⟨measurable_fst.comp hf, measurable_snd.comp hf⟩, λ h, measurable.prod h.1 h.2⟩

omit mγ

@[measurability] lemma measurable_swap :
  measurable (prod.swap : α × β → β × α) :=
measurable.prod measurable_snd measurable_fst

lemma measurable_swap_iff {mγ : measurable_space γ} {f : α × β → γ} :
  measurable (f ∘ prod.swap) ↔ measurable f :=
⟨λ hf, by { convert hf.comp measurable_swap, ext ⟨x, y⟩, refl }, λ hf, hf.comp measurable_swap⟩

@[measurability]
lemma measurable_set.prod {s : set α} {t : set β} (hs : measurable_set s) (ht : measurable_set t) :
  measurable_set (s ×ˢ t) :=
measurable_set.inter (measurable_fst hs) (measurable_snd ht)

lemma measurable_set_prod_of_nonempty {s : set α} {t : set β} (h : (s ×ˢ t : set _).nonempty) :
  measurable_set (s ×ˢ t) ↔ measurable_set s ∧ measurable_set t :=
begin
  rcases h with ⟨⟨x, y⟩, hx, hy⟩,
  refine ⟨λ hst, _, λ h, h.1.prod h.2⟩,
  have : measurable_set ((λ x, (x, y)) ⁻¹' s ×ˢ t) := measurable_prod_mk_right hst,
  have : measurable_set (prod.mk x ⁻¹' s ×ˢ t) := measurable_prod_mk_left hst,
  simp * at *
end

lemma measurable_set_prod {s : set α} {t : set β} :
  measurable_set (s ×ˢ t) ↔ (measurable_set s ∧ measurable_set t) ∨ s = ∅ ∨ t = ∅ :=
begin
  cases (s ×ˢ t : set _).eq_empty_or_nonempty with h h,
  { simp [h, prod_eq_empty_iff.mp h] },
  { simp [←not_nonempty_iff_eq_empty, prod_nonempty_iff.mp h, measurable_set_prod_of_nonempty h] }
end

lemma measurable_set_swap_iff {s : set (α × β)} :
  measurable_set (prod.swap ⁻¹' s) ↔ measurable_set s :=
⟨λ hs, by { convert measurable_swap hs, ext ⟨x, y⟩, refl }, λ hs, measurable_swap hs⟩

lemma measurable_from_prod_encodable [encodable β] [measurable_singleton_class β]
  {mγ : measurable_space γ} {f : α × β → γ} (hf : ∀ y, measurable (λ x, f (x, y))) :
  measurable f :=
begin
  intros s hs,
  have : f ⁻¹' s = ⋃ y, ((λ x, f (x, y)) ⁻¹' s) ×ˢ ({y} : set β),
  { ext1 ⟨x, y⟩,
    simp [and_assoc, and.left_comm] },
  rw this,
  exact measurable_set.Union (λ y, (hf y hs).prod (measurable_set_singleton y))
end

/-- A piecewise function on countably many pieces is measurable if all the data is measurable. -/
@[measurability]
lemma measurable.find {m : measurable_space α}
  {f : ℕ → α → β} {p : ℕ → α → Prop} [∀ n, decidable_pred (p n)]
  (hf : ∀ n, measurable (f n)) (hp : ∀ n, measurable_set {x | p n x}) (h : ∀ x, ∃ n, p n x) :
  measurable (λ x, f (nat.find (h x)) x) :=
begin
  have : measurable (λ (p : α × ℕ), f p.2 p.1) := measurable_from_prod_encodable (λ n, hf n),
  exact this.comp (measurable.prod_mk measurable_id (measurable_find h hp)),
end

/-- Given countably many disjoint measurable sets `t n` and countably many measurable
functions `g n`, one can construct a measurable function that coincides with `g n` on `t n`. -/
lemma exists_measurable_piecewise_nat {m : measurable_space α} (t : ℕ → set β)
  (t_meas : ∀ n, measurable_set (t n)) (t_disj : pairwise (disjoint on t))
  (g : ℕ → β → α) (hg : ∀ n, measurable (g n)) :
  ∃ f : β → α, measurable f ∧ (∀ n x, x ∈ t n → f x = g n x) :=
begin
  classical,
  let p : ℕ → β → Prop := λ n x, x ∈ t n ∪ (⋃ k, t k)ᶜ,
  have M : ∀ n, measurable_set {x | p n x} :=
    λ n, (t_meas n).union (measurable_set.compl (measurable_set.Union t_meas)),
  have P : ∀ x, ∃ n, p n x,
  { assume x,
    by_cases H : ∀ (i : ℕ), x ∉ t i,
    { exact ⟨0, or.inr (by simpa only [mem_Inter, compl_Union] using H)⟩ },
    { simp only [not_forall, not_not_mem] at H,
      rcases H with ⟨n, hn⟩,
      exact ⟨n, or.inl hn⟩ } },
  refine ⟨λ x, g (nat.find (P x)) x, measurable.find hg M P, _⟩,
  assume n x hx,
  have : x ∈ t (nat.find (P x)),
  { have B : x ∈ t (nat.find (P x)) ∪ (⋃ k, t k)ᶜ := nat.find_spec (P x),
    have B' : (∀ (i : ℕ), x ∉ t i) ↔ false,
    { simp only [iff_false, not_forall, not_not_mem], exact ⟨n, hx⟩ },
    simpa only [B', mem_union_eq, mem_Inter, or_false, compl_Union, mem_compl_eq] using B },
  congr,
  by_contra h,
  exact t_disj n (nat.find (P x)) (ne.symm h) ⟨hx, this⟩
end

end prod

section pi

variables {π : δ → Type*} [measurable_space α]

instance measurable_space.pi [m : Π a, measurable_space (π a)] : measurable_space (Π a, π a) :=
⨆ a, (m a).comap (λ b, b a)

variables [Π a, measurable_space (π a)] [measurable_space γ]

lemma measurable_pi_iff {g : α → Π a, π a} :
  measurable g ↔ ∀ a, measurable (λ x, g x a) :=
by simp_rw [measurable_iff_comap_le, measurable_space.pi, measurable_space.comap_supr,
    measurable_space.comap_comp, function.comp, supr_le_iff]

@[measurability]
lemma measurable_pi_apply (a : δ) : measurable (λ f : Π a, π a, f a) :=
measurable.of_comap_le $ le_supr _ a

@[measurability]
lemma measurable.eval {a : δ} {g : α → Π a, π a}
  (hg : measurable g) : measurable (λ x, g x a) :=
(measurable_pi_apply a).comp hg

@[measurability]
lemma measurable_pi_lambda (f : α → Π a, π a) (hf : ∀ a, measurable (λ c, f c a)) :
  measurable f :=
measurable_pi_iff.mpr hf

/-- The function `update f a : π a → Π a, π a` is always measurable.
  This doesn't require `f` to be measurable.
  This should not be confused with the statement that `update f a x` is measurable. -/
@[measurability]
lemma measurable_update (f : Π (a : δ), π a) {a : δ} [decidable_eq δ] : measurable (update f a) :=
begin
  apply measurable_pi_lambda,
  intro x, by_cases hx : x = a,
  { cases hx, convert measurable_id, ext, simp },
  simp_rw [update_noteq hx], apply measurable_const,
end

/- Even though we cannot use projection notation, we still keep a dot to be consistent with similar
  lemmas, like `measurable_set.prod`. -/
@[measurability]
lemma measurable_set.pi {s : set δ} {t : Π i : δ, set (π i)} (hs : countable s)
  (ht : ∀ i ∈ s, measurable_set (t i)) :
  measurable_set (s.pi t) :=
by { rw [pi_def], exact measurable_set.bInter hs (λ i hi, measurable_pi_apply _ (ht i hi)) }

lemma measurable_set.univ_pi [encodable δ] {t : Π i : δ, set (π i)}
  (ht : ∀ i, measurable_set (t i)) : measurable_set (pi univ t) :=
measurable_set.pi (countable_encodable _) (λ i _, ht i)

lemma measurable_set_pi_of_nonempty
  {s : set δ} {t : Π i, set (π i)} (hs : countable s)
  (h : (pi s t).nonempty) : measurable_set (pi s t) ↔ ∀ i ∈ s, measurable_set (t i) :=
begin
  classical,
  rcases h with ⟨f, hf⟩, refine ⟨λ hst i hi, _, measurable_set.pi hs⟩,
  convert measurable_update f hst, rw [update_preimage_pi hi], exact λ j hj _, hf j hj
end

lemma measurable_set_pi {s : set δ} {t : Π i, set (π i)} (hs : countable s) :
  measurable_set (pi s t) ↔ (∀ i ∈ s, measurable_set (t i)) ∨ pi s t = ∅ :=
begin
  cases (pi s t).eq_empty_or_nonempty with h h,
  { simp [h] },
  { simp [measurable_set_pi_of_nonempty hs, h, ← not_nonempty_iff_eq_empty] }
end

section
variable (π)

@[measurability]
lemma measurable_pi_equiv_pi_subtype_prod_symm (p : δ → Prop) [decidable_pred p] :
  measurable (equiv.pi_equiv_pi_subtype_prod p π).symm :=
begin
  apply measurable_pi_iff.2 (λ j, _),
  by_cases hj : p j,
  { simp only [hj, dif_pos, equiv.pi_equiv_pi_subtype_prod_symm_apply],
    have : measurable (λ (f : (Π (i : {x // p x}), π ↑i)), f ⟨j, hj⟩) :=
      measurable_pi_apply ⟨j, hj⟩,
    exact measurable.comp this measurable_fst },
  { simp only [hj, equiv.pi_equiv_pi_subtype_prod_symm_apply, dif_neg, not_false_iff],
    have : measurable (λ (f : (Π (i : {x // ¬ p x}), π ↑i)), f ⟨j, hj⟩) :=
      measurable_pi_apply ⟨j, hj⟩,
    exact measurable.comp this measurable_snd }
end

@[measurability]
lemma measurable_pi_equiv_pi_subtype_prod (p : δ → Prop) [decidable_pred p] :
  measurable (equiv.pi_equiv_pi_subtype_prod p π) :=
begin
  refine measurable_prod.2 _,
  split;
  { apply measurable_pi_iff.2 (λ j, _),
    simp only [pi_equiv_pi_subtype_prod_apply, measurable_pi_apply] }
end

end

section fintype

local attribute [instance] fintype.to_encodable

lemma measurable_set.pi_fintype [fintype δ] {s : set δ} {t : Π i, set (π i)}
  (ht : ∀ i ∈ s, measurable_set (t i)) : measurable_set (pi s t) :=
measurable_set.pi (countable_encodable _) ht

lemma measurable_set.univ_pi_fintype [fintype δ] {t : Π i, set (π i)}
  (ht : ∀ i, measurable_set (t i)) : measurable_set (pi univ t) :=
measurable_set.pi_fintype (λ i _, ht i)

end fintype
end pi

instance tprod.measurable_space (π : δ → Type*) [∀ x, measurable_space (π x)] :
  ∀ (l : list δ), measurable_space (list.tprod π l)
| []        := punit.measurable_space
| (i :: is) := @prod.measurable_space _ _ _ (tprod.measurable_space is)

section tprod

open list

variables {π : δ → Type*} [∀ x, measurable_space (π x)]

lemma measurable_tprod_mk (l : list δ) : measurable (@tprod.mk δ π l) :=
begin
  induction l with i l ih,
  { exact measurable_const },
  { exact (measurable_pi_apply i).prod_mk ih }
end

lemma measurable_tprod_elim [decidable_eq δ] : ∀ {l : list δ} {i : δ} (hi : i ∈ l),
  measurable (λ (v : tprod π l), v.elim hi)
| (i :: is) j hj := begin
  by_cases hji : j = i,
  { subst hji, simp [measurable_fst] },
  { rw [funext $ tprod.elim_of_ne _ hji],
    exact (measurable_tprod_elim (hj.resolve_left hji)).comp measurable_snd }
end

lemma measurable_tprod_elim' [decidable_eq δ] {l : list δ} (h : ∀ i, i ∈ l) :
  measurable (tprod.elim' h : tprod π l → Π i, π i) :=
measurable_pi_lambda _ (λ i, measurable_tprod_elim (h i))

lemma measurable_set.tprod (l : list δ) {s : ∀ i, set (π i)} (hs : ∀ i, measurable_set (s i)) :
  measurable_set (set.tprod l s) :=
by { induction l with i l ih, exact measurable_set.univ, exact (hs i).prod ih }

end tprod

instance {α β} [m₁ : measurable_space α] [m₂ : measurable_space β] : measurable_space (α ⊕ β) :=
m₁.map sum.inl ⊓ m₂.map sum.inr

section sum

@[measurability] lemma measurable_inl [measurable_space α] [measurable_space β] :
  measurable (@sum.inl α β) :=
measurable.of_le_map inf_le_left

@[measurability] lemma measurable_inr [measurable_space α] [measurable_space β] :
  measurable (@sum.inr α β) :=
measurable.of_le_map inf_le_right

variables {m : measurable_space α} {mβ : measurable_space β}

include m mβ

lemma measurable_sum {mγ : measurable_space γ} {f : α ⊕ β → γ}
  (hl : measurable (f ∘ sum.inl)) (hr : measurable (f ∘ sum.inr)) : measurable f :=
measurable.of_comap_le $ le_inf
  (measurable_space.comap_le_iff_le_map.2 $ hl)
  (measurable_space.comap_le_iff_le_map.2 $ hr)

@[measurability]
lemma measurable.sum_elim {mγ : measurable_space γ} {f : α → γ} {g : β → γ}
  (hf : measurable f) (hg : measurable g) :
  measurable (sum.elim f g) :=
measurable_sum hf hg

lemma measurable_set.inl_image {s : set α} (hs : measurable_set s) :
  measurable_set (sum.inl '' s : set (α ⊕ β)) :=
⟨show measurable_set (sum.inl ⁻¹' _), by { rwa [preimage_image_eq], exact (λ a b, sum.inl.inj) },
  have sum.inr ⁻¹' (sum.inl '' s : set (α ⊕ β)) = ∅ :=
    eq_empty_of_subset_empty $ assume x ⟨y, hy, eq⟩, by contradiction,
  show measurable_set (sum.inr ⁻¹' _), by { rw [this], exact measurable_set.empty }⟩

lemma measurable_set_inr_image {s : set β} (hs : measurable_set s) :
  measurable_set (sum.inr '' s : set (α ⊕ β)) :=
⟨ have sum.inl ⁻¹' (sum.inr '' s : set (α ⊕ β)) = ∅ :=
    eq_empty_of_subset_empty $ assume x ⟨y, hy, eq⟩, by contradiction,
  show measurable_set (sum.inl ⁻¹' _), by { rw [this], exact measurable_set.empty },
  show measurable_set (sum.inr ⁻¹' _), by { rwa [preimage_image_eq], exact λ a b, sum.inr.inj }⟩

omit m

lemma measurable_set_range_inl [measurable_space α] :
  measurable_set (range sum.inl : set (α ⊕ β)) :=
by { rw [← image_univ], exact measurable_set.univ.inl_image }

lemma measurable_set_range_inr [measurable_space α] :
  measurable_set (range sum.inr : set (α ⊕ β)) :=
by { rw [← image_univ], exact measurable_set_inr_image measurable_set.univ }

end sum

instance {α} {β : α → Type*} [m : Πa, measurable_space (β a)] : measurable_space (sigma β) :=
⨅a, (m a).map (sigma.mk a)

end constructions

/-- A map `f : α → β` is called a *measurable embedding* if it is injective, measurable, and sends
measurable sets to measurable sets. The latter assumption can be replaced with “`f` has measurable
inverse `g : range f → α`”, see `measurable_embedding.measurable_range_splitting`,
`measurable_embedding.of_measurable_inverse_range`, and
`measurable_embedding.of_measurable_inverse`.

One more interpretation: `f` is a measurable embedding if it defines a measurable equivalence to its
range and the range is a measurable set. One implication is formalized as
`measurable_embedding.equiv_range`; the other one follows from
`measurable_equiv.measurable_embedding`, `measurable_embedding.subtype_coe`, and
`measurable_embedding.comp`. -/
@[protect_proj]
structure measurable_embedding {α β : Type*} [measurable_space α] [measurable_space β] (f : α → β) :
  Prop :=
(injective : injective f)
(measurable : measurable f)
(measurable_set_image' : ∀ ⦃s⦄, measurable_set s → measurable_set (f '' s))

namespace measurable_embedding

variables {mα : measurable_space α} [measurable_space β] [measurable_space γ]
  {f : α → β} {g : β → γ}

include mα

lemma measurable_set_image (hf : measurable_embedding f) {s : set α} :
  measurable_set (f '' s) ↔ measurable_set s :=
⟨λ h, by simpa only [hf.injective.preimage_image] using hf.measurable h,
  λ h, hf.measurable_set_image' h⟩

lemma id : measurable_embedding (id : α → α) :=
⟨injective_id, measurable_id, λ s hs, by rwa image_id⟩

lemma comp (hg : measurable_embedding g) (hf : measurable_embedding f) :
  measurable_embedding (g ∘ f) :=
⟨hg.injective.comp hf.injective, hg.measurable.comp hf.measurable,
  λ s hs, by rwa [← image_image, hg.measurable_set_image, hf.measurable_set_image]⟩

lemma subtype_coe {s : set α} (hs : measurable_set s) : measurable_embedding (coe : s → α) :=
{ injective := subtype.coe_injective,
  measurable := measurable_subtype_coe,
  measurable_set_image' := λ _, measurable_set.subtype_image hs }

lemma measurable_set_range (hf : measurable_embedding f) : measurable_set (range f) :=
by { rw ← image_univ, exact hf.measurable_set_image' measurable_set.univ }

lemma measurable_set_preimage (hf : measurable_embedding f) {s : set β} :
  measurable_set (f ⁻¹' s) ↔ measurable_set (s ∩ range f) :=
by rw [← image_preimage_eq_inter_range, hf.measurable_set_image]

lemma measurable_range_splitting (hf : measurable_embedding f) :
  measurable (range_splitting f) :=
λ s hs, by rwa [preimage_range_splitting hf.injective,
  ← (subtype_coe hf.measurable_set_range).measurable_set_image, ← image_comp,
  coe_comp_range_factorization, hf.measurable_set_image]

lemma measurable_extend (hf : measurable_embedding f) {g : α → γ} {g' : β → γ}
  (hg : measurable g) (hg' : measurable g') :
  measurable (extend f g g') :=
begin
  refine measurable_of_restrict_of_restrict_compl hf.measurable_set_range _ _,
  { rw restrict_extend_range,
    simpa only [range_splitting] using hg.comp hf.measurable_range_splitting },
  { rw restrict_extend_compl_range, exact hg'.comp measurable_subtype_coe }
end

lemma exists_measurable_extend (hf : measurable_embedding f) {g : α → γ} (hg : measurable g)
  (hne : β → nonempty γ) :
  ∃ g' : β → γ, measurable g' ∧ g' ∘ f = g :=
⟨extend f g (λ x, classical.choice (hne x)),
  hf.measurable_extend hg (measurable_const' $ λ _ _, rfl),
  funext $ λ x, extend_apply hf.injective _ _ _⟩

lemma measurable_comp_iff (hg : measurable_embedding g) : measurable (g ∘ f) ↔ measurable f :=
begin
  refine ⟨λ H, _, hg.measurable.comp⟩,
  suffices : measurable ((range_splitting g ∘ range_factorization g) ∘ f),
    by rwa [(right_inverse_range_splitting hg.injective).comp_eq_id] at this,
  exact hg.measurable_range_splitting.comp H.subtype_mk
end

end measurable_embedding

lemma measurable_set.exists_measurable_proj {m : measurable_space α} {s : set α}
  (hs : measurable_set s) (hne : s.nonempty) : ∃ f : α → s, measurable f ∧ ∀ x : s, f x = x :=
let ⟨f, hfm, hf⟩ := (measurable_embedding.subtype_coe hs).exists_measurable_extend
  measurable_id (λ _, hne.to_subtype)
in ⟨f, hfm, congr_fun hf⟩

/-- Equivalences between measurable spaces. Main application is the simplification of measurability
statements along measurable equivalences. -/
structure measurable_equiv (α β : Type*) [measurable_space α] [measurable_space β] extends α ≃ β :=
(measurable_to_fun : measurable to_equiv)
(measurable_inv_fun : measurable to_equiv.symm)

infix ` ≃ᵐ `:25 := measurable_equiv

namespace measurable_equiv

variables (α β) [measurable_space α] [measurable_space β] [measurable_space γ] [measurable_space δ]

instance : has_coe_to_fun (α ≃ᵐ β) (λ _, α → β) := ⟨λ e, e.to_fun⟩

variables {α β}

@[simp] lemma coe_to_equiv (e : α ≃ᵐ β) : (e.to_equiv : α → β) = e := rfl

@[measurability]
protected lemma measurable (e : α ≃ᵐ β) : measurable (e : α → β) :=
e.measurable_to_fun

@[simp] lemma coe_mk (e : α ≃ β) (h1 : measurable e) (h2 : measurable e.symm) :
  ((⟨e, h1, h2⟩ : α ≃ᵐ β) : α → β) = e := rfl

/-- Any measurable space is equivalent to itself. -/
def refl (α : Type*) [measurable_space α] : α ≃ᵐ α :=
{ to_equiv := equiv.refl α,
  measurable_to_fun := measurable_id, measurable_inv_fun := measurable_id }

instance : inhabited (α ≃ᵐ α) := ⟨refl α⟩

/-- The composition of equivalences between measurable spaces. -/
def trans (ab : α ≃ᵐ β) (bc : β ≃ᵐ γ) :
  α ≃ᵐ γ :=
{ to_equiv := ab.to_equiv.trans bc.to_equiv,
  measurable_to_fun := bc.measurable_to_fun.comp ab.measurable_to_fun,
  measurable_inv_fun := ab.measurable_inv_fun.comp bc.measurable_inv_fun }

/-- The inverse of an equivalence between measurable spaces. -/
def symm (ab : α ≃ᵐ β) : β ≃ᵐ α :=
{ to_equiv := ab.to_equiv.symm,
  measurable_to_fun := ab.measurable_inv_fun,
  measurable_inv_fun := ab.measurable_to_fun }

@[simp] lemma coe_to_equiv_symm (e : α ≃ᵐ β) : (e.to_equiv.symm : β → α) = e.symm := rfl

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def simps.apply (h : α ≃ᵐ β) : α → β := h
/-- See Note [custom simps projection] -/
def simps.symm_apply (h : α ≃ᵐ β) : β → α := h.symm

initialize_simps_projections measurable_equiv
  (to_equiv_to_fun → apply, to_equiv_inv_fun → symm_apply)

lemma to_equiv_injective : injective (to_equiv : (α ≃ᵐ β) → (α ≃ β)) :=
by { rintro ⟨e₁, _, _⟩ ⟨e₂, _, _⟩ (rfl : e₁ = e₂), refl }

@[ext] lemma ext {e₁ e₂ : α ≃ᵐ β} (h : (e₁ : α → β) = e₂) : e₁ = e₂ :=
to_equiv_injective $ equiv.coe_fn_injective h

@[simp] lemma symm_mk (e : α ≃ β) (h1 : measurable e) (h2 : measurable e.symm) :
  (⟨e, h1, h2⟩ : α ≃ᵐ β).symm = ⟨e.symm, h2, h1⟩ := rfl

attribute [simps apply to_equiv] trans refl

@[simp] lemma symm_refl (α : Type*) [measurable_space α] : (refl α).symm = refl α := rfl

@[simp] theorem symm_comp_self (e : α ≃ᵐ β) : e.symm ∘ e = id := funext e.left_inv

@[simp] theorem self_comp_symm (e : α ≃ᵐ β) : e ∘ e.symm = id := funext e.right_inv

@[simp] theorem apply_symm_apply (e : α ≃ᵐ β) (y : β) : e (e.symm y) = y := e.right_inv y

@[simp] theorem symm_apply_apply (e : α ≃ᵐ β) (x : α) : e.symm (e x) = x := e.left_inv x

@[simp] theorem symm_trans_self (e : α ≃ᵐ β) : e.symm.trans e = refl β :=
ext e.self_comp_symm

@[simp] theorem self_trans_symm (e : α ≃ᵐ β) : e.trans e.symm = refl α :=
ext e.symm_comp_self

protected theorem surjective (e : α ≃ᵐ β) : surjective e := e.to_equiv.surjective
protected theorem bijective (e : α ≃ᵐ β) : bijective e := e.to_equiv.bijective
protected theorem injective (e : α ≃ᵐ β) : injective e := e.to_equiv.injective

@[simp] theorem symm_preimage_preimage (e : α ≃ᵐ β) (s : set β) : e.symm ⁻¹' (e ⁻¹' s) = s :=
e.to_equiv.symm_preimage_preimage s

theorem image_eq_preimage (e : α ≃ᵐ β) (s : set α) : e '' s = e.symm ⁻¹' s :=
e.to_equiv.image_eq_preimage s

@[simp] theorem measurable_set_preimage (e : α ≃ᵐ β) {s : set β} :
  measurable_set (e ⁻¹' s) ↔ measurable_set s :=
⟨λ h, by simpa only [symm_preimage_preimage] using e.symm.measurable h, λ h, e.measurable h⟩

@[simp] theorem measurable_set_image (e : α ≃ᵐ β) {s : set α} :
  measurable_set (e '' s) ↔ measurable_set s :=
by rw [image_eq_preimage, measurable_set_preimage]

/-- A measurable equivalence is a measurable embedding. -/
protected lemma measurable_embedding (e : α ≃ᵐ β) : measurable_embedding e :=
{ injective := e.injective,
  measurable := e.measurable,
  measurable_set_image' := λ s, e.measurable_set_image.2 }

/-- Equal measurable spaces are equivalent. -/
protected def cast {α β} [i₁ : measurable_space α] [i₂ : measurable_space β]
  (h : α = β) (hi : i₁ == i₂) : α ≃ᵐ β :=
{ to_equiv := equiv.cast h,
  measurable_to_fun  := by { substI h, substI hi, exact measurable_id },
  measurable_inv_fun := by { substI h, substI hi, exact measurable_id }}

protected lemma measurable_comp_iff {f : β → γ} (e : α ≃ᵐ β) :
  measurable (f ∘ e) ↔ measurable f :=
iff.intro
  (assume hfe,
    have measurable (f ∘ (e.symm.trans e).to_equiv) := hfe.comp e.symm.measurable,
    by rwa [coe_to_equiv, symm_trans_self] at this)
  (λ h, h.comp e.measurable)

/-- Any two types with unique elements are measurably equivalent. -/
def of_unique_of_unique (α β : Type*) [measurable_space α] [measurable_space β]
  [unique α] [unique β] : α ≃ᵐ β :=
{ to_equiv := equiv_of_unique_of_unique,
  measurable_to_fun := subsingleton.measurable,
  measurable_inv_fun := subsingleton.measurable }

/-- Products of equivalent measurable spaces are equivalent. -/
def prod_congr (ab : α ≃ᵐ β) (cd : γ ≃ᵐ δ) : α × γ ≃ᵐ β × δ :=
{ to_equiv := prod_congr ab.to_equiv cd.to_equiv,
  measurable_to_fun := (ab.measurable_to_fun.comp measurable_id.fst).prod_mk
    (cd.measurable_to_fun.comp measurable_id.snd),
  measurable_inv_fun := (ab.measurable_inv_fun.comp measurable_id.fst).prod_mk
    (cd.measurable_inv_fun.comp measurable_id.snd) }

/-- Products of measurable spaces are symmetric. -/
def prod_comm : α × β ≃ᵐ β × α :=
{ to_equiv := prod_comm α β,
  measurable_to_fun  := measurable_id.snd.prod_mk measurable_id.fst,
  measurable_inv_fun := measurable_id.snd.prod_mk measurable_id.fst }

/-- Products of measurable spaces are associative. -/
def prod_assoc : (α × β) × γ ≃ᵐ α × (β × γ) :=
{ to_equiv := prod_assoc α β γ,
  measurable_to_fun  := measurable_fst.fst.prod_mk $ measurable_fst.snd.prod_mk measurable_snd,
  measurable_inv_fun := (measurable_fst.prod_mk measurable_snd.fst).prod_mk measurable_snd.snd }

/-- Sums of measurable spaces are symmetric. -/
def sum_congr (ab : α ≃ᵐ β) (cd : γ ≃ᵐ δ) : α ⊕ γ ≃ᵐ β ⊕ δ :=
{ to_equiv := sum_congr ab.to_equiv cd.to_equiv,
  measurable_to_fun :=
    begin
      cases ab with ab' abm, cases ab', cases cd with cd' cdm, cases cd',
      refine measurable_sum (measurable_inl.comp abm) (measurable_inr.comp cdm)
    end,
  measurable_inv_fun :=
    begin
      cases ab with ab' _ abm, cases ab', cases cd with cd' _ cdm, cases cd',
      refine measurable_sum (measurable_inl.comp abm) (measurable_inr.comp cdm)
    end }

/-- `s ×ˢ t ≃ (s × t)` as measurable spaces. -/
def set.prod (s : set α) (t : set β) : ↥(s ×ˢ t) ≃ᵐ s × t :=
{ to_equiv := equiv.set.prod s t,
  measurable_to_fun := measurable_id.subtype_coe.fst.subtype_mk.prod_mk
    measurable_id.subtype_coe.snd.subtype_mk,
  measurable_inv_fun := measurable.subtype_mk $ measurable_id.fst.subtype_coe.prod_mk
    measurable_id.snd.subtype_coe }

/-- `univ α ≃ α` as measurable spaces. -/
def set.univ (α : Type*) [measurable_space α] : (univ : set α) ≃ᵐ α :=
{ to_equiv := equiv.set.univ α,
  measurable_to_fun := measurable_id.subtype_coe,
  measurable_inv_fun := measurable_id.subtype_mk }

/-- `{a} ≃ unit` as measurable spaces. -/
def set.singleton (a : α) : ({a} : set α) ≃ᵐ unit :=
{ to_equiv := equiv.set.singleton a,
  measurable_to_fun := measurable_const,
  measurable_inv_fun := measurable_const }

/-- A set is equivalent to its image under a function `f` as measurable spaces,
  if `f` is an injective measurable function that sends measurable sets to measurable sets. -/
noncomputable def set.image (f : α → β) (s : set α) (hf : injective f)
  (hfm : measurable f) (hfi : ∀ s, measurable_set s → measurable_set (f '' s)) : s ≃ᵐ (f '' s) :=
{ to_equiv := equiv.set.image f s hf,
  measurable_to_fun  := (hfm.comp measurable_id.subtype_coe).subtype_mk,
  measurable_inv_fun :=
    begin
      rintro t ⟨u, hu, rfl⟩, simp [preimage_preimage, set.image_symm_preimage hf],
      exact measurable_subtype_coe (hfi u hu)
    end }

/-- The domain of `f` is equivalent to its range as measurable spaces,
  if `f` is an injective measurable function that sends measurable sets to measurable sets. -/
noncomputable def set.range (f : α → β) (hf : injective f) (hfm : measurable f)
  (hfi : ∀ s, measurable_set s → measurable_set (f '' s)) :
  α ≃ᵐ (range f) :=
(measurable_equiv.set.univ _).symm.trans $
  (measurable_equiv.set.image f univ hf hfm hfi).trans $
  measurable_equiv.cast (by rw image_univ) (by rw image_univ)

/-- `α` is equivalent to its image in `α ⊕ β` as measurable spaces. -/
def set.range_inl : (range sum.inl : set (α ⊕ β)) ≃ᵐ α :=
{ to_fun    := λ ab, match ab with
    | ⟨sum.inl a, _⟩ := a
    | ⟨sum.inr b, p⟩ := have false, by { cases p, contradiction }, this.elim
    end,
  inv_fun   := λ a, ⟨sum.inl a, a, rfl⟩,
  left_inv  := by { rintro ⟨ab, a, rfl⟩, refl },
  right_inv := assume a, rfl,
  measurable_to_fun  := assume s (hs : measurable_set s),
    begin
      refine ⟨_, hs.inl_image, set.ext _⟩,
      rintros ⟨ab, a, rfl⟩,
      simp [set.range_inl._match_1]
    end,
  measurable_inv_fun := measurable.subtype_mk measurable_inl }

/-- `β` is equivalent to its image in `α ⊕ β` as measurable spaces. -/
def set.range_inr : (range sum.inr : set (α ⊕ β)) ≃ᵐ β :=
{ to_fun    := λ ab, match ab with
    | ⟨sum.inr b, _⟩ := b
    | ⟨sum.inl a, p⟩ := have false, by { cases p, contradiction }, this.elim
    end,
  inv_fun   := λ b, ⟨sum.inr b, b, rfl⟩,
  left_inv  := by { rintro ⟨ab, b, rfl⟩, refl },
  right_inv := assume b, rfl,
  measurable_to_fun  := assume s (hs : measurable_set s),
    begin
      refine ⟨_, measurable_set_inr_image hs, set.ext _⟩,
      rintros ⟨ab, b, rfl⟩,
      simp [set.range_inr._match_1]
    end,
  measurable_inv_fun := measurable.subtype_mk measurable_inr }

/-- Products distribute over sums (on the right) as measurable spaces. -/
def sum_prod_distrib (α β γ) [measurable_space α] [measurable_space β] [measurable_space γ] :
  (α ⊕ β) × γ ≃ᵐ (α × γ) ⊕ (β × γ) :=
{ to_equiv := sum_prod_distrib α β γ,
  measurable_to_fun  :=
  begin
    refine measurable_of_measurable_union_cover
      (range sum.inl ×ˢ (univ : set γ))
      (range sum.inr ×ˢ (univ : set γ))
      (measurable_set_range_inl.prod measurable_set.univ)
      (measurable_set_range_inr.prod measurable_set.univ)
      (by { rintro ⟨a|b, c⟩; simp [set.prod_eq] })
      _
      _,
    { refine (set.prod (range sum.inl) univ).symm.measurable_comp_iff.1 _,
      refine (prod_congr set.range_inl (set.univ _)).symm.measurable_comp_iff.1 _,
      dsimp [(∘)],
      convert measurable_inl,
      ext ⟨a, c⟩, refl },
    { refine (set.prod (range sum.inr) univ).symm.measurable_comp_iff.1 _,
      refine (prod_congr set.range_inr (set.univ _)).symm.measurable_comp_iff.1 _,
      dsimp [(∘)],
      convert measurable_inr,
      ext ⟨b, c⟩, refl }
  end,
  measurable_inv_fun :=
    measurable_sum
      ((measurable_inl.comp measurable_fst).prod_mk measurable_snd)
      ((measurable_inr.comp measurable_fst).prod_mk measurable_snd) }

/-- Products distribute over sums (on the left) as measurable spaces. -/
def prod_sum_distrib (α β γ) [measurable_space α] [measurable_space β] [measurable_space γ] :
  α × (β ⊕ γ) ≃ᵐ (α × β) ⊕ (α × γ) :=
prod_comm.trans $ (sum_prod_distrib _ _ _).trans $ sum_congr prod_comm prod_comm

/-- Products distribute over sums as measurable spaces. -/
def sum_prod_sum (α β γ δ)
  [measurable_space α] [measurable_space β] [measurable_space γ] [measurable_space δ] :
  (α ⊕ β) × (γ ⊕ δ) ≃ᵐ ((α × γ) ⊕ (α × δ)) ⊕ ((β × γ) ⊕ (β × δ)) :=
(sum_prod_distrib _ _ _).trans $ sum_congr (prod_sum_distrib _ _ _) (prod_sum_distrib _ _ _)

variables {π π' : δ' → Type*} [∀ x, measurable_space (π x)] [∀ x, measurable_space (π' x)]

/-- A family of measurable equivalences `Π a, β₁ a ≃ᵐ β₂ a` generates a measurable equivalence
  between  `Π a, β₁ a` and `Π a, β₂ a`. -/
def Pi_congr_right (e : Π a, π a ≃ᵐ π' a) : (Π a, π a) ≃ᵐ (Π a, π' a) :=
{ to_equiv := Pi_congr_right (λ a, (e a).to_equiv),
  measurable_to_fun :=
    measurable_pi_lambda _ (λ i, (e i).measurable_to_fun.comp (measurable_pi_apply i)),
  measurable_inv_fun :=
    measurable_pi_lambda _ (λ i, (e i).measurable_inv_fun.comp (measurable_pi_apply i)) }

/-- Pi-types are measurably equivalent to iterated products. -/
@[simps {fully_applied := ff}]
def pi_measurable_equiv_tprod [decidable_eq δ']
  {l : list δ'} (hnd : l.nodup) (h : ∀ i, i ∈ l) :
  (Π i, π i) ≃ᵐ list.tprod π l :=
{ to_equiv := list.tprod.pi_equiv_tprod hnd h,
  measurable_to_fun := measurable_tprod_mk l,
  measurable_inv_fun := measurable_tprod_elim' h }

/-- If `α` has a unique term, then the type of function `α → β` is measurably equivalent to `β`. -/
@[simps {fully_applied := ff}] def fun_unique (α β : Type*) [unique α] [measurable_space β] :
  (α → β) ≃ᵐ β :=
{ to_equiv := equiv.fun_unique α β,
  measurable_to_fun := measurable_pi_apply _,
  measurable_inv_fun := measurable_pi_iff.2 $ λ b, measurable_id }

/-- The space `Π i : fin 2, α i` is measurably equivalent to `α 0 × α 1`. -/
@[simps {fully_applied := ff}] def pi_fin_two (α : fin 2 → Type*) [∀ i, measurable_space (α i)] :
  (Π i, α i) ≃ᵐ α 0 × α 1 :=
{ to_equiv := pi_fin_two_equiv α,
  measurable_to_fun := measurable.prod (measurable_pi_apply _) (measurable_pi_apply _),
  measurable_inv_fun := measurable_pi_iff.2 $
    fin.forall_fin_two.2 ⟨measurable_fst, measurable_snd⟩ }

/-- The space `fin 2 → α` is measurably equivalent to `α × α`. -/
@[simps {fully_applied := ff}] def fin_two_arrow : (fin 2 → α) ≃ᵐ α × α := pi_fin_two (λ _, α)

/-- Measurable equivalence between `Π j : fin (n + 1), α j` and
`α i × Π j : fin n, α (fin.succ_above i j)`. -/
@[simps {fully_applied := ff}]
def pi_fin_succ_above_equiv {n : ℕ} (α : fin (n + 1) → Type*) [Π i, measurable_space (α i)]
  (i : fin (n + 1)) :
  (Π j, α j) ≃ᵐ α i × (Π j, α (i.succ_above j)) :=
{ to_equiv := pi_fin_succ_above_equiv α i,
  measurable_to_fun := (measurable_pi_apply i).prod_mk $ measurable_pi_iff.2 $
    λ j, measurable_pi_apply _,
  measurable_inv_fun := by simp [measurable_pi_iff, i.forall_iff_succ_above, measurable_fst,
    (measurable_pi_apply _).comp measurable_snd]  }

variable (π)

/-- Measurable equivalence between (dependent) functions on a type and pairs of functions on
`{i // p i}` and `{i // ¬p i}`. See also `equiv.pi_equiv_pi_subtype_prod`. -/
@[simps {fully_applied := ff}]
def pi_equiv_pi_subtype_prod (p : δ' → Prop) [decidable_pred p] :
  (Π i, π i) ≃ᵐ ((Π i : subtype p, π i) × (Π i : {i // ¬p i}, π i)) :=
{ to_equiv := pi_equiv_pi_subtype_prod p π,
  measurable_to_fun := measurable_pi_equiv_pi_subtype_prod π p,
  measurable_inv_fun := measurable_pi_equiv_pi_subtype_prod_symm π p }

end measurable_equiv

namespace measurable_embedding

variables [measurable_space α] [measurable_space β] [measurable_space γ] {f : α → β}

/-- A measurable embedding defines a measurable equivalence between its domain
and its range. -/
noncomputable def equiv_range (f : α → β) (hf : measurable_embedding f) :
  α ≃ᵐ range f :=
{ to_equiv := equiv.of_injective f hf.injective,
  measurable_to_fun := hf.measurable.subtype_mk,
  measurable_inv_fun :=
    by { rw coe_of_injective_symm, exact hf.measurable_range_splitting } }

lemma of_measurable_inverse_on_range {g : range f → α} (hf₁ : measurable f)
  (hf₂ : measurable_set (range f)) (hg : measurable g)
  (H : left_inverse g (range_factorization f)) : measurable_embedding f :=
begin
  set e : α ≃ᵐ range f :=
    ⟨⟨range_factorization f, g, H, H.right_inverse_of_surjective surjective_onto_range⟩,
      hf₁.subtype_mk, hg⟩,
  exact (measurable_embedding.subtype_coe hf₂).comp e.measurable_embedding
end

lemma of_measurable_inverse {g : β → α} (hf₁ : measurable f)
  (hf₂ : measurable_set (range f)) (hg : measurable g)
  (H : left_inverse g f) : measurable_embedding f :=
of_measurable_inverse_on_range hf₁ hf₂ (hg.comp measurable_subtype_coe) H

end measurable_embedding

namespace filter

variables [measurable_space α]

/-- A filter `f` is measurably generates if each `s ∈ f` includes a measurable `t ∈ f`. -/
class is_measurably_generated (f : filter α) : Prop :=
(exists_measurable_subset : ∀ ⦃s⦄, s ∈ f → ∃ t ∈ f, measurable_set t ∧ t ⊆ s)

instance is_measurably_generated_bot : is_measurably_generated (⊥ : filter α) :=
⟨λ _ _, ⟨∅, mem_bot, measurable_set.empty, empty_subset _⟩⟩

instance is_measurably_generated_top : is_measurably_generated (⊤ : filter α) :=
⟨λ s hs, ⟨univ, univ_mem, measurable_set.univ, λ x _, hs x⟩⟩

lemma eventually.exists_measurable_mem {f : filter α} [is_measurably_generated f]
  {p : α → Prop} (h : ∀ᶠ x in f, p x) :
  ∃ s ∈ f, measurable_set s ∧ ∀ x ∈ s, p x :=
is_measurably_generated.exists_measurable_subset h

lemma eventually.exists_measurable_mem_of_small_sets {f : filter α} [is_measurably_generated f]
  {p : set α → Prop} (h : ∀ᶠ s in f.small_sets, p s) :
  ∃ s ∈ f, measurable_set s ∧ p s :=
let ⟨s, hsf, hs⟩ := eventually_small_sets.1 h,
  ⟨t, htf, htm, hts⟩ := is_measurably_generated.exists_measurable_subset hsf
in ⟨t, htf, htm, hs t hts⟩

instance inf_is_measurably_generated (f g : filter α) [is_measurably_generated f]
  [is_measurably_generated g] :
  is_measurably_generated (f ⊓ g) :=
begin
  refine ⟨_⟩,
  rintros t ⟨sf, hsf, sg, hsg, rfl⟩,
  rcases is_measurably_generated.exists_measurable_subset hsf with ⟨s'f, hs'f, hmf, hs'sf⟩,
  rcases is_measurably_generated.exists_measurable_subset hsg with ⟨s'g, hs'g, hmg, hs'sg⟩,
  refine ⟨s'f ∩ s'g, inter_mem_inf hs'f hs'g, hmf.inter hmg, _⟩,
  exact inter_subset_inter hs'sf hs'sg
end

lemma principal_is_measurably_generated_iff {s : set α} :
  is_measurably_generated (𝓟 s) ↔ measurable_set s :=
begin
  refine ⟨_, λ hs, ⟨λ t ht, ⟨s, mem_principal_self s, hs, ht⟩⟩⟩,
  rintros ⟨hs⟩,
  rcases hs (mem_principal_self s) with ⟨t, ht, htm, hts⟩,
  have : t = s := subset.antisymm hts ht,
  rwa ← this
end

alias principal_is_measurably_generated_iff ↔
  _ measurable_set.principal_is_measurably_generated

instance infi_is_measurably_generated {f : ι → filter α} [∀ i, is_measurably_generated (f i)] :
  is_measurably_generated (⨅ i, f i) :=
begin
  refine ⟨λ s hs, _⟩,
  rw [← equiv.plift.surjective.infi_comp, mem_infi] at hs,
  rcases hs with ⟨t, ht, ⟨V, hVf, rfl⟩⟩,
  choose U hUf hU using λ i, is_measurably_generated.exists_measurable_subset (hVf i),
  refine ⟨⋂ i : t, U i, _, _, _⟩,
  { rw [← equiv.plift.surjective.infi_comp, mem_infi],
    refine ⟨t, ht, U, hUf, rfl⟩ },
  { haveI := ht.countable.to_encodable,
    exact measurable_set.Inter (λ i, (hU i).1) },
  { exact Inter_mono (λ i, (hU i).2) }
end

end filter

/-- We say that a collection of sets is countably spanning if a countable subset spans the
  whole type. This is a useful condition in various parts of measure theory. For example, it is
  a needed condition to show that the product of two collections generate the product sigma algebra,
  see `generate_from_prod_eq`. -/
def is_countably_spanning (C : set (set α)) : Prop :=
∃ (s : ℕ → set α), (∀ n, s n ∈ C) ∧ (⋃ n, s n) = univ

lemma is_countably_spanning_measurable_set [measurable_space α] :
  is_countably_spanning {s : set α | measurable_set s} :=
⟨λ _, univ, λ _, measurable_set.univ, Union_const _⟩

namespace measurable_set

/-!
### Typeclasses on `subtype measurable_set`
-/

variables [measurable_space α]

instance : has_mem α (subtype (measurable_set : set α → Prop)) :=
⟨λ a s, a ∈ (s : set α)⟩

@[simp] lemma mem_coe (a : α) (s : subtype (measurable_set : set α → Prop)) :
  a ∈ (s : set α) ↔ a ∈ s := iff.rfl

instance : has_emptyc (subtype (measurable_set : set α → Prop)) :=
⟨⟨∅, measurable_set.empty⟩⟩

@[simp] lemma coe_empty : ↑(∅ : subtype (measurable_set : set α → Prop)) = (∅ : set α) := rfl

instance [measurable_singleton_class α] : has_insert α (subtype (measurable_set : set α → Prop)) :=
⟨λ a s, ⟨has_insert.insert a s, s.prop.insert a⟩⟩

@[simp] lemma coe_insert [measurable_singleton_class α] (a : α)
  (s : subtype (measurable_set : set α → Prop)) :
  ↑(has_insert.insert a s) = (has_insert.insert a s : set α) := rfl

instance : has_compl (subtype (measurable_set : set α → Prop)) :=
⟨λ x, ⟨xᶜ, x.prop.compl⟩⟩

@[simp] lemma coe_compl (s : subtype (measurable_set : set α → Prop)) : ↑(sᶜ) = (sᶜ : set α) := rfl

instance : has_union (subtype (measurable_set : set α → Prop)) :=
⟨λ x y, ⟨x ∪ y, x.prop.union y.prop⟩⟩

@[simp] lemma coe_union (s t : subtype (measurable_set : set α → Prop)) :
  ↑(s ∪ t) = (s ∪ t : set α) := rfl

instance : has_inter (subtype (measurable_set : set α → Prop)) :=
⟨λ x y, ⟨x ∩ y, x.prop.inter y.prop⟩⟩

@[simp] lemma coe_inter (s t : subtype (measurable_set : set α → Prop)) :
  ↑(s ∩ t) = (s ∩ t : set α) := rfl

instance : has_sdiff (subtype (measurable_set : set α → Prop)) :=
⟨λ x y, ⟨x \ y, x.prop.diff y.prop⟩⟩

@[simp] lemma coe_sdiff (s t : subtype (measurable_set : set α → Prop)) :
  ↑(s \ t) = (s \ t : set α) := rfl

instance : has_bot (subtype (measurable_set : set α → Prop)) :=
⟨⟨⊥, measurable_set.empty⟩⟩

@[simp] lemma coe_bot : ↑(⊥ : subtype (measurable_set : set α → Prop)) = (⊥ : set α) := rfl

instance : has_top (subtype (measurable_set : set α → Prop)) :=
⟨⟨⊤, measurable_set.univ⟩⟩

@[simp] lemma coe_top : ↑(⊤ : subtype (measurable_set : set α → Prop)) = (⊤ : set α) := rfl

instance : partial_order (subtype (measurable_set : set α → Prop)) :=
partial_order.lift _ subtype.coe_injective

instance : distrib_lattice (subtype (measurable_set : set α → Prop)) :=
{ sup := (∪),
  le_sup_left := λ a b, show (a : set α) ≤ a ⊔ b, from le_sup_left,
  le_sup_right := λ a b, show (b : set α) ≤ a ⊔ b, from le_sup_right,
  sup_le := λ a b c ha hb, show (a ⊔ b : set α) ≤ c, from sup_le ha hb,
  inf := (∩),
  inf_le_left := λ a b, show (a ⊓ b : set α) ≤ a, from inf_le_left,
  inf_le_right := λ a b, show (a ⊓ b : set α) ≤ b, from inf_le_right,
  le_inf := λ a b c ha hb, show (a : set α) ≤ b ⊓ c, from le_inf ha hb,
  le_sup_inf := λ x y z, show ((x ⊔ y) ⊓ (x ⊔ z) : set α) ≤ x ⊔ y ⊓ z, from le_sup_inf,
  .. measurable_set.subtype.partial_order }

instance : bounded_order (subtype (measurable_set : set α → Prop)) :=
{ top := ⊤,
  le_top := λ a, show (a : set α) ≤ ⊤, from le_top,
  bot := ⊥,
  bot_le := λ a, show (⊥ : set α) ≤ a, from bot_le }

instance : boolean_algebra (subtype (measurable_set : set α → Prop)) :=
{ sdiff := (\),
  sup_inf_sdiff := λ a b, subtype.eq $ sup_inf_sdiff a b,
  inf_inf_sdiff := λ a b, subtype.eq $ inf_inf_sdiff a b,
  compl := has_compl.compl,
  inf_compl_le_bot := λ a, boolean_algebra.inf_compl_le_bot (a : set α),
  top_le_sup_compl := λ a, boolean_algebra.top_le_sup_compl (a : set α),
  sdiff_eq := λ a b, subtype.eq $ sdiff_eq,
  .. measurable_set.subtype.bounded_order,
  .. measurable_set.subtype.distrib_lattice }

end measurable_set
