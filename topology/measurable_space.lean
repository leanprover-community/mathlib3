/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Measurable spaces -- σ-algberas
-/
import data.set order.galois_connection data.set.countable
open classical set lattice
local attribute [instance] decidable_inhabited prop_decidable

universes u v w x

structure measurable_space (α : Type u) :=
(is_measurable : set α → Prop)
(is_measurable_empty : is_measurable ∅)
(is_measurable_compl : ∀s, is_measurable s → is_measurable (- s))
(is_measurable_Union : ∀f:ℕ → set α, (∀i, is_measurable (f i)) → is_measurable (⋃i, f i))

attribute [class] measurable_space

variables {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x}
  {s t u : set α}

section
variable [m : measurable_space α]
include m

def is_measurable : set α → Prop := m.is_measurable

lemma is_measurable_empty : is_measurable (∅ : set α) := m.is_measurable_empty

lemma is_measurable_compl : is_measurable s → is_measurable (-s) :=
m.is_measurable_compl s

lemma is_measurable_Union_nat {f : ℕ → set α} : (∀i, is_measurable (f i)) → is_measurable (⋃i, f i) :=
m.is_measurable_Union f

lemma is_measurable_sUnion {s : set (set α)} (hs : countable s) (h : ∀t∈s, is_measurable t) :
  is_measurable (⋃₀ s) :=
let ⟨f, hf⟩ := countable_iff_exists_surjective.mp hs in
have (⋃₀ s) = (⋃i, if f i ∈ s then f i else ∅),
  from le_antisymm
    (Sup_le $ assume u hu, let ⟨i, hi⟩ := hf hu in le_supr_of_le i $ by simp [hi, hu, le_refl])
    (supr_le $ assume i, by_cases
      (assume : f i ∈ s, by simp [this]; exact subset_sUnion_of_mem this)
      (assume : f i ∉ s, by simp [this]; exact bot_le)),
begin
  rw [this],
  apply is_measurable_Union_nat _,
  intro i,
  by_cases f i ∈ s with h'; simp [h', h, is_measurable_empty]
end

lemma is_measurable_bUnion {f : β → set α} {s : set β} (hs : countable s)
  (h : ∀b∈s, is_measurable (f b)) : is_measurable (⋃b∈s, f b) :=
have ⋃₀ (f '' s) = (⋃a∈s, f a), from lattice.Sup_image,
by rw [←this];
from (is_measurable_sUnion (countable_image hs) $ assume a ⟨s', hs', eq⟩, eq ▸ h s' hs')

lemma is_measurable_Union [encodable β] {f : β → set α} (h : ∀b, is_measurable (f b)) :
  is_measurable (⋃b, f b) :=
have is_measurable (⋃b∈(univ : set β), f b),
  from is_measurable_bUnion countable_encodable $ assume b _, h b,
by simp [*] at *

lemma is_measurable_sInter {s : set (set α)} (hs : countable s) (h : ∀t∈s, is_measurable t) :
  is_measurable (⋂₀ s) :=
by rw [sInter_eq_comp_sUnion_compl, sUnion_image];
from is_measurable_compl (is_measurable_bUnion hs $ assume t ht, is_measurable_compl $ h t ht)

lemma is_measurable_bInter {f : β → set α} {s : set β} (hs : countable s)
  (h : ∀b∈s, is_measurable (f b)) : is_measurable (⋂b∈s, f b) :=
have ⋂₀ (f '' s) = (⋂a∈s, f a), from lattice.Inf_image,
by rw [←this];
from (is_measurable_sInter (countable_image hs) $ assume a ⟨s', hs', eq⟩, eq ▸ h s' hs')

lemma is_measurable_Inter [encodable β] {f : β → set α} (h : ∀b, is_measurable (f b)) :
  is_measurable (⋂b, f b) :=
by rw Inter_eq_comp_Union_comp;
from is_measurable_compl (is_measurable_Union $ assume b, is_measurable_compl $ h b)

lemma is_measurable_union {s₁ s₂ : set α}
  (h₁ : is_measurable s₁) (h₂ : is_measurable s₂) : is_measurable (s₁ ∪ s₂) :=
have s₁ ∪ s₂ = (⨆b ∈ ({tt, ff} : set bool), bool.cases_on b s₁ s₂),
  by simp [lattice.supr_or, lattice.supr_sup_eq]; refl,
by rw [this]; from is_measurable_bUnion countable_encodable (assume b,
  match b with
  | tt := by simp [h₂]
  | ff := by simp [h₁]
  end)

lemma is_measurable_inter {s₁ s₂ : set α}
  (h₁ : is_measurable s₁) (h₂ : is_measurable s₂) : is_measurable (s₁ ∩ s₂) :=
by rw [inter_eq_compl_compl_union_compl];
from is_measurable_compl (is_measurable_union (is_measurable_compl h₁) (is_measurable_compl h₂))

lemma is_measurable_sdiff {s₁ s₂ : set α}
  (h₁ : is_measurable s₁) (h₂ : is_measurable s₂) : is_measurable (s₁ \ s₂) :=
is_measurable_inter h₁ $ is_measurable_compl h₂

lemma is_measurable_sub {s₁ s₂ : set α} :
  is_measurable s₁ → is_measurable s₂ → is_measurable (s₁ - s₂) :=
is_measurable_sdiff

end

lemma measurable_space_eq :
  ∀{m₁ m₂ : measurable_space α}, (∀s:set α, m₁.is_measurable s ↔ m₂.is_measurable s) → m₁ = m₂
| ⟨s₁, _, _, _⟩ ⟨s₂, _, _, _⟩ h :=
  have s₁ = s₂, from funext $ assume x, propext $ h x,
  by subst this

namespace measurable_space
section complete_lattice

instance : partial_order (measurable_space α) :=
{ partial_order .
  le          := λm₁ m₂, m₁.is_measurable ≤ m₂.is_measurable,
  le_refl     := assume a b, le_refl _,
  le_trans    := assume a b c, le_trans,
  le_antisymm := assume a b h₁ h₂, measurable_space_eq $ assume s, ⟨h₁ s, h₂ s⟩ }

instance : has_top (measurable_space α) :=
⟨{measurable_space .
  is_measurable       := λs, true,
  is_measurable_empty := trivial,
  is_measurable_compl := assume s hs, trivial,
  is_measurable_Union := assume f hf, trivial }⟩

instance : has_bot (measurable_space α) :=
⟨{measurable_space .
  is_measurable       := λs, s = ∅ ∨ s = univ,
  is_measurable_empty := or.inl rfl,
  is_measurable_compl := by simp [or_imp_distrib] {contextual := tt},
  is_measurable_Union := assume f hf, by_cases
    (assume h : ∃i, f i = univ,
      let ⟨i, hi⟩ := h in
      or.inr $ eq_univ_of_univ_subset $ hi ▸ le_supr f i)
    (assume h : ¬ ∃i, f i = univ,
      or.inl $ eq_empty_of_subset_empty $ Union_subset $ assume i,
        (hf i).elim (by simp {contextual := tt}) (assume hi, false.elim $ h ⟨i, hi⟩)) }⟩

instance : has_inf (measurable_space α) :=
⟨λm₁ m₂, {measurable_space .
  is_measurable       := λs:set α, m₁.is_measurable s ∧ m₂.is_measurable s,
  is_measurable_empty := ⟨m₁.is_measurable_empty, m₂.is_measurable_empty⟩,
  is_measurable_compl := assume s ⟨h₁, h₂⟩, ⟨m₁.is_measurable_compl s h₁, m₂.is_measurable_compl s h₂⟩,
  is_measurable_Union := assume f hf,
    ⟨m₁.is_measurable_Union f (λi, (hf i).left), m₂.is_measurable_Union f (λi, (hf i).right)⟩ }⟩

instance : has_Inf (measurable_space α) :=
⟨λx, {measurable_space .
  is_measurable       := λs:set α, ∀m:measurable_space α, m ∈ x → m.is_measurable s,
  is_measurable_empty := assume m hm, m.is_measurable_empty,
  is_measurable_compl := assume s hs m hm, m.is_measurable_compl s $ hs _ hm,
  is_measurable_Union := assume f hf m hm, m.is_measurable_Union f $ assume i, hf _ _ hm }⟩

protected lemma le_Inf {s : set (measurable_space α)} {m : measurable_space α}
  (h : ∀m'∈s, m ≤ m') : m ≤ Inf s :=
assume s hs m hm, h m hm s hs

protected lemma Inf_le {s : set (measurable_space α)} {m : measurable_space α}
  (h : m ∈ s) : Inf s ≤ m :=
assume s hs, hs m h

instance : complete_lattice (measurable_space α) :=
{ measurable_space.partial_order with
  sup           := λa b, Inf {x | a ≤ x ∧ b ≤ x},
  le_sup_left   := assume a b, measurable_space.le_Inf $ assume x, assume h : a ≤ x ∧ b ≤ x, h.left,
  le_sup_right  := assume a b, measurable_space.le_Inf $ assume x, assume h : a ≤ x ∧ b ≤ x, h.right,
  sup_le        := assume a b c h₁ h₂,
    measurable_space.Inf_le $ show c ∈ {x | a ≤ x ∧ b ≤ x}, from ⟨h₁, h₂⟩,
  inf           := (⊓),
  le_inf        := assume a b h h₁ h₂ s hs, ⟨h₁ s hs, h₂ s hs⟩,
  inf_le_left   := assume a b s ⟨h₁, h₂⟩, h₁,
  inf_le_right  := assume a b s ⟨h₁, h₂⟩, h₂,
  top           := ⊤,
  le_top        := assume a t ht, trivial,
  bot           := ⊥,
  bot_le        := assume a s hs, hs.elim
    (assume h, h.symm ▸ a.is_measurable_empty)
    (assume h, begin rw [h, ←compl_empty], exact a.is_measurable_compl _ a.is_measurable_empty end),
  Sup           := λtt, Inf {t | ∀t'∈tt, t' ≤ t},
  le_Sup        := assume s f h, measurable_space.le_Inf $ assume t ht, ht _ h,
  Sup_le        := assume s f h, measurable_space.Inf_le $ assume t ht, h _ ht,
  Inf           := Inf,
  le_Inf        := assume s a, measurable_space.le_Inf,
  Inf_le        := assume s a, measurable_space.Inf_le }

instance : inhabited (measurable_space α) := ⟨⊤⟩

end complete_lattice

section functors
variables {m m₁ m₂ : measurable_space α} {m' : measurable_space β} {f : α → β} {g : β → α}

protected def map (f : α → β) (m : measurable_space α) : measurable_space β :=
{measurable_space .
  is_measurable       := λs, m.is_measurable $ f ⁻¹' s,
  is_measurable_empty := m.is_measurable_empty,
  is_measurable_compl := assume s hs, m.is_measurable_compl _ hs,
  is_measurable_Union := assume f hf, by rw [preimage_Union]; exact m.is_measurable_Union _ hf }

@[simp] lemma map_id : m.map id = m :=
measurable_space_eq $ assume s, iff.refl _

@[simp] lemma map_comp {f : α → β} {g : β → γ} : (m.map f).map g = m.map (g ∘ f) :=
measurable_space_eq $ assume s, iff.refl _

protected def comap (f : α → β) (m : measurable_space β) : measurable_space α :=
{measurable_space .
  is_measurable       := λs, ∃s', m.is_measurable s' ∧ s = f ⁻¹' s',
  is_measurable_empty := ⟨∅, m.is_measurable_empty, rfl⟩,
  is_measurable_compl := assume s ⟨s', h₁, h₂⟩, ⟨-s', m.is_measurable_compl _ h₁, h₂.symm ▸ rfl⟩,
  is_measurable_Union := assume s hs,
    let ⟨s', hs'⟩ := axiom_of_choice hs in
    have ∀i, s i = f ⁻¹' s' i, from assume i, (hs' i).right,
    ⟨⋃i, s' i, m.is_measurable_Union _ (λi, (hs' i).left), by simp [this] ⟩ }

@[simp] lemma comap_id : m.comap id = m :=
measurable_space_eq $ assume s, ⟨assume ⟨s', hs', h⟩, h.symm ▸ hs', assume h, ⟨s, h, rfl⟩⟩

@[simp] lemma comap_comp {f : β → α} {g : γ → β} : (m.comap f).comap g = m.comap (f ∘ g) :=
measurable_space_eq $ assume s,
  ⟨assume ⟨t, ⟨u, h, hu⟩, ht⟩, ⟨u, h, ht.symm ▸ hu.symm ▸ rfl⟩,
    assume ⟨t, h, ht⟩, ⟨f ⁻¹' t, ⟨_, h, rfl⟩, ht⟩⟩

lemma comap_le_iff_le_map {f : α → β} : m'.comap f ≤ m ↔ m' ≤ m.map f :=
⟨assume h s hs, h _ ⟨_, hs, rfl⟩, assume h s ⟨t, ht, heq⟩, heq.symm ▸ h _ ht⟩

lemma gc_comap_map (f : α → β) :
  galois_connection (measurable_space.comap f) (measurable_space.map f) :=
assume f g, comap_le_iff_le_map

lemma map_mono (h : m₁ ≤ m₂) : m₁.map f ≤ m₂.map f := (gc_comap_map f).monotone_u h
lemma monotone_map : monotone (measurable_space.map f) := assume a b h, map_mono h
lemma comap_mono (h : m₁ ≤ m₂) : m₁.comap g ≤ m₂.comap g := (gc_comap_map g).monotone_l h
lemma monotone_comap : monotone (measurable_space.comap g) := assume a b h, comap_mono h

@[simp] lemma comap_bot : (⊥:measurable_space α).comap g = ⊥ := (gc_comap_map g).l_bot
@[simp] lemma comap_sup : (m₁ ⊔ m₂).comap g = m₁.comap g ⊔ m₂.comap g := (gc_comap_map g).l_sup
@[simp] lemma comap_supr {m : ι → measurable_space α} :(⨆i, m i).comap g = (⨆i, (m i).comap g) :=
(gc_comap_map g).l_supr

@[simp] lemma map_top : (⊤:measurable_space α).map f = ⊤ := (gc_comap_map f).u_top
@[simp] lemma map_inf : (m₁ ⊓ m₂).map f = m₁.map f ⊓ m₂.map f := (gc_comap_map f).u_inf
@[simp] lemma map_infi {m : ι → measurable_space α} : (⨅i, m i).map f = (⨅i, (m i).map f) :=
(gc_comap_map f).u_infi

lemma comap_map_le : (m.map f).comap f ≤ m := (gc_comap_map f).decreasing_l_u _
lemma le_map_comap : m ≤ (m.comap g).map g := (gc_comap_map g).increasing_u_l _

end functors

end measurable_space

section measurable_functions
open measurable_space

def measurable [m₁ : measurable_space α] [m₂ : measurable_space β] (f : α → β) : Prop :=
m₂ ≤ m₁.map f

lemma measurable_id [measurable_space α] : measurable (@id α) := le_refl _

lemma measurable_comp [measurable_space α] [measurable_space β] [measurable_space γ]
  {f : α → β} {g : β → γ} (hf : measurable f) (hg : measurable g) : measurable (g ∘ f) :=
le_trans hg $ map_mono hf

end measurable_functions

section constructions

instance : measurable_space empty := ⊤
instance : measurable_space unit := ⊤
instance : measurable_space bool := ⊤
instance : measurable_space ℕ := ⊤
instance : measurable_space ℤ := ⊤

instance {p : α → Prop} [m : measurable_space α] : measurable_space (subtype p) :=
m.comap subtype.val

instance [m₁ : measurable_space α] [m₂ : measurable_space β] : measurable_space (α × β) :=
m₁.comap prod.fst ⊔ m₂.comap prod.snd

instance [m₁ : measurable_space α] [m₂ : measurable_space β] : measurable_space (α ⊕ β) :=
m₁.map sum.inl ⊓ m₂.map sum.inr

instance {β : α → Type v} [m : Πa, measurable_space (β a)] : measurable_space (sigma β) :=
⨅a, (m a).map (sigma.mk a)

end constructions
