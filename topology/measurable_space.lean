/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Measurable spaces -- σ-algberas
-/
import data.set data.finset order.galois_connection data.set.countable
open classical set lattice
local attribute [instance] decidable_inhabited prop_decidable

universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x}
  {s t u : set α}

namespace set
def disjointed (f : ℕ → set α) (n : ℕ) : set α := f n ∩ (⋂i<n, - f i)

lemma disjoint_disjointed {i j : ℕ} {f : ℕ → set α} (h : i ≠ j) :
  disjointed f i ∩ disjointed f j = ∅ :=
have ∀i j, i < j → disjointed f i ∩ disjointed f j = ∅,
  from assume i j hij, eq_empty_of_forall_not_mem $ assume x h,
  have x ∈ f i, from h.left.left,
  have x ∈ (⋂i<j, - f i), from h.right.right,
  have x ∉ f i, begin simp at this; exact this _ hij end,
  absurd ‹x ∈ f i› this,
show disjointed f i ∩ disjointed f j = ∅,
  from (ne_iff_lt_or_gt.mp h).elim (this i j) begin rw [inter_comm], exact this j i end

lemma disjointed_Union {f : ℕ → set α} : (⋃n, disjointed f n) = (⋃n, f n) :=
subset.antisymm (Union_subset_Union $ assume i, inter_subset_left _ _) $
  assume x h,
  have ∃n, x ∈ f n, from (mem_Union_eq _ _).mp h,
  have hn : ∀ (i : ℕ), i < nat.find this → x ∉ f i,
    from assume i, nat.find_min this,
  (mem_Union_eq _ _).mpr ⟨nat.find this, nat.find_spec this, by simp; assumption⟩
end set

namespace nat
open nat

lemma lt_succ_iff {n i : ℕ } : n < i.succ ↔ (n < i ∨ n = i) :=
calc n < i.succ ↔ n ≤ i : succ_le_succ_iff _ _
  ... ↔ (n + 1 ≤ i ∨ n = i) : iff.intro
    (assume h : n ≤ i, match le.dest h with
    | ⟨zero, h⟩ := by simp at h; simp [*]
    | ⟨succ k, h⟩ := or.inl $ h ▸ add_le_add_left (le_add_left _ _) _
    end)
    (or.rec (assume h, le_trans (le_add_right _ _) h) le_of_eq)

end nat

open set

structure measurable_space (α : Type u) :=
(is_measurable : set α → Prop)
(is_measurable_empty : is_measurable ∅)
(is_measurable_compl : ∀s, is_measurable s → is_measurable (- s))
(is_measurable_Union : ∀f:ℕ → set α, (∀i, is_measurable (f i)) → is_measurable (⋃i, f i))

attribute [class] measurable_space

section
variable [m : measurable_space α]
include m

def is_measurable : set α → Prop := m.is_measurable

lemma is_measurable_empty : is_measurable (∅ : set α) := m.is_measurable_empty

lemma is_measurable_compl : is_measurable s → is_measurable (-s) :=
m.is_measurable_compl s

lemma is_measurable_univ : is_measurable (univ : set α) :=
have is_measurable (- ∅ : set α), from is_measurable_compl is_measurable_empty,
by simp * at *

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

section generated_from

inductive generate_measurable (s : set (set α)) : set α → Prop
| basic : ∀u∈s, generate_measurable u
| empty : generate_measurable ∅
| compl : ∀s, generate_measurable s → generate_measurable (-s)
| union : ∀f:ℕ → set α, (∀n, generate_measurable (f n)) → generate_measurable (⋃i, f i)

def generate_from (s : set (set α)) : measurable_space α :=
{measurable_space .
  is_measurable       := generate_measurable s,
  is_measurable_empty := generate_measurable.empty s,
  is_measurable_compl := generate_measurable.compl,
  is_measurable_Union := generate_measurable.union }

lemma is_measurable_generate_from {s : set (set α)} {t : set α} (ht : t ∈ s) :
  (generate_from s).is_measurable t :=
generate_measurable.basic t ht

lemma generate_from_le {s : set (set α)} {m : measurable_space α} (h : ∀t∈s, m.is_measurable t) :
  generate_from s ≤ m :=
assume t (ht : generate_measurable s t), ht.rec_on h
  (is_measurable_empty m)
  (assume s _ hs, is_measurable_compl m s hs)
  (assume f _ hf, is_measurable_Union m f hf)

end generated_from

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

lemma measurable_generate_from [measurable_space α] {s : set (set β)} {f : α → β}
  (h : ∀t∈s, is_measurable (f ⁻¹' t)) : @measurable _ _ _ (generate_from s) f :=
generate_from_le h

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

namespace measurable_space

/-- Dynkin systems
The main purpose of Dynkin systems is to provide a powerful induction rule for σ-algebras generated
by intersection stable set systems.
-/
structure dynkin_system (α : Type*) :=
(has : set α → Prop)
(has_empty : has ∅)
(has_compl : ∀{a}, has a → has (-a))
(has_Union : ∀{f:ℕ → set α}, (∀i j, i ≠ j → f i ∩ f j = ∅) → (∀i, has (f i)) → has (⋃i, f i))

namespace dynkin_system

lemma dynkin_system_eq :
  ∀{d₁ d₂ : dynkin_system α}, (∀s:set α, d₁.has s ↔ d₂.has s) → d₁ = d₂
| ⟨s₁, _, _, _⟩ ⟨s₂, _, _, _⟩ h :=
  have s₁ = s₂, from funext $ assume x, propext $ h x,
  by subst this

instance : partial_order (dynkin_system α) :=
{ partial_order .
  le          := λm₁ m₂, m₁.has ≤ m₂.has,
  le_refl     := assume a b, le_refl _,
  le_trans    := assume a b c, le_trans,
  le_antisymm := assume a b h₁ h₂, dynkin_system_eq $ assume s, ⟨h₁ s, h₂ s⟩ }

def of_measurable_space (m : measurable_space α) : dynkin_system α :=
{ dynkin_system .
  has       := m.is_measurable,
  has_empty := m.is_measurable_empty,
  has_compl := m.is_measurable_compl,
  has_Union := assume f _ hf, m.is_measurable_Union f hf }

lemma of_measurable_space_le_of_measurable_space_iff {m₁ m₂ : measurable_space α} :
  of_measurable_space m₁ ≤ of_measurable_space m₂ ↔ m₁ ≤ m₂ :=
iff.refl _

inductive generate_has (s : set (set α)) : set α → Prop
| basic : ∀t∈s, generate_has t
| empty : generate_has ∅
| compl : ∀{a}, generate_has a → generate_has (-a)
| Union : ∀{f:ℕ → set α}, (∀i j, i ≠ j → f i ∩ f j = ∅) →
    (∀i, generate_has (f i)) → generate_has (⋃i, f i)

def generate (s : set (set α)) : dynkin_system α :=
{ dynkin_system .
  has := generate_has s,
  has_empty := generate_has.empty s,
  has_compl := assume a, generate_has.compl,
  has_Union := assume f, generate_has.Union }

section internal
parameters {δ : Type*} (d : dynkin_system δ)

lemma has_univ : d.has univ :=
have d.has (- ∅), from d.has_compl d.has_empty,
by simp * at *

lemma has_union {s₁ s₂ : set δ} (h₁ : d.has s₁) (h₂ : d.has s₂) (h : s₁ ∩ s₂ = ∅) : d.has (s₁ ∪ s₂) :=
let f := [s₁, s₂].inth in
have hf0 : f 0 = s₁, from rfl,
have hf1 : f 1 = s₂, from rfl,
have hf2 : ∀n:ℕ, f n.succ.succ = ∅, from assume n, rfl,
have (∀i j, i ≠ j → f i ∩ f j = ∅),
  from assume i, i.two_step_induction
    (assume j, j.two_step_induction (by simp) (by simp [hf0, hf1, h]) (by simp [hf2]))
    (assume j, j.two_step_induction (by simp [hf0, hf1, h]) (by simp) (by simp [hf2]))
    (by simp [hf2]),
have eq : s₁ ∪ s₂ = (⋃i, f i),
  from subset.antisymm (union_subset (le_supr f 0) (le_supr f 1)) $
  Union_subset $ assume i,
  match i with
  | 0 := subset_union_left _ _
  | 1 := subset_union_right _ _
  | nat.succ (nat.succ n) := by simp [hf2]
  end,
by rw [eq]; exact d.has_Union this (assume i,
  match i with
  | 0 := h₁
  | 1 := h₂
  | nat.succ (nat.succ n) := by simp [d.has_empty, hf2]
  end)

lemma has_sdiff {s₁ s₂ : set δ} (h₁ : d.has s₁) (h₂ : d.has s₂) (h : s₂ ⊆ s₁) : d.has (s₁ - s₂) :=
have d.has (- (s₂ ∪ -s₁)),
  from d.has_compl $ d.has_union h₂ (d.has_compl h₁) $ eq_empty_of_forall_not_mem $
    assume x ⟨h₁, h₂⟩, h₂ $ h h₁,
have s₁ - s₂ = - (s₂ ∪ -s₁),
  by rw [compl_union, compl_compl, inter_comm]; refl,
by rwa [this]

def to_measurable_space (h_inter : ∀s₁ s₂, d.has s₁ → d.has s₂ → d.has (s₁ ∩ s₂)) :=
{ measurable_space .
  is_measurable := d.has,
  is_measurable_empty := d.has_empty,
  is_measurable_compl := assume s h, d.has_compl h,
  is_measurable_Union := assume f hf,
    have h_diff : ∀{s₁ s₂}, d.has s₁ → d.has s₂ → d.has (s₁ - s₂),
      from assume s₁ s₂ h₁ h₂, h_inter _ _ h₁ (d.has_compl h₂),
    have ∀n, d.has (disjointed f n),
      from assume n, h_inter _ _ (hf n)
      begin
        induction n,
        case nat.zero {
          have h : (⋂ (i : ℕ) (H : i < 0), -f i) = univ,
            { apply eq_univ_of_forall,
              simp [mem_Inter, nat.not_lt_zero] },
          simp [h, d.has_univ] },
        case nat.succ n ih {
          have h : (⨅ (i : ℕ) (H : i < n.succ), -f i) = (⨅ (i : ℕ) (H : i < n), -f i) ⊓ - f n,
            by simp [nat.lt_succ_iff, infi_or, infi_inf_eq, inf_comm],
          change (⋂ (i : ℕ) (H : i < n.succ), -f i) = (⋂ (i : ℕ) (H : i < n), -f i) ∩ - f n at h,
          rw [h],
          exact h_inter _ _ ih (d.has_compl $ hf _) },
      end,
    have d.has (⋃n, disjointed f n), from d.has_Union (assume i j, disjoint_disjointed) this,
    by rwa [disjointed_Union] at this }

lemma of_measurable_space_to_measurable_space
  (h_inter : ∀s₁ s₂, d.has s₁ → d.has s₂ → d.has (s₁ ∩ s₂)) :
  of_measurable_space (d.to_measurable_space h_inter) = d :=
dynkin_system_eq $ assume s, iff.refl _

def restrict_on {s : set δ} (h : d.has s) : dynkin_system δ :=
{ dynkin_system .
  has       := λt, d.has (t ∩ s),
  has_empty := by simp [d.has_empty],
  has_compl := assume t hts,
    have -t ∩ s = (- (t ∩ s)) \ -s,
      from set.ext $ assume x, by by_cases x ∈ s; simp [h],
    by rw [this]; from d.has_sdiff (d.has_compl hts) (d.has_compl h)
      (compl_subset_compl_iff_subset.mpr $ inter_subset_right _ _),
  has_Union := assume f hd hf,
    begin
      rw [inter_comm, inter_distrib_Union_left],
      apply d.has_Union,
      exact assume i j h,
        calc s ∩ f i ∩ (s ∩ f j) = s ∩ s ∩ (f i ∩ f j) : by cc
          ... = ∅ : by rw [hd i j h]; simp,
      intro i, rw [inter_comm], exact hf i
    end }

lemma generate_le {s : set (set δ)} (h : ∀t∈s, d.has t) : generate s ≤ d :=
assume t ht,
ht.rec_on h d.has_empty (assume a _ h, d.has_compl h) (assume f hd _ hf, d.has_Union hd hf)

end internal

lemma generate_inter {s : set (set α)}
  (hs : ∀t₁ t₂, t₁ ∈ s → t₂ ∈ s → t₁ ∩ t₂ ∈ s) {t₁ t₂ : set α}
  (ht₁ : (generate s).has t₁) (ht₂ : (generate s).has t₂) : (generate s).has (t₁ ∩ t₂) :=
have generate s ≤ (generate s).restrict_on ht₂,
  from generate_le _ $ assume s₁ hs₁,
  have (generate s).has s₁, from generate_has.basic s₁ hs₁,
  have generate s ≤ (generate s).restrict_on this,
    from generate_le _ $ assume s₂ hs₂, show (generate s).has (s₂ ∩ s₁),
      from generate_has.basic _ (hs _ _ hs₂ hs₁),
  have (generate s).has (t₂ ∩ s₁), from this _ ht₂,
  show (generate s).has (s₁ ∩ t₂), by rwa [inter_comm],
this _ ht₁

lemma generate_from_eq {s : set (set α)}
  (hs : ∀t₁ t₂, t₁ ∈ s → t₂ ∈ s → t₁ ∩ t₂ ∈ s) :
generate_from s = (generate s).to_measurable_space (assume t₁ t₂, generate_inter hs) :=
le_antisymm
  (generate_from_le $ assume t ht, generate_has.basic t ht)
  (of_measurable_space_le_of_measurable_space_iff.mp $
    by rw [of_measurable_space_to_measurable_space];
    from (generate_le _ $ assume t ht, is_measurable_generate_from ht))

end dynkin_system

lemma induction_on_inter {C : set α → Prop} {s : set (set α)} {m : measurable_space α}
  (h_eq : m = generate_from s)
  (h_inter : ∀t₁ t₂, t₁ ∈ s → t₂ ∈ s → t₁ ∩ t₂ ∈ s)
  (h_empty : C ∅) (h_basic : ∀t∈s, C t) (h_compl : ∀t, m.is_measurable t → C t → C (- t))
  (h_union : ∀f:ℕ → set α, (∀i j, i ≠ j → f i ∩ f j = ∅) →
    (∀i, m.is_measurable (f i)) → (∀i, C (f i)) → C (⋃i, f i)) :
  ∀{t}, m.is_measurable t → C t :=
have eq : m.is_measurable = dynkin_system.generate_has s,
  by rw [h_eq, dynkin_system.generate_from_eq h_inter]; refl,
assume t ht,
have dynkin_system.generate_has s t, by rwa [eq] at ht,
this.rec_on h_basic h_empty
  (assume t ht, h_compl t $ by rw [eq]; exact ht)
  (assume f hf ht, h_union f hf $ assume i, by rw [eq]; exact ht _)

end measurable_space
