/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Theory of filters on preorders.
-/
import order.galois_connection order.zorn
import data.set.finite data.list
import category.applicative
open lattice set

universes u v w x y

local attribute [instance] classical.prop_decidable

namespace lattice
variables {α : Type u} {ι : Sort v}

section
variable [complete_lattice α]

lemma Inf_eq_finite_sets {s : set α} :
  Inf s = (⨅ t ∈ { t | finite t ∧ t ⊆ s}, Inf t) :=
le_antisymm
  (le_infi $ assume t, le_infi $ assume ⟨_, h⟩, Inf_le_Inf h)
  (le_Inf $ assume b h, infi_le_of_le {b} $ infi_le_of_le
    (by simp only [h, finite_singleton, and_self, mem_set_of_eq,
      singleton_subset_iff]) $ Inf_le $ by simp only [mem_singleton])

lemma infi_insert_finset {ι : Type v} {s : finset ι} {f : ι → α} {i : ι} :
  (⨅j∈insert i s, f j) = f i ⊓ (⨅j∈s, f j) :=
by simp [infi_or, infi_inf_eq]

lemma infi_empty_finset {ι : Type v} {f : ι → α} : (⨅j∈(∅ : finset ι), f j) = ⊤ :=
by simp only [finset.not_mem_empty, infi_top, infi_false, eq_self_iff_true]

end

end lattice

namespace set

variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} {ι : Sort y}

theorem monotone_inter [preorder β] {f g : β → set α}
  (hf : monotone f) (hg : monotone g) : monotone (λx, (f x) ∩ (g x)) :=
assume a b h x ⟨h₁, h₂⟩, ⟨hf h h₁, hg h h₂⟩

theorem monotone_set_of [preorder α] {p : α → β → Prop}
  (hp : ∀b, monotone (λa, p a b)) : monotone (λa, {b | p a b}) :=
assume a a' h b, hp b h

end set

open set lattice

section order
variables {α : Type u} (r : α → α → Prop)
local infix `≼` : 50 := r

lemma directed_on_Union {r} {ι : Sort v} {f : ι → set α} (hd : directed (⊆) f)
  (h : ∀x, directed_on r (f x)) : directed_on r (⋃x, f x) :=
by simp only [directed_on, exists_prop, mem_Union, exists_imp_distrib]; exact
⟨let ⟨i⟩ := hd.1, ⟨x, hx⟩ := (h i).1 in ⟨x, i, hx⟩,
  λ a₁ b₁ fb₁ a₂ b₂ fb₂,
  let ⟨z, zb₁, zb₂⟩ := hd.2 b₁ b₂,
      ⟨x, xf, xa₁, xa₂⟩ := (h z).2 a₁ (zb₁ fb₁) a₂ (zb₂ fb₂) in
  ⟨x, ⟨z, xf⟩, xa₁, xa₂⟩⟩

end order

theorem directed_of_chain {α β r} [is_refl β r] {f : α → β} {c : set α}
  (h : zorn.chain (f ⁻¹'o r) c) (hc : c ≠ ∅) :
  directed r (λx:{a:α // a ∈ c}, f (x.val)) :=
⟨let ⟨x, hx⟩ := exists_mem_of_ne_empty hc in ⟨⟨x, hx⟩⟩,
 assume ⟨a, ha⟩ ⟨b, hb⟩, classical.by_cases
  (assume : a = b, by simp only [this, exists_prop, and_self, subtype.exists];
    exact ⟨b, hb, refl _⟩)
  (assume : a ≠ b, (h a ha b hb this).elim
    (λ h : r (f a) (f b), ⟨⟨b, hb⟩, h, refl _⟩)
    (λ h : r (f b) (f a), ⟨⟨a, ha⟩, refl _, h⟩))⟩

structure pfilter (α : Type*) [preorder α] :=
(sets             : set α)
(top_sets         : ∃ x, x ∈ sets)
(sets_of_le {x y} : x ≤ y → x ∈ sets → y ∈ sets)
(inf_sets {x y}   : x ∈ sets → y ∈ sets → ∃ z ∈ sets, z ≤ x ∧ z ≤ y)

namespace pfilter
variables {α : Type u} [preorder α] {f g : pfilter α} {s t : α}

lemma sets_inj : ∀ {f g : pfilter α}, f.sets = g.sets → f = g
| ⟨a, _, _, _⟩ ⟨._, _, _, _⟩ rfl := rfl

lemma sets_inj_iff : f.sets = g.sets ↔ f = g :=
⟨sets_inj, congr_arg _⟩

instance : has_mem α (pfilter α) := ⟨λ s f, s ∈ f.sets⟩

@[simp] lemma mem_sets_iff : s ∈ f.sets ↔ s ∈ f := iff.rfl

protected lemma ext_iff : f = g ↔ ∀ s, s ∈ f ↔ s ∈ g :=
by rw [← sets_inj_iff, ext_iff]; refl

@[extensionality]
protected lemma ext : (∀ s, s ∈ f ↔ s ∈ g) → f = g :=
pfilter.ext_iff.2

lemma exists_mem (f : pfilter α) : ∃ x, x ∈ f := f.top_sets

lemma mem_of_le : ∀ {x y : α}, x ≤ y → x ∈ f → y ∈ f :=
f.sets_of_le

lemma top_mem {α} [order_top α] (f : pfilter α) : ⊤ ∈ f :=
let ⟨x, h⟩ := f.exists_mem in mem_of_le le_top h

lemma mem_directed : ∀ {s t}, s ∈ f → t ∈ f → ∃ u ∈ f, u ≤ s ∧ u ≤ t :=
f.inf_sets

lemma inf_mem {α} [semilattice_inf α] {f : pfilter α} {s t}
  (hs : s ∈ f) (ht : t ∈ f) : s ⊓ t ∈ f :=
let ⟨u, hu, us, ut⟩ := mem_directed hs ht in
f.sets_of_le (le_inf us ut) hu

lemma infi_mem {α : Type u} [complete_lattice α]
  {f : pfilter α} {ι} {s : ι → α} {is : set ι} (hf : finite is) :
  (∀i∈is, s i ∈ f) → (⨅ i ∈ is, s i) ∈ f :=
finite.induction_on hf
  (assume hs, by simp only [top_mem, mem_empty_eq, infi_neg, infi_top, not_false_iff])
  (assume i is _ hf hi hs,
    have h₁ : s i ∈ f, from hs i (by simp),
    have h₂ : (⨅x∈is, s x) ∈ f, from hi $ assume a ha, hs _ $ by simp only [ha, mem_insert_iff, or_true],
    by simp [infi_or, infi_inf_eq, inf_mem h₁ h₂])

lemma exists_mem_le_iff : (∃t∈f, t ≤ s) ↔ s ∈ f :=
⟨assume ⟨t, ht, ts⟩, mem_of_le ts ht, assume hs, ⟨s, hs, le_refl _⟩⟩

lemma forall_mem_le_iff : (∀ t, s ≤ t → t ∈ f) ↔ s ∈ f :=
⟨λ H, H _ (le_refl _), λ hs t ht, mem_of_le ht hs⟩

lemma monotone_mem {f : pfilter α} : monotone (∈ f) :=
assume s t hst, mem_of_le hst

end pfilter

namespace pfilter
variables {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x}

section le
variable [preorder α]

instance : partial_order (pfilter α) :=
{ le            := λf g, ∀ ⦃x⦄, x ∈ g → x ∈ f,
  le_antisymm   := assume a b h₁ h₂, sets_inj $ subset.antisymm h₂ h₁,
  le_refl       := assume a _, id,
  le_trans      := assume a b c h₁ h₂, subset.trans h₂ h₁ }

theorem le_def {f g : pfilter α} : f ≤ g ↔ ∀ ⦃x⦄, x ∈ g → x ∈ f := iff.rfl

end le

section principal
variable [preorder α]
/-- The principal pfilter of `s` is the collection of all supersets of `s`. -/
def principal (s : α) : pfilter α :=
{ sets       := {t | s ≤ t},
  top_sets   := ⟨s, le_refl _⟩,
  sets_of_le := assume x y h₁ h₂, le_trans h₂ h₁,
  inf_sets   := assume x y hx hy, ⟨s, le_refl _, hx, hy⟩ }

@[simp] lemma mem_principal {s t : α} : s ∈ principal t ↔ t ≤ s := iff.rfl

lemma mem_principal_self (s : α) : s ∈ principal s := le_refl _

@[simp] lemma le_principal_iff {s : α} {f : pfilter α} : f ≤ principal s ↔ s ∈ f :=
forall_mem_le_iff

lemma principal_mono {s t : α} : principal s ≤ principal t ↔ s ≤ t :=
le_principal_iff

lemma monotone_principal : monotone (principal : α → pfilter α) :=
λ _ _, principal_mono.2

@[simp] lemma principal_inj {s t : set α} : principal s = principal t ↔ s = t :=
by simp only [le_antisymm_iff, principal_mono]

end principal

section generate
variable [semilattice_inf_top α]

/-- `generate_sets g s`: `s` is in the pfilter closure of `g`. -/
inductive generate_sets (g : set α) : α → Prop
| basic {s : α} : s ∈ g → generate_sets s
| top {}        : generate_sets ⊤
| le {s t : α}  : s ≤ t → generate_sets s → generate_sets t
| inf {s t : α} : generate_sets s → generate_sets t → generate_sets (s ⊓ t)

/-- `generate g` is the smallest pfilter containing the sets `g`. -/
def generate (g : set α) : pfilter α :=
{ sets       := {s | generate_sets g s},
  top_sets   := ⟨_, generate_sets.top⟩,
  sets_of_le := assume x y, generate_sets.le,
  inf_sets   := assume s t hs ht, ⟨s ⊓ t,
    generate_sets.inf hs ht, inf_le_left, inf_le_right⟩ }

lemma sets_iff_generate {s : set α} {f : pfilter α} : f ≤ pfilter.generate s ↔ s ⊆ f.sets :=
iff.intro
  (assume h u hu, h $ generate_sets.basic $ hu)
  (assume h u hu, hu.rec_on h f.top_mem
    (assume x y hxy _, mem_of_le hxy)
    (assume x y _ _, inf_mem))

protected def mk_of_closure (s : set α) (hs : (generate s).sets = s) : pfilter α :=
{ sets       := s,
  top_sets   := hs ▸ exists_mem (generate s),
  sets_of_le := assume x y, hs ▸ @mem_of_le _ _ (generate s) _ _,
  inf_sets   := assume x y, hs ▸ @mem_directed _ _ (generate s) _ _ }

lemma mk_of_closure_sets {s : set α} {hs} :
  pfilter.mk_of_closure s hs = generate s :=
pfilter.ext $ assume u, iff_of_eq (congr_arg (λ f : set α, u ∈ f) hs).symm

/- Galois insertion from sets of sets into a pfilters. -/
def gi_generate (α : Type*) [semilattice_inf_top α] :
  @galois_insertion (set α) (order_dual (pfilter α)) _ _ pfilter.generate pfilter.sets :=
{ gc        := assume s f, sets_iff_generate,
  le_l_u    := assume f, @generate_sets.basic _ _ _,
  choice    := λs hs, pfilter.mk_of_closure s (le_antisymm hs $ sets_iff_generate.1 $ le_refl _),
  choice_eq := assume s hs, mk_of_closure_sets }

end generate

section inf
variable [semilattice_inf α]

/-- The infimum of pfilters is the pfilter generated by infima
  of elements of the two pfilters. -/
instance : has_inf (pfilter α) := ⟨λf g : pfilter α,
{ sets       := {s | ∃ (a ∈ f) (b ∈ g), a ⊓ b ≤ s },
  top_sets   :=
    let ⟨a, ha⟩ := f.exists_mem, ⟨b, hb⟩ := g.exists_mem in
    ⟨a ⊓ b, a, ha, b, hb, le_refl _⟩,
  sets_of_le := assume x y xy ⟨a, ha, b, hb, h⟩, ⟨a, ha, b, hb, le_trans h xy⟩,
  inf_sets   := assume x y ⟨a, ha, b, hb, hx⟩ ⟨c, hc, d, hd, hy⟩,
    ⟨_, ⟨_, inf_mem ha hc, _, inf_mem hb hd, le_refl _⟩,
      le_trans (inf_le_inf inf_le_left inf_le_left) hx,
      le_trans (inf_le_inf inf_le_right inf_le_right) hy⟩ }⟩

@[simp] lemma mem_inf {f g : pfilter α} {s : α} :
  s ∈ f ⊓ g ↔ ∃t₁∈f, ∃t₂∈g, t₁ ⊓ t₂ ≤ s := iff.rfl

lemma mem_inf_of_left {f g : pfilter α} {s : α} (h : s ∈ f) : s ∈ f ⊓ g :=
let ⟨t, ht⟩ := g.exists_mem in ⟨s, h, t, ht, inf_le_left⟩

lemma mem_inf_of_right {f g : pfilter α} {s : α} (h : s ∈ g) : s ∈ f ⊓ g :=
let ⟨t, ht⟩ := f.exists_mem in ⟨t, ht, s, h, inf_le_right⟩

lemma inf_mem_inf {f g : pfilter α} {s t : α}
  (hs : s ∈ f) (ht : t ∈ g) : s ⊓ t ∈ f ⊓ g :=
inf_mem (mem_inf_of_left hs) (mem_inf_of_right ht)

instance : semilattice_inf (pfilter α) :=
{ inf := (⊓),
  inf_le_left := λ f g s, mem_inf_of_left,
  inf_le_right := λ f g s, mem_inf_of_right,
  le_inf := λ f g k fg fk s ⟨a, ha, b, hb, h⟩,
    mem_of_le h (inf_mem (fg ha) (fk hb)),
  ..pfilter.partial_order }

@[simp] lemma inf_principal {s t : α} : principal s ⊓ principal t = principal (s ⊓ t) :=
le_antisymm
  (λ x h, ⟨s, mem_principal_self _, t, mem_principal_self _, h⟩)
  (le_inf (principal_mono.2 inf_le_left) (principal_mono.2 inf_le_right))

end inf

section top
variable [order_top α]

instance : order_top (pfilter α) :=
{ top := principal ⊤,
  le_top := λ f s h, mem_of_le h f.top_mem,
  ..pfilter.partial_order }

lemma mem_top_iff_top_le {s : α} : s ∈ (⊤ : pfilter α) ↔ ⊤ ≤ s := iff.rfl

@[simp] lemma mem_top {s : α} : s ∈ (⊤ : pfilter α) ↔ s = ⊤ := eq_top_iff.symm

end top

section bot

section
variables [preorder α] (dir : directed (≥) (@id α))

protected def bot : pfilter α :=
{ sets := set.univ,
  top_sets := let ⟨x⟩ := dir.1 in ⟨x, trivial⟩,
  sets_of_le := λ x y _ _, trivial,
  inf_sets := λ x y _ _,
    let ⟨z, h⟩ := dir.2 x y in ⟨z, trivial, h⟩,
  ..pfilter.partial_order }

protected theorem bot_le (f : pfilter α) : pfilter.bot dir ≤ f := λ x _, trivial
end

variable [semilattice_inf_top α]

instance : order_bot (pfilter α) :=
have dir : directed (≥) (@id α) :=
  ⟨⟨⊤⟩, λ x y, ⟨x ⊓ y, inf_le_left, inf_le_right⟩⟩,
{ bot := pfilter.bot dir,
  bot_le := pfilter.bot_le dir,
  ..pfilter.partial_order }

@[simp] lemma mem_bot (s : α) : s ∈ (⊥ : pfilter α) := trivial

end bot

section join
variable [preorder α]

/-- The join of a pfilter of pfilters is defined by the relation `s ∈ join f ↔ {t | s ≤ t} ∈ f`. -/
def join (f : pfilter (pfilter α)) : pfilter α :=
{ sets             := {s | principal s ∈ f},
  top_sets         :=
    let ⟨g, hg⟩ := f.exists_mem, ⟨x, xg⟩ := g.exists_mem in
    ⟨x, mem_of_le (λ y hy, mem_of_le hy xg) hg⟩,
  sets_of_le := λ x y xy, mem_of_le (principal_mono.2 xy),
  inf_sets       := assume x y hx hy,
    let ⟨l, hl, lx, ly⟩ := mem_directed hx hy,
        ⟨z, hz, zx, zy⟩ := mem_directed (le_principal_iff.1 lx) (le_principal_iff.1 ly) in
    ⟨z, mem_of_le (le_principal_iff.2 hz) hl, zx, zy⟩ }

@[simp] lemma mem_join {s : α} {f : pfilter (pfilter α)} :
  s ∈ join f ↔ principal s ∈ f := iff.rfl

end join

section comap
variables [preorder α] [preorder β] (m : α → β)

class directed_map : Prop :=
(mono : monotone m)
(dir : ∀ x, directed_on (≥) {a | x ≤ m a})
open directed_map

variables [preorder γ] [directed_map m] (m' : β → γ) [directed_map m']
  {f : pfilter β} {g : pfilter γ} {s : α} {t : β}

/-- The inverse map of a preorder filter -/
def comap (f : pfilter β) : pfilter α :=
{ sets       := {a | m a ∈ f},
  top_sets   := let ⟨x, h⟩ := f.exists_mem,
    ⟨y, hy⟩ := (dir m x).1 in ⟨y, mem_of_le hy h⟩,
  sets_of_le := assume s t hs, mem_of_le (mono m hs),
  inf_sets   := assume s t hs ht,
    let ⟨u, hu, us, ut⟩ := mem_directed hs ht,
        ⟨c, hc, cs, ct⟩ := (dir m _).2 _ us _ ut in
    ⟨c, mem_of_le hc hu, cs, ct⟩ }

@[simp] lemma mem_comap : s ∈ comap m f ↔ m s ∈ f := iff.rfl

instance directed_map.id : directed_map (@id α) :=
⟨monotone_id, λ x, ⟨⟨x, le_refl _⟩, λ y xy z xz, ⟨x, le_refl _, xy, xz⟩⟩⟩

@[simp] lemma comap_id : comap id f = f :=
pfilter.ext $ λ _, iff.rfl

instance directed_map.comp : directed_map (m' ∘ m) :=
⟨monotone_comp (mono m) (mono m'), λ a, ⟨
  let ⟨b, hb⟩ := (dir m' a).1, ⟨c, hc⟩ := (dir m b).1 in
    ⟨c, le_trans hb (mono m' hc)⟩,
  λ c hc c' hc',
    let ⟨b, hb, bc, bc'⟩ := (dir m' a).2 _ hc _ hc',
        ⟨z, hz, zc, zc'⟩ := (dir m b).2 _ bc _ bc' in
    ⟨z, le_trans hb (mono _ hz), zc, zc'⟩⟩⟩

@[simp] lemma comap_comap : comap m (comap m' g) = comap (m' ∘ m) g :=
pfilter.ext $ λ _, iff.rfl

@[simp] lemma comap_comp : comap m ∘ comap m' = comap (m' ∘ m) :=
funext $ assume _, comap_comap _ _

end comap

section map
variables [preorder α] [preorder β] [preorder γ]
  (m : α → β) (mo : monotone m) (m' : β → γ) (mo' : monotone m')
  {f : pfilter α} {s : α} {t : β}

/-- The forward map of a preorder filter -/
def map (f : pfilter α) : pfilter β :=
{ sets       := { s | ∃t∈f, m t ≤ s },
  top_sets   := let ⟨a, ha⟩ := f.exists_mem in ⟨m a, a, ha, le_refl _⟩,
  sets_of_le := λ a b ab ⟨a', ha', ma'a⟩, ⟨a', ha', le_trans ma'a ab⟩,
  inf_sets   := λ a b ⟨a', ha₁, ha₂⟩ ⟨b', hb₁, hb₂⟩,
    let ⟨c, hc, ca, cb⟩ := mem_directed ha₁ hb₁ in
    ⟨m c, ⟨c, hc, le_refl _⟩,
      le_trans (mo ca) ha₂,
      le_trans (mo cb) hb₂⟩ }

variables {mo mo'}

lemma mem_map (hs : s ∈ f) : m s ∈ map m mo f := ⟨_, hs, le_refl _⟩

lemma range_mem_map {α β} [order_top α] [preorder β]
  (m : α → β) {mo} {f : pfilter α} : m ⊤ ∈ map m mo f :=
mem_map _ f.top_mem

lemma mem_map_iff : t ∈ map m mo f ↔ ∃s∈f, m s ≤ t := iff.rfl

@[simp] lemma map_id : map id monotone_id f = f :=
pfilter.ext $ λ _, exists_mem_le_iff

@[simp] lemma map_map :
  map m' mo' (map m mo f) = map (m' ∘ m) (monotone_comp mo mo') f :=
pfilter.ext $ λ c, ⟨
  λ ⟨b, ⟨a, ha, ab⟩, bc⟩, ⟨a, ha, le_trans (mo' ab) bc⟩,
  λ ⟨a, ha, ac⟩, ⟨m a, mem_map m ha, ac⟩⟩

@[simp] lemma map_comp :
  map m' mo' ∘ map m mo = map (m' ∘ m) (monotone_comp mo mo') :=
funext $ λ f, map_map _ _

end map

section Sup
variable [semilattice_inf_top α]

def Sup (S : set (pfilter α)) : pfilter α :=
join (_)

end Sup

section complete_lattice
variable [semilattice_inf_top α]

/- We lift the complete lattice along the Galois connection `generate` / `sets`. Unfortunately,
  we want to have different definitional equalities for the lattice operations. So we define them
  upfront and change the lattice operations for the complete lattice instance. -/

private def original_complete_lattice : complete_lattice (pfilter α) :=
@order_dual.lattice.complete_lattice _ (gi_generate α).lift_complete_lattice

local attribute [instance] original_complete_lattice

--set_option pp.all true
instance : complete_lattice (pfilter α) := original_complete_lattice.copy
  /- le  -/ pfilter.partial_order.le rfl
  /- top -/ ⊤
  (top_unique $ by exact (gi_generate _).gc.l_le (λ x, false.elim)).symm
  /- bot -/ ⊥ rfl
  /- sup -/ _ rfl
  /- inf -/ (⊓)
  (by ext f g : 2; apply le_antisymm; exact le_inf inf_le_left inf_le_right)
  /- Sup -/ (join ∘ principal) (by ext s x; exact (@mem_bInter_iff _ _ s pfilter x).symm)
  /- Inf -/ _ rfl

end complete_lattice
#exit
lemma bot_sets_eq : (⊥ : pfilter α) = univ := rfl

lemma sup_sets_eq {f g : pfilter α} : (f ⊔ g) = f ∩ g :=
(gi_generate α).gc.u_inf

lemma Sup_sets_eq {s : set (pfilter α)} : (Sup s) = (⋂f∈s, (f:pfilter α)) :=
(gi_generate α).gc.u_Inf

lemma supr_sets_eq {f : ι → pfilter α} : (supr f) = (⋂i, (f i)) :=
(gi_generate α).gc.u_infi

lemma generate_empty : pfilter.generate ∅ = (⊤ : pfilter α) :=
(gi_generate α).gc.l_bot

lemma generate_univ : pfilter.generate univ = (⊥ : pfilter α) :=
mk_of_closure_sets.symm

lemma generate_union {s t : set (set α)} :
  pfilter.generate (s ∪ t) = pfilter.generate s ⊓ pfilter.generate t :=
(gi_generate α).gc.l_sup

lemma generate_Union {s : ι → set (set α)} :
  pfilter.generate (⋃ i, s i) = (⨅ i, pfilter.generate (s i)) :=
(gi_generate α).gc.l_supr

@[simp] lemma mem_bot_sets {s : set α} : s ∈ (⊥ : pfilter α) :=
trivial

@[simp] lemma mem_sup_sets {f g : pfilter α} {s : set α} :
  s ∈ (f ⊔ g) ↔ s ∈ f ∧ s ∈ g :=
iff.rfl

@[simp] lemma mem_Sup_sets {x : set α} {s : set (pfilter α)} :
  x ∈ (Sup s) ↔ (∀f∈s, x ∈ (f:pfilter α)) :=
iff.rfl

@[simp] lemma mem_supr_sets {x : set α} {f : ι → pfilter α} :
  x ∈ (supr f) ↔ (∀i, x ∈ (f i)) :=
by simp only [supr_sets_eq, iff_self, mem_Inter]

@[simp] lemma join_principal_eq_Sup {s : set (pfilter α)} : join (principal s) = Sup s := rfl

/- lattice equations -/

lemma empty_in_sets_eq_bot {f : pfilter α} : ∅ ∈ f ↔ f = ⊥ :=
⟨assume h, bot_unique $ assume s _, mem_sets_of_superset h (empty_subset s),
  assume : f = ⊥, this.symm ▸ mem_bot_sets⟩

lemma inhabited_of_mem_sets {f : pfilter α} {s : set α} (hf : f ≠ ⊥) (hs : s ∈ f) :
  ∃x, x ∈ s :=
have ∅ ∉ f, from assume h, hf $ empty_in_sets_eq_bot.mp h,
have s ≠ ∅, from assume h, this (h ▸ hs),
exists_mem_of_ne_empty this

lemma pfilter_eq_bot_of_not_nonempty {f : pfilter α} (ne : ¬ nonempty α) : f = ⊥ :=
empty_in_sets_eq_bot.mp $ univ_mem_sets' $ assume x, false.elim (ne ⟨x⟩)

lemma forall_sets_neq_empty_iff_neq_bot {f : pfilter α} :
  (∀ (s : set α), s ∈ f → s ≠ ∅) ↔ f ≠ ⊥ :=
by
  simp only [(@empty_in_sets_eq_bot α f).symm, ne.def];
  exact ⟨assume h hs, h _ hs rfl, assume h s hs eq, h $ eq ▸ hs⟩

lemma mem_sets_of_neq_bot {f : pfilter α} {s : set α} (h : f ⊓ principal (-s) = ⊥) : s ∈ f :=
have ∅ ∈ (f ⊓ principal (- s)), from h.symm ▸ mem_bot_sets,
let ⟨s₁, hs₁, s₂, (hs₂ : -s ⊆ s₂), (hs : s₁ ∩ s₂ ⊆ ∅)⟩ := this in
by pfilter_upwards [hs₁] assume a ha, classical.by_contradiction $ assume ha', hs ⟨ha, hs₂ ha'⟩

lemma infi_sets_eq {f : ι → pfilter α} (h : directed (≥) f) (ne : nonempty ι) :
  (infi f) = (⋃ i, (f i)) :=
let ⟨i⟩ := ne, u := { pfilter .
    sets             := (⋃ i, (f i)),
    univ_sets        := by simp only [mem_Union]; exact ⟨i, univ_mem_sets⟩,
    sets_of_superset := by simp only [mem_Union, exists_imp_distrib];
                        intros x y i hx hxy; exact ⟨i, mem_sets_of_superset hx hxy⟩,
    inter_sets       :=
    begin
      simp only [mem_Union, exists_imp_distrib],
      assume x y a hx b hy,
      rcases h a b with ⟨c, ha, hb⟩,
      exact ⟨c, inter_mem_sets (ha hx) (hb hy)⟩
    end } in
subset.antisymm
  (show u ≤ infi f, from le_infi $ assume i, le_supr (λi, (f i)) i)
  (Union_subset $ assume i, infi_le f i)

lemma infi_sets_eq' {f : β → pfilter α} {s : set β} (h : directed_on (f ⁻¹'o (≥)) s) (ne : ∃i, i ∈ s) :
  (⨅ i∈s, f i) = (⋃ i ∈ s, (f i)) :=
let ⟨i, hi⟩ := ne in
calc (⨅ i ∈ s, f i)  = (⨅ t : {t // t ∈ s}, (f t.val)) : by rw [infi_subtype]; refl
  ... = (⨆ t : {t // t ∈ s}, (f t.val)) : infi_sets_eq
    (assume ⟨x, hx⟩ ⟨y, hy⟩, match h x hx y hy with ⟨z, h₁, h₂, h₃⟩ := ⟨⟨z, h₁⟩, h₂, h₃⟩ end)
    ⟨⟨i, hi⟩⟩
  ... = (⨆ t ∈ {t | t ∈ s}, (f t)) : by rw [supr_subtype]; refl

lemma Inf_sets_eq_finite {s : set (pfilter α)} :
  (Inf s) = (⋃ t ∈ {t | finite t ∧ t ⊆ s}, (Inf t)) :=
calc (Inf s) = (⨅ t ∈ { t | finite t ∧ t ⊆ s}, Inf t) : by rw [lattice.Inf_eq_finite_sets]
  ... = (⨆ t ∈ {t | finite t ∧ t ⊆ s}, (Inf t)) : infi_sets_eq'
    (assume x ⟨hx₁, hx₂⟩ y ⟨hy₁, hy₂⟩, ⟨x ∪ y, ⟨finite_union hx₁ hy₁, union_subset hx₂ hy₂⟩,
      Inf_le_Inf $ subset_union_left _ _, Inf_le_Inf $ subset_union_right _ _⟩)
    ⟨∅, by simp only [empty_subset, finite_empty, and_self, mem_set_of_eq]⟩

@[simp] lemma sup_join {f₁ f₂ : pfilter (pfilter α)} : (join f₁ ⊔ join f₂) = join (f₁ ⊔ f₂) :=
pfilter_eq $ set.ext $ assume x, by simp only [supr_sets_eq, join, mem_sup_sets, iff_self, mem_set_of_eq]

@[simp] lemma supr_join {ι : Sort w} {f : ι → pfilter (pfilter α)} : (⨆x, join (f x)) = join (⨆x, f x) :=
pfilter_eq $ set.ext $ assume x, by simp only [supr_sets_eq, join, iff_self, mem_Inter, mem_set_of_eq]

instance : bounded_distrib_lattice (pfilter α) :=
{ le_sup_inf :=
  begin
    assume x y z s,
    simp only [and_assoc, mem_inf_sets, mem_sup_sets, exists_prop, exists_imp_distrib, and_imp],
    intros hs t₁ ht₁ t₂ ht₂ hts,
    exact ⟨s ∪ t₁,
      x_of_superset hs $ subset_union_left _ _,
      y_of_superset ht₁ $ subset_union_right _ _,
      s ∪ t₂,
      x_of_superset hs $ subset_union_left _ _,
      z_of_superset ht₂ $ subset_union_right _ _,
      subset.trans (@le_sup_inf (set α) _ _ _ _) (union_subset (subset.refl _) hts)⟩
  end,
  ..pfilter.lattice.complete_lattice }

private lemma infi_finite_distrib {s : set (pfilter α)} {f : pfilter α} (h : finite s) :
  (⨅ a ∈ s, f ⊔ a) = f ⊔ (Inf s) :=
finite.induction_on h
  (by simp only [mem_empty_eq, infi_false, infi_top, Inf_empty, sup_top_eq])
  (by intros a s hn hs hi; rw [infi_insert, hi, ← sup_inf_left, Inf_insert])

/- the complementary version with ⨆ g∈s, f ⊓ g does not hold! -/
lemma binfi_sup_eq { f : pfilter α } {s : set (pfilter α)} : (⨅ g∈s, f ⊔ g) = f ⊔ Inf s :=
le_antisymm
  begin
    intros t h,
    cases h with h₁ h₂,
    rw [Inf_sets_eq_finite] at h₂,
    simp only [and_assoc, exists_prop, mem_Union, mem_set_of_eq] at h₂,
    rcases h₂ with ⟨s', hs', hs's, ht'⟩,
    have ht : t ∈ (⨅ a ∈ s', f ⊔ a),
    { rw [infi_finite_distrib], exact ⟨h₁, ht'⟩, exact hs' },
    clear h₁ ht',
    revert ht t,
    change (⨅ a ∈ s, f ⊔ a) ≤ (⨅ a ∈ s', f ⊔ a),
    apply infi_le_infi2 _,
    exact assume i, ⟨i, infi_le_infi2 $ assume h, ⟨hs's h, le_refl _⟩⟩
  end
  (le_infi $ assume g, le_infi $ assume h, sup_le_sup (le_refl f) $ Inf_le h)

lemma infi_sup_eq { f : pfilter α } {g : ι → pfilter α} : (⨅ x, f ⊔ g x) = f ⊔ infi g :=
calc (⨅ x, f ⊔ g x) = (⨅ x (h : ∃i, g i = x), f ⊔ x) :
  by simp only [infi_exists]; rw infi_comm; simp only [infi_infi_eq_right, eq_self_iff_true]
  ... = f ⊔ Inf {x | ∃i, g i = x} : binfi_sup_eq
  ... = f ⊔ infi g : by rw Inf_eq_infi; dsimp; simp only [infi_exists];
                        rw infi_comm; simp only [infi_infi_eq_right, eq_self_iff_true]

lemma mem_infi_sets_finset {s : finset α} {f : α → pfilter β} :
  ∀t, t ∈ (⨅a∈s, f a) ↔ (∃p:α → set β, (∀a∈s, p a ∈ (f a)) ∧ (⋂a∈s, p a) ⊆ t) :=
show ∀t, t ∈ (⨅a∈s, f a) ↔ (∃p:α → set β, (∀a∈s, p a ∈ (f a)) ∧ (⨅a∈s, p a) ≤ t),
begin
  refine finset.induction_on s _ _,
  { simp only [finset.not_mem_empty, false_implies_iff, lattice.infi_empty_finset, top_le_iff,
      imp_true_iff, mem_top_sets, true_and, exists_const],
    intros; refl },
  { intros a s has ih t,
    simp only [ih, finset.forall_mem_insert, lattice.infi_insert_finset, mem_inf_sets,
      exists_prop, iff_iff_implies_and_implies, exists_imp_distrib, and_imp, and_assoc] {contextual := tt},
    split,
    { intros t₁ ht₁ t₂ p hp ht₂ ht,
      existsi function.update p a t₁,
      have : ∀a'∈s, function.update p a t₁ a' = p a',
        from assume a' ha',
        have a' ≠ a, from assume h, has $ h ▸ ha',
        function.update_noteq this,
      have eq : (⨅j ∈ s, function.update p a t₁ j) = (⨅j ∈ s, p j),
        begin congr, funext b, congr, funext h, apply this, assumption end,
      simp only [this, ht₁, hp, function.update_same, true_and, imp_true_iff, eq] {contextual := tt},
      exact subset.trans (inter_subset_inter (subset.refl _) ht₂) ht },
    from assume p hpa hp ht, ⟨p a, hpa, (⨅j∈s, p j), ⟨⟨p, hp, le_refl _⟩, ht⟩⟩ }
end

/- principal equations -/

@[simp] lemma sup_principal {s t : set α} : principal s ⊔ principal t = principal (s ∪ t) :=
pfilter_eq $ set.ext $
  by simp only [union_subset_iff, union_subset_iff, mem_sup_sets, forall_const, iff_self, mem_principal_sets]

@[simp] lemma supr_principal {ι : Sort w} {s : ι → set α} : (⨆x, principal (s x)) = principal (⋃i, s i) :=
pfilter_eq $ set.ext $ assume x, by simp only [supr_sets_eq, mem_principal_sets, mem_Inter];
exact (@supr_le_iff (set α) _ _ _ _).symm

lemma principal_univ : principal (univ : set α) = ⊤ :=
top_unique $ by simp only [le_principal_iff, mem_top_sets, eq_self_iff_true]

lemma principal_empty : principal (∅ : set α) = ⊥ :=
bot_unique $ assume s _, empty_subset _

@[simp] lemma principal_eq_bot_iff {s : set α} : principal s = ⊥ ↔ s = ∅ :=
⟨assume h, principal_eq_iff_eq.mp $ by simp only [principal_empty, h, eq_self_iff_true],
  assume h, by simp only [h, principal_empty, eq_self_iff_true]⟩

lemma inf_principal_eq_bot {f : pfilter α} {s : set α} (hs : -s ∈ f) : f ⊓ principal s = ⊥ :=
empty_in_sets_eq_bot.mp ⟨_, hs, s, mem_principal_self s, assume x ⟨h₁, h₂⟩, h₁ h₂⟩

end lattice

section map

/-- The forward map of a pfilter -/
def map (m : α → β) (f : pfilter α) : pfilter β :=
{ sets             := preimage m ⁻¹' f,
  univ_sets        := univ_mem_sets,
  sets_of_superset := assume s t hs st, mem_sets_of_superset hs $ preimage_mono st,
  inter_sets       := assume s t hs ht, inter_mem_sets hs ht }

@[simp] lemma map_principal {s : set α} {f : α → β} :
  map f (principal s) = principal (set.image f s) :=
pfilter_eq $ set.ext $ assume a, image_subset_iff.symm

variables {f : pfilter α} {m : α → β} {m' : β → γ} {s : set α} {t : set β}

@[simp] lemma mem_map : t ∈ (map m f) ↔ {x | m x ∈ t} ∈ f := iff.rfl

lemma image_mem_map (hs : s ∈ f) : m '' s ∈ (map m f) :=
f_of_superset hs $ subset_preimage_image m s

lemma range_mem_map : range m ∈ (map m f) :=
by rw ←image_univ; exact image_mem_map univ_mem_sets

lemma mem_map_sets_iff : t ∈ (map m f) ↔ (∃s∈f, m '' s ⊆ t) :=
iff.intro
  (assume ht, ⟨set.preimage m t, ht, image_preimage_subset _ _⟩)
  (assume ⟨s, hs, ht⟩, mem_sets_of_superset (image_mem_map hs) ht)

@[simp] lemma map_id : pfilter.map id f = f :=
pfilter_eq $ rfl

@[simp] lemma map_compose : pfilter.map m' ∘ pfilter.map m = pfilter.map (m' ∘ m) :=
funext $ assume _, pfilter_eq $ rfl

@[simp] lemma map_map : pfilter.map m' (pfilter.map m f) = pfilter.map (m' ∘ m) f :=
congr_fun (@@pfilter.map_compose m m') f

end map

section comap

/-- The inverse map of a pfilter -/
def comap (m : α → β) (f : pfilter β) : pfilter α :=
{ sets             := { s | ∃t∈f, m ⁻¹' t ⊆ s },
  univ_sets        := ⟨univ, univ_mem_sets, by simp only [subset_univ, preimage_univ]⟩,
  sets_of_superset := assume a b ⟨a', ha', ma'a⟩ ab,
    ⟨a', ha', subset.trans ma'a ab⟩,
  inter_sets       := assume a b ⟨a', ha₁, ha₂⟩ ⟨b', hb₁, hb₂⟩,
    ⟨a' ∩ b', inter_mem_sets ha₁ hb₁, inter_subset_inter ha₂ hb₂⟩ }

end comap

/-- The cofinite pfilter is the pfilter of subsets whose complements are finite. -/
def cofinite : pfilter α :=
{ sets             := {s | finite (- s)},
  univ_sets        := by simp only [compl_univ, finite_empty, mem_set_of_eq],
  sets_of_superset := assume s t (hs : finite (-s)) (st: s ⊆ t),
    finite_subset hs $ @lattice.neg_le_neg (set α) _ _ _ st,
  inter_sets       := assume s t (hs : finite (-s)) (ht : finite (-t)),
    by simp only [compl_inter, finite_union, ht, hs, mem_set_of_eq] }

/-- The monadic bind operation on pfilter is defined the usual way in terms of `map` and `join`.

Unfortunately, this `bind` does not result in the expected applicative. See `pfilter.seq` for the
applicative instance. -/
def bind (f : pfilter α) (m : α → pfilter β) : pfilter β := join (map m f)

/-- The applicative sequentiation operation. This is not induced by the bind operation. -/
def seq (f : pfilter (α → β)) (g : pfilter α) : pfilter β :=
⟨{ s | ∃u∈f, ∃t∈g, (∀m∈u, ∀x∈t, (m : α → β) x ∈ s) },
  ⟨univ, univ_mem_sets, univ, univ_mem_sets, by simp only [forall_prop_of_true, mem_univ, forall_true_iff]⟩,
  assume s₀ s₁ ⟨t₀, t₁, h₀, h₁, h⟩ hst, ⟨t₀, t₁, h₀, h₁, assume x hx y hy, hst $ h _ hx _ hy⟩,
  assume s₀ s₁ ⟨t₀, ht₀, t₁, ht₁, ht⟩ ⟨u₀, hu₀, u₁, hu₁, hu⟩,
    ⟨t₀ ∩ u₀, inter_mem_sets ht₀ hu₀, t₁ ∩ u₁, inter_mem_sets ht₁ hu₁,
      assume x ⟨hx₀, hx₁⟩ x ⟨hy₀, hy₁⟩, ⟨ht _ hx₀ _ hy₀, hu _ hx₁ _ hy₁⟩⟩⟩

instance : has_pure pfilter := ⟨λ(α : Type u) x, principal {x}⟩

instance : has_bind pfilter := ⟨@pfilter.bind⟩

instance : has_seq pfilter := ⟨@pfilter.seq⟩

instance : functor pfilter := { map := @pfilter.map }

section
-- this section needs to be before applicative, otherwise the wrong instance will be chosen
protected def monad : monad pfilter := { map := @pfilter.map }

local attribute [instance] pfilter.monad
protected def is_lawful_monad : is_lawful_monad pfilter :=
{ id_map     := assume α f, pfilter_eq rfl,
  pure_bind  := assume α β a f, by simp only [bind, Sup_image, image_singleton,
    join_principal_eq_Sup, lattice.Sup_singleton, map_principal, eq_self_iff_true],
  bind_assoc := assume α β γ f m₁ m₂, pfilter_eq rfl,
  bind_pure_comp_eq_map := assume α β f x, pfilter_eq $
    by simp only [bind, join, map, preimage, principal, set.subset_univ, eq_self_iff_true,
      function.comp_app, mem_set_of_eq, singleton_subset_iff] }
end

instance : applicative pfilter := { map := @pfilter.map, seq := @pfilter.seq }

instance : alternative pfilter :=
{ failure := λα, ⊥,
  orelse  := λα x y, x ⊔ y }

@[simp] lemma pure_def (x : α) : pure x = principal {x} := rfl

@[simp] lemma mem_pure {a : α} {s : set α} : a ∈ s → s ∈ (pure a : pfilter α) :=
by simp only [imp_self, pure_def, mem_principal_sets, singleton_subset_iff]; exact id

@[simp] lemma mem_pure_iff {a : α} {s : set α} : s ∈ (pure a : pfilter α) ↔ a ∈ s :=
by rw [pure_def, mem_principal_sets, set.singleton_subset_iff]

@[simp] lemma map_def {α β} (m : α → β) (f : pfilter α) : m <$> f = map m f := rfl

@[simp] lemma bind_def {α β} (f : pfilter α) (m : α → pfilter β) : f >>= m = bind f m := rfl

/- map and comap equations -/
section map
variables {f f₁ f₂ : pfilter α} {g g₁ g₂ : pfilter β} {m : α → β} {m' : β → γ} {s : set α} {t : set β}

@[simp] theorem mem_comap_sets : s ∈ (comap m g) ↔ ∃t∈g, m ⁻¹' t ⊆ s := iff.rfl
theorem preimage_mem_comap (ht : t ∈ g) : m ⁻¹' t ∈ (comap m g) :=
⟨t, ht, subset.refl _⟩

lemma comap_id : comap id f = f :=
le_antisymm (assume s, preimage_mem_comap) (assume s ⟨t, ht, hst⟩, mem_sets_of_superset ht hst)

lemma comap_comap_comp {m : γ → β} {n : β → α} : comap m (comap n f) = comap (n ∘ m) f :=
le_antisymm
  (assume c ⟨b, hb, (h : preimage (n ∘ m) b ⊆ c)⟩, ⟨preimage n b, preimage_mem_comap hb, h⟩)
  (assume c ⟨b, ⟨a, ha, (h₁ : preimage n a ⊆ b)⟩, (h₂ : preimage m b ⊆ c)⟩,
    ⟨a, ha, show preimage m (preimage n a) ⊆ c, from subset.trans (preimage_mono h₁) h₂⟩)

@[simp] theorem comap_principal {t : set β} : comap m (principal t) = principal (m ⁻¹' t) :=
pfilter_eq $ set.ext $ assume s,
  ⟨assume ⟨u, (hu : t ⊆ u), (b : preimage m u ⊆ s)⟩, subset.trans (preimage_mono hu) b,
    assume : preimage m t ⊆ s, ⟨t, subset.refl t, this⟩⟩

lemma map_le_iff_le_comap : map m f ≤ g ↔ f ≤ comap m g :=
⟨assume h s ⟨t, ht, hts⟩, mem_sets_of_superset (h ht) hts, assume h s ht, h ⟨_, ht, subset.refl _⟩⟩

lemma gc_map_comap (m : α → β) : galois_connection (map m) (comap m) :=
assume f g, map_le_iff_le_comap

lemma map_mono (h : f₁ ≤ f₂) : map m f₁ ≤ map m f₂ := (gc_map_comap m).monotone_l h
lemma monotone_map : monotone (map m) | a b := map_mono
lemma comap_mono (h : g₁ ≤ g₂) : comap m g₁ ≤ comap m g₂ := (gc_map_comap m).monotone_u h
lemma monotone_comap : monotone (comap m) | a b := comap_mono

@[simp] lemma map_bot : map m ⊥ = ⊥ := (gc_map_comap m).l_bot
@[simp] lemma map_sup : map m (f₁ ⊔ f₂) = map m f₁ ⊔ map m f₂ := (gc_map_comap m).l_sup
@[simp] lemma map_supr {f : ι → pfilter α} : map m (⨆i, f i) = (⨆i, map m (f i)) :=
(gc_map_comap m).l_supr

@[simp] lemma comap_top : comap m ⊤ = ⊤ := (gc_map_comap m).u_top
@[simp] lemma comap_inf : comap m (g₁ ⊓ g₂) = comap m g₁ ⊓ comap m g₂ := (gc_map_comap m).u_inf
@[simp] lemma comap_infi {f : ι → pfilter β} : comap m (⨅i, f i) = (⨅i, comap m (f i)) :=
(gc_map_comap m).u_infi

lemma map_comap_le : map m (comap m g) ≤ g := (gc_map_comap m).l_u_le _
lemma le_comap_map : f ≤ comap m (map m f) := (gc_map_comap m).le_u_l _

@[simp] lemma comap_bot : comap m ⊥ = ⊥ :=
bot_unique $ assume s _, ⟨∅, by simp only [mem_bot_sets], by simp only [empty_subset, preimage_empty]⟩

lemma comap_supr {ι} {f : ι → pfilter β} {m : α → β} :
  comap m (supr f) = (⨆i, comap m (f i)) :=
le_antisymm
  (assume s hs,
    have ∀i, ∃t, t ∈ (f i) ∧ m ⁻¹' t ⊆ s, by simpa only [mem_comap_sets, exists_prop, mem_supr_sets] using mem_supr_sets.1 hs,
    let ⟨t, ht⟩ := classical.axiom_of_choice this in
    ⟨⋃i, t i, mem_supr_sets.2 $ assume i, (f i)_of_superset (ht i).1 (subset_Union _ _),
      begin
        rw [preimage_Union, Union_subset_iff],
        assume i,
        exact (ht i).2
      end⟩)
  (supr_le $ assume i, monotone_comap $ le_supr _ _)

lemma comap_Sup {s : set (pfilter β)} {m : α → β} : comap m (Sup s) = (⨆f∈s, comap m f) :=
by simp only [Sup_eq_supr, comap_supr, eq_self_iff_true]

lemma comap_sup : comap m (g₁ ⊔ g₂) = comap m g₁ ⊔ comap m g₂ :=
le_antisymm
  (assume s ⟨⟨t₁, ht₁, hs₁⟩, ⟨t₂, ht₂, hs₂⟩⟩,
    ⟨t₁ ∪ t₂,
      ⟨g₁_of_superset ht₁ (subset_union_left _ _), g₂_of_superset ht₂ (subset_union_right _ _)⟩,
      union_subset hs₁ hs₂⟩)
  (sup_le (comap_mono le_sup_left) (comap_mono le_sup_right))

lemma le_map_comap' {f : pfilter β} {m : α → β} {s : set β}
  (hs : s ∈ f) (hm : ∀b∈s, ∃a, m a = b) : f ≤ map m (comap m f) :=
assume t' ⟨t, ht, (sub : m ⁻¹' t ⊆ m ⁻¹' t')⟩,
by pfilter_upwards [ht, hs] assume x hxt hxs,
  let ⟨y, hy⟩ := hm x hxs in
  hy ▸ sub (show m y ∈ t, from hy.symm ▸ hxt)

lemma le_map_comap {f : pfilter β} {m : α → β} (hm : ∀x, ∃y, m y = x) : f ≤ map m (comap m f) :=
le_map_comap' univ_mem_sets (assume b _, hm b)

lemma comap_map {f : pfilter α} {m : α → β} (h : ∀ x y, m x = m y → x = y) :
  comap m (map m f) = f :=
have ∀s, preimage m (image m s) = s,
  from assume s, preimage_image_eq s h,
le_antisymm
  (assume s hs, ⟨
    image m s,
    f_of_superset hs $ by simp only [this, subset.refl],
    by simp only [this, subset.refl]⟩)
  le_comap_map

lemma le_of_map_le_map_inj' {f g : pfilter α} {m : α → β} {s : set α}
  (hsf : s ∈ f) (hsg : s ∈ g) (hm : ∀x∈s, ∀y∈s, m x = m y → x = y)
  (h : map m f ≤ map m g) : f ≤ g :=
assume t ht, by pfilter_upwards [hsf, h $ image_mem_map (inter_mem_sets hsg ht)]
assume a has ⟨b, ⟨hbs, hb⟩, h⟩,
have b = a, from hm _ hbs _ has h,
this ▸ hb

lemma le_of_map_le_map_inj_iff {f g : pfilter α} {m : α → β} {s : set α}
  (hsf : s ∈ f) (hsg : s ∈ g) (hm : ∀x∈s, ∀y∈s, m x = m y → x = y) :
  map m f ≤ map m g ↔ f ≤ g :=
iff.intro (le_of_map_le_map_inj' hsf hsg hm) map_mono

lemma eq_of_map_eq_map_inj' {f g : pfilter α} {m : α → β} {s : set α}
  (hsf : s ∈ f) (hsg : s ∈ g) (hm : ∀x∈s, ∀y∈s, m x = m y → x = y)
  (h : map m f = map m g) : f = g :=
le_antisymm
  (le_of_map_le_map_inj' hsf hsg hm $ le_of_eq h)
  (le_of_map_le_map_inj' hsg hsf hm $ le_of_eq h.symm)

lemma map_inj {f g : pfilter α} {m : α → β} (hm : ∀ x y, m x = m y → x = y) (h : map m f = map m g) :
  f = g :=
have comap m (map m f) = comap m (map m g), by rw h,
by rwa [comap_map hm, comap_map hm] at this

lemma comap_neq_bot {f : pfilter β} {m : α → β}
  (hm : ∀t∈f, ∃a, m a ∈ t) : comap m f ≠ ⊥ :=
forall_sets_neq_empty_iff_neq_bot.mp $ assume s ⟨t, ht, t_s⟩,
  let ⟨a, (ha : a ∈ preimage m t)⟩ := hm t ht in
  neq_bot_of_le_neq_bot (ne_empty_of_mem ha) t_s

lemma comap_neq_bot_of_surj {f : pfilter β} {m : α → β}
  (hf : f ≠ ⊥) (hm : ∀b, ∃a, m a = b) : comap m f ≠ ⊥ :=
comap_neq_bot $ assume t ht,
  let
    ⟨b, (hx : b ∈ t)⟩ := inhabited_of_mem_sets hf ht,
    ⟨a, (ha : m a = b)⟩ := hm b
  in ⟨a, ha.symm ▸ hx⟩

@[simp] lemma map_eq_bot_iff : map m f = ⊥ ↔ f = ⊥ :=
⟨by rw [←empty_in_sets_eq_bot, ←empty_in_sets_eq_bot]; exact id,
  assume h, by simp only [h, eq_self_iff_true, map_bot]⟩

lemma map_ne_bot (hf : f ≠ ⊥) : map m f ≠ ⊥ :=
assume h, hf $ by rwa [map_eq_bot_iff] at h

lemma sInter_comap_sets (f : α → β) (F : pfilter β) :
  ⋂₀(comap f F) = ⋂ U ∈ F, f ⁻¹' U :=
begin
  ext x,
  suffices : (∀ (A : set α) (B : set β), B ∈ F → f ⁻¹' B ⊆ A → x ∈ A) ↔
    ∀ (B : set β), B ∈ F → f x ∈ B,
  by simp only [mem_sInter, mem_Inter, mem_comap_sets, this, and_imp, mem_comap_sets, exists_prop, mem_sInter,
    iff_self, mem_Inter, mem_preimage_eq, exists_imp_distrib],
  split,
  { intros h U U_in,
    simpa only [set.subset.refl, forall_prop_of_true, mem_preimage_eq] using h (f ⁻¹' U) U U_in },
  { intros h V U U_in f_U_V,
    exact f_U_V (h U U_in) },
end
end map

lemma map_cong {m₁ m₂ : α → β} {f : pfilter α} (h : {x | m₁ x = m₂ x} ∈ f) :
  map m₁ f = map m₂ f :=
have ∀(m₁ m₂ : α → β) (h : {x | m₁ x = m₂ x} ∈ f), map m₁ f ≤ map m₂ f,
begin
  intros  m₁ m₂ h s hs,
  show {x | m₁ x ∈ s} ∈ f,
  pfilter_upwards [h, hs],
  simp only [subset_def, mem_preimage_eq, mem_set_of_eq, forall_true_iff] {contextual := tt}
end,
le_antisymm (this m₁ m₂ h) (this m₂ m₁ $ mem_sets_of_superset h $ assume x, eq.symm)

-- this is a generic rule for monotone functions:
lemma map_infi_le {f : ι → pfilter α} {m : α → β} :
  map m (infi f) ≤ (⨅ i, map m (f i)) :=
le_infi $ assume i, map_mono $ infi_le _ _

lemma map_infi_eq {f : ι → pfilter α} {m : α → β} (hf : directed (≥) f) (hι : nonempty ι) :
  map m (infi f) = (⨅ i, map m (f i)) :=
le_antisymm
  map_infi_le
  (assume s (hs : preimage m s ∈ (infi f)),
    have ∃i, preimage m s ∈ (f i),
      by simp only [infi_sets_eq hf hι, mem_Union] at hs; assumption,
    let ⟨i, hi⟩ := this in
    have (⨅ i, map m (f i)) ≤ principal s, from
      infi_le_of_le i $ by simp only [le_principal_iff, mem_map]; assumption,
    by simp only [pfilter.le_principal_iff] at this; assumption)

lemma map_binfi_eq {ι : Type w} {f : ι → pfilter α} {m : α → β} {p : ι → Prop}
  (h : directed_on (f ⁻¹'o (≥)) {x | p x}) (ne : ∃i, p i) :
  map m (⨅i (h : p i), f i) = (⨅i (h: p i), map m (f i)) :=
let ⟨i, hi⟩ := ne in
calc map m (⨅i (h : p i), f i) = map m (⨅i:subtype p, f i.val) : by simp only [infi_subtype, eq_self_iff_true]
  ... = (⨅i:subtype p, map m (f i.val)) : map_infi_eq
    (assume ⟨x, hx⟩ ⟨y, hy⟩, match h x hx y hy with ⟨z, h₁, h₂, h₃⟩ := ⟨⟨z, h₁⟩, h₂, h₃⟩ end)
    ⟨⟨i, hi⟩⟩
  ... = (⨅i (h : p i), map m (f i)) : by simp only [infi_subtype, eq_self_iff_true]

lemma map_inf' {f g : pfilter α} {m : α → β} {t : set α} (htf : t ∈ f) (htg : t ∈ g)
  (h : ∀x∈t, ∀y∈t, m x = m y → x = y) : map m (f ⊓ g) = map m f ⊓ map m g :=
begin
  refine le_antisymm
    (le_inf (map_mono inf_le_left) (map_mono inf_le_right))
    (assume s hs, _),
  simp only [map, mem_inf_sets, exists_prop, mem_map, mem_preimage_eq, mem_inf_sets] at hs ⊢,
  rcases hs with ⟨t₁, h₁, t₂, h₂, hs⟩,
  refine ⟨m '' (t₁ ∩ t), _, m '' (t₂ ∩ t), _, _⟩,
  { pfilter_upwards [h₁, htf] assume a h₁ h₂, mem_image_of_mem _ ⟨h₁, h₂⟩ },
  { pfilter_upwards [h₂, htg] assume a h₁ h₂, mem_image_of_mem _ ⟨h₁, h₂⟩ },
  { rw [image_inter_on],
    { refine image_subset_iff.2 _,
      exact λ x ⟨⟨h₁, _⟩, h₂, _⟩, hs ⟨h₁, h₂⟩ },
    { exact λ x ⟨_, hx⟩ y ⟨_, hy⟩, h x hx y hy } }
end

lemma map_inf {f g : pfilter α} {m : α → β} (h : ∀ x y, m x = m y → x = y) :
  map m (f ⊓ g) = map m f ⊓ map m g :=
map_inf' univ_mem_sets univ_mem_sets (assume x _ y _, h x y)

lemma map_eq_comap_of_inverse {f : pfilter α} {m : α → β} {n : β → α}
  (h₁ : m ∘ n = id) (h₂ : n ∘ m = id) : map m f = comap n f :=
le_antisymm
  (assume b ⟨a, ha, (h : preimage n a ⊆ b)⟩, f_of_superset ha $
    calc a = preimage (n ∘ m) a : by simp only [h₂, preimage_id, eq_self_iff_true]
      ... ⊆ preimage m b : preimage_mono h)
  (assume b (hb : preimage m b ∈ f),
    ⟨preimage m b, hb, show preimage (m ∘ n) b ⊆ b, by simp only [h₁]; apply subset.refl⟩)

lemma map_swap_eq_comap_swap {f : pfilter (α × β)} : prod.swap <$> f = comap prod.swap f :=
map_eq_comap_of_inverse prod.swap_swap_eq prod.swap_swap_eq

lemma le_map {f : pfilter α} {m : α → β} {g : pfilter β} (h : ∀s∈f, m '' s ∈ g) :
  g ≤ f.map m :=
assume s hs, mem_sets_of_superset (h _ hs) $ image_preimage_subset _ _

section applicative

@[simp] lemma mem_pure_sets {a : α} {s : set α} :
  s ∈ (pure a : pfilter α) ↔ a ∈ s :=
by simp only [iff_self, pure_def, mem_principal_sets, singleton_subset_iff]

lemma singleton_mem_pure_sets {a : α} : {a} ∈ (pure a : pfilter α) :=
by simp only [mem_singleton, pure_def, mem_principal_sets, singleton_subset_iff]

@[simp] lemma pure_neq_bot {α : Type u} {a : α} : pure a ≠ (⊥ : pfilter α) :=
by simp only [pure, has_pure.pure, ne.def, not_false_iff, singleton_ne_empty, principal_eq_bot_iff]

lemma mem_seq_sets_def {f : pfilter (α → β)} {g : pfilter α} {s : set β} :
  s ∈ (f.seq g) ↔ (∃u∈f, ∃t∈g, ∀x∈u, ∀y∈t, (x : α → β) y ∈ s) :=
iff.refl _

lemma mem_seq_sets_iff {f : pfilter (α → β)} {g : pfilter α} {s : set β} :
  s ∈ (f.seq g) ↔ (∃u∈f, ∃t∈g, set.seq u t ⊆ s) :=
by simp only [mem_seq_sets_def, seq_subset, exists_prop, iff_self]

lemma mem_map_seq_iff {f : pfilter α} {g : pfilter β} {m : α → β → γ} {s : set γ} :
  s ∈ ((f.map m).seq g) ↔ (∃t u, t ∈ g ∧ u ∈ f ∧ ∀x∈u, ∀y∈t, m x y ∈ s) :=
iff.intro
  (assume ⟨t, ht, s, hs, hts⟩, ⟨s, m ⁻¹' t, hs, ht, assume a, hts _⟩)
  (assume ⟨t, s, ht, hs, hts⟩, ⟨m '' s, image_mem_map hs, t, ht, assume f ⟨a, has, eq⟩, eq ▸ hts _ has⟩)

lemma seq_mem_seq_sets {f : pfilter (α → β)} {g : pfilter α} {s : set (α → β)} {t : set α}
  (hs : s ∈ f) (ht : t ∈ g): s.seq t ∈ (f.seq g) :=
⟨s, hs, t, ht, assume f hf a ha, ⟨f, hf, a, ha, rfl⟩⟩

lemma le_seq {f : pfilter (α → β)} {g : pfilter α} {h : pfilter β}
  (hh : ∀t∈f, ∀u∈g, set.seq t u ∈ h) : h ≤ seq f g :=
assume s ⟨t, ht, u, hu, hs⟩, mem_sets_of_superset (hh _ ht _ hu) $
  assume b ⟨m, hm, a, ha, eq⟩, eq ▸ hs _ hm _ ha

lemma seq_mono {f₁ f₂ : pfilter (α → β)} {g₁ g₂ : pfilter α}
  (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) : f₁.seq g₁ ≤ f₂.seq g₂ :=
le_seq $ assume s hs t ht, seq_mem_seq_sets (hf hs) (hg ht)

@[simp] lemma pure_seq_eq_map (g : α → β) (f : pfilter α) : seq (pure g) f = f.map g :=
begin
  refine le_antisymm  (le_map $ assume s hs, _) (le_seq $ assume s hs t ht, _),
  { rw ← singleton_seq, apply seq_mem_seq_sets _ hs,
    simp only [mem_singleton, pure_def, mem_principal_sets, singleton_subset_iff] },
  { rw mem_pure_sets at hs,
    refine sets_of_superset (map g f) (image_mem_map ht) _,
    rintros b ⟨a, ha, rfl⟩, exact ⟨g, hs, a, ha, rfl⟩ }
end

@[simp] lemma map_pure (f : α → β) (a : α) : map f (pure a) = pure (f a) :=
le_antisymm
  (le_principal_iff.2 $ sets_of_superset (map f (pure a)) (image_mem_map singleton_mem_pure_sets) $
    by simp only [image_singleton, mem_singleton, singleton_subset_iff])
  (le_map $ assume s, begin
    simp only [mem_image, pure_def, mem_principal_sets, singleton_subset_iff],
    exact assume has, ⟨a, has, rfl⟩
  end)

@[simp] lemma seq_pure (f : pfilter (α → β)) (a : α) : seq f (pure a) = map (λg:α → β, g a) f :=
begin
  refine le_antisymm (le_map $ assume s hs, _) (le_seq $ assume s hs t ht, _),
  { rw ← seq_singleton, exact seq_mem_seq_sets hs
    (by simp only [mem_singleton, pure_def, mem_principal_sets, singleton_subset_iff]) },
  { rw mem_pure_sets at ht,
    refine sets_of_superset (map (λg:α→β, g a) f) (image_mem_map hs) _,
    rintros b ⟨g, hg, rfl⟩, exact ⟨g, hg, a, ht, rfl⟩ }
end

@[simp] lemma seq_assoc (x : pfilter α) (g : pfilter (α → β)) (h : pfilter (β → γ)) :
  seq h (seq g x) = seq (seq (map (∘) h) g) x :=
begin
  refine le_antisymm (le_seq $ assume s hs t ht, _) (le_seq $ assume s hs t ht, _),
  { rcases mem_seq_sets_iff.1 hs with ⟨u, hu, v, hv, hs⟩,
    rcases mem_map_sets_iff.1 hu with ⟨w, hw, hu⟩,
    refine mem_sets_of_superset _
      (set.seq_mono (subset.trans (set.seq_mono hu (subset.refl _)) hs) (subset.refl _)),
    rw ← set.seq_seq,
    exact seq_mem_seq_sets hw (seq_mem_seq_sets hv ht) },
  { rcases mem_seq_sets_iff.1 ht with ⟨u, hu, v, hv, ht⟩,
    refine mem_sets_of_superset _ (set.seq_mono (subset.refl _) ht),
    rw set.seq_seq,
    exact seq_mem_seq_sets (seq_mem_seq_sets (image_mem_map hs) hu) hv }
end

lemma prod_map_seq_comm (f : pfilter α) (g : pfilter β) :
  (map prod.mk f).seq g = seq (map (λb a, (a, b)) g) f :=
begin
  refine le_antisymm (le_seq $ assume s hs t ht, _) (le_seq $ assume s hs t ht, _),
  { rcases mem_map_sets_iff.1 hs with ⟨u, hu, hs⟩,
    refine mem_sets_of_superset _ (set.seq_mono hs (subset.refl _)),
    rw ← set.prod_image_seq_comm,
    exact seq_mem_seq_sets (image_mem_map ht) hu },
  { rcases mem_map_sets_iff.1 hs with ⟨u, hu, hs⟩,
    refine mem_sets_of_superset _ (set.seq_mono hs (subset.refl _)),
    rw set.prod_image_seq_comm,
    exact seq_mem_seq_sets (image_mem_map ht) hu }
end

instance : is_lawful_functor (pfilter : Type u → Type u) :=
{ id_map   := assume α f, map_id,
  comp_map := assume α β γ f g a, map_map.symm }

instance : is_lawful_applicative (pfilter : Type u → Type u) :=
{ pure_seq_eq_map := assume α β, pure_seq_eq_map,
  map_pure        := assume α β, map_pure,
  seq_pure        := assume α β, seq_pure,
  seq_assoc       := assume α β γ, seq_assoc }

instance : is_comm_applicative (pfilter : Type u → Type u) :=
⟨assume α β f g, prod_map_seq_comm f g⟩

lemma {l} seq_eq_pfilter_seq {α β : Type l} (f : pfilter (α → β)) (g : pfilter α) :
  f <*> g = seq f g := rfl

end applicative

/- bind equations -/
section bind
@[simp] lemma mem_bind_sets {s : set β} {f : pfilter α} {m : α → pfilter β} :
  s ∈ (bind f m) ↔ ∃t ∈ f, ∀x ∈ t, s ∈ (m x) :=
calc s ∈ (bind f m) ↔ {a | s ∈ (m a)} ∈ f : by simp only [bind, mem_map, iff_self, mem_join_sets, mem_set_of_eq]
                     ... ↔ (∃t ∈ f, t ⊆ {a | s ∈ (m a)}) : exists_sets_subset_iff.symm
                     ... ↔ (∃t ∈ f, ∀x ∈ t, s ∈ (m x)) : iff.refl _

lemma bind_mono {f : pfilter α} {g h : α → pfilter β} (h₁ : {a | g a ≤ h a} ∈ f) :
  bind f g ≤ bind f h :=
assume x h₂, show (_ ∈ f), by pfilter_upwards [h₁, h₂] assume s gh' h', gh' h'

lemma bind_sup {f g : pfilter α} {h : α → pfilter β} :
  bind (f ⊔ g) h = bind f h ⊔ bind g h :=
by simp only [bind, sup_join, map_sup, eq_self_iff_true]

lemma bind_mono2 {f g : pfilter α} {h : α → pfilter β} (h₁ : f ≤ g) :
  bind f h ≤ bind g h :=
assume s h', h₁ h'

lemma principal_bind {s : set α} {f : α → pfilter β} :
  (bind (principal s) f) = (⨆x ∈ s, f x) :=
show join (map f (principal s)) = (⨆x ∈ s, f x),
  by simp only [Sup_image, join_principal_eq_Sup, map_principal, eq_self_iff_true]

end bind

lemma infi_neq_bot_of_directed {f : ι → pfilter α}
  (hn : nonempty α) (hd : directed (≥) f) (hb : ∀i, f i ≠ ⊥): (infi f) ≠ ⊥ :=
let ⟨x⟩ := hn in
assume h, have he: ∅ ∈ (infi f), from h.symm ▸ mem_bot_sets,
classical.by_cases
  (assume : nonempty ι,
    have ∃i, ∅ ∈ (f i),
      by rw [infi_sets_eq hd this] at he; simp only [mem_Union] at he; assumption,
    let ⟨i, hi⟩ := this in
    hb i $ bot_unique $
    assume s _, (f i)_of_superset hi $ empty_subset _)
  (assume : ¬ nonempty ι,
    have univ ⊆ (∅ : set α),
    begin
      rw [←principal_mono, principal_univ, principal_empty, ←h],
      exact (le_infi $ assume i, false.elim $ this ⟨i⟩)
    end,
    this $ mem_univ x)

lemma infi_neq_bot_iff_of_directed {f : ι → pfilter α}
  (hn : nonempty α) (hd : directed (≥) f) : (infi f) ≠ ⊥ ↔ (∀i, f i ≠ ⊥) :=
⟨assume neq_bot i eq_bot, neq_bot $ bot_unique $ infi_le_of_le i $ eq_bot ▸ le_refl _,
  infi_neq_bot_of_directed hn hd⟩

lemma mem_infi_sets {f : ι → pfilter α} (i : ι) : ∀{s}, s ∈ (f i) → s ∈ (⨅i, f i) :=
show (⨅i, f i) ≤ f i, from infi_le _ _

@[elab_as_eliminator]
lemma infi_sets_induct {f : ι → pfilter α} {s : set α} (hs : s ∈ (infi f)) {p : set α → Prop}
  (uni : p univ)
  (ins : ∀{i s₁ s₂}, s₁ ∈ (f i) → p s₂ → p (s₁ ∩ s₂))
  (upw : ∀{s₁ s₂}, s₁ ⊆ s₂ → p s₁ → p s₂) : p s :=
begin
  have hs' : s ∈ (Inf {a : pfilter α | ∃ (i : ι), a = f i}) := hs,
  rw [Inf_sets_eq_finite] at hs',
  simp only [mem_Union] at hs',
  rcases hs' with ⟨is, ⟨fin_is, his⟩, hs⟩, revert his s,
  refine finite.induction_on fin_is _ (λ fi is fi_ne_is fin_is ih, _); intros his s hs' hs,
  { rw [Inf_empty, mem_top_sets] at hs, simpa only [hs] },
  { rw [Inf_insert] at hs,
    rcases hs with ⟨s₁, hs₁, s₂, hs₂, hs⟩,
    rcases (his (mem_insert _ _) : ∃i, fi = f i) with ⟨i, rfl⟩,
    have hs₂ : p s₂, from
      have his : is ⊆ {x | ∃i, x = f i}, from assume i hi, his $ mem_insert_of_mem _ hi,
      have infi f ≤ Inf is, from Inf_le_Inf his,
      ih his (this hs₂) hs₂,
    exact upw hs (ins hs₁ hs₂) }
end

/- tendsto -/

/-- `tendsto` is the generic "limit of a function" predicate.
  `tendsto f l₁ l₂` asserts that for every `l₂` neighborhood `a`,
  the `f`-preimage of `a` is an `l₁` neighborhood. -/
def tendsto (f : α → β) (l₁ : pfilter α) (l₂ : pfilter β) := l₁.map f ≤ l₂

lemma tendsto_def {f : α → β} {l₁ : pfilter α} {l₂ : pfilter β} :
  tendsto f l₁ l₂ ↔ ∀ s ∈ l₂, f ⁻¹' s ∈ l₁ := iff.rfl

lemma tendsto_iff_comap {f : α → β} {l₁ : pfilter α} {l₂ : pfilter β} :
  tendsto f l₁ l₂ ↔ l₁ ≤ l₂.comap f :=
map_le_iff_le_comap

lemma tendsto_cong {f₁ f₂ : α → β} {l₁ : pfilter α} {l₂ : pfilter β}
  (h : tendsto f₁ l₁ l₂) (hl : {x | f₁ x = f₂ x} ∈ l₁) : tendsto f₂ l₁ l₂ :=
by rwa [tendsto, ←map_cong hl]

lemma tendsto_id' {x y : pfilter α} : x ≤ y → tendsto id x y :=
by simp only [tendsto, map_id, forall_true_iff] {contextual := tt}

lemma tendsto_id {x : pfilter α} : tendsto id x x := tendsto_id' $ le_refl x

lemma tendsto.comp {f : α → β} {g : β → γ} {x : pfilter α} {y : pfilter β} {z : pfilter γ}
  (hf : tendsto f x y) (hg : tendsto g y z) : tendsto (g ∘ f) x z :=
calc map (g ∘ f) x = map g (map f x) : by rw [map_map]
  ... ≤ map g y : map_mono hf
  ... ≤ z : hg

lemma tendsto_le_left {f : α → β} {x y : pfilter α} {z : pfilter β}
  (h : y ≤ x) : tendsto f x z → tendsto f y z :=
le_trans (map_mono h)

lemma tendsto_le_right {f : α → β} {x : pfilter α} {y z : pfilter β}
  (h₁ : y ≤ z) (h₂ : tendsto f x y) : tendsto f x z :=
le_trans h₂ h₁

lemma tendsto_map {f : α → β} {x : pfilter α} : tendsto f x (map f x) := le_refl (map f x)

lemma tendsto_map' {f : β → γ} {g : α → β} {x : pfilter α} {y : pfilter γ}
  (h : tendsto (f ∘ g) x y) : tendsto f (map g x) y :=
by rwa [tendsto, map_map]

lemma tendsto_map'_iff {f : β → γ} {g : α → β} {x : pfilter α} {y : pfilter γ} :
  tendsto f (map g x) y ↔ tendsto (f ∘ g) x y :=
by rw [tendsto, map_map]; refl

lemma tendsto_comap {f : α → β} {x : pfilter β} : tendsto f (comap f x) x :=
map_comap_le

lemma tendsto_comap_iff {f : α → β} {g : β → γ} {a : pfilter α} {c : pfilter γ} :
  tendsto f a (c.comap g) ↔ tendsto (g ∘ f) a c :=
⟨assume h, h.comp tendsto_comap, assume h, map_le_iff_le_comap.mp $ by rwa [map_map]⟩

lemma tendsto_comap'' {m : α → β} {f : pfilter α} {g : pfilter β} (s : set α)
  {i : γ → α} (hs : s ∈ f) (hi : ∀a∈s, ∃c, i c = a)
  (h : tendsto (m ∘ i) (comap i f) g) : tendsto m f g :=
have tendsto m (map i $ comap i $ f) g,
  by rwa [tendsto, ←map_compose] at h,
le_trans (map_mono $ le_map_comap' hs hi) this

lemma comap_eq_of_inverse {f : pfilter α} {g : pfilter β} {φ : α → β} (ψ : β → α)
  (eq : ψ ∘ φ = id) (hφ : tendsto φ f g) (hψ : tendsto ψ g f) : comap φ g = f :=
begin
  refine le_antisymm (le_trans (comap_mono $ map_le_iff_le_comap.1 hψ) _) (map_le_iff_le_comap.1 hφ),
  rw [comap_comap_comp, eq, comap_id],
  exact le_refl _
end

lemma map_eq_of_inverse {f : pfilter α} {g : pfilter β} {φ : α → β} (ψ : β → α)
  (eq : φ ∘ ψ = id) (hφ : tendsto φ f g) (hψ : tendsto ψ g f) : map φ f = g :=
begin
  refine le_antisymm hφ (le_trans _ (map_mono hψ)),
  rw [map_map, eq, map_id],
  exact le_refl _
end

lemma tendsto_inf {f : α → β} {x : pfilter α} {y₁ y₂ : pfilter β} :
  tendsto f x (y₁ ⊓ y₂) ↔ tendsto f x y₁ ∧ tendsto f x y₂ :=
by simp only [tendsto, lattice.le_inf_iff, iff_self]

lemma tendsto_inf_left {f : α → β} {x₁ x₂ : pfilter α} {y : pfilter β}
  (h : tendsto f x₁ y) : tendsto f (x₁ ⊓ x₂) y  :=
le_trans (map_mono inf_le_left) h

lemma tendsto_inf_right {f : α → β} {x₁ x₂ : pfilter α} {y : pfilter β}
  (h : tendsto f x₂ y) : tendsto f (x₁ ⊓ x₂) y  :=
le_trans (map_mono inf_le_right) h

lemma tendsto_infi {f : α → β} {x : pfilter α} {y : ι → pfilter β} :
  tendsto f x (⨅i, y i) ↔ ∀i, tendsto f x (y i) :=
by simp only [tendsto, iff_self, lattice.le_infi_iff]

lemma tendsto_infi' {f : α → β} {x : ι → pfilter α} {y : pfilter β} (i : ι) :
  tendsto f (x i) y → tendsto f (⨅i, x i) y :=
tendsto_le_left (infi_le _ _)

lemma tendsto_principal {f : α → β} {a : pfilter α} {s : set β} :
  tendsto f a (principal s) ↔ {a | f a ∈ s} ∈ a :=
by simp only [tendsto, le_principal_iff, mem_map, iff_self]

lemma tendsto_principal_principal {f : α → β} {s : set α} {t : set β} :
  tendsto f (principal s) (principal t) ↔ ∀a∈s, f a ∈ t :=
by simp only [tendsto, image_subset_iff, le_principal_iff, map_principal, mem_principal_sets]; refl

lemma tendsto_pure_pure (f : α → β) (a : α) :
  tendsto f (pure a) (pure (f a)) :=
show pfilter.map f (pure a) ≤ pure (f a),
  by rw [pfilter.map_pure]; exact le_refl _

lemma tendsto_const_pure {a : pfilter α} {b : β} : tendsto (λa, b) a (pure b) :=
by simp [tendsto]; exact univ_mem_sets

section lift

/-- A variant on `bind` using a function `g` taking a set
  instead of a member of `α`. -/
protected def lift (f : pfilter α) (g : set α → pfilter β) :=
⨅s ∈ f, g s

variables {f f₁ f₂ : pfilter α} {g g₁ g₂ : set α → pfilter β}

lemma lift_sets_eq (hg : monotone g) : (f.lift g) = (⋃t∈f, (g t)) :=
infi_sets_eq'
  (assume s hs t ht, ⟨s ∩ t, inter_mem_sets hs ht,
    hg $ inter_subset_left s t, hg $ inter_subset_right s t⟩)
  ⟨univ, univ_mem_sets⟩

lemma mem_lift {s : set β} {t : set α} (ht : t ∈ f) (hs : s ∈ (g t)) :
  s ∈ (f.lift g) :=
le_principal_iff.mp $ show f.lift g ≤ principal s,
  from infi_le_of_le t $ infi_le_of_le ht $ le_principal_iff.mpr hs

lemma mem_lift_sets (hg : monotone g) {s : set β} :
  s ∈ (f.lift g) ↔ (∃t∈f, s ∈ (g t)) :=
by rw [lift_sets_eq hg]; simp only [mem_Union]

lemma lift_le {f : pfilter α} {g : set α → pfilter β} {h : pfilter β} {s : set α}
  (hs : s ∈ f) (hg : g s ≤ h) : f.lift g ≤ h :=
infi_le_of_le s $ infi_le_of_le hs $ hg

lemma le_lift {f : pfilter α} {g : set α → pfilter β} {h : pfilter β}
  (hh : ∀s∈f, h ≤ g s) : h ≤ f.lift g :=
le_infi $ assume s, le_infi $ assume hs, hh s hs

lemma lift_mono (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) : f₁.lift g₁ ≤ f₂.lift g₂ :=
infi_le_infi $ assume s, infi_le_infi2 $ assume hs, ⟨hf hs, hg s⟩

lemma lift_mono' (hg : ∀s∈f, g₁ s ≤ g₂ s) : f.lift g₁ ≤ f.lift g₂ :=
infi_le_infi $ assume s, infi_le_infi $ assume hs, hg s hs

lemma map_lift_eq {m : β → γ} (hg : monotone g) : map m (f.lift g) = f.lift (map m ∘ g) :=
have monotone (map m ∘ g),
  from monotone_comp hg monotone_map,
pfilter_eq $ set.ext $
  by simp only [mem_lift_sets, hg, @mem_lift_sets _ _ f _ this, exists_prop, forall_const, mem_map, iff_self, function.comp_app]

lemma comap_lift_eq {m : γ → β} (hg : monotone g) : comap m (f.lift g) = f.lift (comap m ∘ g) :=
have monotone (comap m ∘ g),
  from monotone_comp hg monotone_comap,
pfilter_eq $ set.ext begin
  simp only [hg, @mem_lift_sets _ _ f _ this, comap, mem_lift_sets, mem_set_of_eq, exists_prop,
    function.comp_apply],
  exact λ s,
   ⟨λ ⟨b, ⟨a, ha, hb⟩, hs⟩, ⟨a, ha, b, hb, hs⟩,
    λ ⟨a, ha, b, hb, hs⟩, ⟨b, ⟨a, ha, hb⟩, hs⟩⟩
end

theorem comap_lift_eq2 {m : β → α} {g : set β → pfilter γ} (hg : monotone g) :
  (comap m f).lift g = f.lift (g ∘ preimage m) :=
le_antisymm
  (le_infi $ assume s, le_infi $ assume hs,
    infi_le_of_le (preimage m s) $ infi_le _ ⟨s, hs, subset.refl _⟩)
  (le_infi $ assume s, le_infi $ assume ⟨s', hs', (h_sub : preimage m s' ⊆ s)⟩,
    infi_le_of_le s' $ infi_le_of_le hs' $ hg h_sub)

lemma map_lift_eq2 {g : set β → pfilter γ} {m : α → β} (hg : monotone g) :
  (map m f).lift g = f.lift (g ∘ image m) :=
le_antisymm
  (infi_le_infi2 $ assume s, ⟨image m s,
    infi_le_infi2 $ assume hs, ⟨
      f_of_superset hs $ assume a h, mem_image_of_mem _ h,
      le_refl _⟩⟩)
  (infi_le_infi2 $ assume t, ⟨preimage m t,
    infi_le_infi2 $ assume ht, ⟨ht,
      hg $ assume x, assume h : x ∈ m '' preimage m t,
        let ⟨y, hy, h_eq⟩ := h in
        show x ∈ t, from h_eq ▸ hy⟩⟩)

lemma lift_comm {g : pfilter β} {h : set α → set β → pfilter γ} :
  f.lift (λs, g.lift (h s)) = g.lift (λt, f.lift (λs, h s t)) :=
le_antisymm
  (le_infi $ assume i, le_infi $ assume hi, le_infi $ assume j, le_infi $ assume hj,
    infi_le_of_le j $ infi_le_of_le hj $ infi_le_of_le i $ infi_le _ hi)
  (le_infi $ assume i, le_infi $ assume hi, le_infi $ assume j, le_infi $ assume hj,
    infi_le_of_le j $ infi_le_of_le hj $ infi_le_of_le i $ infi_le _ hi)

lemma lift_assoc {h : set β → pfilter γ} (hg : monotone g)  :
  (f.lift g).lift h = f.lift (λs, (g s).lift h) :=
le_antisymm
  (le_infi $ assume s, le_infi $ assume hs, le_infi $ assume t, le_infi $ assume ht,
    infi_le_of_le t $ infi_le _ $ (mem_lift_sets hg).mpr ⟨_, hs, ht⟩)
  (le_infi $ assume t, le_infi $ assume ht,
    let ⟨s, hs, h'⟩ := (mem_lift_sets hg).mp ht in
    infi_le_of_le s $ infi_le_of_le hs $ infi_le_of_le t $ infi_le _ h')

lemma lift_lift_same_le_lift {g : set α → set α → pfilter β} :
  f.lift (λs, f.lift (g s)) ≤ f.lift (λs, g s s) :=
le_infi $ assume s, le_infi $ assume hs, infi_le_of_le s $ infi_le_of_le hs $ infi_le_of_le s $ infi_le _ hs

lemma lift_lift_same_eq_lift {g : set α → set α → pfilter β}
  (hg₁ : ∀s, monotone (λt, g s t)) (hg₂ : ∀t, monotone (λs, g s t)):
  f.lift (λs, f.lift (g s)) = f.lift (λs, g s s) :=
le_antisymm
  lift_lift_same_le_lift
  (le_infi $ assume s, le_infi $ assume hs, le_infi $ assume t, le_infi $ assume ht,
    infi_le_of_le (s ∩ t) $
    infi_le_of_le (inter_mem_sets hs ht) $
    calc g (s ∩ t) (s ∩ t) ≤ g s (s ∩ t) : hg₂ (s ∩ t) (inter_subset_left _ _)
      ... ≤ g s t                        : hg₁ s (inter_subset_right _ _))

lemma lift_principal {s : set α} (hg : monotone g) :
  (principal s).lift g = g s :=
le_antisymm
  (infi_le_of_le s $ infi_le _ $ subset.refl _)
  (le_infi $ assume t, le_infi $ assume hi, hg hi)

theorem monotone_lift [preorder γ] {f : γ → pfilter α} {g : γ → set α → pfilter β}
  (hf : monotone f) (hg : monotone g) : monotone (λc, (f c).lift (g c)) :=
assume a b h, lift_mono (hf h) (hg h)

lemma lift_neq_bot_iff (hm : monotone g) : (f.lift g ≠ ⊥) ↔ (∀s∈f, g s ≠ ⊥) :=
classical.by_cases
  (assume hn : nonempty β,
    calc f.lift g ≠ ⊥ ↔ (⨅s : { s // s ∈ f}, g s.val) ≠ ⊥ :
      by simp only [pfilter.lift, infi_subtype, iff_self, ne.def]
      ... ↔ (∀s:{ s // s ∈ f}, g s.val ≠ ⊥) :
        infi_neq_bot_iff_of_directed hn
          (assume ⟨a, ha⟩ ⟨b, hb⟩, ⟨⟨a ∩ b, inter_mem_sets ha hb⟩,
            hm $ inter_subset_left _ _, hm $ inter_subset_right _ _⟩)
      ... ↔ (∀s∈f, g s ≠ ⊥) : ⟨assume h s hs, h ⟨s, hs⟩, assume h ⟨s, hs⟩, h s hs⟩)
  (assume hn : ¬ nonempty β,
    have h₁ : f.lift g = ⊥, from pfilter_eq_bot_of_not_nonempty hn,
    have h₂ : ∀s, g s = ⊥, from assume s, pfilter_eq_bot_of_not_nonempty hn,
    calc (f.lift g ≠ ⊥) ↔ false : by simp only [h₁, iff_self, eq_self_iff_true, not_true, ne.def]
      ... ↔ (∀s∈f, false) : ⟨false.elim, assume h, h univ univ_mem_sets⟩
      ... ↔ (∀s∈f, g s ≠ ⊥) : by simp only [h₂, iff_self, eq_self_iff_true, not_true, ne.def])

@[simp] lemma lift_const {f : pfilter α} {g : pfilter β} : f.lift (λx, g) = g :=
le_antisymm (lift_le univ_mem_sets $ le_refl g) (le_lift $ assume s hs, le_refl g)

@[simp] lemma lift_inf {f : pfilter α} {g h : set α → pfilter β} :
  f.lift (λx, g x ⊓ h x) = f.lift g ⊓ f.lift h :=
by simp only [pfilter.lift, infi_inf_eq, eq_self_iff_true]

@[simp] lemma lift_principal2 {f : pfilter α} : f.lift principal = f :=
le_antisymm
  (assume s hs, mem_lift hs (mem_principal_self s))
  (le_infi $ assume s, le_infi $ assume hs, by simp only [hs, le_principal_iff])

lemma lift_infi {f : ι → pfilter α} {g : set α → pfilter β}
  (hι : nonempty ι) (hg : ∀{s t}, g s ⊓ g t = g (s ∩ t)) : (infi f).lift g = (⨅i, (f i).lift g) :=
le_antisymm
  (le_infi $ assume i, lift_mono (infi_le _ _) (le_refl _))
  (assume s,
    have g_mono : monotone g,
      from assume s t h, le_of_inf_eq $ eq.trans hg $ congr_arg g $ inter_eq_self_of_subset_left h,
    have ∀t∈(infi f), (⨅ (i : ι), pfilter.lift (f i) g) ≤ g t,
      from assume t ht, infi_sets_induct ht
        (let ⟨i⟩ := hι in infi_le_of_le i $ infi_le_of_le univ $ infi_le _ univ_mem_sets)
        (assume i s₁ s₂ hs₁ hs₂,
          @hg s₁ s₂ ▸ le_inf (infi_le_of_le i $ infi_le_of_le s₁ $ infi_le _ hs₁) hs₂)
        (assume s₁ s₂ hs₁ hs₂, le_trans hs₂ $ g_mono hs₁),
    begin
      rw [lift_sets_eq g_mono],
      simp only [mem_Union, exists_imp_distrib],
      exact assume t ht hs, this t ht hs
    end)

end lift

section lift'
/-- Specialize `lift` to functions `set α → set β`. This can be viewed as
  a generalization of `comap`. -/
protected def lift' (f : pfilter α) (h : set α → set β) :=
f.lift (principal ∘ h)

variables {f f₁ f₂ : pfilter α} {h h₁ h₂ : set α → set β}

lemma mem_lift' {t : set α} (ht : t ∈ f) : h t ∈ (f.lift' h) :=
le_principal_iff.mp $ show f.lift' h ≤ principal (h t),
  from infi_le_of_le t $ infi_le_of_le ht $ le_refl _

lemma mem_lift'_sets (hh : monotone h) {s : set β} : s ∈ (f.lift' h) ↔ (∃t∈f, h t ⊆ s) :=
have monotone (principal ∘ h),
  from assume a b h, principal_mono.mpr $ hh h,
by simp only [pfilter.lift', @mem_lift_sets α β f _ this, exists_prop, iff_self, mem_principal_sets, function.comp_app]

lemma lift'_le {f : pfilter α} {g : set α → set β} {h : pfilter β} {s : set α}
  (hs : s ∈ f) (hg : principal (g s) ≤ h) : f.lift' g ≤ h :=
lift_le hs hg

lemma lift'_mono (hf : f₁ ≤ f₂) (hh : h₁ ≤ h₂) : f₁.lift' h₁ ≤ f₂.lift' h₂ :=
lift_mono hf $ assume s, principal_mono.mpr $ hh s

lemma lift'_mono' (hh : ∀s∈f, h₁ s ⊆ h₂ s) : f.lift' h₁ ≤ f.lift' h₂ :=
infi_le_infi $ assume s, infi_le_infi $ assume hs, principal_mono.mpr $ hh s hs

lemma lift'_cong (hh : ∀s∈f, h₁ s = h₂ s) : f.lift' h₁ = f.lift' h₂ :=
le_antisymm (lift'_mono' $ assume s hs, le_of_eq $ hh s hs) (lift'_mono' $ assume s hs, le_of_eq $ (hh s hs).symm)

lemma map_lift'_eq {m : β → γ} (hh : monotone h) : map m (f.lift' h) = f.lift' (image m ∘ h) :=
calc map m (f.lift' h) = f.lift (map m ∘ principal ∘ h) :
    map_lift_eq $ monotone_comp hh monotone_principal
  ... = f.lift' (image m ∘ h) : by simp only [(∘), pfilter.lift', map_principal, eq_self_iff_true]

lemma map_lift'_eq2 {g : set β → set γ} {m : α → β} (hg : monotone g) :
  (map m f).lift' g = f.lift' (g ∘ image m) :=
map_lift_eq2 $ monotone_comp hg monotone_principal

theorem comap_lift'_eq {m : γ → β} (hh : monotone h) :
  comap m (f.lift' h) = f.lift' (preimage m ∘ h) :=
calc comap m (f.lift' h) = f.lift (comap m ∘ principal ∘ h) :
    comap_lift_eq $ monotone_comp hh monotone_principal
  ... = f.lift' (preimage m ∘ h) : by simp only [(∘), pfilter.lift', comap_principal, eq_self_iff_true]

theorem comap_lift'_eq2 {m : β → α} {g : set β → set γ} (hg : monotone g) :
  (comap m f).lift' g = f.lift' (g ∘ preimage m) :=
comap_lift_eq2 $ monotone_comp hg monotone_principal

lemma lift'_principal {s : set α} (hh : monotone h) :
  (principal s).lift' h = principal (h s) :=
lift_principal $ monotone_comp hh monotone_principal

lemma principal_le_lift' {t : set β} (hh : ∀s∈f, t ⊆ h s) :
  principal t ≤ f.lift' h :=
le_infi $ assume s, le_infi $ assume hs, principal_mono.mpr (hh s hs)

theorem monotone_lift' [preorder γ] {f : γ → pfilter α} {g : γ → set α → set β}
  (hf : monotone f) (hg : monotone g) : monotone (λc, (f c).lift' (g c)) :=
assume a b h, lift'_mono (hf h) (hg h)

lemma lift_lift'_assoc {g : set α → set β} {h : set β → pfilter γ}
  (hg : monotone g) (hh : monotone h) :
  (f.lift' g).lift h = f.lift (λs, h (g s)) :=
calc (f.lift' g).lift h = f.lift (λs, (principal (g s)).lift h) :
    lift_assoc (monotone_comp hg monotone_principal)
  ... = f.lift (λs, h (g s)) : by simp only [lift_principal, hh, eq_self_iff_true]

lemma lift'_lift'_assoc {g : set α → set β} {h : set β → set γ}
  (hg : monotone g) (hh : monotone h) :
  (f.lift' g).lift' h = f.lift' (λs, h (g s)) :=
lift_lift'_assoc hg (monotone_comp hh monotone_principal)

lemma lift'_lift_assoc {g : set α → pfilter β} {h : set β → set γ}
  (hg : monotone g) : (f.lift g).lift' h = f.lift (λs, (g s).lift' h) :=
lift_assoc hg

lemma lift_lift'_same_le_lift' {g : set α → set α → set β} :
  f.lift (λs, f.lift' (g s)) ≤ f.lift' (λs, g s s) :=
lift_lift_same_le_lift

lemma lift_lift'_same_eq_lift' {g : set α → set α → set β}
  (hg₁ : ∀s, monotone (λt, g s t)) (hg₂ : ∀t, monotone (λs, g s t)):
  f.lift (λs, f.lift' (g s)) = f.lift' (λs, g s s) :=
lift_lift_same_eq_lift
  (assume s, monotone_comp monotone_id $ monotone_comp (hg₁ s) monotone_principal)
  (assume t, monotone_comp (hg₂ t) monotone_principal)

lemma lift'_inf_principal_eq {h : set α → set β} {s : set β} :
  f.lift' h ⊓ principal s = f.lift' (λt, h t ∩ s) :=
le_antisymm
  (le_infi $ assume t, le_infi $ assume ht,
    calc pfilter.lift' f h ⊓ principal s ≤ principal (h t) ⊓ principal s :
        inf_le_inf (infi_le_of_le t $ infi_le _ ht) (le_refl _)
      ... = _ : by simp only [principal_eq_iff_eq, inf_principal, eq_self_iff_true, function.comp_app])
  (le_inf
    (le_infi $ assume t, le_infi $ assume ht,
      infi_le_of_le t $ infi_le_of_le ht $
      by simp only [le_principal_iff, inter_subset_left, mem_principal_sets, function.comp_app]; exact inter_subset_right _ _)
    (infi_le_of_le univ $ infi_le_of_le univ_mem_sets $
    by simp only [le_principal_iff, inter_subset_right, mem_principal_sets, function.comp_app]; exact inter_subset_left _ _))

lemma lift'_neq_bot_iff (hh : monotone h) : (f.lift' h ≠ ⊥) ↔ (∀s∈f, h s ≠ ∅) :=
calc (f.lift' h ≠ ⊥) ↔ (∀s∈f, principal (h s) ≠ ⊥) :
    lift_neq_bot_iff (monotone_comp hh monotone_principal)
  ... ↔ (∀s∈f, h s ≠ ∅) : by simp only [principal_eq_bot_iff, iff_self, ne.def, principal_eq_bot_iff]

@[simp] lemma lift'_id {f : pfilter α} : f.lift' id = f :=
lift_principal2

lemma le_lift' {f : pfilter α} {h : set α → set β} {g : pfilter β}
  (h_le : ∀s∈f, h s ∈ g) : g ≤ f.lift' h :=
le_infi $ assume s, le_infi $ assume hs, by simp only [h_le, le_principal_iff, function.comp_app]; exact h_le s hs

lemma lift_infi' {f : ι → pfilter α} {g : set α → pfilter β}
  (hι : nonempty ι) (hf : directed (≥) f) (hg : monotone g) : (infi f).lift g = (⨅i, (f i).lift g) :=
le_antisymm
  (le_infi $ assume i, lift_mono (infi_le _ _) (le_refl _))
  (assume s,
  begin
    rw [lift_sets_eq hg],
    simp only [mem_Union, exists_imp_distrib, infi_sets_eq hf hι],
    exact assume t i ht hs, mem_infi_sets i $ mem_lift ht hs
  end)

lemma lift'_infi {f : ι → pfilter α} {g : set α → set β}
  (hι : nonempty ι) (hg : ∀{s t}, g s ∩ g t = g (s ∩ t)) : (infi f).lift' g = (⨅i, (f i).lift' g) :=
lift_infi hι $ by simp only [principal_eq_iff_eq, inf_principal, function.comp_app]; apply assume s t, hg

theorem comap_eq_lift' {f : pfilter β} {m : α → β} :
  comap m f = f.lift' (preimage m) :=
pfilter_eq $ set.ext $ by simp only [mem_lift'_sets, monotone_preimage, comap, exists_prop, forall_const, iff_self, mem_set_of_eq]

end lift'

section prod
variables {s : set α} {t : set β} {f : pfilter α} {g : pfilter β}
/- The product pfilter cannot be defined using the monad structure on pfilters. For example:

  F := do {x <- seq, y <- top, return (x, y)}
  hence:
    s ∈ F  <->  ∃n, [n..∞] × univ ⊆ s

  G := do {y <- top, x <- seq, return (x, y)}
  hence:
    s ∈ G  <->  ∀i:ℕ, ∃n, [n..∞] × {i} ⊆ s

  Now ⋃i, [i..∞] × {i}  is in G but not in F.

  As product pfilter we want to have F as result.
-/

/-- Product of pfilters. This is the pfilter generated by cartesian products
  of elements of the component pfilters. -/
protected def prod (f : pfilter α) (g : pfilter β) : pfilter (α × β) :=
f.comap prod.fst ⊓ g.comap prod.snd

lemma prod_mem_prod {s : set α} {t : set β} {f : pfilter α} {g : pfilter β}
  (hs : s ∈ f) (ht : t ∈ g) : set.prod s t ∈ (pfilter.prod f g) :=
inter_mem_inf_sets (preimage_mem_comap hs) (preimage_mem_comap ht)

lemma mem_prod_iff {s : set (α×β)} {f : pfilter α} {g : pfilter β} :
  s ∈ (pfilter.prod f g) ↔ (∃t₁∈f, ∃t₂∈g, set.prod t₁ t₂ ⊆ s) :=
begin
  simp only [pfilter.prod],
  split,
  exact assume ⟨t₁, ⟨s₁, hs₁, hts₁⟩, t₂, ⟨s₂, hs₂, hts₂⟩, h⟩,
    ⟨s₁, hs₁, s₂, hs₂, subset.trans (inter_subset_inter hts₁ hts₂) h⟩,
  exact assume ⟨t₁, ht₁, t₂, ht₂, h⟩,
    ⟨prod.fst ⁻¹' t₁, ⟨t₁, ht₁, subset.refl _⟩, prod.snd ⁻¹' t₂, ⟨t₂, ht₂, subset.refl _⟩, h⟩
end

lemma tendsto_fst {f : pfilter α} {g : pfilter β} : tendsto prod.fst (pfilter.prod f g) f :=
tendsto_inf_left tendsto_comap

lemma tendsto_snd {f : pfilter α} {g : pfilter β} : tendsto prod.snd (pfilter.prod f g) g :=
tendsto_inf_right tendsto_comap

lemma tendsto.prod_mk {f : pfilter α} {g : pfilter β} {h : pfilter γ} {m₁ : α → β} {m₂ : α → γ}
  (h₁ : tendsto m₁ f g) (h₂ : tendsto m₂ f h) : tendsto (λx, (m₁ x, m₂ x)) f (pfilter.prod g h) :=
tendsto_inf.2 ⟨tendsto_comap_iff.2 h₁, tendsto_comap_iff.2 h₂⟩

lemma prod_infi_left {f : ι → pfilter α} {g : pfilter β} (i : ι) :
  pfilter.prod (⨅i, f i) g = (⨅i, pfilter.prod (f i) g) :=
by rw [pfilter.prod, comap_infi, infi_inf i]; simp only [pfilter.prod, eq_self_iff_true]

lemma prod_infi_right {f : pfilter α} {g : ι → pfilter β} (i : ι) :
  pfilter.prod f (⨅i, g i) = (⨅i, pfilter.prod f (g i)) :=
by rw [pfilter.prod, comap_infi, inf_infi i]; simp only [pfilter.prod, eq_self_iff_true]

lemma prod_mono {f₁ f₂ : pfilter α} {g₁ g₂ : pfilter β} (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) :
  pfilter.prod f₁ g₁ ≤ pfilter.prod f₂ g₂ :=
inf_le_inf (comap_mono hf) (comap_mono hg)

lemma prod_comap_comap_eq {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
  {f₁ : pfilter α₁} {f₂ : pfilter α₂} {m₁ : β₁ → α₁} {m₂ : β₂ → α₂} :
  pfilter.prod (comap m₁ f₁) (comap m₂ f₂) = comap (λp:β₁×β₂, (m₁ p.1, m₂ p.2)) (pfilter.prod f₁ f₂) :=
by simp only [pfilter.prod, comap_comap_comp, eq_self_iff_true, comap_inf]

lemma prod_comm' : pfilter.prod f g = comap (prod.swap) (pfilter.prod g f) :=
by simp only [pfilter.prod, comap_comap_comp, (∘), inf_comm, prod.fst_swap,
  eq_self_iff_true, prod.snd_swap, comap_inf]

lemma prod_comm : pfilter.prod f g = map (λp:β×α, (p.2, p.1)) (pfilter.prod g f) :=
by rw [prod_comm', ← map_swap_eq_comap_swap]; refl

lemma prod_map_map_eq {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
  {f₁ : pfilter α₁} {f₂ : pfilter α₂} {m₁ : α₁ → β₁} {m₂ : α₂ → β₂} :
  pfilter.prod (map m₁ f₁) (map m₂ f₂) = map (λp:α₁×α₂, (m₁ p.1, m₂ p.2)) (pfilter.prod f₁ f₂) :=
le_antisymm
  (assume s hs,
    let ⟨s₁, hs₁, s₂, hs₂, h⟩ := mem_prod_iff.mp hs in
    pfilter_of_superset _ (prod_mem_prod (image_mem_map hs₁) (image_mem_map hs₂)) $
      calc set.prod (m₁ '' s₁) (m₂ '' s₂) = (λp:α₁×α₂, (m₁ p.1, m₂ p.2)) '' set.prod s₁ s₂ :
          set.prod_image_image_eq
        ... ⊆ _ : by rwa [image_subset_iff])
  ((tendsto_fst.comp (le_refl _)).prod_mk (tendsto_snd.comp (le_refl _)))

lemma map_prod (m : α × β → γ) (f : pfilter α) (g : pfilter β) :
  map m (f.prod g) = (f.map (λa b, m (a, b))).seq g :=
begin
  simp [pfilter.ext_iff, mem_prod_iff, mem_map_seq_iff],
  assume s,
  split,
  exact assume ⟨t, ht, s, hs, h⟩, ⟨s, hs, t, ht, assume x hx y hy, @h ⟨x, y⟩ ⟨hx, hy⟩⟩,
  exact assume ⟨s, hs, t, ht, h⟩, ⟨t, ht, s, hs, assume ⟨x, y⟩ ⟨hx, hy⟩, h x hx y hy⟩
end

lemma prod_eq {f : pfilter α} {g : pfilter β} : f.prod g = (f.map prod.mk).seq g  :=
have h : _ := map_prod id f g, by rwa [map_id] at h

lemma prod_inf_prod {f₁ f₂ : pfilter α} {g₁ g₂ : pfilter β} :
  pfilter.prod f₁ g₁ ⊓ pfilter.prod f₂ g₂ = pfilter.prod (f₁ ⊓ f₂) (g₁ ⊓ g₂) :=
by simp only [pfilter.prod, comap_inf, inf_comm, inf_assoc, lattice.inf_left_comm]

@[simp] lemma prod_bot1 {f : pfilter α} : pfilter.prod f (⊥ : pfilter β) = ⊥ := by simp [pfilter.prod]
@[simp] lemma prod_bot2 {g : pfilter β} : pfilter.prod (⊥ : pfilter α) g = ⊥ := by simp [pfilter.prod]

@[simp] lemma prod_principal_principal {s : set α} {t : set β} :
  pfilter.prod (principal s) (principal t) = principal (set.prod s t) :=
by simp only [pfilter.prod, comap_principal, principal_eq_iff_eq, comap_principal, inf_principal]; refl

@[simp] lemma prod_pure_pure {a : α} {b : β} : pfilter.prod (pure a) (pure b) = pure (a, b) :=
by simp

lemma prod_def {f : pfilter α} {g : pfilter β} : f.prod g = (f.lift $ λs, g.lift' $ set.prod s) :=
have ∀(s:set α) (t : set β),
    principal (set.prod s t) = (principal s).comap prod.fst ⊓ (principal t).comap prod.snd,
  by simp only [principal_eq_iff_eq, comap_principal, inf_principal]; intros; refl,
begin
  simp only [pfilter.lift', function.comp, this, -comap_principal, lift_inf, lift_const, lift_inf],
  rw [← comap_lift_eq monotone_principal, ← comap_lift_eq monotone_principal],
  simp only [pfilter.prod, lift_principal2, eq_self_iff_true]
end

lemma prod_same_eq : pfilter.prod f f = f.lift' (λt, set.prod t t) :=
by rw [prod_def];
from lift_lift'_same_eq_lift'
  (assume s, set.monotone_prod monotone_const monotone_id)
  (assume t, set.monotone_prod monotone_id monotone_const)

lemma mem_prod_same_iff {s : set (α×α)} :
  s ∈ (pfilter.prod f f) ↔ (∃t∈f, set.prod t t ⊆ s) :=
by rw [prod_same_eq, mem_lift'_sets]; exact set.monotone_prod monotone_id monotone_id

lemma prod_lift_lift {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
  {f₁ : pfilter α₁} {f₂ : pfilter α₂} {g₁ : set α₁ → pfilter β₁} {g₂ : set α₂ → pfilter β₂}
  (hg₁ : monotone g₁) (hg₂ : monotone g₂) :
  pfilter.prod (f₁.lift g₁) (f₂.lift g₂) = f₁.lift (λs, f₂.lift (λt, pfilter.prod (g₁ s) (g₂ t))) :=
begin
  simp only [prod_def],
  rw [lift_assoc],
  apply congr_arg, funext x,
  rw [lift_comm],
  apply congr_arg, funext y,
  rw [lift'_lift_assoc],
  exact hg₂,
  exact hg₁
end

lemma prod_lift'_lift' {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
  {f₁ : pfilter α₁} {f₂ : pfilter α₂} {g₁ : set α₁ → set β₁} {g₂ : set α₂ → set β₂}
  (hg₁ : monotone g₁) (hg₂ : monotone g₂) :
  pfilter.prod (f₁.lift' g₁) (f₂.lift' g₂) = f₁.lift (λs, f₂.lift' (λt, set.prod (g₁ s) (g₂ t))) :=
begin
  rw [prod_def, lift_lift'_assoc],
  apply congr_arg, funext x,
  rw [lift'_lift'_assoc],
  exact hg₂,
  exact set.monotone_prod monotone_const monotone_id,
  exact hg₁,
  exact (monotone_lift' monotone_const $ monotone_lam $
    assume x, set.monotone_prod monotone_id monotone_const)
end

lemma prod_neq_bot {f : pfilter α} {g : pfilter β} : pfilter.prod f g ≠ ⊥ ↔ (f ≠ ⊥ ∧ g ≠ ⊥) :=
calc pfilter.prod f g ≠ ⊥ ↔ (∀s∈f, g.lift' (set.prod s) ≠ ⊥) :
  begin
    rw [prod_def, lift_neq_bot_iff],
    exact (monotone_lift' monotone_const $ monotone_lam $ assume s, set.monotone_prod monotone_id monotone_const)
  end
  ... ↔ (∀s∈f, ∀t∈g, s ≠ ∅ ∧ t ≠ ∅) :
  begin
    apply forall_congr, intro s,
    apply forall_congr, intro hs,
    rw [lift'_neq_bot_iff],
    apply forall_congr, intro t,
    apply forall_congr, intro ht,
    rw [set.prod_neq_empty_iff],
    exact set.monotone_prod monotone_const monotone_id
  end
  ... ↔ (∀s∈f, s ≠ ∅) ∧ (∀t∈g, t ≠ ∅) :
    ⟨assume h, ⟨assume s hs, (h s hs univ univ_mem_sets).left,
        assume t ht, (h univ univ_mem_sets t ht).right⟩,
      assume ⟨h₁, h₂⟩ s hs t ht, ⟨h₁ s hs, h₂ t ht⟩⟩
  ... ↔ _ : by simp only [forall_sets_neq_empty_iff_neq_bot]

lemma tendsto_prod_iff {f : α × β → γ} {x : pfilter α} {y : pfilter β} {z : pfilter γ} :
  pfilter.tendsto f (pfilter.prod x y) z ↔
  ∀ W ∈ z, ∃ U ∈ x,  ∃ V ∈ y, ∀ x y, x ∈ U → y ∈ V → f (x, y) ∈ W :=
by simp only [tendsto_def, mem_prod_iff, prod_sub_preimage_iff, exists_prop, iff_self]

lemma tendsto_prod_self_iff {f : α × α → β} {x : pfilter α} {y : pfilter β} :
  pfilter.tendsto f (pfilter.prod x x) y ↔
  ∀ W ∈ y, ∃ U ∈ x, ∀ (x x' : α), x ∈ U → x' ∈ U → f (x, x') ∈ W :=
by simp only [tendsto_def, mem_prod_same_iff, prod_sub_preimage_iff, exists_prop, iff_self]

end prod

/- at_top and at_bot -/

/-- `at_top` is the pfilter representing the limit `→ ∞` on an ordered set.
  It is generated by the collection of up-sets `{b | a ≤ b}`.
  (The preorder need not have a top element for this to be well defined,
  and indeed is trivial when a top element exists.) -/
def at_top [preorder α] : pfilter α := ⨅ a, principal {b | a ≤ b}

/-- `at_bot` is the pfilter representing the limit `→ -∞` on an ordered set.
  It is generated by the collection of down-sets `{b | b ≤ a}`.
  (The preorder need not have a bottom element for this to be well defined,
  and indeed is trivial when a bottom element exists.) -/
def at_bot [preorder α] : pfilter α := ⨅ a, principal {b | b ≤ a}

lemma mem_at_top [preorder α] (a : α) : {b : α | a ≤ b} ∈ (@at_top α _) :=
mem_infi_sets a $ subset.refl _

@[simp] lemma at_top_ne_bot [inhabited α] [semilattice_sup α] : (at_top : pfilter α) ≠ ⊥ :=
infi_neq_bot_of_directed (by apply_instance)
  (assume a b, ⟨a ⊔ b, by simp only [ge, le_principal_iff, forall_const, set_of_subset_set_of,
    mem_principal_sets, and_self, sup_le_iff, forall_true_iff] {contextual := tt}⟩)
  (assume a, by simp only [principal_eq_bot_iff, ne.def, principal_eq_bot_iff]; exact ne_empty_of_mem (le_refl a))

@[simp] lemma mem_at_top_sets [inhabited α] [semilattice_sup α] {s : set α} :
  s ∈ (at_top : pfilter α) ↔ ∃a:α, ∀b≥a, b ∈ s :=
iff.intro
  (assume h, infi_sets_induct h ⟨default α, by simp only [forall_const, mem_univ, forall_true_iff]⟩
    (assume a s₁ s₂ ha ⟨b, hb⟩, ⟨a ⊔ b,
      assume c hc, ⟨ha $ le_trans le_sup_left hc, hb _ $ le_trans le_sup_right hc⟩⟩)
    (assume s₁ s₂ h ⟨a, ha⟩, ⟨a, assume b hb, h $ ha _ hb⟩))
  (assume ⟨a, h⟩, mem_infi_sets a $ assume x, h x)

lemma map_at_top_eq [inhabited α] [semilattice_sup α] {f : α → β} :
  at_top.map f = (⨅a, principal $ f '' {a' | a ≤ a'}) :=
calc map f (⨅a, principal {a' | a ≤ a'}) = (⨅a, map f $ principal {a' | a ≤ a'}) :
    map_infi_eq (assume a b, ⟨a ⊔ b, by simp only [ge, le_principal_iff, forall_const, set_of_subset_set_of,
      mem_principal_sets, and_self, sup_le_iff, forall_true_iff] {contextual := tt}⟩) ⟨default α⟩
  ... = (⨅a, principal $ f '' {a' | a ≤ a'}) : by simp only [map_principal, eq_self_iff_true]

lemma tendsto_at_top {α β} [partial_order β] (m : α → β) (f : pfilter α) :
  tendsto m f at_top ↔ (∀b, {a | b ≤ m a} ∈ f) :=
by simp only [at_top, tendsto_infi, tendsto_principal]; refl

lemma tendsto_finset_image_at_top_at_top {i : β → γ} {j : γ → β} (h : ∀x, j (i x) = x) :
  tendsto (λs:finset γ, s.image j) at_top at_top :=
tendsto_infi.2 $ assume s, tendsto_infi' (s.image i) $ tendsto_principal_principal.2 $
  assume t (ht : s.image i ⊆ t),
  calc s = (s.image i).image j :
      by simp only [finset.image_image, (∘), h]; exact finset.image_id.symm
    ... ⊆  t.image j : finset.image_subset_image ht

/- ultrapfilter -/

section ultrapfilter
open zorn

variables {f g : pfilter α}

/-- An ultrapfilter is a minimal (maximal in the set order) proper pfilter. -/
def is_ultrapfilter (f : pfilter α) := f ≠ ⊥ ∧ ∀g, g ≠ ⊥ → g ≤ f → f ≤ g

lemma ultrapfilter_unique (hg : is_ultrapfilter g) (hf : f ≠ ⊥) (h : f ≤ g) : f = g :=
le_antisymm h (hg.right _ hf h)

lemma le_of_ultrapfilter {g : pfilter α} (hf : is_ultrapfilter f) (h : f ⊓ g ≠ ⊥) :
  f ≤ g :=
le_of_inf_eq $ ultrapfilter_unique hf h inf_le_left

/-- Equivalent characterization of ultrapfilters:
  A pfilter f is an ultrapfilter if and only if for each set s,
  -s belongs to f if and only if s does not belong to f. -/
lemma ultrapfilter_iff_compl_mem_iff_not_mem :
  is_ultrapfilter f ↔ (∀ s, -s ∈ f ↔ s ∉ f) :=
⟨assume hf s,
   ⟨assume hns hs,
      hf.1 $ empty_in_sets_eq_bot.mp $ by convert f.inter_sets hs hns; rw [inter_compl_self],
    assume hs,
      have f ≤ principal (-s), from
        le_of_ultrapfilter hf $ assume h, hs $ mem_sets_of_neq_bot $
          by simp only [h, eq_self_iff_true, lattice.neg_neg],
      by simp only [le_principal_iff] at this; assumption⟩,
 assume hf,
   ⟨mt empty_in_sets_eq_bot.mpr ((hf ∅).mp (by convert f.univ_sets; rw [compl_empty])),
    assume g hg g_le s hs, classical.by_contradiction $ mt (hf s).mpr $
      assume : - s ∈ f,
        have s ∩ -s ∈ g, from inter_mem_sets hs (g_le this),
        by simp only [empty_in_sets_eq_bot, hg, inter_compl_self] at this; contradiction⟩⟩

lemma mem_or_compl_mem_of_ultrapfilter (hf : is_ultrapfilter f) (s : set α) :
  s ∈ f ∨ - s ∈ f :=
classical.or_iff_not_imp_left.2 (ultrapfilter_iff_compl_mem_iff_not_mem.mp hf s).mpr

lemma mem_or_mem_of_ultrapfilter {s t : set α} (hf : is_ultrapfilter f) (h : s ∪ t ∈ f) :
  s ∈ f ∨ t ∈ f :=
(mem_or_compl_mem_of_ultrapfilter hf s).imp_right
  (assume : -s ∈ f, by pfilter_upwards [this, h] assume x hnx hx, hx.resolve_left hnx)

lemma mem_of_finite_sUnion_ultrapfilter {s : set (set α)} (hf : is_ultrapfilter f) (hs : finite s)
  : ⋃₀ s ∈ f → ∃t∈s, t ∈ f :=
finite.induction_on hs (by simp only [empty_in_sets_eq_bot, hf.left, mem_empty_eq, sUnion_empty,
  forall_prop_of_false, exists_false, not_false_iff, exists_prop_of_false]) $
λ t s' ht' hs' ih, by simp only [exists_prop, mem_insert_iff, set.sUnion_insert]; exact
assume h, (mem_or_mem_of_ultrapfilter hf h).elim
  (assume : t ∈ f, ⟨t, or.inl rfl, this⟩)
  (assume h, let ⟨t, hts', ht⟩ := ih h in ⟨t, or.inr hts', ht⟩)

lemma mem_of_finite_Union_ultrapfilter {is : set β} {s : β → set α}
  (hf : is_ultrapfilter f) (his : finite is) (h : (⋃i∈is, s i) ∈ f) : ∃i∈is, s i ∈ f :=
have his : finite (image s is), from finite_image s his,
have h : (⋃₀ image s is) ∈ f, from by simp only [sUnion_image, set.sUnion_image]; assumption,
let ⟨t, ⟨i, hi, h_eq⟩, (ht : t ∈ f)⟩ := mem_of_finite_sUnion_ultrapfilter hf his h in
⟨i, hi, h_eq.symm ▸ ht⟩

lemma ultrapfilter_map {f : pfilter α} {m : α → β} (h : is_ultrapfilter f) : is_ultrapfilter (map m f) :=
by rw ultrapfilter_iff_compl_mem_iff_not_mem at ⊢ h; exact assume s, h (m ⁻¹' s)

lemma ultrapfilter_pure {a : α} : is_ultrapfilter (pure a) :=
begin
  rw ultrapfilter_iff_compl_mem_iff_not_mem, intro s,
  rw [mem_pure_sets, mem_pure_sets], exact iff.rfl
end

lemma ultrapfilter_bind {f : pfilter α} (hf : is_ultrapfilter f) {m : α → pfilter β}
  (hm : ∀ a, is_ultrapfilter (m a)) : is_ultrapfilter (f.bind m) :=
begin
  simp only [ultrapfilter_iff_compl_mem_iff_not_mem] at ⊢ hf hm, intro s,
  dsimp [bind, join, map],
  simp only [hm], apply hf
end

/-- The ultrapfilter lemma: Any proper pfilter is contained in an ultrapfilter. -/
lemma exists_ultrapfilter (h : f ≠ ⊥) : ∃u, u ≤ f ∧ is_ultrapfilter u :=
let
  τ                := {f' // f' ≠ ⊥ ∧ f' ≤ f},
  r : τ → τ → Prop := λt₁ t₂, t₂.val ≤ t₁.val,
  ⟨a, ha⟩          := inhabited_of_mem_sets h univ_mem_sets,
  top : τ          := ⟨f, h, le_refl f⟩,
  sup : Π(c:set τ), chain r c → τ :=
    λc hc, ⟨⨅a:{a:τ // a ∈ insert top c}, a.val.val,
      infi_neq_bot_of_directed ⟨a⟩
        (directed_of_chain $ chain_insert hc $ assume ⟨b, _, hb⟩ _ _, or.inl hb)
        (assume ⟨⟨a, ha, _⟩, _⟩, ha),
      infi_le_of_le ⟨top, mem_insert _ _⟩ (le_refl _)⟩
in
have ∀c (hc: chain r c) a (ha : a ∈ c), r a (sup c hc),
  from assume c hc a ha, infi_le_of_le ⟨a, mem_insert_of_mem _ ha⟩ (le_refl _),
have (∃ (u : τ), ∀ (a : τ), r u a → r a u),
  from zorn (assume c hc, ⟨sup c hc, this c hc⟩) (assume f₁ f₂ f₃ h₁ h₂, le_trans h₂ h₁),
let ⟨uτ, hmin⟩ := this in
⟨uτ.val, uτ.property.right, uτ.property.left, assume g hg₁ hg₂,
  hmin ⟨g, hg₁, le_trans hg₂ uτ.property.right⟩ hg₂⟩

/-- Construct an ultrapfilter extending a given pfilter.
  The ultrapfilter lemma is the assertion that such a pfilter exists;
  we use the axiom of choice to pick one. -/
noncomputable def ultrapfilter_of (f : pfilter α) : pfilter α :=
if h : f = ⊥ then ⊥ else classical.epsilon (λu, u ≤ f ∧ is_ultrapfilter u)

lemma ultrapfilter_of_spec (h : f ≠ ⊥) : ultrapfilter_of f ≤ f ∧ is_ultrapfilter (ultrapfilter_of f) :=
begin
  have h' := classical.epsilon_spec (exists_ultrapfilter h),
  simp only [ultrapfilter_of, dif_neg, h, dif_neg, not_false_iff],
  simp only at h',
  assumption
end

lemma ultrapfilter_of_le : ultrapfilter_of f ≤ f :=
if h : f = ⊥ then by simp only [ultrapfilter_of, dif_pos, h, dif_pos, eq_self_iff_true, le_bot_iff]; exact le_refl _
  else (ultrapfilter_of_spec h).left

lemma ultrapfilter_ultrapfilter_of (h : f ≠ ⊥) : is_ultrapfilter (ultrapfilter_of f) :=
(ultrapfilter_of_spec h).right

lemma ultrapfilter_of_ultrapfilter (h : is_ultrapfilter f) : ultrapfilter_of f = f :=
ultrapfilter_unique h (ultrapfilter_ultrapfilter_of h.left).left ultrapfilter_of_le

/-- A pfilter equals the intersection of all the ultrapfilters which contain it. -/
lemma sup_of_ultrapfilters (f : pfilter α) : f = ⨆ (g) (u : is_ultrapfilter g) (H : g ≤ f), g :=
begin
  refine le_antisymm _ (supr_le $ λ g, supr_le $ λ u, supr_le $ λ H, H),
  intros s hs,
  -- If s ∉ f, we'll apply the ultrapfilter lemma to the restriction of f to -s.
  by_contradiction hs',
  let j : (-s) → α := subtype.val,
  have j_inv_s : j ⁻¹' s = ∅, by
    erw [←preimage_inter_range, subtype_val_range, inter_compl_self, preimage_empty],
  let f' := comap j f,
  have : f' ≠ ⊥,
  { apply mt empty_in_sets_eq_bot.mpr,
    rintro ⟨t, htf, ht⟩,
    suffices : t ⊆ s, from absurd (f_of_superset htf this) hs',
    rw [subset_empty_iff] at ht,
    have : j '' (j ⁻¹' t) = ∅, by rw [ht, image_empty],
    erw [image_preimage_eq_inter_range, subtype_val_range, ←subset_compl_iff_disjoint,
      set.compl_compl] at this,
    exact this },
  rcases exists_ultrapfilter this with ⟨g', g'f', u'⟩,
  simp only [supr_sets_eq, mem_Inter] at hs,
  have := hs (g'.map subtype.val) (ultrapfilter_map u') (map_le_iff_le_comap.mpr g'f'),
  rw [←le_principal_iff, map_le_iff_le_comap, comap_principal, j_inv_s, principal_empty,
    le_bot_iff] at this,
  exact absurd this u'.1
end

/-- The `tendsto` relation can be checked on ultrapfilters. -/
lemma tendsto_iff_ultrapfilter (f : α → β) (l₁ : pfilter α) (l₂ : pfilter β) :
  tendsto f l₁ l₂ ↔ ∀ g, is_ultrapfilter g → g ≤ l₁ → g.map f ≤ l₂ :=
⟨assume h g u gx, le_trans (map_mono gx) h,
 assume h, by rw [sup_of_ultrapfilters l₁]; simpa only [tendsto, map_supr, supr_le_iff]⟩

/- The ultrapfilter monad. The monad structure on ultrapfilters is the
  restriction of the one on pfilters. -/

def ultrapfilter (α : Type u) : Type u := {f : pfilter α // is_ultrapfilter f}

def ultrapfilter.map (m : α → β) (u : ultrapfilter α) : ultrapfilter β :=
⟨u.val.map m, ultrapfilter_map u.property⟩

def ultrapfilter.pure (x : α) : ultrapfilter α := ⟨pure x, ultrapfilter_pure⟩

def ultrapfilter.bind (u : ultrapfilter α) (m : α → ultrapfilter β) : ultrapfilter β :=
⟨u.val.bind (λ a, (m a).val), ultrapfilter_bind u.property (λ a, (m a).property)⟩

instance ultrapfilter.has_pure : has_pure ultrapfilter := ⟨@ultrapfilter.pure⟩
instance ultrapfilter.has_bind : has_bind ultrapfilter := ⟨@ultrapfilter.bind⟩
instance ultrapfilter.functor : functor ultrapfilter := { map := @ultrapfilter.map }
instance ultrapfilter.monad : monad ultrapfilter := { map := @ultrapfilter.map }

section

local attribute [instance] pfilter.monad pfilter.is_lawful_monad

instance ultrapfilter.is_lawful_monad : is_lawful_monad ultrapfilter :=
{ id_map := assume α f, subtype.eq (id_map f.val),
  pure_bind := assume α β a f, subtype.eq (pure_bind a (subtype.val ∘ f)),
  bind_assoc := assume α β γ f m₁ m₂, subtype.eq (pfilter_eq rfl),
  bind_pure_comp_eq_map := assume α β f x, subtype.eq (bind_pure_comp_eq_map _ f x.val) }

end

lemma ultrapfilter.eq_iff_val_le_val {u v : ultrapfilter α} : u = v ↔ u.val ≤ v.val :=
⟨assume h, by rw h; exact le_refl _,
 assume h, by rw subtype.ext; apply ultrapfilter_unique v.property u.property.1 h⟩

lemma exists_ultrapfilter_iff (f : pfilter α) : (∃ (u : ultrapfilter α), u.val ≤ f) ↔ f ≠ ⊥ :=
⟨assume ⟨u, uf⟩, lattice.neq_bot_of_le_neq_bot u.property.1 uf,
 assume h, let ⟨u, uf, hu⟩ := exists_ultrapfilter h in ⟨⟨u, hu⟩, uf⟩⟩

end ultrapfilter

end pfilter

namespace pfilter
variables {α β γ : Type u} {f : β → pfilter α} {s : γ → set α}
open list

lemma mem_traverse_sets :
  ∀(fs : list β) (us : list γ),
    forall₂ (λb c, s c ∈ (f b)) fs us → traverse s us ∈ (traverse f fs)
| []      []      forall₂.nil         := mem_pure_sets.2 $ mem_singleton _
| (f::fs) (u::us) (forall₂.cons h hs) := seq_mem_seq_sets (image_mem_map h) (mem_traverse_sets fs us hs)

lemma mem_traverse_sets_iff (fs : list β) (t : set (list α)) :
  t ∈ (traverse f fs) ↔
    (∃us:list (set α), forall₂ (λb (s : set α), s ∈ (f b)) fs us ∧ sequence us ⊆ t) :=
begin
  split,
  { induction fs generalizing t,
    case nil { simp only [sequence, pure_def, imp_self, forall₂_nil_left_iff, pure_def,
      exists_eq_left, mem_principal_sets, set.pure_def, singleton_subset_iff, traverse_nil] },
    case cons : b fs ih t {
      assume ht,
      rcases mem_seq_sets_iff.1 ht with ⟨u, hu, v, hv, ht⟩,
      rcases mem_map_sets_iff.1 hu with ⟨w, hw, hwu⟩,
      rcases ih v hv with ⟨us, hus, hu⟩,
      exact ⟨w :: us, forall₂.cons hw hus, subset.trans (set.seq_mono hwu hu) ht⟩ } },
  { rintros ⟨us, hus, hs⟩,
    exact mem_sets_of_superset (mem_traverse_sets _ _ hus) hs }
end

lemma sequence_mono :
  ∀(as bs : list (pfilter α)), forall₂ (≤) as bs → sequence as ≤ sequence bs
| []      []      forall₂.nil         := le_refl _
| (a::as) (b::bs) (forall₂.cons h hs) := seq_mono (map_mono h) (sequence_mono as bs hs)

end pfilter
