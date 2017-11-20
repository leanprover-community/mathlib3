/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Theory of filters on sets.
-/
import order.complete_lattice order.galois_connection data.set data.finset order.zorn
open lattice set

universes u v w x y

open set classical
local attribute [instance] decidable_inhabited prop_decidable

-- should be handled by implies_true_iff

namespace lattice
variables {α : Type u} {ι : Sort v} [complete_lattice α]

lemma Inf_eq_finite_sets {s : set α} :
  Inf s = (⨅ t ∈ { t | finite t ∧ t ⊆ s}, Inf t) :=
le_antisymm
  (le_infi $ assume t, le_infi $ assume ⟨_, h⟩, Inf_le_Inf h)
  (le_Inf $ assume b h, infi_le_of_le {b} $ infi_le_of_le (by simp [h]) $ Inf_le $ by simp)

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

section order
variables {α : Type u} (r : α → α → Prop)
local infix `≼` : 50 := r

def directed {ι : Sort v} (f : ι → α) := ∀x, ∀y, ∃z, f z ≼ f x ∧ f z ≼ f y
def directed_on (s : set α) := ∀x ∈ s, ∀y ∈ s, ∃z ∈ s, z ≼ x ∧ z ≼ y

lemma directed_on_Union {r} {ι : Sort v} {f : ι → set α} (hd : directed (⊇) f)
  (h : ∀x, directed_on r (f x)) : directed_on r (⋃x, f x) :=
by simp [directed_on]; exact
  assume a₁ b₁ fb₁ a₂ b₂ fb₂,
  let
    ⟨z, zb₁, zb₂⟩ := hd b₁ b₂,
    ⟨x, xf, xa₁, xa₂⟩ := h z a₁ (zb₁ fb₁) a₂ (zb₂ fb₂)
  in
    ⟨x, xa₁, xa₂, z, xf⟩

def upwards (s : set α) := ∀{x y}, x ∈ s → x ≼ y → y ∈ s

end order

theorem directed_of_chain {α : Type u} {β : Type v} [preorder β] {f : α → β} {c : set α}
  (h : @zorn.chain α (λa b, f b ≤ f a) c) :
  directed (≤) (λx:{a:α // a ∈ c}, f (x.val)) :=
assume ⟨a, ha⟩ ⟨b, hb⟩, classical.by_cases
  (assume : a = b, by simp [this]; exact ⟨b, hb, le_refl _⟩)
  (assume : a ≠ b,
    have f b ≤ f a ∨ f a ≤ f b, from h a ha b hb this,
    or.elim this
      (assume : f b ≤ f a, ⟨⟨b, hb⟩, this, le_refl _⟩)
      (assume : f a ≤ f b, ⟨⟨a, ha⟩, le_refl _, this⟩))

structure filter (α : Type u) :=
(sets            : set (set α))
(exists_mem_sets : ∃x, x ∈ sets)
(upwards_sets    : upwards (⊆) sets)
(directed_sets   : directed_on (⊆) sets)

namespace filter
variables {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x}

lemma filter_eq : ∀{f g : filter α}, f.sets = g.sets → f = g
| ⟨a, _, _, _⟩ ⟨._, _, _, _⟩ rfl := rfl

lemma univ_mem_sets' {f : filter α} {s : set α} (h : ∀ a, a ∈ s): s ∈ f.sets :=
let ⟨x, x_in_s⟩ := f.exists_mem_sets in
f.upwards_sets x_in_s (assume x _, h x)

lemma univ_mem_sets {f : filter α} : univ ∈ f.sets :=
univ_mem_sets' mem_univ

lemma inter_mem_sets {f : filter α} {x y : set α} (hx : x ∈ f.sets) (hy : y ∈ f.sets) :
  x ∩ y ∈ f.sets :=
let ⟨z, ⟨z_in_s, z_le_x, z_le_y⟩⟩ := f.directed_sets _ hx _ hy in
f.upwards_sets z_in_s (subset_inter z_le_x z_le_y)

lemma Inter_mem_sets {f : filter α} {s : β → set α}
  {is : set β} (hf : finite is) (hs : ∀i∈is, s i ∈ f.sets) : (⋂i∈is, s i) ∈ f.sets :=
begin /- equation compiler complains that this requires well-founded recursion -/
  induction hf with i is _ hf hi,
  { simp [univ_mem_sets] },
  begin
    simp,
    apply inter_mem_sets,
    apply hs i,
    simp,
    exact (hi $ assume a ha, hs _ $ by simp [ha])
  end
end

lemma exists_sets_subset_iff {f : filter α} {x : set α} :
  (∃y∈f.sets, y ⊆ x) ↔ x ∈ f.sets :=
⟨assume ⟨y, hy, yx⟩, f.upwards_sets hy yx,
  assume hx, ⟨x, hx, subset.refl _⟩⟩

lemma monotone_mem_sets {f : filter α} : monotone (λs, s ∈ f.sets) :=
assume s t hst h, f.upwards_sets h hst

def principal (s : set α) : filter α :=
{ filter .
  sets            := {t | s ⊆ t},
  exists_mem_sets := ⟨s, subset.refl _⟩,
  upwards_sets    := assume x y hx hy, subset.trans hx hy,
  directed_sets   := assume x hx y hy, ⟨s, subset.refl _, hx, hy⟩ }

def join (f : filter (filter α)) : filter α :=
{ filter .
  sets            := {s | {t : filter α | s ∈ t.sets} ∈ f.sets},
  exists_mem_sets := ⟨univ, by simp [univ_mem_sets]; exact univ_mem_sets⟩,
  upwards_sets    := assume x y hx xy, f.upwards_sets hx $ assume a h, a.upwards_sets h xy,
  directed_sets   := assume x hx y hy, ⟨x ∩ y,
    f.upwards_sets (inter_mem_sets hx hy) $ assume z ⟨h₁, h₂⟩, inter_mem_sets h₁ h₂,
    inter_subset_left _ _,  inter_subset_right _ _⟩ }

def map (m : α → β) (f : filter α) : filter β :=
{ filter .
  sets            := preimage (preimage m) f.sets,
  exists_mem_sets := ⟨univ, univ_mem_sets⟩,
  upwards_sets    := assume s t hs st, f.upwards_sets hs (assume x h, st h),
  directed_sets   := assume s hs t ht, ⟨s ∩ t, inter_mem_sets hs ht,
    inter_subset_left _ _,  inter_subset_right _ _⟩ }

def vmap (m : α → β) (f : filter β) : filter α :=
{ filter .
  sets            := { s | ∃t∈f.sets, preimage m t ⊆ s },
  exists_mem_sets := ⟨univ, univ, univ_mem_sets, by simp⟩,
  upwards_sets    := assume a b ⟨a', ha', ma'a⟩ ab, ⟨a', ha', subset.trans ma'a ab⟩,
  directed_sets   := assume a ⟨a', ha₁, ha₂⟩ b ⟨b', hb₁, hb₂⟩,
    ⟨preimage m (a' ∩ b'),
      ⟨a' ∩ b', inter_mem_sets ha₁ hb₁, subset.refl _⟩,
      subset.trans (preimage_mono $ inter_subset_left _ _) ha₂,
      subset.trans (preimage_mono $ inter_subset_right _ _) hb₂⟩ }

protected def sup (f g : filter α) : filter α :=
{ filter .
  sets            := f.sets ∩ g.sets,
  exists_mem_sets := ⟨univ, by simp [univ_mem_sets]; exact univ_mem_sets⟩,
  upwards_sets    := assume x y hx xy,
    and.imp (assume h, f.upwards_sets h xy) (assume h, g.upwards_sets h xy) hx,
  directed_sets   := assume x ⟨hx₁, hx₂⟩ y ⟨hy₁, hy₂⟩, ⟨x ∩ y,
    ⟨inter_mem_sets hx₁ hy₁, inter_mem_sets hx₂ hy₂⟩,
    inter_subset_left _ _,  inter_subset_right _ _⟩ }

protected def inf (f g : filter α) :=
{ filter .
  sets            := {s | ∃ a ∈ f.sets, ∃ b ∈ g.sets, a ∩ b ⊆ s },
  exists_mem_sets := ⟨univ, univ, univ_mem_sets, univ, univ_mem_sets, subset_univ _⟩,
  upwards_sets    := assume x y ⟨a, ha, b, hb, h⟩ xy,
    ⟨a, ha, b, hb, subset.trans h xy⟩,
  directed_sets   := assume x ⟨a₁, ha₁, b₁, hb₁, h₁⟩ y ⟨a₂, ha₂, b₂, hb₂, h₂⟩,
    ⟨x ∩ y,
      ⟨_, inter_mem_sets ha₁ ha₂, _, inter_mem_sets hb₁ hb₂,
        calc (a₁ ⊓ a₂) ⊓ (b₁ ⊓ b₂) = (a₁ ⊓ b₁) ⊓ (a₂ ⊓ b₂) : by ac_refl
                                ... ≤ x ∩ y : inf_le_inf h₁ h₂ ⟩,
      inter_subset_left _ _, inter_subset_right _ _⟩ }

def cofinite : filter α :=
{ filter .
  sets            := {s | finite (- s)},
  exists_mem_sets := ⟨univ, by simp⟩,
  upwards_sets    := assume s t, assume hs : finite (-s), assume st: s ⊆ t,
    finite_subset hs $ @lattice.neg_le_neg (set α) _ _ _ st,
  directed_sets   := assume s, assume hs : finite (-s), assume t, assume ht : finite (-t),
    ⟨s ∩ t, by simp [compl_inter, finite_union, ht, hs],
      inter_subset_left _ _, inter_subset_right _ _⟩ }

instance partial_order_filter : partial_order (filter α) :=
{ partial_order .
  le            := λf g, g.sets ⊆ f.sets,
  le_antisymm   := assume a b h₁ h₂, filter_eq $ subset.antisymm h₂ h₁,
  le_refl       := assume a, subset.refl _,
  le_trans      := assume a b c h₁ h₂, subset.trans h₂ h₁ }

instance : has_Sup (filter α) := ⟨join ∘ principal⟩

instance : inhabited (filter α) :=
⟨principal ∅⟩

protected lemma le_Sup {s : set (filter α)} {f : filter α} : f ∈ s → f ≤ Sup s :=
assume f_in_s t' h, h f_in_s

protected lemma Sup_le {s : set (filter α)} {f : filter α} : (∀g∈s, g ≤ f) → Sup s ≤ f :=
assume h a ha g hg, h g hg ha

@[simp] lemma mem_join_sets {s : set α} {f : filter (filter α)} :
  s ∈ (join f).sets = ({t | s ∈ filter.sets t} ∈ f.sets) := rfl

@[simp] lemma mem_principal_sets {s t : set α} : s ∈ (principal t).sets = (t ⊆ s) := rfl

@[simp] lemma le_principal_iff {s : set α} {f : filter α} : f ≤ principal s ↔ s ∈ f.sets :=
show (∀{t}, s ⊆ t → t ∈ f.sets) ↔ s ∈ f.sets,
  from ⟨assume h, h (subset.refl s), assume hs t ht, f.upwards_sets hs ht⟩

lemma principal_mono {s t : set α} : principal s ≤ principal t ↔ s ⊆ t :=
by simp

lemma monotone_principal : monotone (principal : set α → filter α) :=
by simp [monotone, principal_mono]; exact assume a b h, h

@[simp] lemma principal_eq_iff_eq {s t : set α} : principal s = principal t ↔ s = t :=
by simp [eq_iff_le_and_le]; refl

instance complete_lattice_filter : complete_lattice (filter α) :=
{ sup           := filter.sup,
  le_sup_left   := assume a b, inter_subset_left _ _,
  le_sup_right  := assume a b, inter_subset_right _ _,
  sup_le        := assume a b c h₁ h₂, subset_inter h₁ h₂,
  inf           := filter.inf,
  le_inf        := assume f g h fg fh s ⟨a, ha, b, hb, h⟩,
    f.upwards_sets (inter_mem_sets (fg ha) (fh hb)) h,
  inf_le_left   := assume f g s h, ⟨s, h, univ, univ_mem_sets, inter_subset_left _ _⟩,
  inf_le_right  := assume f g s h, ⟨univ, univ_mem_sets, s, h, inter_subset_right _ _⟩,
  top           := principal univ,
  le_top        := assume a, show a ≤ principal univ, by simp [univ_mem_sets],
  bot           := principal ∅,
  bot_le        := assume a, show a.sets ⊆ {x | ∅ ⊆ x}, by simp; apply subset_univ,
  Sup           := Sup,
  le_Sup        := assume s f, filter.le_Sup,
  Sup_le        := assume s f, filter.Sup_le,
  Inf           := λs, Sup {x | ∀y∈s, x ≤ y},
  le_Inf        := assume s a h, filter.le_Sup h,
  Inf_le        := assume s a ha, filter.Sup_le $ assume b h, h _ ha,
  ..filter.partial_order_filter }

@[simp] lemma map_principal {s : set α} {f : α → β} :
  map f (principal s) = principal (set.image f s) :=
filter_eq $ set.ext $ assume a, image_subset_iff.symm

@[simp] lemma mem_top_sets_iff {s : set α} : s ∈ (⊤ : filter α).sets ↔ s = univ :=
⟨assume h, top_unique $ h, assume h, h.symm ▸ univ_mem_sets⟩

@[simp] lemma join_principal_eq_Sup {s : set (filter α)} : join (principal s) = Sup s := rfl

instance monad_filter : monad filter :=
{ monad .
  bind       := λ(α β : Type u) f m, join (map m f),
  pure       := λ(α : Type u) x, principal {x},
  map        := λ(α β : Type u), filter.map,
  id_map     := assume α f, filter_eq $ rfl,
  pure_bind  := assume α β a f, by simp [Sup_image],
  bind_assoc := assume α β γ f m₁ m₂, filter_eq $ rfl,
  bind_pure_comp_eq_map := assume α β f x, filter_eq $ by simp [join, map, preimage, principal] }

@[simp] lemma pure_def (x : α) : pure x = principal {x} := rfl

@[simp] lemma bind_def {α β} (f : filter α) (m : α → filter β) : f >>= m = join (map m f) := rfl

instance : alternative filter :=
{ failure := λα, ⊥,
  orelse  := λα x y, x ⊔ y,
  ..filter.monad_filter }

/- lattice equations -/

lemma mem_inf_sets_of_left {f g : filter α} {s : set α} :
  s ∈ f.sets → s ∈ (f ⊓ g).sets :=
have f ⊓ g ≤ f, from inf_le_left,
assume hs, this hs

lemma mem_inf_sets_of_right {f g : filter α} {s : set α} :
  s ∈ g.sets → s ∈ (f ⊓ g).sets :=
have f ⊓ g ≤ g, from inf_le_right,
assume hs, this hs

@[simp] lemma mem_bot_sets {s : set α} : s ∈ (⊥ : filter α).sets :=
assume x, false.elim

lemma empty_in_sets_eq_bot {f : filter α} : ∅ ∈ f.sets ↔ f = ⊥ :=
⟨assume h, bot_unique $ assume s _, f.upwards_sets h (empty_subset s),
  assume : f = ⊥, this.symm ▸ mem_bot_sets⟩

lemma inhabited_of_mem_sets {f : filter α} {s : set α} (hf : f ≠ ⊥) (hs : s ∈ f.sets) :
  ∃x, x ∈ s :=
have ∅ ∉ f.sets, from assume h, hf $ empty_in_sets_eq_bot.mp h,
have s ≠ ∅, from assume h, this (h ▸ hs),
exists_mem_of_ne_empty this

lemma filter_eq_bot_of_not_nonempty {f : filter α} (ne : ¬ nonempty α) : f = ⊥ :=
empty_in_sets_eq_bot.mp $ f.upwards_sets univ_mem_sets $
  assume x, false.elim (ne ⟨x⟩)

lemma forall_sets_neq_empty_iff_neq_bot {f : filter α} :
  (∀ (s : set α), s ∈ f.sets → s ≠ ∅) ↔ f ≠ ⊥ :=
by
  simp [(@empty_in_sets_eq_bot α f).symm];
  exact ⟨assume h hs, h _ hs rfl, assume h s hs eq, h $ eq ▸ hs⟩

lemma mem_sets_of_neq_bot {f : filter α} {s : set α} (h : f ⊓ principal (-s) = ⊥) : s ∈ f.sets :=
have ∅ ∈ (f ⊓ principal (- s)).sets, from h.symm ▸ mem_bot_sets,
let ⟨s₁, hs₁, s₂, (hs₂ : -s ⊆ s₂), (hs : s₁ ∩ s₂ ⊆ ∅)⟩ := this in
have s₁ ⊆ s, from assume a ha, classical.by_contradiction $ assume ha', hs ⟨ha, hs₂ ha'⟩,
f.upwards_sets hs₁ this

@[simp] lemma mem_sup_sets {f g : filter α} {s : set α} :
  s ∈ (f ⊔ g).sets = (s ∈ f.sets ∧ s ∈ g.sets) := rfl

@[simp] lemma mem_inf_sets {f g : filter α} {s : set α} :
  s ∈ (f ⊓ g).sets = (∃t₁∈f.sets, ∃t₂∈g.sets, t₁ ∩ t₂ ⊆ s) :=
by refl

lemma inter_mem_inf_sets {α : Type u} {f g : filter α} {s t : set α}
  (hs : s ∈ f.sets) (ht : t ∈ g.sets) : s ∩ t ∈ (f ⊓ g).sets :=
inter_mem_sets (mem_inf_sets_of_left hs) (mem_inf_sets_of_right ht)

lemma infi_sets_eq {f : ι → filter α} (h : directed (≤) f) (ne : nonempty ι) :
  (infi f).sets = (⋃ i, (f i).sets) :=
let
  ⟨i⟩          := ne,
  u           := { filter .
    sets            := (⋃ i, (f i).sets),
    exists_mem_sets := ⟨univ, begin simp, exact ⟨i, univ_mem_sets⟩ end⟩,
    directed_sets   := directed_on_Union (show directed (≤) f, from h) (assume i, (f i).directed_sets),
    upwards_sets    := by simp [upwards]; exact assume x y j xf xy, ⟨j, (f j).upwards_sets xf xy⟩ }
in
  subset.antisymm
    (show u ≤ infi f, from le_infi $ assume i, le_supr (λi, (f i).sets) i)
    (Union_subset $ assume i, infi_le f i)

lemma infi_sets_eq' {f : β → filter α} {s : set β} (h : directed_on (λx y, f x ≤ f y) s) (ne : ∃i, i ∈ s) :
  (⨅ i∈s, f i).sets = (⋃ i ∈ s, (f i).sets) :=
let ⟨i, hi⟩ := ne in
calc (⨅ i ∈ s, f i).sets  = (⨅ t : {t // t ∈ s}, (f t.val)).sets : by simp [infi_subtype]; refl
  ... = (⨆ t : {t // t ∈ s}, (f t.val).sets) : infi_sets_eq
    (assume ⟨x, hx⟩ ⟨y, hy⟩, match h x hx y hy with ⟨z, h₁, h₂, h₃⟩ := ⟨⟨z, h₁⟩, h₂, h₃⟩ end)
    ⟨⟨i, hi⟩⟩
  ... = (⨆ t ∈ {t | t ∈ s}, (f t).sets) : by simp [supr_subtype]; refl

lemma Inf_sets_eq_finite {s : set (filter α)} :
  (complete_lattice.Inf s).sets = (⋃ t ∈ {t | finite t ∧ t ⊆ s}, (Inf t).sets) :=
calc (Inf s).sets = (⨅ t ∈ { t | finite t ∧ t ⊆ s}, Inf t).sets : by rw [lattice.Inf_eq_finite_sets]
  ... = (⨆ t ∈ {t | finite t ∧ t ⊆ s}, (Inf t).sets) : infi_sets_eq'
    (assume x ⟨hx₁, hx₂⟩ y ⟨hy₁, hy₂⟩, ⟨x ∪ y, ⟨finite_union hx₁ hy₁, union_subset hx₂ hy₂⟩,
      Inf_le_Inf $ subset_union_left _ _, Inf_le_Inf $ subset_union_right _ _⟩)
    ⟨∅, by simp⟩

lemma supr_sets_eq {f : ι → filter α} : (supr f).sets = (⋂i, (f i).sets) :=
set.ext $ assume s,
show s ∈ (join (principal {a : filter α | ∃i : ι, a = f i})).sets ↔ s ∈ (⋂i, (f i).sets),
begin
  rw [mem_join_sets],
  simp, rw [forall_swap],
  exact forall_congr (λ i, by simp)
end

@[simp] lemma sup_join {f₁ f₂ : filter (filter α)} : (join f₁ ⊔ join f₂) = join (f₁ ⊔ f₂) :=
filter_eq $ set.ext $ assume x, by simp [supr_sets_eq, join]

@[simp] lemma supr_join {ι : Sort w} {f : ι → filter (filter α)} : (⨆x, join (f x)) = join (⨆x, f x) :=
filter_eq $ set.ext $ assume x, by simp [supr_sets_eq, join]

instance : bounded_distrib_lattice (filter α) :=
{ le_sup_inf := assume x y z s ⟨h₁, h₂⟩, begin
    revert h₂, simp,
    exact assume t₁ ht₁ t₂ ht₂ hs, ⟨s ∪ t₁,
      x.upwards_sets h₁ $ subset_union_left _ _,
      y.upwards_sets ht₁ $ subset_union_right _ _,
      s ∪ t₂,
      x.upwards_sets h₁ $ subset_union_left _ _,
      z.upwards_sets ht₂ $ subset_union_right _ _,
      subset.trans (@le_sup_inf (set α) _ _ _ _) (union_subset (subset.refl _) hs)⟩
  end, ..filter.complete_lattice_filter }

private lemma infi_finite_distrib {s : set (filter α)} {f : filter α} (h : finite s) :
  (⨅ a ∈ s, f ⊔ a) = f ⊔ (Inf s) :=
begin
  induction h with a s hn hs hi,
  { simp },
  { rw [infi_insert], simp [hi, infi_or, sup_inf_left] }
end

/- the complementary version with ⨆ g∈s, f ⊓ g does not hold! -/
lemma binfi_sup_eq { f : filter α } {s : set (filter α)} :
  (⨅ g∈s, f ⊔ g) = f ⊔ complete_lattice.Inf s :=
le_antisymm
  begin
    intros t h,
    cases h with h₁ h₂,
    rw [Inf_sets_eq_finite] at h₂,
    simp at h₂,
    cases h₂ with s' hs', cases hs' with hs' hs'', cases hs'' with hs's ht',
    have ht : t ∈ (⨅ a ∈ s', f ⊔ a).sets,
    { rw [infi_finite_distrib], exact ⟨h₁, ht'⟩, exact hs' },
    clear h₁ ht',
    revert ht t,
    change (⨅ a ∈ s, f ⊔ a) ≤ (⨅ a ∈ s', f ⊔ a),
    apply infi_le_infi2 _,
    exact assume i, ⟨i, infi_le_infi2 $ assume h, ⟨hs's h, le_refl _⟩⟩
  end
  (le_infi $ assume g, le_infi $ assume h, sup_le_sup (le_refl f) $ Inf_le h)

lemma infi_sup_eq { f : filter α } {g : ι → filter α} :
  (⨅ x, f ⊔ g x) = f ⊔ infi g :=
calc (⨅ x, f ⊔ g x) = (⨅ x (h : ∃i, g i = x), f ⊔ x) : by simp; rw [infi_comm]; simp
  ... = f ⊔ Inf {x | ∃i, g i = x} : binfi_sup_eq
  ... = f ⊔ infi g : by rw [Inf_eq_infi]; dsimp; simp; rw [infi_comm]; simp

lemma mem_infi_sets_finset {s : finset α} {f : α → filter β} :
  ∀t, t ∈ (⨅a∈s, f a).sets ↔ (∃p:α → set β, (∀a∈s, p a ∈ (f a).sets) ∧ (⋂a∈s, p a) ⊆ t) :=
show ∀t,  t ∈ (⨅a∈s, f a).sets ↔ (∃p:α → set β, (∀a∈s, p a ∈ (f a).sets) ∧ (⨅a∈s, p a) ≤ t),
  from s.induction_on (by simp; exact assume t, iff.refl _) $
    by simp [infi_or, mem_inf_sets, infi_inf_eq] {contextual := tt};
    from assume a s has ih t, iff.intro
      (assume ⟨t₁, ht₁, t₂, ht, p, hp, ht₂⟩,
        ⟨λa', if a' = a then t₁ else p a',
          assume a' ha', by by_cases a' = a; simp * at *,
          have ∀a', (⨅ (h : a' ∈ s), ite (a' = a) t₁ (p a')) ≤ ⨅ (H : a' ∈ s), p a',
            from assume a', infi_le_infi $ assume has',
              have a' ≠ a, from assume h, has $ h ▸ has',
              le_of_eq $ by simp [this],
          le_trans (inf_le_inf (by simp; exact le_refl t₁) (le_trans (infi_le_infi this) ht₂)) ht⟩)
      (assume ⟨p, hp, ht⟩, ⟨p a, hp _ (by simp), ⨅ (x : α) (h : x ∈ s), p x, ht, p,
        assume a ha, hp _ (or.inr ha), le_refl _⟩)

/- principal equations -/

@[simp] lemma inf_principal {s t : set α} : principal s ⊓ principal t = principal (s ∩ t) :=
le_antisymm
  (by simp; exact ⟨s, subset.refl s, t, subset.refl t, subset.refl _⟩)
  (by simp [le_inf_iff, inter_subset_left, inter_subset_right])

@[simp] lemma sup_principal {s t : set α} : principal s ⊔ principal t = principal (s ∪ t) :=
filter_eq $ set.ext $ by simp [union_subset_iff]

@[simp] lemma supr_principal {ι : Sort w} {s : ι → set α} : (⨆x, principal (s x)) = principal (⋃i, s i) :=
filter_eq $ set.ext $ assume x, by simp [supr_sets_eq]; exact (@supr_le_iff (set α) _ _ _ _).symm

lemma principal_univ : principal (univ : set α) = ⊤ := rfl

lemma principal_empty : principal (∅ : set α) = ⊥ := rfl

@[simp] lemma principal_eq_bot_iff {s : set α} : principal s = ⊥ ↔ s = ∅ :=
⟨assume h, principal_eq_iff_eq.mp $ by simp [principal_empty, h], assume h, by simp [*, principal_empty]⟩

lemma inf_principal_eq_bot {f : filter α} {s : set α} (hs : -s ∈ f.sets) : f ⊓ principal s = ⊥ :=
empty_in_sets_eq_bot.mp $ (f ⊓ principal s).upwards_sets
  (inter_mem_inf_sets hs (mem_principal_sets.mpr $ set.subset.refl s))
  (assume x ⟨h₁, h₂⟩, h₁ h₂)

@[simp] lemma mem_pure {a : α} {s : set α} : a ∈ s → s ∈ (pure a : filter α).sets :=
by simp; exact id

/- map and vmap equations -/
section map

variables {f f₁ f₂ : filter α} {g g₁ g₂ : filter β} {m : α → β} {m' : β → γ} {s : set α} {t : set β}

@[simp] lemma mem_map : (t ∈ (map m f).sets) = ({x | m x ∈ t} ∈ f.sets) := rfl
lemma image_mem_map (hs : s ∈ f.sets) : m '' s ∈ (map m f).sets :=
f.upwards_sets hs $ assume x hx, ⟨x, hx, rfl⟩

@[simp] lemma map_id : filter.map id f = f :=
filter_eq $ rfl

@[simp] lemma map_compose : filter.map m' ∘ filter.map m = filter.map (m' ∘ m) :=
funext $ assume _, filter_eq $ rfl

@[simp] lemma map_map : filter.map m' (filter.map m f) = filter.map (m' ∘ m) f :=
congr_fun (@@filter.map_compose m m') f

theorem mem_vmap : s ∈ (vmap m g).sets = (∃t∈g.sets, m ⁻¹' t ⊆ s) := rfl
theorem preimage_mem_vmap (ht : t ∈ g.sets) : m ⁻¹' t ∈ (vmap m g).sets :=
⟨t, ht, subset.refl _⟩

lemma vmap_id : vmap id f = f :=
le_antisymm (assume s, preimage_mem_vmap) (assume s ⟨t, ht, hst⟩, f.upwards_sets ht hst)

lemma vmap_vmap_comp {m : γ → β} {n : β → α} : vmap m (vmap n f) = vmap (n ∘ m) f :=
le_antisymm
  (assume c ⟨b, hb, (h : preimage (n ∘ m) b ⊆ c)⟩, ⟨preimage n b, preimage_mem_vmap hb, h⟩)
  (assume c ⟨b, ⟨a, ha, (h₁ : preimage n a ⊆ b)⟩, (h₂ : preimage m b ⊆ c)⟩,
    ⟨a, ha, show preimage m (preimage n a) ⊆ c, from subset.trans (preimage_mono h₁) h₂⟩)

@[simp] theorem vmap_principal {t : set β} : vmap m (principal t) = principal (m ⁻¹' t) :=
filter_eq $ set.ext $ assume s,
  ⟨assume ⟨u, (hu : t ⊆ u), (b : preimage m u ⊆ s)⟩, subset.trans (preimage_mono hu) b,
    assume : preimage m t ⊆ s, ⟨t, subset.refl t, this⟩⟩

lemma map_le_iff_vmap_le : map m f ≤ g ↔ f ≤ vmap m g :=
⟨assume h s ⟨t, ht, hts⟩, f.upwards_sets (h ht) hts, assume h s ht, h ⟨_, ht, subset.refl _⟩⟩

lemma gc_map_vmap (m : α → β) : galois_connection (map m) (vmap m) :=
assume f g, map_le_iff_vmap_le

lemma map_mono (h : f₁ ≤ f₂) : map m f₁ ≤ map m f₂ := (gc_map_vmap m).monotone_l h
lemma monotone_map : monotone (map m) := assume a b h, map_mono h
lemma vmap_mono (h : g₁ ≤ g₂) : vmap m g₁ ≤ vmap m g₂ := (gc_map_vmap m).monotone_u h
lemma monotone_vmap : monotone (vmap m) := assume a b h, vmap_mono h

@[simp] lemma map_bot : map m ⊥ = ⊥ := (gc_map_vmap m).l_bot
@[simp] lemma map_sup : map m (f₁ ⊔ f₂) = map m f₁ ⊔ map m f₂ := (gc_map_vmap m).l_sup
@[simp] lemma map_supr {f : ι → filter α} : map m (⨆i, f i) = (⨆i, map m (f i)) :=
(gc_map_vmap m).l_supr

@[simp] lemma vmap_top : vmap m ⊤ = ⊤ := (gc_map_vmap m).u_top
@[simp] lemma vmap_inf : vmap m (g₁ ⊓ g₂) = vmap m g₁ ⊓ vmap m g₂ := (gc_map_vmap m).u_inf
@[simp] lemma vmap_infi {f : ι → filter β} : vmap m (⨅i, f i) = (⨅i, vmap m (f i)) :=
(gc_map_vmap m).u_infi

lemma map_vmap_le : map m (vmap m g) ≤ g := (gc_map_vmap m).decreasing_l_u _
lemma le_vmap_map : f ≤ vmap m (map m f) := (gc_map_vmap m).increasing_u_l _

@[simp] lemma vmap_bot : vmap m ⊥ = ⊥ :=
bot_unique $ assume s _, ⟨∅, by simp, by simp⟩

lemma vmap_sup : vmap m (g₁ ⊔ g₂) = vmap m g₁ ⊔ vmap m g₂ :=
le_antisymm
  (assume s ⟨⟨t₁, ht₁, hs₁⟩, ⟨t₂, ht₂, hs₂⟩⟩,
    ⟨t₁ ∪ t₂,
      ⟨g₁.upwards_sets ht₁ (subset_union_left _ _), g₂.upwards_sets ht₂ (subset_union_right _ _)⟩,
      union_subset hs₁ hs₂⟩)
  (sup_le (vmap_mono le_sup_left) (vmap_mono le_sup_right))

lemma le_map_vmap' {f : filter β} {m : α → β} {s : set β}
  (hs : s ∈ f.sets) (hm : ∀b∈s, ∃a, m a = b) : f ≤ map m (vmap m f) :=
assume t' ⟨t, ht, (sub : m ⁻¹' t ⊆ m ⁻¹' t')⟩,
f.upwards_sets (inter_mem_sets ht hs) $
  assume x ⟨hxt, hxs⟩,
  let ⟨y, (hy : m y = x)⟩ := hm x hxs in
  hy ▸ sub (show m y ∈ t, from hy.symm ▸ hxt)

lemma le_map_vmap {f : filter β} {m : α → β} (hm : ∀x, ∃y, m y = x) : f ≤ map m (vmap m f) :=
le_map_vmap' univ_mem_sets (assume b _, hm b)

lemma vmap_map {f : filter α} {m : α → β} (h : ∀ x y, m x = m y → x = y) :
  vmap m (map m f) = f :=
have ∀s, preimage m (image m s) = s,
  from assume s, preimage_image_eq h,
le_antisymm
  (assume s hs, ⟨
    image m s,
    f.upwards_sets hs $ by simp [this, subset.refl],
    by simp [this, subset.refl]⟩)
  (assume s ⟨t, (h₁ : preimage m t ∈ f.sets), (h₂ : preimage m t ⊆ s)⟩,
    f.upwards_sets h₁ h₂)

lemma le_of_map_le_map_inj' {f g : filter α} {m : α → β} {s : set α}
  (hsf : s ∈ f.sets) (hsg : s ∈ g.sets) (hm : ∀x∈s, ∀y∈s, m x = m y → x = y)
  (h : map m f ≤ map m g) : f ≤ g :=
assume t ht,
  have m ⁻¹' (m '' (s ∩ t)) ∈ f.sets, from h $ image_mem_map (inter_mem_sets hsg ht),
  f.upwards_sets (inter_mem_sets hsf this) $
    assume a ⟨has, b, ⟨hbs, hb⟩, h⟩,
    have b = a, from hm _ hbs _ has h,
    this ▸ hb

lemma eq_of_map_eq_map_inj' {f g : filter α} {m : α → β} {s : set α}
  (hsf : s ∈ f.sets) (hsg : s ∈ g.sets) (hm : ∀x∈s, ∀y∈s, m x = m y → x = y)
  (h : map m f = map m g) : f = g :=
le_antisymm
  (le_of_map_le_map_inj' hsf hsg hm $ le_of_eq h)
  (le_of_map_le_map_inj' hsg hsf hm $ le_of_eq h.symm)

lemma map_inj {f g : filter α} {m : α → β} (hm : ∀ x y, m x = m y → x = y) (h : map m f = map m g) :
  f = g :=
have vmap m (map m f) = vmap m (map m g), by rw h,
by rwa [vmap_map hm, vmap_map hm] at this

lemma vmap_neq_bot {f : filter β} {m : α → β}
  (hm : ∀t∈f.sets, ∃a, m a ∈ t) : vmap m f ≠ ⊥ :=
forall_sets_neq_empty_iff_neq_bot.mp $ assume s ⟨t, ht, t_s⟩,
  let ⟨a, (ha : a ∈ preimage m t)⟩ := hm t ht in
  neq_bot_of_le_neq_bot (ne_empty_of_mem ha) t_s

lemma vmap_neq_bot_of_surj {f : filter β} {m : α → β}
  (hf : f ≠ ⊥) (hm : ∀b, ∃a, m a = b) : vmap m f ≠ ⊥ :=
vmap_neq_bot $ assume t ht,
  let
    ⟨b, (hx : b ∈ t)⟩ := inhabited_of_mem_sets hf ht,
    ⟨a, (ha : m a = b)⟩ := hm b
  in ⟨a, ha.symm ▸ hx⟩

lemma le_vmap_iff_map_le {f : filter α} {g : filter β} {m : α → β} :
  f ≤ vmap m g ↔ map m f ≤ g :=
⟨assume h, le_trans (map_mono h) map_vmap_le,
  assume h, le_trans le_vmap_map (vmap_mono h)⟩

@[simp] lemma map_eq_bot_iff : map m f = ⊥ ↔ f = ⊥ :=
⟨by rw [←empty_in_sets_eq_bot, ←empty_in_sets_eq_bot]; exact id,
  assume h, by simp [*]⟩

lemma map_ne_bot (hf : f ≠ ⊥) : map m f ≠ ⊥ :=
assume h, hf $ by rwa [map_eq_bot_iff] at h

end map

lemma map_cong {m₁ m₂ : α → β} {f : filter α} (h : {x | m₁ x = m₂ x} ∈ f.sets) :
  map m₁ f = map m₂ f :=
have ∀(m₁ m₂ : α → β) (h : {x | m₁ x = m₂ x} ∈ f.sets), map m₁ f ≤ map m₂ f,
  from assume m₁ m₂ h s (hs : {x | m₂ x ∈ s} ∈ f.sets),
  show {x | m₁ x ∈ s} ∈ f.sets,
    from f.upwards_sets (inter_mem_sets hs h) $
    assume x ⟨(h₁ : m₂ x ∈ s), (h₂ : m₁ x = m₂ x)⟩, show m₁ x ∈ s, from h₂.symm ▸ h₁,
le_antisymm (this m₁ m₂ h) (this m₂ m₁ $ f.upwards_sets h $ assume x, eq.symm)

-- this is a generic rule for monotone functions:
lemma map_infi_le {f : ι → filter α} {m : α → β} :
  map m (infi f) ≤ (⨅ i, map m (f i)) :=
le_infi $ assume i, map_mono $ infi_le _ _

lemma map_infi_eq {f : ι → filter α} {m : α → β} (hf : directed (≤) f) (hι : nonempty ι) :
  map m (infi f) = (⨅ i, map m (f i)) :=
le_antisymm
  map_infi_le
  (assume s (hs : preimage m s ∈ (infi f).sets),
    have ∃i, preimage m s ∈ (f i).sets,
      by simp [infi_sets_eq hf hι] at hs; assumption,
    let ⟨i, hi⟩ := this in
    have (⨅ i, map m (f i)) ≤ principal s,
      from infi_le_of_le i $ by simp; assumption,
    by simp at this; assumption)

lemma map_binfi_eq {ι : Type w} {f : ι → filter α} {m : α → β} {p : ι → Prop}
  (h : directed_on (λx y, f x ≤ f y) {x | p x}) (ne : ∃i, p i) :
  map m (⨅i (h : p i), f i) = (⨅i (h: p i), map m (f i)) :=
let ⟨i, hi⟩ := ne in
calc map m (⨅i (h : p i), f i) = map m (⨅i:subtype p, f i.val) : by simp [infi_subtype]
  ... = (⨅i:subtype p, map m (f i.val)) : map_infi_eq
    (assume ⟨x, hx⟩ ⟨y, hy⟩, match h x hx y hy with ⟨z, h₁, h₂, h₃⟩ := ⟨⟨z, h₁⟩, h₂, h₃⟩ end)
    ⟨⟨i, hi⟩⟩
  ... = (⨅i (h : p i), map m (f i)) : by simp [infi_subtype]

lemma map_inf' {f g : filter α} {m : α → β} {t : set α} (htf : t ∈ f.sets) (htg : t ∈ g.sets)
  (h : ∀x∈t, ∀y∈t, m x = m y → x = y) : map m (f ⊓ g) = map m f ⊓ map m g :=
le_antisymm
  (le_inf (map_mono inf_le_left) (map_mono inf_le_right))
  (assume s hs,
  begin
    simp [map, mem_inf_sets] at hs,
    simp [map, mem_inf_sets],
    exact (let ⟨t₁, h₁, t₂, h₂, hs⟩ := hs in
      have m '' (t₁ ∩ t) ∩ m '' (t₂ ∩ t) ⊆ s,
      begin
        rw [image_inter_on],
        refine image_subset_iff.2 _,
        exact assume x ⟨⟨h₁, _⟩, h₂, _⟩, hs ⟨h₁, h₂⟩,
        exact assume x ⟨_, hx⟩ y ⟨_, hy⟩, h x hx y hy
      end,
      ⟨m '' (t₁ ∩ t),
        f.upwards_sets (inter_mem_sets h₁ htf) $ image_subset_iff.mp $ subset.refl _,
        m '' (t₂ ∩ t),
        this,
        g.upwards_sets (inter_mem_sets h₂ htg) $ image_subset_iff.mp $ subset.refl _⟩)
  end)

lemma map_inf {f g : filter α} {m : α → β} (h : ∀ x y, m x = m y → x = y) :
  map m (f ⊓ g) = map m f ⊓ map m g :=
map_inf' univ_mem_sets univ_mem_sets (assume x _ y _, h x y)

/- bind equations -/

lemma mem_bind_sets {β : Type u} {s : set β} {f : filter α} {m : α → filter β} :
  s ∈ (f >>= m).sets ↔ (∃t ∈ f.sets, ∀x ∈ t, s ∈ (m x).sets) :=
calc s ∈ (f >>= m).sets ↔ {a | s ∈ (m a).sets} ∈ f.sets : by simp
                     ... ↔ (∃t ∈ f.sets, t ⊆ {a | s ∈ (m a).sets}) : exists_sets_subset_iff.symm
                     ... ↔ (∃t ∈ f.sets, ∀x ∈ t, s ∈ (m x).sets) : iff.refl _

lemma bind_mono {β : Type u} {f : filter α} {g h : α → filter β} (h₁ : {a | g a ≤ h a} ∈ f.sets) :
  f >>= g ≤ f >>= h :=
assume x h₂, f.upwards_sets (inter_mem_sets h₁ h₂) $ assume s ⟨gh', h'⟩, gh' h'

lemma bind_sup {β : Type u} {f g : filter α} {h : α → filter β} :
  (f ⊔ g) >>= h = (f >>= h) ⊔ (g >>= h) :=
by simp

lemma bind_mono2 {β : Type u} {f g : filter α} {h : α → filter β} (h₁ : f ≤ g) :
  f >>= h ≤ g >>= h :=
assume s h', h₁ h'

lemma principal_bind {β : Type u} {s : set α} {f : α → filter β} :
  (principal s >>= f) = (⨆x ∈ s, f x) :=
show join (map f (principal s)) = (⨆x ∈ s, f x),
  by simp [Sup_image]

lemma seq_mono {β : Type u} {f₁ f₂ : filter (α → β)} {g₁ g₂ : filter α}
  (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) : f₁ <*> g₁ ≤ f₂ <*> g₂ :=
le_trans (bind_mono2 hf) (bind_mono $ univ_mem_sets' $ assume f, map_mono hg)

@[simp] lemma fmap_principal {β : Type u} {s : set α} {f : α → β} :
  f <$> principal s = principal (set.image f s) :=
filter_eq $ set.ext $ assume a, image_subset_iff.symm

lemma mem_return_sets {a : α} {s : set α} : s ∈ (return a : filter α).sets ↔ a ∈ s :=
show s ∈ (principal {a}).sets ↔ a ∈ s,
  by simp

lemma infi_neq_bot_of_directed {f : ι → filter α}
  (hn : nonempty α) (hd : directed (≤) f) (hb : ∀i, f i ≠ ⊥): (infi f) ≠ ⊥ :=
let ⟨x⟩ := hn in
assume h, have he: ∅ ∈ (infi f).sets, from h.symm ▸ mem_bot_sets,
classical.by_cases
  (assume : nonempty ι,
    have ∃i, ∅ ∈ (f i).sets,
      by rw [infi_sets_eq hd this] at he; simp at he; assumption,
    let ⟨i, hi⟩ := this in
    hb i $ bot_unique $
    assume s _, (f i).upwards_sets hi $ empty_subset _)
  (assume : ¬ nonempty ι,
    have univ ⊆ (∅ : set α),
    begin
      rw [←principal_mono, principal_univ, principal_empty, ←h],
      exact (le_infi $ assume i, false.elim $ this ⟨i⟩)
    end,
    this $ mem_univ x)

lemma infi_neq_bot_iff_of_directed {f : ι → filter α}
  (hn : nonempty α) (hd : directed (≤) f) : (infi f) ≠ ⊥ ↔ (∀i, f i ≠ ⊥) :=
⟨assume neq_bot i eq_bot, neq_bot $ bot_unique $ infi_le_of_le i $ eq_bot ▸ le_refl _,
  infi_neq_bot_of_directed hn hd⟩

@[simp] lemma return_neq_bot {α : Type u} {a : α} : return a ≠ (⊥ : filter α) :=
by simp [return]

/- tendsto -/
def tendsto (f : α → β) (l₁ : filter α) (l₂ : filter β) := filter.map f l₁ ≤ l₂

lemma tendsto_cong {f₁ f₂ : α → β} {l₁ : filter α} {l₂ : filter β}
  (h : tendsto f₁ l₁ l₂) (hl : {x | f₁ x = f₂ x} ∈ l₁.sets) : tendsto f₂ l₁ l₂ :=
by rwa [tendsto, ←map_cong hl]

lemma tendsto_id' {x y : filter α} : x ≤ y → tendsto id x y :=
by simp [tendsto] { contextual := tt }

lemma tendsto_id {x : filter α} : tendsto id x x := tendsto_id' $ le_refl x

lemma tendsto_compose {f : α → β} {g : β → γ} {x : filter α} {y : filter β} {z : filter γ}
  (hf : tendsto f x y) (hg : tendsto g y z) : tendsto (g ∘ f) x z :=
calc map (g ∘ f) x = map g (map f x) : by rw [map_map]
  ... ≤ map g y : map_mono hf
  ... ≤ z : hg

lemma tendsto_map {f : α → β} {x : filter α} : tendsto f x (map f x) := le_refl (map f x)

lemma tendsto_map' {f : β → γ} {g : α → β} {x : filter α} {y : filter γ}
  (h : tendsto (f ∘ g) x y) : tendsto f (map g x) y :=
by rwa [tendsto, map_map]

lemma tendsto_vmap {f : α → β} {x : filter β} : tendsto f (vmap f x) x :=
map_vmap_le

lemma tendsto_vmap' {f : β → γ} {g : α → β} {x : filter α} {y : filter γ}
  (h : tendsto (f ∘ g) x y) : tendsto g x (vmap f y) :=
le_vmap_iff_map_le.mpr $ by rwa [map_map]

lemma tendsto_vmap'' {m : α → β} {f : filter α} {g : filter β} (s : set α)
  {i : γ → α} (hs : s ∈ f.sets) (hi : ∀a∈s, ∃c, i c = a)
  (h : tendsto (m ∘ i) (vmap i f) g) : tendsto m f g :=
have tendsto m (map i $ vmap i $ f) g,
  by rwa [tendsto, ←map_compose] at h,
le_trans (map_mono $ le_map_vmap' hs hi) this

lemma tendsto_inf {f : α → β} {x : filter α} {y₁ y₂ : filter β}
  (h₁ : tendsto f x y₁) (h₂ : tendsto f x y₂) : tendsto f x (y₁ ⊓ y₂) :=
le_inf h₁ h₂

lemma tendsto_inf_left {f : α → β} {x₁ x₂ : filter α} {y : filter β}
  (h : tendsto f x₁ y) : tendsto f (x₁ ⊓ x₂) y :=
le_trans (map_mono inf_le_left) h

lemma tendsto_infi {f : α → β} {x : filter α} {y : ι → filter β}
  (h : ∀i, tendsto f x (y i)) : tendsto f x (⨅i, y i) :=
le_infi h

lemma tendsto_infi' {f : α → β} {x : ι → filter α} {y : filter β} (i : ι)
  (h : tendsto f (x i) y) : tendsto f (⨅i, x i) y :=
le_trans (map_mono $ infi_le _ _) h

lemma tendsto_principal {f : α → β} {a : filter α} {s : set β}
  (h : {a | f a ∈ s} ∈ a.sets) : tendsto f a (principal s) :=
by simp [tendsto]; exact h

lemma tendsto_principal_principal {f : α → β} {s : set α} {t : set β}
  (h : ∀a∈s, f a ∈ t) : tendsto f (principal s) (principal t) :=
by simp [tendsto, image_subset_iff]; exact h

section lift

protected def lift (f : filter α) (g : set α → filter β) :=
(⨅s ∈ f.sets, g s)

section
variables {f f₁ f₂ : filter α} {g g₁ g₂ : set α → filter β}

lemma lift_sets_eq (hg : monotone g) : (f.lift g).sets = (⋃t∈f.sets, (g t).sets) :=
infi_sets_eq'
  (assume s hs t ht, ⟨s ∩ t, inter_mem_sets hs ht,
    hg $ inter_subset_left s t, hg $ inter_subset_right s t⟩)
  ⟨univ, univ_mem_sets⟩

lemma mem_lift {s : set β} {t : set α} (ht : t ∈ f.sets) (hs : s ∈ (g t).sets) :
  s ∈ (f.lift g).sets :=
le_principal_iff.mp $ show f.lift g ≤ principal s,
  from infi_le_of_le t $ infi_le_of_le ht $ le_principal_iff.mpr hs

lemma mem_lift_iff (hg : monotone g) {s : set β} :
  s ∈ (f.lift g).sets ↔ (∃t∈f.sets, s ∈ (g t).sets) :=
by rw [lift_sets_eq hg]; simp

lemma lift_le {f : filter α} {g : set α → filter β}  {h : filter β} {s : set α}
  (hs : s ∈ f.sets) (hg : g s ≤ h) : f.lift g ≤ h :=
infi_le_of_le s $ infi_le_of_le hs $ hg

lemma lift_mono (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) : f₁.lift g₁ ≤ f₂.lift g₂ :=
infi_le_infi $ assume s, infi_le_infi2 $ assume hs, ⟨hf hs, hg s⟩

lemma lift_mono' (hg : ∀s∈f.sets, g₁ s ≤ g₂ s) : f.lift g₁ ≤ f.lift g₂ :=
infi_le_infi $ assume s, infi_le_infi $ assume hs, hg s hs

lemma map_lift_eq {m : β → γ} (hg : monotone g) :
  map m (f.lift g) = f.lift (map m ∘ g) :=
have monotone (map m ∘ g),
  from monotone_comp hg monotone_map,
filter_eq $ set.ext $
  by simp [mem_lift_iff, hg, @mem_lift_iff _ _ f _ this]

lemma vmap_lift_eq {m : γ → β} (hg : monotone g) :
  vmap m (f.lift g) = f.lift (vmap m ∘ g) :=
have monotone (vmap m ∘ g),
  from monotone_comp hg monotone_vmap,
filter_eq $ set.ext $
begin
  simp [vmap, mem_lift_iff, hg, @mem_lift_iff _ _ f _ this],
  simp [vmap, function.comp],
  exact assume s, ⟨assume ⟨t₁, hs, t₂, ht, ht₁⟩, ⟨t₂, ht, t₁, hs, ht₁⟩,
    assume ⟨t₂, ht, t₁, hs, ht₁⟩, ⟨t₁, hs, t₂, ht, ht₁⟩⟩
end

theorem vmap_lift_eq2 {m : β → α} {g : set β → filter γ} (hg : monotone g) :
  (vmap m f).lift g = f.lift (g ∘ preimage m) :=
le_antisymm
  (le_infi $ assume s, le_infi $ assume hs,
    infi_le_of_le (preimage m s) $ infi_le _ ⟨s, hs, subset.refl _⟩)
  (le_infi $ assume s, le_infi $ assume ⟨s', hs', (h_sub : preimage m s' ⊆ s)⟩,
    infi_le_of_le s' $ infi_le_of_le hs' $ hg h_sub)

lemma map_lift_eq2 {g : set β → filter γ} {m : α → β} (hg : monotone g) :
  (map m f).lift g = f.lift (g ∘ image m) :=
le_antisymm
  (infi_le_infi2 $ assume s, ⟨image m s,
    infi_le_infi2 $ assume hs, ⟨
      f.upwards_sets hs $ assume a h, mem_image_of_mem _ h,
      le_refl _⟩⟩)
  (infi_le_infi2 $ assume t, ⟨preimage m t,
    infi_le_infi2 $ assume ht, ⟨ht,
      hg $ assume x, assume h : x ∈ m '' preimage m t,
        let ⟨y, hy, h_eq⟩ := h in
        show x ∈ t, from h_eq ▸ hy⟩⟩)

lemma lift_comm {g : filter β} {h : set α → set β → filter γ} :
  f.lift (λs, g.lift (h s)) = g.lift (λt, f.lift (λs, h s t)) :=
le_antisymm
  (le_infi $ assume i, le_infi $ assume hi, le_infi $ assume j, le_infi $ assume hj,
    infi_le_of_le j $ infi_le_of_le hj $ infi_le_of_le i $ infi_le _ hi)
  (le_infi $ assume i, le_infi $ assume hi, le_infi $ assume j, le_infi $ assume hj,
    infi_le_of_le j $ infi_le_of_le hj $ infi_le_of_le i $ infi_le _ hi)

lemma lift_assoc {h : set β → filter γ} (hg : monotone g)  :
  (f.lift g).lift h = f.lift (λs, (g s).lift h) :=
le_antisymm
  (le_infi $ assume s, le_infi $ assume hs, le_infi $ assume t, le_infi $ assume ht,
    infi_le_of_le t $ infi_le _ $ (mem_lift_iff hg).mpr ⟨_, hs, ht⟩)
  (le_infi $ assume t, le_infi $ assume ht,
    let ⟨s, hs, h'⟩ := (mem_lift_iff hg).mp ht in
    infi_le_of_le s $ infi_le_of_le hs $ infi_le_of_le t $ infi_le _ h')

lemma lift_lift_same_le_lift {g : set α → set α → filter β} :
  f.lift (λs, f.lift (g s)) ≤ f.lift (λs, g s s) :=
le_infi $ assume s, le_infi $ assume hs, infi_le_of_le s $ infi_le_of_le hs $ infi_le_of_le s $ infi_le _ hs

lemma lift_lift_same_eq_lift {g : set α → set α → filter β}
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

theorem monotone_lift [preorder γ] {f : γ → filter α} {g : γ → set α → filter β}
  (hf : monotone f) (hg : monotone g) : monotone (λc, (f c).lift (g c)) :=
assume a b h, lift_mono (hf h) (hg h)

lemma lift_neq_bot_iff (hm : monotone g) : (f.lift g ≠ ⊥) ↔ (∀s∈f.sets, g s ≠ ⊥) :=
classical.by_cases
  (assume hn : nonempty β,
    calc f.lift g ≠ ⊥ ↔ (⨅s : { s // s ∈ f.sets}, g s.val) ≠ ⊥ : by simp [filter.lift, infi_subtype]
      ... ↔ (∀s:{ s // s ∈ f.sets}, g s.val ≠ ⊥) :
        infi_neq_bot_iff_of_directed hn
          (assume ⟨a, ha⟩ ⟨b, hb⟩, ⟨⟨a ∩ b, inter_mem_sets ha hb⟩,
            hm $ inter_subset_left _ _, hm $ inter_subset_right _ _⟩)
      ... ↔ (∀s∈f.sets, g s ≠ ⊥) : ⟨assume h s hs, h ⟨s, hs⟩, assume h ⟨s, hs⟩, h s hs⟩)
  (assume hn : ¬ nonempty β,
    have h₁ : f.lift g = ⊥, from filter_eq_bot_of_not_nonempty hn,
    have h₂ : ∀s, g s = ⊥, from assume s, filter_eq_bot_of_not_nonempty hn,
    calc (f.lift g ≠ ⊥) ↔ false : by simp [h₁]
      ... ↔ (∀s∈f.sets, false) : ⟨false.elim, assume h, h univ univ_mem_sets⟩
      ... ↔ (∀s∈f.sets, g s ≠ ⊥) : by simp [h₂])

end

section
protected def lift' (f : filter α) (h : set α → set β) :=
f.lift (principal ∘ h)

variables {f f₁ f₂ : filter α} {h h₁ h₂ : set α → set β}

lemma mem_lift' {t : set α} (ht : t ∈ f.sets) : h t ∈ (f.lift' h).sets :=
le_principal_iff.mp $ show f.lift' h ≤ principal (h t),
  from infi_le_of_le t $ infi_le_of_le ht $ le_refl _

lemma mem_lift'_iff (hh : monotone h) {s : set β} : s ∈ (f.lift' h).sets ↔ (∃t∈f.sets, h t ⊆ s) :=
have monotone (principal ∘ h),
  from assume a b h, principal_mono.mpr $ hh h,
by simp [filter.lift', @mem_lift_iff α β f _ this]

lemma lift'_le {f : filter α} {g : set α → set β} {h : filter β} {s : set α}
  (hs : s ∈ f.sets) (hg : principal (g s) ≤ h) : f.lift' g ≤ h :=
lift_le hs hg

lemma lift'_mono (hf : f₁ ≤ f₂) (hh : h₁ ≤ h₂) : f₁.lift' h₁ ≤ f₂.lift' h₂ :=
lift_mono hf $ assume s, principal_mono.mpr $ hh s

lemma lift'_mono' (hh : ∀s∈f.sets, h₁ s ⊆ h₂ s) : f.lift' h₁ ≤ f.lift' h₂ :=
infi_le_infi $ assume s, infi_le_infi $ assume hs, principal_mono.mpr $ hh s hs

lemma lift'_cong (hh : ∀s∈f.sets, h₁ s = h₂ s) : f.lift' h₁ = f.lift' h₂ :=
le_antisymm (lift'_mono' $ assume s hs, le_of_eq $ hh s hs) (lift'_mono' $ assume s hs, le_of_eq $ (hh s hs).symm)

lemma map_lift'_eq {m : β → γ} (hh : monotone h) : map m (f.lift' h) = f.lift' (image m ∘ h) :=
calc map m (f.lift' h) = f.lift (map m ∘ principal ∘ h) :
    map_lift_eq $ monotone_comp hh monotone_principal
  ... = f.lift' (image m ∘ h) : by simp [function.comp, filter.lift']

lemma map_lift'_eq2 {g : set β → set γ} {m : α → β} (hg : monotone g) :
  (map m f).lift' g = f.lift' (g ∘ image m) :=
map_lift_eq2 $ monotone_comp hg monotone_principal

theorem vmap_lift'_eq {m : γ → β} (hh : monotone h) :
  vmap m (f.lift' h) = f.lift' (preimage m ∘ h) :=
calc vmap m (f.lift' h) = f.lift (vmap m ∘ principal ∘ h) :
    vmap_lift_eq $ monotone_comp hh monotone_principal
  ... = f.lift' (preimage m ∘ h) : by simp [function.comp, filter.lift']

theorem vmap_lift'_eq2 {m : β → α} {g : set β → set γ} (hg : monotone g) :
  (vmap m f).lift' g = f.lift' (g ∘ preimage m) :=
vmap_lift_eq2 $ monotone_comp hg monotone_principal

lemma lift'_principal {s : set α} (hh : monotone h) :
  (principal s).lift' h = principal (h s) :=
lift_principal $ monotone_comp hh monotone_principal

lemma principal_le_lift' {t : set β} (hh : ∀s∈f.sets, t ⊆ h s) :
  principal t ≤ f.lift' h :=
le_infi $ assume s, le_infi $ assume hs, principal_mono.mpr (hh s hs)

theorem monotone_lift' [preorder γ] {f : γ → filter α} {g : γ → set α → set β}
  (hf : monotone f) (hg : monotone g) : monotone (λc, (f c).lift' (g c)) :=
assume a b h, lift'_mono (hf h) (hg h)

lemma lift_lift'_assoc {g : set α → set β} {h : set β → filter γ}
  (hg : monotone g) (hh : monotone h) :
  (f.lift' g).lift h = f.lift (λs, h (g s)) :=
calc (f.lift' g).lift h = f.lift (λs, (principal (g s)).lift h) :
    lift_assoc (monotone_comp hg monotone_principal)
  ... = f.lift (λs, h (g s)) : by simp [lift_principal, hh]

lemma lift'_lift'_assoc {g : set α → set β} {h : set β → set γ}
  (hg : monotone g) (hh : monotone h) :
  (f.lift' g).lift' h = f.lift' (λs, h (g s)) :=
lift_lift'_assoc hg (monotone_comp hh monotone_principal)

lemma lift'_lift_assoc {g : set α → filter β} {h : set β → set γ}
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
    calc filter.lift' f h ⊓ principal s ≤ principal (h t) ⊓ principal s :
        inf_le_inf (infi_le_of_le t $ infi_le _ ht) (le_refl _)
      ... = _ : by simp)
  (le_inf
    (le_infi $ assume t, le_infi $ assume ht,
      infi_le_of_le t $ infi_le_of_le ht $ by simp; exact inter_subset_right _ _)
    (infi_le_of_le univ $ infi_le_of_le univ_mem_sets $ by simp; exact inter_subset_left _ _))

lemma lift'_neq_bot_iff (hh : monotone h) : (f.lift' h ≠ ⊥) ↔ (∀s∈f.sets, h s ≠ ∅) :=
calc (f.lift' h ≠ ⊥) ↔ (∀s∈f.sets, principal (h s) ≠ ⊥) :
    lift_neq_bot_iff (monotone_comp hh monotone_principal)
  ... ↔ (∀s∈f.sets, h s ≠ ∅) : by simp [principal_eq_bot_iff]

@[simp] lemma lift'_id {f : filter α} : f.lift' id = f :=
le_antisymm
  (assume s hs, mem_lift' hs)
  (le_infi $ assume s, le_infi $ assume hs, by simp [hs])

lemma le_lift' {f : filter α} {h : set α → set β} {g : filter β}
  (h_le : ∀s∈f.sets, h s ∈ g.sets) : g ≤ f.lift' h :=
le_infi $ assume s, le_infi $ assume hs, by simp [h_le]; exact h_le s hs

end

end lift

theorem vmap_eq_lift' {f : filter β} {m : α → β} :
  vmap m f = f.lift' (preimage m) :=
filter_eq $ set.ext $ by simp [mem_lift'_iff, monotone_preimage, vmap]

/- product filter -/

/- The product filter cannot be defined using the monad structure on filters. For example:

  F := do {x <- seq, y <- top, return (x, y)}
  hence:
    s ∈ F  <->  ∃n, [n..∞] × univ ⊆ s

  G := do {y <- top, x <- seq, return (x, y)}
  hence:
    s ∈ G  <->  ∀i:ℕ, ∃n, [n..∞] × {i} ⊆ s

  Now ⋃i, [i..∞] × {i}  is in G but not in F.

  As product filter we want to have F as result.
-/

/- Alternative definition of the product:
protected def prod (f : filter α) (g : filter β) : filter (α × β) :=
f.vmap prod.fst ⊓ g.vmap prod.snd

lemma prod_mem_prod {s : set α} {t : set β} {f : filter α} {g : filter β}
  (hs : s ∈ f.sets) (ht : t ∈ g.sets) : set.prod s t ∈ (filter.prod f g).sets :=
inter_mem_inf_sets (preimage_mem_vmap hs) (preimage_mem_vmap ht)

lemma mem_prod_iff {s : set (α×β)} {f : filter α} {g : filter β} :
  s ∈ (filter.prod f g).sets ↔ (∃t₁∈f.sets, ∃t₂∈g.sets, set.prod t₁ t₂ ⊆ s) :=
by simp [filter.prod, mem_inf_sets, mem_vmap];
  exact ⟨assume ⟨t₁', ⟨t₁, ht₁, h₁⟩, t₂', hst, ⟨t₂, ht₂, h₂⟩⟩,
      ⟨t₁, ht₁, t₂, ht₂, subset.trans (inter_subset_inter h₁ h₂) hst⟩,
    assume ⟨t₁, ht₁, t₂, ht₂, h⟩,
      ⟨prod.fst ⁻¹' t₁, ⟨t₁, ht₁, subset.refl _⟩, prod.snd ⁻¹' t₂, h, t₂, ht₂, subset.refl _⟩⟩

#exit
-/

section prod
variables {s : set α} {t : set β} {f : filter α} {g : filter β}

protected def prod (f : filter α) (g : filter β) : filter (α × β) :=
f.lift $ λs, g.lift' $ λt, set.prod s t

lemma prod_mem_prod (hs : s ∈ f.sets) (ht : t ∈ g.sets) : set.prod s t ∈ (filter.prod f g).sets :=
le_principal_iff.mp $ show filter.prod f g ≤ principal (set.prod s t),
  from infi_le_of_le s $ infi_le_of_le hs $ infi_le_of_le t $ infi_le _ ht

lemma prod_same_eq : filter.prod f f = f.lift' (λt, set.prod t t) :=
lift_lift'_same_eq_lift'
  (assume s, set.monotone_prod monotone_const monotone_id)
  (assume t, set.monotone_prod monotone_id monotone_const)

lemma mem_prod_iff {s : set (α×β)} :
  s ∈ (filter.prod f g).sets ↔ (∃t₁∈f.sets, ∃t₂∈g.sets, set.prod t₁ t₂ ⊆ s) :=
begin
  delta filter.prod,
  rw [mem_lift_iff],
  apply exists_congr, intro t₁,
  apply exists_congr, intro ht₁,
  rw [mem_lift'_iff],
  exact set.monotone_prod monotone_const monotone_id,
  exact (monotone_lift' monotone_const $ monotone_lam $ assume b, set.monotone_prod monotone_id monotone_const)
end

lemma prod_def : filter.prod f g = f.vmap prod.fst ⊓ g.vmap prod.snd :=
filter_eq $ set.ext $ assume s,
  begin
    simp [mem_prod_iff, mem_inf_sets],
    exact ⟨assume ⟨t₁, ht₁, t₂, ht₂, h⟩,
        ⟨prod.fst ⁻¹' t₁, ⟨t₁, ht₁, subset.refl _⟩, prod.snd ⁻¹' t₂, h, ⟨t₂, ht₂, subset.refl _⟩⟩,
      assume ⟨t₁, ⟨s₁, hs₁, hts₁⟩, t₂, h, ⟨s₂, hs₂, hts₂⟩⟩,
      ⟨s₁, hs₁, s₂, hs₂, subset.trans (inter_subset_inter hts₁ hts₂) h⟩⟩
  end

lemma prod_infi_left {f : ι → filter α} {g : filter β} (i : ι) :
  filter.prod (⨅i, f i) g = (⨅i, filter.prod (f i) g) :=
by rw [prod_def, vmap_infi, infi_inf i]; simp [prod_def]

lemma prod_infi_right {f : filter α} {g : ι → filter β} (i : ι) :
  filter.prod f (⨅i, g i) = (⨅i, filter.prod f (g i)) :=
by rw [prod_def, vmap_infi, inf_infi i]; simp [prod_def]

lemma mem_prod_same_iff {s : set (α×α)} :
  s ∈ (filter.prod f f).sets ↔ (∃t∈f.sets, set.prod t t ⊆ s) :=
by rw [prod_same_eq, mem_lift'_iff]; exact set.monotone_prod monotone_id monotone_id

lemma prod_mono {f₁ f₂ : filter α} {g₁ g₂ : filter β} (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) :
  filter.prod f₁ g₁ ≤ filter.prod f₂ g₂ :=
lift_mono hf $ assume s, lift'_mono hg $ le_refl _

lemma prod_comm : filter.prod f g = map (λp:β×α, (p.2, p.1)) (filter.prod g f) :=
eq.symm $ calc map (λp:β×α, (p.2, p.1)) (filter.prod g f) =
        (g.lift $ λt, map (λp:β×α, (p.2, p.1)) (f.lift' $ λs, set.prod t s)) :
    map_lift_eq $ assume a b h, lift'_mono (le_refl f) (assume t, set.prod_mono h (subset.refl t))
  ... = (g.lift $ λt, f.lift' $ λs, image (λp:β×α, (p.2, p.1)) (set.prod t s)) :
    congr_arg (filter.lift g) $ funext $ assume s, map_lift'_eq $ assume a b h, set.prod_mono (subset.refl s) h
  ... = (g.lift $ λt, f.lift' $ λs, set.prod s t) : by simp [set.image_swap_prod]
  ... = filter.prod f g : lift_comm

lemma prod_lift_lift {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
  {f₁ : filter α₁} {f₂ : filter α₂} {g₁ : set α₁ → filter β₁} {g₂ : set α₂ → filter β₂}
  (hg₁ : monotone g₁) (hg₂ : monotone g₂) :
  filter.prod (f₁.lift g₁) (f₂.lift g₂) = f₁.lift (λs, f₂.lift (λt, filter.prod (g₁ s) (g₂ t))) :=
begin
  delta filter.prod,
  rw [lift_assoc],
  apply congr_arg, apply funext, intro x,
  rw [lift_comm],
  apply congr_arg, apply funext, intro y,
  rw [lift'_lift_assoc],
  exact hg₂,
  exact hg₁
end

lemma prod_lift'_lift' {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
  {f₁ : filter α₁} {f₂ : filter α₂} {g₁ : set α₁ → set β₁} {g₂ : set α₂ → set β₂}
  (hg₁ : monotone g₁) (hg₂ : monotone g₂) :
  filter.prod (f₁.lift' g₁) (f₂.lift' g₂) = f₁.lift (λs, f₂.lift' (λt, set.prod (g₁ s) (g₂ t))) :=
begin
  delta filter.prod,
  rw [lift_lift'_assoc],
  apply congr_arg, apply funext, intro x,
  rw [lift'_lift'_assoc],
  exact hg₂,
  exact set.monotone_prod monotone_const monotone_id,
  exact hg₁,
  exact (monotone_lift' monotone_const $ monotone_lam $
    assume x, set.monotone_prod monotone_id monotone_const)
end

lemma tendsto_fst {f : filter α} {g : filter β} : tendsto prod.fst (filter.prod f g) f :=
assume s hs, (filter.prod f g).upwards_sets (prod_mem_prod hs univ_mem_sets) $
  show set.prod s univ ⊆ preimage prod.fst s, by simp [set.prod, preimage] {contextual := tt}

lemma tendsto_snd {f : filter α} {g : filter β} : tendsto prod.snd (filter.prod f g) g :=
assume s hs, (filter.prod f g).upwards_sets (prod_mem_prod univ_mem_sets hs) $
  show set.prod univ s ⊆ preimage prod.snd s, by simp [set.prod, preimage] {contextual := tt}

lemma tendsto_prod_mk {f : filter α} {g : filter β} {h : filter γ} {m₁ : α → β} {m₂ : α → γ}
  (h₁ : tendsto m₁ f g) (h₂ : tendsto m₂ f h) : tendsto (λx, (m₁ x, m₂ x)) f (filter.prod g h) :=
assume s hs,
let ⟨s₁, hs₁, s₂, hs₂, h⟩ := mem_prod_iff.mp hs in
f.upwards_sets (inter_mem_sets (h₁ hs₁) (h₂ hs₂)) $
  calc preimage m₁ s₁ ∩ preimage m₂ s₂ ⊆ preimage (λx, (m₁ x, m₂ x)) (set.prod s₁ s₂) : λx ⟨h₁, h₂⟩, ⟨h₁, h₂⟩
    ... ⊆ preimage (λx, (m₁ x, m₂ x)) s : preimage_mono h

lemma prod_map_map_eq {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
  {f₁ : filter α₁} {f₂ : filter α₂} {m₁ : α₁ → β₁} {m₂ : α₂ → β₂} :
  filter.prod (map m₁ f₁) (map m₂ f₂) = map (λp:α₁×α₂, (m₁ p.1, m₂ p.2)) (filter.prod f₁ f₂) :=
le_antisymm
  (assume s hs,
    let ⟨s₁, hs₁, s₂, hs₂, h⟩ := mem_prod_iff.mp hs in
    filter.upwards_sets _ (prod_mem_prod (image_mem_map hs₁) (image_mem_map hs₂)) $
      calc set.prod (m₁ '' s₁) (m₂ '' s₂) = (λp:α₁×α₂, (m₁ p.1, m₂ p.2)) '' set.prod s₁ s₂ :
          set.prod_image_image_eq
        ... ⊆ _ : by rwa [image_subset_iff])
  (tendsto_prod_mk (tendsto_compose tendsto_fst (le_refl _)) (tendsto_compose tendsto_snd (le_refl _)))

lemma prod_vmap_vmap_eq {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
  {f₁ : filter α₁} {f₂ : filter α₂} {m₁ : β₁ → α₁} {m₂ : β₂ → α₂} :
  filter.prod (vmap m₁ f₁) (vmap m₂ f₂) = vmap (λp:β₁×β₂, (m₁ p.1, m₂ p.2)) (filter.prod f₁ f₂) :=
have ∀s t, set.prod (preimage m₁ s) (preimage m₂ t) = preimage (λp:β₁×β₂, (m₁ p.1, m₂ p.2)) (set.prod s t),
  from assume s t, rfl,
begin
  rw [vmap_eq_lift', vmap_eq_lift', prod_lift'_lift'],
  simp [this, filter.prod],
  rw [vmap_lift_eq], tactic.swap, exact (monotone_lift' monotone_const $
    monotone_lam $ assume t, set.monotone_prod monotone_id monotone_const),
  apply congr_arg, apply funext, intro t',
  dsimp [function.comp],
  rw [vmap_lift'_eq],
  exact set.monotone_prod monotone_const monotone_id,
  exact monotone_preimage,
  exact monotone_preimage
end

lemma prod_inf_prod {f₁ f₂ : filter α} {g₁ g₂ : filter β} :
  filter.prod f₁ g₁ ⊓ filter.prod f₂ g₂ = filter.prod (f₁ ⊓ f₂) (g₁ ⊓ g₂) :=
le_antisymm
  (le_infi $ assume s, le_infi $ assume hs, le_infi $ assume t, le_infi $ assume ht,
  begin
    revert s hs t ht,
    simp,
    exact assume s s₁ hs₁ s₂ hs₂ hs t t₁ ht₁ t₂ ht₂ ht,
      ⟨set.prod s₁ t₁, prod_mem_prod hs₁ ht₁, set.prod s₂ t₂, prod_mem_prod hs₂ ht₂,
      by rw [set.prod_inter_prod]; exact set.prod_mono hs ht⟩
  end)
  (le_inf (prod_mono inf_le_left inf_le_left) (prod_mono inf_le_right inf_le_right))

lemma prod_neq_bot {f : filter α} {g : filter β} :
  filter.prod f g ≠ ⊥ ↔ (f ≠ ⊥ ∧ g ≠ ⊥) :=
calc filter.prod f g ≠ ⊥ ↔ (∀s∈f.sets, g.lift' (set.prod s) ≠ ⊥) :
  begin
    delta filter.prod,
    rw [lift_neq_bot_iff],
    exact (monotone_lift' monotone_const $ monotone_lam $ assume s, set.monotone_prod monotone_id monotone_const)
  end
  ... ↔ (∀s∈f.sets, ∀t∈g.sets, s ≠ ∅ ∧ t ≠ ∅) :
  begin
    apply forall_congr, intro s,
    apply forall_congr, intro hs,
    rw [lift'_neq_bot_iff],
    apply forall_congr, intro t,
    apply forall_congr, intro ht,
    rw [set.prod_neq_empty_iff],
    exact set.monotone_prod monotone_const monotone_id
  end
  ... ↔ (∀s∈f.sets, s ≠ ∅) ∧ (∀t∈g.sets, t ≠ ∅) :
    ⟨assume h, ⟨assume s hs, (h s hs univ univ_mem_sets).left,
        assume t ht, (h univ univ_mem_sets t ht).right⟩,
      assume ⟨h₁, h₂⟩ s hs t ht, ⟨h₁ s hs, h₂ t ht⟩⟩
  ... ↔ _ : by simp [forall_sets_neq_empty_iff_neq_bot]

lemma prod_principal_principal {s : set α} {t : set β} :
  filter.prod (principal s) (principal t) = principal (set.prod s t) :=
begin
  delta filter.prod,
  rw [lift_principal, lift'_principal],
  exact set.monotone_prod monotone_const monotone_id,
  exact (monotone_lift' monotone_const $ monotone_lam $
    assume s, set.monotone_prod monotone_id monotone_const)
end

end prod

lemma mem_infi_sets {f : ι → filter α} (i : ι) : ∀{s}, s ∈ (f i).sets → s ∈ (⨅i, f i).sets :=
show (⨅i, f i) ≤ f i, from infi_le _ _

@[elab_as_eliminator]
lemma infi_sets_induct {f : ι → filter α} {s : set α} (hs : s ∈ (infi f).sets) {p : set α → Prop}
  (uni : p univ)
  (ins : ∀{i s₁ s₂}, s₁ ∈ (f i).sets → p s₂ → p (s₁ ∩ s₂))
  (upw : ∀{s₁ s₂}, s₁ ⊆ s₂ → p s₁ → p s₂) : p s :=
begin
  have hs' : s ∈ (complete_lattice.Inf {a : filter α | ∃ (i : ι), a = f i}).sets := hs,
  rw [Inf_sets_eq_finite] at hs',
  simp at hs',
  cases hs' with is hs, cases hs with fin_is hs, cases hs with hs his,
  induction fin_is generalizing s,
  case finite.empty hs' s hs' hs {
    simp at hs, subst hs, assumption },
  case finite.insert fi is fi_ne_is fin_is ih fi_sub s hs' hs {
    simp at hs,
    cases hs with s₁ hs, cases hs with hs₁ hs, cases hs with s₂ hs, cases hs with hs hs₂,
    have hi : ∃i, fi = f i := fi_sub (mem_insert _ _),
    cases hi with i hi,
    exact have hs₁ : s₁ ∈ (f i).sets, from hi ▸ hs₁,
    have hs₂ : p s₂, from
      have his : is ⊆ {x | ∃i, x = f i}, from assume i hi, fi_sub $  mem_insert_of_mem _ hi,
      have infi f ≤ Inf is, from Inf_le_Inf his,
      ih his (this hs₂) hs₂,
    show p s, from upw hs $ ins hs₁ hs₂ }
end

lemma lift_infi {f : ι → filter α} {g : set α → filter β}
  (hι : nonempty ι) (hg : ∀{s t}, g s ⊓ g t = g (s ∩ t)) : (infi f).lift g = (⨅i, (f i).lift g) :=
le_antisymm
  (le_infi $ assume i, lift_mono (infi_le _ _) (le_refl _))
  (assume s,
    have g_mono : monotone g,
      from assume s t h, le_of_inf_eq $ eq.trans hg $ congr_arg g $ inter_eq_self_of_subset_left h,
    have ∀t∈(infi f).sets, (⨅ (i : ι), filter.lift (f i) g) ≤ g t,
      from assume t ht, infi_sets_induct ht
        (let ⟨i⟩ := hι in infi_le_of_le i $ infi_le_of_le univ $ infi_le _ univ_mem_sets)
        (assume i s₁ s₂ hs₁ hs₂,
          @hg s₁ s₂ ▸ le_inf (infi_le_of_le i $ infi_le_of_le s₁ $ infi_le _ hs₁) hs₂)
        (assume s₁ s₂ hs₁ hs₂, le_trans hs₂ $ g_mono hs₁),
    by rw [lift_sets_eq g_mono]; simp; exact assume t hs ht, this t ht hs)

lemma lift_infi' {f : ι → filter α} {g : set α → filter β}
  (hι : nonempty ι) (hf : directed (≤) f) (hg : monotone g) : (infi f).lift g = (⨅i, (f i).lift g) :=
le_antisymm
  (le_infi $ assume i, lift_mono (infi_le _ _) (le_refl _))
  (assume s,
  begin
    rw [lift_sets_eq hg],
    simp [infi_sets_eq hf hι],
    exact assume t hs i ht, mem_infi_sets i $ mem_lift ht hs
  end)

lemma lift'_infi {f : ι → filter α} {g : set α → set β}
  (hι : nonempty ι) (hg : ∀{s t}, g s ∩ g t = g (s ∩ t)) : (infi f).lift' g = (⨅i, (f i).lift' g) :=
lift_infi hι $ by simp; apply assume s t, hg

lemma map_eq_vmap_of_inverse {f : filter α} {m : α → β} {n : β → α}
  (h₁ : m ∘ n = id) (h₂ : n ∘ m = id) : map m f = vmap n f :=
le_antisymm
  (assume b ⟨a, ha, (h : preimage n a ⊆ b)⟩, f.upwards_sets ha $
    calc a = preimage (n ∘ m) a : by simp [h₂, preimage_id]
      ... ⊆ preimage m b : preimage_mono h)
  (assume b (hb : preimage m b ∈ f.sets),
    ⟨preimage m b, hb, show preimage (m ∘ n) b ⊆ b, by simp [h₁]; apply subset.refl⟩)

lemma map_swap_vmap_swap_eq {f : filter (α × β)} : prod.swap <$> f = vmap prod.swap f :=
map_eq_vmap_of_inverse prod.swap_swap_eq prod.swap_swap_eq

/- at_top and at_bot -/

def at_top [preorder α] : filter α := ⨅ a, principal {b | a ≤ b}
def at_bot [preorder α] : filter α := ⨅ a, principal {b | b ≤ a}

lemma mem_at_top [preorder α] (a : α) : {b : α | a ≤ b} ∈ (@at_top α _).sets :=
mem_infi_sets a $ subset.refl _

@[simp] lemma at_top_ne_bot [inhabited α] [semilattice_sup α] : (at_top : filter α) ≠ ⊥ :=
infi_neq_bot_of_directed (by apply_instance)
  (assume a b, ⟨a ⊔ b, by simp {contextual := tt}⟩)
  (assume a, by simp [principal_eq_bot_iff]; exact ne_empty_of_mem (le_refl a))

lemma mem_at_top_iff [inhabited α] [semilattice_sup α] {s : set α} :
  s ∈ (at_top : filter α).sets ↔ (∃a:α, ∀b≥a, b ∈ s) :=
iff.intro
  (assume h, infi_sets_induct h ⟨default α, by simp⟩
    (assume a s₁ s₂ ha ⟨b, hb⟩, ⟨a ⊔ b,
      assume c hc, ⟨ha $ le_trans le_sup_left hc, hb _ $ le_trans le_sup_right hc⟩⟩)
    (assume s₁ s₂ h ⟨a, ha⟩, ⟨a, assume b hb, h $ ha _ hb⟩))
  (assume ⟨a, h⟩, mem_infi_sets a $ assume x, h x)

lemma map_at_top_eq [inhabited α] [semilattice_sup α] {f : α → β} :
  at_top.map f = (⨅a, principal $ f '' {a' | a ≤ a'}) :=
calc map f (⨅a, principal {a' | a ≤ a'}) = (⨅a, map f $ principal {a' | a ≤ a'}) :
    map_infi_eq (assume a b, ⟨a ⊔ b, by simp {contextual := tt}⟩) ⟨default α⟩
  ... = (⨅a, principal $ f '' {a' | a ≤ a'}) : by simp

lemma tendsto_finset_image_at_top_at_top {i : β → γ} {j : γ → β} (h : ∀x, j (i x) = x) :
  tendsto (λs:finset γ, s.image j) at_top at_top :=
tendsto_infi $ assume s, tendsto_infi' (s.image i) $ tendsto_principal_principal $
  assume t (ht : s.image i ⊆ t),
  calc s = (s.image i).image j :
      by simp [finset.image_image, (∘), h]; exact finset.image_id.symm
    ... ⊆  t.image j : finset.image_subset_image ht


/- ultrafilter -/

section ultrafilter
open classical zorn
local attribute [instance] prop_decidable

variables {f g : filter α}

def ultrafilter (f : filter α) := f ≠ ⊥ ∧ ∀g, g ≠ ⊥ → g ≤ f → f ≤ g

lemma ultrafilter_pure {a : α} : ultrafilter (pure a) :=
⟨return_neq_bot,
  assume g hg ha,
  have {a} ∈ g.sets, by simp at ha; assumption,
  show ∀s∈g.sets, {a} ⊆ s, from classical.by_contradiction $
  begin
    simp [classical.not_forall, not_imp],
    exact assume s hna hs,
      have {a} ∩ s ∈ g.sets, from inter_mem_sets ‹{a} ∈ g.sets› hs,
      have ∅ ∈ g.sets, from g.upwards_sets this $
        assume x ⟨hxa, hxs⟩, begin simp at hxa; simp [hxa] at hxs, exact hna hxs end,
      have g = ⊥, from empty_in_sets_eq_bot.mp this,
      hg this
  end⟩

lemma ultrafilter_unique (hg : ultrafilter g) (hf : f ≠ ⊥) (h : f ≤ g) : f = g :=
le_antisymm h (hg.right _ hf h)

lemma exists_ultrafilter (h : f ≠ ⊥) : ∃u, u ≤ f ∧ ultrafilter u :=
let
  τ                := {f' // f' ≠ ⊥ ∧ f' ≤ f},
  r : τ → τ → Prop := λt₁ t₂, t₂.val ≤ t₁.val,
  ⟨a, ha⟩          := inhabited_of_mem_sets h univ_mem_sets,
  top : τ          := ⟨f, h, le_refl f⟩,
  sup : Π(c:set τ), chain c → τ :=
    λc hc, ⟨⨅a:{a:τ // a ∈ insert top c}, a.val.val,
      infi_neq_bot_of_directed ⟨a⟩
        (directed_of_chain $ chain_insert hc $ assume ⟨b, _, hb⟩ _ _, or.inl hb)
        (assume ⟨⟨a, ha, _⟩, _⟩, ha),
      infi_le_of_le ⟨top, mem_insert _ _⟩ (le_refl _)⟩
in
have ∀c (hc: chain c) a (ha : a ∈ c), r a (sup c hc),
  from assume c hc a ha, infi_le_of_le ⟨a, mem_insert_of_mem _ ha⟩ (le_refl _),
have (∃ (u : τ), ∀ (a : τ), r u a → r a u),
  from zorn (assume c hc, ⟨sup c hc, this c hc⟩) (assume f₁ f₂ f₃ h₁ h₂, le_trans h₂ h₁),
let ⟨uτ, hmin⟩ := this in
⟨uτ.val, uτ.property.right, uτ.property.left, assume g hg₁ hg₂,
  hmin ⟨g, hg₁, le_trans hg₂ uτ.property.right⟩ hg₂⟩

lemma le_of_ultrafilter {g : filter α} (hf : ultrafilter f) (h : f ⊓ g ≠ ⊥) :
  f ≤ g :=
le_of_inf_eq $ ultrafilter_unique hf h inf_le_left

lemma mem_or_compl_mem_of_ultrafilter (hf : ultrafilter f) (s : set α) :
  s ∈ f.sets ∨ - s ∈ f.sets :=
or_iff_not_imp_right.2 $ assume : - s ∉ f.sets,
  have f ≤ principal s,
    from le_of_ultrafilter hf $ assume h, this $ mem_sets_of_neq_bot $ by simp [*],
  by simp at this; assumption

lemma mem_or_mem_of_ultrafilter {s t : set α} (hf : ultrafilter f) (h : s ∪ t ∈ f.sets) :
  s ∈ f.sets ∨ t ∈ f.sets :=
(mem_or_compl_mem_of_ultrafilter hf s).imp_right
  (assume : -s ∈ f.sets, f.upwards_sets (inter_mem_sets this h) $
    assume x ⟨hnx, hx⟩, hx.resolve_left hnx)

lemma mem_of_finite_sUnion_ultrafilter {s : set (set α)} (hf : ultrafilter f) (hs : finite s)
  : ⋃₀ s ∈ f.sets → ∃t∈s, t ∈ f.sets :=
begin
  induction hs,
  case finite.empty { simp [empty_in_sets_eq_bot, hf.left] },
  case finite.insert t s' ht' hs' ih {
    simp,
    exact assume h, (mem_or_mem_of_ultrafilter hf h).elim
      (assume : t ∈ f.sets, ⟨t, this, or.inl rfl⟩)
      (assume h, let ⟨t, hts', ht⟩ := ih h in ⟨t, ht, or.inr hts'⟩) }
end

lemma mem_of_finite_Union_ultrafilter {is : set β} {s : β → set α}
  (hf : ultrafilter f) (his : finite is) (h : (⋃i∈is, s i) ∈ f.sets) : ∃i∈is, s i ∈ f.sets :=
have his : finite (image s is), from finite_image his,
have h : (⋃₀ image s is) ∈ f.sets, from by simp [sUnion_image]; assumption,
let ⟨t, ⟨i, hi, h_eq⟩, (ht : t ∈ f.sets)⟩ := mem_of_finite_sUnion_ultrafilter hf his h in
⟨i, hi, h_eq.symm ▸ ht⟩

lemma ultrafilter_of_split {f : filter α} (hf : f ≠ ⊥) (h : ∀s, s ∈ f.sets ∨ - s ∈ f.sets) :
  ultrafilter f :=
⟨hf, assume g hg g_le s hs, (h s).elim id $
  assume : - s ∈ f.sets,
  have s ∩ -s ∈ g.sets, from inter_mem_sets hs (g_le this),
  by simp [empty_in_sets_eq_bot, hg] at this; contradiction⟩

lemma ultrafilter_map {f : filter α} {m : α → β} (h : ultrafilter f) : ultrafilter (map m f) :=
ultrafilter_of_split (by simp [map_eq_bot_iff, h.left]) $
  assume s, show preimage m s ∈ f.sets ∨ - preimage m s ∈ f.sets,
    from mem_or_compl_mem_of_ultrafilter h (preimage m s)

noncomputable def ultrafilter_of (f : filter α) : filter α :=
if h : f = ⊥ then ⊥ else epsilon (λu, u ≤ f ∧ ultrafilter u)

lemma ultrafilter_of_spec (h : f ≠ ⊥) : ultrafilter_of f ≤ f ∧ ultrafilter (ultrafilter_of f) :=
begin
  have h' := epsilon_spec (exists_ultrafilter h),
  simp [ultrafilter_of, dif_neg, h],
  simp at h',
  assumption
end

lemma ultrafilter_of_le : ultrafilter_of f ≤ f :=
if h : f = ⊥ then by simp [ultrafilter_of, dif_pos, h]; exact le_refl _
  else (ultrafilter_of_spec h).left

lemma ultrafilter_ultrafilter_of (h : f ≠ ⊥) : ultrafilter (ultrafilter_of f) :=
(ultrafilter_of_spec h).right

lemma ultrafilter_of_ultrafilter (h : ultrafilter f) : ultrafilter_of f = f :=
ultrafilter_unique h (ultrafilter_ultrafilter_of h.left).left ultrafilter_of_le

end ultrafilter

end filter
