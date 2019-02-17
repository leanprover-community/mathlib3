/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad

Theory of filters on sets.
-/
import order.galois_connection order.zorn
import data.set.finite data.list data.pfun
import algebra.pi_instances
import category.applicative
open lattice set

universes u v w x y

local attribute [instance] classical.prop_decidable

namespace lattice
variables {α : Type u} {ι : Sort v}

def complete_lattice.copy (c : complete_lattice α)
  (le : α → α → Prop) (eq_le : le = @complete_lattice.le α c)
  (top : α) (eq_top : top = @complete_lattice.top α c)
  (bot : α) (eq_bot : bot = @complete_lattice.bot α c)
  (sup : α → α → α) (eq_sup : sup = @complete_lattice.sup α c)
  (inf : α → α → α) (eq_inf : inf = @complete_lattice.inf α c)
  (Sup : set α → α) (eq_Sup : Sup = @complete_lattice.Sup α c)
  (Inf : set α → α) (eq_Inf : Inf = @complete_lattice.Inf α c) :
  complete_lattice α :=
begin
  refine { le := le, top := top, bot := bot, sup := sup, inf := inf, Sup := Sup, Inf := Inf, ..};
    subst_vars,
  exact @complete_lattice.le_refl α c,
  exact @complete_lattice.le_trans α c,
  exact @complete_lattice.le_antisymm α c,
  exact @complete_lattice.le_sup_left α c,
  exact @complete_lattice.le_sup_right α c,
  exact @complete_lattice.sup_le α c,
  exact @complete_lattice.inf_le_left α c,
  exact @complete_lattice.inf_le_right α c,
  exact @complete_lattice.le_inf α c,
  exact @complete_lattice.le_top α c,
  exact @complete_lattice.bot_le α c,
  exact @complete_lattice.le_Sup α c,
  exact @complete_lattice.Sup_le α c,
  exact @complete_lattice.Inf_le α c,
  exact @complete_lattice.le_Inf α c
end

end lattice

open set lattice

section order
variables {α : Type u} (r : α → α → Prop)
local infix `≼` : 50 := r

lemma directed_on_Union {r} {ι : Sort v} {f : ι → set α} (hd : directed (⊆) f)
  (h : ∀x, directed_on r (f x)) : directed_on r (⋃x, f x) :=
by simp only [directed_on, exists_prop, mem_Union, exists_imp_distrib]; exact
assume a₁ b₁ fb₁ a₂ b₂ fb₂,
let ⟨z, zb₁, zb₂⟩ := hd b₁ b₂,
    ⟨x, xf, xa₁, xa₂⟩ := h z a₁ (zb₁ fb₁) a₂ (zb₂ fb₂) in
⟨x, ⟨z, xf⟩, xa₁, xa₂⟩

end order

theorem directed_of_chain {α β r} [is_refl β r] {f : α → β} {c : set α}
  (h : zorn.chain (f ⁻¹'o r) c) :
  directed r (λx:{a:α // a ∈ c}, f (x.val)) :=
assume ⟨a, ha⟩ ⟨b, hb⟩, classical.by_cases
  (assume : a = b, by simp only [this, exists_prop, and_self, subtype.exists];
    exact ⟨b, hb, refl _⟩)
  (assume : a ≠ b, (h a ha b hb this).elim
    (λ h : r (f a) (f b), ⟨⟨b, hb⟩, h, refl _⟩)
    (λ h : r (f b) (f a), ⟨⟨a, ha⟩, refl _, h⟩))

structure filter (α : Type*) :=
(sets                   : set (set α))
(univ_sets              : set.univ ∈ sets)
(sets_of_superset {x y} : x ∈ sets → x ⊆ y → y ∈ sets)
(inter_sets {x y}       : x ∈ sets → y ∈ sets → x ∩ y ∈ sets)

namespace filter
variables {α : Type u} {f g : filter α} {s t : set α}

lemma filter_eq : ∀{f g : filter α}, f.sets = g.sets → f = g
| ⟨a, _, _, _⟩ ⟨._, _, _, _⟩ rfl := rfl

lemma filter_eq_iff : f = g ↔ f.sets = g.sets :=
⟨congr_arg _, filter_eq⟩

protected lemma ext_iff : f = g ↔ ∀ s, s ∈ f.sets ↔ s ∈ g.sets :=
by rw [filter_eq_iff, ext_iff]

@[extensionality]
protected lemma ext : (∀ s, s ∈ f.sets ↔ s ∈ g.sets) → f = g :=
filter.ext_iff.2

lemma univ_mem_sets : univ ∈ f.sets :=
f.univ_sets

lemma mem_sets_of_superset : ∀{x y : set α}, x ∈ f.sets → x ⊆ y → y ∈ f.sets :=
f.sets_of_superset

lemma inter_mem_sets : ∀{s t}, s ∈ f.sets → t ∈ f.sets → s ∩ t ∈ f.sets :=
f.inter_sets

lemma univ_mem_sets' (h : ∀ a, a ∈ s): s ∈ f.sets :=
mem_sets_of_superset univ_mem_sets (assume x _, h x)

lemma mp_sets (hs : s ∈ f.sets) (h : {x | x ∈ s → x ∈ t} ∈ f.sets) : t ∈ f.sets :=
mem_sets_of_superset (inter_mem_sets hs h) $ assume x ⟨h₁, h₂⟩, h₂ h₁

lemma Inter_mem_sets {β : Type v} {s : β → set α} {is : set β} (hf : finite is) :
  (∀i∈is, s i ∈ f.sets) → (⋂i∈is, s i) ∈ f.sets :=
finite.induction_on hf
  (assume hs, by simp only [univ_mem_sets, mem_empty_eq, Inter_neg, Inter_univ, not_false_iff])
  (assume i is _ hf hi hs,
    have h₁ : s i ∈ f.sets, from hs i (by simp),
    have h₂ : (⋂x∈is, s x) ∈ f.sets, from hi $ assume a ha, hs _ $ by simp only [ha, mem_insert_iff, or_true],
    by simp [inter_mem_sets h₁ h₂])

lemma exists_sets_subset_iff : (∃t∈f.sets, t ⊆ s) ↔ s ∈ f.sets :=
⟨assume ⟨t, ht, ts⟩, mem_sets_of_superset ht ts, assume hs, ⟨s, hs, subset.refl _⟩⟩

lemma monotone_mem_sets {f : filter α} : monotone (λs, s ∈ f.sets) :=
assume s t hst h, mem_sets_of_superset h hst

end filter

namespace tactic.interactive
open tactic interactive

/-- `filter_upwards [h1, ⋯, hn]` replaces a goal of the form `s ∈ f.sets`
and terms `h1 : t1 ∈ f.sets, ⋯, hn : tn ∈ f.sets` with `∀x, x ∈ t1 → ⋯ → x ∈ tn → x ∈ s`.

`filter_upwards [h1, ⋯, hn] e` is a short form for `{ filter_upwards [h1, ⋯, hn], exact e }`.
-/
meta def filter_upwards
  (s : parse types.pexpr_list)
  (e' : parse $ optional types.texpr) : tactic unit :=
do
  s.reverse.mmap (λ e, eapplyc `filter.mp_sets >> eapply e),
  eapplyc `filter.univ_mem_sets',
  match e' with
  | some e := interactive.exact e
  | none := skip
  end

end tactic.interactive

namespace filter
variables {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x}

section principal

/-- The principal filter of `s` is the collection of all supersets of `s`. -/
def principal (s : set α) : filter α :=
{ sets             := {t | s ⊆ t},
  univ_sets        := subset_univ s,
  sets_of_superset := assume x y hx hy, subset.trans hx hy,
  inter_sets       := assume x y, subset_inter }

instance : inhabited (filter α) :=
⟨principal ∅⟩

@[simp] lemma mem_principal_sets {s t : set α} : s ∈ (principal t).sets ↔ t ⊆ s := iff.rfl

lemma mem_principal_self (s : set α) : s ∈ (principal s).sets := subset.refl _

end principal

section join

/-- The join of a filter of filters is defined by the relation `s ∈ join f ↔ {t | s ∈ t} ∈ f`. -/
def join (f : filter (filter α)) : filter α :=
{ sets             := {s | {t : filter α | s ∈ t.sets} ∈ f.sets},
  univ_sets        := by simp only [univ_mem_sets, mem_set_of_eq]; exact univ_mem_sets,
  sets_of_superset := assume x y hx xy,
    mem_sets_of_superset hx $ assume f h, mem_sets_of_superset h xy,
  inter_sets       := assume x y hx hy,
    mem_sets_of_superset (inter_mem_sets hx hy) $ assume f ⟨h₁, h₂⟩, inter_mem_sets h₁ h₂ }

@[simp] lemma mem_join_sets {s : set α} {f : filter (filter α)} :
  s ∈ (join f).sets ↔ {t | s ∈ filter.sets t} ∈ f.sets := iff.rfl

end join

section lattice

instance : partial_order (filter α) :=
{ le            := λf g, g.sets ⊆ f.sets,
  le_antisymm   := assume a b h₁ h₂, filter_eq $ subset.antisymm h₂ h₁,
  le_refl       := assume a, subset.refl _,
  le_trans      := assume a b c h₁ h₂, subset.trans h₂ h₁ }

theorem le_def {f g : filter α} : f ≤ g ↔ ∀ x ∈ g.sets, x ∈ f.sets := iff.rfl

/-- `generate_sets g s`: `s` is in the filter closure of `g`. -/
inductive generate_sets (g : set (set α)) : set α → Prop
| basic {s : set α}      : s ∈ g → generate_sets s
| univ {}                : generate_sets univ
| superset {s t : set α} : generate_sets s → s ⊆ t → generate_sets t
| inter {s t : set α}    : generate_sets s → generate_sets t → generate_sets (s ∩ t)

/-- `generate g` is the smallest filter containing the sets `g`. -/
def generate (g : set (set α)) : filter α :=
{ sets             := {s | generate_sets g s},
  univ_sets        := generate_sets.univ,
  sets_of_superset := assume x y, generate_sets.superset,
  inter_sets       := assume s t, generate_sets.inter }

lemma sets_iff_generate {s : set (set α)} {f : filter α} : f ≤ filter.generate s ↔ s ⊆ f.sets :=
iff.intro
  (assume h u hu, h $ generate_sets.basic $ hu)
  (assume h u hu, hu.rec_on h univ_mem_sets
    (assume x y _ hxy hx, mem_sets_of_superset hx hxy)
    (assume x y _ _ hx hy, inter_mem_sets hx hy))

protected def mk_of_closure (s : set (set α)) (hs : (generate s).sets = s) : filter α :=
{ sets             := s,
  univ_sets        := hs ▸ univ_mem_sets,
  sets_of_superset := assume x y, hs ▸ mem_sets_of_superset,
  inter_sets       := assume x y, hs ▸ inter_mem_sets }

lemma mk_of_closure_sets {s : set (set α)} {hs : (generate s).sets = s} :
  filter.mk_of_closure s hs = generate s :=
filter.ext $ assume u, hs.symm ▸ iff.refl _

/- Galois insertion from sets of sets into a filters. -/
def gi_generate (α : Type*) :
  @galois_insertion (set (set α)) (order_dual (filter α)) _ _ filter.generate filter.sets :=
{ gc        := assume s f, sets_iff_generate,
  le_l_u    := assume f u, generate_sets.basic,
  choice    := λs hs, filter.mk_of_closure s (le_antisymm hs $ sets_iff_generate.1 $ le_refl _),
  choice_eq := assume s hs, mk_of_closure_sets }

/-- The infimum of filters is the filter generated by intersections
  of elements of the two filters. -/
instance : has_inf (filter α) := ⟨λf g : filter α,
{ sets             := {s | ∃ (a ∈ f.sets) (b ∈ g.sets), a ∩ b ⊆ s },
  univ_sets        := ⟨_, univ_mem_sets, _, univ_mem_sets, inter_subset_left _ _⟩,
  sets_of_superset := assume x y ⟨a, ha, b, hb, h⟩ xy, ⟨a, ha, b, hb, subset.trans h xy⟩,
  inter_sets       := assume x y ⟨a, ha, b, hb, hx⟩ ⟨c, hc, d, hd, hy⟩,
    ⟨_, inter_mem_sets ha hc, _, inter_mem_sets hb hd,
      calc a ∩ c ∩ (b ∩ d) = (a ∩ b) ∩ (c ∩ d) : by ac_refl
        ... ⊆ x ∩ y : inter_subset_inter hx hy⟩ }⟩

@[simp] lemma mem_inf_sets {f g : filter α} {s : set α} :
  s ∈ (f ⊓ g).sets ↔ ∃t₁∈f.sets, ∃t₂∈g.sets, t₁ ∩ t₂ ⊆ s := iff.rfl

lemma mem_inf_sets_of_left {f g : filter α} {s : set α} (h : s ∈ f.sets) : s ∈ (f ⊓ g).sets :=
⟨s, h, univ, univ_mem_sets, inter_subset_left _ _⟩

lemma mem_inf_sets_of_right {f g : filter α} {s : set α} (h : s ∈ g.sets) : s ∈ (f ⊓ g).sets :=
⟨univ, univ_mem_sets, s, h, inter_subset_right _ _⟩

lemma inter_mem_inf_sets {α : Type u} {f g : filter α} {s t : set α}
  (hs : s ∈ f.sets) (ht : t ∈ g.sets) : s ∩ t ∈ (f ⊓ g).sets :=
inter_mem_sets (mem_inf_sets_of_left hs) (mem_inf_sets_of_right ht)

instance : has_top (filter α) :=
⟨{ sets            := {s | ∀x, x ∈ s},
  univ_sets        := assume x, mem_univ x,
  sets_of_superset := assume x y hx hxy a, hxy (hx a),
  inter_sets       := assume x y hx hy a, mem_inter (hx _) (hy _) }⟩

lemma mem_top_sets_iff_forall {s : set α} : s ∈ (⊤ : filter α).sets ↔ (∀x, x ∈ s) :=
iff.refl _

@[simp] lemma mem_top_sets {s : set α} : s ∈ (⊤ : filter α).sets ↔ s = univ :=
by rw [mem_top_sets_iff_forall, eq_univ_iff_forall]

section complete_lattice

/- We lift the complete lattice along the Galois connection `generate` / `sets`. Unfortunately,
  we want to have different definitional equalities for the lattice operations. So we define them
  upfront and change the lattice operations for the complete lattice instance. -/

private def original_complete_lattice : complete_lattice (filter α) :=
@order_dual.lattice.complete_lattice _ (gi_generate α).lift_complete_lattice

local attribute [instance] original_complete_lattice

instance : complete_lattice (filter α) := original_complete_lattice.copy
  /- le  -/ filter.partial_order.le rfl
  /- top -/ (filter.lattice.has_top).1
  (top_unique $ assume s hs, (eq_univ_of_forall hs).symm ▸ univ_mem_sets)
  /- bot -/ _ rfl
  /- sup -/ _ rfl
  /- inf -/ (filter.lattice.has_inf).1
  begin
    ext f g : 2,
    exact le_antisymm
      (le_inf (assume s, mem_inf_sets_of_left) (assume s, mem_inf_sets_of_right))
      (assume s ⟨a, ha, b, hb, hs⟩, mem_sets_of_superset (inter_mem_sets
        (@inf_le_left (filter α) _ _ _ _ ha)
        (@inf_le_right (filter α) _ _ _ _ hb)) hs)
  end
  /- Sup -/ (join ∘ principal) (by ext s x; exact (@mem_bInter_iff _ _ s filter.sets x).symm)
  /- Inf -/ _ rfl

end complete_lattice

lemma bot_sets_eq : (⊥ : filter α).sets = univ := rfl

lemma sup_sets_eq {f g : filter α} : (f ⊔ g).sets = f.sets ∩ g.sets :=
(gi_generate α).gc.u_inf

lemma Sup_sets_eq {s : set (filter α)} : (Sup s).sets = (⋂f∈s, (f:filter α).sets) :=
(gi_generate α).gc.u_Inf

lemma supr_sets_eq {f : ι → filter α} : (supr f).sets = (⋂i, (f i).sets) :=
(gi_generate α).gc.u_infi

lemma generate_empty : filter.generate ∅ = (⊤ : filter α) :=
(gi_generate α).gc.l_bot

lemma generate_univ : filter.generate univ = (⊥ : filter α) :=
mk_of_closure_sets.symm

lemma generate_union {s t : set (set α)} :
  filter.generate (s ∪ t) = filter.generate s ⊓ filter.generate t :=
(gi_generate α).gc.l_sup

lemma generate_Union {s : ι → set (set α)} :
  filter.generate (⋃ i, s i) = (⨅ i, filter.generate (s i)) :=
(gi_generate α).gc.l_supr

@[simp] lemma mem_bot_sets {s : set α} : s ∈ (⊥ : filter α).sets :=
trivial

@[simp] lemma mem_sup_sets {f g : filter α} {s : set α} :
  s ∈ (f ⊔ g).sets ↔ s ∈ f.sets ∧ s ∈ g.sets :=
iff.rfl

@[simp] lemma mem_Sup_sets {x : set α} {s : set (filter α)} :
  x ∈ (Sup s).sets ↔ (∀f∈s, x ∈ (f:filter α).sets) :=
iff.rfl

@[simp] lemma mem_supr_sets {x : set α} {f : ι → filter α} :
  x ∈ (supr f).sets ↔ (∀i, x ∈ (f i).sets) :=
by simp only [supr_sets_eq, iff_self, mem_Inter]

@[simp] lemma le_principal_iff {s : set α} {f : filter α} : f ≤ principal s ↔ s ∈ f.sets :=
show (∀{t}, s ⊆ t → t ∈ f.sets) ↔ s ∈ f.sets,
  from ⟨assume h, h (subset.refl s), assume hs t ht, mem_sets_of_superset hs ht⟩

lemma principal_mono {s t : set α} : principal s ≤ principal t ↔ s ⊆ t :=
by simp only [le_principal_iff, iff_self, mem_principal_sets]

lemma monotone_principal : monotone (principal : set α → filter α) :=
by simp only [monotone, principal_mono]; exact assume a b h, h

@[simp] lemma principal_eq_iff_eq {s t : set α} : principal s = principal t ↔ s = t :=
by simp only [le_antisymm_iff, le_principal_iff, mem_principal_sets]; refl

@[simp] lemma join_principal_eq_Sup {s : set (filter α)} : join (principal s) = Sup s := rfl

/- lattice equations -/

lemma empty_in_sets_eq_bot {f : filter α} : ∅ ∈ f.sets ↔ f = ⊥ :=
⟨assume h, bot_unique $ assume s _, mem_sets_of_superset h (empty_subset s),
  assume : f = ⊥, this.symm ▸ mem_bot_sets⟩

lemma inhabited_of_mem_sets {f : filter α} {s : set α} (hf : f ≠ ⊥) (hs : s ∈ f.sets) :
  ∃x, x ∈ s :=
have ∅ ∉ f.sets, from assume h, hf $ empty_in_sets_eq_bot.mp h,
have s ≠ ∅, from assume h, this (h ▸ hs),
exists_mem_of_ne_empty this

lemma filter_eq_bot_of_not_nonempty {f : filter α} (ne : ¬ nonempty α) : f = ⊥ :=
empty_in_sets_eq_bot.mp $ univ_mem_sets' $ assume x, false.elim (ne ⟨x⟩)

lemma forall_sets_neq_empty_iff_neq_bot {f : filter α} :
  (∀ (s : set α), s ∈ f.sets → s ≠ ∅) ↔ f ≠ ⊥ :=
by
  simp only [(@empty_in_sets_eq_bot α f).symm, ne.def];
  exact ⟨assume h hs, h _ hs rfl, assume h s hs eq, h $ eq ▸ hs⟩

lemma mem_sets_of_neq_bot {f : filter α} {s : set α} (h : f ⊓ principal (-s) = ⊥) : s ∈ f.sets :=
have ∅ ∈ (f ⊓ principal (- s)).sets, from h.symm ▸ mem_bot_sets,
let ⟨s₁, hs₁, s₂, (hs₂ : -s ⊆ s₂), (hs : s₁ ∩ s₂ ⊆ ∅)⟩ := this in
by filter_upwards [hs₁] assume a ha, classical.by_contradiction $ assume ha', hs ⟨ha, hs₂ ha'⟩

lemma infi_sets_eq {f : ι → filter α} (h : directed (≥) f) (ne : nonempty ι) :
  (infi f).sets = (⋃ i, (f i).sets) :=
let ⟨i⟩ := ne, u := { filter .
    sets             := (⋃ i, (f i).sets),
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
  (show u ≤ infi f, from le_infi $ assume i, le_supr (λi, (f i).sets) i)
  (Union_subset $ assume i, infi_le f i)

lemma infi_sets_eq' {f : β → filter α} {s : set β}
  (h : directed_on (f ⁻¹'o (≥)) s) (ne : ∃i, i ∈ s) :
  (⨅ i∈s, f i).sets = (⋃ i ∈ s, (f i).sets) :=
let ⟨i, hi⟩ := ne in
calc (⨅ i ∈ s, f i).sets  = (⨅ t : {t // t ∈ s}, (f t.val)).sets : by rw [infi_subtype]; refl
  ... = (⨆ t : {t // t ∈ s}, (f t.val).sets) : infi_sets_eq
    (assume ⟨x, hx⟩ ⟨y, hy⟩, match h x hx y hy with ⟨z, h₁, h₂, h₃⟩ := ⟨⟨z, h₁⟩, h₂, h₃⟩ end)
    ⟨⟨i, hi⟩⟩
  ... = (⨆ t ∈ {t | t ∈ s}, (f t).sets) : by rw [supr_subtype]; refl

lemma infi_sets_eq_finite (f : ι → filter α) :
  (⨅i, f i).sets = (⋃t:finset (plift ι), (⨅i∈t, f (plift.down i)).sets) :=
begin
  rw [infi_eq_infi_finset, infi_sets_eq],
  exact (directed_of_sup $ λs₁ s₂ hs, infi_le_infi $ λi, infi_le_infi_const $ λh, hs h),
  apply_instance
end

@[simp] lemma sup_join {f₁ f₂ : filter (filter α)} : (join f₁ ⊔ join f₂) = join (f₁ ⊔ f₂) :=
filter_eq $ set.ext $ assume x,
  by simp only [supr_sets_eq, join, mem_sup_sets, iff_self, mem_set_of_eq]

@[simp] lemma supr_join {ι : Sort w} {f : ι → filter (filter α)} :
  (⨆x, join (f x)) = join (⨆x, f x) :=
filter_eq $ set.ext $ assume x,
  by simp only [supr_sets_eq, join, iff_self, mem_Inter, mem_set_of_eq]

instance : bounded_distrib_lattice (filter α) :=
{ le_sup_inf :=
  begin
    assume x y z s,
    simp only [and_assoc, mem_inf_sets, mem_sup_sets, exists_prop, exists_imp_distrib, and_imp],
    intros hs t₁ ht₁ t₂ ht₂ hts,
    exact ⟨s ∪ t₁,
      x.sets_of_superset hs $ subset_union_left _ _,
      y.sets_of_superset ht₁ $ subset_union_right _ _,
      s ∪ t₂,
      x.sets_of_superset hs $ subset_union_left _ _,
      z.sets_of_superset ht₂ $ subset_union_right _ _,
      subset.trans (@le_sup_inf (set α) _ _ _ _) (union_subset (subset.refl _) hts)⟩
  end,
  ..filter.lattice.complete_lattice }

/- the complementary version with ⨆i, f ⊓ g i does not hold! -/
lemma infi_sup_eq {f : filter α} {g : ι → filter α} : (⨅ x, f ⊔ g x) = f ⊔ infi g :=
begin
  refine le_antisymm _ (le_infi $ assume i, sup_le_sup (le_refl f) $ infi_le _ _),
  rintros t ⟨h₁, h₂⟩,
  rw [infi_sets_eq_finite] at h₂,
  simp only [mem_Union, (finset.inf_eq_infi _ _).symm] at h₂,
  rcases h₂ with ⟨s, hs⟩,
  suffices : (⨅i, f ⊔ g i) ≤ f ⊔ s.inf (λi, g i.down), { exact this ⟨h₁, hs⟩ },
  refine finset.induction_on s _ _,
  { exact le_sup_right_of_le le_top },
  { rintros ⟨i⟩ s his ih,
    rw [finset.inf_insert, sup_inf_left],
    exact le_inf (infi_le _ _) ih }
end

lemma mem_infi_sets_finset {s : finset α} {f : α → filter β} :
  ∀t, t ∈ (⨅a∈s, f a).sets ↔ (∃p:α → set β, (∀a∈s, p a ∈ (f a).sets) ∧ (⋂a∈s, p a) ⊆ t) :=
show ∀t, t ∈ (⨅a∈s, f a).sets ↔ (∃p:α → set β, (∀a∈s, p a ∈ (f a).sets) ∧ (⨅a∈s, p a) ≤ t),
begin
  simp only [(finset.inf_eq_infi _ _).symm],
  refine finset.induction_on s _ _,
  { simp only [finset.not_mem_empty, false_implies_iff, finset.inf_empty, top_le_iff,
      imp_true_iff, mem_top_sets, true_and, exists_const],
    intros; refl },
  { intros a s has ih t,
    simp only [ih, finset.forall_mem_insert, finset.inf_insert, mem_inf_sets,
      exists_prop, iff_iff_implies_and_implies, exists_imp_distrib, and_imp, and_assoc] {contextual := tt},
    split,
    { intros t₁ ht₁ t₂ p hp ht₂ ht,
      existsi function.update p a t₁,
      have : ∀a'∈s, function.update p a t₁ a' = p a',
        from assume a' ha',
        have a' ≠ a, from assume h, has $ h ▸ ha',
        function.update_noteq this,
      have eq : s.inf (λj, function.update p a t₁ j) = s.inf (λj, p j) :=
        finset.inf_congr rfl this,
      simp only [this, ht₁, hp, function.update_same, true_and, imp_true_iff, eq] {contextual := tt},
      exact subset.trans (inter_subset_inter (subset.refl _) ht₂) ht },
    assume p hpa hp ht,
    exact ⟨p a, hpa, (s.inf p), ⟨⟨p, hp, le_refl _⟩, ht⟩⟩ }
end

/- principal equations -/

@[simp] lemma inf_principal {s t : set α} : principal s ⊓ principal t = principal (s ∩ t) :=
le_antisymm
  (by simp; exact ⟨s, subset.refl s, t, subset.refl t, by simp⟩)
  (by simp [le_inf_iff, inter_subset_left, inter_subset_right])

@[simp] lemma sup_principal {s t : set α} : principal s ⊔ principal t = principal (s ∪ t) :=
filter_eq $ set.ext $
  by simp only [union_subset_iff, union_subset_iff, mem_sup_sets, forall_const, iff_self, mem_principal_sets]

@[simp] lemma supr_principal {ι : Sort w} {s : ι → set α} : (⨆x, principal (s x)) = principal (⋃i, s i) :=
filter_eq $ set.ext $ assume x, by simp only [supr_sets_eq, mem_principal_sets, mem_Inter];
exact (@supr_le_iff (set α) _ _ _ _).symm

lemma principal_univ : principal (univ : set α) = ⊤ :=
top_unique $ by simp only [le_principal_iff, mem_top_sets, eq_self_iff_true]

lemma principal_empty : principal (∅ : set α) = ⊥ :=
bot_unique $ assume s _, empty_subset _

@[simp] lemma principal_eq_bot_iff {s : set α} : principal s = ⊥ ↔ s = ∅ :=
⟨assume h, principal_eq_iff_eq.mp $ by simp only [principal_empty, h, eq_self_iff_true],
  assume h, by simp only [h, principal_empty, eq_self_iff_true]⟩

lemma inf_principal_eq_bot {f : filter α} {s : set α} (hs : -s ∈ f.sets) : f ⊓ principal s = ⊥ :=
empty_in_sets_eq_bot.mp ⟨_, hs, s, mem_principal_self s, assume x ⟨h₁, h₂⟩, h₁ h₂⟩

theorem mem_inf_principal (f : filter α) (s t : set α) :
  s ∈ (f ⊓ principal t).sets ↔ { x | x ∈ t → x ∈ s } ∈ f.sets :=
begin
  simp only [mem_inf_sets, mem_principal_sets, exists_prop], split,
  { rintros ⟨u, ul, v, tsubv, uvinter⟩,
    apply filter.mem_sets_of_superset ul,
    intros x xu xt, exact uvinter ⟨xu, tsubv xt⟩ },
  intro h, refine ⟨_, h, t, set.subset.refl t, _⟩,
  rintros x ⟨hx, xt⟩,
  exact hx xt
end

end lattice

section map

/-- The forward map of a filter -/
def map (m : α → β) (f : filter α) : filter β :=
{ sets             := preimage m ⁻¹' f.sets,
  univ_sets        := univ_mem_sets,
  sets_of_superset := assume s t hs st, mem_sets_of_superset hs $ preimage_mono st,
  inter_sets       := assume s t hs ht, inter_mem_sets hs ht }

@[simp] lemma map_principal {s : set α} {f : α → β} :
  map f (principal s) = principal (set.image f s) :=
filter_eq $ set.ext $ assume a, image_subset_iff.symm

variables {f : filter α} {m : α → β} {m' : β → γ} {s : set α} {t : set β}

@[simp] lemma mem_map : t ∈ (map m f).sets ↔ {x | m x ∈ t} ∈ f.sets := iff.rfl

lemma image_mem_map (hs : s ∈ f.sets) : m '' s ∈ (map m f).sets :=
f.sets_of_superset hs $ subset_preimage_image m s

lemma range_mem_map : range m ∈ (map m f).sets :=
by rw ←image_univ; exact image_mem_map univ_mem_sets

lemma mem_map_sets_iff : t ∈ (map m f).sets ↔ (∃s∈f.sets, m '' s ⊆ t) :=
iff.intro
  (assume ht, ⟨set.preimage m t, ht, image_preimage_subset _ _⟩)
  (assume ⟨s, hs, ht⟩, mem_sets_of_superset (image_mem_map hs) ht)

@[simp] lemma map_id : filter.map id f = f :=
filter_eq $ rfl

@[simp] lemma map_compose : filter.map m' ∘ filter.map m = filter.map (m' ∘ m) :=
funext $ assume _, filter_eq $ rfl

@[simp] lemma map_map : filter.map m' (filter.map m f) = filter.map (m' ∘ m) f :=
congr_fun (@@filter.map_compose m m') f

end map

section comap

/-- The inverse map of a filter -/
def comap (m : α → β) (f : filter β) : filter α :=
{ sets             := { s | ∃t∈f.sets, m ⁻¹' t ⊆ s },
  univ_sets        := ⟨univ, univ_mem_sets, by simp only [subset_univ, preimage_univ]⟩,
  sets_of_superset := assume a b ⟨a', ha', ma'a⟩ ab,
    ⟨a', ha', subset.trans ma'a ab⟩,
  inter_sets       := assume a b ⟨a', ha₁, ha₂⟩ ⟨b', hb₁, hb₂⟩,
    ⟨a' ∩ b', inter_mem_sets ha₁ hb₁, inter_subset_inter ha₂ hb₂⟩ }

end comap

/-- The cofinite filter is the filter of subsets whose complements are finite. -/
def cofinite : filter α :=
{ sets             := {s | finite (- s)},
  univ_sets        := by simp only [compl_univ, finite_empty, mem_set_of_eq],
  sets_of_superset := assume s t (hs : finite (-s)) (st: s ⊆ t),
    finite_subset hs $ @lattice.neg_le_neg (set α) _ _ _ st,
  inter_sets       := assume s t (hs : finite (-s)) (ht : finite (-t)),
    by simp only [compl_inter, finite_union, ht, hs, mem_set_of_eq] }

/-- The monadic bind operation on filter is defined the usual way in terms of `map` and `join`.

Unfortunately, this `bind` does not result in the expected applicative. See `filter.seq` for the
applicative instance. -/
def bind (f : filter α) (m : α → filter β) : filter β := join (map m f)

/-- The applicative sequentiation operation. This is not induced by the bind operation. -/
def seq (f : filter (α → β)) (g : filter α) : filter β :=
⟨{ s | ∃u∈f.sets, ∃t∈g.sets, (∀m∈u, ∀x∈t, (m : α → β) x ∈ s) },
  ⟨univ, univ_mem_sets, univ, univ_mem_sets, by simp only [forall_prop_of_true, mem_univ, forall_true_iff]⟩,
  assume s₀ s₁ ⟨t₀, t₁, h₀, h₁, h⟩ hst, ⟨t₀, t₁, h₀, h₁, assume x hx y hy, hst $ h _ hx _ hy⟩,
  assume s₀ s₁ ⟨t₀, ht₀, t₁, ht₁, ht⟩ ⟨u₀, hu₀, u₁, hu₁, hu⟩,
    ⟨t₀ ∩ u₀, inter_mem_sets ht₀ hu₀, t₁ ∩ u₁, inter_mem_sets ht₁ hu₁,
      assume x ⟨hx₀, hx₁⟩ x ⟨hy₀, hy₁⟩, ⟨ht _ hx₀ _ hy₀, hu _ hx₁ _ hy₁⟩⟩⟩

instance : has_pure filter := ⟨λ(α : Type u) x, principal {x}⟩

instance : has_bind filter := ⟨@filter.bind⟩

instance : has_seq filter := ⟨@filter.seq⟩

instance : functor filter := { map := @filter.map }

section
-- this section needs to be before applicative, otherwise the wrong instance will be chosen
protected def monad : monad filter := { map := @filter.map }

local attribute [instance] filter.monad
protected def is_lawful_monad : is_lawful_monad filter :=
{ id_map     := assume α f, filter_eq rfl,
  pure_bind  := assume α β a f, by simp only [bind, Sup_image, image_singleton,
    join_principal_eq_Sup, lattice.Sup_singleton, map_principal, eq_self_iff_true],
  bind_assoc := assume α β γ f m₁ m₂, filter_eq rfl,
  bind_pure_comp_eq_map := assume α β f x, filter_eq $
    by simp only [bind, join, map, preimage, principal, set.subset_univ, eq_self_iff_true,
      function.comp_app, mem_set_of_eq, singleton_subset_iff] }
end

instance : applicative filter := { map := @filter.map, seq := @filter.seq }

instance : alternative filter :=
{ failure := λα, ⊥,
  orelse  := λα x y, x ⊔ y }

@[simp] lemma pure_def (x : α) : pure x = principal {x} := rfl

@[simp] lemma mem_pure {a : α} {s : set α} : a ∈ s → s ∈ (pure a : filter α).sets :=
by simp only [imp_self, pure_def, mem_principal_sets, singleton_subset_iff]; exact id

@[simp] lemma mem_pure_iff {a : α} {s : set α} : s ∈ (pure a : filter α).sets ↔ a ∈ s :=
by rw [pure_def, mem_principal_sets, set.singleton_subset_iff]

@[simp] lemma map_def {α β} (m : α → β) (f : filter α) : m <$> f = map m f := rfl

@[simp] lemma bind_def {α β} (f : filter α) (m : α → filter β) : f >>= m = bind f m := rfl

/- map and comap equations -/
section map
variables {f f₁ f₂ : filter α} {g g₁ g₂ : filter β} {m : α → β} {m' : β → γ} {s : set α} {t : set β}

@[simp] theorem mem_comap_sets : s ∈ (comap m g).sets ↔ ∃t∈g.sets, m ⁻¹' t ⊆ s := iff.rfl

theorem preimage_mem_comap (ht : t ∈ g.sets) : m ⁻¹' t ∈ (comap m g).sets :=
⟨t, ht, subset.refl _⟩

lemma comap_id : comap id f = f :=
le_antisymm (assume s, preimage_mem_comap) (assume s ⟨t, ht, hst⟩, mem_sets_of_superset ht hst)

lemma comap_comap_comp {m : γ → β} {n : β → α} : comap m (comap n f) = comap (n ∘ m) f :=
le_antisymm
  (assume c ⟨b, hb, (h : preimage (n ∘ m) b ⊆ c)⟩, ⟨preimage n b, preimage_mem_comap hb, h⟩)
  (assume c ⟨b, ⟨a, ha, (h₁ : preimage n a ⊆ b)⟩, (h₂ : preimage m b ⊆ c)⟩,
    ⟨a, ha, show preimage m (preimage n a) ⊆ c, from subset.trans (preimage_mono h₁) h₂⟩)

@[simp] theorem comap_principal {t : set β} : comap m (principal t) = principal (m ⁻¹' t) :=
filter_eq $ set.ext $ assume s,
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
@[simp] lemma map_supr {f : ι → filter α} : map m (⨆i, f i) = (⨆i, map m (f i)) :=
(gc_map_comap m).l_supr

@[simp] lemma comap_top : comap m ⊤ = ⊤ := (gc_map_comap m).u_top
@[simp] lemma comap_inf : comap m (g₁ ⊓ g₂) = comap m g₁ ⊓ comap m g₂ := (gc_map_comap m).u_inf
@[simp] lemma comap_infi {f : ι → filter β} : comap m (⨅i, f i) = (⨅i, comap m (f i)) :=
(gc_map_comap m).u_infi

lemma map_comap_le : map m (comap m g) ≤ g := (gc_map_comap m).l_u_le _
lemma le_comap_map : f ≤ comap m (map m f) := (gc_map_comap m).le_u_l _

@[simp] lemma comap_bot : comap m ⊥ = ⊥ :=
bot_unique $ assume s _, ⟨∅, by simp only [mem_bot_sets], by simp only [empty_subset, preimage_empty]⟩

lemma comap_supr {ι} {f : ι → filter β} {m : α → β} :
  comap m (supr f) = (⨆i, comap m (f i)) :=
le_antisymm
  (assume s hs,
    have ∀i, ∃t, t ∈ (f i).sets ∧ m ⁻¹' t ⊆ s, by simpa only [mem_comap_sets, exists_prop, mem_supr_sets] using mem_supr_sets.1 hs,
    let ⟨t, ht⟩ := classical.axiom_of_choice this in
    ⟨⋃i, t i, mem_supr_sets.2 $ assume i, (f i).sets_of_superset (ht i).1 (subset_Union _ _),
      begin
        rw [preimage_Union, Union_subset_iff],
        assume i,
        exact (ht i).2
      end⟩)
  (supr_le $ assume i, monotone_comap $ le_supr _ _)

lemma comap_Sup {s : set (filter β)} {m : α → β} : comap m (Sup s) = (⨆f∈s, comap m f) :=
by simp only [Sup_eq_supr, comap_supr, eq_self_iff_true]

lemma comap_sup : comap m (g₁ ⊔ g₂) = comap m g₁ ⊔ comap m g₂ :=
le_antisymm
  (assume s ⟨⟨t₁, ht₁, hs₁⟩, ⟨t₂, ht₂, hs₂⟩⟩,
    ⟨t₁ ∪ t₂,
      ⟨g₁.sets_of_superset ht₁ (subset_union_left _ _), g₂.sets_of_superset ht₂ (subset_union_right _ _)⟩,
      union_subset hs₁ hs₂⟩)
  (sup_le (comap_mono le_sup_left) (comap_mono le_sup_right))

lemma map_comap {f : filter β} {m : α → β} (hf : range m ∈ f.sets) : (f.comap m).map m = f :=
le_antisymm
  map_comap_le
  (assume t' ⟨t, ht, sub⟩, by filter_upwards [ht, hf]; rintros x hxt ⟨y, rfl⟩; exact sub hxt)

lemma comap_map {f : filter α} {m : α → β} (h : ∀ x y, m x = m y → x = y) :
  comap m (map m f) = f :=
have ∀s, preimage m (image m s) = s,
  from assume s, preimage_image_eq s h,
le_antisymm
  (assume s hs, ⟨
    image m s,
    f.sets_of_superset hs $ by simp only [this, subset.refl],
    by simp only [this, subset.refl]⟩)
  le_comap_map

lemma le_of_map_le_map_inj' {f g : filter α} {m : α → β} {s : set α}
  (hsf : s ∈ f.sets) (hsg : s ∈ g.sets) (hm : ∀x∈s, ∀y∈s, m x = m y → x = y)
  (h : map m f ≤ map m g) : f ≤ g :=
assume t ht, by filter_upwards [hsf, h $ image_mem_map (inter_mem_sets hsg ht)]
assume a has ⟨b, ⟨hbs, hb⟩, h⟩,
have b = a, from hm _ hbs _ has h,
this ▸ hb

lemma le_of_map_le_map_inj_iff {f g : filter α} {m : α → β} {s : set α}
  (hsf : s ∈ f.sets) (hsg : s ∈ g.sets) (hm : ∀x∈s, ∀y∈s, m x = m y → x = y) :
  map m f ≤ map m g ↔ f ≤ g :=
iff.intro (le_of_map_le_map_inj' hsf hsg hm) map_mono

lemma eq_of_map_eq_map_inj' {f g : filter α} {m : α → β} {s : set α}
  (hsf : s ∈ f.sets) (hsg : s ∈ g.sets) (hm : ∀x∈s, ∀y∈s, m x = m y → x = y)
  (h : map m f = map m g) : f = g :=
le_antisymm
  (le_of_map_le_map_inj' hsf hsg hm $ le_of_eq h)
  (le_of_map_le_map_inj' hsg hsf hm $ le_of_eq h.symm)

lemma map_inj {f g : filter α} {m : α → β} (hm : ∀ x y, m x = m y → x = y) (h : map m f = map m g) :
  f = g :=
have comap m (map m f) = comap m (map m g), by rw h,
by rwa [comap_map hm, comap_map hm] at this

theorem le_map_comap_of_surjective' {f : α → β} {l : filter β} {u : set β} (ul : u ∈ l.sets)
    (hf : ∀ y ∈ u, ∃ x, f x = y) :
  l ≤ map f (comap f l) :=
assume s ⟨t, tl, ht⟩,
have t ∩ u ⊆ s, from
  assume x ⟨xt, xu⟩,
  exists.elim (hf x xu) $ λ a faeq,
  by { rw ←faeq, apply ht, change f a ∈ t, rw faeq, exact xt },
mem_sets_of_superset (inter_mem_sets tl ul) this

theorem map_comap_of_surjective' {f : α → β} {l : filter β} {u : set β} (ul : u ∈ l.sets)
    (hf : ∀ y ∈ u, ∃ x, f x = y)  :
  map f (comap f l) = l :=
le_antisymm map_comap_le (le_map_comap_of_surjective' ul hf)

theorem le_map_comap_of_surjective {f : α → β} (hf : function.surjective f) (l : filter β) :
  l ≤ map f (comap f l) :=
le_map_comap_of_surjective' univ_mem_sets (λ y _, hf y)

theorem map_comap_of_surjective {f : α → β} (hf : function.surjective f) (l : filter β) :
  map f (comap f l) = l :=
le_antisymm map_comap_le (le_map_comap_of_surjective hf l)

lemma comap_neq_bot {f : filter β} {m : α → β}
  (hm : ∀t∈f.sets, ∃a, m a ∈ t) : comap m f ≠ ⊥ :=
forall_sets_neq_empty_iff_neq_bot.mp $ assume s ⟨t, ht, t_s⟩,
  let ⟨a, (ha : a ∈ preimage m t)⟩ := hm t ht in
  neq_bot_of_le_neq_bot (ne_empty_of_mem ha) t_s

lemma comap_neq_bot_of_surj {f : filter β} {m : α → β}
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

lemma sInter_comap_sets (f : α → β) (F : filter β) :
  ⋂₀(comap f F).sets = ⋂ U ∈ F.sets, f ⁻¹' U :=
begin
  ext x,
  suffices : (∀ (A : set α) (B : set β), B ∈ F.sets → f ⁻¹' B ⊆ A → x ∈ A) ↔
    ∀ (B : set β), B ∈ F.sets → f x ∈ B,
  by simp only [mem_sInter, mem_Inter, mem_comap_sets, this, and_imp, mem_comap_sets, exists_prop, mem_sInter,
    iff_self, mem_Inter, mem_preimage_eq, exists_imp_distrib],
  split,
  { intros h U U_in,
    simpa only [set.subset.refl, forall_prop_of_true, mem_preimage_eq] using h (f ⁻¹' U) U U_in },
  { intros h V U U_in f_U_V,
    exact f_U_V (h U U_in) },
end
end map

lemma map_cong {m₁ m₂ : α → β} {f : filter α} (h : {x | m₁ x = m₂ x} ∈ f.sets) :
  map m₁ f = map m₂ f :=
have ∀(m₁ m₂ : α → β) (h : {x | m₁ x = m₂ x} ∈ f.sets), map m₁ f ≤ map m₂ f,
begin
  intros  m₁ m₂ h s hs,
  show {x | m₁ x ∈ s} ∈ f.sets,
  filter_upwards [h, hs],
  simp only [subset_def, mem_preimage_eq, mem_set_of_eq, forall_true_iff] {contextual := tt}
end,
le_antisymm (this m₁ m₂ h) (this m₂ m₁ $ mem_sets_of_superset h $ assume x, eq.symm)

-- this is a generic rule for monotone functions:
lemma map_infi_le {f : ι → filter α} {m : α → β} :
  map m (infi f) ≤ (⨅ i, map m (f i)) :=
le_infi $ assume i, map_mono $ infi_le _ _

lemma map_infi_eq {f : ι → filter α} {m : α → β} (hf : directed (≥) f) (hι : nonempty ι) :
  map m (infi f) = (⨅ i, map m (f i)) :=
le_antisymm
  map_infi_le
  (assume s (hs : preimage m s ∈ (infi f).sets),
    have ∃i, preimage m s ∈ (f i).sets,
      by simp only [infi_sets_eq hf hι, mem_Union] at hs; assumption,
    let ⟨i, hi⟩ := this in
    have (⨅ i, map m (f i)) ≤ principal s, from
      infi_le_of_le i $ by simp only [le_principal_iff, mem_map]; assumption,
    by simp only [filter.le_principal_iff] at this; assumption)

lemma map_binfi_eq {ι : Type w} {f : ι → filter α} {m : α → β} {p : ι → Prop}
  (h : directed_on (f ⁻¹'o (≥)) {x | p x}) (ne : ∃i, p i) :
  map m (⨅i (h : p i), f i) = (⨅i (h: p i), map m (f i)) :=
let ⟨i, hi⟩ := ne in
calc map m (⨅i (h : p i), f i) = map m (⨅i:subtype p, f i.val) : by simp only [infi_subtype, eq_self_iff_true]
  ... = (⨅i:subtype p, map m (f i.val)) : map_infi_eq
    (assume ⟨x, hx⟩ ⟨y, hy⟩, match h x hx y hy with ⟨z, h₁, h₂, h₃⟩ := ⟨⟨z, h₁⟩, h₂, h₃⟩ end)
    ⟨⟨i, hi⟩⟩
  ... = (⨅i (h : p i), map m (f i)) : by simp only [infi_subtype, eq_self_iff_true]

lemma map_inf' {f g : filter α} {m : α → β} {t : set α} (htf : t ∈ f.sets) (htg : t ∈ g.sets)
  (h : ∀x∈t, ∀y∈t, m x = m y → x = y) : map m (f ⊓ g) = map m f ⊓ map m g :=
begin
  refine le_antisymm
    (le_inf (map_mono inf_le_left) (map_mono inf_le_right))
    (assume s hs, _),
  simp only [map, mem_inf_sets, exists_prop, mem_map, mem_preimage_eq, mem_inf_sets] at hs ⊢,
  rcases hs with ⟨t₁, h₁, t₂, h₂, hs⟩,
  refine ⟨m '' (t₁ ∩ t), _, m '' (t₂ ∩ t), _, _⟩,
  { filter_upwards [h₁, htf] assume a h₁ h₂, mem_image_of_mem _ ⟨h₁, h₂⟩ },
  { filter_upwards [h₂, htg] assume a h₁ h₂, mem_image_of_mem _ ⟨h₁, h₂⟩ },
  { rw [image_inter_on],
    { refine image_subset_iff.2 _,
      exact λ x ⟨⟨h₁, _⟩, h₂, _⟩, hs ⟨h₁, h₂⟩ },
    { exact λ x ⟨_, hx⟩ y ⟨_, hy⟩, h x hx y hy } }
end

lemma map_inf {f g : filter α} {m : α → β} (h : ∀ x y, m x = m y → x = y) :
  map m (f ⊓ g) = map m f ⊓ map m g :=
map_inf' univ_mem_sets univ_mem_sets (assume x _ y _, h x y)

lemma map_eq_comap_of_inverse {f : filter α} {m : α → β} {n : β → α}
  (h₁ : m ∘ n = id) (h₂ : n ∘ m = id) : map m f = comap n f :=
le_antisymm
  (assume b ⟨a, ha, (h : preimage n a ⊆ b)⟩, f.sets_of_superset ha $
    calc a = preimage (n ∘ m) a : by simp only [h₂, preimage_id, eq_self_iff_true]
      ... ⊆ preimage m b : preimage_mono h)
  (assume b (hb : preimage m b ∈ f.sets),
    ⟨preimage m b, hb, show preimage (m ∘ n) b ⊆ b, by simp only [h₁]; apply subset.refl⟩)

lemma map_swap_eq_comap_swap {f : filter (α × β)} : prod.swap <$> f = comap prod.swap f :=
map_eq_comap_of_inverse prod.swap_swap_eq prod.swap_swap_eq

lemma le_map {f : filter α} {m : α → β} {g : filter β} (h : ∀s∈f.sets, m '' s ∈ g.sets) :
  g ≤ f.map m :=
assume s hs, mem_sets_of_superset (h _ hs) $ image_preimage_subset _ _

section applicative

@[simp] lemma mem_pure_sets {a : α} {s : set α} :
  s ∈ (pure a : filter α).sets ↔ a ∈ s :=
by simp only [iff_self, pure_def, mem_principal_sets, singleton_subset_iff]

lemma singleton_mem_pure_sets {a : α} : {a} ∈ (pure a : filter α).sets :=
by simp only [mem_singleton, pure_def, mem_principal_sets, singleton_subset_iff]

@[simp] lemma pure_neq_bot {α : Type u} {a : α} : pure a ≠ (⊥ : filter α) :=
by simp only [pure, has_pure.pure, ne.def, not_false_iff, singleton_ne_empty, principal_eq_bot_iff]

lemma mem_seq_sets_def {f : filter (α → β)} {g : filter α} {s : set β} :
  s ∈ (f.seq g).sets ↔ (∃u∈f.sets, ∃t∈g.sets, ∀x∈u, ∀y∈t, (x : α → β) y ∈ s) :=
iff.refl _

lemma mem_seq_sets_iff {f : filter (α → β)} {g : filter α} {s : set β} :
  s ∈ (f.seq g).sets ↔ (∃u∈f.sets, ∃t∈g.sets, set.seq u t ⊆ s) :=
by simp only [mem_seq_sets_def, seq_subset, exists_prop, iff_self]

lemma mem_map_seq_iff {f : filter α} {g : filter β} {m : α → β → γ} {s : set γ} :
  s ∈ ((f.map m).seq g).sets ↔ (∃t u, t ∈ g.sets ∧ u ∈ f.sets ∧ ∀x∈u, ∀y∈t, m x y ∈ s) :=
iff.intro
  (assume ⟨t, ht, s, hs, hts⟩, ⟨s, m ⁻¹' t, hs, ht, assume a, hts _⟩)
  (assume ⟨t, s, ht, hs, hts⟩, ⟨m '' s, image_mem_map hs, t, ht, assume f ⟨a, has, eq⟩, eq ▸ hts _ has⟩)

lemma seq_mem_seq_sets {f : filter (α → β)} {g : filter α} {s : set (α → β)} {t : set α}
  (hs : s ∈ f.sets) (ht : t ∈ g.sets): s.seq t ∈ (f.seq g).sets :=
⟨s, hs, t, ht, assume f hf a ha, ⟨f, hf, a, ha, rfl⟩⟩

lemma le_seq {f : filter (α → β)} {g : filter α} {h : filter β}
  (hh : ∀t∈f.sets, ∀u∈g.sets, set.seq t u ∈ h.sets) : h ≤ seq f g :=
assume s ⟨t, ht, u, hu, hs⟩, mem_sets_of_superset (hh _ ht _ hu) $
  assume b ⟨m, hm, a, ha, eq⟩, eq ▸ hs _ hm _ ha

lemma seq_mono {f₁ f₂ : filter (α → β)} {g₁ g₂ : filter α}
  (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) : f₁.seq g₁ ≤ f₂.seq g₂ :=
le_seq $ assume s hs t ht, seq_mem_seq_sets (hf hs) (hg ht)

@[simp] lemma pure_seq_eq_map (g : α → β) (f : filter α) : seq (pure g) f = f.map g :=
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

@[simp] lemma seq_pure (f : filter (α → β)) (a : α) : seq f (pure a) = map (λg:α → β, g a) f :=
begin
  refine le_antisymm (le_map $ assume s hs, _) (le_seq $ assume s hs t ht, _),
  { rw ← seq_singleton, exact seq_mem_seq_sets hs
    (by simp only [mem_singleton, pure_def, mem_principal_sets, singleton_subset_iff]) },
  { rw mem_pure_sets at ht,
    refine sets_of_superset (map (λg:α→β, g a) f) (image_mem_map hs) _,
    rintros b ⟨g, hg, rfl⟩, exact ⟨g, hg, a, ht, rfl⟩ }
end

@[simp] lemma seq_assoc (x : filter α) (g : filter (α → β)) (h : filter (β → γ)) :
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

lemma prod_map_seq_comm (f : filter α) (g : filter β) :
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

instance : is_lawful_functor (filter : Type u → Type u) :=
{ id_map   := assume α f, map_id,
  comp_map := assume α β γ f g a, map_map.symm }

instance : is_lawful_applicative (filter : Type u → Type u) :=
{ pure_seq_eq_map := assume α β, pure_seq_eq_map,
  map_pure        := assume α β, map_pure,
  seq_pure        := assume α β, seq_pure,
  seq_assoc       := assume α β γ, seq_assoc }

instance : is_comm_applicative (filter : Type u → Type u) :=
⟨assume α β f g, prod_map_seq_comm f g⟩

lemma {l} seq_eq_filter_seq {α β : Type l} (f : filter (α → β)) (g : filter α) :
  f <*> g = seq f g := rfl

end applicative

/- bind equations -/
section bind
@[simp] lemma mem_bind_sets {s : set β} {f : filter α} {m : α → filter β} :
  s ∈ (bind f m).sets ↔ ∃t ∈ f.sets, ∀x ∈ t, s ∈ (m x).sets :=
calc s ∈ (bind f m).sets ↔ {a | s ∈ (m a).sets} ∈ f.sets : by simp only [bind, mem_map, iff_self, mem_join_sets, mem_set_of_eq]
                     ... ↔ (∃t ∈ f.sets, t ⊆ {a | s ∈ (m a).sets}) : exists_sets_subset_iff.symm
                     ... ↔ (∃t ∈ f.sets, ∀x ∈ t, s ∈ (m x).sets) : iff.refl _

lemma bind_mono {f : filter α} {g h : α → filter β} (h₁ : {a | g a ≤ h a} ∈ f.sets) :
  bind f g ≤ bind f h :=
assume x h₂, show (_ ∈ f.sets), by filter_upwards [h₁, h₂] assume s gh' h', gh' h'

lemma bind_sup {f g : filter α} {h : α → filter β} :
  bind (f ⊔ g) h = bind f h ⊔ bind g h :=
by simp only [bind, sup_join, map_sup, eq_self_iff_true]

lemma bind_mono2 {f g : filter α} {h : α → filter β} (h₁ : f ≤ g) :
  bind f h ≤ bind g h :=
assume s h', h₁ h'

lemma principal_bind {s : set α} {f : α → filter β} :
  (bind (principal s) f) = (⨆x ∈ s, f x) :=
show join (map f (principal s)) = (⨆x ∈ s, f x),
  by simp only [Sup_image, join_principal_eq_Sup, map_principal, eq_self_iff_true]

end bind

lemma infi_neq_bot_of_directed {f : ι → filter α}
  (hn : nonempty α) (hd : directed (≥) f) (hb : ∀i, f i ≠ ⊥) : (infi f) ≠ ⊥ :=
let ⟨x⟩ := hn in
assume h, have he: ∅ ∈ (infi f).sets, from h.symm ▸ mem_bot_sets,
classical.by_cases
  (assume : nonempty ι,
    have ∃i, ∅ ∈ (f i).sets,
      by rw [infi_sets_eq hd this] at he; simp only [mem_Union] at he; assumption,
    let ⟨i, hi⟩ := this in
    hb i $ bot_unique $
    assume s _, (f i).sets_of_superset hi $ empty_subset _)
  (assume : ¬ nonempty ι,
    have univ ⊆ (∅ : set α),
    begin
      rw [←principal_mono, principal_univ, principal_empty, ←h],
      exact (le_infi $ assume i, false.elim $ this ⟨i⟩)
    end,
    this $ mem_univ x)

lemma infi_neq_bot_iff_of_directed {f : ι → filter α}
  (hn : nonempty α) (hd : directed (≥) f) : (infi f) ≠ ⊥ ↔ (∀i, f i ≠ ⊥) :=
⟨assume neq_bot i eq_bot, neq_bot $ bot_unique $ infi_le_of_le i $ eq_bot ▸ le_refl _,
  infi_neq_bot_of_directed hn hd⟩

lemma mem_infi_sets {f : ι → filter α} (i : ι) : ∀{s}, s ∈ (f i).sets → s ∈ (⨅i, f i).sets :=
show (⨅i, f i) ≤ f i, from infi_le _ _

@[elab_as_eliminator]
lemma infi_sets_induct {f : ι → filter α} {s : set α} (hs : s ∈ (infi f).sets) {p : set α → Prop}
  (uni : p univ)
  (ins : ∀{i s₁ s₂}, s₁ ∈ (f i).sets → p s₂ → p (s₁ ∩ s₂))
  (upw : ∀{s₁ s₂}, s₁ ⊆ s₂ → p s₁ → p s₂) : p s :=
begin
  rw [infi_sets_eq_finite] at hs,
  simp only [mem_Union, (finset.inf_eq_infi _ _).symm] at hs,
  rcases hs with ⟨is, his⟩,
  revert s,
  refine finset.induction_on is _ _,
  { assume s hs, rwa [mem_top_sets.1 hs] },
  { rintros ⟨i⟩ js his ih s hs,
    rw [finset.inf_insert, mem_inf_sets] at hs,
    rcases hs with ⟨s₁, hs₁, s₂, hs₂, hs⟩,
    exact upw hs (ins hs₁ (ih hs₂)) }
end

/- tendsto -/

/-- `tendsto` is the generic "limit of a function" predicate.
  `tendsto f l₁ l₂` asserts that for every `l₂` neighborhood `a`,
  the `f`-preimage of `a` is an `l₁` neighborhood. -/
def tendsto (f : α → β) (l₁ : filter α) (l₂ : filter β) := l₁.map f ≤ l₂

lemma tendsto_def {f : α → β} {l₁ : filter α} {l₂ : filter β} :
  tendsto f l₁ l₂ ↔ ∀ s ∈ l₂.sets, f ⁻¹' s ∈ l₁.sets := iff.rfl

lemma tendsto_iff_comap {f : α → β} {l₁ : filter α} {l₂ : filter β} :
  tendsto f l₁ l₂ ↔ l₁ ≤ l₂.comap f :=
map_le_iff_le_comap

lemma tendsto_cong {f₁ f₂ : α → β} {l₁ : filter α} {l₂ : filter β}
  (h : tendsto f₁ l₁ l₂) (hl : {x | f₁ x = f₂ x} ∈ l₁.sets) : tendsto f₂ l₁ l₂ :=
by rwa [tendsto, ←map_cong hl]

lemma tendsto_id' {x y : filter α} : x ≤ y → tendsto id x y :=
by simp only [tendsto, map_id, forall_true_iff] {contextual := tt}

lemma tendsto_id {x : filter α} : tendsto id x x := tendsto_id' $ le_refl x

lemma tendsto.comp {f : α → β} {g : β → γ} {x : filter α} {y : filter β} {z : filter γ}
  (hf : tendsto f x y) (hg : tendsto g y z) : tendsto (g ∘ f) x z :=
calc map (g ∘ f) x = map g (map f x) : by rw [map_map]
  ... ≤ map g y : map_mono hf
  ... ≤ z : hg

lemma tendsto_le_left {f : α → β} {x y : filter α} {z : filter β}
  (h : y ≤ x) : tendsto f x z → tendsto f y z :=
le_trans (map_mono h)

lemma tendsto_le_right {f : α → β} {x : filter α} {y z : filter β}
  (h₁ : y ≤ z) (h₂ : tendsto f x y) : tendsto f x z :=
le_trans h₂ h₁

lemma tendsto_map {f : α → β} {x : filter α} : tendsto f x (map f x) := le_refl (map f x)

lemma tendsto_map' {f : β → γ} {g : α → β} {x : filter α} {y : filter γ}
  (h : tendsto (f ∘ g) x y) : tendsto f (map g x) y :=
by rwa [tendsto, map_map]

lemma tendsto_map'_iff {f : β → γ} {g : α → β} {x : filter α} {y : filter γ} :
  tendsto f (map g x) y ↔ tendsto (f ∘ g) x y :=
by rw [tendsto, map_map]; refl

lemma tendsto_comap {f : α → β} {x : filter β} : tendsto f (comap f x) x :=
map_comap_le

lemma tendsto_comap_iff {f : α → β} {g : β → γ} {a : filter α} {c : filter γ} :
  tendsto f a (c.comap g) ↔ tendsto (g ∘ f) a c :=
⟨assume h, h.comp tendsto_comap, assume h, map_le_iff_le_comap.mp $ by rwa [map_map]⟩

lemma tendsto_comap'_iff {m : α → β} {f : filter α} {g : filter β} {i : γ → α}
  (h : range i ∈ f.sets) : tendsto (m ∘ i) (comap i f) g ↔ tendsto m f g :=
by rw [tendsto, ← map_compose]; simp only [(∘), map_comap h, tendsto]

lemma comap_eq_of_inverse {f : filter α} {g : filter β} {φ : α → β} (ψ : β → α)
  (eq : ψ ∘ φ = id) (hφ : tendsto φ f g) (hψ : tendsto ψ g f) : comap φ g = f :=
begin
  refine le_antisymm (le_trans (comap_mono $ map_le_iff_le_comap.1 hψ) _) (map_le_iff_le_comap.1 hφ),
  rw [comap_comap_comp, eq, comap_id],
  exact le_refl _
end

lemma map_eq_of_inverse {f : filter α} {g : filter β} {φ : α → β} (ψ : β → α)
  (eq : φ ∘ ψ = id) (hφ : tendsto φ f g) (hψ : tendsto ψ g f) : map φ f = g :=
begin
  refine le_antisymm hφ (le_trans _ (map_mono hψ)),
  rw [map_map, eq, map_id],
  exact le_refl _
end

lemma tendsto_inf {f : α → β} {x : filter α} {y₁ y₂ : filter β} :
  tendsto f x (y₁ ⊓ y₂) ↔ tendsto f x y₁ ∧ tendsto f x y₂ :=
by simp only [tendsto, lattice.le_inf_iff, iff_self]

lemma tendsto_inf_left {f : α → β} {x₁ x₂ : filter α} {y : filter β}
  (h : tendsto f x₁ y) : tendsto f (x₁ ⊓ x₂) y  :=
le_trans (map_mono inf_le_left) h

lemma tendsto_inf_right {f : α → β} {x₁ x₂ : filter α} {y : filter β}
  (h : tendsto f x₂ y) : tendsto f (x₁ ⊓ x₂) y  :=
le_trans (map_mono inf_le_right) h

lemma tendsto_infi {f : α → β} {x : filter α} {y : ι → filter β} :
  tendsto f x (⨅i, y i) ↔ ∀i, tendsto f x (y i) :=
by simp only [tendsto, iff_self, lattice.le_infi_iff]

lemma tendsto_infi' {f : α → β} {x : ι → filter α} {y : filter β} (i : ι) :
  tendsto f (x i) y → tendsto f (⨅i, x i) y :=
tendsto_le_left (infi_le _ _)

lemma tendsto_principal {f : α → β} {a : filter α} {s : set β} :
  tendsto f a (principal s) ↔ {a | f a ∈ s} ∈ a.sets :=
by simp only [tendsto, le_principal_iff, mem_map, iff_self]

lemma tendsto_principal_principal {f : α → β} {s : set α} {t : set β} :
  tendsto f (principal s) (principal t) ↔ ∀a∈s, f a ∈ t :=
by simp only [tendsto, image_subset_iff, le_principal_iff, map_principal, mem_principal_sets]; refl

lemma tendsto_pure_pure (f : α → β) (a : α) :
  tendsto f (pure a) (pure (f a)) :=
show filter.map f (pure a) ≤ pure (f a),
  by rw [filter.map_pure]; exact le_refl _

lemma tendsto_const_pure {a : filter α} {b : β} : tendsto (λa, b) a (pure b) :=
by simp [tendsto]; exact univ_mem_sets

lemma tendsto_if {l₁ : filter α} {l₂ : filter β}
    {f g : α → β} {p : α → Prop} [decidable_pred p]
    (h₀ : tendsto f (l₁ ⊓ principal p) l₂)
    (h₁ : tendsto g (l₁ ⊓ principal { x | ¬ p x }) l₂) :
  tendsto (λ x, if p x then f x else g x) l₁ l₂ :=
begin
  revert h₀ h₁, simp only [tendsto_def, mem_inf_principal],
  intros h₀ h₁ s hs,
  apply mem_sets_of_superset (inter_mem_sets (h₀ s hs) (h₁ s hs)),
  rintros x ⟨hp₀, hp₁⟩, dsimp,
  by_cases h : p x,
  { rw if_pos h, exact hp₀ h },
  rw if_neg h, exact hp₁ h
end


section prod
variables {s : set α} {t : set β} {f : filter α} {g : filter β}
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

/-- Product of filters. This is the filter generated by cartesian products
  of elements of the component filters. -/
protected def prod (f : filter α) (g : filter β) : filter (α × β) :=
f.comap prod.fst ⊓ g.comap prod.snd

lemma prod_mem_prod {s : set α} {t : set β} {f : filter α} {g : filter β}
  (hs : s ∈ f.sets) (ht : t ∈ g.sets) : set.prod s t ∈ (filter.prod f g).sets :=
inter_mem_inf_sets (preimage_mem_comap hs) (preimage_mem_comap ht)

lemma mem_prod_iff {s : set (α×β)} {f : filter α} {g : filter β} :
  s ∈ (filter.prod f g).sets ↔ (∃t₁∈f.sets, ∃t₂∈g.sets, set.prod t₁ t₂ ⊆ s) :=
begin
  simp only [filter.prod],
  split,
  exact assume ⟨t₁, ⟨s₁, hs₁, hts₁⟩, t₂, ⟨s₂, hs₂, hts₂⟩, h⟩,
    ⟨s₁, hs₁, s₂, hs₂, subset.trans (inter_subset_inter hts₁ hts₂) h⟩,
  exact assume ⟨t₁, ht₁, t₂, ht₂, h⟩,
    ⟨prod.fst ⁻¹' t₁, ⟨t₁, ht₁, subset.refl _⟩, prod.snd ⁻¹' t₂, ⟨t₂, ht₂, subset.refl _⟩, h⟩
end

lemma tendsto_fst {f : filter α} {g : filter β} : tendsto prod.fst (filter.prod f g) f :=
tendsto_inf_left tendsto_comap

lemma tendsto_snd {f : filter α} {g : filter β} : tendsto prod.snd (filter.prod f g) g :=
tendsto_inf_right tendsto_comap

lemma tendsto.prod_mk {f : filter α} {g : filter β} {h : filter γ} {m₁ : α → β} {m₂ : α → γ}
  (h₁ : tendsto m₁ f g) (h₂ : tendsto m₂ f h) : tendsto (λx, (m₁ x, m₂ x)) f (filter.prod g h) :=
tendsto_inf.2 ⟨tendsto_comap_iff.2 h₁, tendsto_comap_iff.2 h₂⟩

lemma prod_infi_left {f : ι → filter α} {g : filter β} (i : ι) :
  filter.prod (⨅i, f i) g = (⨅i, filter.prod (f i) g) :=
by rw [filter.prod, comap_infi, infi_inf i]; simp only [filter.prod, eq_self_iff_true]

lemma prod_infi_right {f : filter α} {g : ι → filter β} (i : ι) :
  filter.prod f (⨅i, g i) = (⨅i, filter.prod f (g i)) :=
by rw [filter.prod, comap_infi, inf_infi i]; simp only [filter.prod, eq_self_iff_true]

lemma prod_mono {f₁ f₂ : filter α} {g₁ g₂ : filter β} (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) :
  filter.prod f₁ g₁ ≤ filter.prod f₂ g₂ :=
inf_le_inf (comap_mono hf) (comap_mono hg)

lemma prod_comap_comap_eq {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
  {f₁ : filter α₁} {f₂ : filter α₂} {m₁ : β₁ → α₁} {m₂ : β₂ → α₂} :
  filter.prod (comap m₁ f₁) (comap m₂ f₂) = comap (λp:β₁×β₂, (m₁ p.1, m₂ p.2)) (filter.prod f₁ f₂) :=
by simp only [filter.prod, comap_comap_comp, eq_self_iff_true, comap_inf]

lemma prod_comm' : filter.prod f g = comap (prod.swap) (filter.prod g f) :=
by simp only [filter.prod, comap_comap_comp, (∘), inf_comm, prod.fst_swap,
  eq_self_iff_true, prod.snd_swap, comap_inf]

lemma prod_comm : filter.prod f g = map (λp:β×α, (p.2, p.1)) (filter.prod g f) :=
by rw [prod_comm', ← map_swap_eq_comap_swap]; refl

lemma prod_map_map_eq {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
  {f₁ : filter α₁} {f₂ : filter α₂} {m₁ : α₁ → β₁} {m₂ : α₂ → β₂} :
  filter.prod (map m₁ f₁) (map m₂ f₂) = map (λp:α₁×α₂, (m₁ p.1, m₂ p.2)) (filter.prod f₁ f₂) :=
le_antisymm
  (assume s hs,
    let ⟨s₁, hs₁, s₂, hs₂, h⟩ := mem_prod_iff.mp hs in
    filter.sets_of_superset _ (prod_mem_prod (image_mem_map hs₁) (image_mem_map hs₂)) $
      calc set.prod (m₁ '' s₁) (m₂ '' s₂) = (λp:α₁×α₂, (m₁ p.1, m₂ p.2)) '' set.prod s₁ s₂ :
          set.prod_image_image_eq
        ... ⊆ _ : by rwa [image_subset_iff])
  ((tendsto_fst.comp (le_refl _)).prod_mk (tendsto_snd.comp (le_refl _)))

lemma map_prod (m : α × β → γ) (f : filter α) (g : filter β) :
  map m (f.prod g) = (f.map (λa b, m (a, b))).seq g :=
begin
  simp [filter.ext_iff, mem_prod_iff, mem_map_seq_iff],
  assume s,
  split,
  exact assume ⟨t, ht, s, hs, h⟩, ⟨s, hs, t, ht, assume x hx y hy, @h ⟨x, y⟩ ⟨hx, hy⟩⟩,
  exact assume ⟨s, hs, t, ht, h⟩, ⟨t, ht, s, hs, assume ⟨x, y⟩ ⟨hx, hy⟩, h x hx y hy⟩
end

lemma prod_eq {f : filter α} {g : filter β} : f.prod g = (f.map prod.mk).seq g  :=
have h : _ := map_prod id f g, by rwa [map_id] at h

lemma prod_inf_prod {f₁ f₂ : filter α} {g₁ g₂ : filter β} :
  filter.prod f₁ g₁ ⊓ filter.prod f₂ g₂ = filter.prod (f₁ ⊓ f₂) (g₁ ⊓ g₂) :=
by simp only [filter.prod, comap_inf, inf_comm, inf_assoc, lattice.inf_left_comm]

@[simp] lemma prod_bot {f : filter α} : filter.prod f (⊥ : filter β) = ⊥ := by simp [filter.prod]
@[simp] lemma bot_prod {g : filter β} : filter.prod (⊥ : filter α) g = ⊥ := by simp [filter.prod]

@[simp] lemma prod_principal_principal {s : set α} {t : set β} :
  filter.prod (principal s) (principal t) = principal (set.prod s t) :=
by simp only [filter.prod, comap_principal, principal_eq_iff_eq, comap_principal, inf_principal]; refl

@[simp] lemma prod_pure_pure {a : α} {b : β} : filter.prod (pure a) (pure b) = pure (a, b) :=
by simp

lemma prod_eq_bot {f : filter α} {g : filter β} : filter.prod f g = ⊥ ↔ (f = ⊥ ∨ g = ⊥) :=
begin
  split,
  { assume h,
    rcases mem_prod_iff.1 (empty_in_sets_eq_bot.2 h) with ⟨s, hs, t, ht, hst⟩,
    rw [subset_empty_iff, set.prod_eq_empty_iff] at hst,
    cases hst with s_eq t_eq,
    { left, exact empty_in_sets_eq_bot.1 (s_eq ▸ hs) },
    { right, exact empty_in_sets_eq_bot.1 (t_eq ▸ ht) } },
  { rintros (rfl | rfl),
    exact bot_prod,
    exact prod_bot }
end

lemma prod_neq_bot {f : filter α} {g : filter β} : filter.prod f g ≠ ⊥ ↔ (f ≠ ⊥ ∧ g ≠ ⊥) :=
by rw [(≠), prod_eq_bot, not_or_distrib]

lemma tendsto_prod_iff {f : α × β → γ} {x : filter α} {y : filter β} {z : filter γ} :
  filter.tendsto f (filter.prod x y) z ↔
  ∀ W ∈ z.sets, ∃ U ∈ x.sets,  ∃ V ∈ y.sets, ∀ x y, x ∈ U → y ∈ V → f (x, y) ∈ W :=
by simp only [tendsto_def, mem_prod_iff, prod_sub_preimage_iff, exists_prop, iff_self]

end prod

/- at_top and at_bot -/

/-- `at_top` is the filter representing the limit `→ ∞` on an ordered set.
  It is generated by the collection of up-sets `{b | a ≤ b}`.
  (The preorder need not have a top element for this to be well defined,
  and indeed is trivial when a top element exists.) -/
def at_top [preorder α] : filter α := ⨅ a, principal {b | a ≤ b}

/-- `at_bot` is the filter representing the limit `→ -∞` on an ordered set.
  It is generated by the collection of down-sets `{b | b ≤ a}`.
  (The preorder need not have a bottom element for this to be well defined,
  and indeed is trivial when a bottom element exists.) -/
def at_bot [preorder α] : filter α := ⨅ a, principal {b | b ≤ a}

lemma mem_at_top [preorder α] (a : α) : {b : α | a ≤ b} ∈ (@at_top α _).sets :=
mem_infi_sets a $ subset.refl _

@[simp] lemma at_top_ne_bot [nonempty α] [semilattice_sup α] : (at_top : filter α) ≠ ⊥ :=
infi_neq_bot_of_directed (by apply_instance)
  (assume a b, ⟨a ⊔ b, by simp only [ge, le_principal_iff, forall_const, set_of_subset_set_of,
    mem_principal_sets, and_self, sup_le_iff, forall_true_iff] {contextual := tt}⟩)
  (assume a, by simp only [principal_eq_bot_iff, ne.def, principal_eq_bot_iff]; exact ne_empty_of_mem (le_refl a))

@[simp] lemma mem_at_top_sets [nonempty α] [semilattice_sup α] {s : set α} :
  s ∈ (at_top : filter α).sets ↔ ∃a:α, ∀b≥a, b ∈ s :=
let ⟨a⟩ := ‹nonempty α› in
iff.intro
  (assume h, infi_sets_induct h ⟨a, by simp only [forall_const, mem_univ, forall_true_iff]⟩
    (assume a s₁ s₂ ha ⟨b, hb⟩, ⟨a ⊔ b,
      assume c hc, ⟨ha $ le_trans le_sup_left hc, hb _ $ le_trans le_sup_right hc⟩⟩)
    (assume s₁ s₂ h ⟨a, ha⟩, ⟨a, assume b hb, h $ ha _ hb⟩))
  (assume ⟨a, h⟩, mem_infi_sets a $ assume x, h x)

lemma map_at_top_eq [nonempty α] [semilattice_sup α] {f : α → β} :
  at_top.map f = (⨅a, principal $ f '' {a' | a ≤ a'}) :=
calc map f (⨅a, principal {a' | a ≤ a'}) = (⨅a, map f $ principal {a' | a ≤ a'}) :
    map_infi_eq (assume a b, ⟨a ⊔ b, by simp only [ge, le_principal_iff, forall_const, set_of_subset_set_of,
      mem_principal_sets, and_self, sup_le_iff, forall_true_iff] {contextual := tt}⟩)
      (by apply_instance)
  ... = (⨅a, principal $ f '' {a' | a ≤ a'}) : by simp only [map_principal, eq_self_iff_true]

lemma tendsto_at_top [preorder β] (m : α → β) (f : filter α) :
  tendsto m f at_top ↔ (∀b, {a | b ≤ m a} ∈ f.sets) :=
by simp only [at_top, tendsto_infi, tendsto_principal]; refl

lemma tendsto_at_top' [nonempty α] [semilattice_sup α] (f : α → β) (l : filter β) :
  tendsto f at_top l ↔ (∀s∈l.sets, ∃a, ∀b≥a, f b ∈ s) :=
by simp only [tendsto_def, mem_at_top_sets]; refl

theorem tendsto_at_top_principal [nonempty β] [semilattice_sup β] {f : β → α} {s : set α} :
  tendsto f at_top (principal s) ↔ ∃N, ∀n≥N, f n ∈ s :=
by rw [tendsto_iff_comap, comap_principal, le_principal_iff, mem_at_top_sets]; refl

/-- A function `f` grows to infinity independent of an order-preserving embedding `e`. -/
lemma tendsto_at_top_embedding {α β γ : Type*} [preorder β] [preorder γ]
  {f : α → β} {e : β → γ} {l : filter α}
  (hm : ∀b₁ b₂, e b₁ ≤ e b₂ ↔ b₁ ≤ b₂) (hu : ∀c, ∃b, c ≤ e b) :
  tendsto (e ∘ f) l at_top ↔ tendsto f l at_top :=
begin
  rw [tendsto_at_top, tendsto_at_top],
  split,
  { assume hc b,
    filter_upwards [hc (e b)] assume a, (hm b (f a)).1 },
  { assume hb c,
    rcases hu c with ⟨b, hc⟩,
    filter_upwards [hb b] assume a ha, le_trans hc ((hm b (f a)).2 ha) }
end

lemma tendsto_at_top_at_top [nonempty α] [semilattice_sup α] [preorder β] (f : α → β) :
  tendsto f at_top at_top ↔ ∀ b : β, ∃ i : α, ∀ a : α, i ≤ a → b ≤ f a :=
iff.trans tendsto_infi $ forall_congr $ assume b, tendsto_at_top_principal

lemma tendsto_finset_image_at_top_at_top {i : β → γ} {j : γ → β} (h : ∀x, j (i x) = x) :
  tendsto (λs:finset γ, s.image j) at_top at_top :=
tendsto_infi.2 $ assume s, tendsto_infi' (s.image i) $ tendsto_principal_principal.2 $
  assume t (ht : s.image i ⊆ t),
  calc s = (s.image i).image j :
      by simp only [finset.image_image, (∘), h]; exact finset.image_id.symm
    ... ⊆  t.image j : finset.image_subset_image ht

lemma prod_at_top_at_top_eq {β₁ β₂ : Type*} [inhabited β₁] [inhabited β₂] [semilattice_sup β₁]
  [semilattice_sup β₂] : filter.prod (@at_top β₁ _) (@at_top β₂ _) = @at_top (β₁ × β₂) _ :=
by simp [at_top, prod_infi_left (default β₁), prod_infi_right (default β₂), infi_prod];
    exact infi_comm

lemma prod_map_at_top_eq {α₁ α₂ β₁ β₂ : Type*} [inhabited β₁] [inhabited β₂]
  [semilattice_sup β₁] [semilattice_sup β₂] (u₁ : β₁ → α₁) (u₂ : β₂ → α₂) :
  filter.prod (map u₁ at_top) (map u₂ at_top) = map (prod.map u₁ u₂) at_top :=
by rw [prod_map_map_eq, prod_at_top_at_top_eq, prod.map_def]

/-- A function `f` maps upwards closed sets (at_top sets) to upwards closed sets when it is a
Galois insertion. The Galois "insertion" and "connection" is weakened to only require it to be an
insertion and a connetion above `b'`. -/
lemma map_at_top_eq_of_gc [semilattice_sup α] [semilattice_sup β] {f : α → β} (g : β → α) (b' : β)(hf : monotone f) (gc : ∀a, ∀b≥b', f a ≤ b ↔ a ≤ g b) (hgi : ∀b≥b', b ≤ f (g b)) :
  map f at_top = at_top :=
begin
  rw [@map_at_top_eq α _ ⟨g b'⟩],
  refine le_antisymm
    (le_infi $ assume b, infi_le_of_le (g (b ⊔ b')) $ principal_mono.2 $ image_subset_iff.2 _)
    (le_infi $ assume a, infi_le_of_le (f a ⊔ b') $ principal_mono.2 _),
  { assume a ha, exact (le_trans le_sup_left $ le_trans (hgi _ le_sup_right) $ hf ha) },
  { assume b hb,
    have hb' : b' ≤ b := le_trans le_sup_right hb,
    exact ⟨g b, (gc _ _ hb').1 (le_trans le_sup_left hb),
      le_antisymm ((gc _ _ hb').2 (le_refl _)) (hgi _ hb')⟩ }
end

lemma map_add_at_top_eq_nat (k : ℕ) : map (λa, a + k) at_top = at_top :=
map_at_top_eq_of_gc (λa, a - k) k
  (assume a b h, add_le_add_right h k)
  (assume a b h, (nat.le_sub_right_iff_add_le h).symm)
  (assume a h, by rw [nat.sub_add_cancel h])

lemma map_sub_at_top_eq_nat (k : ℕ) : map (λa, a - k) at_top = at_top :=
map_at_top_eq_of_gc (λa, a + k) 0
  (assume a b h, nat.sub_le_sub_right h _)
  (assume a b _, nat.sub_le_right_iff_le_add)
  (assume b _, by rw [nat.add_sub_cancel])

lemma tendso_add_at_top_nat (k : ℕ) : tendsto (λa, a + k) at_top at_top :=
le_of_eq (map_add_at_top_eq_nat k)

lemma tendso_sub_at_top_nat (k : ℕ) : tendsto (λa, a - k) at_top at_top :=
le_of_eq (map_sub_at_top_eq_nat k)

lemma tendsto_add_at_top_iff_nat {f : ℕ → α} {l : filter α} (k : ℕ) :
  tendsto (λn, f (n + k)) at_top l ↔ tendsto f at_top l :=
show tendsto (f ∘ (λn, n + k)) at_top l ↔ tendsto f at_top l,
  by rw [← tendsto_map'_iff, map_add_at_top_eq_nat]

lemma map_div_at_top_eq_nat (k : ℕ) (hk : k > 0) : map (λa, a / k) at_top = at_top :=
map_at_top_eq_of_gc (λb, b * k + (k - 1)) 1
  (assume a b h, nat.div_le_div_right h)
  (assume a b _,
    calc a / k ≤ b ↔ a / k < b + 1 : by rw [← nat.succ_eq_add_one, nat.lt_succ_iff]
      ... ↔ a < (b + 1) * k : nat.div_lt_iff_lt_mul _ _ hk
      ... ↔ _ :
      begin
        cases k,
        exact (lt_irrefl _ hk).elim,
        simp [mul_add, add_mul, nat.succ_add, nat.lt_succ_iff]
      end)
  (assume b _,
    calc b = (b * k) / k : by rw [nat.mul_div_cancel b hk]
      ... ≤ (b * k + (k - 1)) / k : nat.div_le_div_right $ nat.le_add_right _ _)

/- ultrafilter -/

section ultrafilter
open zorn

variables {f g : filter α}

/-- An ultrafilter is a minimal (maximal in the set order) proper filter. -/
def is_ultrafilter (f : filter α) := f ≠ ⊥ ∧ ∀g, g ≠ ⊥ → g ≤ f → f ≤ g

lemma ultrafilter_unique (hg : is_ultrafilter g) (hf : f ≠ ⊥) (h : f ≤ g) : f = g :=
le_antisymm h (hg.right _ hf h)

lemma le_of_ultrafilter {g : filter α} (hf : is_ultrafilter f) (h : f ⊓ g ≠ ⊥) :
  f ≤ g :=
le_of_inf_eq $ ultrafilter_unique hf h inf_le_left

/-- Equivalent characterization of ultrafilters:
  A filter f is an ultrafilter if and only if for each set s,
  -s belongs to f if and only if s does not belong to f. -/
lemma ultrafilter_iff_compl_mem_iff_not_mem :
  is_ultrafilter f ↔ (∀ s, -s ∈ f.sets ↔ s ∉ f.sets) :=
⟨assume hf s,
   ⟨assume hns hs,
      hf.1 $ empty_in_sets_eq_bot.mp $ by convert f.inter_sets hs hns; rw [inter_compl_self],
    assume hs,
      have f ≤ principal (-s), from
        le_of_ultrafilter hf $ assume h, hs $ mem_sets_of_neq_bot $
          by simp only [h, eq_self_iff_true, lattice.neg_neg],
      by simp only [le_principal_iff] at this; assumption⟩,
 assume hf,
   ⟨mt empty_in_sets_eq_bot.mpr ((hf ∅).mp (by convert f.univ_sets; rw [compl_empty])),
    assume g hg g_le s hs, classical.by_contradiction $ mt (hf s).mpr $
      assume : - s ∈ f.sets,
        have s ∩ -s ∈ g.sets, from inter_mem_sets hs (g_le this),
        by simp only [empty_in_sets_eq_bot, hg, inter_compl_self] at this; contradiction⟩⟩

lemma mem_or_compl_mem_of_ultrafilter (hf : is_ultrafilter f) (s : set α) :
  s ∈ f.sets ∨ - s ∈ f.sets :=
classical.or_iff_not_imp_left.2 (ultrafilter_iff_compl_mem_iff_not_mem.mp hf s).mpr

lemma mem_or_mem_of_ultrafilter {s t : set α} (hf : is_ultrafilter f) (h : s ∪ t ∈ f.sets) :
  s ∈ f.sets ∨ t ∈ f.sets :=
(mem_or_compl_mem_of_ultrafilter hf s).imp_right
  (assume : -s ∈ f.sets, by filter_upwards [this, h] assume x hnx hx, hx.resolve_left hnx)

lemma mem_of_finite_sUnion_ultrafilter {s : set (set α)} (hf : is_ultrafilter f) (hs : finite s)
  : ⋃₀ s ∈ f.sets → ∃t∈s, t ∈ f.sets :=
finite.induction_on hs (by simp only [empty_in_sets_eq_bot, hf.left, mem_empty_eq, sUnion_empty,
  forall_prop_of_false, exists_false, not_false_iff, exists_prop_of_false]) $
λ t s' ht' hs' ih, by simp only [exists_prop, mem_insert_iff, set.sUnion_insert]; exact
assume h, (mem_or_mem_of_ultrafilter hf h).elim
  (assume : t ∈ f.sets, ⟨t, or.inl rfl, this⟩)
  (assume h, let ⟨t, hts', ht⟩ := ih h in ⟨t, or.inr hts', ht⟩)

lemma mem_of_finite_Union_ultrafilter {is : set β} {s : β → set α}
  (hf : is_ultrafilter f) (his : finite is) (h : (⋃i∈is, s i) ∈ f.sets) : ∃i∈is, s i ∈ f.sets :=
have his : finite (image s is), from finite_image s his,
have h : (⋃₀ image s is) ∈ f.sets, from by simp only [sUnion_image, set.sUnion_image]; assumption,
let ⟨t, ⟨i, hi, h_eq⟩, (ht : t ∈ f.sets)⟩ := mem_of_finite_sUnion_ultrafilter hf his h in
⟨i, hi, h_eq.symm ▸ ht⟩

lemma ultrafilter_map {f : filter α} {m : α → β} (h : is_ultrafilter f) : is_ultrafilter (map m f) :=
by rw ultrafilter_iff_compl_mem_iff_not_mem at ⊢ h; exact assume s, h (m ⁻¹' s)

lemma ultrafilter_pure {a : α} : is_ultrafilter (pure a) :=
begin
  rw ultrafilter_iff_compl_mem_iff_not_mem, intro s,
  rw [mem_pure_sets, mem_pure_sets], exact iff.rfl
end

lemma ultrafilter_bind {f : filter α} (hf : is_ultrafilter f) {m : α → filter β}
  (hm : ∀ a, is_ultrafilter (m a)) : is_ultrafilter (f.bind m) :=
begin
  simp only [ultrafilter_iff_compl_mem_iff_not_mem] at ⊢ hf hm, intro s,
  dsimp [bind, join, map],
  simp only [hm], apply hf
end

/-- The ultrafilter lemma: Any proper filter is contained in an ultrafilter. -/
lemma exists_ultrafilter (h : f ≠ ⊥) : ∃u, u ≤ f ∧ is_ultrafilter u :=
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

/-- Construct an ultrafilter extending a given filter.
  The ultrafilter lemma is the assertion that such a filter exists;
  we use the axiom of choice to pick one. -/
noncomputable def ultrafilter_of (f : filter α) : filter α :=
if h : f = ⊥ then ⊥ else classical.epsilon (λu, u ≤ f ∧ is_ultrafilter u)

lemma ultrafilter_of_spec (h : f ≠ ⊥) : ultrafilter_of f ≤ f ∧ is_ultrafilter (ultrafilter_of f) :=
begin
  have h' := classical.epsilon_spec (exists_ultrafilter h),
  simp only [ultrafilter_of, dif_neg, h, dif_neg, not_false_iff],
  simp only at h',
  assumption
end

lemma ultrafilter_of_le : ultrafilter_of f ≤ f :=
if h : f = ⊥ then by simp only [ultrafilter_of, dif_pos, h, dif_pos, eq_self_iff_true, le_bot_iff]; exact le_refl _
  else (ultrafilter_of_spec h).left

lemma ultrafilter_ultrafilter_of (h : f ≠ ⊥) : is_ultrafilter (ultrafilter_of f) :=
(ultrafilter_of_spec h).right

lemma ultrafilter_of_ultrafilter (h : is_ultrafilter f) : ultrafilter_of f = f :=
ultrafilter_unique h (ultrafilter_ultrafilter_of h.left).left ultrafilter_of_le

/-- A filter equals the intersection of all the ultrafilters which contain it. -/
lemma sup_of_ultrafilters (f : filter α) : f = ⨆ (g) (u : is_ultrafilter g) (H : g ≤ f), g :=
begin
  refine le_antisymm _ (supr_le $ λ g, supr_le $ λ u, supr_le $ λ H, H),
  intros s hs,
  -- If s ∉ f.sets, we'll apply the ultrafilter lemma to the restriction of f to -s.
  by_contradiction hs',
  let j : (-s) → α := subtype.val,
  have j_inv_s : j ⁻¹' s = ∅, by
    erw [←preimage_inter_range, subtype.val_range, inter_compl_self, preimage_empty],
  let f' := comap j f,
  have : f' ≠ ⊥,
  { apply mt empty_in_sets_eq_bot.mpr,
    rintro ⟨t, htf, ht⟩,
    suffices : t ⊆ s, from absurd (f.sets_of_superset htf this) hs',
    rw [subset_empty_iff] at ht,
    have : j '' (j ⁻¹' t) = ∅, by rw [ht, image_empty],
    erw [image_preimage_eq_inter_range, subtype.val_range, ←subset_compl_iff_disjoint,
      set.compl_compl] at this,
    exact this },
  rcases exists_ultrafilter this with ⟨g', g'f', u'⟩,
  simp only [supr_sets_eq, mem_Inter] at hs,
  have := hs (g'.map subtype.val) (ultrafilter_map u') (map_le_iff_le_comap.mpr g'f'),
  rw [←le_principal_iff, map_le_iff_le_comap, comap_principal, j_inv_s, principal_empty,
    le_bot_iff] at this,
  exact absurd this u'.1
end

/-- The `tendsto` relation can be checked on ultrafilters. -/
lemma tendsto_iff_ultrafilter (f : α → β) (l₁ : filter α) (l₂ : filter β) :
  tendsto f l₁ l₂ ↔ ∀ g, is_ultrafilter g → g ≤ l₁ → g.map f ≤ l₂ :=
⟨assume h g u gx, le_trans (map_mono gx) h,
 assume h, by rw [sup_of_ultrafilters l₁]; simpa only [tendsto, map_supr, supr_le_iff]⟩

/- The ultrafilter monad. The monad structure on ultrafilters is the
  restriction of the one on filters. -/

def ultrafilter (α : Type u) : Type u := {f : filter α // is_ultrafilter f}

def ultrafilter.map (m : α → β) (u : ultrafilter α) : ultrafilter β :=
⟨u.val.map m, ultrafilter_map u.property⟩

def ultrafilter.pure (x : α) : ultrafilter α := ⟨pure x, ultrafilter_pure⟩

def ultrafilter.bind (u : ultrafilter α) (m : α → ultrafilter β) : ultrafilter β :=
⟨u.val.bind (λ a, (m a).val), ultrafilter_bind u.property (λ a, (m a).property)⟩

instance ultrafilter.has_pure : has_pure ultrafilter := ⟨@ultrafilter.pure⟩
instance ultrafilter.has_bind : has_bind ultrafilter := ⟨@ultrafilter.bind⟩
instance ultrafilter.functor : functor ultrafilter := { map := @ultrafilter.map }
instance ultrafilter.monad : monad ultrafilter := { map := @ultrafilter.map }

section

local attribute [instance] filter.monad filter.is_lawful_monad

instance ultrafilter.is_lawful_monad : is_lawful_monad ultrafilter :=
{ id_map := assume α f, subtype.eq (id_map f.val),
  pure_bind := assume α β a f, subtype.eq (pure_bind a (subtype.val ∘ f)),
  bind_assoc := assume α β γ f m₁ m₂, subtype.eq (filter_eq rfl),
  bind_pure_comp_eq_map := assume α β f x, subtype.eq (bind_pure_comp_eq_map _ f x.val) }

end

lemma ultrafilter.eq_iff_val_le_val {u v : ultrafilter α} : u = v ↔ u.val ≤ v.val :=
⟨assume h, by rw h; exact le_refl _,
 assume h, by rw subtype.ext; apply ultrafilter_unique v.property u.property.1 h⟩

lemma exists_ultrafilter_iff (f : filter α) : (∃ (u : ultrafilter α), u.val ≤ f) ↔ f ≠ ⊥ :=
⟨assume ⟨u, uf⟩, lattice.neq_bot_of_le_neq_bot u.property.1 uf,
 assume h, let ⟨u, uf, hu⟩ := exists_ultrafilter h in ⟨⟨u, hu⟩, uf⟩⟩

end ultrafilter

end filter

namespace filter
variables {α β γ : Type u} {f : β → filter α} {s : γ → set α}
open list

lemma mem_traverse_sets :
  ∀(fs : list β) (us : list γ),
    forall₂ (λb c, s c ∈ (f b).sets) fs us → traverse s us ∈ (traverse f fs).sets
| []      []      forall₂.nil         := mem_pure_sets.2 $ mem_singleton _
| (f::fs) (u::us) (forall₂.cons h hs) := seq_mem_seq_sets (image_mem_map h) (mem_traverse_sets fs us hs)

lemma mem_traverse_sets_iff (fs : list β) (t : set (list α)) :
  t ∈ (traverse f fs).sets ↔
    (∃us:list (set α), forall₂ (λb (s : set α), s ∈ (f b).sets) fs us ∧ sequence us ⊆ t) :=
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
  ∀(as bs : list (filter α)), forall₂ (≤) as bs → sequence as ≤ sequence bs
| []      []      forall₂.nil         := le_refl _
| (a::as) (b::bs) (forall₂.cons h hs) := seq_mono (map_mono h) (sequence_mono as bs hs)

end filter
