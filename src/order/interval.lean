/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.set.intervals.basic
import data.set.lattice
import data.set_like.basic

/-!
# Order intervals

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines (nonempty) closed intervals in an order (see `set.Icc`). This is a prototype for
interval arithmetic.

## Main declarations

* `nonempty_interval`: Nonempty intervals. Pairs where the second element is greater than the first.
* `interval`: Intervals. Either `∅` or a nonempty interval.
-/

open function order_dual set

variables {α β γ δ : Type*} {ι : Sort*} {κ : ι → Sort*}

/-- The nonempty closed intervals in an order.

We define intervals by the pair of endpoints `fst`, `snd`. To convert intervals to the set of
elements between these endpoints, use the coercion `nonempty_interval α → set α`. -/
@[ext] structure nonempty_interval (α : Type*) [has_le α] extends α × α :=
(fst_le_snd : fst ≤ snd)

namespace nonempty_interval
section has_le
variables [has_le α] {s t : nonempty_interval α}

lemma to_prod_injective : injective (to_prod : nonempty_interval α → α × α) :=
λ s t, (ext_iff _ _).2

/-- The injection that induces the order on intervals. -/
def to_dual_prod : nonempty_interval α → αᵒᵈ × α := to_prod

@[simp] lemma to_dual_prod_apply (s : nonempty_interval α) :
  s.to_dual_prod = (to_dual s.fst, s.snd) := prod.mk.eta.symm

lemma to_dual_prod_injective : injective (to_dual_prod : nonempty_interval α → αᵒᵈ × α) :=
to_prod_injective

instance [is_empty α] : is_empty (nonempty_interval α) := ⟨λ s, is_empty_elim s.fst⟩
instance [subsingleton α] : subsingleton (nonempty_interval α) :=
to_dual_prod_injective.subsingleton

instance : has_le (nonempty_interval α) := ⟨λ s t, t.fst ≤ s.fst ∧ s.snd ≤ t.snd⟩

lemma le_def : s ≤ t ↔ t.fst ≤ s.fst ∧ s.snd ≤ t.snd := iff.rfl

/-- `to_dual_prod` as an order embedding. -/
@[simps] def to_dual_prod_hom : nonempty_interval α ↪o αᵒᵈ × α :=
{ to_fun := to_dual_prod,
  inj' := to_dual_prod_injective,
  map_rel_iff' := λ _ _, iff.rfl }

/-- Turn an interval into an interval in the dual order. -/
def dual : nonempty_interval α ≃ nonempty_interval αᵒᵈ :=
{ to_fun := λ s, ⟨s.to_prod.swap, s.fst_le_snd⟩,
  inv_fun := λ s, ⟨s.to_prod.swap, s.fst_le_snd⟩,
  left_inv := λ s, ext _ _ $ prod.swap_swap _,
  right_inv := λ s, ext _ _ $ prod.swap_swap _ }

@[simp] lemma fst_dual (s : nonempty_interval α) : s.dual.fst = to_dual s.snd := rfl
@[simp] lemma snd_dual (s : nonempty_interval α) : s.dual.snd = to_dual s.fst := rfl

end has_le

section preorder
variables [preorder α] [preorder β] [preorder γ] [preorder δ] {s : nonempty_interval α} {x : α × α}
  {a : α}

instance : preorder (nonempty_interval α) := preorder.lift to_dual_prod

instance : has_coe_t (nonempty_interval α) (set α) := ⟨λ s, Icc s.fst s.snd⟩
@[priority 100] instance : has_mem α (nonempty_interval α) := ⟨λ a s, a ∈ (s : set α)⟩

@[simp] lemma mem_mk {hx : x.1 ≤ x.2} : a ∈ mk x hx ↔ x.1 ≤ a ∧ a ≤ x.2 := iff.rfl
lemma mem_def : a ∈ s ↔ s.fst ≤ a ∧ a ≤ s.snd := iff.rfl

@[simp] lemma coe_nonempty (s : nonempty_interval α) : (s : set α).nonempty :=
nonempty_Icc.2 s.fst_le_snd

/-- `{a}` as an interval. -/
@[simps] def pure (a : α) : nonempty_interval α := ⟨⟨a, a⟩, le_rfl⟩

lemma mem_pure_self (a : α) : a ∈ pure a := ⟨le_rfl, le_rfl⟩

lemma pure_injective : injective (pure : α → nonempty_interval α) :=
λ s t, congr_arg $ prod.fst ∘ to_prod

@[simp] lemma dual_pure (a : α) : (pure a).dual = pure (to_dual a) := rfl

instance [inhabited α] : inhabited (nonempty_interval α) := ⟨pure default⟩
instance : ∀ [nonempty α], nonempty (nonempty_interval α) := nonempty.map pure
instance [nontrivial α] : nontrivial (nonempty_interval α) := pure_injective.nontrivial

/-- Pushforward of nonempty intervals. -/
@[simps] def map (f : α →o β) (a : nonempty_interval α) : nonempty_interval β :=
⟨a.to_prod.map f f, f.mono a.fst_le_snd⟩

@[simp] lemma map_pure (f : α →o β) (a : α) : (pure a).map f = pure (f a) := rfl
@[simp] lemma map_map (g : β →o γ) (f : α →o β) (a : nonempty_interval α) :
  (a.map f).map g = a.map (g.comp f) := rfl

@[simp] lemma dual_map (f : α →o β) (a : nonempty_interval α) :
  (a.map f).dual = a.dual.map f.dual := rfl

/-- Binary pushforward of nonempty intervals. -/
@[simps]
def map₂ (f : α → β → γ) (h₀ : ∀ b, monotone (λ a, f a b)) (h₁ : ∀ a, monotone (f a)) :
  nonempty_interval α → nonempty_interval β → nonempty_interval γ :=
λ s t, ⟨(f s.fst t.fst, f s.snd t.snd), (h₀ _ s.fst_le_snd).trans $ h₁ _ t.fst_le_snd⟩

@[simp] lemma map₂_pure (f : α → β → γ) (h₀ h₁) (a : α) (b : β) :
  map₂ f h₀ h₁ (pure a) (pure b) = pure (f a b) := rfl

@[simp] lemma dual_map₂ (f : α → β → γ) (h₀ h₁ s t) :
  (map₂ f h₀ h₁ s t).dual = map₂ (λ a b, to_dual $ f (of_dual a) $ of_dual b)
    (λ _, (h₀ _).dual) (λ _, (h₁ _).dual) s.dual t.dual := rfl

variables [bounded_order α]

instance : order_top (nonempty_interval α) :=
{ top := ⟨⟨⊥, ⊤⟩, bot_le⟩,
  le_top := λ a, ⟨bot_le, le_top⟩ }

@[simp] lemma dual_top : (⊤ : nonempty_interval α).dual = ⊤ := rfl

end preorder

section partial_order
variables [partial_order α] [partial_order β] {s t : nonempty_interval α} {x : α × α} {a b : α}

instance : partial_order (nonempty_interval α) := partial_order.lift _ to_dual_prod_injective

/-- Consider a nonempty interval `[a, b]` as the set `[a, b]`. -/
def coe_hom : nonempty_interval α ↪o set α :=
order_embedding.of_map_le_iff (λ s, Icc s.fst s.snd) (λ s t, Icc_subset_Icc_iff s.fst_le_snd)

instance : set_like (nonempty_interval α) α :=
{ coe := λ s, Icc s.fst s.snd,
  coe_injective' := coe_hom.injective }

@[simp, norm_cast] lemma coe_subset_coe : (s : set α) ⊆ t ↔ s ≤ t := (@coe_hom α _).le_iff_le
@[simp, norm_cast] lemma coe_ssubset_coe : (s : set α) ⊂ t ↔ s < t := (@coe_hom α _).lt_iff_lt

@[simp] lemma coe_coe_hom : (coe_hom : nonempty_interval α → set α) = coe := rfl

@[simp, norm_cast] lemma coe_pure (a : α) : (pure a : set α) = {a} := Icc_self _

@[simp] lemma mem_pure : b ∈ pure a ↔ b = a :=
by rw [←set_like.mem_coe, coe_pure, mem_singleton_iff]

@[simp, norm_cast]
lemma coe_top [bounded_order α] : ((⊤ : nonempty_interval α) : set α) = univ := Icc_bot_top

@[simp, norm_cast]
lemma coe_dual (s : nonempty_interval α) : (s.dual : set αᵒᵈ) = of_dual ⁻¹' s := dual_Icc

lemma subset_coe_map (f : α →o β) (s : nonempty_interval α) : f '' s ⊆ s.map f :=
image_subset_iff.2 $ λ a ha, ⟨f.mono ha.1, f.mono ha.2⟩

end partial_order

section lattice
variables [lattice α]

instance : has_sup (nonempty_interval α) :=
⟨λ s t, ⟨⟨s.fst ⊓ t.fst, s.snd ⊔ t.snd⟩, inf_le_left.trans $ s.fst_le_snd.trans le_sup_left⟩⟩

instance : semilattice_sup (nonempty_interval α) :=
to_dual_prod_injective.semilattice_sup _ $ λ _ _, rfl

@[simp] lemma fst_sup (s t : nonempty_interval α) : (s ⊔ t).fst = s.fst ⊓ t.fst := rfl
@[simp] lemma snd_sup (s t : nonempty_interval α) : (s ⊔ t).snd = s.snd ⊔ t.snd := rfl

end lattice
end nonempty_interval

/-- The closed intervals in an order.

We represent intervals either as `⊥` or a nonempty interval given by its endpoints `fst`, `snd`.
To convert intervals to the set of elements between these endpoints, use the coercion
`interval α → set α`. -/
@[derive [inhabited, has_le, order_bot]]
def interval (α : Type*) [has_le α] := with_bot (nonempty_interval α)

namespace interval
section has_le
variables [has_le α] {s t : interval α}

instance : has_coe_t (nonempty_interval α) (interval α) := with_bot.has_coe_t
instance can_lift : can_lift (interval α) (nonempty_interval α) coe (λ r, r ≠ ⊥) :=
with_bot.can_lift

lemma coe_injective : injective (coe : nonempty_interval α → interval α) := with_bot.coe_injective
@[simp, norm_cast] lemma coe_inj {s t : nonempty_interval α} : (s : interval α) = t ↔ s = t :=
with_bot.coe_inj

@[protected] lemma «forall» {p : interval α → Prop} :
  (∀ s, p s) ↔ p ⊥ ∧ ∀ s : nonempty_interval α, p s := option.forall
@[protected] lemma «exists» {p : interval α → Prop} :
  (∃ s, p s) ↔ p ⊥ ∨ ∃ s : nonempty_interval α, p s := option.exists

instance [is_empty α] : unique (interval α) := option.unique

/-- Turn an interval into an interval in the dual order. -/
def dual : interval α ≃ interval αᵒᵈ := nonempty_interval.dual.option_congr

end has_le

section preorder
variables [preorder α] [preorder β] [preorder γ]

instance : preorder (interval α) := with_bot.preorder

/-- `{a}` as an interval. -/
def pure (a : α) : interval α := nonempty_interval.pure a

lemma pure_injective : injective (pure : α → interval α) :=
coe_injective.comp nonempty_interval.pure_injective

@[simp] lemma dual_pure (a : α) : (pure a).dual = pure (to_dual a) := rfl
@[simp] lemma dual_bot : (⊥ : interval α).dual = ⊥ := rfl
@[simp] lemma pure_ne_bot {a : α} : pure a ≠ ⊥ := with_bot.coe_ne_bot
@[simp] lemma bot_ne_pure {a : α} : ⊥ ≠ pure a := with_bot.bot_ne_coe

instance [nonempty α] : nontrivial (interval α) := option.nontrivial

/-- Pushforward of intervals. -/
def map (f : α →o β) : interval α → interval β := with_bot.map (nonempty_interval.map f)

@[simp] lemma map_pure (f : α →o β) (a : α) : (pure a).map f = pure (f a) := rfl
@[simp] lemma map_map (g : β →o γ) (f : α →o β) (s : interval α) :
  (s.map f).map g = s.map (g.comp f) := option.map_map _ _ _

@[simp] lemma dual_map (f : α →o β) (s : interval α) : (s.map f).dual = s.dual.map f.dual :=
by { cases s, { refl }, { exact with_bot.map_comm rfl _ } }

variables [bounded_order α]

instance : bounded_order (interval α) := with_bot.bounded_order

@[simp] lemma dual_top : (⊤ : interval α).dual = ⊤ := rfl

end preorder

section partial_order
variables [partial_order α] [partial_order β] {s t : interval α} {a b : α}

instance : partial_order (interval α) := with_bot.partial_order

/-- Consider a interval `[a, b]` as the set `[a, b]`. -/
def coe_hom : interval α ↪o set α :=
order_embedding.of_map_le_iff (λ s, match s with
    | ⊥ := ∅
    | some s := s
  end) (λ s t, match s, t with
  | ⊥, t := iff_of_true bot_le bot_le
  | some s, ⊥ := iff_of_false (λ h, s.coe_nonempty.ne_empty $ le_bot_iff.1 h)
                   (with_bot.not_coe_le_bot _)
  | some s, some t := (@nonempty_interval.coe_hom α _).le_iff_le.trans with_bot.some_le_some.symm
  end)

instance : set_like (interval α) α :=
{ coe := coe_hom,
  coe_injective' := coe_hom.injective }

@[simp, norm_cast] lemma coe_subset_coe : (s : set α) ⊆ t ↔ s ≤ t := (@coe_hom α _).le_iff_le
@[simp, norm_cast] lemma coe_ssubset_coe : (s : set α) ⊂ t ↔ s < t := (@coe_hom α _).lt_iff_lt
@[simp, norm_cast] lemma coe_pure (a : α) : (pure a : set α) = {a} := Icc_self _
@[simp, norm_cast] lemma coe_coe (s : nonempty_interval α) : ((s : interval α) : set α) = s := rfl
@[simp, norm_cast] lemma coe_bot : ((⊥  : interval α) : set α) = ∅ := rfl
@[simp, norm_cast] lemma coe_top [bounded_order α] : ((⊤ : interval α) : set α) = univ :=
Icc_bot_top
@[simp, norm_cast] lemma coe_dual (s : interval α) : (s.dual : set αᵒᵈ) = of_dual ⁻¹' s :=
by { cases s, { refl }, exact s.coe_dual }

lemma subset_coe_map (f : α →o β) : ∀ s : interval α, f '' s ⊆ s.map f
| ⊥ := by simp
| (s : nonempty_interval α) := s.subset_coe_map _

@[simp] lemma mem_pure : b ∈ pure a ↔ b = a :=
by rw [←set_like.mem_coe, coe_pure, mem_singleton_iff]
lemma mem_pure_self (a : α) : a ∈ pure a := mem_pure.2 rfl

end partial_order

section lattice
variables [lattice α]

instance : semilattice_sup (interval α) := with_bot.semilattice_sup

section decidable
variables [@decidable_rel α (≤)]

instance : lattice (interval α) :=
{ inf := λ s t, match s, t with
    | ⊥, t := ⊥
    | s, ⊥ := ⊥
    | some s, some t := if h : s.fst ≤ t.snd ∧ t.fst ≤ s.snd then some
      ⟨⟨s.fst ⊔ t.fst, s.snd ⊓ t.snd⟩, sup_le (le_inf s.fst_le_snd h.1) $ le_inf h.2 t.fst_le_snd⟩
      else ⊥
  end,
  inf_le_left := λ s t, match s, t with
    | ⊥, ⊥ := bot_le
    | ⊥, some t := bot_le
    | some s, ⊥ := bot_le
    | some s, some t := begin
      change dite _ _ _ ≤ _,
      split_ifs,
      { exact with_bot.some_le_some.2 ⟨le_sup_left, inf_le_left⟩ },
      { exact bot_le }
    end
  end,
  inf_le_right := λ s t, match s, t with
    | ⊥, ⊥ := bot_le
    | ⊥, some t := bot_le
    | some s, ⊥ := bot_le
    | some s, some t := begin
      change dite _ _ _ ≤ _,
      split_ifs,
      { exact with_bot.some_le_some.2 ⟨le_sup_right, inf_le_right⟩ },
      { exact bot_le }
    end
  end,
  le_inf := λ s t c, match s, t, c with
    | ⊥, t, c := λ _ _, bot_le
    | some s, t, c := λ hb hc, begin
      lift t to nonempty_interval α using ne_bot_of_le_ne_bot with_bot.coe_ne_bot hb,
      lift c to nonempty_interval α using ne_bot_of_le_ne_bot with_bot.coe_ne_bot hc,
      change _ ≤ dite _ _ _,
      simp only [with_bot.some_eq_coe, with_bot.coe_le_coe] at ⊢ hb hc,
      rw [dif_pos, with_bot.coe_le_coe],
      exact ⟨sup_le hb.1 hc.1, le_inf hb.2 hc.2⟩,
      exact ⟨hb.1.trans $ s.fst_le_snd.trans hc.2, hc.1.trans $ s.fst_le_snd.trans hb.2⟩,
    end
  end,
  ..interval.semilattice_sup }

@[simp, norm_cast] lemma coe_inf (s t : interval α) : (↑(s ⊓ t) : set α) = s ∩ t :=
begin
  cases s,
  { rw [with_bot.none_eq_bot, bot_inf_eq],
    exact (empty_inter _).symm },
  cases t,
  { rw [with_bot.none_eq_bot, inf_bot_eq],
    exact (inter_empty _).symm },
  refine (_ : coe (dite _ _ _) = _).trans Icc_inter_Icc.symm,
  split_ifs,
  { refl },
  { exact (Icc_eq_empty $ λ H,
      h ⟨le_sup_left.trans $ H.trans inf_le_right, le_sup_right.trans $ H.trans inf_le_left⟩).symm }
end

end decidable

@[simp, norm_cast]
lemma disjoint_coe (s t : interval α) : disjoint (s : set α) t ↔ disjoint s t :=
begin
  classical,
  rw [disjoint_iff_inf_le, disjoint_iff_inf_le, le_eq_subset, ←coe_subset_coe, coe_inf], refl
end

end lattice
end interval

namespace nonempty_interval
section preorder
variables [preorder α] {s : nonempty_interval α} {a : α}

@[simp, norm_cast] lemma coe_pure_interval (a : α) : (pure a : interval α) = interval.pure a := rfl
@[simp, norm_cast] lemma coe_eq_pure : (s : interval α) = interval.pure a ↔ s = pure a :=
by rw [←interval.coe_inj, coe_pure_interval]

@[simp, norm_cast]
lemma coe_top_interval [bounded_order α] : ((⊤ : nonempty_interval α) : interval α) = ⊤ := rfl

end preorder

@[simp, norm_cast]
lemma mem_coe_interval [partial_order α] {s : nonempty_interval α} {x : α} :
  x ∈ (s : interval α) ↔ x ∈ s := iff.rfl

@[simp, norm_cast] lemma coe_sup_interval [lattice α] (s t : nonempty_interval α) :
  (↑(s ⊔ t) : interval α) = s ⊔ t := rfl

end nonempty_interval

namespace interval
section complete_lattice
variables [complete_lattice α]

noncomputable instance [@decidable_rel α (≤)] : complete_lattice (interval α) :=
by classical; exact { Sup := λ S, if h : S ⊆ {⊥} then ⊥ else some
    ⟨⟨⨅ (s : nonempty_interval α) (h : ↑s ∈ S), s.fst,
      ⨆ (s : nonempty_interval α) (h : ↑s ∈ S), s.snd⟩, begin
        obtain ⟨s, hs, ha⟩ := not_subset.1 h,
        lift s to nonempty_interval α using ha,
        exact infi₂_le_of_le s hs (le_supr₂_of_le s hs s.fst_le_snd)
      end⟩,
  le_Sup := λ s s ha, begin
    split_ifs,
    { exact (h ha).le },
    cases s,
    { exact bot_le },
    { exact with_bot.some_le_some.2 ⟨infi₂_le _ ha, le_supr₂_of_le _ ha le_rfl⟩ }
  end,
  Sup_le := λ s s ha, begin
    split_ifs,
    { exact bot_le },
    obtain ⟨b, hs, hb⟩ := not_subset.1 h,
    lift s to nonempty_interval α using ne_bot_of_le_ne_bot hb (ha _ hs),
    exact with_bot.coe_le_coe.2 ⟨le_infi₂ $ λ c hc, (with_bot.coe_le_coe.1 $ ha _ hc).1,
      supr₂_le $ λ c hc, (with_bot.coe_le_coe.1 $ ha _ hc).2⟩,
  end,
  Inf := λ S, if h : ⊥ ∉ S ∧ ∀ ⦃s : nonempty_interval α⦄, ↑s ∈ S → ∀ ⦃t : nonempty_interval α⦄,
    ↑t ∈ S → s.fst ≤ t.snd then some
      ⟨⟨⨆ (s : nonempty_interval α) (h : ↑s ∈ S), s.fst,
        ⨅ (s : nonempty_interval α) (h : ↑s ∈ S), s.snd⟩,
          supr₂_le $ λ s hs, le_infi₂ $ h.2 hs⟩ else ⊥,
  Inf_le := λ s s ha, begin
    split_ifs,
    { lift s to nonempty_interval α using ne_of_mem_of_not_mem ha h.1,
      exact with_bot.coe_le_coe.2 ⟨le_supr₂ s ha, infi₂_le s ha⟩ },
    { exact bot_le }
  end,
  le_Inf := λ S s ha, begin
    cases s,
    { exact bot_le },
    split_ifs,
    { exact with_bot.some_le_some.2 ⟨supr₂_le $ λ t hb, (with_bot.coe_le_coe.1 $ ha _ hb).1,
        le_infi₂ $ λ t hb, (with_bot.coe_le_coe.1 $ ha _ hb).2⟩ },
    rw [not_and_distrib, not_not] at h,
    cases h,
    { exact ha _ h },
    cases h (λ t hb c hc, (with_bot.coe_le_coe.1 $ ha _ hb).1.trans $ s.fst_le_snd.trans
      (with_bot.coe_le_coe.1 $ ha _ hc).2),
  end,
  ..interval.lattice, ..interval.bounded_order }

@[simp, norm_cast] lemma coe_Inf [@decidable_rel α (≤)] (S : set (interval α)) :
  ↑(Inf S) = ⋂ s ∈ S, (s : set α) :=
begin
  change coe (dite _ _ _) = _,
  split_ifs,
  { ext,
    simp [with_bot.some_eq_coe, interval.forall, h.1, ←forall_and_distrib,
      ←nonempty_interval.mem_def] },
  simp_rw [not_and_distrib, not_not] at h,
  cases h,
  { refine (eq_empty_of_subset_empty _).symm,
    exact Inter₂_subset_of_subset _ h subset.rfl },
  { refine (not_nonempty_iff_eq_empty.1 _).symm,
    rintro ⟨x, hx⟩,
    rw mem_Inter₂ at hx,
    exact h (λ s ha t hb, (hx _ ha).1.trans (hx _ hb).2) }
end

@[simp, norm_cast] lemma coe_infi [@decidable_rel α (≤)] (f : ι → interval α) :
  ↑(⨅ i, f i) = ⋂ i, (f i : set α) :=
by simp [infi]

@[simp, norm_cast] lemma coe_infi₂ [@decidable_rel α (≤)] (f : Π i, κ i → interval α) :
  ↑(⨅ i j, f i j) = ⋂ i j, (f i j : set α) :=
by simp_rw [coe_infi]

end complete_lattice
end interval
