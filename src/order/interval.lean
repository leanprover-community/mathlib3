/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.set.intervals.basic
import data.set.lattice

/-!
# Order intervals

This file defines (nonempty) intervals in an order. This is a prototype for interval arithmetic.

## Main declarations

* `nonempty_interval`: Nonempty intervals. Pairs where the second element is greater than the first.
* `interval`: Intervals. Either `∅` or a nonempty interval.
-/

namespace option
variables {α β γ δ : Type*}

lemma map_comm {f₁ : α → β} {f₂ : α → γ} {g₁ : β → δ} {g₂ : γ → δ} (h : g₁ ∘ f₁ = g₂ ∘ f₂) (a : α) :
  (option.map f₁ a).map g₁ = (option.map f₂ a).map g₂ :=
by rw [map_map, h, ←map_map]

end option

namespace with_bot
variables {α β γ δ : Type*} {a b : α}

open function

lemma coe_injective : injective (coe : α → with_bot α) := option.some_injective _
@[norm_cast] lemma coe_inj : (a : with_bot α) = b ↔ a = b := option.some_inj

lemma map_comm {f₁ : α → β} {f₂ : α → γ} {g₁ : β → δ} {g₂ : γ → δ} (h : g₁ ∘ f₁ = g₂ ∘ f₂) (a : α) :
  map g₁ (map f₁ a) = map g₂ (map f₂ a) :=
option.map_comm h _

end with_bot

namespace set
variables {α : Type*} {ι : Sort*} {κ : ι → Sort*} {s : set α} {f : Π i, κ i → set α}

/-- This rather trivial consequence of `subset_Union₂` is convenient with `apply`, and has `i` and
`j` explicit for this purpose. -/
lemma subset_Union₂_of_subset (i : ι) (j : κ i) (h : s ⊆ f i j) : s ⊆ ⋃ i j, f i j :=
@le_supr₂_of_le (set α) _ _ _ _ _ i j h

/-- This rather trivial consequence of `Inter₂_subset` is convenient with `apply`, and has `i` and
`j` explicit for this purpose. -/
lemma Inter₂_subset_of_subset (i : ι) (j : κ i) (h : f i j ⊆ s) : (⋂ i j, f i j) ⊆ s :=
@infi₂_le_of_le (set α) _ _ _ _ _ i j h

end set

open function order_dual set

variables {α β γ : Type*} {ι : Sort*} {κ : ι → Sort*}

/-- The nonempty intervals in an order. -/
@[ext] structure nonempty_interval (α : Type*) [has_le α] extends α × α :=
(fst_le_snd : fst ≤ snd)

namespace nonempty_interval
section has_le
variables [has_le α] {a b : nonempty_interval α}

/-- The injection from which we get the order. -/
def to_dual_prod : nonempty_interval α → αᵒᵈ × α := to_prod

@[simp] lemma to_dual_prod_apply (a : nonempty_interval α) :
  a.to_dual_prod = (to_dual a.fst, a.snd) := prod.mk.eta.symm

lemma to_dual_prod_injective : injective (to_dual_prod : nonempty_interval α → αᵒᵈ × α) :=
λ a b, (ext_iff _ _).2

instance [is_empty α] : is_empty (nonempty_interval α) := ⟨λ a, is_empty_elim a.fst⟩
instance [subsingleton α] : subsingleton (nonempty_interval α) :=
to_dual_prod_injective.subsingleton

instance : has_le (nonempty_interval α) := ⟨λ a b, b.fst ≤ a.fst ∧ a.snd ≤ b.snd⟩

lemma le_def : a ≤ b ↔ b.fst ≤ a.fst ∧ a.snd ≤ b.snd := iff.rfl

/-- Turn an interval into an interval in the dual order. -/
def dual : nonempty_interval α ≃ nonempty_interval αᵒᵈ :=
{ to_fun := λ a, ⟨a.to_prod.swap, a.fst_le_snd⟩,
  inv_fun := λ a, ⟨a.to_prod.swap, a.fst_le_snd⟩,
  left_inv := λ a, ext _ _ $ prod.swap_swap _,
  right_inv := λ a, ext _ _ $ prod.swap_swap _ }

@[simp] lemma fst_dual (a : nonempty_interval α) : a.dual.fst = to_dual a.snd := rfl
@[simp] lemma snd_dual (a : nonempty_interval α) : a.dual.snd = to_dual a.fst := rfl

end has_le

section preorder
variables [preorder α] [preorder β] [preorder γ]

instance : preorder (nonempty_interval α) := preorder.lift to_dual_prod

/-- `{a}` as an interval. -/
@[simps] def pure (a : α) : nonempty_interval α := ⟨⟨a, a⟩, le_rfl⟩

lemma pure_injective : injective (pure : α → nonempty_interval α) :=
λ a b, congr_arg $ prod.fst ∘ to_prod

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

variables [bounded_order α]

instance : order_top (nonempty_interval α) :=
{ top := ⟨⟨⊥, ⊤⟩, bot_le⟩,
  le_top := λ a, ⟨bot_le, le_top⟩ }

@[simp] lemma dual_top : (⊤ : nonempty_interval α).dual = ⊤ := rfl

end preorder

section partial_order
variables [partial_order α]

instance : partial_order (nonempty_interval α) := partial_order.lift _ to_dual_prod_injective

/-- Consider a nonempty interval `[a, b]` as the set `[a, b]`. -/
@[simps] def to_set : nonempty_interval α ↪o set α :=
order_embedding.of_map_le_iff (λ a, Icc a.fst a.snd) (λ a b, Icc_subset_Icc_iff a.fst_le_snd)

@[simp] lemma to_set_pure (a : α) : (pure a).to_set = {a} := Icc_self _
@[simp] lemma to_set_top [bounded_order α] : (⊤ : nonempty_interval α).to_set = univ := Icc_bot_top
@[simp] lemma to_set_dual (a : nonempty_interval α) : a.dual.to_set = of_dual ⁻¹' a.to_set :=
dual_Icc

lemma to_set_nonempty (a : nonempty_interval α) : a.to_set.nonempty := nonempty_Icc.2 a.fst_le_snd

end partial_order

section lattice
variables [lattice α]

instance : has_sup (nonempty_interval α) :=
⟨λ a b, ⟨⟨a.fst ⊓ b.fst, a.snd ⊔ b.snd⟩, inf_le_left.trans $ a.fst_le_snd.trans le_sup_left⟩⟩

instance : semilattice_sup (nonempty_interval α) :=
to_dual_prod_injective.semilattice_sup _ $ λ _ _, rfl

@[simp] lemma fst_sup (a b : nonempty_interval α) : (a ⊔ b).fst = a.fst ⊓ b.fst := rfl
@[simp] lemma snd_sup (a b : nonempty_interval α) : (a ⊔ b).snd = a.snd ⊔ b.snd := rfl

end lattice
end nonempty_interval

/-- The intervals in an order. -/
@[derive [inhabited, has_le, order_bot]]
def interval (α : Type*) [has_le α] := with_bot (nonempty_interval α)

namespace interval
section has_le
variables [has_le α] {a b : interval α}

instance : has_coe_t (nonempty_interval α) (interval α) := with_bot.has_coe_t
instance : can_lift (interval α) (nonempty_interval α) := with_bot.can_lift

lemma coe_injective : injective (coe : nonempty_interval α → interval α) := with_bot.coe_injective
@[simp, norm_cast] lemma coe_inj {a b : nonempty_interval α} : (a : interval α) = b ↔ a = b :=
with_bot.coe_inj

@[protected] lemma «forall» {p : interval α → Prop} :
  (∀ a, p a) ↔ p ⊥ ∧ ∀ a : nonempty_interval α, p a := option.forall
@[protected] lemma «exists» {p : interval α → Prop} :
  (∃ a, p a) ↔ p ⊥ ∨ ∃ a : nonempty_interval α, p a := option.exists

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

instance [nonempty α] : nontrivial (interval α) := option.nontrivial

/-- Pushforward of intervals. -/
def map (f : α →o β) : interval α → interval β := with_bot.map (nonempty_interval.map f)

@[simp] lemma map_pure (f : α →o β) (a : α) : (pure a).map f = pure (f a) := rfl
@[simp] lemma map_map (g : β →o γ) (f : α →o β) (a : interval α) :
  (a.map f).map g = a.map (g.comp f) := option.map_map _ _ _

@[simp] lemma dual_map (f : α →o β) (a : interval α) : (a.map f).dual = a.dual.map f.dual :=
by { cases a, { refl }, { exact with_bot.map_comm rfl _ } }

variables [bounded_order α]

instance : bounded_order (interval α) := with_bot.bounded_order

@[simp] lemma dual_top : (⊤ : interval α).dual = ⊤ := rfl

end preorder

section partial_order
variables [partial_order α] {a b : interval α}

instance : partial_order (interval α) := with_bot.partial_order

/-- Consider a interval `[a, b]` as the set `[a, b]`. -/
def to_set : interval α ↪o set α :=
order_embedding.of_map_le_iff (λ a, match a with
    | ⊥ := ∅
    | some a := a.to_set
  end) (λ a b, match a, b with
  | ⊥, b := iff_of_true bot_le bot_le
  | some a, ⊥ := iff_of_false (λ h, a.to_set_nonempty.ne_empty $ le_bot_iff.1 h)
                   (with_bot.not_coe_le_bot _)
  | some a, some b := (@nonempty_interval.to_set α _).le_iff_le.trans with_bot.some_le_some.symm
  end)

@[simp] lemma to_set_pure (a : α) : (pure a).to_set = {a} := Icc_self _
@[simp] lemma to_set_coe (a : nonempty_interval α) : (a  : interval α).to_set = a.to_set := rfl
@[simp] lemma to_set_bot : (⊥  : interval α).to_set = ∅ := rfl
@[simp] lemma to_set_top [bounded_order α] : (⊤ : interval α).to_set = univ := Icc_bot_top
@[simp] lemma to_set_dual (a : interval α) : a.dual.to_set = of_dual ⁻¹' a.to_set :=
by { cases a, { refl }, exact a.to_set_dual }

lemma to_set_le_to_set : a.to_set ⊆ b.to_set ↔ a ≤ b := (@to_set α _).le_iff_le
lemma to_set_mono : a ≤ b → a.to_set ⊆ b.to_set := to_set_le_to_set.2

end partial_order

section lattice
variables [lattice α]

instance : semilattice_sup (interval α) := with_bot.semilattice_sup

variables [@decidable_rel α (≤)]

instance : lattice (interval α) :=
{ inf := λ a b, match a, b with
    | ⊥, b := ⊥
    | a, ⊥ := ⊥
    | some a, some b := if h : a.fst ≤ b.snd ∧ b.fst ≤ a.snd then some
      ⟨⟨a.fst ⊔ b.fst, a.snd ⊓ b.snd⟩, sup_le (le_inf a.fst_le_snd h.1) $ le_inf h.2 b.fst_le_snd⟩
      else ⊥
  end,
  inf_le_left := λ a b, match a, b with
    | ⊥, ⊥ := bot_le
    | ⊥, some b := bot_le
    | some a, ⊥ := bot_le
    | some a, some b := begin
      change dite _ _ _ ≤ _,
      split_ifs,
      { exact with_bot.some_le_some.2 ⟨le_sup_left, inf_le_left⟩ },
      { exact bot_le }
    end
  end,
  inf_le_right := λ a b, match a, b with
    | ⊥, ⊥ := bot_le
    | ⊥, some b := bot_le
    | some a, ⊥ := bot_le
    | some a, some b := begin
      change dite _ _ _ ≤ _,
      split_ifs,
      { exact with_bot.some_le_some.2 ⟨le_sup_right, inf_le_right⟩ },
      { exact bot_le }
    end
  end,
  le_inf := λ a b c, match a, b, c with
    | ⊥, b, c := λ _ _, bot_le
    | some a, b, c := λ hb hc, begin
      lift b to nonempty_interval α using ne_bot_of_le_ne_bot with_bot.coe_ne_bot hb,
      lift c to nonempty_interval α using ne_bot_of_le_ne_bot with_bot.coe_ne_bot hc,
      change _ ≤ dite _ _ _,
      simp only [with_bot.some_eq_coe, with_bot.coe_le_coe] at ⊢ hb hc,
      rw [dif_pos, with_bot.coe_le_coe],
      exact ⟨sup_le hb.1 hc.1, le_inf hb.2 hc.2⟩,
      exact ⟨hb.1.trans $ a.fst_le_snd.trans hc.2, hc.1.trans $ a.fst_le_snd.trans hb.2⟩,
    end
  end,
  ..interval.semilattice_sup }

@[simp] lemma to_set_inf (a b : interval α) : (a ⊓ b).to_set = a.to_set ∩ b.to_set :=
begin
  cases a,
  { rw [with_bot.none_eq_bot, bot_inf_eq],
    exact (empty_inter _).symm },
  cases b,
  { rw [with_bot.none_eq_bot, inf_bot_eq],
    exact (inter_empty _).symm },
  refine (_ : to_set (dite _ _ _) = _).trans Icc_inter_Icc.symm,
  split_ifs,
  { refl },
  { exact (Icc_eq_empty $ λ H,
      h ⟨le_sup_left.trans $ H.trans inf_le_right, le_sup_right.trans $ H.trans inf_le_left⟩).symm }
end

@[simp] lemma disjoint_to_set (a b : interval α) : disjoint a.to_set b.to_set ↔ disjoint a b :=
by { rw [disjoint, disjoint, ←(@to_set α _).le_iff_le, to_set_inf], refl }

end lattice

section complete_lattice
variables [complete_lattice α]

noncomputable instance : complete_lattice (interval α) :=
by classical; exact
{ Sup := λ s, if h : s ⊆ {⊥} then ⊥ else some
    ⟨⟨⨅ (a : nonempty_interval α) (h : ↑a ∈ s), a.fst,
      ⨆ (a : nonempty_interval α) (h : ↑a ∈ s), a.snd⟩, begin
        obtain ⟨a, hs, ha⟩ := not_subset.1 h,
        lift a to nonempty_interval α using ha,
        exact infi₂_le_of_le a hs (le_supr₂_of_le a hs a.fst_le_snd)
      end⟩,
  le_Sup := λ s a ha, begin
    split_ifs,
    { exact (h ha).le },
    cases a,
    { exact bot_le },
    { exact with_bot.some_le_some.2 ⟨infi₂_le _ ha, le_supr₂_of_le _ ha le_rfl⟩ }
  end,
  Sup_le := λ s a ha, begin
    split_ifs,
    { exact bot_le },
    obtain ⟨b, hs, hb⟩ := not_subset.1 h,
    lift a to nonempty_interval α using ne_bot_of_le_ne_bot hb (ha _ hs),
    exact with_bot.coe_le_coe.2 ⟨le_infi₂ $ λ c hc, (with_bot.coe_le_coe.1 $ ha _ hc).1,
      supr₂_le $ λ c hc, (with_bot.coe_le_coe.1 $ ha _ hc).2⟩,
  end,
  Inf := λ s, if h : ⊥ ∉ s ∧ ∀ ⦃a : nonempty_interval α⦄, ↑a ∈ s → ∀ ⦃b : nonempty_interval α⦄,
    ↑b ∈ s → a.fst ≤ b.snd then some
      ⟨⟨⨆ (a : nonempty_interval α) (h : ↑a ∈ s), a.fst,
        ⨅ (a : nonempty_interval α) (h : ↑a ∈ s), a.snd⟩,
          supr₂_le $ λ a ha, le_infi₂ $ h.2 ha⟩ else ⊥,
  Inf_le := λ s a ha, begin
    split_ifs,
    { lift a to nonempty_interval α using ne_of_mem_of_not_mem ha h.1,
      exact with_bot.coe_le_coe.2 ⟨le_supr₂ a ha, infi₂_le a ha⟩ },
    { exact bot_le }
  end,
  le_Inf := λ s a ha, begin
    cases a,
    { exact bot_le },
    split_ifs,
    { exact with_bot.some_le_some.2 ⟨supr₂_le $ λ b hb, (with_bot.coe_le_coe.1 $ ha _ hb).1,
        le_infi₂ $ λ b hb, (with_bot.coe_le_coe.1 $ ha _ hb).2⟩ },
    rw [not_and_distrib, not_not] at h,
    cases h,
    { exact ha _ h },
    cases h (λ b hb c hc, (with_bot.coe_le_coe.1 $ ha _ hb).1.trans $ a.fst_le_snd.trans
      (with_bot.coe_le_coe.1 $ ha _ hc).2),
  end,
  ..interval.lattice, ..interval.bounded_order }

@[simp] lemma to_set_Inf (s : set (interval α)) : (Inf s).to_set = ⋂ a ∈ s, to_set a :=
begin
  change to_set (dite _ _ _) = _,
  split_ifs,
  { ext,
    simp [with_bot.some_eq_coe, interval.forall, h.1, forall_and_distrib] },
  simp_rw [not_and_distrib, not_not] at h,
  cases h,
  { refine (eq_empty_of_subset_empty _).symm,
    exact Inter₂_subset_of_subset _ h subset.rfl },
  { refine (not_nonempty_iff_eq_empty.1 _).symm,
    rintro ⟨x, hx⟩,
    rw mem_Inter₂ at hx,
    exact h (λ a ha b hb, (hx _ ha).1.trans (hx _ hb).2) }
end

@[simp] lemma to_set_infi (f : ι → interval α) : (⨅ i, f i).to_set = ⋂ i, (f i).to_set :=
by simp [infi]

@[simp] lemma to_set_infi₂ (f : Π i, κ i → interval α) :
  (⨅ i j, f i j).to_set = ⋂ i j, (f i j).to_set :=
by simp_rw [to_set_infi]

end complete_lattice
end interval

namespace nonempty_interval
section preorder
variables [preorder α]

@[simp, norm_cast] lemma coe_pure (a : α) : (pure a : interval α) = interval.pure a := rfl
@[simp, norm_cast] lemma coe_top [bounded_order α] : ((⊤ : nonempty_interval α) : interval α) = ⊤ :=
rfl

end preorder

@[simp, norm_cast] lemma coe_sup [lattice α] (a b : nonempty_interval α) :
  (↑(a ⊔ b) : interval α) = a ⊔ b := rfl

end nonempty_interval
