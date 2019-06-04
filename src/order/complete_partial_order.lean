/- Chain-complete partial orders
Helpful for a small-scale domain theory, see
  http://home.in.tum.de/~hoelzl/documents/lochbihler2014recursive.pdf
-/

import data.pfun
import data.stream.basic
import tactic.wlog

universes u v

local attribute [instance] classical.prop_decidable

/- Chains (totally ordered sets) -/

-- domain theory
structure chain (α : Type u) [preorder α] :=
(elems : stream α)
(mono : monotone elems)

-- ensemble filtrés /- directed order -/
-- partial_order + (non-unique) upper bound of finite sets

namespace stream

variables {α : Type u} {β : Type v} {γ : Type*}
variables [preorder α] [preorder β] [preorder γ]

variables {f : α → β} (hf : monotone f)
          {s : stream α} (hs : monotone s)

lemma monotone_map : monotone (s.map f) :=
λ i j h, hf (hs h)

end stream

namespace chain

variables {α : Type u} {β : Type v} {γ : Type*}
variables [preorder α] [preorder β] [preorder γ]

instance : has_mem α (chain α) :=
⟨λa c, a ∈ c.elems⟩

@[simp] lemma mem_mk (x : α) (s : stream α) (h) : x ∈ chain.mk s h ↔ x ∈ s := iff.refl _

def nth (i : ℕ) (c : chain α) : α := c.elems.nth i

@[simp] lemma nth_mk (i : ℕ) (s : stream α) (h) : (chain.mk s h).nth i = s.nth i := rfl

-- instance : has_emptyc (chain α) :=
-- ⟨ ⟨∅, assume x Hx, false.elim Hx⟩ ⟩

variables (c c' : chain α)
  (f : α → β) (hf : monotone f)
  {g : β → γ} (hg : monotone g)

instance : has_le (chain α) :=
{ le := λ x y, ∀ a, a ∈ x → ∃ b ∈ y, a ≤ b  }

@[extensionality]
lemma ext (h : ∀ i, c.nth i = c'.nth i) : c = c' :=
by cases c; cases c'; congr; ext; apply h

-- lemma eq_empty_iff (c : chain α) : c = ∅ ↔ (∀ x, ¬ x ∈ c) :=
-- begin
--   split; intro h, subst c, rintros x ⟨ ⟩,
--   ext, split; intro h', cases h _ h', cases h',
-- end

def map : chain β :=
⟨c.elems.map f, stream.monotone_map hf c.mono ⟩

variables {f}

@[simp] lemma elems_map (c : chain α) : (c.map f hf).elems = c.elems.map f := rfl

lemma mem_map (x : α) : x ∈ c → f x ∈ chain.map c f hf :=
stream.mem_map _

lemma exists_of_mem_map {b : β} : b ∈ c.map f hf → ∃ a, a ∈ c ∧ f a = b :=
stream.exists_of_mem_map

lemma mem_map_iff {b : β} : b ∈ c.map f hf ↔ ∃ a, a ∈ c ∧ f a = b :=
⟨ exists_of_mem_map _ _, λ h, by { rcases h with ⟨w,h,h'⟩, subst b, apply mem_map c hf _ h, } ⟩

lemma chain_map_le (c' : chain β) (h : ∀ a, a ∈ c → f a ∈ c') : chain.map c f hf ≤ c' :=
begin
  intros b hb,
  rcases exists_of_mem_map _ hf hb with ⟨a,h₀,h₁⟩,
  subst b, existsi [f a,h _ h₀], refl
end

lemma le_chain_map (c' : chain β) (h : ∀ b, b ∈ c' → ∃ a, b ≤ f a ∧ a ∈ c) : c' ≤ chain.map c f hf :=
begin
  intros b hb,
  replace h := h _ hb, rcases h with ⟨a,h₀,h₁⟩,
  exact ⟨f a,mem_map _ hf _ h₁,h₀⟩
end

lemma map_le_map {g : α → β} (hg : monotone g) (h : ∀ a ∈ c, f a ≤ g a) : c.map f hf ≤ c.map g hg :=
begin
  intros a ha,
  replace ha := exists_of_mem_map _ _ ha,
  rcases ha with ⟨a',ha₀,ha₁⟩,
  existsi [g a', mem_map _ hg _ ha₀],
  rw ← ha₁, apply h _ ha₀,
end

lemma map_comp : (c.map f hf).map g hg = c.map (g ∘ f) (monotone_comp hf hg) := rfl

end chain

/- COMPLETE_PARTIAL_ORDERs (complete partial orders) -/
class complete_partial_order (α : Type*) extends partial_order α :=
(Sup     : chain α → α)
(le_Sup  : ∀(c:chain α), ∀x∈c, x ≤ Sup c)
(Sup_le  : ∀(c:chain α) x, (∀y∈c, y ≤ x) → Sup c ≤ x)

namespace complete_partial_order
variables {α : Type u} {β : Type v} {γ : Type*}
variables [complete_partial_order α]

export lattice.order_bot (bot_le)

lemma le_Sup_of_le {c : chain α} {x y : α} (h : x ≤ y) (hy : y ∈ c) : x ≤ Sup c :=
le_trans h (le_Sup c y hy)

lemma Sup_total {c : chain α} {x : α} (h : ∀y∈c, y ≤ x ∨ x ≤ y) : Sup c ≤ x ∨ x ≤ Sup c :=
classical.by_cases
  (assume : ∀y ∈ c, y ≤ x, or.inl (Sup_le _ _ this))
  (assume : ¬ ∀y ∈ c, y ≤ x,
    have ∃y∈c, ¬ y ≤ x,
      by simp only [not_forall] at this ⊢; assumption,
    let ⟨y, hy, hyx⟩ := this in
    have x ≤ y, from (h y hy).resolve_left hyx,
    or.inr $ le_Sup_of_le this hy)

lemma Sup_le_Sup_of_le {c₀ c₁ : chain α} (h : c₀ ≤ c₁) : Sup c₀ ≤ Sup c₁ :=
Sup_le _ _ $
λ y hy, Exists.rec_on (h y hy) $
λ x ⟨hx,hxy⟩, le_trans hxy $ le_Sup _ _ hx

lemma Sup_le_iff (c : chain α) (x : α) : Sup c ≤ x ↔ (∀ y ∈ c, y ≤ x) :=
begin
  split; intros,
  { transitivity Sup c,
    apply le_Sup _ _ H, exact a },
  apply Sup_le _ _ a,
end

section continuity
open chain

variables [complete_partial_order β]
          [complete_partial_order γ]
  (f : α → β) (hf : monotone f)
  (g : β → γ) (hg : monotone g)

def continuous :=
∀ C : chain α, f (Sup C) = Sup (C.map f hf)

lemma continuous_comp (hfc : continuous f hf) (hgc : continuous g hg) :
  continuous (g ∘ f) (monotone_comp hf hg) :=
begin
  dsimp [continuous] at *, intro,
  rw [hfc,hgc,chain.map_comp]
end

variables (h' : ∀ C, f (Sup C) ≤ Sup (chain.map C f hf))
include h'

lemma continuous_of_le  : continuous f hf  :=
begin
  intro, apply le_antisymm (h' C),
  rw Sup_le_iff,
  intros y hy,
  replace hy := exists_of_mem_map C hf hy,
  rcases hy with ⟨x,hx,⟨hx'⟩⟩,
  apply hf, apply le_Sup _ _ hx
end

end continuity

end complete_partial_order

namespace roption

variables {α : Type u} {β : Type v} {γ : Type*}
open lattice (has_bot order_bot)
open complete_partial_order

lemma eq_of_chain {c : chain (roption α)} {a b : α} (ha : some a ∈ c) (hb : some b ∈ c) : a = b :=
begin
  cases ha with i ha, replace ha := ha.symm,
  cases hb with j hb, replace hb := hb.symm,
  wlog h : i ≤ j := le_total i j using [a b i j,b a j i],
  rw [eq_some_iff] at ha hb,
  have := c.mono h _ ha, apply mem_unique this hb
end

protected noncomputable def Sup (c : chain (roption α)) : roption α :=
if h : ∃a, some a ∈ c then some (classical.some h) else none

lemma Sup_eq_some {c : chain (roption α)} {a : α} (h : some a ∈ c) : roption.Sup c = some a :=
have ∃a, some a ∈ c, from ⟨a, h⟩,
have a' : some (classical.some this) ∈ c, from classical.some_spec this,
calc roption.Sup c = some (classical.some this) : dif_pos this
               ... = some a : congr_arg _ (eq_of_chain a' h)

lemma Sup_eq_none {c : chain (roption α)} (h : ¬∃a, some a ∈ c) : roption.Sup c = none :=
dif_neg h

lemma mem_chain_of_mem_Sup {c : chain (roption α)} {a : α} (h : a ∈ roption.Sup c) : some a ∈ c :=
begin
  simp [roption.Sup] at h, split_ifs at h,
  { have h' := classical.some_spec h_1,
    rw ← eq_some_iff at h, rw ← h, exact h' },
  { rcases h with ⟨ ⟨ ⟩ ⟩ }
end

noncomputable def complete_partial_order : complete_partial_order (roption α) :=
{ Sup    := roption.Sup,
  le_Sup := λ c x hx, by { intros a ha, rw ← eq_some_iff at ha, subst x,
                           rw Sup_eq_some hx, apply mem_some },
  Sup_le := by { intros c x hx a ha, replace ha := mem_chain_of_mem_Sup ha,
                 apply hx _ ha _ (mem_some _) } }

end roption

namespace pi

variables (α : Type*) (β : α → Type v)

lemma monotone_apply [∀a, partial_order (β a)] (a : α) : monotone (λf:Πa, β a, f a) :=
assume f g hfg, hfg a

lemma monotone_lambda {γ : Type*} [∀a, partial_order (β a)] [partial_order γ] {m : γ → Πa, β a}
  (hm : ∀a, monotone (λc, m c a)) : monotone m :=
assume f g h a, hm a h

open complete_partial_order chain

instance [∀a, complete_partial_order (β a)] :
  complete_partial_order (Πa, β a) :=
{ Sup    := λc a, Sup (c.map _ (monotone_apply α β a)),
  Sup_le := assume c f hf a, Sup_le _ _ $ by { rintro b ⟨i,⟨ ⟩⟩, apply hf, exact ⟨i,rfl⟩ },
  le_Sup := assume c x hx a, le_Sup _ _ $ by { rw mem_map_iff, exact ⟨x,hx,rfl⟩ } }

end pi

namespace set
variables (α : Type u)

instance : partial_order (set α) :=
{ le          := (⊆),
  le_refl     := assume s x hx, hx,
  le_trans    := assume a b c hab hbc x hx, hbc $ hab $ hx,
  le_antisymm := assume a b hab hba, ext $ assume x, ⟨@hab x, @hba x⟩ }

instance : complete_partial_order (set α) :=
{ Sup    := λc, ⋃ i, c.elems i,
  Sup_le := assume ⟨c, _⟩ s hs x, by simp [stream.mem_def] at ⊢ hs; intros i hx; apply hs _ i rfl hx,
  le_Sup := assume ⟨c, _⟩ s hs x hxs, by simp [stream.mem_def,stream.nth] at ⊢ hs;
                                         cases hs with i hs; exact ⟨_,(hs ▸ hxs : x ∈ c i)⟩ }

end set
