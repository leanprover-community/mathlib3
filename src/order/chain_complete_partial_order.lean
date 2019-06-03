/- Chain-complete partial orders
Helpful for a small-scale domain theory, see
  http://home.in.tum.de/~hoelzl/documents/lochbihler2014recursive.pdf
-/

-- import logic.basic
-- import data.stream.basic
-- import order.basic
-- import order.bounded_lattice
import data.pfun
-- import data.nat.up
import tactic.wlog

universes u v

local attribute [instance] classical.prop_decidable

/- Chains (totally ordered sets) -/

section chain
variables (α : Type u) {β : Type v} {γ : Type*} [preorder α] [preorder β] [preorder γ]

structure chain :=
(elems : set α)
(linear_ordered : ∀x∈elems, ∀y∈elems, x ≤ y ∨ y ≤ x)

instance : has_mem α (chain α) :=
⟨λa c, a ∈ c.elems⟩

@[simp] lemma mem_chain_mk (x : α) (s : set α) (h) : x ∈ chain.mk s h ↔ x ∈ s := iff.refl _

instance : has_emptyc (chain α) :=
⟨ ⟨∅, assume x Hx, false.elim Hx⟩ ⟩

variables {α}
variables (c c' : chain α)
  {f : α → β} (hf : monotone f)
  {g : β → γ} (hg : monotone g)

instance : has_le (chain α) :=
{ le := λ x y, ∀ a, a ∈ x → ∃ b ∈ y, a ≤ b  }

@[extensionality]
lemma ext (h : ∀ x, x ∈ c ↔ x ∈ c') : c = c' :=
by cases c; cases c'; congr; ext; simp at h; apply h

def chain.map : chain β :=
⟨{b | ∃a∈c, f a = b},
  assume x hx y hy,
  match x, y, hx, hy with
  | _, _, ⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩ := (c.linear_ordered x hx y hy).imp (@hf _ _) (@hf _ _)
  end⟩

lemma mem_chain.map (x : α) : x ∈ c → f x ∈ chain.map c hf :=
by simp [chain.map]; intros h; exact ⟨_,h,rfl⟩

lemma exists_of_mem_map {b : β} : b ∈ c.map hf → ∃ a, a ∈ c ∧ f a = b :=
by simp [chain.map]; introv h₀ h₁; exact ⟨_,h₀,h₁⟩

lemma chain_map_le (c' : chain β) (h : ∀ a, a ∈ c → f a ∈ c') : chain.map c hf ≤ c' :=
begin
  intros b hb,
  rcases exists_of_mem_map _ hf hb with ⟨a,h₀,h₁⟩,
  subst b, existsi [f a,h _ h₀], refl
end

lemma le_chain_map (c' : chain β) (h : ∀ b, b ∈ c' → ∃ a, b ≤ f a ∧ a ∈ c) : c' ≤ chain.map c hf :=
begin
  intros b hb,
  replace h := h _ hb, rcases h with ⟨a,h₀,h₁⟩,
  exact ⟨f a,mem_chain.map _ hf _ h₁,h₀⟩
end

lemma map_comp : (c.map hf).map hg = c.map (monotone_comp hf hg) :=
by { dsimp [chain.map], congr, ext, simp,
     split; intro h,
     { rcases h with ⟨b,⟨a,ha,hfab⟩,hb⟩, subst b, exact ⟨_,ha,hb⟩ },
     { rcases h with ⟨a,ha,ha'⟩,
       exact ⟨f a,⟨_,ha,rfl⟩,ha'⟩ }, }

end chain
/- CCPOs (chain complete partial orders) -/

class chain_complete_partial_order (α : Type*) extends partial_order α :=
(Sup     : chain α → α)
(le_Sup  : ∀(c:chain α), ∀x∈c, x ≤ Sup c)
(Sup_le  : ∀(c:chain α) x, (∀y∈c, y ≤ x) → Sup c ≤ x)

namespace chain_complete_partial_order
variables {α : Type*} [chain_complete_partial_order α]

def bot : α := Sup ∅

lemma bot_le (x : α) : bot ≤ x :=
Sup_le ∅ _ (assume x, false.elim)

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

section continuity

variables {β : Type*} [chain_complete_partial_order β]
          {γ : Type*} [chain_complete_partial_order γ]
  (f : α → β) (hf : monotone f)
  (g : β → γ) (hg : monotone g)

def continuous :=
∀ C : chain α, f (Sup C) = Sup (C.map hf)

lemma continuous_comp (hfc : continuous f hf) (hgc : continuous g hg) :
  continuous (g ∘ f) (monotone_comp hf hg) :=
begin
  dsimp [continuous] at *, intro,
  rw [hfc,hgc,map_comp]
end

end continuity

/- Fixed point construction  -/

inductive iterates (f : α → α) : α → Prop
| step (a : α) : iterates a → iterates (f a)
| Sup (c : chain α) : (∀x ∈ c, iterates x) → iterates (Sup c)

variables (f : α → α) (hf : monotone f)
include hf

lemma iterates_le (a : α) (h : iterates f a) : a ≤ f a :=
iterates.rec_on h
  (assume a h ih, show f a ≤ f (f a), from hf ih)
  (assume c h ih, show Sup c ≤ f (Sup c), from
    Sup_le _ _ $
    assume a (ha : a ∈ c),
    have a ≤ Sup c, from le_Sup c a ha,
    calc a ≤ f a : ih a ha
      ... ≤ f (Sup c) : hf this)

def chain_iterates : chain α :=
begin
  refine ⟨iterates f, _⟩,
  assume x hx y hy, show x ≤ y ∨ y ≤ x,
  induction hx generalizing y hy,
  case iterates.step : x hx ih_x {
    show f x ≤ y ∨ y ≤ f x,
    induction hy,
    case iterates.step : z hz ih_z {
      have : x ≤ z ∨ z ≤ x := ih_x z hz,
      exact this.imp (@hf _ _) (@hf _ _) },
    case iterates.Sup : c h ih {
      exact (or.swap $ Sup_total $ assume y hy, or.swap $ ih y hy) } },
  case iterates.Sup : c h ih {
    exact Sup_total (assume z hz, ih z hz y hy) }
end

def lfp : α := Sup (chain_iterates f hf)

lemma iterates.lfp : iterates f (lfp f hf) :=
iterates.Sup _ $ assume x hx, hx

lemma lfp_induction
  {p : α → Prop} (h₀ : ∀a, p a → p (f a)) (h₁ : ∀c:chain α, (∀a∈c, p a) → p (Sup c)) :
  p (lfp f hf) :=
iterates.rec_on (iterates.lfp f hf) (assume a _, h₀ a) (assume a _, h₁ a)

lemma lfp_eq : lfp f hf = f (lfp f hf) :=
le_antisymm
  (Sup_le _ _ $ assume y hy,
    calc y ≤ f y : iterates_le f hf _ hy
       ... ≤ f (lfp f hf) : hf $ le_Sup _ _ hy)
  (le_Sup _ _ $ (iterates.lfp f hf).step _)

end chain_complete_partial_order

namespace roption

open lattice (has_bot order_bot)
open chain_complete_partial_order (hiding bot_le)
variables {α : Type u}

lemma eq_of_chain {c : chain (roption α)} {a b : α} (ha : some a ∈ c) (hb : some b ∈ c) : a = b :=
begin
  wlog h : some a ≤ some b := c.linear_ordered (some a) ha _ hb using [a b,b a],
  replace this := h _ (mem_some a), rw mem_some_iff at this, exact this
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

noncomputable def chain_complete_partial_order : chain_complete_partial_order (roption α) :=
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

open chain_complete_partial_order

instance chain_complete_partial_order [∀a, chain_complete_partial_order (β a)] :
  chain_complete_partial_order (Πa, β a) :=
{ Sup    := λc a, Sup (c.map (monotone_apply α β a)),
  Sup_le := assume c f hf a, Sup_le _ _ $ assume b ⟨x, hx, eq⟩, eq ▸ hf x hx a,
  le_Sup := assume c x hx a, le_Sup _ _ ⟨x, hx, rfl⟩ }


end pi

namespace set
variables (α : Type u)

instance : partial_order (set α) :=
{ le          := (⊆),
  le_refl     := assume s x hx, hx,
  le_trans    := assume a b c hab hbc x hx, hbc $ hab $ hx,
  le_antisymm := assume a b hab hba, ext $ assume x, ⟨@hab x, @hba x⟩ }

instance : chain_complete_partial_order (set α) :=
{ Sup    := λc, ⋃₀ c.elems,
  Sup_le := assume ⟨c, _⟩ s hs x ⟨t, (ht : t ∈ c), hxt⟩, hs t ht hxt,
  le_Sup := assume ⟨c, _⟩ s hs x hxs, ⟨s, hs, hxs⟩ }

end set
