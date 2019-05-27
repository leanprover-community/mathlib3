/- complete partial orders
Helpful for a small-scale domain theory, see
  http://home.in.tum.de/~hoelzl/documents/lochbihler2014recursive.pdf
-/

import data.pfun
import data.stream.basic
import tactic.wlog

universes u v

open_locale classical

section mono
variables {α : Type*} {β : Type*}
variables  [preorder α]

lemma const_mono [preorder β] (f : β) : monotone (λ _ : α, f) :=
assume x y h, le_refl _

lemma ite_mono [preorder β] {f g : α → β}
  {p : Prop} {h : decidable p}
  (hf : monotone f) (hg : monotone g) :
  monotone (λ x, @ite _ h _ (f x) (g x)) :=
by intros x y h; dsimp; split_ifs; [apply hf h, apply hg h]

lemma bind_mono {β γ} (f : α → roption β)
                (g : α → β → roption γ)
  (hf : monotone f) (hg : monotone g) :
  monotone (λ x, f x >>= g x)  :=
begin
  intros x y h a, simp, intros b hb ha,
  refine ⟨b,hf h _ hb,hg h _ _ ha⟩,
end

end mono


/-- Chains are monotonically increasing sequences -/
structure chain (α : Type u) [preorder α] :=
(elems : stream α)
(mono : monotone elems)

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

variables (c c' : chain α)
  (f : α → β) (hf : monotone f)
  {g : β → γ} (hg : monotone g)

instance : has_le (chain α) :=
{ le := λ x y, ∀ a, a ∈ x → ∃ b ∈ y, a ≤ b  }

@[ext]
lemma ext (h : ∀ i, c.nth i = c'.nth i) : c = c' :=
by cases c; cases c'; congr; ext; apply h

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

lemma map_id : c.map id (monotone_id) = c :=
by cases c; refl

lemma map_comp : (c.map f hf).map g hg = c.map (g ∘ f) (monotone.comp hg hf) := rfl

lemma le_total_of_mem_of_mem {x y : α} (h : x ∈ c) (h' : y ∈ c) : x ≤ y ∨ y ≤ x :=
begin
  cases c, simp [stream.mem_def] at h h',
  cases h with i h, cases h' with j h',
  wlog : i ≤ j := le_total i j using [x y i j,y x j i],
  subst h, subst h', left, apply c_mono case,
end

end chain

section prio
set_option default_priority 100 -- see Note [default priority]

/- CPOs (complete partial orders) -/
class complete_partial_order (α : Type*) extends partial_order α :=
(Sup     : chain α → α)
(le_Sup  : ∀(c:chain α), ∀x∈c, x ≤ Sup c)
(Sup_le  : ∀(c:chain α) x, (∀y∈c, y ≤ x) → Sup c ≤ x)

end prio

namespace complete_partial_order
variables {α : Type u} {β : Type v} {γ : Type*}
variables [complete_partial_order α]

export order_bot (bot_le)

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

def continuous' := ∃ h, continuous f h

lemma continuous_comp (hfc : continuous f hf) (hgc : continuous g hg) :
  continuous (g ∘ f) (monotone.comp hg hf) :=
begin
  dsimp [continuous] at *, intro,
  rw [hfc,hgc,chain.map_comp]
end

end continuity

end complete_partial_order

namespace roption

variables {α : Type u} {β : Type v} {γ : Type*}
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

noncomputable instance complete_partial_order : complete_partial_order (roption α) :=
{ Sup    := roption.Sup,
  le_Sup := λ c x hx, by { intros a ha, rw ← eq_some_iff at ha, subst x,
                           rw Sup_eq_some hx, apply mem_some },
  Sup_le := by { intros c x hx a ha, replace ha := mem_chain_of_mem_Sup ha,
                 apply hx _ ha _ (mem_some _) } }

section inst

lemma mem_Sup (x : α) (c : chain (roption α)) : x ∈ Sup c ↔ some x ∈ c :=
begin
  simp [complete_partial_order.Sup,roption.Sup],
  split,
  { split_ifs, swap, rintro ⟨⟨⟩⟩,
    intro h', have hh := classical.some_spec h,
    simp at h', subst x, exact hh },
  { intro h,
    have h' : ∃ (a : α), some a ∈ c := ⟨_,h⟩,
    rw dif_pos h', have hh := classical.some_spec h',
    rw eq_of_chain hh h, simp }
end

end inst

end roption

namespace pi

variables {α : Type*} {β : α → Type v}

section monotone

variables [∀a, partial_order (β a)]

lemma monotone_apply (a : α) : monotone (λf:Πa, β a, f a) :=
assume f g hfg, hfg a

lemma monotone_lambda {γ : Type*} [partial_order γ] {m : γ → Πa, β a}
  (hm : ∀a, monotone (λc, m c a)) : monotone m :=
assume f g h a, hm a h

end monotone

open complete_partial_order chain

variables  [∀a, complete_partial_order (β a)]
instance : complete_partial_order (Πa, β a) :=
{ Sup    := λc a, Sup (c.map _ (monotone_apply a)),
  Sup_le := assume c f hf a, Sup_le _ _ $ by { rintro b ⟨i,⟨ ⟩⟩, apply hf, exact ⟨i,rfl⟩ },
  le_Sup := assume c x hx a, le_Sup _ _ $ by { rw mem_map_iff, exact ⟨x,hx,rfl⟩ } }

protected lemma Sup_eq (c : chain (Π x, β x)) (a : α) : Sup c a = Sup (c.map _ (monotone_apply a) ) := rfl

section continuity

variables {γ : Type*} [complete_partial_order γ]

lemma continuous_ext (f : γ → Π a, β a) (h : ∀ x, continuous' (λ g, f g x)) :
  continuous' f :=
begin
  have : monotone f,
  { intros x y h' a, apply (h a).fst h' },
  existsi this, intro c, ext,
  rw [pi.Sup_eq,map_comp,← (h x).snd c],
end

lemma continuous_congr (f : Π a, γ → β a) (x : α) (h : continuous' (λ g x, f x g)) :
  continuous' (f x) :=
begin
  simp [continuous',continuous] at ⊢ h,
  cases h with h₀ h₁,
  have : monotone (f x),
  { intros a b h, apply h₀ h },
  existsi this, intro C, apply congr_fun (h₁ C) x,
end

end continuity

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

namespace complete_partial_order
open complete_partial_order

variables {α : Type u} {β : Type v} {γ : Type*}
variables [complete_partial_order α] [complete_partial_order β] [complete_partial_order γ]

lemma cont_const [complete_partial_order β] (f : β) (c : chain α) :
  Sup (c.map (λ _, f) (const_mono _)) = f :=
begin
  apply le_antisymm,
  { apply Sup_le, simp [chain.mem_map_iff],
    intros, subst f },
  { apply le_Sup, simp [chain.mem_map_iff], exact ⟨ c.elems 0,0,rfl ⟩ }
end

lemma cont_ite [complete_partial_order β] {p : Prop} {hp : decidable p} (c : chain α) (f g : α → β) (hf hg) :
  Sup (c.map (λ x, @ite p hp _ (f x) (g x)) (ite_mono hf hg)) = @ite p hp _ (Sup $ c.map f hf) (Sup $ c.map g hg) :=
by split_ifs; refl

lemma cont_bind {β γ} (c : chain α) (f : α → roption β) (g : α → β → roption γ) (h' h'') :
  Sup (c.map (λ x, f x >>= g x : α → roption γ) (bind_mono _ g h' h'')) = Sup (c.map (λ x, f x) h') >>= Sup (c.map (λ x, g x) h'') :=
begin
  apply eq_of_forall_ge_iff, intro x,
  simp [Sup_le_iff,roption.bind_le,-roption.bind_eq_bind,chain.mem_map_iff],
  split; intro h''',
  { intros b hb, apply Sup_le _ _ _,
    simp [-roption.bind_eq_bind,chain.mem_map_iff],
    intros y z hz hy, subst y,
    { intros y hy, simp [roption.mem_Sup] at hb,
      replace h₀ := chain.exists_of_mem_map _ _ hb,
      rcases h₀ with ⟨k,h₂,h₃⟩,
      rw roption.eq_some_iff at h₃,
      cases chain.le_total_of_mem_of_mem _ hz h₂ with hh hh,
      { replace h''' := h''' _ k h₂ rfl,
        apply h''', simp, refine ⟨_,h₃,_⟩,
        apply h'' hh _ _ hy },
      { replace h''' := h''' _ z hz rfl,
        apply h''', simp, refine ⟨_,_,hy⟩,
        apply h' hh _ h₃ } } },
  { intros y a ha hy, subst hy, intros b hb, simp at hb,
    rcases hb with ⟨b',hb₀,hb₁⟩,
    apply h''' b' _ b _, revert hb₀,
    apply le_Sup _ (f a) _, apply chain.mem_map _ _ _ ha,
    apply le_Sup _ (g a b') _, exact hb₁,
    apply chain.mem_map _ _ _ ha, introv _ h, apply h'' h, },
end

lemma cont_const' (f : β) :
  continuous' (λ x : α, f) :=
by { split, intro c; rw cont_const }

lemma cont_id' :
  continuous' (λ x : α, x) :=
by { split, intro c, erw chain.map_id }

lemma cont_ite' {p : Prop} {hp : decidable p} (f g : α → β)
  (hf : continuous' f) (hg : continuous' g) :
  continuous' (λ x, @ite p hp _ (f x) (g x)) :=
by { split, intro c, rw [cont_ite,← hg.snd,← hf.snd] }

lemma cont_bind' {β γ} (f : α → roption β) (g : α → β → roption γ)
  (hf : continuous' f)
  (hg : continuous' g) :
  continuous' (λ x, f x >>= g x) :=
by { split, intro c, rw [cont_bind,← hg.snd,← hf.snd] }

lemma cont_map' {β γ : Type*} (f : β → γ) (g : α → roption β)
  (hg : continuous' g) :
  continuous' (λ x, f <$> g x) :=
begin
  simp [-roption.bind_eq_bind,-roption.map_eq_map,← bind_pure_comp_eq_map],
  apply cont_bind' _ _ hg, apply cont_const'
end

lemma cont_seq' {β γ : Type*} (f : α → roption (β → γ)) (g : α → roption β)
  (hf : continuous' f)
  (hg : continuous' g) :
  continuous' (λ x, f x <*> g x) :=
begin
  simp [-roption.bind_eq_bind,seq_eq_bind_map], apply cont_bind' _ _ hf,
  apply pi.continuous_ext, intro x, apply cont_map' _ _ hg,
end

end complete_partial_order
