/- complete partial orders
Helpful for a small-scale domain theory, see
  http://home.in.tum.de/~hoelzl/documents/lochbihler2014recursive.pdf
-/

import data.pfun
import data.stream.basic
import tactic.wlog
import tactic.find_unused

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

namespace stream

variables {α : Type u} {β : Type v} {γ : Type*}
variables [preorder α] [preorder β] [preorder γ]

variables {f : α → β} (hf : monotone f)
          {s : stream α} (hs : monotone s)

lemma monotone_map : monotone (s.map f) :=
λ i j h, hf (hs h)

end stream

/-- Chains are monotonically increasing sequences -/
structure chain (α : Type u) [preorder α] :=
(elems : stream α)
(mono : monotone elems)

namespace chain

variables {α : Type u} {β : Type v} {γ : Type*}
variables [preorder α] [preorder β] [preorder γ]

@[main_declaration]
instance [inhabited α] : inhabited (chain α) :=
⟨ ⟨ λ _, default _, λ _ _ _, le_refl _ ⟩ ⟩

instance : has_mem α (chain α) :=
⟨λa c, a ∈ c.elems⟩

@[simp] lemma mem_mk (x : α) (s : stream α) (h) : x ∈ chain.mk s h ↔ x ∈ s := iff.refl _

variables (c c' : chain α)
variables (f : α → β) (hf : monotone f)
variables {g : β → γ} (hg : monotone g)

instance : has_le (chain α) :=
{ le := λ x y, ∀ a, a ∈ x → ∃ b ∈ y, a ≤ b  }

/-- `map` function for `chain` -/
def map : chain β :=
⟨c.elems.map f, stream.monotone_map hf c.mono ⟩

variables {f}

lemma mem_map (x : α) : x ∈ c → f x ∈ chain.map c f hf :=
stream.mem_map _

lemma exists_of_mem_map {b : β} : b ∈ c.map f hf → ∃ a, a ∈ c ∧ f a = b :=
stream.exists_of_mem_map

lemma mem_map_iff {b : β} : b ∈ c.map f hf ↔ ∃ a, a ∈ c ∧ f a = b :=
⟨ exists_of_mem_map _ _, λ h, by { rcases h with ⟨w,h,h'⟩, subst b, apply mem_map c hf _ h, } ⟩

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

/-- Complete partial order (ωCPO) are useful for the formalization
of the semantics of programming languages. Its notion of limit
helps define the meaning of recursive procedures -/
class omega_complete_partial_order (α : Type*) extends partial_order α :=
(ωSup     : chain α → α)
(le_ωSup  : ∀(c:chain α), ∀x∈c, x ≤ ωSup c)
(ωSup_le  : ∀(c:chain α) x, (∀y∈c, y ≤ x) → ωSup c ≤ x)

end prio

namespace omega_complete_partial_order
variables {α : Type u} {β : Type v} {γ : Type*}
variables [omega_complete_partial_order α]

@[main_declaration]
lemma le_ωSup_of_le {c : chain α} {x y : α} (h : x ≤ y) (hy : y ∈ c) : x ≤ ωSup c :=
le_trans h (le_ωSup c y hy)

@[main_declaration]
lemma ωSup_total {c : chain α} {x : α} (h : ∀y∈c, y ≤ x ∨ x ≤ y) : ωSup c ≤ x ∨ x ≤ ωSup c :=
classical.by_cases
  (assume : ∀y ∈ c, y ≤ x, or.inl (ωSup_le _ _ this))
  (assume : ¬ ∀y ∈ c, y ≤ x,
    have ∃y∈c, ¬ y ≤ x,
      by simp only [not_forall] at this ⊢; assumption,
    let ⟨y, hy, hyx⟩ := this in
    have x ≤ y, from (h y hy).resolve_left hyx,
    or.inr $ le_ωSup_of_le this hy)

@[main_declaration]
lemma ωSup_le_ωSup_of_le {c₀ c₁ : chain α} (h : c₀ ≤ c₁) : ωSup c₀ ≤ ωSup c₁ :=
ωSup_le _ _ $
λ y hy, Exists.rec_on (h y hy) $
λ x ⟨hx,hxy⟩, le_trans hxy $ le_ωSup _ _ hx

@[main_declaration]
lemma ωSup_le_iff (c : chain α) (x : α) : ωSup c ≤ x ↔ (∀ y ∈ c, y ≤ x) :=
begin
  split; intros,
  { transitivity ωSup c,
    apply le_ωSup _ _ H, exact a },
  apply ωSup_le _ _ a,
end

section continuity
open chain

variables [omega_complete_partial_order β]
          [omega_complete_partial_order γ]
  (f : α → β) (hf : monotone f)
  (g : β → γ) (hg : monotone g)

/-- A monotone function is continuous if it preserves the supremum of chains -/
def continuous :=
∀ C : chain α, f (ωSup C) = ωSup (C.map f hf)

/-- `continuous'` asserts both monotonicity and continuity of function `f` -/
def continuous' := ∃ h, continuous f h

lemma continuous_comp (hfc : continuous f hf) (hgc : continuous g hg) :
  continuous (g ∘ f) (monotone.comp hg hf) :=
begin
  dsimp [continuous] at *, intro,
  rw [hfc,hgc,chain.map_comp]
end

end continuity

end omega_complete_partial_order

namespace roption

variables {α : Type u} {β : Type v} {γ : Type*}
open omega_complete_partial_order

lemma eq_of_chain {c : chain (roption α)} {a b : α} (ha : some a ∈ c) (hb : some b ∈ c) : a = b :=
begin
  cases ha with i ha, replace ha := ha.symm,
  cases hb with j hb, replace hb := hb.symm,
  wlog h : i ≤ j := le_total i j using [a b i j,b a j i],
  rw [eq_some_iff] at ha hb,
  have := c.mono h _ ha, apply mem_unique this hb
end

/-- the `ωSup` definition for the instance `omega_complete_partial_order (roption α)` -/
protected noncomputable def ωSup (c : chain (roption α)) : roption α :=
if h : ∃a, some a ∈ c then some (classical.some h) else none

lemma ωSup_eq_some {c : chain (roption α)} {a : α} (h : some a ∈ c) : roption.ωSup c = some a :=
have ∃a, some a ∈ c, from ⟨a, h⟩,
have a' : some (classical.some this) ∈ c, from classical.some_spec this,
calc roption.ωSup c = some (classical.some this) : dif_pos this
               ... = some a : congr_arg _ (eq_of_chain a' h)

@[main_declaration]
lemma ωSup_eq_none {c : chain (roption α)} (h : ¬∃a, some a ∈ c) : roption.ωSup c = none :=
dif_neg h

lemma mem_chain_of_mem_ωSup {c : chain (roption α)} {a : α} (h : a ∈ roption.ωSup c) : some a ∈ c :=
begin
  simp [roption.ωSup] at h, split_ifs at h,
  { have h' := classical.some_spec h_1,
    rw ← eq_some_iff at h, rw ← h, exact h' },
  { rcases h with ⟨ ⟨ ⟩ ⟩ }
end

noncomputable instance omega_complete_partial_order : omega_complete_partial_order (roption α) :=
{ ωSup    := roption.ωSup,
  le_ωSup := λ c x hx, by { intros a ha, rw ← eq_some_iff at ha, subst x,
                           rw ωSup_eq_some hx, apply mem_some },
  ωSup_le := by { intros c x hx a ha, replace ha := mem_chain_of_mem_ωSup ha,
                 apply hx _ ha _ (mem_some _) } }

section inst

lemma mem_ωSup (x : α) (c : chain (roption α)) : x ∈ ωSup c ↔ some x ∈ c :=
begin
  simp [omega_complete_partial_order.ωSup,roption.ωSup],
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

-- lemma monotone_lambda {γ : Type*} [partial_order γ] {m : γ → Πa, β a}
--   (hm : ∀a, monotone (λc, m c a)) : monotone m :=
-- assume f g h a, hm a h

end monotone

open omega_complete_partial_order chain

variables  [∀a, omega_complete_partial_order (β a)]
instance : omega_complete_partial_order (Πa, β a) :=
{ ωSup    := λc a, ωSup (c.map _ (monotone_apply a)),
  ωSup_le := assume c f hf a, ωSup_le _ _ $ by { rintro b ⟨i,⟨ ⟩⟩, apply hf, exact ⟨i,rfl⟩ },
  le_ωSup := assume c x hx a, le_ωSup _ _ $ by { rw mem_map_iff, exact ⟨x,hx,rfl⟩ } }

protected lemma ωSup_eq (c : chain (Π x, β x)) (a : α) : ωSup c a = ωSup (c.map _ (monotone_apply a) ) := rfl

section continuity

variables {γ : Type*} [omega_complete_partial_order γ]

lemma continuous_ext (f : γ → Π a, β a) (h : ∀ x, continuous' (λ g, f g x)) :
  continuous' f :=
begin
  have : monotone f,
  { intros x y h' a, apply (h a).fst h' },
  existsi this, intro c, ext,
  rw [pi.ωSup_eq,map_comp,← (h x).snd c],
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

namespace complete_lattice
variables (α : Type u) [complete_lattice α]

set_option default_priority 100 -- see Note [default priority]

@[main_declaration]
instance : omega_complete_partial_order α :=
{ ωSup    := λc, ⨆ i, c.elems i,
  ωSup_le := assume ⟨c, _⟩ s hs, by simp [stream.mem_def] at ⊢ hs; intros i; apply hs _ i rfl,
  le_ωSup := assume ⟨c, _⟩ x hx, by simp [stream.mem_def,stream.nth] at ⊢ hx;
                                         cases hx with i hs; apply le_supr_of_le i; rw hs }

end complete_lattice

namespace omega_complete_partial_order
open omega_complete_partial_order

variables {α : Type u} {β : Type v} {γ : Type*}
variables [omega_complete_partial_order α] [omega_complete_partial_order β] [omega_complete_partial_order γ]

lemma cont_const (f : β) (c : chain α) :
  ωSup (c.map (λ _, f) (const_mono _)) = f :=
begin
  apply le_antisymm,
  { apply ωSup_le, simp [chain.mem_map_iff],
    intros, subst f },
  { apply le_ωSup, simp [chain.mem_map_iff], exact ⟨ c.elems 0,0,rfl ⟩ }
end

lemma cont_ite {p : Prop} {hp : decidable p} (c : chain α) (f g : α → β) (hf hg) :
  ωSup (c.map (λ x, @ite p hp _ (f x) (g x)) (ite_mono hf hg)) = @ite p hp _ (ωSup $ c.map f hf) (ωSup $ c.map g hg) :=
by split_ifs; refl

lemma cont_bind {β γ : Type v} (c : chain α) (f : α → roption β) (g : α → β → roption γ) (h' h'') :
  ωSup (c.map (λ x, f x >>= g x : α → roption γ) (bind_mono _ g h' h'')) = ωSup (c.map (λ x, f x) h') >>= ωSup (c.map (λ x, g x) h'') :=
begin
  apply eq_of_forall_ge_iff, intro x,
  simp [ωSup_le_iff,roption.bind_le,-roption.bind_eq_bind,chain.mem_map_iff],
  split; intro h''',
  { intros b hb, apply ωSup_le _ _ _,
    simp [-roption.bind_eq_bind,chain.mem_map_iff],
    intros y z hz hy, subst y,
    { intros y hy, simp [roption.mem_ωSup] at hb,
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
    apply le_ωSup _ (f a) _, apply chain.mem_map _ _ _ ha,
    apply le_ωSup _ (g a b') _, exact hb₁,
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

lemma cont_bind' {β γ : Type v} (f : α → roption β) (g : α → β → roption γ)
  (hf : continuous' f)
  (hg : continuous' g) :
  continuous' (λ x, f x >>= g x) :=
by { split, intro c, rw [cont_bind,← hg.snd,← hf.snd] }

lemma cont_map' {β γ : Type v} (f : β → γ) (g : α → roption β)
  (hg : continuous' g) :
  continuous' (λ x, f <$> g x) :=
begin
  simp [-roption.bind_eq_bind,-roption.map_eq_map,← bind_pure_comp_eq_map],
  apply cont_bind' _ _ hg, apply cont_const'
end

lemma cont_seq' {β γ : Type v} (f : α → roption (β → γ)) (g : α → roption β)
  (hf : continuous' f)
  (hg : continuous' g) :
  continuous' (λ x, f x <*> g x) :=
begin
  simp [-roption.bind_eq_bind,seq_eq_bind_map], apply cont_bind' _ _ hf,
  apply pi.continuous_ext, intro x, apply cont_map' _ _ hg,
end

end omega_complete_partial_order
