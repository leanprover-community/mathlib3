/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/
import data.pfun
import order.category.Preorder
import tactic.wlog
import tactic.find_unused

/-!
# Omega Complete Partial Orders

## Main definitions

 * class `omega_complete_partial_order`
 * `ite`, `map`, `bind`, `seq` as continuous morphisms

## Instances of `omega_complete_partial_order`

 * `roption`
 * every `complete_lattice`
 * pi-types
 * product types
 * `monotone_hom`

## References

 * [G. Markowsky, *Chain-complete posets and directed sets with applications*, https://doi.org/10.1007/BF02485815][markowsky]
-/

universes u v

local attribute [-simp] roption.bind_eq_bind roption.map_eq_map
open_locale classical

namespace preorder_hom

variables (α : Type*) (β : Type*) {γ : Type*} {φ : Type*}
variables [preorder α] [preorder β] [preorder γ] [preorder φ]

instance : preorder (α →ₘ β) :=
preorder.lift preorder_hom.to_fun

variables {β γ}

/-- the constant function as a monotone function -/
@[simps]
def const (f : β) : α →ₘ β :=
{ to_fun := function.const _ f,
  monotone := assume x y h, le_refl _}

variables {α} {α' : Type*} {β' : Type*} [preorder α'] [preorder β']

/-- the diagonal function as a monotone function -/
@[simps]
def prod.diag : α →ₘ (α × α) :=
{ to_fun := λ x, (x,x),
  monotone := λ x y h, ⟨h,h⟩ }

/-- the `prod.map` function as a monotone function -/
@[simps]
def prod.map (f : α →ₘ β) (f' : α' →ₘ β') : (α × α') →ₘ (β × β') :=
{ to_fun := prod.map f f',
  monotone := λ ⟨x,x'⟩ ⟨y,y'⟩ ⟨h,h'⟩, ⟨f.monotone h,f'.monotone h'⟩ }

/-- the `prod.fst` projection as a monotone function -/
@[simps]
def prod.fst : (α × β) →ₘ α :=
{ to_fun := prod.fst,
  monotone := λ ⟨x,x'⟩ ⟨y,y'⟩ ⟨h,h'⟩, h }

/-- the `prod.snd` projection as a monotone function -/
@[simps]
def prod.snd : (α × β) →ₘ β :=
{ to_fun := prod.snd,
  monotone := λ ⟨x,x'⟩ ⟨y,y'⟩ ⟨h,h'⟩, h' }

/-- the `prod` constructor as a monotone function -/
@[simps {rhs_md := semireducible}]
def prod.zip (f : α →ₘ β) (g : α →ₘ γ) : α →ₘ (β × γ) :=
(prod.map f g).comp prod.diag

/-- the `if _ then _ else _` function as a monotone function -/
@[simps]
def ite (p : Prop) [h : decidable p] (f g : α →ₘ β) :
  α →ₘ β :=
{ to_fun := λ x, @ite _ h _ (f x) (g x),
  monotone := by intros x y h; dsimp; split_ifs; [apply f.monotone h, apply g.monotone h] }

/-- `roption.bind` as a monotone function -/
@[simps]
def bind {β γ} (f : α →ₘ roption β) (g : α →ₘ (β → roption γ)) : α →ₘ roption γ :=
{ to_fun := λ x, f x >>= g x,
  monotone :=
  begin
    intros x y h a,
    simp only [and_imp, exists_prop, roption.bind_eq_bind, roption.mem_bind_iff, exists_imp_distrib],
    intros b hb ha,
    refine ⟨b, f.monotone h _ hb, g.monotone h _ _ ha⟩,
  end }

end preorder_hom

namespace omega_complete_partial_order

/-- Chains are monotonically increasing sequences -/
def chain (α : Type u) [preorder α] :=
ℕ →ₘ α

namespace chain

variables {α : Type u} {β : Type v} {γ : Type*}
variables [preorder α] [preorder β] [preorder γ]

instance : has_coe_to_fun (chain α) :=
@infer_instance (has_coe_to_fun $ ℕ →ₘ α) _

@[main_declaration]
instance [inhabited α] : inhabited (chain α) :=
⟨ ⟨ λ _, default _, λ _ _ _, le_refl _ ⟩ ⟩

instance : has_mem α (chain α) :=
⟨λa (c : ℕ →ₘ α), ∃ i, a = c i⟩

variables (c c' : chain α)
variables (f : α →ₘ β)
variables (g : β →ₘ γ)

instance : has_le (chain α) :=
{ le := λ x y, ∀ i, ∃ j, x i ≤ y j  }

/-- `map` function for `chain` -/
@[simps {rhs_md := semireducible}] def map : chain β :=
f.comp c

variables {f}

lemma mem_map (x : α) : x ∈ c → f x ∈ chain.map c f :=
λ ⟨i,h⟩, ⟨i, h.symm ▸ rfl⟩

lemma exists_of_mem_map {b : β} : b ∈ c.map f → ∃ a, a ∈ c ∧ f a = b :=
λ ⟨i,h⟩, ⟨c i, ⟨i, rfl⟩, h.symm⟩

lemma mem_map_iff {b : β} : b ∈ c.map f ↔ ∃ a, a ∈ c ∧ f a = b :=
⟨ exists_of_mem_map _, λ h, by { rcases h with ⟨w,h,h'⟩, subst b, apply mem_map c _ h, } ⟩

@[simp]
lemma map_id : c.map preorder_hom.id = c :=
preorder_hom.comp_id _

lemma map_comp : (c.map f).map g = c.map (g.comp f) := rfl

lemma map_le_map {g : α →ₘ β} (h : f ≤ g) : c.map f ≤ c.map g :=
λ i, by simp [mem_map_iff]; intros; existsi i; apply h

/-- `chain.zip` pairs up the elements of two chains that have the same index -/
@[simps {rhs_md := semireducible}]
def zip (c₀ : chain α) (c₁ : chain β) : chain (α × β) :=
preorder_hom.prod.zip c₀ c₁

end chain

end omega_complete_partial_order

open omega_complete_partial_order

section prio
set_option default_priority 50 -- see Note [default priority]

/-- Complete partial order (ωCPO) are useful for the formalization
of the semantics of programming languages. Its notion of limit
helps define the meaning of recursive procedures -/
class omega_complete_partial_order (α : Type*) extends partial_order α :=
(ωSup     : chain α → α)
(le_ωSup  : ∀(c:chain α), ∀ i, c i ≤ ωSup c)
(ωSup_le  : ∀(c:chain α) x, (∀ i, c i ≤ x) → ωSup c ≤ x)

end prio

namespace omega_complete_partial_order
variables {α : Type u} {β : Type v} {γ : Type*}
variables [omega_complete_partial_order α]

/-- Transfer a `omega_complete_partial_order` on `β` to a `omega_complete_partial_order` on `α` using
a strictly monotone function `f : β →ₘ α`, a definition of ωSup and a proof that `f` is continuous
with regard to the provided `ωSup` and the ωCPO on `α`. -/
@[reducible]
protected def lift [partial_order β] (f : β →ₘ α)
  (ωSup₀ : chain β → β)
  (h : ∀ x y, f x ≤ f y → x ≤ y)
  (h' : ∀ c, f (ωSup₀ c) = ωSup (c.map f)) : omega_complete_partial_order β :=
{ ωSup := ωSup₀,
  ωSup_le := λ c x hx, h _ _ (by rw h'; apply ωSup_le; intro; apply f.monotone (hx i)),
  le_ωSup := λ c i, h _ _ (by rw h'; apply le_ωSup (c.map f)) }

-- @[main_declaration]
-- lemma le_ωSup_of_mem (c : chain α) : ∀ y ∈ c, y ≤ ωSup c :=
-- by rintro y ⟨i,hy⟩; rw hy; apply le_ωSup

lemma le_ωSup_of_le {c : chain α} {x : α} (i : ℕ) (h : x ≤ c i) : x ≤ ωSup c :=
le_trans h (le_ωSup c _)

@[main_declaration]
lemma ωSup_total {c : chain α} {x : α} (h : ∀ i, c i ≤ x ∨ x ≤ c i) : ωSup c ≤ x ∨ x ≤ ωSup c :=
classical.by_cases
  (assume : ∀ i, c i ≤ x, or.inl (ωSup_le _ _ this))
  (assume : ¬ ∀ i, c i ≤ x,
    have ∃ i, ¬ c i ≤ x,
      by simp only [not_forall] at this ⊢; assumption,
    let ⟨i, hx⟩ := this in
    have x ≤ c i, from (h i).resolve_left hx,
    or.inr $ le_ωSup_of_le _ this)

@[main_declaration]
lemma ωSup_le_ωSup_of_le {c₀ c₁ : chain α} (h : c₀ ≤ c₁) : ωSup c₀ ≤ ωSup c₁ :=
ωSup_le _ _ $
λ i, Exists.rec_on (h i) $
λ j h, le_trans h (le_ωSup _ _)

@[main_declaration]
lemma ωSup_le_iff (c : chain α) (x : α) : ωSup c ≤ x ↔ (∀ i, c i ≤ x) :=
begin
  split; intros,
  { transitivity ωSup c,
    apply le_ωSup _ _, exact a },
  apply ωSup_le _ _ a,
end

section continuity
open chain

variables [omega_complete_partial_order β]
variables [omega_complete_partial_order γ]

/-- a monotone function `f : α →ₘ β` is continuous if it distributes over ωSup -/
def continuous (f : α →ₘ β) : Prop :=
∀ c : chain α, f (ωSup c) = ωSup (c.map f)

/-- `continuous' f` asserts that `f` is both monotone and continuous -/
def continuous' (f : α → β) : Prop :=
∃ hf : monotone f, continuous ⟨f,hf⟩

lemma continuous.to_monotone {f : α → β} (hf : continuous' f) : monotone f :=
by rcases hf with ⟨h,h'⟩; exact h

lemma continuous.of_bundled (f : α → β) (hf : monotone f) (hf' : continuous ⟨f,hf⟩) : continuous' f :=
⟨hf, hf'⟩

lemma continuous.of_bundled' (f : α →ₘ β) (hf' : continuous f) : continuous' f :=
⟨f.monotone, hf'⟩

lemma continuous.to_bundled (f : α → β) (hf : continuous' f) : continuous ⟨f, continuous.to_monotone hf⟩ :=
by rcases hf with ⟨h,h'⟩; exact h'

variables (f : α →ₘ β) (g : β →ₘ γ)

@[main_declaration]
lemma continuous_id : continuous (@preorder_hom.id α _) :=
by intro; rw c.map_id; refl

lemma continuous_comp (hfc : continuous f) (hgc : continuous g) : continuous (g.comp f):=
begin
  dsimp [continuous] at *, intro,
  rw [hfc,hgc,chain.map_comp]
end

lemma id_continuous' : continuous' (@id α) :=
continuous.of_bundled _ (λ a b h, h)
begin
  intro c, apply eq_of_forall_ge_iff, intro z,
  simp [ωSup_le_iff,function.const],
end

lemma const_continuous' (x: β) : continuous' (function.const α x) :=
continuous.of_bundled _ (λ a b h, le_refl _)
begin
  intro c, apply eq_of_forall_ge_iff, intro z,
  simp [ωSup_le_iff,function.const],
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
  have := c.monotone h _ ha, apply mem_unique this hb
end

/-- the `ωSup` definition for the instance `omega_complete_partial_order (roption α)` -/
protected noncomputable def ωSup (c : chain (roption α)) : roption α :=
if h : ∃a, some a ∈ c then some (classical.some h) else none

@[main_declaration]
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

@[main_declaration]
noncomputable instance omega_complete_partial_order : omega_complete_partial_order (roption α) :=
{ ωSup    := roption.ωSup,
  le_ωSup := λ c i, by { intros x hx, rw ← eq_some_iff at hx ⊢,
                         rw [ωSup_eq_some, ← hx], rw ← hx, exact ⟨i,rfl⟩ },
  ωSup_le := by { rintros c x hx a ha, replace ha := mem_chain_of_mem_ωSup ha,
                  cases ha with i ha, apply hx i, rw ← ha, apply mem_some } }

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

variables {α : Type*} {β : α → Type*} {γ : Type*}

/-- function application as a monotone function from function spaces to result,
for a fixed arguments -/
@[simps]
def monotone_apply [∀a, partial_order (β a)] (a : α) : (Πa, β a) →ₘ β a  :=
{ to_fun := (λf:Πa, β a, f a),
  monotone := assume f g hfg, hfg a }

open omega_complete_partial_order omega_complete_partial_order.chain

set_option trace.simps.verbose true

instance [∀a, omega_complete_partial_order (β a)] : omega_complete_partial_order (Πa, β a) :=
{ ωSup    := λc a, ωSup (c.map (monotone_apply a)),
  ωSup_le := assume c f hf a, ωSup_le _ _ $ by { rintro i, apply hf },
  le_ωSup := assume c i x, le_ωSup_of_le _ $ le_refl _ }

namespace omega_complete_partial_order

variables [∀ x, omega_complete_partial_order $ β x]
variables [omega_complete_partial_order γ]

lemma flip₁_continuous'
  (f : ∀ x : α, γ → β x) (a : α) (hf : continuous' (λ x y, f y x)) :
  continuous' (f a) :=
continuous.of_bundled _
  (λ x y h, continuous.to_monotone hf h a)
  (λ c, congr_fun (continuous.to_bundled _ hf c) a)

lemma flip₂_continuous'
  (f : γ → Π x, β x) (hf : ∀ x, continuous' (λ g, f g x)) : continuous' f :=
continuous.of_bundled _
  (λ x y h a, continuous.to_monotone (hf a) h)
  (by intro c; ext a; apply continuous.to_bundled _ (hf a) c)

end omega_complete_partial_order

end pi

namespace prod

open omega_complete_partial_order
variables {α : Type*} {β : Type*} {γ : Type*}
variables [omega_complete_partial_order α]
variables [omega_complete_partial_order β]
variables [omega_complete_partial_order γ]

/-- `ωSup` operator for product types -/
@[simps]
protected def ωSup (c : chain (α × β)) : α × β :=
(ωSup (c.map preorder_hom.prod.fst), ωSup (c.map preorder_hom.prod.snd))

@[main_declaration, simps ωSup_fst ωSup_snd {rhs_md := semireducible}]
instance : omega_complete_partial_order (α × β) :=
{ ωSup := prod.ωSup,
  ωSup_le := λ c ⟨x,x'⟩ h, ⟨ωSup_le _ _ $ λ i, (h i).1, ωSup_le _ _ $ λ i, (h i).2⟩,
  le_ωSup := λ c i, by split; [refine le_ωSup (c.map preorder_hom.prod.fst) i, refine le_ωSup (c.map preorder_hom.prod.snd) i] }

end prod

namespace complete_lattice
variables (α : Type u) [complete_lattice α]

set_option default_priority 100 -- see Note [default priority]

@[main_declaration]
instance : omega_complete_partial_order α :=
{ ωSup    := λc, ⨆ i, c i,
  ωSup_le := assume ⟨c, _⟩ s hs, by simp at ⊢ hs; intros i; apply hs i,
  le_ωSup := assume ⟨c, _⟩ i, by simp at ⊢; apply le_supr_of_le i; refl }

end complete_lattice

namespace omega_complete_partial_order

variables {α : Type u} {α' : Type*} {β : Type v} {β' : Type*} {γ : Type*}

variables [omega_complete_partial_order α] [omega_complete_partial_order β] [omega_complete_partial_order γ]
variables [omega_complete_partial_order α'] [omega_complete_partial_order β']

namespace preorder_hom

instance : partial_order (α →ₘ β) :=
partial_order.lift preorder_hom.to_fun $ by rintro ⟨⟩ ⟨⟩ h; congr; exact h

/-- function application as a monotone function from monotone functions to result,
for a fixed arguments -/
@[simps]
def monotone_apply (a : α) : (α →ₘ β) →ₘ β  :=
{ to_fun := (λf : α →ₘ β, f a),
  monotone := assume f g hfg, hfg a }

/-- `preorder_hom.to_fun` as a monotone function from `α →ₘ β` to `α → β` -/
def to_fun_hom : (α →ₘ β) →ₘ (α → β) :=
{ to_fun := λ f, f.to_fun,
  monotone := λ x y h, h }

/-- `ωSup` operator for monotone functions -/
@[simps]
protected def ωSup (c : chain (α →ₘ β)) : α →ₘ β :=
{ to_fun := λ a, ωSup (c.map (monotone_apply a)),
  monotone := λ x y h, ωSup_le_ωSup_of_le (chain.map_le_map _ $ λ a, a.monotone h) }

@[main_declaration, simps ωSup_to_fun {rhs_md := semireducible, simp_rhs := tt}]
instance : omega_complete_partial_order (α →ₘ β) :=
omega_complete_partial_order.lift preorder_hom.to_fun_hom preorder_hom.ωSup
  (λ x y h, h) (λ c, rfl)

end preorder_hom

namespace continuous_hom

lemma ωSup_ite {p : Prop} [hp : decidable p] (c : chain α) (f g : α →ₘ β) :
  ωSup (c.map (preorder_hom.ite p f g)) = ite p (ωSup $ c.map f) (ωSup $ c.map g) :=
by dsimp [preorder_hom.ite]; split_ifs; refl

lemma ite_continuous' {p : Prop} [hp : decidable p] (f g : α → β) :
  continuous' f → continuous' g → continuous' (λ x, ite p (f x) (g x))
| ⟨hf,hf'⟩ ⟨hg,hg'⟩ :=
continuous.of_bundled' (preorder_hom.ite p ⟨f,hf⟩ ⟨g,hg⟩)
  (λ c, by rw [ωSup_ite,← hf', ← hg']; refl)

lemma ωSup_bind {β γ : Type v} (c : chain α) (f : α →ₘ roption β) (g : α →ₘ (β → roption γ)) :
  ωSup (c.map (f.bind g)) = ωSup (c.map f) >>= ωSup (c.map g) :=
begin
  apply eq_of_forall_ge_iff, intro x,
  simp only [ωSup_le_iff, roption.bind_le, chain.mem_map_iff, and_imp, preorder_hom.bind_to_fun, exists_imp_distrib],
  split; intro h''',
  { intros b hb, apply ωSup_le _ _ _,
    rintros i y hy, simp only [roption.mem_ωSup] at hb,
    rcases hb with ⟨j,hb⟩, replace hb := hb.symm,
    simp only [roption.eq_some_iff, chain.map_to_fun, function.comp_app, pi.monotone_apply_to_fun] at hy hb,
    replace hb : b ∈ f (c (max i j))   := f.monotone (c.monotone (le_max_right i j)) _ hb,
    replace hy : y ∈ g (c (max i j)) b := g.monotone (c.monotone (le_max_left i j)) _ _ hy,
    apply h''' (max i j),
    simp only [exists_prop, roption.bind_eq_bind, roption.mem_bind_iff, chain.map_to_fun, function.comp_app,
               preorder_hom.bind_to_fun],
    exact ⟨_,hb,hy⟩, },
  { intros i, intros y hy,
    simp only [exists_prop, roption.bind_eq_bind, roption.mem_bind_iff, chain.map_to_fun, function.comp_app,
               preorder_hom.bind_to_fun] at hy,
    rcases hy with ⟨b,hb₀,hb₁⟩,
    apply h''' b _,
    { apply le_ωSup (c.map g) _ _ _ hb₁ },
    { apply le_ωSup (c.map f) i _ hb₀ } },
end

lemma bind_continuous' {β γ : Type v} (f : α → roption β) (g : α → β → roption γ) :
  continuous' f → continuous' g →
  continuous' (λ x, f x >>= g x)
| ⟨hf,hf'⟩ ⟨hg,hg'⟩ :=
continuous.of_bundled' (preorder_hom.bind ⟨f,hf⟩ ⟨g,hg⟩)
  (by intro c; rw [ωSup_bind, ← hf', ← hg']; refl)

lemma map_continuous' {β γ : Type v} (f : β → γ) (g : α → roption β)
  (hg : continuous' g) :
  continuous' (λ x, f <$> g x) :=
by simp only [map_eq_bind_pure_comp];
   apply bind_continuous' _ _ hg;
   apply const_continuous'

lemma seq_continuous' {β γ : Type v} (f : α → roption (β → γ)) (g : α → roption β)
  (hf : continuous' f) (hg : continuous' g) :
  continuous' (λ x, f x <*> g x) :=
by simp only [seq_eq_bind_map];
   apply bind_continuous' _ _ hf;
   apply pi.omega_complete_partial_order.flip₂_continuous'; intro;
   apply map_continuous' _ _ hg

end continuous_hom

end omega_complete_partial_order
