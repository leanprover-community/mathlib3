/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import control.monad.basic
import data.part
import order.hom.lattice
import tactic.monotonicity
import tactic.wlog

/-!
# Omega Complete Partial Orders

An omega-complete partial order is a partial order with a supremum
operation on increasing sequences indexed by natural numbers (which we
call `ωSup`). In this sense, it is strictly weaker than join complete
semi-lattices as only ω-sized totally ordered sets have a supremum.

The concept of an omega-complete partial order (ωCPO) is useful for the
formalization of the semantics of programming languages. Its notion of
supremum helps define the meaning of recursive procedures.

## Main definitions

 * class `omega_complete_partial_order`
 * `ite`, `map`, `bind`, `seq` as continuous morphisms

## Instances of `omega_complete_partial_order`

 * `part`
 * every `complete_lattice`
 * pi-types
 * product types
 * `monotone_hom`
 * `continuous_hom` (with notation →𝒄)
   * an instance of `omega_complete_partial_order (α →𝒄 β)`
 * `continuous_hom.of_fun`
 * `continuous_hom.of_mono`
 * continuous functions:
   * `id`
   * `ite`
   * `const`
   * `part.bind`
   * `part.map`
   * `part.seq`

## References

 * [Chain-complete posets and directed sets with applications][markowsky1976]
 * [Recursive definitions of partial functions and their computations][cadiou1972]
 * [Semantics of Programming Languages: Structures and Techniques][gunter1992]
-/

universes u v

local attribute [-simp] part.bind_eq_bind part.map_eq_map
open_locale classical

namespace order_hom

variables (α : Type*) (β : Type*) {γ : Type*} {φ : Type*}
variables [preorder α] [preorder β] [preorder γ] [preorder φ]

variables {β γ}

variables {α} {α' : Type*} {β' : Type*} [preorder α'] [preorder β']

/-- `part.bind` as a monotone function -/
@[simps]
def bind {β γ} (f : α →o part β) (g : α →o β → part γ) : α →o part γ :=
{ to_fun := λ x, f x >>= g x,
  monotone' :=
  begin
    intros x y h a,
    simp only [and_imp, exists_prop, part.bind_eq_bind, part.mem_bind_iff,
               exists_imp_distrib],
    intros b hb ha,
    refine ⟨b, f.monotone h _ hb, g.monotone h _ _ ha⟩,
  end }

end order_hom

namespace omega_complete_partial_order

/-- A chain is a monotone sequence.

See the definition on page 114 of [gunter1992]. -/
def chain (α : Type u) [preorder α] :=
ℕ →o α

namespace chain

variables {α : Type u} {β : Type v} {γ : Type*}
variables [preorder α] [preorder β] [preorder γ]

instance : has_coe_to_fun (chain α) (λ _, ℕ → α) := order_hom.has_coe_to_fun

instance [inhabited α] : inhabited (chain α) :=
⟨ ⟨ λ _, default _, λ _ _ _, le_refl _ ⟩ ⟩

instance : has_mem α (chain α) :=
⟨λa (c : ℕ →o α), ∃ i, a = c i⟩

variables (c c' : chain α)
variables (f : α →o β)
variables (g : β →o γ)

instance : has_le (chain α) :=
{ le := λ x y, ∀ i, ∃ j, x i ≤ y j }

/-- `map` function for `chain` -/
@[simps {fully_applied := ff}] def map : chain β :=
f.comp c

variables {f}

lemma mem_map (x : α) : x ∈ c → f x ∈ chain.map c f :=
λ ⟨i,h⟩, ⟨i, h.symm ▸ rfl⟩

lemma exists_of_mem_map {b : β} : b ∈ c.map f → ∃ a, a ∈ c ∧ f a = b :=
λ ⟨i,h⟩, ⟨c i, ⟨i, rfl⟩, h.symm⟩

lemma mem_map_iff {b : β} : b ∈ c.map f ↔ ∃ a, a ∈ c ∧ f a = b :=
⟨ exists_of_mem_map _, λ h, by { rcases h with ⟨w,h,h'⟩, subst b, apply mem_map c _ h, } ⟩

@[simp]
lemma map_id : c.map order_hom.id = c :=
order_hom.comp_id _

lemma map_comp : (c.map f).map g = c.map (g.comp f) := rfl

@[mono]
lemma map_le_map {g : α →o β} (h : f ≤ g) : c.map f ≤ c.map g :=
λ i, by simp [mem_map_iff]; intros; existsi i; apply h

/-- `chain.zip` pairs up the elements of two chains that have the same index -/
@[simps]
def zip (c₀ : chain α) (c₁ : chain β) : chain (α × β) :=
order_hom.prod c₀ c₁

end chain

end omega_complete_partial_order

open omega_complete_partial_order

section prio
set_option extends_priority 50

/-- An omega-complete partial order is a partial order with a supremum
operation on increasing sequences indexed by natural numbers (which we
call `ωSup`). In this sense, it is strictly weaker than join complete
semi-lattices as only ω-sized totally ordered sets have a supremum.

See the definition on page 114 of [gunter1992]. -/
class omega_complete_partial_order (α : Type*) extends partial_order α :=
(ωSup     : chain α → α)
(le_ωSup  : ∀(c:chain α), ∀ i, c i ≤ ωSup c)
(ωSup_le  : ∀(c:chain α) x, (∀ i, c i ≤ x) → ωSup c ≤ x)

end prio

namespace omega_complete_partial_order
variables {α : Type u} {β : Type v} {γ : Type*}
variables [omega_complete_partial_order α]

/-- Transfer a `omega_complete_partial_order` on `β` to a `omega_complete_partial_order` on `α`
using a strictly monotone function `f : β →o α`, a definition of ωSup and a proof that `f` is
continuous with regard to the provided `ωSup` and the ωCPO on `α`. -/
@[reducible]
protected def lift [partial_order β] (f : β →o α)
  (ωSup₀ : chain β → β)
  (h : ∀ x y, f x ≤ f y → x ≤ y)
  (h' : ∀ c, f (ωSup₀ c) = ωSup (c.map f)) : omega_complete_partial_order β :=
{ ωSup := ωSup₀,
  ωSup_le := λ c x hx, h _ _ (by rw h'; apply ωSup_le; intro; apply f.monotone (hx i)),
  le_ωSup := λ c i, h _ _ (by rw h'; apply le_ωSup (c.map f)) }

lemma le_ωSup_of_le {c : chain α} {x : α} (i : ℕ) (h : x ≤ c i) : x ≤ ωSup c :=
le_trans h (le_ωSup c _)

lemma ωSup_total {c : chain α} {x : α} (h : ∀ i, c i ≤ x ∨ x ≤ c i) : ωSup c ≤ x ∨ x ≤ ωSup c :=
classical.by_cases
  (assume : ∀ i, c i ≤ x, or.inl (ωSup_le _ _ this))
  (assume : ¬ ∀ i, c i ≤ x,
    have ∃ i, ¬ c i ≤ x,
      by simp only [not_forall] at this ⊢; assumption,
    let ⟨i, hx⟩ := this in
    have x ≤ c i, from (h i).resolve_left hx,
    or.inr $ le_ωSup_of_le _ this)

@[mono]
lemma ωSup_le_ωSup_of_le {c₀ c₁ : chain α} (h : c₀ ≤ c₁) : ωSup c₀ ≤ ωSup c₁ :=
ωSup_le _ _ $
λ i, Exists.rec_on (h i) $
λ j h, le_trans h (le_ωSup _ _)

lemma ωSup_le_iff (c : chain α) (x : α) : ωSup c ≤ x ↔ (∀ i, c i ≤ x) :=
begin
  split; intros,
  { transitivity ωSup c,
    exact le_ωSup _ _, assumption },
  exact ωSup_le _ _ ‹_›,
end

/-- A subset `p : α → Prop` of the type closed under `ωSup` induces an
`omega_complete_partial_order` on the subtype `{a : α // p a}`. -/
def subtype {α : Type*} [omega_complete_partial_order α] (p : α → Prop)
  (hp : ∀ (c : chain α), (∀ i ∈ c, p i) → p (ωSup c)) :
  omega_complete_partial_order (subtype p) :=
omega_complete_partial_order.lift
  (order_hom.subtype.val p)
  (λ c, ⟨ωSup _, hp (c.map (order_hom.subtype.val p)) (λ i ⟨n, q⟩, q.symm ▸ (c n).2)⟩)
  (λ x y h, h)
  (λ c, rfl)

section continuity
open chain

variables [omega_complete_partial_order β]
variables [omega_complete_partial_order γ]

/-- A monotone function `f : α →o β` is continuous if it distributes over ωSup.

In order to distinguish it from the (more commonly used) continuity from topology
(see topology/basic.lean), the present definition is often referred to as
"Scott-continuity" (referring to Dana Scott). It corresponds to continuity
in Scott topological spaces (not defined here). -/
def continuous (f : α →o β) : Prop :=
∀ c : chain α, f (ωSup c) = ωSup (c.map f)

/-- `continuous' f` asserts that `f` is both monotone and continuous. -/
def continuous' (f : α → β) : Prop :=
∃ hf : monotone f, continuous ⟨f, hf⟩

lemma continuous'.to_monotone {f : α → β} (hf : continuous' f) : monotone f := hf.fst

lemma continuous.of_bundled (f : α → β) (hf : monotone f)
  (hf' : continuous ⟨f, hf⟩) : continuous' f := ⟨hf, hf'⟩

lemma continuous.of_bundled' (f : α →o β) (hf' : continuous f) : continuous' f :=
⟨f.mono, hf'⟩

lemma continuous'.to_bundled (f : α → β) (hf : continuous' f) :
  continuous ⟨f, hf.to_monotone⟩ := hf.snd

@[simp, norm_cast] lemma continuous'_coe : ∀ {f : α →o β}, continuous' f ↔ continuous f
| ⟨f, hf⟩ := ⟨λ ⟨hf', hc⟩, hc, λ hc, ⟨hf, hc⟩⟩

variables (f : α →o β) (g : β →o γ)

lemma continuous_id : continuous (@order_hom.id α _) :=
by intro; rw c.map_id; refl

lemma continuous_comp (hfc : continuous f) (hgc : continuous g) : continuous (g.comp f):=
begin
  dsimp [continuous] at *, intro,
  rw [hfc,hgc,chain.map_comp]
end

lemma id_continuous' : continuous' (@id α) :=
continuous_id.of_bundled' _

lemma continuous_const (x : β) : continuous (order_hom.const α x) :=
λ c, eq_of_forall_ge_iff $ λ z, by simp [ωSup_le_iff]

lemma const_continuous' (x: β) : continuous' (function.const α x) :=
continuous.of_bundled' (order_hom.const α x) (continuous_const x)

end continuity

end omega_complete_partial_order

namespace part

variables {α : Type u} {β : Type v} {γ : Type*}
open omega_complete_partial_order

lemma eq_of_chain {c : chain (part α)} {a b : α} (ha : some a ∈ c) (hb : some b ∈ c) : a = b :=
begin
  cases ha with i ha, replace ha := ha.symm,
  cases hb with j hb, replace hb := hb.symm,
  wlog h : i ≤ j := le_total i j using [a b i j, b a j i],
  rw [eq_some_iff] at ha hb,
  have := c.monotone h _ ha, apply mem_unique this hb
end

/-- The (noncomputable) `ωSup` definition for the `ω`-CPO structure on `part α`. -/
protected noncomputable def ωSup (c : chain (part α)) : part α :=
if h : ∃a, some a ∈ c then some (classical.some h) else none

lemma ωSup_eq_some {c : chain (part α)} {a : α} (h : some a ∈ c) : part.ωSup c = some a :=
have ∃a, some a ∈ c, from ⟨a, h⟩,
have a' : some (classical.some this) ∈ c, from classical.some_spec this,
calc part.ωSup c = some (classical.some this) : dif_pos this
                ... = some a : congr_arg _ (eq_of_chain a' h)

lemma ωSup_eq_none {c : chain (part α)} (h : ¬∃a, some a ∈ c) : part.ωSup c = none :=
dif_neg h

lemma mem_chain_of_mem_ωSup {c : chain (part α)} {a : α} (h : a ∈ part.ωSup c) : some a ∈ c :=
begin
  simp [part.ωSup] at h, split_ifs at h,
  { have h' := classical.some_spec h_1,
    rw ← eq_some_iff at h, rw ← h, exact h' },
  { rcases h with ⟨ ⟨ ⟩ ⟩ }
end

noncomputable instance omega_complete_partial_order : omega_complete_partial_order (part α) :=
{ ωSup    := part.ωSup,
  le_ωSup := λ c i, by { intros x hx, rw ← eq_some_iff at hx ⊢,
                         rw [ωSup_eq_some, ← hx], rw ← hx, exact ⟨i,rfl⟩ },
  ωSup_le := by { rintros c x hx a ha, replace ha := mem_chain_of_mem_ωSup ha,
                  cases ha with i ha, apply hx i, rw ← ha, apply mem_some } }

section inst

lemma mem_ωSup (x : α) (c : chain (part α)) : x ∈ ωSup c ↔ some x ∈ c :=
begin
  simp [omega_complete_partial_order.ωSup,part.ωSup],
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

end part

namespace pi

variables {α : Type*} {β : α → Type*} {γ : Type*}

open omega_complete_partial_order omega_complete_partial_order.chain

instance [∀a, omega_complete_partial_order (β a)] : omega_complete_partial_order (Πa, β a) :=
{ ωSup    := λc a, ωSup (c.map (pi.eval_order_hom a)),
  ωSup_le := assume c f hf a, ωSup_le _ _ $ by { rintro i, apply hf },
  le_ωSup := assume c i x, le_ωSup_of_le _ $ le_refl _ }

namespace omega_complete_partial_order

variables [∀ x, omega_complete_partial_order $ β x]
variables [omega_complete_partial_order γ]

lemma flip₁_continuous'
  (f : ∀ x : α, γ → β x) (a : α) (hf : continuous' (λ x y, f y x)) :
  continuous' (f a) :=
continuous.of_bundled _
  (λ x y h, hf.to_monotone h a)
  (λ c, congr_fun (hf.to_bundled _ c) a)

lemma flip₂_continuous'
  (f : γ → Π x, β x) (hf : ∀ x, continuous' (λ g, f g x)) : continuous' f :=
continuous.of_bundled _
  (λ x y h a, (hf a).to_monotone h)
  (by intro c; ext a; apply (hf a).to_bundled _ c)

end omega_complete_partial_order

end pi

namespace prod

open omega_complete_partial_order
variables {α : Type*} {β : Type*} {γ : Type*}
variables [omega_complete_partial_order α]
variables [omega_complete_partial_order β]
variables [omega_complete_partial_order γ]

/-- The supremum of a chain in the product `ω`-CPO. -/
@[simps]
protected def ωSup (c : chain (α × β)) : α × β :=
(ωSup (c.map order_hom.fst), ωSup (c.map order_hom.snd))

@[simps ωSup_fst ωSup_snd]
instance : omega_complete_partial_order (α × β) :=
{ ωSup := prod.ωSup,
  ωSup_le := λ c ⟨x,x'⟩ h, ⟨ωSup_le _ _ $ λ i, (h i).1, ωSup_le _ _ $ λ i, (h i).2⟩,
  le_ωSup := λ c i,
    ⟨le_ωSup (c.map order_hom.fst) i, le_ωSup (c.map order_hom.snd) i⟩ }

end prod

namespace complete_lattice
variables (α : Type u)

/-- Any complete lattice has an `ω`-CPO structure where the countable supremum is a special case
of arbitrary suprema. -/

@[priority 100] -- see Note [lower instance priority]
instance [complete_lattice α] : omega_complete_partial_order α :=
{ ωSup    := λc, ⨆ i, c i,
  ωSup_le := λ ⟨c, _⟩ s hs, by simp only [supr_le_iff, order_hom.coe_fun_mk] at ⊢ hs;
    intros i; apply hs i,
  le_ωSup := assume ⟨c, _⟩ i, by simp only [order_hom.coe_fun_mk]; apply le_supr_of_le i; refl }

variables {α} {β : Type v} [omega_complete_partial_order α] [complete_lattice β]
open omega_complete_partial_order

lemma inf_continuous [is_total β (≤)] (f g : α →o β) (hf : continuous f) (hg : continuous g) :
  continuous (f ⊓ g) :=
begin
  intro c,
  apply eq_of_forall_ge_iff, intro z,
  simp only [inf_le_iff, hf c, hg c, ωSup_le_iff, ←forall_or_distrib_left, ←forall_or_distrib_right,
             function.comp_app, chain.map_coe, order_hom.has_inf_inf_coe],
  split,
  { introv h, apply h },
  { intros h i j,
    apply or.imp _ _ (h (max i j)); apply le_trans; mono*; try { exact le_rfl },
    { apply le_max_left },
    { apply le_max_right }, },
end

lemma Sup_continuous (s : set $ α →o β) (hs : ∀ f ∈ s, continuous f) :
  continuous (Sup s) :=
begin
  intro c, apply eq_of_forall_ge_iff, intro z,
  suffices : (∀ (f ∈ s) n, (f : _) (c n) ≤ z) ↔ (∀ n (f ∈ s), (f : _) (c n) ≤ z),
    by simpa [ωSup_le_iff, hs _ _ _] { contextual := tt },
  exact ⟨λ H n f hf, H f hf n, λ H f hf n, H n f hf⟩
end

lemma supr_continuous {ι : Sort*} {f : ι → α →o β} (h : ∀ i, continuous (f i)) :
  continuous (⨆ i, f i) :=
Sup_continuous _ $ set.forall_range_iff.2 h

theorem Sup_continuous' (s : set (α → β)) (hc : ∀ f ∈ s, continuous' f) :
  continuous' (Sup s) :=
begin
  lift s to set (α →o β) using λ f hf, (hc f hf).to_monotone,
  simp only [set.ball_image_iff, continuous'_coe] at hc,
  rw [Sup_image],
  norm_cast,
  exact supr_continuous (λ f, supr_continuous (λ hf, hc f hf)),
end

lemma sup_continuous {f g : α →o β} (hf : continuous f) (hg : continuous g) :
  continuous (f ⊔ g) :=
begin
  rw ← Sup_pair, apply Sup_continuous,
  rintro f (rfl|rfl|_); assumption
end

lemma top_continuous :
  continuous (⊤ : α →o β) :=
begin
  intro c, apply eq_of_forall_ge_iff, intro z,
  simp only [ωSup_le_iff, forall_const, chain.map_coe, (∘), function.const,
             order_hom.has_top_top, order_hom.const_coe_coe],
end

lemma bot_continuous :
  continuous (⊥ : α →o β) :=
begin
  rw ← Sup_empty,
  exact Sup_continuous _ (λ f hf, hf.elim),
end

end complete_lattice

namespace omega_complete_partial_order

variables {α : Type u} {α' : Type*} {β : Type v} {β' : Type*} {γ : Type*} {φ : Type*}

variables [omega_complete_partial_order α] [omega_complete_partial_order β]
variables [omega_complete_partial_order γ] [omega_complete_partial_order φ]
variables [omega_complete_partial_order α'] [omega_complete_partial_order β']

namespace order_hom

/-- The `ωSup` operator for monotone functions. -/
@[simps]
protected def ωSup (c : chain (α →o β)) : α →o β :=
{ to_fun := λ a, ωSup (c.map (order_hom.apply a)),
  monotone' := λ x y h, ωSup_le_ωSup_of_le (chain.map_le_map _ $ λ a, a.monotone h) }

@[simps ωSup_coe]
instance omega_complete_partial_order : omega_complete_partial_order (α →o β) :=
omega_complete_partial_order.lift order_hom.coe_fn_hom order_hom.ωSup
  (λ x y h, h) (λ c, rfl)

end order_hom

section
variables (α β)

/-- A monotone function on `ω`-continuous partial orders is said to be continuous
if for every chain `c : chain α`, `f (⊔ i, c i) = ⊔ i, f (c i)`.
This is just the bundled version of `order_hom.continuous`. -/
structure continuous_hom extends order_hom α β :=
(cont : continuous (order_hom.mk to_fun monotone'))

attribute [nolint doc_blame] continuous_hom.to_order_hom

infixr ` →𝒄 `:25 := continuous_hom -- Input: \r\MIc

instance : has_coe_to_fun (α →𝒄 β) (λ _, α → β) := ⟨λ f, f.to_order_hom.to_fun⟩

instance : has_coe (α →𝒄 β) (α →o β) :=
{ coe :=  continuous_hom.to_order_hom }

instance : partial_order (α →𝒄 β) :=
partial_order.lift (λ f, f.to_order_hom.to_fun) $ by rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ h; congr; exact h

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def continuous_hom.simps.apply (h : α →𝒄 β) : α → β := h

initialize_simps_projections continuous_hom
  (to_order_hom_to_fun → apply, -to_order_hom)

end

namespace continuous_hom

theorem congr_fun {f g : α →𝒄 β} (h : f = g) (x : α) : f x = g x :=
congr_arg (λ h : α →𝒄 β, h x) h

theorem congr_arg (f : α →𝒄 β) {x y : α} (h : x = y) : f x = f y :=
congr_arg (λ x : α, f x) h

protected lemma monotone (f : α →𝒄 β) : monotone f := f.monotone'

@[mono] lemma apply_mono {f g : α →𝒄 β} {x y : α} (h₁ : f ≤ g) (h₂ : x ≤ y) : f x ≤ g y :=
order_hom.apply_mono (show (f : α →o β) ≤ g, from h₁) h₂

lemma ite_continuous' {p : Prop} [hp : decidable p] (f g : α → β)
  (hf : continuous' f) (hg : continuous' g) : continuous' (λ x, if p then f x else g x) :=
by split_ifs; simp *

lemma ωSup_bind {β γ : Type v} (c : chain α) (f : α →o part β) (g : α →o β → part γ) :
  ωSup (c.map (f.bind g)) = ωSup (c.map f) >>= ωSup (c.map g) :=
begin
  apply eq_of_forall_ge_iff, intro x,
  simp only [ωSup_le_iff, part.bind_le, chain.mem_map_iff, and_imp, order_hom.bind_coe,
    exists_imp_distrib],
  split; intro h''',
  { intros b hb, apply ωSup_le _ _ _,
    rintros i y hy, simp only [part.mem_ωSup] at hb,
    rcases hb with ⟨j,hb⟩, replace hb := hb.symm,
    simp only [part.eq_some_iff, chain.map_coe, function.comp_app, order_hom.apply_coe]
      at hy hb,
    replace hb : b ∈ f (c (max i j))   := f.mono (c.mono (le_max_right i j)) _ hb,
    replace hy : y ∈ g (c (max i j)) b := g.mono (c.mono (le_max_left i j)) _ _ hy,
    apply h''' (max i j),
    simp only [exists_prop, part.bind_eq_bind, part.mem_bind_iff, chain.map_coe,
               function.comp_app, order_hom.bind_coe],
    exact ⟨_,hb,hy⟩, },
  { intros i, intros y hy,
    simp only [exists_prop, part.bind_eq_bind, part.mem_bind_iff, chain.map_coe,
               function.comp_app, order_hom.bind_coe] at hy,
    rcases hy with ⟨b,hb₀,hb₁⟩,
    apply h''' b _,
    { apply le_ωSup (c.map g) _ _ _ hb₁ },
    { apply le_ωSup (c.map f) i _ hb₀ } },
end

lemma bind_continuous' {β γ : Type v} (f : α → part β) (g : α → β → part γ) :
  continuous' f → continuous' g →
  continuous' (λ x, f x >>= g x)
| ⟨hf,hf'⟩ ⟨hg,hg'⟩ :=
continuous.of_bundled' (order_hom.bind ⟨f,hf⟩ ⟨g,hg⟩)
  (by intro c; rw [ωSup_bind, ← hf', ← hg']; refl)

lemma map_continuous' {β γ : Type v} (f : β → γ) (g : α → part β)
  (hg : continuous' g) :
  continuous' (λ x, f <$> g x) :=
by simp only [map_eq_bind_pure_comp];
   apply bind_continuous' _ _ hg;
   apply const_continuous'

lemma seq_continuous' {β γ : Type v} (f : α → part (β → γ)) (g : α → part β)
  (hf : continuous' f) (hg : continuous' g) :
  continuous' (λ x, f x <*> g x) :=
by simp only [seq_eq_bind_map];
   apply bind_continuous' _ _ hf;
   apply pi.omega_complete_partial_order.flip₂_continuous'; intro;
   apply map_continuous' _ _ hg

lemma continuous (F : α →𝒄 β) (C : chain α) : F (ωSup C) = ωSup (C.map F) :=
continuous_hom.cont _ _

/-- Construct a continuous function from a bare function, a continuous function, and a proof that
they are equal. -/
@[simps, reducible]
def of_fun (f : α → β) (g : α →𝒄 β) (h : f = g) : α →𝒄 β :=
by refine {to_order_hom := {to_fun := f, ..}, ..}; subst h; rcases g with ⟨⟨⟩⟩; assumption

/-- Construct a continuous function from a monotone function with a proof of continuity. -/
@[simps, reducible]
def of_mono (f : α →o β) (h : ∀ c : chain α, f (ωSup c) = ωSup (c.map f)) : α →𝒄 β :=
{ to_fun := f,
  monotone' := f.monotone,
  cont := h }

/-- The identity as a continuous function. -/
@[simps]
def id : α →𝒄 α :=
of_mono order_hom.id continuous_id

/-- The composition of continuous functions. -/
@[simps]
def comp (f : β →𝒄 γ) (g : α →𝒄 β) : α →𝒄 γ :=
of_mono (order_hom.comp (↑f) (↑g)) (continuous_comp _ _ g.cont f.cont)

@[ext]
protected lemma ext (f g : α →𝒄 β) (h : ∀ x, f x = g x) : f = g :=
by cases f; cases g; congr; ext; apply h

protected lemma coe_inj (f g : α →𝒄 β) (h : (f : α → β) = g) : f = g :=
continuous_hom.ext _ _ $ _root_.congr_fun h

@[simp]
lemma comp_id (f : β →𝒄 γ) : f.comp id = f := by ext; refl

@[simp]
lemma id_comp (f : β →𝒄 γ) : id.comp f = f := by ext; refl

@[simp]
lemma comp_assoc (f : γ →𝒄 φ) (g : β →𝒄 γ) (h : α →𝒄 β) : f.comp (g.comp h) = (f.comp g).comp h :=
by ext; refl

@[simp]
lemma coe_apply (a : α) (f : α →𝒄 β) : (f : α →o β) a = f a := rfl

/-- `function.const` is a continuous function. -/
def const (x : β) : α →𝒄 β :=
of_mono (order_hom.const _ x) (continuous_const x)

@[simp] theorem const_apply (f : β) (a : α) : const f a = f := rfl

instance [inhabited β] : inhabited (α →𝒄 β) :=
⟨ const (default β) ⟩

namespace prod

/-- The application of continuous functions as a monotone function.

(It would make sense to make it a continuous function, but we are currently constructing a
`omega_complete_partial_order` instance for `α →𝒄 β`, and we cannot use it as the domain or image
of a continuous function before we do.) -/
@[simps]
def apply : (α →𝒄 β) × α →o β :=
{ to_fun := λ f, f.1 f.2,
  monotone' := λ x y h, by dsimp; transitivity y.fst x.snd; [apply h.1, apply y.1.monotone h.2] }

end prod

/-- The map from continuous functions to monotone functions is itself a monotone function. -/
@[simps]
def to_mono : (α →𝒄 β) →o (α →o β) :=
{ to_fun := λ f, f,
  monotone' := λ x y h, h }

/-- When proving that a chain of applications is below a bound `z`, it suffices to consider the
functions and values being selected from the same index in the chains.

This lemma is more specific than necessary, i.e. `c₀` only needs to be a
chain of monotone functions, but it is only used with continuous functions. -/
@[simp]
lemma forall_forall_merge (c₀ : chain (α →𝒄 β)) (c₁ : chain α) (z : β) :
  (∀ (i j : ℕ), (c₀ i) (c₁ j) ≤ z) ↔ ∀ (i : ℕ), (c₀ i) (c₁ i) ≤ z :=
begin
  split; introv h,
  { apply h },
  { apply le_trans _ (h (max i j)),
    transitivity c₀ i (c₁ (max i j)),
    { apply (c₀ i).monotone, apply c₁.monotone, apply le_max_right },
    { apply c₀.monotone, apply le_max_left } }
end

@[simp]
lemma forall_forall_merge' (c₀ : chain (α →𝒄 β)) (c₁ : chain α) (z : β) :
  (∀ (j i : ℕ), (c₀ i) (c₁ j) ≤ z) ↔ ∀ (i : ℕ), (c₀ i) (c₁ i) ≤ z :=
by rw [forall_swap,forall_forall_merge]

/-- The `ωSup` operator for continuous functions, which takes the pointwise countable supremum
of the functions in the `ω`-chain. -/
@[simps]
protected def ωSup (c : chain (α →𝒄 β)) : α →𝒄 β :=
continuous_hom.of_mono (ωSup $ c.map to_mono)
begin
  intro c',
  apply eq_of_forall_ge_iff, intro z,
  simp only [ωSup_le_iff, (c _).continuous, chain.map_coe, order_hom.apply_coe,
    to_mono_coe, coe_apply, order_hom.omega_complete_partial_order_ωSup_coe,
    forall_forall_merge, forall_forall_merge', (∘), function.eval],
end

@[simps ωSup]
instance : omega_complete_partial_order (α →𝒄 β) :=
omega_complete_partial_order.lift continuous_hom.to_mono continuous_hom.ωSup
  (λ x y h, h) (λ c, rfl)

lemma ωSup_def (c : chain (α →𝒄 β)) (x : α) : ωSup c x = continuous_hom.ωSup c x := rfl

lemma ωSup_ωSup (c₀ : chain (α →𝒄 β)) (c₁ : chain α) :
  ωSup c₀ (ωSup c₁) = ωSup (continuous_hom.prod.apply.comp $ c₀.zip c₁) :=
begin
  apply eq_of_forall_ge_iff, intro z,
  simp only [ωSup_le_iff, (c₀ _).continuous, chain.map_coe, to_mono_coe, coe_apply,
    order_hom.omega_complete_partial_order_ωSup_coe, ωSup_def, forall_forall_merge,
    chain.zip_coe, order_hom.prod_map_coe, order_hom.diag_coe, prod.map_mk,
    order_hom.apply_coe, function.comp_app, prod.apply_coe,
    order_hom.comp_coe, ωSup_apply, function.eval],
end

/-- A family of continuous functions yields a continuous family of functions. -/
@[simps]
def flip {α : Type*} (f : α → β →𝒄 γ) : β →𝒄 α → γ :=
{ to_fun := λ x y, f y x,
  monotone' := λ x y h a, (f a).monotone h,
  cont := by intro; ext; change f x _ = _; rw [(f x).continuous ]; refl, }

/-- `part.bind` as a continuous function. -/
@[simps { rhs_md := reducible }]
noncomputable def bind {β γ : Type v}
  (f : α →𝒄 part β) (g : α →𝒄 β → part γ) : α →𝒄 part γ :=
of_mono (order_hom.bind (↑f) (↑g)) $ λ c, begin
  rw [order_hom.bind, ← order_hom.bind, ωSup_bind, ← f.continuous, ← g.continuous],
  refl
end

/-- `part.map` as a continuous function. -/
@[simps {rhs_md := reducible}]
noncomputable def map {β γ : Type v} (f : β → γ) (g : α →𝒄 part β) : α →𝒄 part γ :=
of_fun (λ x, f <$> g x) (bind g (const (pure ∘ f))) $
by ext; simp only [map_eq_bind_pure_comp, bind_apply, order_hom.bind_coe, const_apply,
  order_hom.const_coe_coe, coe_apply]

/-- `part.seq` as a continuous function. -/
@[simps {rhs_md := reducible}]
noncomputable def seq {β γ : Type v} (f : α →𝒄 part (β → γ)) (g : α →𝒄 part β) :
  α →𝒄 part γ :=
of_fun (λ x, f x <*> g x) (bind f $ (flip $ _root_.flip map g))
  (by ext; simp only [seq_eq_bind_map, flip, part.bind_eq_bind, map_apply, part.mem_bind_iff,
                      bind_apply, order_hom.bind_coe, coe_apply, flip_apply]; refl)

end continuous_hom

end omega_complete_partial_order
