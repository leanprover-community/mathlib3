/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/
import data.pfun
import data.stream.basic
import tactic.wlog
import tactic.find_unused

/-!
# Omega Complete Partial Orders

## Main definitions

 * class `omega_complete_partial_order`
 * `continuous_hom`, bundled homomorphisms
 * `ite`, `map`, `bind`, `seq` as continuous morphisms

## Instances of `omega_complete_partial_order`

 * `roption`
 * every `complete_lattice`
 * pi-types
 * product types
 * `monotone_hom`
 * `continuous_hom`

## References

 * [G. Markowsky, *Chain-complete posets and directed sets with applications*, https://doi.org/10.1007/BF02485815][markowsky]

-/

universes u v

open_locale classical

structure monotone_hom (α : Type*) [preorder α] (β : Type*) [preorder β] :=
(F : α → β)
(mono : monotone F)

infixr ` →ₘ `:20 := monotone_hom

namespace monotone_hom
variables (α : Type*) (β : Type*) {γ : Type*} {φ : Type*}
variables [preorder α] [preorder β] [preorder γ] [preorder φ]

instance : preorder (α →ₘ β) :=
preorder.lift monotone_hom.F

instance : has_coe_to_fun (α →ₘ β) :=
{ F := λ _, α → β,
  coe := monotone_hom.F }

variables {α β γ}

lemma mono₂ (f : α →ₘ β →ₘ γ) ⦃x₀ x₁ y₀ y₁⦄ (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁) : f x₀ y₀ ≤ f x₁ y₁ :=
by transitivity f x₁ y₀; [ apply f.mono hx, apply (f x₁).mono hy ]

@[simp]
lemma coe_fn_mk_apply (f : α → β) (h) (x) : monotone_hom.mk f h x = f x := rfl

@[simps]
def id : α →ₘ α :=
{ F := id,
  mono := monotone_id }

@[simps]
def comp (f : β →ₘ γ) (g : α →ₘ β) : α →ₘ γ :=
{ F := λ x, f (g x),
  mono := monotone.comp f.mono g.mono }

@[simp]
lemma comp_apply (f : β →ₘ γ) (g : α →ₘ β) {x} : (f.comp g) x = f (g x) := rfl

@[simp]
lemma id_apply {x : α} : id x = x := rfl

@[ext]
protected lemma ext (f g : β →ₘ γ) (h : ∀ x, f x = g x) : f = g :=
by cases f; cases g; congr; ext; apply h

@[simp]
lemma comp_id (f : β →ₘ γ) : f.comp id = f := by ext; refl

@[simp]
lemma id_comp (f : β →ₘ γ) : id.comp f = f := by ext; refl

@[simp]
lemma comp_assoc (f : γ →ₘ φ) (g : β →ₘ γ) (h : α →ₘ β) : f.comp (g.comp h) = (f.comp g).comp h := by ext; refl

variables (α)

@[simps]
def const (f : β) : α →ₘ β :=
{ F := function.const _ f,
  mono := assume x y h, le_refl _}

variables {α} {α' : Type*} {β' : Type*} [preorder α'] [preorder β']

@[simps]
def prod.diag : α →ₘ (α × α) :=
{ F := λ x, (x,x),
  mono := λ x y h, ⟨h,h⟩ }

@[simps]
def prod.map (f : α →ₘ β) (f' : α' →ₘ β') : (α × α') →ₘ (β × β') :=
{ F := prod.map f f',
  mono := λ ⟨x,x'⟩ ⟨y,y'⟩ ⟨h,h'⟩, ⟨f.mono h,f'.mono h'⟩ }

@[simps]
def prod.fst : (α × β) →ₘ α :=
{ F := prod.fst,
  mono := λ ⟨x,x'⟩ ⟨y,y'⟩ ⟨h,h'⟩, h }

@[simps]
def prod.snd : (α × β) →ₘ β :=
{ F := prod.snd,
  mono := λ ⟨x,x'⟩ ⟨y,y'⟩ ⟨h,h'⟩, h' }

@[simp]
lemma prod.fst_map {f : α →ₘ β} {f' : α' →ₘ β'} : prod.fst.comp (prod.map f f') = f.comp prod.fst :=
by ext; refl

@[simp]
lemma prod.snd_map {f : α →ₘ β} {f' : α' →ₘ β'} : prod.snd.comp (prod.map f f') = f'.comp prod.snd :=
by ext; refl

@[simps {rhs_md := semireducible}]
def prod.zip (f : α →ₘ β) (g : α →ₘ γ) : α →ₘ (β × γ) :=
(prod.map f g).comp prod.diag


@[simps]
def prod.zip_with {φ} [preorder φ] (F : β →ₘ (γ →ₘ φ)) (f : α →ₘ β) (g : α →ₘ γ) : α →ₘ φ :=
{ F := λ x, F (f x) (g x),
  mono := λ x y h, by dsimp; apply F.mono₂; [apply f.mono, apply g.mono]; apply h }

@[simps]
def curry : (α × β →ₘ γ) →ₘ α →ₘ β →ₘ γ :=
{ F := λ f, { F := λ x, { F := λ y, f (x, y), mono := λ a b h, f.mono ⟨le_refl _, h⟩ },
              mono := λ a b h x, f.mono ⟨h, le_refl _⟩ },
  mono := λ fx fy h a b, h _ }

@[simps]
def uncurry : (α →ₘ (β →ₘ γ)) →ₘ (α × β) →ₘ γ :=
{ F := λ f, { F := λ x, f x.1 x.2,
              mono := λ x y h, by dsimp; apply f.mono₂; [ exact h.1, exact h.2 ] },
  mono := λ fx fy h a, h _ _ }

@[simps]
def ite (p : Prop) [h : decidable p] (f g : α →ₘ β) :
  α →ₘ β :=
{ F := λ x, @ite _ h _ (f x) (g x),
  mono := by intros x y h; dsimp; split_ifs; [apply f.mono h, apply g.mono h] }

@[simps]
def bind {β γ} (f : α →ₘ roption β) (g : α →ₘ (β → roption γ)) :
  α →ₘ roption γ :=
{ F := λ x, f x >>= g x,
  mono :=
  begin
    intros x y h a,
    simp only [and_imp, exists_prop, roption.bind_eq_bind, roption.mem_bind_iff, exists_imp_distrib],
    intros b hb ha,
    refine ⟨b,f.mono h _ hb,g.mono h _ _ ha⟩,
  end }

end monotone_hom

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

-- @[simp] lemma mem_mk (x : α) (s : stream α) (h) : x ∈ chain.mk s h ↔ x ∈ s := iff.refl _

variables (c c' : chain α)
variables (f : α →ₘ β) -- (hf : monotone f)
variables (g : β →ₘ γ) -- (hg : monotone g)

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
lemma map_id : c.map monotone_hom.id = c :=
monotone_hom.comp_id _

lemma map_comp : (c.map f).map g = c.map (g.comp f) := rfl

lemma map_le_map {g : α →ₘ β} (h : f ≤ g) : c.map f ≤ c.map g :=
λ i, by simp [mem_map_iff]; intros; existsi i; apply h

lemma le_total_of_mem_of_mem {x y : α} (h : x ∈ c) (h' : y ∈ c) : x ≤ y ∨ y ≤ x :=
begin
  cases h with i j, cases h' with j h',
  wlog : i ≤ j := le_total i j using [x y i j,y x j i],
  subst x, subst h', left, apply c.mono case,
end

lemma le_total (i j : ℕ) : c i ≤ c j ∨ c j ≤ c i :=
begin
  wlog : i ≤ j := le_total i j using i j,
  left, apply c.mono case
end

@[simps {rhs_md := semireducible}]
def zip (c₀ : chain α) (c₁ : chain β) : chain (α × β) :=
monotone_hom.prod.zip c₀ c₁

@[simps {rhs_md := semireducible}]
def zip_with (F : α →ₘ β →ₘ γ) (c₀ : chain α) (c₁ : chain β) : chain γ :=
monotone_hom.prod.zip_with F c₀ c₁

end chain

end omega_complete_partial_order

open omega_complete_partial_order

section prio
set_option default_priority 100 -- see Note [default priority]

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

protected def lift [partial_order β] (f : β →ₘ α)
  (ωSup₀ : chain β → β)
  (h : ∀ x y, f x ≤ f y → x ≤ y)
  (h' : ∀ c, f (ωSup₀ c) = ωSup (c.map f)) : omega_complete_partial_order β :=
{ ωSup := ωSup₀,
  ωSup_le := λ c x hx, h _ _ (by rw h'; apply ωSup_le; intro; apply f.mono (hx i)),
  le_ωSup := λ c i, h _ _ (by rw h'; apply le_ωSup (c.map f)) }

protected def lift' [partial_order β] (f : β →ₘ α)
  (ωSup₀ : chain β → β)
  (h : ∀ x y, f x ≤ f y → x ≤ y)
  (h' : ∀ c, f (ωSup₀ c) = ωSup (c.map f)) : omega_complete_partial_order β :=
{ ωSup := ωSup₀,
  ωSup_le := λ c x hx, h _ _ (by rw h'; apply ωSup_le; intro; apply f.mono (hx i)),
  le_ωSup := λ c i, h _ _ (by rw h'; apply le_ωSup (c.map f)) }

lemma le_ωSup_of_mem (c : chain α) : ∀ y ∈ c, y ≤ ωSup c :=
by rintro y ⟨i,hy⟩; rw hy; apply le_ωSup

@[main_declaration]
lemma le_ωSup_of_le {c : chain α} {x : α} {i} (h : x ≤ c i) : x ≤ ωSup c :=
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
    or.inr $ le_ωSup_of_le this)

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

variables (α β)
variables [omega_complete_partial_order β] [omega_complete_partial_order γ]

section old_struct

set_option old_structure_cmd true

/-- A monotone function is continuous if it preserves the supremum of chains -/
structure continuous_hom extends monotone_hom α β :=
(continuous' : ∀ C : chain α, F (ωSup C) = ωSup (C.map (monotone_hom.mk F mono)))

end old_struct

infixr ` →𝒄 `:20 := continuous_hom

instance : has_coe_to_fun (α →𝒄 β) :=
{ F := λ _, α → β,
  coe :=  continuous_hom.F }

instance : partial_order (α →𝒄 β) :=
partial_order.lift continuous_hom.F $ by rintro ⟨⟩ ⟨⟩ h; congr; exact h

variables {α β}

lemma continuous_hom.continuous (F : α →𝒄 β) (C : chain α) :
  F (ωSup C) = ωSup (C.map F.to_monotone_hom) :=
continuous_hom.continuous' _ _

end continuity

namespace continuous_hom

variables {α β} {φ : Type*}
variables [omega_complete_partial_order β]
variables [omega_complete_partial_order γ]
variables [omega_complete_partial_order φ]

variables
  (f : α →𝒄 β)
  (g : β →𝒄 γ)

@[simps]
def id : α →𝒄 α :=
{ F := id,
  mono := monotone_id,
  continuous' := by intro; rw [← monotone_hom.id, chain.map_id]; refl }

@[simps]
def comp (f : β →𝒄 γ) (g : α →𝒄 β) : α →𝒄 γ :=
{ f.to_monotone_hom.comp g.to_monotone_hom with
  continuous' := by intro; rw [monotone_hom.comp,← monotone_hom.comp,← chain.map_comp,← f.continuous,← g.continuous]; refl }

@[simp]
lemma comp_apply (f : β →ₘ γ) (g : α →ₘ β) {x} : (f.comp g) x = f (g x) := rfl

@[simp]
lemma id_apply {x : α} : id x = x := rfl

@[ext]
protected lemma ext (f g : β →𝒄 γ) (h : ∀ x, f x = g x) : f = g :=
by cases f; cases g; congr; ext; apply h

@[simp]
lemma comp_id (f : β →𝒄 γ) : f.comp id = f := by ext; refl

@[simp]
lemma id_comp (f : β →𝒄 γ) : id.comp f = f := by ext; refl

@[simp]
lemma comp_assoc (f : γ →𝒄 φ) (g : β →𝒄 γ) (h : α →𝒄 β) : f.comp (g.comp h) = (f.comp g).comp h := by ext; refl

@[simps, reducible]
def of_fun (f : α → β) (g : α →𝒄 β) (h : f = g) : α →𝒄 β :=
{ F := f,
  mono := by convert g.mono,
  continuous' := by subst f; exact g.continuous' }

@[simps, reducible]
def of_mono (f : α →ₘ β) (h : ∀ c : chain α, f (ωSup c) = ωSup (c.map f)) : α →𝒄 β :=
{ F := f,
  mono := f.mono,
  continuous' := h }

@[simp]
lemma to_montone_hom_apply (a : α) (f : α →𝒄 β) : f.to_monotone_hom a = f a := rfl

@[simps {rhs_md := semireducible}]
def const (f : β) : α →𝒄 β :=
of_mono (monotone_hom.const _ f)
    begin
      intro c, apply le_antisymm,
      { simp [function.const], apply le_ωSup_of_mem, simp [chain.mem_map_iff], exact ⟨ c 0, ⟨0, rfl⟩ ⟩ },
      { apply ωSup_le, simp [chain.mem_map_iff],
        intros, refl },
    end

end continuous_hom

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

variables {α : Type*} {β : α → Type v}

section monotone

variables [∀a, partial_order (β a)]

@[simps]
def monotone_apply (a : α) : (Πa, β a) →ₘ β a  :=
{ F := (λf:Πa, β a, f a),
  mono := assume f g hfg, hfg a }

end monotone

open omega_complete_partial_order omega_complete_partial_order.chain

variables  [∀a, omega_complete_partial_order (β a)]
instance : omega_complete_partial_order (Πa, β a) :=
{ ωSup    := λc a, ωSup (c.map (monotone_apply a)),
  ωSup_le := assume c f hf a, ωSup_le _ _ $ by { rintro i, apply hf },
  le_ωSup := assume c i x, le_ωSup_of_mem _ _ $ by { rw mem_map_iff, exact ⟨c i,⟨i,rfl⟩,rfl⟩ } }

protected lemma ωSup_eq (c : chain (Π x, β x)) (a : α) : ωSup c a = ωSup (c.map (monotone_apply a) ) := rfl

section continuity

variables {γ : Type*} [omega_complete_partial_order γ]

def continuous_ext
  (f : ∀ x : α, γ →𝒄 β x) :
  γ →𝒄 Π a, β a :=
{ F := λ y x, f _ y,
  mono := by { intros x y h' a, apply (f a).mono h' },
  continuous' :=
  by { intro c, ext, dsimp, rw [pi.ωSup_eq,map_comp],
       change f _ _ = _, apply (f x).continuous c } }

def continuous_congr (f : γ →𝒄 Π x, β x) (x : α) : γ →𝒄 β x :=
{ F := λ y, f y x,
  mono := λ a b h, f.mono h _,
  continuous' := λ c, congr_fun (f.continuous _) x }

end continuity

end pi

namespace prod

lemma le_def {α β} [has_le α] [has_le β] (x y : α × β) : x ≤ y ↔ x.1 ≤ y.1 ∧ x.2 ≤ y.2 := iff.refl _

open omega_complete_partial_order
variables {α : Type*} {β : Type*} {γ : Type*}
variables [omega_complete_partial_order α]
variables [omega_complete_partial_order β]
variables [omega_complete_partial_order γ]

@[simps]
protected def ωSup (c : chain (α × β)) : α × β :=
(ωSup (c.map monotone_hom.prod.fst), ωSup (c.map monotone_hom.prod.snd))

@[main_declaration]
instance : omega_complete_partial_order (α × β) :=
{ ωSup := prod.ωSup,
  ωSup_le := λ c ⟨x,x'⟩ h, ⟨ωSup_le _ _ $ λ i, (h i).1, ωSup_le _ _ $ λ i, (h i).2⟩,
  le_ωSup := λ c i, by split; [refine le_ωSup (c.map monotone_hom.prod.fst) i, refine le_ωSup (c.map monotone_hom.prod.snd) i] } -- ; refine ⟨i,_⟩; simp [h] }

variables {α' : Type*} {β' : Type*}
variables [omega_complete_partial_order α'] [omega_complete_partial_order β']

namespace continuous_hom

@[simps {rhs_md := semireducible}]
protected def fst : (α × β) →𝒄 α :=
continuous_hom.of_mono (monotone_hom.prod.fst)
  (by intro; apply eq_of_forall_ge_iff; intro c'; simp [ωSup_le_iff,chain.mem_map_iff,omega_complete_partial_order.ωSup])

@[simps {rhs_md := semireducible}]
protected def snd : (α × β) →𝒄 β :=
continuous_hom.of_mono (monotone_hom.prod.snd)
  (by intro; apply eq_of_forall_ge_iff; intro c'; simp [ωSup_le_iff,chain.mem_map_iff,omega_complete_partial_order.ωSup])

@[simps {rhs_md := semireducible}]
def diag : α →𝒄 (α × α) :=
continuous_hom.of_mono monotone_hom.prod.diag
begin
  intro; apply eq_of_forall_ge_iff; intro c',
  simp only [ωSup_le_iff, chain.mem_map_iff, prod.le_def, omega_complete_partial_order.ωSup, monotone_hom.prod.snd_F, and_imp,
             ωSup_fst, «exists», exists_and_distrib_right, exists_eq_right, mk.inj_iff, ωSup_snd, monotone_hom.prod.diag_F,
             monotone_hom.prod.fst_F, exists_imp_distrib],
   apply and_congr,
   all_goals
   { split, intros, subst_vars, solve_by_elim,
     introv h₀, apply h₀ _, }
end

@[simps {rhs_md := semireducible}]
def map (f : α →𝒄 β) (f' : α' →𝒄 β') : (α × α') →𝒄 (β × β') :=
continuous_hom.of_mono (monotone_hom.prod.map f.to_monotone_hom f'.to_monotone_hom)
begin
  intro; apply eq_of_forall_ge_iff; intro c',
  simp [ωSup_le_iff, prod.le_def, omega_complete_partial_order.ωSup, f.continuous, f'.continuous, c.map_comp],
end

@[simps]
def apply : (α →𝒄 β) × α →ₘ β :=
{ F := λ f, f.1 f.2,
  mono := λ x y h, by dsimp; transitivity y.fst x.snd; [apply h.1, apply y.1.mono h.2] }

def zip (f : α →𝒄 β) (g : α →𝒄 γ) : α →𝒄 (β × γ) :=
(prod.continuous_hom.map f g).comp prod.continuous_hom.diag

end continuous_hom
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

namespace monotone_hom

instance : partial_order (α →ₘ β) :=
partial_order.lift monotone_hom.F $ by rintro ⟨⟩ ⟨⟩ h; congr; exact h

@[simps]
def apply : ((α →ₘ β) × α) →ₘ β :=
{ F := λ fx, fx.1 fx.2,
  mono := λ x y h, by dsimp; transitivity y.fst x.snd; [apply h.1, apply y.1.mono h.2] }

@[simps]
def monotone_apply (a : α) : (α →ₘ β) →ₘ β  :=
{ F := (λf : α →ₘ β, f a),
  mono := assume f g hfg, hfg a }

def F_hom : (α →ₘ β) →ₘ (α → β) :=
{ F := λ f, f.F,
  mono := λ x y h, h }

@[simps]
protected def ωSup (c : chain (α →ₘ β)) : α →ₘ β :=
{  F := λ a, ωSup (c.map (monotone_apply a)),
   mono := λ x y h, ωSup_le_ωSup_of_le (chain.map_le_map _ $ λ a, a.mono h) }

@[simps {rhs_md := semireducible}]
instance : omega_complete_partial_order (α →ₘ β) :=
omega_complete_partial_order.lift monotone_hom.F_hom monotone_hom.ωSup
  (λ x y h, h) (λ c, rfl)

@[simps]
def prod.mk : α →ₘ β →ₘ (α × β) :=
{ F := λ x, { F := λ y, (x,y), mono := λ a b h, ⟨le_refl _, h⟩ },
  mono := λ a b h x, ⟨h, le_refl _⟩ }

@[simp]
lemma prod.fst_mk (x : α) :
  monotone_hom.prod.fst.comp (prod.mk x : β →ₘ α × β) = monotone_hom.const β x := rfl

@[simp]
lemma prod.snd_mk (x : α) :
  monotone_hom.prod.snd.comp (prod.mk x : β →ₘ α × β) = monotone_hom.id := rfl

@[simp]
lemma prod.fst_diag :
  monotone_hom.prod.fst.comp (monotone_hom.prod.diag : α →ₘ α × α) = monotone_hom.id := rfl

@[simp]
lemma prod.snd_diag :
  monotone_hom.prod.snd.comp (monotone_hom.prod.diag : α →ₘ α × α) = monotone_hom.id := rfl

end monotone_hom

namespace continuous_hom

@[simps]
def to_mono : (α →𝒄 β) →ₘ (α →ₘ β) :=
{ F := λ f, f.to_monotone_hom,
  mono := λ x y h, h }

lemma to_mono_inj : function.injective (to_mono : (α →𝒄 β) → (α →ₘ β)) :=
λ ⟨x,_,_⟩ ⟨y,_,_⟩ h, by congr; injection h

@[simp]
lemma to_mono_of_mono (f : α →ₘ β) (h) : to_mono (of_mono f h) = f := by cases f; refl

@[simp]
lemma forall_forall_merge (c₀ : chain (α →𝒄 β)) (c₁ : chain α) (z : β) :
  (∀ (i j : ℕ), (c₀ i) (c₁ j) ≤ z) ↔ ∀ (i : ℕ), (c₀ i) (c₁ i) ≤ z :=
begin
  split; introv h,
  { apply h },
  { apply le_trans _ (h (max i j)),
    transitivity c₀ i (c₁ (max i j)),
    { apply (c₀ i).mono, apply c₁.mono, apply le_max_right },
    { apply c₀.mono, apply le_max_left } }
end

@[simp]
lemma forall_forall_merge' (c₀ : chain (α →𝒄 β)) (c₁ : chain α) (z : β) :
  (∀ (j i : ℕ), (c₀ i) (c₁ j) ≤ z) ↔ ∀ (i : ℕ), (c₀ i) (c₁ i) ≤ z :=
by rw [forall_swap,forall_forall_merge]

protected def ωSup (c : chain (α →𝒄 β)) : α →𝒄 β :=
continuous_hom.of_mono (ωSup $ c.map to_mono)
begin
  intro c',
  apply eq_of_forall_ge_iff, intro z,
  simp only [ωSup_le_iff, (c _).continuous, chain.map_F, monotone_hom.monotone_apply_F, to_mono_F, to_montone_hom_apply,
             monotone_hom.omega_complete_partial_order_ωSup_F, forall_forall_merge, forall_forall_merge'],
end

lemma ωSup_def (c : chain (α →𝒄 β)) : (continuous_hom.ωSup c).to_monotone_hom = ωSup (c.map to_mono) := rfl

@[simps {rhs_md := semireducible}]
instance : omega_complete_partial_order (α →𝒄 β) :=
omega_complete_partial_order.lift continuous_hom.to_mono continuous_hom.ωSup
  (λ x y h, h) (λ c, rfl)

lemma ωSup_ωSup (c₀ : chain (α →𝒄 β)) (c₁ : chain α) :
  ωSup c₀ (ωSup c₁) = ωSup (prod.continuous_hom.apply.comp $ c₀.zip c₁) :=
begin
  apply eq_of_forall_ge_iff, intro z,
  simp only [ωSup_le_iff, (c₀ _).continuous, chain.map_F, monotone_hom.monotone_apply_F, to_mono_F, to_montone_hom_apply,
             monotone_hom.omega_complete_partial_order_ωSup_F, omega_complete_partial_order_ωSup_F, monotone_hom.comp_apply,
             forall_forall_merge, chain.zip_F, monotone_hom.prod.map_F, prod.continuous_hom.apply_F, monotone_hom.prod.diag_F,
             prod.map_mk],
end

def of_mono₂ (f : α →ₘ β →ₘ γ)
  (h : ∀ x c, f x (ωSup c) = ωSup (c.map (f x)))
  (h' : ∀ c, f (ωSup c) = ωSup (c.map f)) : α →𝒄 β →𝒄 γ :=
{ F := λ a, continuous_hom.of_mono (f a) (h a),
  mono := λ a b h x, by dsimp; apply f.mono h,
  continuous' := λ c, by apply to_mono_inj; simp [h']; refl }


lemma cont_ite {p : Prop} [hp : decidable p] (c : chain α) (f g : α →ₘ β) :
  ωSup (c.map (monotone_hom.ite p f g)) = ite p (ωSup $ c.map f) (ωSup $ c.map g) :=
by dsimp [monotone_hom.ite]; split_ifs; refl

@[simps]
def ite (p : Prop) [hp : decidable p] (f g : α →𝒄 β) : α →𝒄 β :=
{ monotone_hom.ite p f.to_monotone_hom g.to_monotone_hom with
  continuous' := λ c, by rw [monotone_hom.ite, ← monotone_hom.ite, cont_ite c _ _,← f.continuous,← g.continuous]; refl }

lemma cont_bind {β γ : Type v} (c : chain α) (f : α →𝒄 roption β) (g : α →𝒄 (β → roption γ)) :
  ωSup (c.map (f.to_monotone_hom.bind g.to_monotone_hom)) = ωSup (c.map f.to_monotone_hom) >>= ωSup (c.map g.to_monotone_hom) :=
begin
  apply eq_of_forall_ge_iff, intro x,
  simp only [ωSup_le_iff, roption.bind_le, chain.mem_map_iff, and_imp, monotone_hom.bind_F, exists_imp_distrib],
  split; intro h''',
  { intros b hb, apply ωSup_le _ _ _,
    simp only [chain.mem_map_iff, and_imp, exists_exists_and_eq_and, exists_imp_distrib],
    intros i,
    { rintros y hy, simp only [roption.mem_ωSup] at hb,
      rcases hb with ⟨j,hb⟩, replace hb := hb.symm,
      simp [roption.eq_some_iff] at hy hb,
      replace hb : b ∈ f (c (max i j))   := f.mono (c.mono (le_max_right i j)) _ hb,
      replace hy : y ∈ g (c (max i j)) b := g.mono (c.mono (le_max_left i j)) _ _ hy,
      apply h''' (max i j),
      simp [exists_prop, roption.bind_eq_bind, roption.mem_bind_iff],
      exact ⟨_,hb,hy⟩, } },
  { intros i, intros y hy,
    simp [exists_prop, roption.bind_eq_bind, roption.mem_bind_iff] at hy,
    rcases hy with ⟨b,hb₀,hb₁⟩,
    apply h''' b _,
    { apply le_ωSup (c.map g.to_monotone_hom) _ _ _ hb₁ },
    { apply le_ωSup (c.map f.to_monotone_hom) i _ hb₀ } },
end

@[simps]
def flip {α : Type*} (f : α → (β →𝒄 γ)) : β →𝒄 (α → γ) :=
{ F := λ x y, f y x,
  mono := λ x y h a, (f a).mono h,
  continuous' := by intro; ext; rw [(f x).continuous]; refl, }

@[simps { rhs_md := reducible }]
noncomputable def bind {β γ : Type v} (f : α →𝒄 roption β) (g : α →𝒄 (β → roption γ)) : α →𝒄 roption γ :=
of_mono (monotone_hom.bind f.to_monotone_hom g.to_monotone_hom)
  (λ c, by rw [monotone_hom.bind, ← monotone_hom.bind, cont_bind, ← f.continuous, ← g.continuous]; refl)

@[simps {rhs_md := reducible}]
noncomputable def map {β γ : Type v} (f : β → γ) (g : α →𝒄 roption β) : α →𝒄 roption γ :=
of_fun (λ x, f <$> g x) (bind g (const (pure ∘ f)))
  (by ext; simp only [map_eq_bind_pure_comp, bind_F, monotone_hom.bind_F, const_F, monotone_hom.const_F, to_montone_hom_apply])

noncomputable def seq {β γ : Type v} (f : α →𝒄 roption (β → γ)) (g : α →𝒄 roption β) : α →𝒄 roption γ :=
of_fun (λ x, f x <*> g x) (bind f $ (flip $ _root_.flip map g))
  (by ext; simp only [seq_eq_bind_map, flip, roption.bind_eq_bind, map_F, roption.mem_bind_iff, bind_F,
                      monotone_hom.bind_F, to_montone_hom_apply, flip_F]; refl)

end continuous_hom

end omega_complete_partial_order
