/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/

import order.omega_complete_partial_order
import order.category.Preorder

/-! 
# Category of types with a omega complete partial order

In this file, we bundle the class `omega_complete_partial_order` into a
concrete category and prove that continuous functions also form
a `omega_complete_partial_order`.

## Main definitions

 * `continuous_hom` (with notation →𝒄)
   * an instance of `omega_complete_partial_order (α →𝒄 β)`
 * `continuous_hom.of_fun`
 * `continuous_hom.of_mono`
 * continuous functions:
   * `id`
   * `ite`
   * `const`
   * `roption.bind`
   * `roption.map`
   * `roption.seq`
 * `ωCPO`
   * an instance of `category` and `concrete_category`

 -/

open category_theory

universes u v

namespace omega_complete_partial_order

variables (α : Type*) (β : Type*) {γ : Type*} {φ : Type*}
variables [omega_complete_partial_order α]
variables [omega_complete_partial_order β]
variables [omega_complete_partial_order γ]
variables [omega_complete_partial_order φ]

section old_struct

set_option old_structure_cmd true

/-- A monotone function is continuous if it preserves the supremum of chains -/
structure continuous_hom extends preorder_hom α β :=
(continuous' : continuous (preorder_hom.mk to_fun monotone))

attribute [nolint doc_blame] continuous_hom.to_preorder_hom

end old_struct

infixr ` →𝒄 `:20 := continuous_hom -- Input: \r\MIc

instance : has_coe_to_fun (α →𝒄 β) :=
{ F := λ _, α → β,
  coe :=  continuous_hom.to_fun }

instance : has_coe (α →𝒄 β) (α →ₘ β) :=
{ coe :=  continuous_hom.to_preorder_hom }

instance : partial_order (α →𝒄 β) :=
partial_order.lift continuous_hom.to_fun $ by rintro ⟨⟩ ⟨⟩ h; congr; exact h

variables {α β}

namespace continuous_hom

lemma continuous (F : α →𝒄 β) (C : chain α) :
  F (ωSup C) = ωSup (C.map F) :=
continuous_hom.continuous' _ _

/-- make a continuous function from a bare function, a continuous function and a proof that
they are equal -/
@[simps, reducible]
def of_fun (f : α → β) (g : α →𝒄 β) (h : f = g) : α →𝒄 β :=
{ to_fun := f,
  monotone := by convert g.monotone,
  continuous' := by subst f; exact g.continuous' }

/-- make a continuous function from a monotone function and a proof of continuity -/
@[simps, reducible]
def of_mono (f : α →ₘ β) (h : ∀ c : chain α, f (ωSup c) = ωSup (c.map f)) : α →𝒄 β :=
{ to_fun := f,
  monotone := f.monotone,
  continuous' := h }

/-- identity continuous function -/
@[simps { rhs_md := reducible }]
def id : α →𝒄 α :=
of_mono preorder_hom.id
  (by intro; rw [chain.map_id]; refl)

/-- composition of continuous function -/
@[simps { rhs_md := reducible }]
def comp (f : β →𝒄 γ) (g : α →𝒄 β) : α →𝒄 γ :=
of_mono (preorder_hom.comp (↑f) (↑g))
  (by intro; rw [preorder_hom.comp,← preorder_hom.comp,← chain.map_comp,← f.continuous,← g.continuous]; refl)

@[ext]
protected lemma ext (f g : α →𝒄 β) (h : ∀ x, f x = g x) : f = g :=
by cases f; cases g; congr; ext; apply h

protected lemma coe_inj (f g : α →𝒄 β) (h : (f : α → β) = g) : f = g :=
continuous_hom.ext _ _ $ congr_fun h

@[simp]
lemma comp_id (f : β →𝒄 γ) : f.comp id = f := by ext; refl

@[simp]
lemma id_comp (f : β →𝒄 γ) : id.comp f = f := by ext; refl

@[simp]
lemma comp_assoc (f : γ →𝒄 φ) (g : β →𝒄 γ) (h : α →𝒄 β) : f.comp (g.comp h) = (f.comp g).comp h := by ext; refl

@[simp]
lemma coe_apply (a : α) (f : α →𝒄 β) : (f : α →ₘ β) a = f a := rfl

/-- `const` as a continuous function -/
@[simps {rhs_md := reducible}]
def const (f : β) : α →𝒄 β :=
of_mono (preorder_hom.const _ f)
    begin
      intro c, apply le_antisymm,
      { simp only [function.const, preorder_hom.const_to_fun],
        apply le_ωSup_of_le 0, refl },
      { apply ωSup_le, simp only [preorder_hom.const_to_fun, chain.map_to_fun, function.comp_app],
        intros, refl },
    end

instance [inhabited β] : inhabited (α →𝒄 β) :=
⟨ const (default β) ⟩

namespace prod

variables {α' : Type*} {β' : Type*}
variables [omega_complete_partial_order α'] [omega_complete_partial_order β']

/-- application of continuous functions as a monotone function.
it would make sense to make it a continuous function but
we are currently proving constructing a `omega_complete_partial_order`
instance for `α →𝒄 β`. We cannot use it as the domain or image of
a continuous function before we do. -/
@[simps]
def apply : (α →𝒄 β) × α →ₘ β :=
{ to_fun := λ f, f.1 f.2,
  monotone := λ x y h, by dsimp; transitivity y.fst x.snd; [apply h.1, apply y.1.monotone h.2] }

end prod

/-- conversion of a continuous function into a monotone function
as a monotone function -/
@[simps]
def to_mono : (α →𝒄 β) →ₘ (α →ₘ β) :=
{ to_fun := λ f, f,
  monotone := λ x y h, h }

/-- this lemma is more specific than necessary, i.e. `c₀` only needs to be a
chain of monotone functions but it is only used with continuous functions -/
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

/-- `ωSup` operator for continuous functions -/
@[simps { rhs_md := reducible }]
protected def ωSup (c : chain (α →𝒄 β)) : α →𝒄 β :=
continuous_hom.of_mono (ωSup $ c.map to_mono)
begin
  intro c',
  apply eq_of_forall_ge_iff, intro z,
  simp only [ωSup_le_iff, (c _).continuous, chain.map_to_fun, preorder_hom.monotone_apply_to_fun, to_mono_to_fun, coe_apply,
             preorder_hom.omega_complete_partial_order_ωSup_to_fun, forall_forall_merge, forall_forall_merge', function.comp_app],
end

@[simps ωSup {rhs_md := reducible}]
instance : omega_complete_partial_order (α →𝒄 β) :=
omega_complete_partial_order.lift continuous_hom.to_mono continuous_hom.ωSup
  (λ x y h, h) (λ c, rfl)

lemma ωSup_def (c : chain (α →𝒄 β)) (x : α) : ωSup c x = continuous_hom.ωSup c x := rfl

lemma ωSup_ωSup (c₀ : chain (α →𝒄 β)) (c₁ : chain α) :
  ωSup c₀ (ωSup c₁) = ωSup (continuous_hom.prod.apply.comp $ c₀.zip c₁) :=
begin
  apply eq_of_forall_ge_iff, intro z,
  simp only [ωSup_le_iff, (c₀ _).continuous, chain.map_to_fun, to_mono_to_fun, coe_apply,
             preorder_hom.omega_complete_partial_order_ωSup_to_fun, ωSup_def, forall_forall_merge, chain.zip_to_fun,
             preorder_hom.prod.map_to_fun, preorder_hom.prod.diag_to_fun, prod.map_mk, preorder_hom.monotone_apply_to_fun,
             function.comp_app, prod.apply_to_fun, preorder_hom.comp_to_fun, ωSup_to_fun],
end

/-- `ite` as a continuous function -/
@[simps { rhs_md := reducible }]
def ite (p : Prop) [hp : decidable p] (f g : α →𝒄 β) : α →𝒄 β :=
continuous_hom.of_mono (preorder_hom.ite p f g)
 (λ c, by { rw [preorder_hom.ite, ← preorder_hom.ite, ωSup_ite c (↑f) (↑g),← f.continuous,← g.continuous], refl })

/-- flip the arguments on a continuous function -/
@[simps]
def flip {α : Type*} (f : α → (β →𝒄 γ)) : β →𝒄 (α → γ) :=
{ to_fun := λ x y, f y x,
  monotone := λ x y h a, (f a).monotone h,
  continuous' := by intro; ext; change f x _ = _; rw [(f x).continuous ]; refl, }

/-- `roption.bind` as a continuous function -/
@[simps { rhs_md := reducible }]
noncomputable def bind {β γ : Type v} (f : α →𝒄 roption β) (g : α →𝒄 (β → roption γ)) : α →𝒄 roption γ :=
of_mono (preorder_hom.bind (↑f) (↑g))
  (λ c, by rw [preorder_hom.bind, ← preorder_hom.bind, ωSup_bind, ← f.continuous, ← g.continuous]; refl)

/-- `roption.map` as a continuous function -/
@[simps {rhs_md := reducible}]
noncomputable def map {β γ : Type v} (f : β → γ) (g : α →𝒄 roption β) : α →𝒄 roption γ :=
of_fun (λ x, f <$> g x) (bind g (const (pure ∘ f)))
  (by ext; simp only [map_eq_bind_pure_comp, bind_to_fun, preorder_hom.bind_to_fun, const_to_fun, preorder_hom.const_to_fun, coe_apply])

/-- `roption.seq` as a continuous function -/
@[simps {rhs_md := reducible}]
noncomputable def seq {β γ : Type v} (f : α →𝒄 roption (β → γ)) (g : α →𝒄 roption β) : α →𝒄 roption γ :=
of_fun (λ x, f x <*> g x) (bind f $ (flip $ _root_.flip map g))
  (by ext; simp only [seq_eq_bind_map, flip, roption.bind_eq_bind, map_to_fun, roption.mem_bind_iff, bind_to_fun,
                      preorder_hom.bind_to_fun, coe_apply, flip_to_fun]; refl)


end continuous_hom

end omega_complete_partial_order

/-- The category of types with a omega complete partial order. -/
def ωCPO := bundled omega_complete_partial_order

namespace ωCPO

open omega_complete_partial_order

instance : bundled_hom @continuous_hom :=
{ to_fun := @continuous_hom.to_fun,
  id := @continuous_hom.id,
  comp := @continuous_hom.comp,
  hom_ext := @continuous_hom.coe_inj }

attribute [derive [has_coe_to_sort, large_category, concrete_category]] ωCPO

/-- Construct a bundled ωCPO from the underlying type and typeclass. -/
def of (α : Type*) [omega_complete_partial_order α] : ωCPO := bundled.of α

instance : inhabited ωCPO := ⟨of punit⟩

instance (α : ωCPO) : omega_complete_partial_order α := α.str

end ωCPO
