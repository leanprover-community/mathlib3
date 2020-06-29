/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro

In the standard library we cannot assume the univalence axiom.
We say two types are equivalent if they are isomorphic.

Two equivalent types have the same cardinality.
-/
import data.set.function
import data.option.basic
import algebra.group.basic

open function

universes u v w z
variables {α : Sort u} {β : Sort v} {γ : Sort w}

/-- `α ≃ β` is the type of functions from `α → β` with a two-sided inverse. -/
structure equiv (α : Sort*) (β : Sort*) :=
(to_fun    : α → β)
(inv_fun   : β → α)
(left_inv  : left_inverse inv_fun to_fun)
(right_inv : right_inverse inv_fun to_fun)

infix ` ≃ `:25 := equiv

/-- Convert an involutive function `f` to an equivalence with `to_fun = inv_fun = f`. -/
def function.involutive.to_equiv (f : α → α) (h : involutive f) : α ≃ α :=
⟨f, f, h.left_inverse, h.right_inverse⟩

namespace equiv

/-- `perm α` is the type of bijections from `α` to itself. -/
@[reducible] def perm (α : Sort*) := equiv α α

instance : has_coe_to_fun (α ≃ β) :=
⟨_, to_fun⟩

@[simp] theorem coe_fn_mk (f : α → β) (g l r) : (equiv.mk f g l r : α → β) = f :=
rfl

/-- The map `coe_fn : (r ≃ s) → (r → s)` is injective. We can't use `function.injective`
here but mimic its signature by using `⦃e₁ e₂⦄`. -/
theorem coe_fn_injective : ∀ ⦃e₁ e₂ : equiv α β⦄, (e₁ : α → β) = e₂ → e₁ = e₂
| ⟨f₁, g₁, l₁, r₁⟩ ⟨f₂, g₂, l₂, r₂⟩ h :=
  have f₁ = f₂, from h,
  have g₁ = g₂, from l₁.eq_right_inverse (this.symm ▸ r₂),
  by simp *

@[ext] lemma ext {f g : equiv α β} (H : ∀ x, f x = g x) : f = g :=
coe_fn_injective (funext H)

@[ext] lemma perm.ext {σ τ : equiv.perm α} (H : ∀ x, σ x = τ x) : σ = τ :=
equiv.ext H

/-- Any type is equivalent to itself. -/
@[refl] protected def refl (α : Sort*) : α ≃ α := ⟨id, id, λ x, rfl, λ x, rfl⟩

/-- Inverse of an equivalence `e : α ≃ β`. -/
@[symm] protected def symm (e : α ≃ β) : β ≃ α := ⟨e.inv_fun, e.to_fun, e.right_inv, e.left_inv⟩

/-- Composition of equivalences `e₁ : α ≃ β` and `e₂ : β ≃ γ`. -/
@[trans] protected def trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
⟨e₂.to_fun ∘ e₁.to_fun, e₁.inv_fun ∘ e₂.inv_fun,
  e₂.left_inv.comp e₁.left_inv, e₂.right_inv.comp e₁.right_inv⟩

@[simp]
lemma to_fun_as_coe (e : α ≃ β) (a : α) : e.to_fun a = e a := rfl

@[simp]
lemma inv_fun_as_coe (e : α ≃ β) (b : β) : e.inv_fun b = e.symm b := rfl

protected theorem injective (e : α ≃ β) : injective e :=
e.left_inv.injective

protected theorem surjective (e : α ≃ β) : surjective e :=
e.right_inv.surjective

protected theorem bijective (f : α ≃ β) : bijective f :=
⟨f.injective, f.surjective⟩

@[simp] lemma range_eq_univ {α : Type*} {β : Type*} (e : α ≃ β) : set.range e = set.univ :=
set.eq_univ_of_forall e.surjective

protected theorem subsingleton (e : α ≃ β) [subsingleton β] : subsingleton α :=
e.injective.comap_subsingleton

/-- Transfer `decidable_eq` across an equivalence. -/
protected def decidable_eq (e : α ≃ β) [decidable_eq β] : decidable_eq α :=
e.injective.decidable_eq

lemma nonempty_iff_nonempty (e : α ≃ β) : nonempty α ↔ nonempty β :=
nonempty.congr e e.symm

/-- If `α ≃ β` and `β` is inhabited, then so is `α`. -/
protected def inhabited [inhabited β] (e : α ≃ β) : inhabited α :=
⟨e.symm (default _)⟩

/-- If `α ≃ β` and `β` is a singleton type, then so is `α`. -/
protected def unique [unique β] (e : α ≃ β) : unique α :=
e.symm.surjective.unique

/-- Equivalence between equal types. -/
protected def cast {α β : Sort*} (h : α = β) : α ≃ β :=
⟨cast h, cast h.symm, λ x, by { cases h, refl }, λ x, by { cases h, refl }⟩

@[simp] theorem coe_fn_symm_mk (f : α → β) (g l r) : ((equiv.mk f g l r).symm : β → α) = g :=
rfl

@[simp] theorem coe_refl : ⇑(equiv.refl α) = id := rfl

theorem refl_apply (x : α) : equiv.refl α x = x := rfl

@[simp] theorem coe_trans (f : α ≃ β) (g : β ≃ γ) : ⇑(f.trans g) = g ∘ f := rfl

theorem trans_apply (f : α ≃ β) (g : β ≃ γ) (a : α) : (f.trans g) a = g (f a) := rfl

@[simp] theorem apply_symm_apply  (e : α ≃ β) (x : β) : e (e.symm x) = x :=
e.right_inv x

@[simp] theorem symm_apply_apply (e : α ≃ β) (x : α) : e.symm (e x) = x :=
e.left_inv x

@[simp] theorem symm_comp_self (e : α ≃ β) : e.symm ∘ e = id := funext e.symm_apply_apply

@[simp] theorem self_comp_symm (e : α ≃ β) : e ∘ e.symm = id := funext e.apply_symm_apply

@[simp] lemma symm_trans_apply (f : α ≃ β) (g : β ≃ γ) (a : γ) :
  (f.trans g).symm a = f.symm (g.symm a) := rfl

@[simp] theorem apply_eq_iff_eq (f : α ≃ β) (x y : α) : f x = f y ↔ x = y :=
f.injective.eq_iff

theorem apply_eq_iff_eq_symm_apply {α β : Sort*} (f : α ≃ β) (x : α) (y : β) :
  f x = y ↔ x = f.symm y :=
begin
  conv_lhs { rw ←apply_symm_apply f y, },
  rw apply_eq_iff_eq,
end

@[simp] theorem cast_apply {α β} (h : α = β) (x : α) : equiv.cast h x = cast h x := rfl

lemma symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = y ↔ x = e y :=
⟨λ H, by simp [H.symm], λ H, by simp [H]⟩

lemma eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm x ↔ e y = x :=
(eq_comm.trans e.symm_apply_eq).trans eq_comm

@[simp] theorem symm_symm (e : α ≃ β) : e.symm.symm = e := by { cases e, refl }

@[simp] theorem trans_refl (e : α ≃ β) : e.trans (equiv.refl β) = e := by { cases e, refl }

@[simp] theorem refl_symm : (equiv.refl α).symm = equiv.refl α := rfl

@[simp] theorem refl_trans (e : α ≃ β) : (equiv.refl α).trans e = e := by { cases e, refl }

@[simp] theorem symm_trans (e : α ≃ β) : e.symm.trans e = equiv.refl β := ext (by simp)

@[simp] theorem trans_symm (e : α ≃ β) : e.trans e.symm = equiv.refl α := ext (by simp)

lemma trans_assoc {δ} (ab : α ≃ β) (bc : β ≃ γ) (cd : γ ≃ δ) :
  (ab.trans bc).trans cd = ab.trans (bc.trans cd) :=
equiv.ext $ assume a, rfl

theorem left_inverse_symm (f : equiv α β) : left_inverse f.symm f := f.left_inv

theorem right_inverse_symm (f : equiv α β) : function.right_inverse f.symm f := f.right_inv

/-- If `α` is equivalent to `β` and `γ` is equivalent to `δ`, then the type of equivalences `α ≃ γ`
is equivalent to the type of equivalences `β ≃ δ`. -/
def equiv_congr {δ} (ab : α ≃ β) (cd : γ ≃ δ) : (α ≃ γ) ≃ (β ≃ δ) :=
⟨ λac, (ab.symm.trans ac).trans cd, λbd, ab.trans $ bd.trans $ cd.symm,
  assume ac, by { ext x, simp }, assume ac, by { ext x, simp } ⟩

/-- If `α` is equivalent to `β`, then `perm α` is equivalent to `perm β`. -/
def perm_congr {α : Type*} {β : Type*} (e : α ≃ β) : perm α ≃ perm β :=
equiv_congr e e

protected lemma image_eq_preimage {α β} (e : α ≃ β) (s : set α) : e '' s = e.symm ⁻¹' s :=
set.ext $ assume x, set.mem_image_iff_of_inverse e.left_inv e.right_inv

protected lemma subset_image {α β} (e : α ≃ β) (s : set α) (t : set β) :
  t ⊆ e '' s ↔ e.symm '' t ⊆ s :=
by rw [set.image_subset_iff, e.image_eq_preimage]

lemma symm_image_image {α β} (f : equiv α β) (s : set α) : f.symm '' (f '' s) = s :=
by { rw [← set.image_comp], simp }

protected lemma image_compl {α β} (f : equiv α β) (s : set α) :
  f '' sᶜ = (f '' s)ᶜ :=
set.image_compl_eq f.bijective

/- The group of permutations (self-equivalences) of a type `α` -/

namespace perm

instance perm_group {α : Type u} : group (perm α) :=
begin
  refine { mul := λ f g, equiv.trans g f, one := equiv.refl α, inv:= equiv.symm, ..};
  intros; apply equiv.ext; try { apply trans_apply },
  apply symm_apply_apply
end

@[simp] theorem mul_apply {α : Type u} (f g : perm α) (x) : (f * g) x = f (g x) :=
equiv.trans_apply _ _ _

@[simp] theorem one_apply {α : Type u} (x) : (1 : perm α) x = x := rfl

@[simp] lemma inv_apply_self {α : Type u} (f : perm α) (x) :
  f⁻¹ (f x) = x := equiv.symm_apply_apply _ _

@[simp] lemma apply_inv_self {α : Type u} (f : perm α) (x) :
  f (f⁻¹ x) = x := equiv.apply_symm_apply _ _

lemma one_def {α : Type u} : (1 : perm α) = equiv.refl α := rfl

lemma mul_def {α : Type u} (f g : perm α) : f * g = g.trans f := rfl

lemma inv_def {α : Type u} (f : perm α) : f⁻¹ = f.symm := rfl

end perm

/-- If `α` is an empty type, then it is equivalent to the `empty` type. -/
def equiv_empty (h : α → false) : α ≃ empty :=
⟨λ x, (h x).elim, λ e, e.rec _, λ x, (h x).elim, λ e, e.rec _⟩

/-- `false` is equivalent to `empty`. -/
def false_equiv_empty : false ≃ empty :=
equiv_empty _root_.id

/-- If `α` is an empty type, then it is equivalent to the `pempty` type in any universe. -/
def {u' v'} equiv_pempty {α : Sort v'} (h : α → false) : α ≃ pempty.{u'} :=
⟨λ x, (h x).elim, λ e, e.rec _, λ x, (h x).elim, λ e, e.rec _⟩

/-- `false` is equivalent to `pempty`. -/
def false_equiv_pempty : false ≃ pempty :=
equiv_pempty _root_.id

/-- `empty` is equivalent to `pempty`. -/
def empty_equiv_pempty : empty ≃ pempty :=
equiv_pempty $ empty.rec _

/-- `pempty` types from any two universes are equivalent. -/
def pempty_equiv_pempty : pempty.{v} ≃ pempty.{w} :=
equiv_pempty pempty.elim

/-- If `α` is not `nonempty`, then it is equivalent to `empty`. -/
def empty_of_not_nonempty {α : Sort*} (h : ¬ nonempty α) : α ≃ empty :=
equiv_empty $ assume a, h ⟨a⟩

/-- If `α` is not `nonempty`, then it is equivalent to `pempty`. -/
def pempty_of_not_nonempty {α : Sort*} (h : ¬ nonempty α) : α ≃ pempty :=
equiv_pempty $ assume a, h ⟨a⟩

/-- The `Sort` of proofs of a true proposition is equivalent to `punit`. -/
def prop_equiv_punit {p : Prop} (h : p) : p ≃ punit :=
⟨λ x, (), λ x, h, λ _, rfl, λ ⟨⟩, rfl⟩

/-- `true` is equivalent to `punit`. -/
def true_equiv_punit : true ≃ punit := prop_equiv_punit trivial

/-- `ulift α` is equivalent to `α`. -/
protected def ulift {α : Type u} : ulift α ≃ α :=
⟨ulift.down, ulift.up, ulift.up_down, λ a, rfl⟩

/-- `plift α` is equivalent to `α`. -/
protected def plift : plift α ≃ α :=
⟨plift.down, plift.up, plift.up_down, plift.down_up⟩

/-- equivalence of propositions is the same as iff -/
def of_iff {P Q : Prop} (h : P ↔ Q) : P ≃ Q :=
{ to_fun := h.mp,
  inv_fun := h.mpr,
  left_inv := λ x, rfl,
  right_inv := λ y, rfl }

/-- If `α₁` is equivalent to `α₂` and `β₁` is equivalent to `β₂`, then the type of maps `α₁ → β₁`
is equivalent to the type of maps `α₂ → β₂`. -/
@[congr] def arrow_congr {α₁ β₁ α₂ β₂ : Sort*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
  (α₁ → β₁) ≃ (α₂ → β₂) :=
{ to_fun := λ f, e₂.to_fun ∘ f ∘ e₁.inv_fun,
  inv_fun := λ f, e₂.inv_fun ∘ f ∘ e₁.to_fun,
  left_inv := λ f, funext $ λ x, by simp,
  right_inv := λ f, funext $ λ x, by simp }

@[simp] lemma arrow_congr_apply {α₁ β₁ α₂ β₂ : Sort*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂)
  (f : α₁ → β₁) (x : α₂) :
  arrow_congr e₁ e₂ f x = (e₂ $ f $ e₁.symm x) :=
rfl

lemma arrow_congr_comp {α₁ β₁ γ₁ α₂ β₂ γ₂ : Sort*}
  (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) (ec : γ₁ ≃ γ₂) (f : α₁ → β₁) (g : β₁ → γ₁) :
  arrow_congr ea ec (g ∘ f) = (arrow_congr eb ec g) ∘ (arrow_congr ea eb f) :=
by { ext, simp only [comp, arrow_congr_apply, eb.symm_apply_apply] }

@[simp] lemma arrow_congr_refl {α β : Sort*} :
  arrow_congr (equiv.refl α) (equiv.refl β) = equiv.refl (α → β) := rfl

@[simp] lemma arrow_congr_trans {α₁ β₁ α₂ β₂ α₃ β₃ : Sort*}
  (e₁ : α₁ ≃ α₂) (e₁' : β₁ ≃ β₂) (e₂ : α₂ ≃ α₃) (e₂' : β₂ ≃ β₃) :
  arrow_congr (e₁.trans e₂) (e₁'.trans e₂') = (arrow_congr e₁ e₁').trans (arrow_congr e₂ e₂') :=
rfl

@[simp] lemma arrow_congr_symm {α₁ β₁ α₂ β₂ : Sort*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
  (arrow_congr e₁ e₂).symm = arrow_congr e₁.symm e₂.symm :=
rfl

/--
A version of `equiv.arrow_congr` in `Type`, rather than `Sort`.

The `equiv_rw` tactic is not able to use the default `Sort` level `equiv.arrow_congr`,
because Lean's universe rules will not unify `?l_1` with `imax (1 ?m_1)`.
-/
@[congr]
def arrow_congr' {α₁ β₁ α₂ β₂ : Type*} (hα : α₁ ≃ α₂) (hβ : β₁ ≃ β₂) : (α₁ → β₁) ≃ (α₂ → β₂) :=
equiv.arrow_congr hα hβ

@[simp] lemma arrow_congr'_apply {α₁ β₁ α₂ β₂ : Type*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂)
  (f : α₁ → β₁) (x : α₂) :
  arrow_congr' e₁ e₂ f x = (e₂ $ f $ e₁.symm x) :=
rfl

@[simp] lemma arrow_congr'_refl {α β : Type*} :
  arrow_congr' (equiv.refl α) (equiv.refl β) = equiv.refl (α → β) := rfl

@[simp] lemma arrow_congr'_trans {α₁ β₁ α₂ β₂ α₃ β₃ : Type*}
  (e₁ : α₁ ≃ α₂) (e₁' : β₁ ≃ β₂) (e₂ : α₂ ≃ α₃) (e₂' : β₂ ≃ β₃) :
  arrow_congr' (e₁.trans e₂) (e₁'.trans e₂') = (arrow_congr' e₁ e₁').trans (arrow_congr' e₂ e₂') :=
rfl

@[simp] lemma arrow_congr'_symm {α₁ β₁ α₂ β₂ : Type*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
  (arrow_congr' e₁ e₂).symm = arrow_congr' e₁.symm e₂.symm :=
rfl

/-- Conjugate a map `f : α → α` by an equivalence `α ≃ β`. -/
def conj (e : α ≃ β) : (α → α) ≃ (β → β) := arrow_congr e e

@[simp] lemma conj_apply (e : α ≃ β) (f : α → α) (x : β) :
  e.conj f x = (e $ f $ e.symm x) :=
rfl

@[simp] lemma conj_refl : conj (equiv.refl α) = equiv.refl (α → α) := rfl

@[simp] lemma conj_symm (e : α ≃ β) : e.conj.symm = e.symm.conj := rfl

@[simp] lemma conj_trans (e₁ : α ≃ β) (e₂ : β ≃ γ) :
  (e₁.trans e₂).conj = e₁.conj.trans e₂.conj :=
rfl

-- This should not be a simp lemma as long as `(∘)` is reducible:
-- when `(∘)` is reducible, Lean can unify `f₁ ∘ f₂` with any `g` using
-- `f₁ := g` and `f₂ := λ x, x`.  This causes nontermination.
lemma conj_comp (e : α ≃ β) (f₁ f₂ : α → α) :
  e.conj (f₁ ∘ f₂) = (e.conj f₁) ∘ (e.conj f₂) :=
by apply arrow_congr_comp

/-- `punit` sorts in any two universes are equivalent. -/
def punit_equiv_punit : punit.{v} ≃ punit.{w} :=
⟨λ _, punit.star, λ _, punit.star, λ u, by { cases u, refl }, λ u, by { cases u, reflexivity }⟩

section
/-- The sort of maps to `punit.{v}` is equivalent to `punit.{w}`. -/
def arrow_punit_equiv_punit (α : Sort*) : (α → punit.{v}) ≃ punit.{w} :=
⟨λ f, punit.star, λ u f, punit.star,
  λ f, by { funext x, cases f x, refl }, λ u, by { cases u, reflexivity }⟩

/-- The sort of maps from `punit` is equivalent to the codomain. -/
def punit_arrow_equiv (α : Sort*) : (punit.{u} → α) ≃ α :=
⟨λ f, f punit.star, λ a u, a, λ f, by { ext ⟨⟩, refl }, λ u, rfl⟩

/-- The sort of maps from `empty` is equivalent to `punit`. -/
def empty_arrow_equiv_punit (α : Sort*) : (empty → α) ≃ punit.{u} :=
⟨λ f, punit.star, λ u e, e.rec _, λ f, funext $ λ x, x.rec _, λ u, by { cases u, refl }⟩

/-- The sort of maps from `pempty` is equivalent to `punit`. -/
def pempty_arrow_equiv_punit (α : Sort*) : (pempty → α) ≃ punit.{u} :=
⟨λ f, punit.star, λ u e, e.rec _, λ f, funext $ λ x, x.rec _, λ u, by { cases u, refl }⟩

/-- The sort of maps from `false` is equivalent to `punit`. -/
def false_arrow_equiv_punit (α : Sort*) : (false → α) ≃ punit.{u} :=
calc (false → α) ≃ (empty → α) : arrow_congr false_equiv_empty (equiv.refl _)
             ... ≃ punit       : empty_arrow_equiv_punit _

end

/-- Product of two equivalences. If `α₁ ≃ α₂` and `β₁ ≃ β₂`, then `α₁ × β₁ ≃ α₂ × β₂`. -/
@[congr] def prod_congr {α₁ β₁ α₂ β₂ : Type*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) : α₁ × β₁ ≃ α₂ × β₂ :=
⟨prod.map e₁ e₂, prod.map e₁.symm e₂.symm, λ ⟨a, b⟩, by simp, λ ⟨a, b⟩, by simp⟩

@[simp] theorem coe_prod_congr {α₁ β₁ α₂ β₂ : Type*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
  ⇑(prod_congr e₁ e₂) = prod.map e₁ e₂ :=
rfl

@[simp] theorem prod_congr_symm {α₁ β₁ α₂ β₂ : Type*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
  (prod_congr e₁ e₂).symm = prod_congr e₁.symm e₂.symm :=
rfl

/-- Type product is commutative up to an equivalence: `α × β ≃ β × α`. -/
def prod_comm (α β : Type*) : α × β ≃ β × α :=
⟨prod.swap, prod.swap, λ⟨a, b⟩, rfl, λ⟨a, b⟩, rfl⟩

@[simp] lemma coe_prod_comm (α β) : ⇑(prod_comm α β)= prod.swap := rfl

@[simp] lemma prod_comm_symm (α β) : (prod_comm α β).symm = prod_comm β α := rfl

/-- Type product is associative up to an equivalence. -/
def prod_assoc (α β γ : Sort*) : (α × β) × γ ≃ α × (β × γ) :=
⟨λ p, ⟨p.1.1, ⟨p.1.2, p.2⟩⟩, λp, ⟨⟨p.1, p.2.1⟩, p.2.2⟩, λ ⟨⟨a, b⟩, c⟩, rfl, λ ⟨a, ⟨b, c⟩⟩, rfl⟩

@[simp] theorem prod_assoc_apply {α β γ : Sort*} (p : (α × β) × γ) :
  prod_assoc α β γ p = ⟨p.1.1, ⟨p.1.2, p.2⟩⟩ := rfl

@[simp] theorem prod_assoc_sym_apply {α β γ : Sort*} (p : α × (β × γ)) :
  (prod_assoc α β γ).symm p = ⟨⟨p.1, p.2.1⟩, p.2.2⟩ := rfl

section
/-- `punit` is a right identity for type product up to an equivalence. -/
def prod_punit (α : Type*) : α × punit.{u+1} ≃ α :=
⟨λ p, p.1, λ a, (a, punit.star), λ ⟨_, punit.star⟩, rfl, λ a, rfl⟩

@[simp] theorem prod_punit_apply {α : Sort*} (a : α × punit.{u+1}) : prod_punit α a = a.1 := rfl

/-- `punit` is a left identity for type product up to an equivalence. -/
def punit_prod (α : Type*) : punit.{u+1} × α ≃ α :=
calc punit × α ≃ α × punit : prod_comm _ _
           ... ≃ α         : prod_punit _

@[simp] theorem punit_prod_apply {α : Type*} (a : punit.{u+1} × α) : punit_prod α a = a.2 := rfl

/-- `empty` type is a right absorbing element for type product up to an equivalence. -/
def prod_empty (α : Type*) : α × empty ≃ empty :=
equiv_empty (λ ⟨_, e⟩, e.rec _)

/-- `empty` type is a left absorbing element for type product up to an equivalence. -/
def empty_prod (α : Type*) : empty × α ≃ empty :=
equiv_empty (λ ⟨e, _⟩, e.rec _)

/-- `pempty` type is a right absorbing element for type product up to an equivalence. -/
def prod_pempty (α : Type*) : α × pempty ≃ pempty :=
equiv_pempty (λ ⟨_, e⟩, e.rec _)

/-- `pempty` type is a left absorbing element for type product up to an equivalence. -/
def pempty_prod (α : Type*) : pempty × α ≃ pempty :=
equiv_pempty (λ ⟨e, _⟩, e.rec _)
end

section
open sum
/-- `psum` is equivalent to `sum`. -/
def psum_equiv_sum (α β : Type*) : psum α β ≃ α ⊕ β :=
⟨λ s, psum.cases_on s inl inr,
 λ s, sum.cases_on s psum.inl psum.inr,
 λ s, by cases s; refl,
 λ s, by cases s; refl⟩

/-- If `α ≃ α'` and `β ≃ β'`, then `α ⊕ β ≃ α' ⊕ β'`. -/
def sum_congr {α₁ β₁ α₂ β₂ : Type*} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) : α₁ ⊕ β₁ ≃ α₂ ⊕ β₂ :=
⟨sum.map ea eb, sum.map ea.symm eb.symm, λ x, by simp, λ x, by simp⟩

@[simp] theorem sum_congr_apply {α₁ β₁ α₂ β₂ : Type*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) (a : α₁ ⊕ β₁) :
  sum_congr e₁ e₂ a = a.map e₁ e₂ :=
rfl

@[simp] lemma sum_congr_symm {α β γ δ : Type u} (e : α ≃ β) (f : γ ≃ δ) :
  (equiv.sum_congr e f).symm = (equiv.sum_congr (e.symm) (f.symm)) :=
rfl

/-- `bool` is equivalent the sum of two `punit`s. -/
def bool_equiv_punit_sum_punit : bool ≃ punit.{u+1} ⊕ punit.{v+1} :=
⟨λ b, cond b (inr punit.star) (inl punit.star),
 λ s, sum.rec_on s (λ_, ff) (λ_, tt),
 λ b, by cases b; refl,
 λ s, by rcases s with ⟨⟨⟩⟩ | ⟨⟨⟩⟩; refl⟩

/-- `Prop` is noncomputably equivalent to `bool`. -/
noncomputable def Prop_equiv_bool : Prop ≃ bool :=
⟨λ p, @to_bool p (classical.prop_decidable _),
 λ b, b, λ p, by simp, λ b, by simp⟩

/-- Sum of types is commutative up to an equivalence. -/
def sum_comm (α β : Sort*) : α ⊕ β ≃ β ⊕ α :=
⟨sum.swap, sum.swap, sum.swap_swap, sum.swap_swap⟩

@[simp] lemma sum_comm_apply (α β) (a) : sum_comm α β a = a.swap := rfl
@[simp] lemma sum_comm_symm (α β) : (sum_comm α β).symm = sum_comm β α := rfl

/-- Sum of types is associative up to an equivalence. -/
def sum_assoc (α β γ : Sort*) : (α ⊕ β) ⊕ γ ≃ α ⊕ (β ⊕ γ) :=
⟨sum.elim (sum.elim sum.inl (sum.inr ∘ sum.inl)) (sum.inr ∘ sum.inr),
  sum.elim (sum.inl ∘ sum.inl) $ sum.elim (sum.inl ∘ sum.inr) sum.inr,
  by rintros (⟨_ | _⟩ | _); refl,
  by rintros (_ | ⟨_ | _⟩); refl⟩

@[simp] theorem sum_assoc_apply_in1 {α β γ} (a) : sum_assoc α β γ (inl (inl a)) = inl a := rfl
@[simp] theorem sum_assoc_apply_in2 {α β γ} (b) : sum_assoc α β γ (inl (inr b)) = inr (inl b) := rfl
@[simp] theorem sum_assoc_apply_in3 {α β γ} (c) : sum_assoc α β γ (inr c) = inr (inr c) := rfl

/-- Sum with `empty` is equivalent to the original type. -/
def sum_empty (α : Type*) : α ⊕ empty ≃ α :=
⟨sum.elim id (empty.rec _),
 inl,
 λ s, by { rcases s with _ | ⟨⟨⟩⟩, refl },
 λ a, rfl⟩

@[simp] lemma sum_empty_apply_inl {α} (a) : sum_empty α (sum.inl a) = a := rfl

/-- The sum of `empty` with any `Sort*` is equivalent to the right summand. -/
def empty_sum (α : Sort*) : empty ⊕ α ≃ α :=
(sum_comm _ _).trans $ sum_empty _

@[simp] lemma empty_sum_apply_inr {α} (a) : empty_sum α (sum.inr a) = a := rfl

/-- Sum with `pempty` is equivalent to the original type. -/
def sum_pempty (α : Type*) : α ⊕ pempty ≃ α :=
⟨sum.elim id (pempty.rec _),
 inl,
 λ s, by { rcases s with _ | ⟨⟨⟩⟩, refl },
 λ a, rfl⟩

@[simp] lemma sum_pempty_apply_inl {α} (a) : sum_pempty α (sum.inl a) = a := rfl

/-- The sum of `pempty` with any `Sort*` is equivalent to the right summand. -/
def pempty_sum (α : Sort*) : pempty ⊕ α ≃ α :=
(sum_comm _ _).trans $ sum_pempty _

@[simp] lemma pempty_sum_apply_inr {α} (a) : pempty_sum α (sum.inr a) = a := rfl

/-- `option α` is equivalent to `α ⊕ punit` -/
def option_equiv_sum_punit (α : Sort*) : option α ≃ α ⊕ punit.{u+1} :=
⟨λ o, match o with none := inr punit.star | some a := inl a end,
 λ s, match s with inr _ := none | inl a := some a end,
 λ o, by cases o; refl,
 λ s, by rcases s with _ | ⟨⟨⟩⟩; refl⟩

@[simp] lemma option_equiv_sum_punit_none {α} : option_equiv_sum_punit α none = sum.inr () := rfl
@[simp] lemma option_equiv_sum_punit_some {α} (a) :
  option_equiv_sum_punit α (some a) = sum.inl a := rfl

/-- The set of `x : option α` such that `is_some x` is equivalent to `α`. -/
def option_is_some_equiv (α : Type*) : {x : option α // x.is_some} ≃ α :=
{ to_fun := λ o, option.get o.2,
  inv_fun := λ x, ⟨some x, dec_trivial⟩,
  left_inv := λ o, subtype.eq $ option.some_get _,
  right_inv := λ x, option.get_some _ _ }

/-- `α ⊕ β` is equivalent to a `sigma`-type over `bool`. -/
def sum_equiv_sigma_bool (α β : Sort*) : α ⊕ β ≃ (Σ b: bool, cond b α β) :=
⟨λ s, match s with inl a := ⟨tt, a⟩ | inr b := ⟨ff, b⟩ end,
 λ s, match s with ⟨tt, a⟩ := inl a | ⟨ff, b⟩ := inr b end,
 λ s, by cases s; refl,
 λ s, by rcases s with ⟨_|_, _⟩; refl⟩

/-- `sigma_preimage_equiv f` for `f : α → β` is the natural equivalence between
the type of all fibres of `f` and the total space `α`. -/
def sigma_preimage_equiv {α β : Type*} (f : α → β) :
  (Σ y : β, {x // f x = y}) ≃ α :=
⟨λ x, x.2.1, λ x, ⟨f x, x, rfl⟩, λ ⟨y, x, rfl⟩, rfl, λ x, rfl⟩

@[simp] lemma sigma_preimage_equiv_apply {α β : Type*} (f : α → β)
  (x : Σ y : β, {x // f x = y}) :
  (sigma_preimage_equiv f) x = x.2.1 := rfl

@[simp] lemma sigma_preimage_equiv_symm_apply_fst {α β : Type*} (f : α → β) (a : α) :
  ((sigma_preimage_equiv f).symm a).1 = f a := rfl

@[simp] lemma sigma_preimage_equiv_symm_apply_snd_fst {α β : Type*} (f : α → β) (a : α) :
  ((sigma_preimage_equiv f).symm a).2.1 = a := rfl

end

section sum_compl

/-- For any predicate `p` on `α`,
the sum of the two subtypes `{a // p a}` and its complement `{a // ¬ p a}`
is naturally equivalent to `α`. -/
def sum_compl {α : Type*} (p : α → Prop) [decidable_pred p] :
  {a // p a} ⊕ {a // ¬ p a} ≃ α :=
{ to_fun := sum.elim coe coe,
  inv_fun := λ a, if h : p a then sum.inl ⟨a, h⟩ else sum.inr ⟨a, h⟩,
  left_inv := by { rintros (⟨x,hx⟩|⟨x,hx⟩); dsimp; [rw dif_pos, rw dif_neg], },
  right_inv := λ a, by { dsimp, split_ifs; refl } }

@[simp] lemma sum_compl_apply_inl {α : Type*} (p : α → Prop) [decidable_pred p]
  (x : {a // p a}) :
  sum_compl p (sum.inl x) = x := rfl

@[simp] lemma sum_compl_apply_inr {α : Type*} (p : α → Prop) [decidable_pred p]
  (x : {a // ¬ p a}) :
  sum_compl p (sum.inr x) = x := rfl

@[simp] lemma sum_compl_apply_symm_of_pos {α : Type*} (p : α → Prop) [decidable_pred p]
  (a : α) (h : p a) :
  (sum_compl p).symm a = sum.inl ⟨a, h⟩ := dif_pos h

@[simp] lemma sum_compl_apply_symm_of_neg {α : Type*} (p : α → Prop) [decidable_pred p]
  (a : α) (h : ¬ p a) :
  (sum_compl p).symm a = sum.inr ⟨a, h⟩ := dif_neg h

end sum_compl

section subtype_preimage

variables (p : α → Prop) [decidable_pred p] (x₀ : {a // p a} → β)

/-- For a fixed function `x₀ : {a // p a} → β` defined on a subtype of `α`,
the subtype of functions `x : α → β` that agree with `x₀` on the subtype `{a // p a}`
is naturally equivalent to the type of functions `{a // ¬ p a} → β`. -/
def subtype_preimage :
  {x : α → β // x ∘ coe = x₀} ≃ ({a // ¬ p a} → β) :=
{ to_fun := λ (x : {x : α → β // x ∘ coe = x₀}) a, (x : α → β) a,
  inv_fun := λ x, ⟨λ a, if h : p a then x₀ ⟨a, h⟩ else x ⟨a, h⟩,
    funext $ λ ⟨a, h⟩, dif_pos h⟩,
  left_inv := λ ⟨x, hx⟩, subtype.val_injective $ funext $ λ a,
    (by { dsimp, split_ifs; [ rw ← hx, skip ]; refl }),
  right_inv := λ x, funext $ λ ⟨a, h⟩,
    show dite (p a) _ _ = _, by { dsimp, rw [dif_neg h] } }

@[simp] lemma subtype_preimage_apply (x : {x : α → β // x ∘ coe = x₀}) :
  subtype_preimage p x₀ x = λ a, (x : α → β) a := rfl

@[simp] lemma subtype_preimage_symm_apply_coe (x : {a // ¬ p a} → β) :
  ((subtype_preimage p x₀).symm x : α → β) =
    λ a, if h : p a then x₀ ⟨a, h⟩ else x ⟨a, h⟩ := rfl

lemma subtype_preimage_symm_apply_coe_pos (x : {a // ¬ p a} → β) (a : α) (h : p a) :
  ((subtype_preimage p x₀).symm x : α → β) a = x₀ ⟨a, h⟩ :=
dif_pos h

lemma subtype_preimage_symm_apply_coe_neg (x : {a // ¬ p a} → β) (a : α) (h : ¬ p a) :
  ((subtype_preimage p x₀).symm x : α → β) a = x ⟨a, h⟩ :=
dif_neg h

end subtype_preimage

section fun_unique

variables (α β) [unique α]

/-- If `α` has a unique term, then the type of function `α → β` is equivalent to `β`. -/
def fun_unique : (α → β) ≃ β :=
{ to_fun := λ f, f (default α),
  inv_fun := λ b a, b,
  left_inv := λ f, funext $ λ a, congr_arg f $ subsingleton.elim _ _,
  right_inv := λ b, rfl }

variables {α β}

@[simp] lemma fun_unique_apply (f : α → β) :
  fun_unique α β f = f (default α) := rfl

@[simp] lemma fun_unique_symm_apply (b : β) (a : α) :
  (fun_unique α β).symm b a = b := rfl

end fun_unique

section

/-- A family of equivalences `Π a, β₁ a ≃ β₂ a` generates an equivalence between `Π a, β₁ a` and
`Π a, β₂ a`. -/
def Pi_congr_right {α} {β₁ β₂ : α → Sort*} (F : Π a, β₁ a ≃ β₂ a) : (Π a, β₁ a) ≃ (Π a, β₂ a) :=
⟨λ H a, F a (H a), λ H a, (F a).symm (H a),
 λ H, funext $ by simp, λ H, funext $ by simp⟩

/-- Dependent `curry` equivalence: the type of dependent functions on `Σ i, β i` is equivalent
to the type of dependent functions of two arguments (i.e., functions to the space of functions). -/
def Pi_curry {α} {β : α → Sort*} (γ : Π a, β a → Sort*) :
  (Π x : Σ i, β i, γ x.1 x.2) ≃ (Π a b, γ a b) :=
{ to_fun := λ f x y, f ⟨x,y⟩,
  inv_fun := λ f x, f x.1 x.2,
  left_inv := λ f, funext $ λ ⟨x,y⟩, rfl,
  right_inv := λ f, funext $ λ x, funext $ λ y, rfl }

end

section
/-- A `psigma`-type is equivalent to the corresponding `sigma`-type. -/
def psigma_equiv_sigma {α} (β : α → Sort*) : (Σ' i, β i) ≃ Σ i, β i :=
⟨λ ⟨a, b⟩, ⟨a, b⟩, λ ⟨a, b⟩, ⟨a, b⟩, λ ⟨a, b⟩, rfl, λ ⟨a, b⟩, rfl⟩

/-- A family of equivalences `Π a, β₁ a ≃ β₂ a` generates an equivalence between `Σ a, β₁ a` and
`Σ a, β₂ a`. -/
def sigma_congr_right {α} {β₁ β₂ : α → Sort*} (F : Π a, β₁ a ≃ β₂ a) : (Σ a, β₁ a) ≃ Σ a, β₂ a :=
⟨λ ⟨a, b⟩, ⟨a, F a b⟩, λ ⟨a, b⟩, ⟨a, (F a).symm b⟩,
 λ ⟨a, b⟩, congr_arg (sigma.mk a) $ symm_apply_apply (F a) b,
 λ ⟨a, b⟩, congr_arg (sigma.mk a) $ apply_symm_apply (F a) b⟩

/-- An equivalence `f : α₁ ≃ α₂` generates an equivalence between `Σ a, β (f a)` and `Σ a, β a`. -/
def sigma_congr_left {α₁ α₂} {β : α₂ → Sort*} : ∀ f : α₁ ≃ α₂, (Σ a:α₁, β (f a)) ≃ (Σ a:α₂, β a)
| ⟨f, g, l, r⟩ :=
  ⟨λ ⟨a, b⟩, ⟨f a, b⟩, λ ⟨a, b⟩, ⟨g a, @@eq.rec β b (r a).symm⟩,
   λ ⟨a, b⟩, match g (f a), l a : ∀ a' (h : a' = a),
       @sigma.mk _ (β ∘ f) _ (@@eq.rec β b (congr_arg f h.symm)) = ⟨a, b⟩ with
     | _, rfl := rfl end,
   λ ⟨a, b⟩, match f (g a), _ : ∀ a' (h : a' = a), sigma.mk a' (@@eq.rec β b h.symm) = ⟨a, b⟩ with
     | _, rfl := rfl end⟩

/-- Transporting a sigma type through an equivalence of the base -/
def sigma_congr_left' {α₁ α₂} {β : α₁ → Sort*} (f : α₁ ≃ α₂) :
  (Σ a:α₁, β a) ≃ (Σ a:α₂, β (f.symm a)) :=
(sigma_congr_left f.symm).symm

/-- Transporting a sigma type through an equivalence of the base and a family of equivalences
of matching fibers -/
def sigma_congr {α₁ α₂} {β₁ : α₁ → Sort*} {β₂ : α₂ → Sort*} (f : α₁ ≃ α₂)
  (F : ∀ a, β₁ a ≃ β₂ (f a)) :
  sigma β₁ ≃ sigma β₂ :=
(sigma_congr_right F).trans (sigma_congr_left f)

/-- `sigma` type with a constant fiber is equivalent to the product. -/
def sigma_equiv_prod (α β : Sort*) : (Σ_:α, β) ≃ α × β :=
⟨λ ⟨a, b⟩, ⟨a, b⟩, λ ⟨a, b⟩, ⟨a, b⟩, λ ⟨a, b⟩, rfl, λ ⟨a, b⟩, rfl⟩

/-- If each fiber of a `sigma` type is equivalent to a fixed type, then the sigma type
is equivalent to the product. -/
def sigma_equiv_prod_of_equiv {α β} {β₁ : α → Sort*} (F : ∀ a, β₁ a ≃ β) : sigma β₁ ≃ α × β :=
(sigma_congr_right F).trans (sigma_equiv_prod α β)

end

section
/-- The type of functions to a product `α × β` is equivalent to the type of pairs of functions
`γ → α` and `γ → β`. -/
def arrow_prod_equiv_prod_arrow (α β γ : Type*) : (γ → α × β) ≃ (γ → α) × (γ → β) :=
⟨λ f, (λ c, (f c).1, λ c, (f c).2),
 λ p c, (p.1 c, p.2 c),
 λ f, funext $ λ c, prod.mk.eta,
 λ p, by { cases p, refl }⟩

/-- Functions `α → β → γ` are equivalent to functions on `α × β`. -/
def arrow_arrow_equiv_prod_arrow (α β γ : Sort*) : (α → β → γ) ≃ (α × β → γ) :=
⟨uncurry, curry, curry_uncurry, uncurry_curry⟩

open sum
/-- The type of functions on a sum type `α ⊕ β` is equivalent to the type of pairs of functions
on `α` and on `β`. -/
def sum_arrow_equiv_prod_arrow (α β γ : Type*) : ((α ⊕ β) → γ) ≃ (α → γ) × (β → γ) :=
⟨λ f, (f ∘ inl, f ∘ inr),
 λ p, sum.elim p.1 p.2,
 λ f, by { ext ⟨⟩; refl },
 λ p, by { cases p, refl }⟩

/-- Type product is right distributive with respect to type sum up to an equivalence. -/
def sum_prod_distrib (α β γ : Sort*) : (α ⊕ β) × γ ≃ (α × γ) ⊕ (β × γ) :=
⟨λ p, match p with (inl a, c) := inl (a, c) | (inr b, c) := inr (b, c) end,
 λ s, match s with inl q := (inl q.1, q.2) | inr q := (inr q.1, q.2) end,
 λ p, by rcases p with ⟨_ | _, _⟩; refl,
 λ s, by rcases s with ⟨_, _⟩ | ⟨_, _⟩; refl⟩

@[simp] theorem sum_prod_distrib_apply_left {α β γ} (a : α) (c : γ) :
   sum_prod_distrib α β γ (sum.inl a, c) = sum.inl (a, c) := rfl
@[simp] theorem sum_prod_distrib_apply_right {α β γ} (b : β) (c : γ) :
   sum_prod_distrib α β γ (sum.inr b, c) = sum.inr (b, c) := rfl

/-- Type product is left distributive with respect to type sum up to an equivalence. -/
def prod_sum_distrib (α β γ : Sort*) : α × (β ⊕ γ) ≃ (α × β) ⊕ (α × γ) :=
calc α × (β ⊕ γ) ≃ (β ⊕ γ) × α       : prod_comm _ _
            ...   ≃ (β × α) ⊕ (γ × α) : sum_prod_distrib _ _ _
            ...   ≃ (α × β) ⊕ (α × γ) : sum_congr (prod_comm _ _) (prod_comm _ _)

@[simp] theorem prod_sum_distrib_apply_left {α β γ} (a : α) (b : β) :
   prod_sum_distrib α β γ (a, sum.inl b) = sum.inl (a, b) := rfl
@[simp] theorem prod_sum_distrib_apply_right {α β γ} (a : α) (c : γ) :
   prod_sum_distrib α β γ (a, sum.inr c) = sum.inr (a, c) := rfl

/-- The product of an indexed sum of types (formally, a `sigma`-type `Σ i, α i`) by a type `β` is
equivalent to the sum of products `Σ i, (α i × β)`. -/
def sigma_prod_distrib {ι : Type*} (α : ι → Type*) (β : Type*) :
  ((Σ i, α i) × β) ≃ (Σ i, (α i × β)) :=
⟨λ p, ⟨p.1.1, (p.1.2, p.2)⟩,
 λ p, (⟨p.1, p.2.1⟩, p.2.2),
 λ p, by { rcases p with ⟨⟨_, _⟩, _⟩, refl },
 λ p, by { rcases p with ⟨_, ⟨_, _⟩⟩, refl }⟩

/-- The product `bool × α` is equivalent to `α ⊕ α`. -/
def bool_prod_equiv_sum (α : Type u) : bool × α ≃ α ⊕ α :=
calc bool × α ≃ (unit ⊕ unit) × α       : prod_congr bool_equiv_punit_sum_punit (equiv.refl _)
      ...     ≃ (unit × α) ⊕ (unit × α) : sum_prod_distrib _ _ _
      ...     ≃ α ⊕ α                   : sum_congr (punit_prod _) (punit_prod _)
end

section
open sum nat
/-- The set of natural numbers is equivalent to `ℕ ⊕ punit`. -/
def nat_equiv_nat_sum_punit : ℕ ≃ ℕ ⊕ punit.{u+1} :=
⟨λ n, match n with zero := inr punit.star | succ a := inl a end,
 λ s, match s with inl n := succ n | inr punit.star := zero end,
 λ n, begin cases n, repeat { refl } end,
 λ s, begin cases s with a u, { refl }, {cases u, { refl }} end⟩

/-- `ℕ ⊕ punit` is equivalent to `ℕ`. -/
def nat_sum_punit_equiv_nat : ℕ ⊕ punit.{u+1} ≃ ℕ :=
nat_equiv_nat_sum_punit.symm

/-- The type of integer numbers is equivalent to `ℕ ⊕ ℕ`. -/
def int_equiv_nat_sum_nat : ℤ ≃ ℕ ⊕ ℕ :=
by refine ⟨_, _, _, _⟩; intro z; {cases z; [left, right]; assumption} <|> {cases z; refl}

end

/-- An equivalence between `α` and `β` generates an equivalence between `list α` and `list β`. -/
def list_equiv_of_equiv {α β : Type*} (e : α ≃ β) : list α ≃ list β :=
{ to_fun := list.map e,
  inv_fun := list.map e.symm,
  left_inv := λ l, by rw [list.map_map, e.symm_comp_self, list.map_id],
  right_inv := λ l, by rw [list.map_map, e.self_comp_symm, list.map_id] }

/-- `fin n` is equivalent to `{m // m < n}`. -/
def fin_equiv_subtype (n : ℕ) : fin n ≃ {m // m < n} :=
⟨λ x, ⟨x.1, x.2⟩, λ x, ⟨x.1, x.2⟩, λ ⟨a, b⟩, rfl,λ ⟨a, b⟩, rfl⟩

/-- If `α` is equivalent to `β`, then `unique α` is equivalent to `β`. -/
def unique_congr (e : α ≃ β) : unique α ≃ unique β :=
{ to_fun := λ h, @equiv.unique _ _ h e.symm,
  inv_fun := λ h, @equiv.unique _ _ h e,
  left_inv := λ _, subsingleton.elim _ _,
  right_inv := λ _, subsingleton.elim _ _ }

section
open subtype

/-- If `α` is equivalent to `β` and the predicates `p : α → Prop` and `q : β → Prop` are equivalent
at corresponding points, then `{a // p a}` is equivalent to `{b // q b}`. -/
def subtype_congr {p : α → Prop} {q : β → Prop}
  (e : α ≃ β) (h : ∀ a, p a ↔ q (e a)) : {a : α // p a} ≃ {b : β // q b} :=
⟨λ x, ⟨e x.1, (h _).1 x.2⟩,
 λ y, ⟨e.symm y.1, (h _).2 (by { simp, exact y.2 })⟩,
 λ ⟨x, h⟩, subtype.ext_val $ by simp,
 λ ⟨y, h⟩, subtype.ext_val $ by simp⟩

/-- If two predicates `p` and `q` are pointwise equivalent, then `{x // p x}` is equivalent to
`{x // q x}`. -/
def subtype_congr_right {p q : α → Prop} (e : ∀x, p x ↔ q x) : {x // p x} ≃ {x // q x} :=
subtype_congr (equiv.refl _) e

@[simp] lemma subtype_congr_right_mk {p q : α → Prop} (e : ∀x, p x ↔ q x)
  {x : α} (h : p x) : subtype_congr_right e ⟨x, h⟩ = ⟨x, (e x).1 h⟩ := rfl

/-- If `α ≃ β`, then for any predicate `p : β → Prop` the subtype `{a // p (e a)}` is equivalent
to the subtype `{b // p b}`. -/
def subtype_equiv_of_subtype {p : β → Prop} (e : α ≃ β) :
  {a : α // p (e a)} ≃ {b : β // p b} :=
subtype_congr e $ by simp

/-- If `α ≃ β`, then for any predicate `p : α → Prop` the subtype `{a // p a}` is equivalent
to the subtype `{b // p (e.symm b)}`. This version is used by `equiv_rw`. -/
def subtype_equiv_of_subtype' {p : α → Prop} (e : α ≃ β) :
  {a : α // p a} ≃ {b : β // p (e.symm b)} :=
e.symm.subtype_equiv_of_subtype.symm

/-- If two predicates are equal, then the corresponding subtypes are equivalent. -/
def subtype_congr_prop {α : Type*} {p q : α → Prop} (h : p = q) : subtype p ≃ subtype q :=
subtype_congr (equiv.refl α) (assume a, h ▸ iff.rfl)

/-- The subtypes corresponding to equal sets are equivalent. -/
def set_congr {α : Type*} {s t : set α} (h : s = t) : s ≃ t :=
subtype_congr_prop h

/-- A subtype of a subtype is equivalent to the subtype of elements satisfying both predicates. This
version allows the “inner” predicate to depend on `h : p a`. -/
def subtype_subtype_equiv_subtype_exists {α : Type u} (p : α → Prop) (q : subtype p → Prop) :
  subtype q ≃ {a : α // ∃h:p a, q ⟨a, h⟩ } :=
⟨λ⟨⟨a, ha⟩, ha'⟩, ⟨a, ha, ha'⟩,
  λ⟨a, ha⟩, ⟨⟨a, ha.cases_on $ assume h _, h⟩, by { cases ha, exact ha_h }⟩,
  assume ⟨⟨a, ha⟩, h⟩, rfl, assume ⟨a, h₁, h₂⟩, rfl⟩

/-- A subtype of a subtype is equivalent to the subtype of elements satisfying both predicates. -/
def subtype_subtype_equiv_subtype_inter {α : Type u} (p q : α → Prop) :
  {x : subtype p // q x.1} ≃ subtype (λ x, p x ∧ q x) :=
(subtype_subtype_equiv_subtype_exists p _).trans $
subtype_congr_right $ λ x, exists_prop

/-- If the outer subtype has more restrictive predicate than the inner one,
then we can drop the latter. -/
def subtype_subtype_equiv_subtype {α : Type u} {p q : α → Prop} (h : ∀ {x}, q x → p x) :
  {x : subtype p // q x.1} ≃ subtype q :=
(subtype_subtype_equiv_subtype_inter p _).trans $
subtype_congr_right $
assume x,
⟨and.right, λ h₁, ⟨h h₁, h₁⟩⟩

/-- If a proposition holds for all elements, then the subtype is
equivalent to the original type. -/
def subtype_univ_equiv {α : Type u} {p : α → Prop} (h : ∀ x, p x) :
  subtype p ≃ α :=
⟨λ x, x, λ x, ⟨x, h x⟩, λ x, subtype.eq rfl, λ x, rfl⟩

/-- A subtype of a sigma-type is a sigma-type over a subtype. -/
def subtype_sigma_equiv {α : Type u} (p : α → Type v) (q : α → Prop) :
  { y : sigma p // q y.1 } ≃ Σ(x : subtype q), p x.1 :=
⟨λ x, ⟨⟨x.1.1, x.2⟩, x.1.2⟩,
 λ x, ⟨⟨x.1.1, x.2⟩, x.1.2⟩,
 λ ⟨⟨x, h⟩, y⟩, rfl,
 λ ⟨⟨x, y⟩, h⟩, rfl⟩

/-- A sigma type over a subtype is equivalent to the sigma set over the original type,
if the fiber is empty outside of the subset -/
def sigma_subtype_equiv_of_subset {α : Type u} (p : α → Type v) (q : α → Prop)
  (h : ∀ x, p x → q x) :
  (Σ x : subtype q, p x) ≃ Σ x : α, p x :=
(subtype_sigma_equiv p q).symm.trans $ subtype_univ_equiv $ λ x, h x.1 x.2

/-- If a predicate `p : β → Prop` is true on the range of a map `f : α → β`, then
`Σ y : {y // p y}, {x // f x = y}` is equivalent to `α`. -/
def sigma_subtype_preimage_equiv {α : Type u} {β : Type v} (f : α → β) (p : β → Prop)
  (h : ∀ x, p (f x)) :
  (Σ y : subtype p, {x : α // f x = y}) ≃ α :=
calc _ ≃ Σ y : β, {x : α // f x = y} : sigma_subtype_equiv_of_subset _ p (λ y ⟨x, h'⟩, h' ▸ h x)
   ... ≃ α                           : sigma_preimage_equiv f

/-- If for each `x` we have `p x ↔ q (f x)`, then `Σ y : {y // q y}, f ⁻¹' {y}` is equivalent
to `{x // p x}`. -/
def sigma_subtype_preimage_equiv_subtype {α : Type u} {β : Type v} (f : α → β)
  {p : α → Prop} {q : β → Prop} (h : ∀ x, p x ↔ q (f x)) :
  (Σ y : subtype q, {x : α // f x = y}) ≃ subtype p :=
calc (Σ y : subtype q, {x : α // f x = y}) ≃
  Σ y : subtype q, {x : subtype p // subtype.mk (f x) ((h x).1 x.2) = y} :
  begin
    apply sigma_congr_right,
    assume y,
    symmetry,
    refine (subtype_subtype_equiv_subtype_exists _ _).trans (subtype_congr_right _),
    assume x,
    exact ⟨λ ⟨hp, h'⟩, congr_arg subtype.val h', λ h', ⟨(h x).2 (h'.symm ▸ y.2), subtype.eq h'⟩⟩
  end

   ... ≃ subtype p : sigma_preimage_equiv (λ x : subtype p, (⟨f x, (h x).1 x.property⟩ : subtype q))

/-- The `pi`-type `Π i, π i` is equivalent to the type of sections `f : ι → Σ i, π i` of the
`sigma` type such that for all `i` we have `(f i).fst = i`. -/
def pi_equiv_subtype_sigma (ι : Type*) (π : ι → Type*) :
  (Πi, π i) ≃ {f : ι → Σi, π i | ∀i, (f i).1 = i } :=
⟨ λf, ⟨λi, ⟨i, f i⟩, assume i, rfl⟩, λf i, begin rw ← f.2 i, exact (f.1 i).2 end,
  assume f, funext $ assume i, rfl,
  assume ⟨f, hf⟩, subtype.eq $ funext $ assume i, sigma.eq (hf i).symm $
    eq_of_heq $ rec_heq_of_heq _ $ rec_heq_of_heq _ $ heq.refl _⟩

/-- The set of functions `f : Π a, β a` such that for all `a` we have `p a (f a)` is equivalent
to the set of functions `Π a, {b : β a // p a b}`. -/
def subtype_pi_equiv_pi {α : Sort u} {β : α → Sort v} {p : Πa, β a → Prop} :
  {f : Πa, β a // ∀a, p a (f a) } ≃ Πa, { b : β a // p a b } :=
⟨λf a, ⟨f.1 a, f.2 a⟩, λf, ⟨λa, (f a).1, λa, (f a).2⟩,
  by { rintro ⟨f, h⟩, refl },
  by { rintro f, funext a, exact subtype.ext_val rfl }⟩

/-- A subtype of a product defined by componentwise conditions
is equivalent to a product of subtypes. -/
def subtype_prod_equiv_prod {α : Type u} {β : Type v} {p : α → Prop} {q : β → Prop} :
  {c : α × β // p c.1 ∧ q c.2} ≃ ({a // p a} × {b // q b}) :=
⟨λ x, ⟨⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩⟩,
 λ x, ⟨⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩⟩,
 λ ⟨⟨_, _⟩, ⟨_, _⟩⟩, rfl,
 λ ⟨⟨_, _⟩, ⟨_, _⟩⟩, rfl⟩

end

section subtype_equiv_codomain
variables {X : Type*} {Y : Type*} [decidable_eq X] {x : X}

/-- The type of all functions `X → Y` with prescribed values for all `x' ≠ x`
is equivalent to the codomain `Y`. -/
def subtype_equiv_codomain (f : {x' // x' ≠ x} → Y) : {g : X → Y // g ∘ coe = f} ≃ Y :=
(subtype_preimage _ f).trans $
@fun_unique {x' // ¬ x' ≠ x} _ $
show unique {x' // ¬ x' ≠ x}, from @equiv.unique _ _
  (show unique {x' // x' = x}, from
    { default := ⟨x, rfl⟩, uniq := λ ⟨x', h⟩, subtype.val_injective h })
  (subtype_congr_right $ λ a, not_not)

@[simp] lemma coe_subtype_equiv_codomain (f : {x' // x' ≠ x} → Y) :
  (subtype_equiv_codomain f : {g : X → Y // g ∘ coe = f} → Y) = λ g, (g : X → Y) x := rfl

@[simp] lemma subtype_equiv_codomain_apply (f : {x' // x' ≠ x} → Y)
  (g : {g : X → Y // g ∘ coe = f}) :
  subtype_equiv_codomain f g = (g : X → Y) x := rfl

lemma coe_subtype_equiv_codomain_symm (f : {x' // x' ≠ x} → Y) :
  ((subtype_equiv_codomain f).symm : Y → {g : X → Y // g ∘ coe = f}) =
  λ y, ⟨λ x', if h : x' ≠ x then f ⟨x', h⟩ else y,
    by { funext x', dsimp, erw [dif_pos x'.2, subtype.coe_eta] }⟩ := rfl

@[simp] lemma subtype_equiv_codomain_symm_apply (f : {x' // x' ≠ x} → Y) (y : Y) (x' : X) :
  ((subtype_equiv_codomain f).symm y : X → Y) x' = if h : x' ≠ x then f ⟨x', h⟩ else y :=
rfl

@[simp] lemma subtype_equiv_codomain_symm_apply_eq (f : {x' // x' ≠ x} → Y) (y : Y) :
  ((subtype_equiv_codomain f).symm y : X → Y) x = y :=
dif_neg (not_not.mpr rfl)

lemma subtype_equiv_codomain_symm_apply_ne (f : {x' // x' ≠ x} → Y) (y : Y) (x' : X) (h : x' ≠ x) :
  ((subtype_equiv_codomain f).symm y : X → Y) x' = f ⟨x', h⟩ :=
dif_pos h

end subtype_equiv_codomain

namespace set
open set

/-- `univ α` is equivalent to `α`. -/
protected def univ (α) : @univ α ≃ α :=
⟨subtype.val, λ a, ⟨a, trivial⟩, λ ⟨a, _⟩, rfl, λ a, rfl⟩

@[simp] lemma univ_apply {α : Type u} (x : @univ α) :
  equiv.set.univ α x = x := rfl

@[simp] lemma univ_symm_apply {α : Type u} (x : α) :
  (equiv.set.univ α).symm x = ⟨x, trivial⟩ := rfl

/-- An empty set is equivalent to the `empty` type. -/
protected def empty (α) : (∅ : set α) ≃ empty :=
equiv_empty $ λ ⟨x, h⟩, not_mem_empty x h

/-- An empty set is equivalent to a `pempty` type. -/
protected def pempty (α) : (∅ : set α) ≃ pempty :=
equiv_pempty $ λ ⟨x, h⟩, not_mem_empty x h

/-- If sets `s` and `t` are separated by a decidable predicate, then `s ∪ t` is equivalent to
`s ⊕ t`. -/
protected def union' {α} {s t : set α}
  (p : α → Prop) [decidable_pred p]
  (hs : ∀ x ∈ s, p x)
  (ht : ∀ x ∈ t, ¬ p x) : (s ∪ t : set α) ≃ s ⊕ t :=
{ to_fun := λ x, if hp : p x
    then sum.inl ⟨_, x.2.resolve_right (λ xt, ht _ xt hp)⟩
    else sum.inr ⟨_, x.2.resolve_left (λ xs, hp (hs _ xs))⟩,
  inv_fun := λ o, match o with
    | (sum.inl x) := ⟨x, or.inl x.2⟩
    | (sum.inr x) := ⟨x, or.inr x.2⟩
  end,
  left_inv := λ ⟨x, h'⟩, by by_cases p x; simp [union'._match_1, h]; congr,
  right_inv := λ o, begin
    rcases o with ⟨x, h⟩ | ⟨x, h⟩;
    dsimp [union'._match_1];
    [simp [hs _ h], simp [ht _ h]]
  end }

/-- If sets `s` and `t` are disjoint, then `s ∪ t` is equivalent to `s ⊕ t`. -/
protected def union {α} {s t : set α} [decidable_pred (λ x, x ∈ s)] (H : s ∩ t ⊆ ∅) :
  (s ∪ t : set α) ≃ s ⊕ t :=
set.union' (λ x, x ∈ s) (λ _, id) (λ x xt xs, H ⟨xs, xt⟩)

lemma union_apply_left {α} {s t : set α} [decidable_pred (λ x, x ∈ s)] (H : s ∩ t ⊆ ∅)
  {a : (s ∪ t : set α)} (ha : ↑a ∈ s) : equiv.set.union H a = sum.inl ⟨a, ha⟩ :=
dif_pos ha

lemma union_apply_right {α} {s t : set α} [decidable_pred (λ x, x ∈ s)] (H : s ∩ t ⊆ ∅)
  {a : (s ∪ t : set α)} (ha : ↑a ∈ t) : equiv.set.union H a = sum.inr ⟨a, ha⟩ :=
dif_neg $ λ h, H ⟨h, ha⟩

-- TODO: Any reason to use the same universe?
/-- A singleton set is equivalent to a `punit` type. -/
protected def singleton {α} (a : α) : ({a} : set α) ≃ punit.{u} :=
⟨λ _, punit.star, λ _, ⟨a, mem_singleton _⟩,
 λ ⟨x, h⟩, by { simp at h, subst x },
 λ ⟨⟩, rfl⟩

/-- Equal sets are equivalent. -/
protected def of_eq {α : Type u} {s t : set α} (h : s = t) : s ≃ t :=
{ to_fun := λ x, ⟨x.1, h ▸ x.2⟩,
  inv_fun := λ x, ⟨x.1, h.symm ▸ x.2⟩,
  left_inv := λ _, subtype.eq rfl,
  right_inv := λ _, subtype.eq rfl }

@[simp] lemma of_eq_apply {α : Type u} {s t : set α} (h : s = t) (a : s) :
  equiv.set.of_eq h a = ⟨a, h ▸ a.2⟩ := rfl

@[simp] lemma of_eq_symm_apply {α : Type u} {s t : set α} (h : s = t) (a : t) :
  (equiv.set.of_eq h).symm a = ⟨a, h.symm ▸ a.2⟩ := rfl

/-- If `a ∉ s`, then `insert a s` is equivalent to `s ⊕ punit`. -/
protected def insert {α} {s : set.{u} α} [decidable_pred s] {a : α} (H : a ∉ s) :
  (insert a s : set α) ≃ s ⊕ punit.{u+1} :=
calc (insert a s : set α) ≃ ↥(s ∪ {a}) : equiv.set.of_eq (by simp)
... ≃ s ⊕ ({a} : set α) : equiv.set.union (by finish [set.subset_def])
... ≃ s ⊕ punit.{u+1} : sum_congr (equiv.refl _) (equiv.set.singleton _)

/-- If `s : set α` is a set with decidable membership, then `s ⊕ sᶜ` is equivalent to `α`. -/
protected def sum_compl {α} (s : set α) [decidable_pred s] : s ⊕ (sᶜ : set α) ≃ α :=
calc s ⊕ (sᶜ : set α) ≃ ↥(s ∪ sᶜ) : (equiv.set.union (by simp [set.ext_iff])).symm
... ≃ @univ α : equiv.set.of_eq (by simp)
... ≃ α : equiv.set.univ _

@[simp] lemma sum_compl_apply_inl {α : Type u} (s : set α) [decidable_pred s] (x : s) :
  equiv.set.sum_compl s (sum.inl x) = x := rfl

@[simp] lemma sum_compl_apply_inr {α : Type u} (s : set α) [decidable_pred s] (x : sᶜ) :
  equiv.set.sum_compl s (sum.inr x) = x := rfl

lemma sum_compl_symm_apply_of_mem {α : Type u} {s : set α} [decidable_pred s] {x : α}
  (hx : x ∈ s) : (equiv.set.sum_compl s).symm x = sum.inl ⟨x, hx⟩ :=
have ↑(⟨x, or.inl hx⟩ : (s ∪ sᶜ : set α)) ∈ s, from hx,
by { rw [equiv.set.sum_compl], simpa using set.union_apply_left _ this }

lemma sum_compl_symm_apply_of_not_mem {α : Type u} {s : set α} [decidable_pred s] {x : α}
  (hx : x ∉ s) : (equiv.set.sum_compl s).symm x = sum.inr ⟨x, hx⟩ :=
have ↑(⟨x, or.inr hx⟩ : (s ∪ sᶜ : set α)) ∈ sᶜ, from hx,
by { rw [equiv.set.sum_compl], simpa using set.union_apply_right _ this }

/-- `sum_diff_subset s t` is the natural equivalence between
`s ⊕ (t \ s)` and `t`, where `s` and `t` are two sets. -/
protected def sum_diff_subset {α} {s t : set α} (h : s ⊆ t) [decidable_pred s] :
  s ⊕ (t \ s : set α) ≃ t :=
calc s ⊕ (t \ s : set α) ≃ (s ∪ (t \ s) : set α) : (equiv.set.union (by simp [inter_diff_self])).symm
... ≃ t : equiv.set.of_eq (by { simp [union_diff_self, union_eq_self_of_subset_left h] })

@[simp] lemma sum_diff_subset_apply_inl
  {α} {s t : set α} (h : s ⊆ t) [decidable_pred s] (x : s) :
  equiv.set.sum_diff_subset h (sum.inl x) = inclusion h x := rfl

@[simp] lemma sum_diff_subset_apply_inr
  {α} {s t : set α} (h : s ⊆ t) [decidable_pred s] (x : t \ s) :
  equiv.set.sum_diff_subset h (sum.inr x) = inclusion (diff_subset t s) x := rfl

lemma sum_diff_subset_symm_apply_of_mem
  {α} {s t : set α} (h : s ⊆ t) [decidable_pred s] {x : t} (hx : x.1 ∈ s) :
  (equiv.set.sum_diff_subset h).symm x = sum.inl ⟨x, hx⟩ :=
begin
  apply (equiv.set.sum_diff_subset h).injective,
  simp only [apply_symm_apply, sum_diff_subset_apply_inl],
  exact subtype.eq rfl,
end

lemma sum_diff_subset_symm_apply_of_not_mem
  {α} {s t : set α} (h : s ⊆ t) [decidable_pred s] {x : t} (hx : x.1 ∉ s) :
  (equiv.set.sum_diff_subset h).symm x = sum.inr ⟨x, ⟨x.2, hx⟩⟩  :=
begin
  apply (equiv.set.sum_diff_subset h).injective,
  simp only [apply_symm_apply, sum_diff_subset_apply_inr],
  exact subtype.eq rfl,
end

/-- If `s` is a set with decidable membership, then the sum of `s ∪ t` and `s ∩ t` is equivalent
to `s ⊕ t`. -/
protected def union_sum_inter {α : Type u} (s t : set α) [decidable_pred s] :
  (s ∪ t : set α) ⊕ (s ∩ t : set α) ≃ s ⊕ t :=
calc  (s ∪ t : set α) ⊕ (s ∩ t : set α)
    ≃ (s ∪ t \ s : set α) ⊕ (s ∩ t : set α) : by rw [union_diff_self]
... ≃ (s ⊕ (t \ s : set α)) ⊕ (s ∩ t : set α) :
  sum_congr (set.union $ subset_empty_iff.2 (inter_diff_self _ _)) (equiv.refl _)
... ≃ s ⊕ (t \ s : set α) ⊕ (s ∩ t : set α) : sum_assoc _ _ _
... ≃ s ⊕ (t \ s ∪ s ∩ t : set α) : sum_congr (equiv.refl _) begin
    refine (set.union' (∉ s) _ _).symm,
    exacts [λ x hx, hx.2, λ x hx, not_not_intro hx.1]
  end
... ≃ s ⊕ t : by { rw (_ : t \ s ∪ s ∩ t = t), rw [union_comm, inter_comm, inter_union_diff] }

/-- The set product of two sets is equivalent to the type product of their coercions to types. -/
protected def prod {α β} (s : set α) (t : set β) :
  s.prod t ≃ s × t :=
@subtype_prod_equiv_prod α β s t

/-- If a function `f` is injective on a set `s`, then `s` is equivalent to `f '' s`. -/
protected noncomputable def image_of_inj_on {α β} (f : α → β) (s : set α) (H : inj_on f s) :
  s ≃ (f '' s) :=
⟨λ p, ⟨f p, mem_image_of_mem f p.2⟩,
 λ p, ⟨classical.some p.2, (classical.some_spec p.2).1⟩,
 λ ⟨x, h⟩, subtype.eq (H (classical.some_spec (mem_image_of_mem f h)).1 h
   (classical.some_spec (mem_image_of_mem f h)).2),
 λ ⟨y, h⟩, subtype.eq (classical.some_spec h).2⟩

/-- If `f` is an injective function, then `s` is equivalent to `f '' s`. -/
protected noncomputable def image {α β} (f : α → β) (s : set α) (H : injective f) : s ≃ (f '' s) :=
equiv.set.image_of_inj_on f s (λ x y hx hy hxy, H hxy)

@[simp] theorem image_apply {α β} (f : α → β) (s : set α) (H : injective f) (a h) :
  set.image f s H ⟨a, h⟩ = ⟨f a, mem_image_of_mem _ h⟩ := rfl

/-- If `f : α → β` is an injective function, then `α` is equivalent to the range of `f`. -/
protected noncomputable def range {α β} (f : α → β) (H : injective f) :
  α ≃ range f :=
{ to_fun := λ x, ⟨f x, mem_range_self _⟩,
  inv_fun := λ x, classical.some x.2,
  left_inv := λ x, H (classical.some_spec (show f x ∈ range f, from mem_range_self _)),
  right_inv := λ x, subtype.eq $ classical.some_spec x.2 }

@[simp] theorem range_apply {α β} (f : α → β) (H : injective f) (a) :
  set.range f H a = ⟨f a, set.mem_range_self _⟩ := rfl

theorem apply_range_symm {α β} (f : α → β) (H : injective f) (b : range f) :
  f ((set.range f H).symm b) = b :=
begin
  conv_rhs { rw ←((set.range f H).right_inv b), },
  simp,
end

/-- If `α` is equivalent to `β`, then `set α` is equivalent to `set β`. -/
protected def congr {α β : Type*} (e : α ≃ β) : set α ≃ set β :=
⟨λ s, e '' s, λ t, e.symm '' t, symm_image_image e, symm_image_image e.symm⟩

/-- The set `{x ∈ s | t x}` is equivalent to the set of `x : s` such that `t x`. -/
protected def sep {α : Type u} (s : set α) (t : α → Prop) :
  ({ x ∈ s | t x } : set α) ≃ { x : s | t x } :=
(equiv.subtype_subtype_equiv_subtype_inter s t).symm

end set

/-- If `f` is a bijective function, then its domain is equivalent to its codomain. -/
noncomputable def of_bijective {α β} (f : α → β) (hf : bijective f) : α ≃ β :=
(equiv.set.range f hf.1).trans $ (set_congr hf.2.range_eq).trans $ equiv.set.univ β

@[simp] theorem coe_of_bijective {α β} {f : α → β} (hf : bijective f) :
  (of_bijective f hf : α → β) = f := rfl

/-- If `f` is an injective function, then its domain is equivalent to its range. -/
noncomputable def of_injective {α β} (f : α → β) (hf : injective f) : α ≃ _root_.set.range f :=
of_bijective (λ x, ⟨f x, set.mem_range_self x⟩) ⟨λ x y hxy, hf $ by injections, λ ⟨_, x, rfl⟩, ⟨x, rfl⟩⟩

@[simp] lemma of_injective_apply {α β} (f : α → β) (hf : injective f) (x : α) :
  of_injective f hf x = ⟨f x, set.mem_range_self x⟩ :=
rfl

def subtype_quotient_equiv_quotient_subtype (p₁ : α → Prop) [s₁ : setoid α]
  [s₂ : setoid (subtype p₁)] (p₂ : quotient s₁ → Prop) (hp₂ :  ∀ a, p₁ a ↔ p₂ ⟦a⟧)
  (h : ∀ x y : subtype p₁, @setoid.r _ s₂ x y ↔ (x : α) ≈ y) :
  {x // p₂ x} ≃ quotient s₂ :=
{ to_fun := λ a, quotient.hrec_on a.1 (λ a h, ⟦⟨a, (hp₂ _).2 h⟩⟧)
    (λ a b hab, hfunext (by rw quotient.sound hab)
    (λ h₁ h₂ _, heq_of_eq (quotient.sound ((h _ _).2 hab)))) a.2,
  inv_fun := λ a, quotient.lift_on a (λ a, (⟨⟦a.1⟧, (hp₂ _).1 a.2⟩ : {x // p₂ x}))
    (λ a b hab, subtype.ext_val (quotient.sound ((h _ _).1 hab))),
  left_inv := λ ⟨a, ha⟩, quotient.induction_on a (λ a ha, rfl) ha,
  right_inv := λ a, quotient.induction_on a (λ ⟨a, ha⟩, rfl) }

section swap
variable [decidable_eq α]
open decidable

/-- A helper function for `equiv.swap`. -/
def swap_core (a b r : α) : α :=
if r = a then b
else if r = b then a
else r

theorem swap_core_self (r a : α) : swap_core a a r = r :=
by { unfold swap_core, split_ifs; cc }

theorem swap_core_swap_core (r a b : α) : swap_core a b (swap_core a b r) = r :=
by { unfold swap_core, split_ifs; cc }

theorem swap_core_comm (r a b : α) : swap_core a b r = swap_core b a r :=
by { unfold swap_core, split_ifs; cc }

/-- `swap a b` is the permutation that swaps `a` and `b` and
  leaves other values as is. -/
def swap (a b : α) : perm α :=
⟨swap_core a b, swap_core a b, λr, swap_core_swap_core r a b, λr, swap_core_swap_core r a b⟩

theorem swap_self (a : α) : swap a a = equiv.refl _ :=
ext $ λ r, swap_core_self r a

theorem swap_comm (a b : α) : swap a b = swap b a :=
ext $ λ r, swap_core_comm r _ _

theorem swap_apply_def (a b x : α) : swap a b x = if x = a then b else if x = b then a else x :=
rfl

@[simp] theorem swap_apply_left (a b : α) : swap a b a = b :=
if_pos rfl

@[simp] theorem swap_apply_right (a b : α) : swap a b b = a :=
by { by_cases h : b = a; simp [swap_apply_def, h], }

theorem swap_apply_of_ne_of_ne {a b x : α} : x ≠ a → x ≠ b → swap a b x = x :=
by simp [swap_apply_def] {contextual := tt}

@[simp] theorem swap_swap (a b : α) : (swap a b).trans (swap a b) = equiv.refl _ :=
ext $ λ x, swap_core_swap_core _ _ _

theorem swap_comp_apply {a b x : α} (π : perm α) :
  π.trans (swap a b) x = if π x = a then b else if π x = b then a else π x :=
by { cases π, refl }

@[simp] lemma swap_inv {α : Type*} [decidable_eq α] (x y : α) :
  (swap x y)⁻¹ = swap x y := rfl

@[simp] lemma symm_trans_swap_trans [decidable_eq β] (a b : α)
  (e : α ≃ β) : (e.symm.trans (swap a b)).trans e = swap (e a) (e b) :=
equiv.ext (λ x, begin
  have : ∀ a, e.symm x = a ↔ x = e a :=
    λ a, by { rw @eq_comm _ (e.symm x), split; intros; simp * at * },
  simp [swap_apply_def, this],
  split_ifs; simp
end)

@[simp] lemma swap_mul_self {α : Type*} [decidable_eq α] (i j : α) : swap i j * swap i j = 1 :=
equiv.swap_swap i j

@[simp] lemma swap_apply_self {α : Type*} [decidable_eq α] (i j a : α) :
  swap i j (swap i j a) = a :=
by rw [← perm.mul_apply, swap_mul_self, perm.one_apply]

/-- Augment an equivalence with a prescribed mapping `f a = b` -/
def set_value (f : α ≃ β) (a : α) (b : β) : α ≃ β :=
(swap a (f.symm b)).trans f

@[simp] theorem set_value_eq (f : α ≃ β) (a : α) (b : β) : set_value f a b a = b :=
by { dsimp [set_value], simp [swap_apply_left] }

end swap

protected lemma forall_congr {p : α → Prop} {q : β → Prop} (f : α ≃ β)
  (h : ∀{x}, p x ↔ q (f x)) : (∀x, p x) ↔ (∀y, q y) :=
begin
  split; intros h₂ x,
  { rw [←f.right_inv x], apply h.mp, apply h₂ },
  apply h.mpr, apply h₂
end
protected lemma forall_congr' {p : α → Prop} {q : β → Prop} (f : α ≃ β)
  (h : ∀{x}, p (f.symm x) ↔ q x) : (∀x, p x) ↔ (∀y, q y) :=
(equiv.forall_congr f.symm (λ x, h.symm)).symm

-- We next build some higher arity versions of `equiv.forall_congr`.
-- Although they appear to just be repeated applications of `equiv.forall_congr`,
-- unification of metavariables works better with these versions.
-- In particular, they are necessary in `equiv_rw`.
-- (Stopping at ternary functions seems reasonable: at least in 1-categorical mathematics,
-- it's rare to have axioms involving more than 3 elements at once.)
universes ua1 ua2 ub1 ub2 ug1 ug2
variables {α₁ : Sort ua1} {α₂ : Sort ua2}
          {β₁ : Sort ub1} {β₂ : Sort ub2}
          {γ₁ : Sort ug1} {γ₂ : Sort ug2}

protected lemma forall₂_congr {p : α₁ → β₁ → Prop} {q : α₂ → β₂ → Prop} (eα : α₁ ≃ α₂)
  (eβ : β₁ ≃ β₂) (h : ∀{x y}, p x y ↔ q (eα x) (eβ y)) :
  (∀x y, p x y) ↔ (∀x y, q x y) :=
begin
  apply equiv.forall_congr,
  intros,
  apply equiv.forall_congr,
  intros,
  apply h,
end
protected lemma forall₂_congr' {p : α₁ → β₁ → Prop} {q : α₂ → β₂ → Prop} (eα : α₁ ≃ α₂)
  (eβ : β₁ ≃ β₂) (h : ∀{x y}, p (eα.symm x) (eβ.symm y) ↔ q x y) :
  (∀x y, p x y) ↔ (∀x y, q x y) :=
(equiv.forall₂_congr eα.symm eβ.symm (λ x y, h.symm)).symm

protected lemma forall₃_congr {p : α₁ → β₁ → γ₁ → Prop} {q : α₂ → β₂ → γ₂ → Prop}
  (eα : α₁ ≃ α₂) (eβ : β₁ ≃ β₂) (eγ : γ₁ ≃ γ₂)
  (h : ∀{x y z}, p x y z ↔ q (eα x) (eβ y) (eγ z)) : (∀x y z, p x y z) ↔ (∀x y z, q x y z) :=
begin
  apply equiv.forall₂_congr,
  intros,
  apply equiv.forall_congr,
  intros,
  apply h,
end
protected lemma forall₃_congr' {p : α₁ → β₁ → γ₁ → Prop} {q : α₂ → β₂ → γ₂ → Prop}
  (eα : α₁ ≃ α₂) (eβ : β₁ ≃ β₂) (eγ : γ₁ ≃ γ₂)
  (h : ∀{x y z}, p (eα.symm x) (eβ.symm y) (eγ.symm z) ↔ q x y z) :
    (∀x y z, p x y z) ↔ (∀x y z, q x y z) :=
(equiv.forall₃_congr eα.symm eβ.symm eγ.symm (λ x y z, h.symm)).symm

protected lemma forall_congr_left' {p : α → Prop} (f : α ≃ β) :
  (∀x, p x) ↔ (∀y, p (f.symm y)) :=
equiv.forall_congr f (λx, by simp)

protected lemma forall_congr_left {p : β → Prop} (f : α ≃ β) :
  (∀x, p (f x)) ↔ (∀y, p y) :=
(equiv.forall_congr_left' f.symm).symm

section
variables (P : α → Sort w) (e : α ≃ β)

/--
Transport dependent functions through an equivalence of the base space.
-/
def Pi_congr_left' : (Π a, P a) ≃ (Π b, P (e.symm b)) :=
{ to_fun := λ f x, f (e.symm x),
  inv_fun := λ f x, begin rw [← e.symm_apply_apply x], exact f (e x)  end,
  left_inv := λ f, funext $ λ x, eq_of_heq ((eq_rec_heq _ _).trans
    (by { dsimp, rw e.symm_apply_apply })),
  right_inv := λ f, funext $ λ x, eq_of_heq ((eq_rec_heq _ _).trans
    (by { rw e.apply_symm_apply })) }

@[simp]
lemma Pi_congr_left'_apply (f : Π a, P a) (b : β) : ((Pi_congr_left' P e) f) b = f (e.symm b) :=
rfl

@[simp]
lemma Pi_congr_left'_symm_apply (g : Π b, P (e.symm b)) (a : α) :
  ((Pi_congr_left' P e).symm g) a = (by { convert g (e a), simp }) :=
rfl

end

section
variables (P : β → Sort w) (e : α ≃ β)

/--
Transporting dependent functions through an equivalence of the base,
expressed as a "simplification".
-/
def Pi_congr_left : (Π a, P (e a)) ≃ (Π b, P b) :=
(Pi_congr_left' P e.symm).symm
end

section
variables
  {W : α → Sort w} {Z : β → Sort z} (h₁ : α ≃ β) (h₂ : Π a : α, (W a ≃ Z (h₁ a)))

/--
Transport dependent functions through
an equivalence of the base spaces and a family
of equivalences of the matching fibers.
-/
def Pi_congr : (Π a, W a) ≃ (Π b, Z b) :=
(equiv.Pi_congr_right h₂).trans (equiv.Pi_congr_left _ h₁)
end

section
variables
  {W : α → Sort w} {Z : β → Sort z} (h₁ : α ≃ β) (h₂ : Π b : β, (W (h₁.symm b) ≃ Z b))

/--
Transport dependent functions through
an equivalence of the base spaces and a family
of equivalences of the matching fibres.
-/
def Pi_congr' : (Π a, W a) ≃ (Π b, Z b) :=
(Pi_congr h₁.symm (λ b, (h₂ b).symm)).symm
end

end equiv

instance {α} [subsingleton α] : subsingleton (ulift α) := equiv.ulift.subsingleton
instance {α} [subsingleton α] : subsingleton (plift α) := equiv.plift.subsingleton

instance {α} [decidable_eq α] : decidable_eq (ulift α) := equiv.ulift.decidable_eq
instance {α} [decidable_eq α] : decidable_eq (plift α) := equiv.plift.decidable_eq

/-- If both `α` and `β` are singletons, then `α ≃ β`. -/
def equiv_of_unique_of_unique [unique α] [unique β] : α ≃ β :=
{ to_fun := λ _, default β,
  inv_fun := λ _, default α,
  left_inv := λ _, subsingleton.elim _ _,
  right_inv := λ _, subsingleton.elim _ _ }

/-- If `α` is a singleton, then it is equivalent to any `punit`. -/
def equiv_punit_of_unique [unique α] : α ≃ punit.{v} :=
equiv_of_unique_of_unique

/-- To give an equivalence between two subsingleton types, it is sufficient to give any two
    functions between them. -/
def equiv_of_subsingleton_of_subsingleton [subsingleton α] [subsingleton β]
  (f : α → β) (g : β → α) : α ≃ β :=
{ to_fun := f,
  inv_fun := g,
  left_inv := λ _, subsingleton.elim _ _,
  right_inv := λ _, subsingleton.elim _ _ }

/-- `unique (unique α)` is equivalent to `unique α`. -/
def unique_unique_equiv : unique (unique α) ≃ unique α :=
equiv_of_subsingleton_of_subsingleton (λ h, h.default)
  (λ h, { default := h, uniq := λ _, subsingleton.elim _ _ })

namespace quot

/-- An equivalence `e : α ≃ β` generates an equivalence between quotient spaces,
if `ra a₁ a₂ ↔ rb (e a₁) (e a₂). -/
protected def congr {ra : α → α → Prop} {rb : β → β → Prop} (e : α ≃ β)
  (eq : ∀a₁ a₂, ra a₁ a₂ ↔ rb (e a₁) (e a₂)) :
  quot ra ≃ quot rb :=
{ to_fun := quot.map e (assume a₁ a₂, (eq a₁ a₂).1),
  inv_fun := quot.map e.symm
    (assume b₁ b₂ h,
     (eq (e.symm b₁) (e.symm b₂)).2
       ((e.apply_symm_apply b₁).symm ▸ (e.apply_symm_apply b₂).symm ▸ h)),
  left_inv := by { rintros ⟨a⟩, dunfold quot.map, simp only [equiv.symm_apply_apply] },
  right_inv := by { rintros ⟨a⟩, dunfold quot.map, simp only [equiv.apply_symm_apply] } }

/-- Quotients are congruent on equivalences under equality of their relation.
An alternative is just to use rewriting with `eq`, but then computational proofs get stuck. -/
protected def congr_right {r r' : α → α → Prop} (eq : ∀a₁ a₂, r a₁ a₂ ↔ r' a₁ a₂) :
  quot r ≃ quot r' :=
quot.congr (equiv.refl α) eq

/-- An equivalence `e : α ≃ β` generates an equivalence between the quotient space of `α`
by a relation `ra` and the quotient space of `β` by the image of this relation under `e`. -/
protected def congr_left {r : α → α → Prop} (e : α ≃ β) :
  quot r ≃ quot (λ b b', r (e.symm b) (e.symm b')) :=
@quot.congr α β r (λ b b', r (e.symm b) (e.symm b')) e (λ a₁ a₂, by simp only [e.symm_apply_apply])

end quot

namespace quotient
/-- An equivalence `e : α ≃ β` generates an equivalence between quotient spaces,
if `ra a₁ a₂ ↔ rb (e a₁) (e a₂). -/
protected def congr {ra : setoid α} {rb : setoid β} (e : α ≃ β)
  (eq : ∀a₁ a₂, @setoid.r α ra a₁ a₂ ↔ @setoid.r β rb (e a₁) (e a₂)) :
  quotient ra ≃ quotient rb :=
quot.congr e eq

/-- Quotients are congruent on equivalences under equality of their relation.
An alternative is just to use rewriting with `eq`, but then computational proofs get stuck. -/
protected def congr_right {r r' : setoid α}
  (eq : ∀a₁ a₂, @setoid.r α r a₁ a₂ ↔ @setoid.r α r' a₁ a₂) : quotient r ≃ quotient r' :=
quot.congr_right eq
end quotient

/-- If a function is a bijection between `univ` and a set `s` in the target type, it induces an
equivalence between the original type and the type `↑s`. -/
noncomputable def set.bij_on.equiv {α : Type*} {β : Type*} {s : set β} (f : α → β)
  (h : set.bij_on f set.univ s) : α ≃ s :=
begin
  have : function.bijective (λ (x : α), (⟨f x, begin exact h.maps_to (set.mem_univ x) end⟩ : s)),
  { split,
    { assume x y hxy,
      apply h.inj_on (set.mem_univ x) (set.mem_univ y) (subtype.mk.inj hxy) },
    { assume x,
      rcases h.surj_on x.2 with ⟨y, hy⟩,
      exact ⟨y, subtype.eq hy.2⟩ } },
  exact equiv.of_bijective _ this
end

/-- The composition of an updated function with an equiv on a subset can be expressed as an
updated function. -/
lemma dite_comp_equiv_update {α : Type*} {β : Type*} {γ : Type*} {s : set α} (e : β ≃ s)
  (v : β → γ) (w : α → γ) (j : β) (x : γ) [decidable_eq β] [decidable_eq α]
  [∀ j, decidable (j ∈ s)] :
  (λ (i : α), if h : i ∈ s then (function.update v j x) (e.symm ⟨i, h⟩) else w i) =
  function.update (λ (i : α), if h : i ∈ s then v (e.symm ⟨i, h⟩) else w i) (e j) x :=
begin
  ext i,
  by_cases h : i ∈ s,
  { simp only [h, dif_pos],
    have A : e.symm ⟨i, h⟩ = j ↔ i = e j,
      by { rw equiv.symm_apply_eq, exact subtype.ext_iff_val },
    by_cases h' : i = e j,
    { rw [A.2 h', h'], simp },
    { have : ¬ e.symm ⟨i, h⟩ = j, by simpa [← A] using h',
      simp [h, h', this] } },
  { have : i ≠ e j,
      by { contrapose! h, have : (e j : α) ∈ s := (e j).2, rwa ← h at this },
    simp [h, this] }
end
