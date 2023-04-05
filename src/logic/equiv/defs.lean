/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import data.fun_like.equiv
import logic.unique

/-!
# Equivalence between types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define two types:

* `equiv α β` a.k.a. `α ≃ β`: a bijective map `α → β` bundled with its inverse map; we use this (and
  not equality!) to express that various `Type`s or `Sort`s are equivalent.

* `equiv.perm α`: the group of permutations `α ≃ α`. More lemmas about `equiv.perm` can be found in
  `group_theory/perm`.

Then we define

* canonical isomorphisms between various types: e.g.,

  - `equiv.refl α` is the identity map interpreted as `α ≃ α`;

* operations on equivalences: e.g.,

  - `equiv.symm e : β ≃ α` is the inverse of `e : α ≃ β`;

  - `equiv.trans e₁ e₂ : α ≃ γ` is the composition of `e₁ : α ≃ β` and `e₂ : β ≃ γ` (note the order
    of the arguments!);

* definitions that transfer some instances along an equivalence. By convention, we transfer
  instances from right to left.

  - `equiv.inhabited` takes `e : α ≃ β` and `[inhabited β]` and returns `inhabited α`;
  - `equiv.unique` takes `e : α ≃ β` and `[unique β]` and returns `unique α`;
  - `equiv.decidable_eq` takes `e : α ≃ β` and `[decidable_eq β]` and returns `decidable_eq α`.

  More definitions of this kind can be found in other files. E.g., `data/equiv/transfer_instance`
  does it for many algebraic type classes like `group`, `module`, etc.

Many more such isomorphisms and operations are defined in `logic/equiv/basic`.

## Tags

equivalence, congruence, bijective map
-/

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

instance {F} [equiv_like F α β] : has_coe_t F (α ≃ β) :=
⟨λ f, { to_fun := f, inv_fun := equiv_like.inv f, left_inv := equiv_like.left_inv f,
  right_inv := equiv_like.right_inv f }⟩

/-- `perm α` is the type of bijections from `α` to itself. -/
@[reducible] def equiv.perm (α : Sort*) := equiv α α

namespace equiv

instance : equiv_like (α ≃ β) α β :=
{ coe := to_fun, inv := inv_fun, left_inv := left_inv, right_inv := right_inv,
  coe_injective' := λ e₁ e₂ h₁ h₂, by { cases e₁, cases e₂, congr' } }

instance : has_coe_to_fun (α ≃ β) (λ _, α → β) := ⟨to_fun⟩

@[simp] theorem coe_fn_mk (f : α → β) (g l r) : (equiv.mk f g l r : α → β) = f :=
rfl

/-- The map `coe_fn : (r ≃ s) → (r → s)` is injective. -/
theorem coe_fn_injective : @function.injective (α ≃ β) (α → β) coe_fn := fun_like.coe_injective
protected lemma coe_inj {e₁ e₂ : α ≃ β} : (e₁ : α → β) = e₂ ↔ e₁ = e₂ := fun_like.coe_fn_eq
@[ext] lemma ext {f g : equiv α β} (H : ∀ x, f x = g x) : f = g := fun_like.ext f g H
protected lemma congr_arg {f : equiv α β} {x x' : α} : x = x' → f x = f x' := fun_like.congr_arg f
protected lemma congr_fun {f g : equiv α β} (h : f = g) (x : α) : f x = g x :=
fun_like.congr_fun h x
lemma ext_iff {f g : equiv α β} : f = g ↔ ∀ x, f x = g x := fun_like.ext_iff

@[ext] lemma perm.ext {σ τ : equiv.perm α} (H : ∀ x, σ x = τ x) : σ = τ :=
equiv.ext H

protected lemma perm.congr_arg {f : equiv.perm α} {x x' : α} : x = x' → f x = f x' :=
equiv.congr_arg

protected lemma perm.congr_fun {f g : equiv.perm α} (h : f = g) (x : α) : f x = g x :=
equiv.congr_fun h x

lemma perm.ext_iff {σ τ : equiv.perm α} : σ = τ ↔ ∀ x, σ x = τ x :=
ext_iff

/-- Any type is equivalent to itself. -/
@[refl] protected def refl (α : Sort*) : α ≃ α := ⟨id, id, λ x, rfl, λ x, rfl⟩

instance inhabited' : inhabited (α ≃ α) := ⟨equiv.refl α⟩

/-- Inverse of an equivalence `e : α ≃ β`. -/
@[symm] protected def symm (e : α ≃ β) : β ≃ α := ⟨e.inv_fun, e.to_fun, e.right_inv, e.left_inv⟩

/-- See Note [custom simps projection] -/
def simps.symm_apply (e : α ≃ β) : β → α := e.symm

initialize_simps_projections equiv (to_fun → apply, inv_fun → symm_apply)

/-- Composition of equivalences `e₁ : α ≃ β` and `e₂ : β ≃ γ`. -/
@[trans] protected def trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm, e₂.left_inv.comp e₁.left_inv, e₂.right_inv.comp e₁.right_inv⟩

@[simp]
lemma to_fun_as_coe (e : α ≃ β) : e.to_fun = e := rfl

@[simp]
lemma inv_fun_as_coe (e : α ≃ β) : e.inv_fun = e.symm := rfl

protected theorem injective (e : α ≃ β) : injective e := equiv_like.injective e
protected theorem surjective (e : α ≃ β) : surjective e := equiv_like.surjective e
protected theorem bijective (e : α ≃ β) : bijective e := equiv_like.bijective e

protected theorem subsingleton (e : α ≃ β) [subsingleton β] : subsingleton α :=
e.injective.subsingleton

protected theorem subsingleton.symm (e : α ≃ β) [subsingleton α] : subsingleton β :=
e.symm.injective.subsingleton

lemma subsingleton_congr (e : α ≃ β) : subsingleton α ↔ subsingleton β :=
⟨λ h, by exactI e.symm.subsingleton, λ h, by exactI e.subsingleton⟩

instance equiv_subsingleton_cod [subsingleton β] : subsingleton (α ≃ β) :=
fun_like.subsingleton_cod

instance equiv_subsingleton_dom [subsingleton α] : subsingleton (α ≃ β) :=
equiv_like.subsingleton_dom

instance perm_unique [subsingleton α] : unique (perm α) :=
unique_of_subsingleton (equiv.refl α)

lemma perm.subsingleton_eq_refl [subsingleton α] (e : perm α) :
  e = equiv.refl α := subsingleton.elim _ _

/-- Transfer `decidable_eq` across an equivalence. -/
protected def decidable_eq (e : α ≃ β) [decidable_eq β] : decidable_eq α :=
e.injective.decidable_eq

lemma nonempty_congr (e : α ≃ β) : nonempty α ↔ nonempty β :=
nonempty.congr e e.symm

protected lemma nonempty (e : α ≃ β) [nonempty β] : nonempty α :=
e.nonempty_congr.mpr ‹_›

/-- If `α ≃ β` and `β` is inhabited, then so is `α`. -/
protected def inhabited [inhabited β] (e : α ≃ β) : inhabited α :=
⟨e.symm default⟩

/-- If `α ≃ β` and `β` is a singleton type, then so is `α`. -/
protected def unique [unique β] (e : α ≃ β) : unique α :=
e.symm.surjective.unique

/-- Equivalence between equal types. -/
protected def cast {α β : Sort*} (h : α = β) : α ≃ β :=
⟨cast h, cast h.symm, λ x, by { cases h, refl }, λ x, by { cases h, refl }⟩

@[simp] theorem coe_fn_symm_mk (f : α → β) (g l r) : ((equiv.mk f g l r).symm : β → α) = g :=
rfl

@[simp] theorem coe_refl : ⇑(equiv.refl α) = id := rfl

/-- This cannot be a `simp` lemmas as it incorrectly matches against `e : α ≃ synonym α`, when
`synonym α` is semireducible. This makes a mess of `multiplicative.of_add` etc. -/
theorem perm.coe_subsingleton {α : Type*} [subsingleton α] (e : perm α) : ⇑(e) = id :=
by rw [perm.subsingleton_eq_refl e, coe_refl]

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

-- The `simp` attribute is needed to make this a `dsimp` lemma.
-- `simp` will always rewrite with `equiv.symm_symm` before this has a chance to fire.
@[simp, nolint simp_nf] theorem symm_symm_apply (f : α ≃ β) (b : α) : f.symm.symm b = f b := rfl

theorem apply_eq_iff_eq (f : α ≃ β) {x y : α} : f x = f y ↔ x = y := equiv_like.apply_eq_iff_eq f

theorem apply_eq_iff_eq_symm_apply {α β : Sort*} (f : α ≃ β) {x : α} {y : β} :
  f x = y ↔ x = f.symm y :=
begin
  conv_lhs { rw ←apply_symm_apply f y, },
  rw apply_eq_iff_eq,
end

@[simp] theorem cast_apply {α β} (h : α = β) (x : α) : equiv.cast h x = cast h x := rfl

@[simp] theorem cast_symm {α β} (h : α = β) : (equiv.cast h).symm = equiv.cast h.symm := rfl

@[simp] theorem cast_refl {α} (h : α = α := rfl) : equiv.cast h = equiv.refl α := rfl

@[simp] theorem cast_trans {α β γ} (h : α = β) (h2 : β = γ) :
  (equiv.cast h).trans (equiv.cast h2) = equiv.cast (h.trans h2) :=
ext $ λ x, by { substs h h2, refl }

lemma cast_eq_iff_heq {α β} (h : α = β) {a : α} {b : β} : equiv.cast h a = b ↔ a == b :=
by { subst h, simp }

lemma symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = y ↔ x = e y :=
⟨λ H, by simp [H.symm], λ H, by simp [H]⟩

lemma eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm x ↔ e y = x :=
(eq_comm.trans e.symm_apply_eq).trans eq_comm

@[simp] theorem symm_symm (e : α ≃ β) : e.symm.symm = e := by { cases e, refl }

@[simp] theorem trans_refl (e : α ≃ β) : e.trans (equiv.refl β) = e := by { cases e, refl }

@[simp] theorem refl_symm : (equiv.refl α).symm = equiv.refl α := rfl

@[simp] theorem refl_trans (e : α ≃ β) : (equiv.refl α).trans e = e := by { cases e, refl }

@[simp] theorem symm_trans_self (e : α ≃ β) : e.symm.trans e = equiv.refl β := ext (by simp)

@[simp] theorem self_trans_symm (e : α ≃ β) : e.trans e.symm = equiv.refl α := ext (by simp)

lemma trans_assoc {δ} (ab : α ≃ β) (bc : β ≃ γ) (cd : γ ≃ δ) :
  (ab.trans bc).trans cd = ab.trans (bc.trans cd) :=
equiv.ext $ assume a, rfl

theorem left_inverse_symm (f : equiv α β) : left_inverse f.symm f := f.left_inv

theorem right_inverse_symm (f : equiv α β) : function.right_inverse f.symm f := f.right_inv

lemma injective_comp (e : α ≃ β) (f : β → γ) : injective (f ∘ e) ↔ injective f :=
equiv_like.injective_comp e f

lemma comp_injective (f : α → β) (e : β ≃ γ) : injective (e ∘ f) ↔ injective f :=
equiv_like.comp_injective f e

lemma surjective_comp (e : α ≃ β) (f : β → γ) : surjective (f ∘ e) ↔ surjective f :=
equiv_like.surjective_comp e f

lemma comp_surjective (f : α → β) (e : β ≃ γ) : surjective (e ∘ f) ↔ surjective f :=
equiv_like.comp_surjective f e

lemma bijective_comp (e : α ≃ β) (f : β → γ) : bijective (f ∘ e) ↔ bijective f :=
equiv_like.bijective_comp e f

lemma comp_bijective (f : α → β) (e : β ≃ γ) : bijective (e ∘ f) ↔ bijective f :=
equiv_like.comp_bijective f e

/-- If `α` is equivalent to `β` and `γ` is equivalent to `δ`, then the type of equivalences `α ≃ γ`
is equivalent to the type of equivalences `β ≃ δ`. -/
def equiv_congr {δ} (ab : α ≃ β) (cd : γ ≃ δ) : (α ≃ γ) ≃ (β ≃ δ) :=
⟨ λac, (ab.symm.trans ac).trans cd, λbd, ab.trans $ bd.trans $ cd.symm,
  assume ac, by { ext x, simp }, assume ac, by { ext x, simp } ⟩

@[simp] lemma equiv_congr_refl {α β} :
  (equiv.refl α).equiv_congr (equiv.refl β) = equiv.refl (α ≃ β) := by { ext, refl }

@[simp] lemma equiv_congr_symm {δ} (ab : α ≃ β) (cd : γ ≃ δ) :
  (ab.equiv_congr cd).symm = ab.symm.equiv_congr cd.symm := by { ext, refl }

@[simp] lemma equiv_congr_trans {δ ε ζ} (ab : α ≃ β) (de : δ ≃ ε) (bc : β ≃ γ) (ef : ε ≃ ζ) :
  (ab.equiv_congr de).trans (bc.equiv_congr ef) = (ab.trans bc).equiv_congr (de.trans ef) :=
by { ext, refl }

@[simp] lemma equiv_congr_refl_left {α β γ} (bg : β ≃ γ) (e : α ≃ β) :
  (equiv.refl α).equiv_congr bg e = e.trans bg := rfl

@[simp] lemma equiv_congr_refl_right {α β} (ab e : α ≃ β) :
  ab.equiv_congr (equiv.refl β) e = ab.symm.trans e := rfl

@[simp] lemma equiv_congr_apply_apply {δ} (ab : α ≃ β) (cd : γ ≃ δ) (e : α ≃ γ) (x) :
  ab.equiv_congr cd e x = cd (e (ab.symm x)) := rfl

section perm_congr

variables {α' β' : Type*} (e : α' ≃ β')

/-- If `α` is equivalent to `β`, then `perm α` is equivalent to `perm β`. -/
def perm_congr : perm α' ≃ perm β' :=
equiv_congr e e

lemma perm_congr_def (p : equiv.perm α') :
  e.perm_congr p = (e.symm.trans p).trans e := rfl

@[simp] lemma perm_congr_refl :
  e.perm_congr (equiv.refl _) = equiv.refl _ :=
by simp [perm_congr_def]

@[simp] lemma perm_congr_symm :
  e.perm_congr.symm = e.symm.perm_congr := rfl

@[simp] lemma perm_congr_apply (p : equiv.perm α') (x) :
  e.perm_congr p x = e (p (e.symm x)) := rfl

lemma perm_congr_symm_apply (p : equiv.perm β') (x) :
  e.perm_congr.symm p x = e.symm (p (e x)) := rfl

lemma perm_congr_trans (p p' : equiv.perm α') :
  (e.perm_congr p).trans (e.perm_congr p') = e.perm_congr (p.trans p') :=
by { ext, simp }

end perm_congr

/-- Two empty types are equivalent. -/
def equiv_of_is_empty  (α β : Sort*) [is_empty α] [is_empty β] : α ≃ β :=
⟨is_empty_elim, is_empty_elim, is_empty_elim, is_empty_elim⟩

/-- If `α` is an empty type, then it is equivalent to the `empty` type. -/
def equiv_empty (α : Sort u) [is_empty α] : α ≃ empty :=
equiv_of_is_empty  α _

/-- If `α` is an empty type, then it is equivalent to the `pempty` type in any universe. -/
def equiv_pempty (α : Sort v) [is_empty α] : α ≃ pempty.{u} :=
equiv_of_is_empty  α _

/-- `α` is equivalent to an empty type iff `α` is empty. -/
def equiv_empty_equiv (α : Sort u) : (α ≃ empty) ≃ is_empty α :=
⟨λ e, function.is_empty e, @equiv_empty α, λ e, ext $ λ x, (e x).elim, λ p, rfl⟩

/-- The `Sort` of proofs of a false proposition is equivalent to `pempty`. -/
def prop_equiv_pempty {p : Prop} (h : ¬p) : p ≃ pempty :=
@equiv_pempty p $ is_empty.prop_iff.2 h

/-- If both `α` and `β` have a unique element, then `α ≃ β`. -/
def equiv_of_unique (α β : Sort*) [unique α] [unique β] : α ≃ β :=
{ to_fun := default,
  inv_fun := default,
  left_inv := λ _, subsingleton.elim _ _,
  right_inv := λ _, subsingleton.elim _ _ }

/-- If `α` has a unique element, then it is equivalent to any `punit`. -/
def equiv_punit (α : Sort*) [unique α] : α ≃ punit.{v} :=
equiv_of_unique α _

/-- The `Sort` of proofs of a true proposition is equivalent to `punit`. -/
def prop_equiv_punit {p : Prop} (h : p) : p ≃ punit :=
@equiv_punit p $ unique_prop h

/-- `ulift α` is equivalent to `α`. -/
@[simps apply symm_apply {fully_applied := ff}]
protected def ulift {α : Type v} : ulift.{u} α ≃ α :=
⟨ulift.down, ulift.up, ulift.up_down, λ a, rfl⟩

/-- `plift α` is equivalent to `α`. -/
@[simps apply symm_apply {fully_applied := ff}]
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
@[congr, simps apply] def arrow_congr {α₁ β₁ α₂ β₂ : Sort*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
  (α₁ → β₁) ≃ (α₂ → β₂) :=
{ to_fun := λ f, e₂ ∘ f ∘ e₁.symm,
  inv_fun := λ f, e₂.symm ∘ f ∘ e₁,
  left_inv := λ f, funext $ λ x, by simp,
  right_inv := λ f, funext $ λ x, by simp }

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
@[congr, simps apply]
def arrow_congr' {α₁ β₁ α₂ β₂ : Type*} (hα : α₁ ≃ α₂) (hβ : β₁ ≃ β₂) : (α₁ → β₁) ≃ (α₂ → β₂) :=
equiv.arrow_congr hα hβ

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
@[simps apply]
def conj (e : α ≃ β) : (α → α) ≃ (β → β) := arrow_congr e e

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

lemma eq_comp_symm {α β γ} (e : α ≃ β) (f : β → γ) (g : α → γ) :
  f = g ∘ e.symm ↔ f ∘ e = g :=
(e.arrow_congr (equiv.refl γ)).symm_apply_eq.symm

lemma comp_symm_eq {α β γ} (e : α ≃ β) (f : β → γ) (g : α → γ) :
  g ∘ e.symm = f ↔ g = f ∘ e :=
(e.arrow_congr (equiv.refl γ)).eq_symm_apply.symm

lemma eq_symm_comp {α β γ} (e : α ≃ β) (f : γ → α) (g : γ → β) :
  f = e.symm ∘ g ↔ e ∘ f = g :=
((equiv.refl γ).arrow_congr e).eq_symm_apply

lemma symm_comp_eq {α β γ} (e : α ≃ β) (f : γ → α) (g : γ → β) :
  e.symm ∘ g = f ↔ g = e ∘ f :=
((equiv.refl γ).arrow_congr e).symm_apply_eq

/-- `punit` sorts in any two universes are equivalent. -/
def punit_equiv_punit : punit.{v} ≃ punit.{w} :=
⟨λ _, punit.star, λ _, punit.star, λ u, by { cases u, refl }, λ u, by { cases u, reflexivity }⟩

/-- `Prop` is noncomputably equivalent to `bool`. -/
noncomputable def Prop_equiv_bool : Prop ≃ bool :=
⟨λ p, @to_bool p (classical.prop_decidable _),
 λ b, b, λ p, by simp, λ b, by simp⟩

section
/-- The sort of maps to `punit.{v}` is equivalent to `punit.{w}`. -/
def arrow_punit_equiv_punit (α : Sort*) : (α → punit.{v}) ≃ punit.{w} :=
⟨λ f, punit.star, λ u f, punit.star,
  λ f, by { funext x, cases f x, refl }, λ u, by { cases u, reflexivity }⟩

/-- If `α` is `subsingleton` and `a : α`, then the type of dependent functions `Π (i : α), β
i` is equivalent to `β i`. -/
@[simps]
def Pi_subsingleton {α} (β : α → Sort*) [subsingleton α] (a : α) : (Π a', β a') ≃ β a :=
{ to_fun := eval a,
  inv_fun := λ x b, cast (congr_arg β $ subsingleton.elim a b) x,
  left_inv := λ f, funext $ λ b, by { rw subsingleton.elim b a, reflexivity },
  right_inv := λ b, rfl }

/-- If `α` has a unique term, then the type of function `α → β` is equivalent to `β`. -/
@[simps { fully_applied := ff }] def fun_unique (α β) [unique α] : (α → β) ≃ β :=
Pi_subsingleton _ default

/-- The sort of maps from `punit` is equivalent to the codomain. -/
def punit_arrow_equiv (α : Sort*) : (punit.{u} → α) ≃ α :=
fun_unique _ _

/-- The sort of maps from `true` is equivalent to the codomain. -/
def true_arrow_equiv (α : Sort*) : (true → α) ≃ α :=
fun_unique _ _

/-- The sort of maps from a type that `is_empty` is equivalent to `punit`. -/
def arrow_punit_of_is_empty (α β : Sort*) [is_empty α] : (α → β) ≃ punit.{u} :=
⟨λ f, punit.star, λ u, is_empty_elim, λ f, funext is_empty_elim, λ u, by { cases u, refl }⟩

/-- The sort of maps from `empty` is equivalent to `punit`. -/
def empty_arrow_equiv_punit (α : Sort*) : (empty → α) ≃ punit.{u} :=
arrow_punit_of_is_empty _ _

/-- The sort of maps from `pempty` is equivalent to `punit`. -/
def pempty_arrow_equiv_punit (α : Sort*) : (pempty → α) ≃ punit.{u} :=
arrow_punit_of_is_empty _ _

/-- The sort of maps from `false` is equivalent to `punit`. -/
def false_arrow_equiv_punit (α : Sort*) : (false → α) ≃ punit.{u} :=
arrow_punit_of_is_empty _ _

end

section

/-- A `psigma`-type is equivalent to the corresponding `sigma`-type. -/
@[simps apply symm_apply] def psigma_equiv_sigma {α} (β : α → Type*) : (Σ' i, β i) ≃ Σ i, β i :=
⟨λ a, ⟨a.1, a.2⟩, λ a, ⟨a.1, a.2⟩, λ ⟨a, b⟩, rfl, λ ⟨a, b⟩, rfl⟩

/-- A `psigma`-type is equivalent to the corresponding `sigma`-type. -/
@[simps apply symm_apply] def psigma_equiv_sigma_plift {α} (β : α → Sort*) :
  (Σ' i, β i) ≃ Σ i : plift α, plift (β i.down) :=
⟨λ a, ⟨plift.up a.1, plift.up a.2⟩, λ a, ⟨a.1.down, a.2.down⟩, λ ⟨a, b⟩, rfl, λ ⟨⟨a⟩, ⟨b⟩⟩, rfl⟩

/-- A family of equivalences `Π a, β₁ a ≃ β₂ a` generates an equivalence between `Σ' a, β₁ a` and
`Σ' a, β₂ a`. -/
@[simps apply]
def psigma_congr_right {α} {β₁ β₂ : α → Sort*} (F : Π a, β₁ a ≃ β₂ a) : (Σ' a, β₁ a) ≃ Σ' a, β₂ a :=
⟨λ a, ⟨a.1, F a.1 a.2⟩, λ a, ⟨a.1, (F a.1).symm a.2⟩,
 λ ⟨a, b⟩, congr_arg (psigma.mk a) $ symm_apply_apply (F a) b,
 λ ⟨a, b⟩, congr_arg (psigma.mk a) $ apply_symm_apply (F a) b⟩

@[simp] lemma psigma_congr_right_trans {α} {β₁ β₂ β₃ : α → Sort*}
  (F : Π a, β₁ a ≃ β₂ a) (G : Π a, β₂ a ≃ β₃ a) :
  (psigma_congr_right F).trans (psigma_congr_right G) =
    psigma_congr_right (λ a, (F a).trans (G a)) :=
by { ext1 x, cases x, refl }

@[simp] lemma psigma_congr_right_symm {α} {β₁ β₂ : α → Sort*} (F : Π a, β₁ a ≃ β₂ a) :
  (psigma_congr_right F).symm = psigma_congr_right (λ a, (F a).symm) :=
by { ext1 x, cases x, refl }

@[simp] lemma psigma_congr_right_refl {α} {β : α → Sort*} :
  (psigma_congr_right (λ a, equiv.refl (β a))) = equiv.refl (Σ' a, β a) :=
by { ext1 x, cases x, refl }

/-- A family of equivalences `Π a, β₁ a ≃ β₂ a` generates an equivalence between `Σ a, β₁ a` and
`Σ a, β₂ a`. -/
@[simps apply]
def sigma_congr_right {α} {β₁ β₂ : α → Type*} (F : Π a, β₁ a ≃ β₂ a) : (Σ a, β₁ a) ≃ Σ a, β₂ a :=
⟨λ a, ⟨a.1, F a.1 a.2⟩, λ a, ⟨a.1, (F a.1).symm a.2⟩,
 λ ⟨a, b⟩, congr_arg (sigma.mk a) $ symm_apply_apply (F a) b,
 λ ⟨a, b⟩, congr_arg (sigma.mk a) $ apply_symm_apply (F a) b⟩

@[simp] lemma sigma_congr_right_trans {α} {β₁ β₂ β₃ : α → Type*}
  (F : Π a, β₁ a ≃ β₂ a) (G : Π a, β₂ a ≃ β₃ a) :
  (sigma_congr_right F).trans (sigma_congr_right G) = sigma_congr_right (λ a, (F a).trans (G a)) :=
by { ext1 x, cases x, refl }

@[simp] lemma sigma_congr_right_symm {α} {β₁ β₂ : α → Type*} (F : Π a, β₁ a ≃ β₂ a) :
  (sigma_congr_right F).symm = sigma_congr_right (λ a, (F a).symm) :=
by { ext1 x, cases x, refl }

@[simp] lemma sigma_congr_right_refl {α} {β : α → Type*} :
  (sigma_congr_right (λ a, equiv.refl (β a))) = equiv.refl (Σ a, β a) :=
by { ext1 x, cases x, refl }

/-- A `psigma` with `Prop` fibers is equivalent to the subtype.  -/
def psigma_equiv_subtype {α : Type v} (P : α → Prop) :
  (Σ' i, P i) ≃ subtype P :=
{ to_fun := λ x, ⟨x.1, x.2⟩,
  inv_fun := λ x, ⟨x.1, x.2⟩,
  left_inv := λ x, by { cases x, refl, },
  right_inv := λ x, by { cases x, refl, }, }

/-- A `sigma` with `plift` fibers is equivalent to the subtype. -/
def sigma_plift_equiv_subtype {α : Type v} (P : α → Prop) :
  (Σ i, plift (P i)) ≃ subtype P :=
((psigma_equiv_sigma _).symm.trans (psigma_congr_right (λ a, equiv.plift))).trans
  (psigma_equiv_subtype P)

/--
A `sigma` with `λ i, ulift (plift (P i))` fibers is equivalent to `{ x // P x }`.
Variant of `sigma_plift_equiv_subtype`.
-/
def sigma_ulift_plift_equiv_subtype {α : Type v} (P : α → Prop) :
  (Σ i, ulift (plift (P i))) ≃ subtype P :=
(sigma_congr_right (λ a, equiv.ulift)).trans (sigma_plift_equiv_subtype P)

namespace perm

/-- A family of permutations `Π a, perm (β a)` generates a permuation `perm (Σ a, β₁ a)`. -/
@[reducible]
def sigma_congr_right {α} {β : α → Sort*} (F : Π a, perm (β a)) : perm (Σ a, β a) :=
equiv.sigma_congr_right F

@[simp] lemma sigma_congr_right_trans {α} {β : α → Sort*}
  (F : Π a, perm (β a)) (G : Π a, perm (β a)) :
  (sigma_congr_right F).trans (sigma_congr_right G) = sigma_congr_right (λ a, (F a).trans (G a)) :=
equiv.sigma_congr_right_trans F G

@[simp] lemma sigma_congr_right_symm {α} {β : α → Sort*} (F : Π a, perm (β a)) :
  (sigma_congr_right F).symm = sigma_congr_right (λ a, (F a).symm) :=
equiv.sigma_congr_right_symm F

@[simp] lemma sigma_congr_right_refl {α} {β : α → Sort*} :
  (sigma_congr_right (λ a, equiv.refl (β a))) = equiv.refl (Σ a, β a) :=
equiv.sigma_congr_right_refl

end perm

/-- An equivalence `f : α₁ ≃ α₂` generates an equivalence between `Σ a, β (f a)` and `Σ a, β a`. -/
@[simps apply]
def sigma_congr_left {α₁ α₂} {β : α₂ → Sort*} (e : α₁ ≃ α₂) : (Σ a:α₁, β (e a)) ≃ (Σ a:α₂, β a) :=
⟨λ a, ⟨e a.1, a.2⟩, λ a, ⟨e.symm a.1, @@eq.rec β a.2 (e.right_inv a.1).symm⟩,
 λ ⟨a, b⟩, match e.symm (e a), e.left_inv a : ∀ a' (h : a' = a),
     @sigma.mk _ (β ∘ e) _ (@@eq.rec β b (congr_arg e h.symm)) = ⟨a, b⟩ with
   | _, rfl := rfl end,
 λ ⟨a, b⟩, match e (e.symm a), _ : ∀ a' (h : a' = a),
     sigma.mk a' (@@eq.rec β b h.symm) = ⟨a, b⟩ with
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
@[simps apply symm_apply] def sigma_equiv_prod (α β : Type*) : (Σ_:α, β) ≃ α × β :=
⟨λ a, ⟨a.1, a.2⟩, λ a, ⟨a.1, a.2⟩, λ ⟨a, b⟩, rfl, λ ⟨a, b⟩, rfl⟩

/-- If each fiber of a `sigma` type is equivalent to a fixed type, then the sigma type
is equivalent to the product. -/
def sigma_equiv_prod_of_equiv {α β} {β₁ : α → Sort*} (F : Π a, β₁ a ≃ β) : sigma β₁ ≃ α × β :=
(sigma_congr_right F).trans (sigma_equiv_prod α β)

/-- Dependent product of types is associative up to an equivalence. -/
def sigma_assoc {α : Type*} {β : α → Type*} (γ : Π (a : α), β a → Type*) :
  (Σ (ab : Σ (a : α), β a), γ ab.1 ab.2) ≃ Σ (a : α), (Σ (b : β a), γ a b) :=
{ to_fun := λ x, ⟨x.1.1, ⟨x.1.2, x.2⟩⟩,
  inv_fun := λ x, ⟨⟨x.1, x.2.1⟩, x.2.2⟩,
  left_inv := λ ⟨⟨a, b⟩, c⟩, rfl,
  right_inv := λ ⟨a, ⟨b, c⟩⟩, rfl }

end

protected lemma exists_unique_congr {p : α → Prop} {q : β → Prop} (f : α ≃ β)
  (h : ∀{x}, p x ↔ q (f x)) : (∃! x, p x) ↔ ∃! y, q y :=
begin
  split,
  { rintro ⟨a, ha₁, ha₂⟩,
    exact ⟨f a, h.1 ha₁, λ b hb, f.symm_apply_eq.1 (ha₂ (f.symm b) (h.2 (by simpa using hb)))⟩ },
  { rintro ⟨b, hb₁, hb₂⟩,
    exact ⟨f.symm b, h.2 (by simpa using hb₁), λ y hy, (eq_symm_apply f).2 (hb₂ _ (h.1 hy))⟩ }
end

protected lemma exists_unique_congr_left' {p : α → Prop} (f : α ≃ β) :
  (∃! x, p x) ↔ (∃! y, p (f.symm y)) :=
equiv.exists_unique_congr f (λx, by simp)

protected lemma exists_unique_congr_left {p : β → Prop} (f : α ≃ β) :
  (∃! x, p (f x)) ↔ (∃! y, p y) :=
(equiv.exists_unique_congr_left' f.symm).symm

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

protected lemma exists_congr_left {α β} (f : α ≃ β) {p : α → Prop} :
  (∃ a, p a) ↔ (∃ b, p (f.symm b)) :=
⟨λ ⟨a, h⟩, ⟨f a, by simpa using h⟩, λ ⟨b, h⟩, ⟨_, h⟩⟩

end equiv


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

@[simp]
lemma congr_mk {ra : α → α → Prop} {rb : β → β → Prop} (e : α ≃ β)
  (eq : ∀ (a₁ a₂ : α), ra a₁ a₂ ↔ rb (e a₁) (e a₂)) (a : α) :
  quot.congr e eq (quot.mk ra a) = quot.mk rb (e a) := rfl

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

@[simp]
lemma congr_mk {ra : setoid α} {rb : setoid β} (e : α ≃ β)
  (eq : ∀ (a₁ a₂ : α), setoid.r a₁ a₂ ↔ setoid.r (e a₁) (e a₂)) (a : α):
  quotient.congr e eq (quotient.mk a) = quotient.mk (e a) :=
rfl

/-- Quotients are congruent on equivalences under equality of their relation.
An alternative is just to use rewriting with `eq`, but then computational proofs get stuck. -/
protected def congr_right {r r' : setoid α}
  (eq : ∀a₁ a₂, @setoid.r α r a₁ a₂ ↔ @setoid.r α r' a₁ a₂) : quotient r ≃ quotient r' :=
quot.congr_right eq

end quotient
