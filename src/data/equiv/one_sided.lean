/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import data.set.function

/-!
# Functions with a bundled one-sided inverse

This provides `α ↬ β` (`injection`) and `α ↠ β` (`surjection`), for functions associated with a
specific left- or right-inverse. For the two-sided inverse, use `α ≃ β` (`equiv`).

For cases when you care only that a function is injective, and do not need a specific inverse, use
`α ↪ β` (`embedding`).
-/

open function

universes u v w z
variables {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort w}

set_option old_structure_cmd true

/-- `α ↬ β` is the type of functions from `α → β` with an associated left-inverse. -/
@[nolint has_inhabited_instance]
structure injection (α : Sort*) (β : Sort*) :=
(to_fun    : α → β)
(inv_fun   : β → α)
(left_inv  : left_inverse inv_fun to_fun)

/-- `α ↠ β` is the type of functions from `α → β` with an associated right-inverse. -/
@[nolint has_inhabited_instance]
structure surjection (α : Sort*) (β : Sort*) :=
(to_fun    : α → β)
(inv_fun   : β → α)
(right_inv : right_inverse inv_fun to_fun)


infix ` ↬ `:25 := injection
infix ` ↠ `:25 := surjection

/-! ### Coercion lemmas -/

section coes

namespace injection

instance : has_coe_to_fun (α ↬ β) :=
⟨_, to_fun⟩

@[simp] lemma to_fun_eq_coe (f : α ↬ β) : f.to_fun = f := rfl

@[simp] lemma coe_mk (f : α → β) (g l) : (injection.mk f g l : α → β) = f :=
rfl

protected lemma congr_arg {f : α ↬ β} : Π {x x' : α}, x = x' → f x = f x'
| _ _ rfl := rfl

protected lemma congr_fun {f g : α ↬ β} (h : f = g) (x : α) : f x = g x := h ▸ rfl

end injection

namespace surjection

instance : has_coe_to_fun (α ↠ β) :=
⟨_, to_fun⟩

@[simp] lemma to_fun_eq_coe (f : α ↠ β) : f.to_fun = f := rfl

@[simp] lemma coe_mk (f : α → β) (g r) : (surjection.mk f g r : α → β) = f :=
rfl

protected lemma congr_arg {f : α ↠ β} : Π {x x' : α}, x = x' → f x = f x'
| _ _ rfl := rfl

protected lemma congr_fun {f g : α ↠ β} (h : f = g) (x : α) : f x = g x := h ▸ rfl

end surjection

end coes

/-! ### Symmetry -/

section symm

def injection.symm (f : α ↬ β) : β ↠ α := ⟨f.inv_fun, f.to_fun, f.left_inv.right_inverse⟩

def surjection.symm (f : α ↠ β) : β ↬ α := ⟨f.inv_fun, f.to_fun, f.right_inv.left_inverse⟩

@[simp] lemma injection.symm_symm (f : α ↬ β) : f.symm.symm = f :=
by { cases f, refl, }

@[simp] lemma surjection.symm_symm (f : α ↠ β) : f.symm.symm = f :=
by { cases f, refl, }

/-- See Note [custom simps projection] -/
def injection.simps.inv_fun (e : α ↬ β) : β → α := e.symm

initialize_simps_projections injection (to_fun → apply, inv_fun → symm_apply)

/-- See Note [custom simps projection] -/
def surjection.simps.inv_fun (e : α ↠ β) : β → α := e.symm

initialize_simps_projections surjection (to_fun → apply, inv_fun → symm_apply)

@[simp] lemma injection.symm_apply_apply (e : α ↬ β) (x : α) : e.symm (e x) = x :=
e.left_inv x

@[simp] lemma surjection.apply_symm_apply (e : α ↠ β) (x : β) : e (e.symm x) = x :=
e.right_inv x

@[simp] lemma injection.symm_comp_self (e : α ↬ β) : e.symm ∘ e = id := funext e.symm_apply_apply

@[simp] lemma surjection.self_comp_symm (e : α ↠ β) : e ∘ e.symm = id := funext e.apply_symm_apply

end symm

/-! ### Extensionality -/

section ext

@[ext] lemma injection.ext {f g : α ↬ β}
  (H : ∀ x, f x = g x) (H_symm : ∀ x, f.symm x = g.symm x) : f = g :=
begin
  cases f,
  cases g,
  congr,
  exact funext H,
  exact funext H_symm,
end

@[ext] lemma surjection.ext {f g : α ↠ β}
  (H : ∀ x, f x = g x) (H_symm : ∀ x, f.symm x = g.symm x) : f = g :=
begin
  cases f,
  cases g,
  congr,
  exact funext H,
  exact funext H_symm,
end

end ext

/-! ### Composition and identity -/

section comp

namespace injection

def id (α : Sort*) : α ↬ α := ⟨id, id, λ _, rfl⟩

@[simp] lemma id_apply (x : α) : id α x = x := rfl

def comp (f : β ↬ γ) (g : α ↬ β) : α ↬ γ:=
⟨f ∘ g, g.inv_fun ∘ f.inv_fun, f.left_inv.comp g.left_inv⟩

@[simp] lemma comp_id (f : α ↬ β) : f.comp (id α) = f := ext (λ _, rfl) (λ _, rfl)

@[simp] lemma id_comp (f : α ↬ β) : (id β).comp f = f := ext (λ _, rfl) (λ _, rfl)

@[simp] lemma comp_apply (f : β ↬ γ) (g : α ↬ β) (x : α) : (f.comp g) x = f (g x) := rfl

@[simp] lemma symm_comp_apply (f : β ↬ γ) (g : α ↬ β) (x : γ) :
  (f.comp g).symm x = g.symm (f.symm x) := rfl

lemma comp_assoc (f : γ ↬ δ) (g : β ↬ γ) (h : α ↬ β) :
  (f.comp g).comp h = f.comp (g.comp h) :=
by ext; simp

end injection

namespace surjection

def id (α : Sort*) : α ↠ α := ⟨id, id, λ _, rfl⟩

@[simp] lemma id_apply (x : α) : id α x = x := rfl

def comp (f : β ↠ γ) (g : α ↠ β) : α ↠ γ:=
⟨f ∘ g, g.inv_fun ∘ f.inv_fun, f.right_inv.comp g.right_inv⟩

@[simp] lemma comp_id (f : α ↠ β) : f.comp (id α) = f := ext (λ _, rfl) (λ _, rfl)

@[simp] lemma id_comp (f : α ↠ β) : (id β).comp f = f := ext (λ _, rfl) (λ _, rfl)

@[simp] lemma comp_apply (f : β ↠ γ) (g : α ↠ β) (x : α) : (f.comp g) x = f (g x) := rfl

@[simp] lemma symm_comp_apply (f : β ↠ γ) (g : α ↠ β) (x : γ) :
  (f.comp g).symm x = g.symm (f.symm x) := rfl

lemma comp_assoc (f : γ ↠ δ) (g : β ↠ γ) (h : α ↠ β) :
  (f.comp g).comp h = f.comp (g.comp h) :=
by ext; simp

end surjection

end comp

/-! ### Properties -/

section aliases

protected lemma injection.left_inverse (e : α ↬ β) : left_inverse e.symm e :=
e.left_inv

protected lemma injection.injective (e : α ↬ β) : injective e :=
e.left_inv.injective

protected lemma surjection.right_inverse (e : α ↠ β) : function.right_inverse e.symm e :=
e.right_inv

protected lemma surjection.surjective (e : α ↠ β) : surjective e :=
e.right_inv.surjective

end aliases

/-! ### Classical constructions -/

section classical

/-- Construct a `α ↬ β` from a proof of injectivity of a function. -/
noncomputable def function.injective.to_injection {α} [nonempty α]
  {f : α → β} (hf : injective f) :
  α ↬ β :=
⟨f, inv_fun f, left_inverse_inv_fun hf⟩

/-- Construct a `α ↬ β` from a proof of surjectivity of a function. -/
noncomputable def function.surjective.to_surjection {f : α → β} (hf : surjective f) :
  α ↠ β :=
⟨f, surj_inv hf, right_inverse_surj_inv hf⟩

end classical
