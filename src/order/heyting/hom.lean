/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.hom.lattice

/-!
# Heyting algebra morphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A Heyting homomorphism between two Heyting algebras is a bounded lattice homomorphism that preserves
Heyting implication.

We use the `fun_like` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `heyting_hom`: Heyting homomorphisms.
* `coheyting_hom`: Co-Heyting homomorphisms.
* `biheyting_hom`: Bi-Heyting homomorphisms.

## Typeclasses

* `heyting_hom_class`
* `coheyting_hom_class`
* `biheyting_hom_class`
-/

open function

variables {F α β γ δ : Type*}

/-- The type of Heyting homomorphisms from `α` to `β`. Bounded lattice homomorphisms that preserve
Heyting implication. -/
@[protect_proj]
structure heyting_hom (α β : Type*) [heyting_algebra α] [heyting_algebra β]
  extends lattice_hom α β :=
(map_bot' : to_fun ⊥ = ⊥)
(map_himp' : ∀ a b, to_fun (a ⇨ b) = to_fun a ⇨ to_fun b)

/-- The type of co-Heyting homomorphisms from `α` to `β`. Bounded lattice homomorphisms that
preserve difference. -/
@[protect_proj]
structure coheyting_hom (α β : Type*) [coheyting_algebra α] [coheyting_algebra β]
  extends lattice_hom α β :=
(map_top' : to_fun ⊤ = ⊤)
(map_sdiff' : ∀ a b, to_fun (a \ b) = to_fun a \ to_fun b)

/-- The type of bi-Heyting homomorphisms from `α` to `β`. Bounded lattice homomorphisms that
preserve Heyting implication and difference. -/
@[protect_proj]
structure biheyting_hom (α β : Type*) [biheyting_algebra α] [biheyting_algebra β]
  extends lattice_hom α β :=
(map_himp' : ∀ a b, to_fun (a ⇨ b) = to_fun a ⇨ to_fun b)
(map_sdiff' : ∀ a b, to_fun (a \ b) = to_fun a \ to_fun b)

/-- `heyting_hom_class F α β` states that `F` is a type of Heyting homomorphisms.

You should extend this class when you extend `heyting_hom`. -/
class heyting_hom_class (F : Type*) (α β : out_param $ Type*) [heyting_algebra α]
  [heyting_algebra β] extends lattice_hom_class F α β :=
(map_bot (f : F) : f ⊥ = ⊥)
(map_himp (f : F) : ∀ a b, f (a ⇨ b) = f a ⇨ f b)

/-- `coheyting_hom_class F α β` states that `F` is a type of co-Heyting homomorphisms.

You should extend this class when you extend `coheyting_hom`. -/
class coheyting_hom_class (F : Type*) (α β : out_param $ Type*) [coheyting_algebra α]
  [coheyting_algebra β] extends lattice_hom_class F α β :=
(map_top (f : F) : f ⊤ = ⊤)
(map_sdiff (f : F) : ∀ a b, f (a \ b) = f a \ f b)

/-- `biheyting_hom_class F α β` states that `F` is a type of bi-Heyting homomorphisms.

You should extend this class when you extend `biheyting_hom`. -/
class biheyting_hom_class (F : Type*) (α β : out_param $ Type*) [biheyting_algebra α]
  [biheyting_algebra β] extends lattice_hom_class F α β :=
(map_himp (f : F) : ∀ a b, f (a ⇨ b) = f a ⇨ f b)
(map_sdiff (f : F) : ∀ a b, f (a \ b) = f a \ f b)

export heyting_hom_class (map_himp)
export coheyting_hom_class (map_sdiff)

attribute [simp] map_himp map_sdiff

@[priority 100] -- See note [lower instance priority]
instance heyting_hom_class.to_bounded_lattice_hom_class [heyting_algebra α] [heyting_algebra β]
  [heyting_hom_class F α β] : bounded_lattice_hom_class F α β :=
{ map_top := λ f, by rw [←@himp_self α _ ⊥, ←himp_self, map_himp],
  ..‹heyting_hom_class F α β› }

@[priority 100] -- See note [lower instance priority]
instance coheyting_hom_class.to_bounded_lattice_hom_class [coheyting_algebra α]
  [coheyting_algebra β] [coheyting_hom_class F α β] : bounded_lattice_hom_class F α β :=
{ map_bot := λ f, by rw [←@sdiff_self α _ ⊤, ←sdiff_self, map_sdiff],
  ..‹coheyting_hom_class F α β› }

@[priority 100] -- See note [lower instance priority]
instance biheyting_hom_class.to_heyting_hom_class [biheyting_algebra α] [biheyting_algebra β]
  [biheyting_hom_class F α β] :
  heyting_hom_class F α β :=
{ map_bot := λ f, by rw [←@sdiff_self α _ ⊤, ←sdiff_self, biheyting_hom_class.map_sdiff],
  ..‹biheyting_hom_class F α β› }

@[priority 100] -- See note [lower instance priority]
instance biheyting_hom_class.to_coheyting_hom_class [biheyting_algebra α] [biheyting_algebra β]
  [biheyting_hom_class F α β] :
  coheyting_hom_class F α β :=
{ map_top := λ f, by rw [←@himp_self α _ ⊥, ←himp_self, map_himp],
  ..‹biheyting_hom_class F α β› }

@[priority 100] -- See note [lower instance priority]
instance order_iso_class.to_heyting_hom_class [heyting_algebra α] [heyting_algebra β]
  [order_iso_class F α β] :
  heyting_hom_class F α β :=
{ map_himp := λ f a b, eq_of_forall_le_iff $ λ c,
    by { simp only [←map_inv_le_iff, le_himp_iff], rw ←order_iso_class.map_le_map_iff f, simp },
  ..order_iso_class.to_bounded_lattice_hom_class }

@[priority 100] -- See note [lower instance priority]
instance order_iso_class.to_coheyting_hom_class [coheyting_algebra α] [coheyting_algebra β]
  [order_iso_class F α β] :
  coheyting_hom_class F α β :=
{ map_sdiff := λ f a b, eq_of_forall_ge_iff $ λ c,
    by { simp only [←le_map_inv_iff, sdiff_le_iff], rw ←order_iso_class.map_le_map_iff f, simp },
  ..order_iso_class.to_bounded_lattice_hom_class }

@[priority 100] -- See note [lower instance priority]
instance order_iso_class.to_biheyting_hom_class [biheyting_algebra α] [biheyting_algebra β]
  [order_iso_class F α β] :
  biheyting_hom_class F α β :=
{ map_himp := λ f a b, eq_of_forall_le_iff $ λ c,
    by { simp only [←map_inv_le_iff, le_himp_iff], rw ←order_iso_class.map_le_map_iff f, simp },
  map_sdiff := λ f a b, eq_of_forall_ge_iff $ λ c,
    by { simp only [←le_map_inv_iff, sdiff_le_iff], rw ←order_iso_class.map_le_map_iff f, simp },
  ..order_iso_class.to_lattice_hom_class }

/-- This can't be an instance because of typeclass loops. -/
@[reducible] -- See note [reducible non instances]
def bounded_lattice_hom_class.to_biheyting_hom_class [boolean_algebra α] [boolean_algebra β]
  [bounded_lattice_hom_class F α β] :
  biheyting_hom_class F α β :=
{ map_himp := λ f a b, by rw [himp_eq, himp_eq, map_sup, (is_compl_compl.map _).compl_eq],
  map_sdiff := λ f a b, by rw [sdiff_eq, sdiff_eq, map_inf, (is_compl_compl.map _).compl_eq],
   ..‹bounded_lattice_hom_class F α β› }

section heyting_algebra
variables [heyting_algebra α] [heyting_algebra β] [heyting_hom_class F α β] (f : F)
include β

@[simp] lemma map_compl (a : α) : f aᶜ = (f a)ᶜ := by rw [←himp_bot, ←himp_bot, map_himp, map_bot]

@[simp] lemma map_bihimp (a b : α) : f (a ⇔ b) = f a ⇔ f b :=
by simp_rw [bihimp, map_inf, map_himp]

-- TODO: `map_bihimp`

end heyting_algebra

section coheyting_algebra
variables [coheyting_algebra α] [coheyting_algebra β] [coheyting_hom_class F α β] (f : F)
include β

@[simp] lemma map_hnot (a : α) : f ￢a = ￢f a :=
by rw [←top_sdiff', ←top_sdiff', map_sdiff, map_top]

@[simp] lemma map_symm_diff (a b : α) : f (a ∆ b) = f a ∆ f b :=
by simp_rw [symm_diff, map_sup, map_sdiff]

end coheyting_algebra

instance [heyting_algebra α] [heyting_algebra β] [heyting_hom_class F α β] :
  has_coe_t F (heyting_hom α β) :=
⟨λ f, { to_fun := f,
        map_sup' := map_sup f,
        map_inf' := map_inf f,
        map_bot' := map_bot f,
        map_himp' := map_himp f }⟩

instance [coheyting_algebra α] [coheyting_algebra β] [coheyting_hom_class F α β] :
  has_coe_t F (coheyting_hom α β) :=
⟨λ f, { to_fun := f,
        map_sup' := map_sup f,
        map_inf' := map_inf f,
        map_top' := map_top f,
        map_sdiff' := map_sdiff f }⟩

instance [biheyting_algebra α] [biheyting_algebra β] [biheyting_hom_class F α β] :
  has_coe_t F (biheyting_hom α β) :=
⟨λ f, { to_fun := f,
        map_sup' := map_sup f,
        map_inf' := map_inf f,
        map_himp' := map_himp f,
        map_sdiff' := map_sdiff f }⟩

namespace heyting_hom
variables [heyting_algebra α] [heyting_algebra β] [heyting_algebra γ] [heyting_algebra δ]

instance : heyting_hom_class (heyting_hom α β) α β :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f; obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g; congr',
  map_sup := λ f, f.map_sup',
  map_inf := λ f, f.map_inf',
  map_bot := λ f, f.map_bot',
  map_himp := heyting_hom.map_himp' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (heyting_hom α β) (λ _, α → β) := fun_like.has_coe_to_fun

@[simp] lemma to_fun_eq_coe {f : heyting_hom α β} : f.to_fun = (f : α → β) := rfl

@[ext] lemma ext {f g : heyting_hom α β} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

/-- Copy of a `heyting_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : heyting_hom α β) (f' : α → β) (h : f' = f) : heyting_hom α β :=
{ to_fun := f',
  map_sup' := by simpa only [h] using map_sup f,
  map_inf' := by simpa only [h] using map_inf f,
  map_bot' := by simpa only [h] using map_bot f,
  map_himp' := by simpa only [h] using map_himp f }

@[simp] lemma coe_copy (f : heyting_hom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' := rfl
lemma copy_eq (f : heyting_hom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f := fun_like.ext' h

variables (α)

/-- `id` as a `heyting_hom`. -/
protected def id : heyting_hom α α :=
{ to_lattice_hom := lattice_hom.id _,
  map_himp' := λ a b, rfl,
  ..bot_hom.id _ }

@[simp] lemma coe_id : ⇑(heyting_hom.id α) = id := rfl

variables {α}

@[simp] lemma id_apply (a : α) : heyting_hom.id α a = a := rfl

instance : inhabited (heyting_hom α α) := ⟨heyting_hom.id _⟩

instance : partial_order (heyting_hom α β) := partial_order.lift _ fun_like.coe_injective

/-- Composition of `heyting_hom`s as a `heyting_hom`. -/
def comp (f : heyting_hom β γ) (g : heyting_hom α β) : heyting_hom α γ :=
{ to_fun := f ∘ g,
  map_bot' := by simp,
  map_himp' := λ a b, by simp,
  ..f.to_lattice_hom.comp g.to_lattice_hom }

variables {f f₁ f₂ : heyting_hom α β} {g g₁ g₂ : heyting_hom β γ}

@[simp] lemma coe_comp (f : heyting_hom β γ) (g : heyting_hom α β) : ⇑(f.comp g) = f ∘ g := rfl
@[simp] lemma comp_apply (f : heyting_hom β γ) (g : heyting_hom α β) (a : α) :
 f.comp g a = f (g a) := rfl
@[simp] lemma comp_assoc (f : heyting_hom γ δ) (g : heyting_hom β γ) (h : heyting_hom α β) :
  (f.comp g).comp h = f.comp (g.comp h) := rfl
@[simp] lemma comp_id (f : heyting_hom α β) : f.comp (heyting_hom.id α) = f := ext $ λ a, rfl
@[simp] lemma id_comp (f : heyting_hom α β) : (heyting_hom.id β).comp f = f := ext $ λ a, rfl

lemma cancel_right (hf : surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, ext $ hf.forall.2 $ fun_like.ext_iff.1 h, congr_arg _⟩

lemma cancel_left (hg : injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, heyting_hom.ext $ λ a, hg $ by rw [←comp_apply, h, comp_apply], congr_arg _⟩

end heyting_hom

namespace coheyting_hom
variables [coheyting_algebra α] [coheyting_algebra β] [coheyting_algebra γ] [coheyting_algebra δ]

instance : coheyting_hom_class (coheyting_hom α β) α β :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f; obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g; congr',
  map_sup := λ f, f.map_sup',
  map_inf := λ f, f.map_inf',
  map_top := λ f, f.map_top',
  map_sdiff := coheyting_hom.map_sdiff' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (coheyting_hom α β) (λ _, α → β) := fun_like.has_coe_to_fun

@[simp] lemma to_fun_eq_coe {f : coheyting_hom α β} : f.to_fun = (f : α → β) := rfl

@[ext] lemma ext {f g : coheyting_hom α β} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

/-- Copy of a `coheyting_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : coheyting_hom α β) (f' : α → β) (h : f' = f) : coheyting_hom α β :=
{ to_fun := f',
  map_sup' := by simpa only [h] using map_sup f,
  map_inf' := by simpa only [h] using map_inf f,
  map_top' := by simpa only [h] using map_top f,
  map_sdiff' := by simpa only [h] using map_sdiff f }

@[simp]
lemma coe_copy (f : coheyting_hom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' := rfl

lemma copy_eq (f : coheyting_hom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f := fun_like.ext' h

variables (α)

/-- `id` as a `coheyting_hom`. -/
protected def id : coheyting_hom α α :=
{ to_lattice_hom := lattice_hom.id _,
  map_sdiff' := λ a b, rfl,
  ..top_hom.id _ }

@[simp] lemma coe_id : ⇑(coheyting_hom.id α) = id := rfl

variables {α}

@[simp] lemma id_apply (a : α) : coheyting_hom.id α a = a := rfl

instance : inhabited (coheyting_hom α α) := ⟨coheyting_hom.id _⟩

instance : partial_order (coheyting_hom α β) := partial_order.lift _ fun_like.coe_injective

/-- Composition of `coheyting_hom`s as a `coheyting_hom`. -/
def comp (f : coheyting_hom β γ) (g : coheyting_hom α β) : coheyting_hom α γ :=
{ to_fun := f ∘ g,
  map_top' := by simp,
  map_sdiff' := λ a b, by simp,
  ..f.to_lattice_hom.comp g.to_lattice_hom }

variables {f f₁ f₂ : coheyting_hom α β} {g g₁ g₂ : coheyting_hom β γ}

@[simp] lemma coe_comp (f : coheyting_hom β γ) (g : coheyting_hom α β) : ⇑(f.comp g) = f ∘ g := rfl
@[simp] lemma comp_apply (f : coheyting_hom β γ) (g : coheyting_hom α β) (a : α) :
 f.comp g a = f (g a) := rfl
@[simp] lemma comp_assoc (f : coheyting_hom γ δ) (g : coheyting_hom β γ) (h : coheyting_hom α β) :
  (f.comp g).comp h = f.comp (g.comp h) := rfl
@[simp] lemma comp_id (f : coheyting_hom α β) : f.comp (coheyting_hom.id α) = f := ext $ λ a, rfl
@[simp] lemma id_comp (f : coheyting_hom α β) : (coheyting_hom.id β).comp f = f := ext $ λ a, rfl

lemma cancel_right (hf : surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, ext $ hf.forall.2 $ fun_like.ext_iff.1 h, congr_arg _⟩

lemma cancel_left (hg : injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, coheyting_hom.ext $ λ a, hg $ by rw [←comp_apply, h, comp_apply], congr_arg _⟩

end coheyting_hom


namespace biheyting_hom
variables [biheyting_algebra α] [biheyting_algebra β] [biheyting_algebra γ] [biheyting_algebra δ]

instance : biheyting_hom_class (biheyting_hom α β) α β :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f; obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g; congr',
  map_sup := λ f, f.map_sup',
  map_inf := λ f, f.map_inf',
  map_himp := λ f, f.map_himp',
  map_sdiff := λ f, f.map_sdiff' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (biheyting_hom α β) (λ _, α → β) := fun_like.has_coe_to_fun

@[simp] lemma to_fun_eq_coe {f : biheyting_hom α β} : f.to_fun = (f : α → β) := rfl

@[ext] lemma ext {f g : biheyting_hom α β} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

/-- Copy of a `biheyting_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : biheyting_hom α β) (f' : α → β) (h : f' = f) : biheyting_hom α β :=
{ to_fun := f',
  map_sup' := by simpa only [h] using map_sup f,
  map_inf' := by simpa only [h] using map_inf f,
  map_himp' := by simpa only [h] using map_himp f,
  map_sdiff' := by simpa only [h] using map_sdiff f }

@[simp] lemma coe_copy (f : biheyting_hom α β) (f' : α → β) (h : f' = f) :
  ⇑(f.copy f' h) = f' :=
rfl

lemma copy_eq (f : biheyting_hom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f := fun_like.ext' h

variables (α)

/-- `id` as a `biheyting_hom`. -/
protected def id : biheyting_hom α α :=
{ to_lattice_hom := lattice_hom.id _,
  ..heyting_hom.id _, ..coheyting_hom.id _ }

@[simp] lemma coe_id : ⇑(biheyting_hom.id α) = id := rfl

variables {α}

@[simp] lemma id_apply (a : α) : biheyting_hom.id α a = a := rfl

instance : inhabited (biheyting_hom α α) := ⟨biheyting_hom.id _⟩

instance : partial_order (biheyting_hom α β) := partial_order.lift _ fun_like.coe_injective

/-- Composition of `biheyting_hom`s as a `biheyting_hom`. -/
def comp (f : biheyting_hom β γ) (g : biheyting_hom α β) : biheyting_hom α γ :=
{ to_fun := f ∘ g,
  map_himp' := λ a b, by simp,
  map_sdiff' := λ a b, by simp,
  ..f.to_lattice_hom.comp g.to_lattice_hom }

variables {f f₁ f₂ : biheyting_hom α β} {g g₁ g₂ : biheyting_hom β γ}

@[simp] lemma coe_comp (f : biheyting_hom β γ) (g : biheyting_hom α β) : ⇑(f.comp g) = f ∘ g := rfl
@[simp] lemma comp_apply (f : biheyting_hom β γ) (g : biheyting_hom α β) (a : α) :
 f.comp g a = f (g a) := rfl
@[simp] lemma comp_assoc (f : biheyting_hom γ δ) (g : biheyting_hom β γ) (h : biheyting_hom α β) :
  (f.comp g).comp h = f.comp (g.comp h) := rfl
@[simp] lemma comp_id (f : biheyting_hom α β) : f.comp (biheyting_hom.id α) = f := ext $ λ a, rfl
@[simp] lemma id_comp (f : biheyting_hom α β) : (biheyting_hom.id β).comp f = f := ext $ λ a, rfl

lemma cancel_right (hf : surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, ext $ hf.forall.2 $ fun_like.ext_iff.1 h, congr_arg _⟩

lemma cancel_left (hg : injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, biheyting_hom.ext $ λ a, hg $ by rw [←comp_apply, h, comp_apply], congr_arg _⟩

end biheyting_hom
