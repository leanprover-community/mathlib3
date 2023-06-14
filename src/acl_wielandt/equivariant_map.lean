/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import algebra.group.defs
import data.set.pointwise.basic
import group_theory.group_action.defs
import .for_mathlib.set

-- import data.finset.pointwise
-- import group_theory.group_action.sub_mul_action
-- import group_theory.group_action.fixing_subgroup

/-! Equivariant maps

In this file, we adapt the formalism of semi-linear maps (see `linear_map.lean`)
to the context of group actions.
This generalizes the notion defined as `mul_action_hom` in `group_action.lean`.

We define :

* `equivariant_map φ α β`, `α →ₑ[φ] β` : an equivariant map between to `has_smul`.
This means that `φ : M → N` is a map, `has_smul M α`, `has_smul N β` and `f : α →ₑ[φ] β`
satisfies `f(m • a) = φ(m) • f(a)`.

* composition of such maps, identities, inverses when possible

* some pointwise lemmas.

We also introduce the notation `α →[M] β` to mean `α →ₑ[id M] β`.

* `is_equivariant φ f` is a predicate that says that `f : α → β`
is equivariant with respect to `φ`.

## TODO

If this is to replace `mul_action_hom`,
then one has to rewrite the rest of `group_action.lean`

-/

/-- Equivariant maps -/
structure equivariant_map {M N : Type*} (φ : M → N)
  (α : Type*) (β : Type*) [has_smul M α] [has_smul N β] :=
(to_fun : α → β)
(map_smul' : ∀ (m : M) (a : α), to_fun (m • a) = φ(m) • to_fun (a))

notation α ` →ₑ[`:25 φ:25 `] `:0 β:0 := equivariant_map φ α β
notation α ` →[`:25 M:25 `] `:0 β:0 := equivariant_map (@id M) α β

/-- Equivariant maps (unbundled version) -/
structure is_equivariant_map {M N α β: Type*} [has_smul M α] [has_smul N β] (φ : M → N) (f : α → β) : Prop :=
(map_smul : ∀ (m : M) (a : α), f(m • a) = φ(m) • f(a))

-- ACL : I don't understand this, and this does not work as intended!
/-- `equivariant_map_class F α β` states that `F` is a type of equivariant maps.
You should declare an instance of this typeclass when you extend `equivariant_map`.
-/
class equivariant_map_class (F : Type*) (α β : out_param $ Type*)
  (M N : Type*) (φ : M → N) [has_smul M α] [has_smul N β]
  extends fun_like F α (λ _, β) :=
(map_smul : ∀ (f : F) (m : M) (a : α), f (m • a) = φ(m) • f(a))

/-- Predicate stating that a map is equivariant -/
theorem is_equivariant {α β M N : Type*} {φ : M → N} [has_smul M α] [has_smul N β]
  (f : α →ₑ[φ] β) : is_equivariant_map φ f.to_fun := ⟨f.map_smul'⟩

namespace equivariant_map

section has_smul

variables {α β M N : Type*} {φ : M → N} [has_smul M α] [has_smul N β]

/-- The map on scalars underlying an equivariant map -/
def to_smul_map (f : α →ₑ[φ] β) := φ

-- ACL : I copied a few of them from `group_theory.hom.group_action.lean` and `linear_map.lean`
-- but I don't really know what I'm doing

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (α →ₑ[φ] β) (λ _, α → β) := ⟨equivariant_map.to_fun⟩

@[simp] lemma to_fun_eq_coe {f : α →ₑ[φ] β} : f.to_fun = (f : α → β) := rfl

@[simp] lemma map_smul (f : α →ₑ[φ] β) (m : M) (a : α) : f (m • a) = φ(m) • f(a) :=
f.map_smul' m a

@[ext] theorem ext : ∀ {f g : α →ₑ[φ] β}, (∀ a, f a = g a) → f = g
| ⟨f, _⟩ ⟨g, _⟩ H := by { congr' 1 with a, exact H a }

theorem ext_iff {f g : α →ₑ[φ] β} : f = g ↔ ∀ a, f a = g a :=
⟨λ H a, by rw H, ext⟩

protected lemma congr_fun {f g : α →ₑ[φ] β} (h : f = g) (a : α) : f a = g a := h ▸ rfl

/-- Copy of a `equivariant_map` with a new `to_fun` equal to the old one.
Useful to fix definitional equalities. -/
protected def copy (f : α →ₑ[φ] β) (f' : α → β) (h : f' = ⇑f) : α →ₑ[φ] β :=
{ to_fun := f',
  map_smul' := h.symm ▸ f.map_smul' }

initialize_simps_projections equivariant_map (to_fun → apply)

@[simp] lemma coe_mk {φ : M → N} (f : α → β) (h) :
  ((equivariant_map.mk f h : α →ₑ[φ] β) : α → β) = f := rfl

/- Why does this not work ?
theorem coe_injective : @function.injective (α →ₑ[φ] β) (α → β) coe_fn :=
fun_like.coe_injective

protected lemma congr_arg {x x' : α} {f : α →ₑ[φ] β} : x = x' → f x = f x' :=
fun_like.congr_arg f
-/

/-- Two equal maps on scalars give rise to an equivariant map for identity -/
def of_eq {φ' : M → N} (h : φ = φ') (f : α →ₑ[φ] β) : α →ₑ[φ'] β := {
to_fun := f.to_fun,
map_smul' := λ m a, h ▸ (f.map_smul' m a) }

@[simp] lemma of_eq_coe {φ' : M → N} (h : φ = φ') (f : α →ₑ[φ] β) :
  (f.of_eq h).to_fun = f.to_fun := rfl

@[simp] lemma of_eq_apply {φ' : M → N} (h : φ = φ') (f : α →ₑ[φ] β) (a : α) :
  (f.of_eq h) a = f a := rfl

variables (M)

/-- The identity map as an equivariant map. -/
protected def id : α →[M] α :=
⟨id, λ _ _, rfl⟩

@[simp] lemma id_apply (a : α) : equivariant_map.id M a = a := rfl

@[simp, norm_cast] lemma id_coe : ((equivariant_map.id M : α →[M] α) : α → α) = _root_.id := rfl


variables {M}

section composition

/-- Composition of two equivariant maps. -/
variables {P γ : Type*}  [has_smul P γ] {ψ : N → P}

/-- Composition of equivariant maps -/
def comp (g : β →ₑ[ψ] γ) (f : α →ₑ[φ] β) : α →ₑ[ψ ∘ φ] γ :=
⟨g ∘ f, λ m a, calc
g (f (m • a)) = g (φ m • f a) : by rw f.map_smul
          ... = ψ (φ m) • g (f a) : g.map_smul _ _⟩

@[simp] lemma comp_apply (g : β →ₑ[ψ] γ) (f : α →ₑ[φ] β) (a : α) : g.comp f a = g (f a) := rfl

@[simp] lemma id_comp  (f : α →ₑ[φ] β) :
  ((equivariant_map.id N).comp f).of_eq (function.comp.left_id φ) = f :=
ext $ λ x, by rw [of_eq_apply, comp_apply, id_apply]

@[simp] lemma comp_id  (f : α →ₑ[φ] β) :
  (f.comp (equivariant_map.id M)).of_eq (function.comp.right_id φ) = f :=
ext $ λ x, by rw [of_eq_apply, comp_apply, id_apply]

variables {Q δ : Type*} [has_smul Q δ] {χ : P → Q}
@[simp] lemma comp_assoc (h : γ →ₑ[χ] δ) (g : β →ₑ[ψ] γ) (f : α →ₑ[φ] β) :
  h.comp (g.comp f) = (h.comp g).comp f := ext $ λ x, rfl

end composition

section inverse

variables {ψ : N → M}

/-- The inverse of a bijective equivariant map is equivariant with
respect to any right inverse of the scalar map -/

@[simps] def inverse
  (k₂ : function.right_inverse ψ φ)
  (f : α →ₑ[φ] β) (g : β → α)
  (h₁ : function.left_inverse g f) (h₂ : function.right_inverse g f) :
  β →ₑ[ψ] α :=
{ to_fun    := g,
  map_smul' := λ n b,
    calc g (n • b) = g (φ(ψ(n)) • (f (g b))) : by rw [k₂, h₂]
               ... = g (f (ψ(n) • (g b))) : by rw f.map_smul
               ... = ψ(n) • g b : by rw h₁, }

/-- Inverse composed with map is identity (if the map on scalars is bijective) -/
@[simp] lemma inverse_comp
  (k₁ : function.left_inverse ψ φ) (k₂ : function.right_inverse ψ φ)
  (f : α →ₑ[φ] β) (g : β → α)
  (h₁ : function.left_inverse g f) (h₂ : function.right_inverse g f) :
  ((inverse k₂ f g h₁ h₂).comp f).of_eq (function.left_inverse.id k₁) = equivariant_map.id M :=
ext $ λ a, by rw [of_eq_apply, comp_apply, inverse_apply, id_coe, id.def, h₁]

/-- Map composed with inverse is identity -/
@[simp] lemma comp_inverse
  (k₂ : function.right_inverse ψ φ)
  (f : α →ₑ[φ] β) (g : β → α)
  (h₁ : function.left_inverse g f) (h₂ : function.right_inverse g f) :
  (f.comp (inverse k₂ f g h₁ h₂)).of_eq (function.right_inverse.id k₂) = equivariant_map.id N :=
ext $ λ a, by rw [of_eq_apply, comp_apply, inverse_apply, id_coe, id.def, h₂]

-- Necessary ?
@[simp] lemma inverse_inverse
  (k₁ : function.left_inverse ψ φ) (k₂ : function.right_inverse ψ φ)
  (f : α →ₑ[φ] β) (g : β → α)
  (h₁ : function.left_inverse g f) (h₂ : function.right_inverse g f) :
  inverse k₁ (inverse k₂ f g h₁ h₂) ⇑f h₂ h₁ = f :=
ext $ λ b, by simp only [to_fun_eq_coe, inverse_apply]

end inverse

section pointwise

open_locale pointwise

variable {f : α →ₑ[φ] β}

/-- Image of translated set under an action -/
@[simp] lemma image_smul_setₑ (m : M) (s : set α) :
  f '' (m • s) = (φ m) • f '' s :=
begin
  change f.to_fun '' ((λ a, m • a) '' s) =
    (λ b, φ m • b) '' (f.to_fun '' s),
  simp only [set.image_image],
  apply set.image_congr,
  intros a _, rw f.map_smul'
end

variables {β₁ : Type*} [has_smul M β₁] {f₁ : α →[M] β₁}

lemma image_smul_set (m : M) (s : set α) :
  f₁ '' (m • s) = m • f₁ '' s :=
by simp

/-- Translation of preimage is contained in preimage of translation -/
lemma preimage_smul_setₑ_le {m : M} (t : set β) :
  m • f ⁻¹' t ⊆ f ⁻¹' (φ m • t) :=
begin
  rintros x ⟨y, hy, rfl⟩,
  refine ⟨f y, hy, by rw map_smul⟩
end

lemma preimage_smul_set_le {m : M} (t : set β₁) :
  m • f₁ ⁻¹' t ⊆ f₁ ⁻¹' (m • t) := preimage_smul_setₑ_le t

/-- When the action is bijective, preimage of translation equals translation of preimage -/
lemma preimage_smul_setₑ' {m : M}
  (hmα : function.bijective (λ a : α, m • a))
  (hmβ : function.bijective (λ b : β, φ(m) • b))
  (t : set β) :
  f ⁻¹' (φ m • t) = m • f ⁻¹' t :=
begin
  apply set.subset.antisymm,
  { rintros x ⟨y, yt, hy⟩,
    obtain ⟨x', hx' : m • x' = x⟩ := hmα.surjective x,
    use x', apply and.intro _ hx',
    simp, simp only [←hx', map_smul] at hy,
    rw ← hmβ.injective hy, exact yt },
  exact preimage_smul_setₑ_le t
end

lemma preimage_smul_set' {m : M}
  (hmα : function.bijective (λ a : α, m • a))
  (hmβ : function.bijective (λ b : β₁, m • b))
  (t : set β₁) :
  f₁ ⁻¹' (m • t) = m • f₁ ⁻¹' t :=
preimage_smul_setₑ' hmα hmβ t


end pointwise

end has_smul

section group


variables {M N : Type*} [group M] [group N] {φ : M → N}
variables {α β : Type*} [mul_action M α] [mul_action N β]
variable {f : α →ₑ[φ] β}

open_locale pointwise

/-- For an equivariant map between group actions,
preimage of translation equals translation of preimage -/
lemma preimage_smul_setₑ {m : M} (t : set β) :
  f ⁻¹' (φ m • t) = m • f ⁻¹' t :=
preimage_smul_setₑ' (mul_action.bijective m) (mul_action.bijective (φ(m))) t

variables {β₁ : Type*} [mul_action M β₁] {f₁ : α →[M] β₁}
lemma preimage_smul_set {m : M}
  (t : set β₁) :
  f₁ ⁻¹' (m • t) = m • f₁ ⁻¹' t :=
preimage_smul_set' (mul_action.bijective m) (mul_action.bijective m) t

end group

end equivariant_map


section pretransitivity

open mul_action

variables {M : Type*} [group M] {α : Type*} [mul_action M α]
variables {N β : Type*} [group N] [mul_action N β]

lemma is_pretransitive_of_surjective_map
  {φ : M → N} {f : α →ₑ[φ] β} (hf : function.surjective f)
  (h : is_pretransitive M α) : is_pretransitive N β :=
begin
  apply mul_action.is_pretransitive.mk,
  intros x y, let h_eq := h.exists_smul_eq,
  obtain ⟨x', rfl⟩ := hf x,
  obtain ⟨y', rfl⟩ := hf y,
  obtain ⟨g, rfl⟩ := h_eq x' y',
  use φ g, simp only [equivariant_map.map_smul]
end

/-
lemma _root_.mul_action.is_pretransitive.exists_smul_eq' (hN : is_pretransitive M α) :
  ∀ (x y : α), ∃ (g : M), g • x = y :=
begin
sorry
end -/

lemma is_pretransitive_of_bijective_map_iff
  {φ : M → N} {f : α →ₑ[φ] β}
  (hφ : function.surjective φ)
  (hf : function.bijective f) :
  is_pretransitive M α ↔ is_pretransitive N β :=
begin
  split,
  apply is_pretransitive_of_surjective_map hf.surjective,
  { introI hN,
  -- let hN_heq := hN.exists_smul_eq,
    apply is_pretransitive.mk,
    intros x y,
    obtain ⟨k, hk⟩ := exists_smul_eq N (f x) (f y),
    obtain ⟨g, rfl⟩ := hφ k,
    use g,
    apply hf.injective,
    simp only [hk, equivariant_map.map_smul] }
end

end pretransitivity

#lint
