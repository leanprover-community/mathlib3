/-
Copyright (c) 2021 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
import representation_theory.basic

/-!
# Morphisms of representations
TODO
-/

universes u v w

open function
open_locale big_operators

section rep_hom
variables (k : Type u) (G : Type v) (M N: Type w)
variables [semiring k] [monoid G] [add_comm_monoid M] [add_comm_monoid N]
variables [module k M] [distrib_mul_action G M] [module k N] [distrib_mul_action G N]

set_option old_structure_cmd true
/-- A homomorphism between representations `M` and `N` over `k` and `G` is a
`k`-linear map which commutes with the `G`-action. -/
@[nolint has_inhabited_instance]
structure rep_hom [representation k G M] [representation k G N] extends linear_map k M N :=
(commutes' : ∀ (g : G) (m : M), to_fun (g • m) = g • to_fun m)

run_cmd tactic.add_doc_string `rep_hom.to_linear_map "Reinterpret an `rep_hom` as a `linear_map`"

infixr ` →ᵣ `:25 := rep_hom _
notation M ` →ᵣ[`:25 k `, ` G `] ` N := rep_hom k G M N

end rep_hom

namespace rep_hom
variables {k : Type u} {G : Type v} {M N: Type w} {ι : Type*}
variables [semiring k] [monoid G] [add_comm_monoid M] [add_comm_monoid N]
variables [module k M] [distrib_mul_action G M] [module k N] [distrib_mul_action G N]
variables [representation k G M] [representation k G N]

instance : has_coe_to_fun (M →ᵣ[k, G] N) := ⟨_, λ f, f.to_fun⟩

initialize_simps_projections rep_hom (to_fun → apply)

@[simp] lemma to_fun_eq_coe (f : M →ᵣ[k, G] N) : f.to_fun = f := rfl

/-- The `distrib_mul_action_hom` underlying a `rep_hom`. -/
def to_distrib_mul_action_hom (f : M →ᵣ[k, G] N) : distrib_mul_action_hom G M N :=
{ to_fun := f,
  map_smul' := f.commutes',
  map_zero' := f.to_linear_map.map_zero,
  map_add' := f.to_linear_map.map_add' }

@[simp] lemma to_distrib_mul_action_hom_coe (f : M →ᵣ[k, G] N) :
  ⇑f.to_distrib_mul_action_hom = f := rfl

/-- convert a linear map to an additive map -/
def to_add_monoid_hom (f : M →ᵣ[k, G] N) : M →+ N :=
{ to_fun := f,
  map_zero' := f.to_linear_map.map_zero,
  map_add' := f.to_linear_map.map_add }

@[simp] lemma to_add_monoid_hom_coe (f : M →ᵣ[k, G] N) : ⇑f.to_add_monoid_hom = f := rfl

@[simp] lemma coe_mk (f : M → N) (h₁ h₂ h₃) :
  ((rep_hom.mk f h₁ h₂ h₃ : M →ᵣ[k, G] N) : M → N) = f := rfl

/-- Identity map as a `rep_hom` -/
def id : M →ᵣ[k, G] M :=
⟨id, λ _ _, rfl, λ _ _, rfl, λ _ _, rfl⟩

lemma id_apply (x : M) :
  @id k G M _ _ _ _ _ _ x = x := rfl

@[simp, norm_cast] lemma id_coe : ((rep_hom.id : M →ᵣ[k, G] M) : M → M) = _root_.id :=
by { ext x, refl }

theorem coe_injective : injective (λ f : M →ᵣ[k, G] N, show M → N, from f) :=
by rintro ⟨f, _⟩ ⟨g, _⟩ ⟨h⟩; congr

@[ext] theorem ext {f g :  M →ᵣ[k, G] N} (H : ∀ x, f x = g x) : f = g :=
coe_injective $ funext H

protected lemma congr_arg {f : M →ᵣ[k, G] N} : Π {x x' : M}, x = x' → f x = f x'
| _ _ rfl := rfl

/-- If two linear maps are equal, they are equal at each point. -/
protected lemma congr_fun {f g :  M →ᵣ[k, G] N} (h : f = g) (x : M) : f x = g x := h ▸ rfl

theorem ext_iff {f g :  M →ᵣ[k, G] N} : f = g ↔ ∀ x, f x = g x :=
⟨by { rintro rfl x, refl }, ext⟩

@[simp] lemma mk_coe (f :  M →ᵣ[k, G] N) (h₁ h₂ h₃) :
  (rep_hom.mk f h₁ h₂ h₃ :  M →ᵣ[k, G] N) = f := ext $ λ _, rfl

variables (f g : M →ᵣ[k, G] N)

@[simp] lemma map_add (x y : M) : f (x + y) = f x + f y := f.map_add' x y

@[simp] lemma map_smul (c : k) (x : M) : f (c • x) = c • f x := f.map_smul' c x

@[simp] lemma map_gsmul (g : G) (x : M) : f (g • x) = g • f x :=
f.to_distrib_mul_action_hom.map_smul' g x

@[simp] lemma map_zero : f 0 = 0 := f.to_distrib_mul_action_hom.map_zero

@[simp] lemma map_sum {t : finset ι} {g : ι → M} :
  f (∑ i in t, g i) = (∑ i in t, f (g i)) :=
f.to_add_monoid_hom.map_sum _ _

end rep_hom
