/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/

import linear_algebra.linear_pmap
import topology.algebra.module.basic

/-!
# Continuous Linear Pmap

A `continuous_linear_pmap 𝕜 E F` or `E →L.[𝕜] F` is a continuous linear map from a submodule
of `E` to `F`.
This file contains all properties that hold in general topological vector spaces.

## Main definitions

* `continuous_linear_pmap`: a partially defined continuous linear map

## Tags

partially defined continuous linear map
-/

variables {𝕜 E F : Type*}
variables [ring 𝕜] [add_comm_group E] [module 𝕜 E] [add_comm_group F] [module 𝕜 F]
variables [topological_space E] [topological_space F]

/-- A `continuous_linear_pmap 𝕜 E F` or `E →L.[𝕜] F` is a continuous linear map from a submodule
of `E` to `F`. -/
structure continuous_linear_pmap (𝕜 E F : Type*)
  [ring 𝕜] [add_comm_group E] [module 𝕜 E] [add_comm_group F] [module 𝕜 F]
  [topological_space E] [topological_space F]
  extends (linear_pmap 𝕜 E F) :=
(cont : continuous to_linear_pmap.to_fun)

notation E ` →L.[`:25 R:25 `] `:0 F:0 := continuous_linear_pmap R E F

namespace continuous_linear_pmap

instance : has_coe (E →L.[𝕜] F) (linear_pmap 𝕜 E F) := ⟨λ f, f.to_linear_pmap⟩

/-- A continuous partial linear map as a continuous linear map. -/
def to_cont_fun (f : E →L.[𝕜] F) : f.domain →L[𝕜] F :=
⟨f.to_fun, f.cont⟩

-- make the coercion the preferred form
@[simp] lemma to_linear_map_eq_coe (f : E →L.[𝕜] F) : f.to_linear_pmap = f := rfl

lemma to_linear_pmap_apply (f : E →L.[𝕜] F) {x : f.domain} : f.to_linear_pmap x = f x := rfl

theorem coe_injective : function.injective (coe : (E →L.[𝕜] F) → (linear_pmap 𝕜 E F)) :=
by { intros f g H, cases f, cases g, congr' }

@[simp] lemma coe_domain (f : E →L.[𝕜] F) : (f : linear_pmap 𝕜 E F).domain = f.domain := rfl

instance : has_coe_to_fun (E →L.[𝕜] F)
  (λ f : E →L.[𝕜] F, f.to_linear_pmap.domain → F) :=
⟨λ f, f.to_fun⟩

@[simp] lemma to_fun_eq_coe (f : E →L.[𝕜] F) (x : f.domain) :
  f.to_fun x = f x := rfl

@[ext] lemma ext {f g : E →L.[𝕜] F} (h : f.domain = g.domain)
  (h' : ∀ ⦃x : f.domain⦄ ⦃y : g.domain⦄ (h : (x:E) = y), f x = g y) : f = g :=
coe_injective (linear_pmap.ext (by simp_rw [coe_domain, h]) h')

lemma map_zero (f : E →L.[𝕜] F) : f 0 = 0 :=
f.to_fun.map_zero

lemma map_add (f : E →L.[𝕜] F) (x y : f.domain) : f (x + y) = f x + f y :=
f.to_fun.map_add x y

lemma map_neg (f : E →L.[𝕜] F) {x : f.domain} : f (-x) = -f x :=
f.to_fun.map_neg x

lemma map_sub (f : E →L.[𝕜] F) {x y : f.domain} : f (x - y) = f x - f y :=
f.to_fun.map_sub x y

lemma map_smul (f : E →L.[𝕜] F) (r : 𝕜) (x : f.domain) : f (r • x) = r • f x :=
f.to_fun.map_smul r x

instance : has_le (E →L.[𝕜] F) :=
⟨λ f g, f.to_linear_pmap ≤ g.to_linear_pmap⟩

lemma le_iff {f g : E →L.[𝕜] F} :
  f ≤ g ↔ f.domain ≤ g.domain ∧ ∀ ⦃x : f.domain⦄ ⦃y : g.domain⦄, (x : E) = y → f x = g y :=
⟨λ h, ⟨h.1, λ _ _ hxy, h.2 hxy⟩, λ h, ⟨h.1, λ _ _ hxy, h.2 hxy⟩⟩

lemma eq_of_le_of_domain_eq {f g : E →L.[𝕜] F} (hle : f ≤ g) (heq : f.domain = g.domain) :
  f = g :=
continuous_linear_pmap.ext heq hle.2

section neg

variables [has_continuous_neg F]

instance : has_neg (E →L.[𝕜] F) :=
⟨λ f, ⟨-f.to_linear_pmap, f.cont.neg⟩⟩

@[simp] lemma neg_apply (f : E →L.[𝕜] F) (x : (-f).domain) : (-f) x = - f x := rfl

end neg

instance : has_bot (E →L.[𝕜] F) :=
⟨⟨(⊥ : linear_pmap 𝕜 E F), continuous_zero⟩⟩

instance : inhabited (E →L.[𝕜] F) := ⟨⊥⟩

instance : order_bot (E →L.[𝕜] F) :=
{ bot := ⊥,
  bot_le := λ f, ⟨bot_le, λ x y h,
    have hx : x = 0, from subtype.eq ((submodule.mem_bot 𝕜).1 x.2),
    have hy : y = 0, from subtype.eq (h.symm.trans (congr_arg _ hx)),
    by simp_rw [hx, hy, linear_pmap.map_zero]⟩ }

section smul

variables {M N : Type*} [monoid M] [distrib_mul_action M F] [smul_comm_class 𝕜 M F]
variables [monoid N] [distrib_mul_action N F] [smul_comm_class 𝕜 N F]
variables [has_continuous_const_smul M F]

instance : has_smul M (E →L.[𝕜] F) :=
⟨λ a f,
  { to_linear_pmap := a • f,
    cont := f.cont.const_smul a }⟩

lemma smul_apply (a : M) (f : E →L.[𝕜] F) (x : ((a • f).domain)) :
  (a • f) x = a • f x := rfl

@[simp] lemma coe_smul (a : M) (f : E →L.[𝕜] F) : ⇑(a • f) = a • f := rfl

end smul

end continuous_linear_pmap
