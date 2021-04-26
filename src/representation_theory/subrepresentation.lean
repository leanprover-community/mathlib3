/-
Copyright (c) 2021 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
import representation_theory.basic
import ring_theory.simple_module

universes u v w

open function
open_locale big_operators
section subrepresentation
variables (k : Type u) (G : Type v) (M : Type w)
variables [semiring k] [monoid G] [add_comm_monoid M]
variables [module k M] [distrib_mul_action G M]

/-- A subrepresentation `N` of a `representation k G M` is a `k`-submodule of `M`
fixed by the action of `G`, i.e. `∀ g, g • N ⊆ N`-/
structure subrepresentation [representation k G M] extends submodule k M :=
(group_smul_mem' : ∀ (c : G) {x : M}, x ∈ carrier → c • x ∈ carrier)

/-- Reinterpret a `submodule` as an `add_submonoid`. -/
add_decl_doc subrepresentation.to_submodule

end subrepresentation

namespace subrepresentation

section definitions
variables {k : Type u} {G : Type v} {M : Type w}
variables [semiring k] [monoid G] [add_comm_monoid M]
variables [module k M] [distrib_mul_action G M] [representation k G M]

instance : set_like (subrepresentation k G M) M :=
{ coe := λ p, p.carrier,
  coe_injective' := λ p q h, by { cases p; cases q; simp only at *, apply set_like.ext', exact h } }

@[simp] lemma mk_coe (S : set M) (h₁ h₂ h₃)
  (h₄ : ∀ (c : G) {x : M}, x ∈ S → c • x ∈ S) :
  ((⟨⟨S, h₁, h₂, h₃⟩, h₄⟩ : subrepresentation k G M) : set M) = S := rfl

@[ext] theorem ext {p q : subrepresentation k G M} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q :=
set_like.ext h

/-- Copy of a submodule with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy
  (p : subrepresentation k G M) (s : set M) (hs : s = ↑p) : subrepresentation k G M :=
⟨{ carrier := s,
  zero_mem' := hs.symm ▸ p.zero_mem',
  add_mem' := hs.symm ▸ p.add_mem',
  smul_mem' := hs.symm ▸ p.smul_mem', },
  by { cases hs, exact p.group_smul_mem', } ⟩

theorem to_submodule_injective :
  injective (to_submodule : subrepresentation k G M → submodule k M) :=
λ p q h, set_like.ext'_iff.2 (show _, from set_like.ext'_iff.1 h)

@[simp] theorem to_submodule_eq {p q : subrepresentation k G M} :
  p.to_submodule = q.to_submodule ↔ p = q :=
injective.eq_iff $ to_submodule_injective

@[mono] lemma to_submodule_strict_mono :
  strict_mono (to_submodule : subrepresentation k G M → submodule k M) := λ _ _, id

@[mono]
lemma to_submodule_mono : monotone (to_submodule : subrepresentation k G M → submodule k M) :=
to_submodule_strict_mono.monotone

@[simp] theorem coe_to_submodule (p : subrepresentation k G M) :
  (p.to_submodule : set M) = p := rfl

/-- Reinterpret a `subrepresentation` as an `sub_mul_action`. -/
def to_sub_mul_action (p : subrepresentation k G M) : sub_mul_action G M :=
{ carrier := p.carrier,
  smul_mem' := λ g m, p.group_smul_mem' g }

theorem to_sub_mul_action_injective :
  injective (to_sub_mul_action : subrepresentation k G M → sub_mul_action G M) :=
λ p q h, set_like.ext'_iff.2 (show _, from set_like.ext'_iff.1 h)

@[simp] theorem to_sub_mul_action_eq {p q : subrepresentation k G M} :
  p.to_sub_mul_action = q.to_sub_mul_action ↔ p = q :=
to_sub_mul_action_injective.eq_iff

@[mono] lemma to_sub_mul_action_strict_mono :
  strict_mono (to_sub_mul_action : subrepresentation k G M → sub_mul_action G M) := λ _ _, id

@[mono]
lemma to_sub_mul_action_mono :
  monotone (to_sub_mul_action : subrepresentation k G M → sub_mul_action G M) :=
to_sub_mul_action_strict_mono.monotone

@[simp] theorem coe_to_sub_mul_action (p : subrepresentation k G M) :
  (p.to_sub_mul_action : set M) = p := rfl

end definitions

section subrepresentation
variables {k : Type u} {G : Type v} {M : Type w} {ι : Type*}
variables [semiring k] [monoid G] [add_comm_monoid M]
variables [module k M] [distrib_mul_action G M]
variables {representation_M : representation k G M} (p : subrepresentation k G M)
variables {r : k} {x y : M}

-- wait. !!! THIS NEEDS TO BE PATCHED UP BY COMBING THROUGH `algebra.module.submodule.lean`
variables (p)
@[simp] lemma mem_carrier : x ∈ p.carrier ↔ x ∈ (p : set M) := iff.rfl

@[simp] lemma zero_mem : (0 : M) ∈ p := p.zero_mem'

lemma add_mem (h₁ : x ∈ p) (h₂ : y ∈ p) : x + y ∈ p := p.add_mem' h₁ h₂

lemma smul_mem (r : k) (h : x ∈ p) : r • x ∈ p := p.smul_mem' r h

lemma gsmul_mem (g : G) (h : x ∈ p) : g • x ∈ p := p.group_smul_mem' g h

lemma sum_mem {t : finset ι} {f : ι → M} : (∀ i ∈ t, f i ∈ p) → (∑ i in t, f i) ∈ p :=
p.to_submodule.sum_mem

lemma sum_smul_mem {t : finset ι} {f : ι → M} (r : ι → k)
    (hyp : ∀ i ∈ t, f i ∈ p) : (∑ i in t, r i • f i) ∈ p :=
sum_mem _ (λ i hi, smul_mem  _ _ (hyp i hi))

lemma sum_gsmul_mem {t : finset ι} {f : ι → M} (g : ι → G)
    (hyp : ∀ i ∈ t, f i ∈ p) : (∑ i in t, g i • f i) ∈ p :=
sum_mem p (λ i hi, gsmul_mem p (g i) (hyp i hi))

instance : has_add p := ⟨λx y, ⟨x.1 + y.1, add_mem _ x.2 y.2⟩⟩
instance : has_zero p := ⟨⟨0, zero_mem _⟩⟩
instance : inhabited p := ⟨0⟩
instance : has_scalar k p := ⟨λ c x, ⟨c • x, smul_mem p c x.2⟩⟩
instance has_gsmul : has_scalar G p := ⟨λ c x, ⟨c • x, gsmul_mem p c x.2⟩⟩

protected lemma nonempty : (p : set M).nonempty := ⟨0, p.zero_mem⟩

@[simp] lemma mk_eq_zero {x} (h : x ∈ p) : (⟨x, h⟩ : p) = 0 ↔ x = 0 := subtype.ext_iff_val

variables {p}
@[simp, norm_cast] lemma coe_eq_zero {x : p} : (x : M) = 0 ↔ x = 0 :=
(set_like.coe_eq_coe : (x : M) = (0 : p) ↔ x = 0)
@[simp, norm_cast] lemma coe_add (x y : p) : (↑(x + y) : M) = ↑x + ↑y := rfl
@[simp, norm_cast] lemma coe_zero : ((0 : p) : M) = 0 := rfl
@[norm_cast] lemma coe_smul (r : k) (x : p) : ((r • x : p) : M) = r • ↑x := rfl
@[norm_cast] lemma coe_gsmul (g : G) (x : p) : ((g • x : p) : M) = g • ↑x := rfl
@[simp, norm_cast] lemma coe_mk (x : M) (hx : x ∈ p) : ((⟨x, hx⟩ : p) : M) = x := rfl
@[simp] lemma coe_mem (x : p) : (x : M) ∈ p := x.2

variables (p)
instance : add_comm_monoid p :=
{ add := (+), zero := 0, .. p.to_submodule.add_comm_monoid }

instance : module k p :=
by refine {smul := (•), ..}; { intros, apply set_coe.ext, simp [smul_add, add_smul, mul_smul] }

instance : mul_action G p :=
{ smul := (•), .. p.to_sub_mul_action.mul_action }

instance : distrib_mul_action G p :=
{ smul_add := λ g m n, by { ext, simp [coe_gsmul], },
  smul_zero := λ g, by { ext, simp [coe_gsmul], } }

instance representation' : representation k G p :=
{ smul_comm := λ r g m, by { ext, simp [coe_gsmul, smul_comm], } }

instance : representation k G p := p.representation'

end subrepresentation

section reducible
variables (k : Type u) (G : Type v) (M N: Type w)
variables [ring k] [monoid G] [add_comm_group M]
variables [module k M] [distrib_mul_action G M]

/-- A representation is irreducible if it has no nontrivial subrepresentations. -/
abbreviation is_irreducible [representation k G M] := is_simple_module (monoid_algebra k G) M

end reducible

end subrepresentation

section rep_hom
variables (k : Type u) (G : Type v) (M N: Type w)
variables [semiring k] [monoid G] [add_comm_monoid M] [add_comm_monoid N]
variables [module k M] [distrib_mul_action G M] [module k N] [distrib_mul_action G N]

/-- A homomorphism between representations `M` and `N` over `k` and `G` is a
`k`-linear map which commutes with the `G`-action. -/
structure rep_hom [representation k G M] [representation k G N] extends linear_map k M N :=
(commutes' : ∀ (g : G) (m : M), to_fun (g • m) = g • to_fun m)

infixr ` →ᵣ `:25 := rep_hom _
notation M ` →ᵣ[`:25 k `, ` G `] ` N := rep_hom k G M N

end rep_hom
