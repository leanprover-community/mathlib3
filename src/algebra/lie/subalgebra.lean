/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.lie.basic

/-!
# Lie subalgebras

This file defines Lie subalgebras of a Lie algebra and provides basic related definitions and
results.

## Main definitions

  * `lie_subalgebra`
  * `lie_subalgebra.incl`
  * `lie_subalgebra.map`
  * `lie_hom.range`
  * `lie_equiv.of_injective`
  * `lie_equiv.of_eq`
  * `lie_equiv.of_subalgebra`
  * `lie_equiv.of_subalgebras`

## Tags

lie algebra, lie subalgebra
-/

universes u v w w₁ w₂

section lie_subalgebra

variables (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L]

set_option old_structure_cmd true
/-- A Lie subalgebra of a Lie algebra is submodule that is closed under the Lie bracket.
This is a sufficient condition for the subset itself to form a Lie algebra. -/
structure lie_subalgebra extends submodule R L :=
(lie_mem' : ∀ {x y}, x ∈ carrier → y ∈ carrier → ⁅x, y⁆ ∈ carrier)

attribute [nolint doc_blame] lie_subalgebra.to_submodule

/-- The zero algebra is a subalgebra of any Lie algebra. -/
instance : has_zero (lie_subalgebra R L) :=
⟨{ lie_mem' := λ x y hx hy, by { rw [((submodule.mem_bot R).1 hx), zero_lie],
                                exact submodule.zero_mem (0 : submodule R L), },
   ..(0 : submodule R L) }⟩

instance : inhabited (lie_subalgebra R L) := ⟨0⟩
instance : has_coe (lie_subalgebra R L) (set L) := ⟨lie_subalgebra.carrier⟩
instance : has_mem L (lie_subalgebra R L) := ⟨λ x L', x ∈ (L' : set L)⟩

instance lie_subalgebra_coe_submodule : has_coe (lie_subalgebra R L) (submodule R L) :=
⟨lie_subalgebra.to_submodule⟩

/-- A Lie subalgebra forms a new Lie ring. -/
instance lie_subalgebra_lie_ring (L' : lie_subalgebra R L) : lie_ring L' :=
{ bracket      := λ x y, ⟨⁅x.val, y.val⁆, L'.lie_mem' x.property y.property⟩,
  lie_add      := by { intros, apply set_coe.ext, apply lie_add, },
  add_lie      := by { intros, apply set_coe.ext, apply add_lie, },
  lie_self     := by { intros, apply set_coe.ext, apply lie_self, },
  leibniz_lie  := by { intros, apply set_coe.ext, apply leibniz_lie, } }

/-- A Lie subalgebra forms a new Lie algebra. -/
instance lie_subalgebra_lie_algebra (L' : lie_subalgebra R L) : lie_algebra R L' :=
{ lie_smul := by { intros, apply set_coe.ext, apply lie_smul } }

namespace lie_subalgebra

variables {R L} (L' : lie_subalgebra R L)

@[simp] lemma zero_mem : (0 : L) ∈ L' := (L' : submodule R L).zero_mem

lemma smul_mem (t : R) {x : L} (h : x ∈ L') : t • x ∈ L' := (L' : submodule R L).smul_mem t h

lemma add_mem {x y : L} (hx : x ∈ L') (hy : y ∈ L') : (x + y : L) ∈ L' :=
(L' : submodule R L).add_mem hx hy

lemma lie_mem {x y : L} (hx : x ∈ L') (hy : y ∈ L') : (⁅x, y⁆ : L) ∈ L' := L'.lie_mem' hx hy

@[simp] lemma mem_coe {x : L} : x ∈ (L' : set L) ↔ x ∈ L' := iff.rfl

@[simp] lemma mem_coe' {x : L} : x ∈ (L' : submodule R L) ↔ x ∈ L' := iff.rfl

@[simp, norm_cast] lemma coe_bracket (x y : L') : (↑⁅x, y⁆ : L) = ⁅(↑x : L), ↑y⁆ := rfl

lemma ext_iff (x y : L') : x = y ↔ (x : L) = y := subtype.ext_iff

lemma coe_zero_iff_zero (x : L') : (x : L) = 0 ↔ x = 0 := (ext_iff L' x 0).symm

@[ext] lemma ext (L₁' L₂' : lie_subalgebra R L) (h : ∀ x, x ∈ L₁' ↔ x ∈ L₂') :
  L₁' = L₂' :=
by { cases L₁', cases L₂', simp only [], ext x, exact h x, }

lemma ext_iff' (L₁' L₂' : lie_subalgebra R L) : L₁' = L₂' ↔ ∀ x, x ∈ L₁' ↔ x ∈ L₂' :=
⟨λ h x, by rw h, ext L₁' L₂'⟩

@[simp] lemma mk_coe (S : set L) (h₁ h₂ h₃ h₄) :
  ((⟨S, h₁, h₂, h₃, h₄⟩ : lie_subalgebra R L) : set L) = S := rfl

lemma coe_injective : function.injective (coe : lie_subalgebra R L → set L) :=
λ L₁' L₂' h, by cases L₁'; cases L₂'; congr'

@[simp, norm_cast] theorem coe_set_eq (L₁' L₂' : lie_subalgebra R L) :
  (L₁' : set L) = L₂' ↔ L₁' = L₂' := coe_injective.eq_iff

lemma to_submodule_injective :
  function.injective (coe : lie_subalgebra R L → submodule R L) :=
λ L₁' L₂' h, by { rw submodule.ext'_iff at h, rw ← coe_set_eq, exact h, }

@[simp] lemma coe_to_submodule_eq (L₁' L₂' : lie_subalgebra R L) :
  (L₁' : submodule R L) = (L₂' : submodule R L) ↔ L₁' = L₂' :=
to_submodule_injective.eq_iff

end lie_subalgebra

variables {R L} {L₂ : Type w} [lie_ring L₂] [lie_algebra R L₂]
variables (f : L →ₗ⁅R⁆ L₂)

/-- The embedding of a Lie subalgebra into the ambient space as a Lie morphism. -/
def lie_subalgebra.incl (L' : lie_subalgebra R L) : L' →ₗ⁅R⁆ L :=
{ map_lie' := λ x y, by { rw [linear_map.to_fun_eq_coe, submodule.subtype_apply], refl, },
  ..L'.to_submodule.subtype }

/-- The range of a morphism of Lie algebras is a Lie subalgebra. -/
def lie_hom.range : lie_subalgebra R L₂ :=
{ lie_mem' := λ x y,
    show x ∈ f.to_linear_map.range → y ∈ f.to_linear_map.range → ⁅x, y⁆ ∈ f.to_linear_map.range,
    by { repeat { rw linear_map.mem_range }, rintros ⟨x', hx⟩ ⟨y', hy⟩, refine ⟨⁅x', y'⁆, _⟩,
         rw [←hx, ←hy], change f ⁅x', y'⁆ = ⁅f x', f y'⁆, rw lie_hom.map_lie, },
  ..f.to_linear_map.range }

@[simp] lemma lie_hom.range_bracket (x y : f.range) :
  (↑⁅x, y⁆ : L₂) = ⁅(↑x : L₂), ↑y⁆ := rfl

@[simp] lemma lie_hom.range_coe : (f.range : set L₂) = set.range f :=
linear_map.range_coe ↑f

@[simp] lemma lie_subalgebra.range_incl (L' : lie_subalgebra R L) : L'.incl.range = L' :=
by { rw ← lie_subalgebra.coe_to_submodule_eq, exact (L' : submodule R L).range_subtype, }

/-- The image of a Lie subalgebra under a Lie algebra morphism is a Lie subalgebra of the
codomain. -/
def lie_subalgebra.map (L' : lie_subalgebra R L) : lie_subalgebra R L₂ :=
{ lie_mem' := λ x y hx hy, by {
    erw submodule.mem_map at hx, rcases hx with ⟨x', hx', hx⟩, rw ←hx,
    erw submodule.mem_map at hy, rcases hy with ⟨y', hy', hy⟩, rw ←hy,
    erw submodule.mem_map,
    exact ⟨⁅x', y'⁆, L'.lie_mem hx' hy', lie_hom.map_lie f x' y'⟩, },
..((L' : submodule R L).map (f : L →ₗ[R] L₂))}

@[simp] lemma lie_subalgebra.mem_map_submodule (e : L ≃ₗ⁅R⁆ L₂) (L' : lie_subalgebra R L) (x : L₂) :
  x ∈ L'.map (e : L →ₗ⁅R⁆ L₂) ↔ x ∈ (L' : submodule R L).map (e : L →ₗ[R] L₂) :=
iff.rfl

end lie_subalgebra

namespace lie_equiv

variables {R : Type u} {L₁ : Type v} {L₂ : Type w}
variables [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_algebra R L₁] [lie_algebra R L₂]

/-- An injective Lie algebra morphism is an equivalence onto its range. -/
noncomputable def of_injective (f : L₁ →ₗ⁅R⁆ L₂) (h : function.injective f) :
  L₁ ≃ₗ⁅R⁆ f.range :=
have h' : (f : L₁ →ₗ[R] L₂).ker = ⊥ := linear_map.ker_eq_bot_of_injective h,
{ map_lie' := λ x y, by { apply set_coe.ext,
    simp only [linear_equiv.of_injective_apply, lie_hom.range_bracket],
    apply f.map_lie, },
..(linear_equiv.of_injective ↑f h')}

@[simp] lemma of_injective_apply (f : L₁ →ₗ⁅R⁆ L₂) (h : function.injective f) (x : L₁) :
  ↑(of_injective f h x) = f x := rfl

variables (L₁' L₁'' : lie_subalgebra R L₁) (L₂' : lie_subalgebra R L₂)

/-- Lie subalgebras that are equal as sets are equivalent as Lie algebras. -/
def of_eq (h : (L₁' : set L₁) = L₁'') : L₁' ≃ₗ⁅R⁆ L₁'' :=
{ map_lie' := λ x y, by { apply set_coe.ext, simp, },
  ..(linear_equiv.of_eq ↑L₁' ↑L₁''
      (by {ext x, change x ∈ (L₁' : set L₁) ↔ x ∈ (L₁'' : set L₁), rw h, } )) }

@[simp] lemma of_eq_apply (L L' : lie_subalgebra R L₁) (h : (L : set L₁) = L') (x : L) :
  (↑(of_eq L L' h x) : L₁) = x := rfl

variables (e : L₁ ≃ₗ⁅R⁆ L₂)

/-- An equivalence of Lie algebras restricts to an equivalence from any Lie subalgebra onto its
image. -/
def of_subalgebra : L₁'' ≃ₗ⁅R⁆ (L₁''.map e : lie_subalgebra R L₂) :=
{ map_lie' := λ x y, by { apply set_coe.ext, exact lie_hom.map_lie (↑e : L₁ →ₗ⁅R⁆ L₂) ↑x ↑y, }
  ..(linear_equiv.of_submodule (e : L₁ ≃ₗ[R] L₂) ↑L₁'') }

@[simp] lemma of_subalgebra_apply (x : L₁'') : ↑(e.of_subalgebra _  x) = e x := rfl

/-- An equivalence of Lie algebras restricts to an equivalence from any Lie subalgebra onto its
image. -/
def of_subalgebras (h : L₁'.map ↑e = L₂') : L₁' ≃ₗ⁅R⁆ L₂' :=
{ map_lie' := λ x y, by { apply set_coe.ext, exact lie_hom.map_lie (↑e : L₁ →ₗ⁅R⁆ L₂) ↑x ↑y, },
  ..(linear_equiv.of_submodules (e : L₁ ≃ₗ[R] L₂) ↑L₁' ↑L₂' (by { rw ←h, refl, })) }

@[simp] lemma of_subalgebras_apply (h : L₁'.map ↑e = L₂') (x : L₁') :
  ↑(e.of_subalgebras _ _ h x) = e x := rfl

@[simp] lemma of_subalgebras_symm_apply (h : L₁'.map ↑e = L₂') (x : L₂') :
  ↑((e.of_subalgebras _ _ h).symm x) = e.symm x := rfl

end lie_equiv
