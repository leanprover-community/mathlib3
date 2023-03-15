/-
Copyright (c) 2019 Johan Commelin All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import ring_theory.ideal.basic
import topology.algebra.ring.basic
import topology.sets.opens
/-!
# Open subgroups of a topological groups

This files builds the lattice `open_subgroup G` of open subgroups in a topological group `G`,
and its additive version `open_add_subgroup`.  This lattice has a top element, the subgroup of all
elements, but no bottom element in general. The trivial subgroup which is the natural candidate
bottom has no reason to be open (this happens only in discrete groups).

Note that this notion is especially relevant in a non-archimedean context, for instance for
`p`-adic groups.

## Main declarations

* `open_subgroup.is_closed`: An open subgroup is automatically closed.
* `subgroup.is_open_mono`: A subgroup containing an open subgroup is open.
                           There are also versions for additive groups, submodules and ideals.
* `open_subgroup.comap`: Open subgroups can be pulled back by a continuous group morphism.

## TODO
* Prove that the identity component of a locally path connected group is an open subgroup.
  Up to now this file is really geared towards non-archimedean algebra, not Lie groups.
-/

open topological_space
open_locale topology

/-- The type of open subgroups of a topological additive group. -/
@[ancestor add_subgroup]
structure open_add_subgroup  (G : Type*) [add_group G] [topological_space G]
  extends add_subgroup G :=
(is_open' : is_open carrier)

/-- The type of open subgroups of a topological group. -/
@[ancestor subgroup, to_additive]
structure open_subgroup (G : Type*) [group G] [topological_space G] extends subgroup G :=
(is_open' : is_open carrier)

/-- Reinterpret an `open_subgroup` as a `subgroup`. -/
add_decl_doc open_subgroup.to_subgroup

/-- Reinterpret an `open_add_subgroup` as an `add_subgroup`. -/
add_decl_doc open_add_subgroup.to_add_subgroup

namespace open_subgroup
open function topological_space
variables {G : Type*} [group G] [topological_space G]
variables {U V : open_subgroup G} {g : G}

@[to_additive]
instance has_coe_subgroup : has_coe_t (open_subgroup G) (subgroup G) := ⟨to_subgroup⟩

@[to_additive]
lemma coe_subgroup_injective : injective (coe : open_subgroup G → subgroup G)
| ⟨_, _⟩ ⟨_, _⟩ rfl := rfl

@[to_additive]
instance : set_like (open_subgroup G) G :=
{ coe := λ U, U.1,
  coe_injective' := λ _ _ h, coe_subgroup_injective $ set_like.ext' h }

@[to_additive]
instance : subgroup_class (open_subgroup G) G :=
{ mul_mem := λ U _ _, U.mul_mem',
  one_mem := λ U, U.one_mem',
  inv_mem := λ U _, U.inv_mem' }

@[to_additive]
instance has_coe_opens : has_coe_t (open_subgroup G) (opens G) := ⟨λ U, ⟨U, U.is_open'⟩⟩

@[simp, norm_cast, to_additive] lemma coe_coe_subgroup : ((U : subgroup G) : set G) = U := rfl
@[simp, norm_cast, to_additive] lemma coe_coe_opens : ((U : opens G) : set G) = U := rfl
@[simp, norm_cast, to_additive] lemma mem_coe_opens : g ∈ (U : opens G) ↔ g ∈ U := iff.rfl
@[simp, norm_cast, to_additive]
lemma mem_coe_subgroup : g ∈ (U : subgroup G) ↔ g ∈ U := iff.rfl

@[ext, to_additive]
lemma ext (h : ∀ x, x ∈ U ↔ x ∈ V) : (U = V) := set_like.ext h

variable (U)
@[to_additive]
protected lemma is_open : is_open (U : set G) := U.is_open'

@[to_additive]
lemma mem_nhds_one : (U : set G) ∈ 𝓝 (1 : G) :=
is_open.mem_nhds U.is_open U.one_mem
variable {U}

@[to_additive]
instance : has_top (open_subgroup G) := ⟨{ is_open' := is_open_univ, .. (⊤ : subgroup G) }⟩

@[simp, to_additive] lemma mem_top (x : G) : x ∈ (⊤ : open_subgroup G) := trivial
@[simp, norm_cast, to_additive] lemma coe_top : ((⊤ : open_subgroup G) : set G) = set.univ := rfl

@[simp, norm_cast, to_additive]
lemma coe_subgroup_top : ((⊤ : open_subgroup G) : subgroup G) = ⊤ := rfl

@[simp, norm_cast, to_additive]
lemma coe_opens_top : ((⊤ : open_subgroup G) : opens G) = ⊤ := rfl

@[to_additive]
instance : inhabited (open_subgroup G) := ⟨⊤⟩

@[to_additive]
lemma is_closed [has_continuous_mul G] (U : open_subgroup G) : is_closed (U : set G) :=
begin
  apply is_open_compl_iff.1,
  refine is_open_iff_forall_mem_open.2 (λ x hx, ⟨(λ y, y * x⁻¹) ⁻¹' U, _, _, _⟩),
  { refine λ u hux hu, hx _,
    simp only [set.mem_preimage, set_like.mem_coe] at hux hu ⊢,
    convert U.mul_mem (U.inv_mem hux) hu,
    simp },
  { exact U.is_open.preimage (continuous_mul_right _) },
  { simp [one_mem] }
end

@[to_additive]
lemma is_clopen [has_continuous_mul G] (U : open_subgroup G) : is_clopen (U : set G) :=
⟨U.is_open, U.is_closed⟩

section
variables {H : Type*} [group H] [topological_space H]

/-- The product of two open subgroups as an open subgroup of the product group. -/
@[to_additive "The product of two open subgroups as an open subgroup of the product group."]
def prod (U : open_subgroup G) (V : open_subgroup H) : open_subgroup (G × H) :=
{ is_open' := U.is_open.prod V.is_open,
  .. (U : subgroup G).prod (V : subgroup H) }

@[simp, norm_cast, to_additive] lemma coe_prod (U : open_subgroup G) (V : open_subgroup H) :
  (U.prod V : set (G × H)) = U ×ˢ V :=
rfl

@[simp, norm_cast, to_additive]
lemma coe_subgroup_prod (U : open_subgroup G) (V : open_subgroup H) :
  (U.prod V : subgroup (G × H)) = (U : subgroup G).prod V :=
rfl

end

@[to_additive]
instance : has_inf (open_subgroup G) :=
⟨λ U V, ⟨U ⊓ V, U.is_open.inter V.is_open⟩⟩

@[simp, norm_cast, to_additive] lemma coe_inf : (↑(U ⊓ V) : set G) = (U : set G) ∩ V := rfl
@[simp, norm_cast, to_additive] lemma coe_subgroup_inf : (↑(U ⊓ V) : subgroup G) = ↑U ⊓ ↑V := rfl
@[simp, norm_cast, to_additive] lemma coe_opens_inf : (↑(U ⊓ V) : opens G) = ↑U ⊓ ↑V := rfl
@[simp, to_additive] lemma mem_inf {x} : x ∈ U ⊓ V ↔ x ∈ U ∧ x ∈ V := iff.rfl

@[to_additive]
instance : semilattice_inf (open_subgroup G) :=
{ .. set_like.partial_order,
  .. set_like.coe_injective.semilattice_inf (coe : open_subgroup G → set G) (λ _ _, rfl) }

@[to_additive]
instance : order_top (open_subgroup G) :=
{ top := ⊤,
  le_top := λ U, set.subset_univ _ }

@[simp, norm_cast, to_additive] lemma coe_subgroup_le :
  (U : subgroup G) ≤ (V : subgroup G) ↔ U ≤ V :=
iff.rfl

variables {N : Type*} [group N] [topological_space N]

/-- The preimage of an `open_subgroup` along a continuous `monoid` homomorphism
  is an `open_subgroup`. -/
@[to_additive "The preimage of an `open_add_subgroup` along a continuous `add_monoid` homomorphism
is an `open_add_subgroup`."]
def comap (f : G →* N) (hf : continuous f) (H : open_subgroup N) : open_subgroup G :=
{ is_open' := H.is_open.preimage hf,
  .. (H : subgroup N).comap f }

@[simp, norm_cast, to_additive]
lemma coe_comap (H : open_subgroup N) (f : G →* N) (hf : continuous f) :
  (H.comap f hf : set G) = f ⁻¹' H := rfl

@[simp, norm_cast, to_additive]
lemma coe_subgroup_comap (H : open_subgroup N) (f : G →* N) (hf : continuous f) :
  (H.comap f hf : subgroup G) = (H : subgroup N).comap f := rfl

@[simp, to_additive]
lemma mem_comap {H : open_subgroup N} {f : G →* N} {hf : continuous f} {x : G} :
  x ∈ H.comap f hf ↔ f x ∈ H := iff.rfl

@[to_additive]
lemma comap_comap {P : Type*} [group P] [topological_space P]
  (K : open_subgroup P) (f₂ : N →* P) (hf₂ : continuous f₂) (f₁ : G →* N) (hf₁ : continuous f₁) :
  (K.comap f₂ hf₂).comap f₁ hf₁ = K.comap (f₂.comp f₁) (hf₂.comp hf₁) :=
rfl

end open_subgroup

namespace subgroup

variables {G : Type*} [group G] [topological_space G] [has_continuous_mul G] (H : subgroup G)

@[to_additive]
lemma is_open_of_mem_nhds {g : G} (hg : (H : set G) ∈ 𝓝 g) :
  is_open (H : set G) :=
begin
  refine is_open_iff_mem_nhds.2 (λ x hx, _),
  have hg' : g ∈ H := set_like.mem_coe.1 (mem_of_mem_nhds hg),
  have : filter.tendsto (λ y, y * (x⁻¹ * g)) (𝓝 x) (𝓝 g) :=
    (continuous_id.mul continuous_const).tendsto' _ _ (mul_inv_cancel_left _ _),
  simpa only [set_like.mem_coe, filter.mem_map',
    H.mul_mem_cancel_right (H.mul_mem (H.inv_mem hx) hg')] using this hg,
end

@[to_additive]
lemma is_open_mono {H₁ H₂ : subgroup G} (h : H₁ ≤ H₂) (h₁ : is_open (H₁ : set G)) :
  is_open (H₂ : set G) :=
is_open_of_mem_nhds _ $ filter.mem_of_superset (h₁.mem_nhds $ one_mem H₁) h

@[to_additive]
lemma is_open_of_open_subgroup {U : open_subgroup G} (h : ↑U ≤ H) :
  is_open (H : set G) :=
is_open_mono h U.is_open

/-- If a subgroup of a topological group has `1` in its interior, then it is open. -/
@[to_additive "If a subgroup of an additive topological group has `0` in its interior, then it is
open."]
lemma is_open_of_one_mem_interior (h_1_int : (1 : G) ∈ interior (H : set G)) :
  is_open (H : set G) :=
is_open_of_mem_nhds H $ mem_interior_iff_mem_nhds.1 h_1_int

end subgroup

namespace open_subgroup

variables {G : Type*} [group G] [topological_space G] [has_continuous_mul G]

@[to_additive]
instance : has_sup (open_subgroup G) :=
⟨λ U V, ⟨U ⊔ V, subgroup.is_open_mono (le_sup_left : U.1 ≤ U ⊔ V) U.is_open⟩⟩

@[simp, norm_cast, to_additive]
lemma coe_subgroup_sup (U V : open_subgroup G) : (↑(U ⊔ V) : subgroup G) = ↑U ⊔ ↑V := rfl

@[to_additive]
instance : lattice (open_subgroup G) :=
{ .. open_subgroup.semilattice_inf,
  .. coe_subgroup_injective.semilattice_sup (coe : open_subgroup G → subgroup G) (λ _ _, rfl) }

end open_subgroup

namespace submodule
open open_add_subgroup
variables {R : Type*} {M : Type*} [comm_ring R]
variables [add_comm_group M] [topological_space M] [topological_add_group M] [module R M]

lemma is_open_mono {U P : submodule R M} (h : U ≤ P) (hU : is_open (U : set M)) :
  is_open (P : set M) :=
@add_subgroup.is_open_mono M _ _ _ U.to_add_subgroup P.to_add_subgroup h hU

end submodule

namespace ideal
variables {R : Type*} [comm_ring R]
variables [topological_space R] [topological_ring R]

lemma is_open_of_open_subideal {U I : ideal R} (h : U ≤ I) (hU : is_open (U : set R)) :
  is_open (I : set R) :=
submodule.is_open_mono h hU

end ideal
