import order.filter.lift
import linear_algebra.basic
import topology.opens topology.algebra.ring

section
open topological_space
variables (G : Type*) [group G] [topological_space G]

/-- The type of open subgroups of a topological group. -/
@[to_additive open_add_subgroup]
def open_subgroup := { U : set G // is_open U ∧ is_subgroup U }

@[to_additive]
instance open_subgroup.has_coe :
  has_coe (open_subgroup G) (opens G) := ⟨λ U, ⟨U.1, U.2.1⟩⟩
end

-- Tell Lean that `open_add_subgroup` is a namespace
namespace open_add_subgroup
end open_add_subgroup

namespace open_subgroup
open function lattice topological_space
open_locale topological_space
variables {G : Type*} [group G] [topological_space G]
variables {U V : open_subgroup G}

@[to_additive]
instance : has_mem G (open_subgroup G) := ⟨λ g U, g ∈ (U : set G)⟩

@[to_additive]
lemma ext : (U = V) ↔ ((U : set G) = V) :=
by cases U; cases V; split; intro h; try {congr}; assumption

@[ext, to_additive]
lemma ext' (h : (U : set G) = V) : (U = V) :=
ext.mpr h

@[to_additive]
lemma coe_injective : injective (λ U : open_subgroup G, (U : set G)) :=
λ U V h, ext' h

@[to_additive is_add_subgroup]
instance : is_subgroup (U : set G) := U.2.2

variable (U)
@[to_additive]
protected lemma is_open : is_open (U : set G) := U.2.1

@[to_additive]
protected lemma one_mem : (1 : G) ∈ U := is_submonoid.one_mem (U : set G)

@[to_additive]
protected lemma inv_mem {g : G} (h : g ∈ U) : g⁻¹ ∈ U :=
  @is_subgroup.inv_mem G _ U _ g h

@[to_additive]
protected lemma mul_mem {g₁ g₂ : G} (h₁ : g₁ ∈ U) (h₂ : g₂ ∈ U) : g₁ * g₂ ∈ U :=
  @is_submonoid.mul_mem G _ U _ g₁ g₂ h₁ h₂

@[to_additive]
lemma mem_nhds_one : (U : set G) ∈ 𝓝 (1 : G) :=
mem_nhds_sets U.is_open U.one_mem
variable {U}

@[to_additive]
instance : inhabited (open_subgroup G) :=
{ default := ⟨set.univ, ⟨is_open_univ, by apply_instance⟩⟩ }

@[to_additive]
lemma is_open_of_nonempty_open_subset [topological_monoid G] {s : set G} [is_subgroup s]
  (h : ∃ U : opens G, nonempty U ∧ (U : set G) ⊆ s) :
  is_open s :=
begin
  rw is_open_iff_forall_mem_open,
  intros x hx,
  rcases h with ⟨U, ⟨g, hg⟩, hU⟩,
  use (λ y, y * (x⁻¹ * g)) ⁻¹' U,
  split,
  { intros u hu,
    erw set.mem_preimage at hu,
    replace hu := hU hu,
    replace hg := hU hg,
    have : (x⁻¹ * g)⁻¹ ∈ s,
    { simp [*, is_subgroup.inv_mem, is_submonoid.mul_mem], },
    convert is_submonoid.mul_mem hu this, simp [mul_assoc] },
  split,
  { exact continuous_id.mul continuous_const _ U.property },
  { change  x * (x⁻¹ * g) ∈ U,
    convert hg,
    rw [← mul_assoc, mul_right_inv, one_mul] }
end

@[to_additive is_open_of_open_add_subgroup]
lemma is_open_of_open_subgroup [topological_monoid G] {s : set G} [is_subgroup s]
  (h : ∃ U : open_subgroup G, (U : set G) ⊆ s) : is_open s :=
is_open_of_nonempty_open_subset $ let ⟨U, hU⟩ := h in ⟨U, ⟨⟨1, U.one_mem⟩⟩, hU⟩

@[to_additive]
lemma is_closed [topological_monoid G] (U : open_subgroup G) : is_closed (U : set G) :=
begin
  show is_open (-(U : set G)),
  rw is_open_iff_forall_mem_open,
  intros x hx,
  use (λ y, y * x⁻¹) ⁻¹' U,
  split,
  { intros u hux,
    erw set.mem_preimage at hux,
    rw set.mem_compl_iff at hx ⊢,
    intro hu, apply hx,
    convert is_submonoid.mul_mem (is_subgroup.inv_mem hux) hu,
    simp },
  split,
  { exact (continuous_mul_right _) _ U.is_open },
  { simpa using is_submonoid.one_mem (U : set G) }
end

section
variables {H : Type*} [group H] [topological_space H]

@[to_additive]
def prod (U : open_subgroup G) (V : open_subgroup H) : open_subgroup (G × H) :=
⟨(U : set G).prod (V : set H), is_open_prod U.is_open V.is_open, by apply_instance⟩

end

@[to_additive]
instance : partial_order (open_subgroup G) := partial_order.lift _ coe_injective (by apply_instance)

@[to_additive]
instance : semilattice_inf_top (open_subgroup G) :=
{ inf := λ U V, ⟨(U : set G) ∩ V, is_open_inter U.is_open V.is_open, by apply_instance⟩,
  inf_le_left := λ U V, set.inter_subset_left _ _,
  inf_le_right := λ U V, set.inter_subset_right _ _,
  le_inf := λ U V W hV hW, set.subset_inter hV hW,
  top := default _,
  le_top := λ U, set.subset_univ _,
  ..open_subgroup.partial_order }

@[to_additive]
instance [topological_monoid G] : semilattice_sup_top (open_subgroup G) :=
{ sup := λ U V,
  { val := group.closure ((U : set G) ∪ V),
    property :=
    begin
      haveI subgrp := _, refine ⟨_, subgrp⟩,
      { refine is_open_of_open_subgroup _,
        exact ⟨U, set.subset.trans (set.subset_union_left _ _) group.subset_closure⟩ },
      { apply_instance }
    end },
  le_sup_left := λ U V, set.subset.trans (set.subset_union_left _ _) group.subset_closure,
  le_sup_right := λ U V, set.subset.trans (set.subset_union_right _ _) group.subset_closure,
  sup_le := λ U V W hU hV, group.closure_subset $ set.union_subset hU hV,
  ..open_subgroup.lattice.semilattice_inf_top }

@[simp, to_additive] lemma coe_inf : (↑(U ⊓ V) : set G) = (U : set G) ∩ V := rfl

@[to_additive] lemma le_iff : U ≤ V ↔ (U : set G) ⊆ V := iff.rfl

end open_subgroup

namespace submodule
open open_add_subgroup
variables {R : Type*} {M : Type*} [comm_ring R]
variables [add_comm_group M] [topological_space M] [topological_add_group M] [module R M]

lemma is_open_of_open_submodule {P : submodule R M}
  (h : ∃ U : submodule R M, is_open (U : set M) ∧ U ≤ P) : is_open (P : set M) :=
let ⟨U, h₁, h₂⟩ := h in is_open_of_open_add_subgroup ⟨⟨U, h₁, by apply_instance⟩, h₂⟩

end submodule

namespace ideal
variables {R : Type*} [comm_ring R]
variables [topological_space R] [topological_ring R]

lemma is_open_of_open_subideal {I : ideal R}
  (h : ∃ U : ideal R, is_open (U : set R) ∧ U ≤ I) : is_open (I : set R) :=
submodule.is_open_of_open_submodule h

end ideal
