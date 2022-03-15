/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn
-/
import order.hom.complete_lattice
import topology.bases
import topology.homeomorph
import topology.continuous_function.basic

/-!
# Open sets

## Summary

We define the subtype of open sets in a topological space.

## Main Definitions

- `opens α` is the type of open subsets of a topological space `α`.
- `open_nhds_of x` is the type of open subsets of a topological space `α` containing `x : α`.
-/

open filter function order set

variables {α β γ : Type*} [topological_space α] [topological_space β] [topological_space γ]

namespace topological_space
variable (α)
/-- The type of open subsets of a topological space. -/
def opens := {s : set α // is_open s}

variable {α}
namespace opens
instance : has_coe (opens α) (set α) := { coe := subtype.val }

lemma val_eq_coe (U : opens α) : U.1 = ↑U := rfl

/-- the coercion `opens α → set α` applied to a pair is the same as taking the first component -/
lemma coe_mk {α : Type*} [topological_space α] {U : set α} {hU : is_open U} :
  ↑(⟨U, hU⟩ : opens α) = U := rfl

instance : has_subset (opens α) :=
{ subset := λ U V, (U : set α) ⊆ V }

instance : has_mem α (opens α) :=
{ mem := λ a U, a ∈ (U : set α) }

@[simp] lemma subset_coe {U V : opens α} : ((U : set α) ⊆ (V : set α)) = (U ⊆ V) := rfl

@[simp] lemma mem_coe {x : α} {U : opens α} : (x ∈ (U : set α)) = (x ∈ U) := rfl

@[ext] lemma ext {U V : opens α} (h : (U : set α) = V) : U = V := subtype.ext h
@[ext] lemma ext_iff {U V : opens α} : (U : set α) = V ↔ U = V := subtype.ext_iff.symm

instance : partial_order (opens α) := subtype.partial_order _

/-- The interior of a set, as an element of `opens`. -/
def interior (s : set α) : opens α := ⟨interior s, is_open_interior⟩

lemma gc : galois_connection (coe : opens α → set α) interior :=
λ U s, ⟨λ h, interior_maximal h U.property, λ h, le_trans h interior_subset⟩

open order_dual (of_dual to_dual)

/-- The galois coinsertion between sets and opens. -/
def gi : galois_coinsertion subtype.val (@interior α _) :=
{ choice := λ s hs, ⟨s, interior_eq_iff_open.mp $ le_antisymm interior_subset hs⟩,
  gc := gc,
  u_l_le := λ _, interior_subset,
  choice_eq := λ s hs, le_antisymm hs interior_subset }

instance : complete_lattice (opens α) :=
complete_lattice.copy (galois_coinsertion.lift_complete_lattice gi)
/- le  -/ (λ U V, U ⊆ V) rfl
/- top -/ ⟨univ, is_open_univ⟩ (ext interior_univ.symm)
/- bot -/ ⟨∅, is_open_empty⟩ rfl
/- sup -/ (λ U V, ⟨↑U ∪ ↑V, U.2.union V.2⟩) rfl
/- inf -/ (λ U V, ⟨↑U ∩ ↑V, U.2.inter V.2⟩)
  (funext $ λ U, funext $ λ V, ext (U.2.inter V.2).interior_eq.symm)
/- Sup -/ _ rfl
/- Inf -/ _ rfl

lemma le_def {U V : opens α} : U ≤ V ↔ (U : set α) ≤ (V : set α) := iff.rfl

@[simp] lemma mk_inf_mk {U V : set α} {hU : is_open U} {hV : is_open V} :
  (⟨U, hU⟩ ⊓ ⟨V, hV⟩ : opens α) = ⟨U ⊓ V, is_open.inter hU hV⟩ := rfl
@[simp, norm_cast] lemma coe_inf {U V : opens α} : ((U ⊓ V : opens α) : set α) = U ∩ V := rfl
@[simp] lemma coe_bot : ((⊥ : opens α) : set α) = ∅ := rfl
@[simp] lemma coe_top : ((⊤ : opens α) : set α) = set.univ := rfl
@[simp] lemma coe_Sup {S : set (opens α)} : (↑(Sup S) : set α) = ⋃ i ∈ S, ↑i := (@gc α _).l_Sup

instance : has_inter (opens α) := ⟨λ U V, U ⊓ V⟩
instance : has_union (opens α) := ⟨λ U V, U ⊔ V⟩
instance : has_emptyc (opens α) := ⟨⊥⟩
instance : inhabited (opens α) := ⟨∅⟩

@[simp] lemma inter_eq (U V : opens α) : U ∩ V = U ⊓ V := rfl
@[simp] lemma union_eq (U V : opens α) : U ∪ V = U ⊔ V := rfl
@[simp] lemma empty_eq : (∅ : opens α) = ⊥ := rfl

lemma supr_def {ι} (s : ι → opens α) : (⨆ i, s i) = ⟨⋃ i, s i, is_open_Union $ λ i, (s i).2⟩ :=
by { ext, simp only [supr, coe_Sup, bUnion_range], refl }

@[simp] lemma supr_mk {ι} (s : ι → set α) (h : Π i, is_open (s i)) :
  (⨆ i, ⟨s i, h i⟩ : opens α) = ⟨⋃ i, s i, is_open_Union h⟩ :=
by { rw supr_def, simp }

@[simp] lemma supr_s {ι} (s : ι → opens α) : ((⨆ i, s i : opens α) : set α) = ⋃ i, s i :=
by simp [supr_def]

@[simp] theorem mem_supr {ι} {x : α} {s : ι → opens α} : x ∈ supr s ↔ ∃ i, x ∈ s i :=
by { rw [←mem_coe], simp, }

@[simp] lemma mem_Sup {Us : set (opens α)} {x : α} : x ∈ Sup Us ↔ ∃ u ∈ Us, x ∈ u :=
by simp_rw [Sup_eq_supr, mem_supr]

instance : frame (opens α) :=
{ Sup := Sup,
  inf_Sup_le_supr_inf := λ a s,
    (ext $ by simp only [coe_inf, supr_s, coe_Sup, set.inter_Union₂]).le,
  ..opens.complete_lattice }

lemma open_embedding_of_le {U V : opens α} (i : U ≤ V) :
  open_embedding (set.inclusion i) :=
{ inj := set.inclusion_injective i,
  induced := (@induced_compose _ _ _ _ (set.inclusion i) coe).symm,
  open_range :=
  begin
    rw set.range_inclusion i,
    exact U.property.preimage continuous_subtype_val
  end, }

lemma not_nonempty_iff_eq_bot (U : opens α) : ¬ set.nonempty (U : set α) ↔ U = ⊥ :=
by rw [← subtype.coe_injective.eq_iff, opens.coe_bot, ← set.not_nonempty_iff_eq_empty]

lemma ne_bot_iff_nonempty (U : opens α) : U ≠ ⊥ ↔ set.nonempty (U : set α) :=
by rw [ne.def, ← opens.not_nonempty_iff_eq_bot, not_not]

/-- A set of `opens α` is a basis if the set of corresponding sets is a topological basis. -/
def is_basis (B : set (opens α)) : Prop := is_topological_basis ((coe : _ → set α) '' B)

lemma is_basis_iff_nbhd {B : set (opens α)} :
  is_basis B ↔ ∀ {U : opens α} {x}, x ∈ U → ∃ U' ∈ B, x ∈ U' ∧ U' ⊆ U :=
begin
  split; intro h,
  { rintros ⟨sU, hU⟩ x hx,
    rcases h.mem_nhds_iff.mp (is_open.mem_nhds hU hx)
      with ⟨sV, ⟨⟨V, H₁, H₂⟩, hsV⟩⟩,
    refine ⟨V, H₁, _⟩,
    cases V, dsimp at H₂, subst H₂, exact hsV },
  { refine is_topological_basis_of_open_of_nhds _ _,
    { rintros sU ⟨U, ⟨H₁, H₂⟩⟩, subst H₂, exact U.property },
    { intros x sU hx hsU,
      rcases @h (⟨sU, hsU⟩ : opens α) x hx with ⟨V, hV, H⟩,
      exact ⟨V, ⟨V, hV, rfl⟩, H⟩ } }
end

lemma is_basis_iff_cover {B : set (opens α)} :
  is_basis B ↔ ∀ U : opens α, ∃ Us ⊆ B, U = Sup Us :=
begin
  split,
  { intros hB U,
    refine ⟨{V : opens α | V ∈ B ∧ V ⊆ U}, λ U hU, hU.left, _⟩,
    apply ext,
    rw [coe_Sup, hB.open_eq_sUnion' U.prop],
    simp_rw [sUnion_eq_bUnion, Union, supr_and, supr_image],
    refl },
  { intro h,
    rw is_basis_iff_nbhd,
    intros U x hx,
    rcases h U with ⟨Us, hUs, rfl⟩,
    rcases mem_Sup.1 hx with ⟨U, Us, xU⟩,
    exact ⟨U, hUs Us, xU, le_Sup Us⟩ }
end

/-- The preimage of an open set, as an open set. -/
def comap (f : C(α, β)) : frame_hom (opens β) (opens α) :=
{ to_fun := λ s, ⟨f ⁻¹' s, s.2.preimage f.continuous⟩,
  map_Sup' := λ s, ext $ by simp only [coe_Sup, preimage_Union, coe_mk, mem_image, Union_exists,
    bUnion_and', Union_Union_eq_right],
  map_inf' := λ a b, rfl }

@[simp] lemma comap_id : comap (continuous_map.id α) = frame_hom.id _ :=
frame_hom.ext $ λ a, ext rfl

lemma comap_mono (f : C(α, β)) {s t : opens β} (h : s ≤ t) : comap f s ≤ comap f t :=
order_hom_class.mono (comap f) h

@[simp] lemma coe_comap (f : C(α, β)) (U : opens β) : ↑(comap f U) = f ⁻¹' U := rfl

@[simp] lemma comap_val (f : C(α, β)) (U : opens β) : (comap f U).1 = f ⁻¹' U := rfl

protected lemma comap_comp (g : C(β, γ)) (f : C(α, β)) :
  comap (g.comp f) = (comap f).comp (comap g) := rfl

protected lemma comap_comap (g : C(β, γ)) (f : C(α, β)) (U : opens γ) :
  comap f (comap g U) = comap (g.comp f) U := rfl

lemma comap_injective [t0_space β] : injective (comap : C(α, β) → frame_hom (opens β) (opens α)) :=
λ f g h, continuous_map.ext $ λ a, indistinguishable.eq $ λ s hs, begin
  simp_rw ←mem_preimage,
  congr' 2,
  have := fun_like.congr_fun h ⟨_, hs⟩,
  exact congr_arg (coe : opens α → set α) this,
end

/-- A homeomorphism induces an equivalence on open sets, by taking comaps. -/
@[simp] protected def equiv (f : α ≃ₜ β) : opens α ≃ opens β :=
{ to_fun := opens.comap f.symm.to_continuous_map,
  inv_fun := opens.comap f.to_continuous_map,
  left_inv := by { intro U, ext1, exact f.to_equiv.preimage_symm_preimage _ },
  right_inv := by { intro U, ext1, exact f.to_equiv.symm_preimage_preimage _ } }

/-- A homeomorphism induces an order isomorphism on open sets, by taking comaps. -/
@[simp] protected def order_iso (f : α ≃ₜ β) : opens α ≃o opens β :=
{ to_equiv := opens.equiv f,
  map_rel_iff' := λ U V, f.symm.surjective.preimage_subset_preimage_iff }

end opens

/-- The open neighborhoods of a point. See also `opens` or `nhds`. -/
def open_nhds_of (x : α) : Type* := { s : set α // is_open s ∧ x ∈ s }

instance open_nhds_of.inhabited {α : Type*} [topological_space α] (x : α) :
  inhabited (open_nhds_of x) := ⟨⟨set.univ, is_open_univ, set.mem_univ _⟩⟩

end topological_space
