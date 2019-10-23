/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Subtype of open subsets in a topological space.
-/
import topology.bases topology.separation

open filter lattice
variables {α : Type*} {β : Type*} [topological_space α] [topological_space β]

namespace topological_space
variable (α)
/-- The type of open subsets of a topological space. -/
def opens := {s : set α // _root_.is_open s}

/-- The type of closed subsets of a topological space. -/
def closeds := {s : set α // is_closed s}

/-- The type of non-empty compact subsets of a topological space. The
non-emptiness will be useful in metric spaces, as we will be able to put
a distance (and not merely an edistance) on this space. -/
def nonempty_compacts := {s : set α // s ≠ ∅ ∧ compact s}

section nonempty_compacts
open topological_space set
variable {α}

instance nonempty_compacts.to_compact_space {p : nonempty_compacts α} : compact_space p.val :=
⟨compact_iff_compact_univ.1 p.property.2⟩

instance nonempty_compacts.to_nonempty {p : nonempty_compacts α} : nonempty p.val :=
nonempty_subtype.2 $ ne_empty_iff_exists_mem.1 p.property.1

/-- Associate to a nonempty compact subset the corresponding closed subset -/
def nonempty_compacts.to_closeds [t2_space α] (s : nonempty_compacts α) : closeds α :=
⟨s.val, closed_of_compact _ s.property.2⟩

end nonempty_compacts

variable {α}
namespace opens
instance : has_coe (opens α) (set α) := { coe := subtype.val }

instance : has_subset (opens α) :=
{ subset := λ U V, U.val ⊆ V.val }

instance : has_mem α (opens α) :=
{ mem := λ a U, a ∈ U.val }

@[extensionality] lemma ext {U V : opens α} (h : U.val = V.val) : U = V := subtype.ext.mpr h

instance : partial_order (opens α) := subtype.partial_order _

def interior (s : set α) : opens α := ⟨interior s, is_open_interior⟩

lemma gc : galois_connection (subtype.val : opens α → set α) interior :=
λ U s, ⟨λ h, interior_maximal h U.property, λ h, le_trans h interior_subset⟩

def gi : @galois_insertion (order_dual (set α)) (order_dual (opens α)) _ _ interior (subtype.val) :=
{ choice := λ s hs, ⟨s, interior_eq_iff_open.mp $ le_antisymm interior_subset hs⟩,
  gc := gc.dual,
  le_l_u := λ _, interior_subset,
  choice_eq := λ s hs, le_antisymm interior_subset hs }

@[simp] lemma gi_choice_val {s : order_dual (set α)} {hs} : (gi.choice s hs).val = s := rfl

instance : complete_lattice (opens α) :=
complete_lattice.copy
(@order_dual.lattice.complete_lattice _
  (@galois_insertion.lift_complete_lattice
    (order_dual (set α)) (order_dual (opens α)) _ interior (subtype.val : opens α → set α) _ gi))
/- le  -/ (λ U V, U.1 ⊆ V.1) rfl
/- top -/ ⟨set.univ, _root_.is_open_univ⟩ (subtype.ext.mpr interior_univ.symm)
/- bot -/ ⟨∅, is_open_empty⟩ rfl
/- sup -/ (λ U V, ⟨U.1 ∪ V.1, _root_.is_open_union U.2 V.2⟩) rfl
/- inf -/ (λ U V, ⟨U.1 ∩ V.1, _root_.is_open_inter U.2 V.2⟩)
begin
  funext,
  apply subtype.ext.mpr,
  symmetry,
  apply interior_eq_of_open,
  exact (_root_.is_open_inter U.2 V.2),
end
/- Sup -/ (λ Us, ⟨⋃₀ (subtype.val '' Us), _root_.is_open_sUnion $ λ U hU,
by { rcases hU with ⟨⟨V, hV⟩, h, h'⟩, dsimp at h', subst h', exact hV}⟩)
begin
  funext,
  apply subtype.ext.mpr,
  simp [Sup_range],
  refl,
end
/- Inf -/ _ rfl

instance : has_inter (opens α) := ⟨λ U V, U ⊓ V⟩
instance : has_union (opens α) := ⟨λ U V, U ⊔ V⟩
instance : has_emptyc (opens α) := ⟨⊥⟩

@[simp] lemma inter_eq (U V : opens α) : U ∩ V = U ⊓ V := rfl
@[simp] lemma union_eq (U V : opens α) : U ∪ V = U ⊔ V := rfl
@[simp] lemma empty_eq : (∅ : opens α) = ⊥ := rfl

@[simp] lemma Sup_s {Us : set (opens α)} : (Sup Us).val = ⋃₀ (subtype.val '' Us) :=
begin
  rw [@galois_connection.l_Sup (opens α) (set α) _ _ (subtype.val : opens α → set α) interior gc Us, set.sUnion_image],
  congr
end

def is_basis (B : set (opens α)) : Prop := is_topological_basis (subtype.val '' B)

lemma is_basis_iff_nbhd {B : set (opens α)} :
  is_basis B ↔ ∀ {U : opens α} {x}, x ∈ U → ∃ U' ∈ B, x ∈ U' ∧ U' ⊆ U :=
begin
  split; intro h,
  { rintros ⟨sU, hU⟩ x hx,
    rcases (mem_nhds_of_is_topological_basis h).mp (mem_nhds_sets hU hx) with ⟨sV, ⟨⟨V, H₁, H₂⟩, hsV⟩⟩,
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
    rcases sUnion_basis_of_is_open hB U.property with ⟨sUs, H, hU⟩,
    existsi {U : opens α | U ∈ B ∧ U.val ∈ sUs},
    split,
    { intros U hU, exact hU.left },
    { apply ext,
      rw [Sup_s, hU],
      congr,
      ext s; split; intro hs,
      { rcases H hs with ⟨V, hV⟩,
        rw ← hV.right at hs,
        refine ⟨V, ⟨⟨hV.left, hs⟩, hV.right⟩⟩ },
      { rcases hs with ⟨V, ⟨⟨H₁, H₂⟩, H₃⟩⟩,
        subst H₃, exact H₂ } } },
  { intro h,
    rw is_basis_iff_nbhd,
    intros U x hx,
    rcases h U with ⟨Us, hUs, H⟩,
    replace H := congr_arg subtype.val H,
    rw Sup_s at H,
    change x ∈ U.val at hx,
    rw H at hx,
    rcases set.mem_sUnion.mp hx with ⟨sV, ⟨⟨V, H₁, H₂⟩, hsV⟩⟩,
    refine ⟨V,hUs H₁,_⟩,
    cases V with V hV,
    dsimp at H₂, subst H₂,
    refine ⟨hsV,_⟩,
    change V ⊆ U.val, rw H,
    exact set.subset_sUnion_of_mem ⟨⟨V, _⟩, ⟨H₁, rfl⟩⟩ }
end

end opens

end topological_space

namespace continuous
open topological_space

def comap {f : α → β} (hf : continuous f) (V : opens β) : opens α :=
⟨f ⁻¹' V.1, hf V.1 V.2⟩

@[simp] lemma comap_id (U : opens α) : (continuous_id).comap U = U := by { ext, refl }

lemma comap_mono {f : α → β} (hf : continuous f) {V W : opens β} (hVW : V ⊆ W) :
  hf.comap V ⊆ hf.comap W :=
λ _ h, hVW h

end continuous
