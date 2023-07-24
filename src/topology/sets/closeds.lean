/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies
-/
import topology.sets.opens

/-!
# Closed sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define a few types of closed sets in a topological space.

## Main Definitions

For a topological space `α`,
* `closeds α`: The type of closed sets.
* `clopens α`: The type of clopen sets.
-/

open order order_dual set

variables {ι α β : Type*} [topological_space α] [topological_space β]

namespace topological_space

/-! ### Closed sets -/

/-- The type of closed subsets of a topological space. -/
structure closeds (α : Type*) [topological_space α] :=
(carrier : set α)
(closed' : is_closed carrier)

namespace closeds
variables {α}

instance : set_like (closeds α) α :=
{ coe := closeds.carrier,
  coe_injective' := λ s t h, by { cases s, cases t, congr' } }

lemma closed (s : closeds α) : is_closed (s : set α) := s.closed'

@[ext] protected lemma ext {s t : closeds α} (h : (s : set α) = t) : s = t := set_like.ext' h

@[simp] lemma coe_mk (s : set α) (h) : (mk s h : set α) = s := rfl

/-- The closure of a set, as an element of `closeds`. -/
protected def closure (s : set α) : closeds α := ⟨closure s, is_closed_closure⟩

lemma gc : galois_connection closeds.closure (coe : closeds α → set α) :=
λ s U, ⟨subset_closure.trans, λ h, closure_minimal h U.closed⟩

/-- The galois coinsertion between sets and opens. -/
def gi : galois_insertion (@closeds.closure α _) coe :=
{ choice := λ s hs, ⟨s, closure_eq_iff_is_closed.1 $ hs.antisymm subset_closure⟩,
  gc := gc,
  le_l_u := λ _, subset_closure,
  choice_eq := λ s hs, set_like.coe_injective $ subset_closure.antisymm hs }

instance : complete_lattice (closeds α) :=
complete_lattice.copy (galois_insertion.lift_complete_lattice gi)
/- le  -/ _ rfl
/- top -/ ⟨univ, is_closed_univ⟩ rfl
/- bot -/ ⟨∅, is_closed_empty⟩ (set_like.coe_injective closure_empty.symm)
/- sup -/ (λ s t, ⟨s ∪ t, s.2.union t.2⟩)
  (funext $ λ s, funext $ λ t, set_like.coe_injective (s.2.union t.2).closure_eq.symm)
/- inf -/ (λ s t, ⟨s ∩ t, s.2.inter t.2⟩) rfl
/- Sup -/ _ rfl
/- Inf -/ (λ S, ⟨⋂ s ∈ S, ↑s, is_closed_bInter $ λ s _, s.2⟩)
  (funext $ λ S, set_like.coe_injective Inf_image.symm)

/-- The type of closed sets is inhabited, with default element the empty set. -/
instance : inhabited (closeds α) := ⟨⊥⟩

@[simp, norm_cast] lemma coe_sup (s t : closeds α) : (↑(s ⊔ t) : set α) = s ∪ t := rfl
@[simp, norm_cast] lemma coe_inf (s t : closeds α) : (↑(s ⊓ t) : set α) = s ∩ t := rfl
@[simp, norm_cast] lemma coe_top : (↑(⊤ : closeds α) : set α) = univ := rfl
@[simp, norm_cast] lemma coe_bot : (↑(⊥ : closeds α) : set α) = ∅ := rfl
@[simp, norm_cast] lemma coe_Inf {S : set (closeds α)} : (↑(Inf S) : set α) = ⋂ i ∈ S, ↑i := rfl

@[simp, norm_cast] lemma coe_finset_sup (f : ι → closeds α) (s : finset ι) :
  (↑(s.sup f) : set α) = s.sup (coe ∘ f) :=
map_finset_sup (⟨⟨coe, coe_sup⟩, coe_bot⟩ : sup_bot_hom (closeds α) (set α)) _ _

@[simp, norm_cast] lemma coe_finset_inf (f : ι → closeds α) (s : finset ι) :
  (↑(s.inf f) : set α) = s.inf (coe ∘ f) :=
map_finset_inf (⟨⟨coe, coe_inf⟩, coe_top⟩ : inf_top_hom (closeds α) (set α)) _ _

lemma infi_def {ι} (s : ι → closeds α) : (⨅ i, s i) = ⟨⋂ i, s i, is_closed_Inter $ λ i, (s i).2⟩ :=
by { ext, simp only [infi, coe_Inf, bInter_range], refl }

@[simp] lemma infi_mk {ι} (s : ι → set α) (h : ∀ i, is_closed (s i)) :
  (⨅ i, ⟨s i, h i⟩ : closeds α) = ⟨⋂ i, s i, is_closed_Inter h⟩ :=
by simp [infi_def]

@[simp, norm_cast] lemma coe_infi {ι} (s : ι → closeds α) :
  ((⨅ i, s i : closeds α) : set α) = ⋂ i, s i :=
by simp [infi_def]

@[simp] lemma mem_infi {ι} {x : α} {s : ι → closeds α} : x ∈ infi s ↔ ∀ i, x ∈ s i :=
by simp [←set_like.mem_coe]

@[simp] lemma mem_Inf {S : set (closeds α)} {x : α} : x ∈ Inf S ↔ ∀ s ∈ S, x ∈ s :=
by simp_rw [Inf_eq_infi, mem_infi]

instance : coframe (closeds α) :=
{ Inf := Inf,
  infi_sup_le_sup_Inf := λ a s,
    (set_like.coe_injective $ by simp only [coe_sup, coe_infi, coe_Inf, set.union_Inter₂]).le,
  ..closeds.complete_lattice }

/-- The term of `closeds α` corresponding to a singleton. -/
@[simps] def singleton [t1_space α] (x : α) : closeds α :=
⟨{x}, is_closed_singleton⟩

end closeds

/-- The complement of a closed set as an open set. -/
@[simps] def closeds.compl (s : closeds α) : opens α := ⟨sᶜ, s.2.is_open_compl⟩

/-- The complement of an open set as a closed set. -/
@[simps] def opens.compl (s : opens α) : closeds α := ⟨sᶜ, s.2.is_closed_compl⟩

lemma closeds.compl_compl (s : closeds α) : s.compl.compl = s := closeds.ext (compl_compl s)
lemma opens.compl_compl (s : opens α) : s.compl.compl = s := opens.ext (compl_compl s)

lemma closeds.compl_bijective : function.bijective (@closeds.compl α _) :=
function.bijective_iff_has_inverse.mpr ⟨opens.compl, closeds.compl_compl, opens.compl_compl⟩
lemma opens.compl_bijective : function.bijective (@opens.compl α _) :=
function.bijective_iff_has_inverse.mpr ⟨closeds.compl, opens.compl_compl, closeds.compl_compl⟩

variables (α)

/-- `closeds.compl` as an `order_iso` to the order dual of `opens α`. -/
@[simps] def closeds.compl_order_iso : closeds α ≃o (opens α)ᵒᵈ :=
{ to_fun := order_dual.to_dual ∘ closeds.compl,
  inv_fun := opens.compl ∘ order_dual.of_dual,
  left_inv := λ s, by simp [closeds.compl_compl],
  right_inv := λ s, by simp [opens.compl_compl],
  map_rel_iff' := λ s t, by simpa only [equiv.coe_fn_mk, function.comp_app,
    order_dual.to_dual_le_to_dual] using compl_subset_compl }

/-- `opens.compl` as an `order_iso` to the order dual of `closeds α`. -/
@[simps] def opens.compl_order_iso : opens α ≃o (closeds α)ᵒᵈ :=
{ to_fun := order_dual.to_dual ∘ opens.compl,
  inv_fun := closeds.compl ∘ order_dual.of_dual,
  left_inv := λ s, by simp [opens.compl_compl],
  right_inv := λ s, by simp [closeds.compl_compl],
  map_rel_iff' := λ s t, by simpa only [equiv.coe_fn_mk, function.comp_app,
    order_dual.to_dual_le_to_dual] using compl_subset_compl }

variables {α}

/-- in a `t1_space`, atoms of `closeds α` are precisely the `closeds.singleton`s. -/
lemma closeds.is_atom_iff [t1_space α] {s : closeds α} : is_atom s ↔ ∃ x, s = closeds.singleton x :=
begin
  have : is_atom (s : set α) ↔ is_atom s,
  { refine closeds.gi.is_atom_iff' rfl (λ t ht, _) s,
    obtain ⟨x, rfl⟩ := t.is_atom_iff.mp ht,
    exact closure_singleton },
  simpa only [← this, (s : set α).is_atom_iff, set_like.ext_iff, set.ext_iff]
end

/-- in a `t1_space`, coatoms of `opens α` are precisely complements of singletons:
`(closeds.singleton x).compl`. -/
lemma opens.is_coatom_iff [t1_space α] {s : opens α} :
  is_coatom s ↔ ∃ x, s = (closeds.singleton x).compl :=
begin
  rw [←s.compl_compl, ←is_atom_dual_iff_is_coatom],
  change is_atom (closeds.compl_order_iso α s.compl) ↔ _,
  rw [(closeds.compl_order_iso α).is_atom_iff, closeds.is_atom_iff],
  congrm ∃ x, _,
  exact closeds.compl_bijective.injective.eq_iff.symm,
end

/-! ### Clopen sets -/

/-- The type of clopen sets of a topological space. -/
structure clopens (α : Type*) [topological_space α] :=
(carrier : set α)
(clopen' : is_clopen carrier)

namespace clopens

instance : set_like (clopens α) α :=
{ coe := λ s, s.carrier,
  coe_injective' := λ s t h, by { cases s, cases t, congr' } }

lemma clopen (s : clopens α) : is_clopen (s : set α) := s.clopen'

/-- Reinterpret a compact open as an open. -/
@[simps] def to_opens (s : clopens α) : opens α := ⟨s, s.clopen.is_open⟩

@[ext] protected lemma ext {s t : clopens α} (h : (s : set α) = t) : s = t := set_like.ext' h

@[simp] lemma coe_mk (s : set α) (h) : (mk s h : set α) = s := rfl

instance : has_sup (clopens α) := ⟨λ s t, ⟨s ∪ t, s.clopen.union t.clopen⟩⟩
instance : has_inf (clopens α) := ⟨λ s t, ⟨s ∩ t, s.clopen.inter t.clopen⟩⟩
instance : has_top (clopens α) := ⟨⟨⊤, is_clopen_univ⟩⟩
instance : has_bot (clopens α) := ⟨⟨⊥, is_clopen_empty⟩⟩
instance : has_sdiff (clopens α) := ⟨λ s t, ⟨s \ t, s.clopen.diff t.clopen⟩⟩
instance : has_compl (clopens α) := ⟨λ s, ⟨sᶜ, s.clopen.compl⟩⟩

instance : boolean_algebra (clopens α) :=
set_like.coe_injective.boolean_algebra _ (λ _ _, rfl) (λ _ _, rfl) rfl rfl (λ _, rfl) (λ _ _, rfl)

@[simp] lemma coe_sup (s t : clopens α) : (↑(s ⊔ t) : set α) = s ∪ t := rfl
@[simp] lemma coe_inf (s t : clopens α) : (↑(s ⊓ t) : set α) = s ∩ t := rfl
@[simp] lemma coe_top : (↑(⊤ : clopens α) : set α) = univ := rfl
@[simp] lemma coe_bot : (↑(⊥ : clopens α) : set α) = ∅ := rfl
@[simp] lemma coe_sdiff (s t : clopens α) : (↑(s \ t) : set α) = s \ t := rfl
@[simp] lemma coe_compl (s : clopens α) : (↑sᶜ : set α) = sᶜ := rfl

instance : inhabited (clopens α) := ⟨⊥⟩

end clopens
end topological_space
