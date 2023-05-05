/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn
-/
import order.hom.complete_lattice
import topology.bases
import topology.homeomorph
import topology.continuous_function.basic
import order.compactly_generated
import tactic.auto_cases

/-!
# Open sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Summary

We define the subtype of open sets in a topological space.

## Main Definitions

### Bundled open sets

- `opens α` is the type of open subsets of a topological space `α`.
- `opens.is_basis` is a predicate saying that a set of `opens`s form a topological basis.
- `opens.comap`: preimage of an open set under a continuous map as a `frame_hom`.
- `homeomorph.opens_congr`: order-preserving equivalence between open sets in the domain and the
  codomain of a homeomorphism.

### Bundled open neighborhoods

- `open_nhds_of x` is the type of open subsets of a topological space `α` containing `x : α`.
- `open_nhds_of.comap f x U` is the preimage of open neighborhood `U` of `f x` under `f : C(α, β)`.

## Main results

We define order structures on both `opens α` (`complete_structure`, `frame`) and `open_nhds_of x`
(`order_top`, `distrib_lattice`).
-/

open filter function order set
open_locale topology

variables {ι α β γ : Type*} [topological_space α] [topological_space β] [topological_space γ]

namespace topological_space

variable (α)

/-- The type of open subsets of a topological space. -/
structure opens :=
(carrier : set α)
(is_open' : is_open carrier)

variable {α}

namespace opens

instance : set_like (opens α) α :=
{ coe := opens.carrier,
  coe_injective' := λ ⟨_, _⟩ ⟨_, _⟩ _, by congr; assumption }

instance : can_lift (set α) (opens α) coe is_open :=
⟨λ s h, ⟨⟨s, h⟩, rfl⟩⟩

lemma «forall» {p : opens α → Prop} : (∀ U, p U) ↔ ∀ (U : set α) (hU : is_open U), p ⟨U, hU⟩ :=
⟨λ h _ _, h _, λ h ⟨U, hU⟩, h _ _⟩

@[simp] lemma carrier_eq_coe (U : opens α) : U.1 = ↑U := rfl

/-- the coercion `opens α → set α` applied to a pair is the same as taking the first component -/
@[simp] lemma coe_mk {U : set α} {hU : is_open U} : ↑(⟨U, hU⟩ : opens α) = U := rfl

@[simp] lemma mem_mk {x : α} {U : set α} {h : is_open U} :
  @has_mem.mem _ (opens α) _ x ⟨U, h⟩ ↔ x ∈ U := iff.rfl

-- todo: make it `simp` for a `set_like`?
@[simp] protected lemma nonempty_coe_sort {U : opens α} : nonempty U ↔ (U : set α).nonempty :=
set.nonempty_coe_sort

@[ext] lemma ext {U V : opens α} (h : (U : set α) = V) : U = V := set_like.coe_injective h
@[simp] lemma coe_inj {U V : opens α} : (U : set α) = V ↔ U = V := set_like.ext'_iff.symm

protected lemma is_open (U : opens α) : is_open (U : set α) := U.is_open'

@[simp] lemma mk_coe (U : opens α) : mk ↑U U.is_open = U := by { cases U, refl }

/-- See Note [custom simps projection]. -/
def simps.coe (U : opens α) : set α := U

initialize_simps_projections opens (carrier → coe)

/-- The interior of a set, as an element of `opens`. -/
def interior (s : set α) : opens α := ⟨interior s, is_open_interior⟩

lemma gc : galois_connection (coe : opens α → set α) interior :=
λ U s, ⟨λ h, interior_maximal h U.is_open, λ h, le_trans h interior_subset⟩

/-- The galois coinsertion between sets and opens. -/
def gi : galois_coinsertion coe (@interior α _) :=
{ choice := λ s hs, ⟨s, interior_eq_iff_is_open.mp $ le_antisymm interior_subset hs⟩,
  gc := gc,
  u_l_le := λ _, interior_subset,
  choice_eq := λ s hs, le_antisymm hs interior_subset }

instance : complete_lattice (opens α) :=
complete_lattice.copy (galois_coinsertion.lift_complete_lattice gi)
/- le  -/ (λ U V, (U : set α) ⊆ V) rfl
/- top -/ ⟨univ, is_open_univ⟩ (ext interior_univ.symm)
/- bot -/ ⟨∅, is_open_empty⟩ rfl
/- sup -/ (λ U V, ⟨↑U ∪ ↑V, U.2.union V.2⟩) rfl
/- inf -/ (λ U V, ⟨↑U ∩ ↑V, U.2.inter V.2⟩) (funext₂ $ λ U V, ext (U.2.inter V.2).interior_eq.symm)
/- Sup -/ (λ S, ⟨⋃ s ∈ S, ↑s, is_open_bUnion $ λ s _, s.2⟩) (funext $ λ S, ext Sup_image.symm)
/- Inf -/ _ rfl

@[simp] lemma mk_inf_mk {U V : set α} {hU : is_open U} {hV : is_open V} :
  (⟨U, hU⟩ ⊓ ⟨V, hV⟩ : opens α) = ⟨U ⊓ V, is_open.inter hU hV⟩ := rfl
@[simp, norm_cast] lemma coe_inf (s t : opens α) : (↑(s ⊓ t) : set α) = s ∩ t := rfl
@[simp, norm_cast] lemma coe_sup (s t : opens α) : (↑(s ⊔ t) : set α) = s ∪ t := rfl
@[simp, norm_cast] lemma coe_bot : ((⊥ : opens α) : set α) = ∅ := rfl
@[simp, norm_cast] lemma coe_top : ((⊤ : opens α) : set α) = set.univ := rfl
@[simp, norm_cast] lemma coe_Sup {S : set (opens α)} : (↑(Sup S) : set α) = ⋃ i ∈ S, ↑i := rfl

@[simp, norm_cast] lemma coe_finset_sup (f : ι → opens α) (s : finset ι) :
  (↑(s.sup f) : set α) = s.sup (coe ∘ f) :=
map_finset_sup (⟨⟨coe, coe_sup⟩, coe_bot⟩ : sup_bot_hom (opens α) (set α)) _ _

@[simp, norm_cast] lemma coe_finset_inf (f : ι → opens α) (s : finset ι) :
  (↑(s.inf f) : set α) = s.inf (coe ∘ f) :=
map_finset_inf (⟨⟨coe, coe_inf⟩, coe_top⟩ : inf_top_hom (opens α) (set α)) _ _

instance : inhabited (opens α) := ⟨⊥⟩

lemma supr_def {ι} (s : ι → opens α) : (⨆ i, s i) = ⟨⋃ i, s i, is_open_Union $ λ i, (s i).2⟩ :=
by { ext, simp only [supr, coe_Sup, bUnion_range], refl }

@[simp] lemma supr_mk {ι} (s : ι → set α) (h : Π i, is_open (s i)) :
  (⨆ i, ⟨s i, h i⟩ : opens α) = ⟨⋃ i, s i, is_open_Union h⟩ :=
by { rw supr_def, simp }

@[simp, norm_cast] lemma coe_supr {ι} (s : ι → opens α) :
  ((⨆ i, s i : opens α) : set α) = ⋃ i, s i :=
by simp [supr_def]

@[simp] theorem mem_supr {ι} {x : α} {s : ι → opens α} : x ∈ supr s ↔ ∃ i, x ∈ s i :=
by { rw [← set_like.mem_coe], simp, }

@[simp] lemma mem_Sup {Us : set (opens α)} {x : α} : x ∈ Sup Us ↔ ∃ u ∈ Us, x ∈ u :=
by simp_rw [Sup_eq_supr, mem_supr]

instance : frame (opens α) :=
{ Sup := Sup,
  inf_Sup_le_supr_inf := λ a s,
    (ext $ by simp only [coe_inf, coe_supr, coe_Sup, set.inter_Union₂]).le,
  ..opens.complete_lattice }

lemma open_embedding_of_le {U V : opens α} (i : U ≤ V) :
  open_embedding (set.inclusion i) :=
{ inj := set.inclusion_injective i,
  induced := (@induced_compose _ _ _ _ (set.inclusion i) coe).symm,
  open_range :=
  begin
    rw set.range_inclusion i,
    exact U.is_open.preimage continuous_subtype_val
  end, }

lemma not_nonempty_iff_eq_bot (U : opens α) : ¬ set.nonempty (U : set α) ↔ U = ⊥ :=
by rw [← coe_inj, opens.coe_bot, ← set.not_nonempty_iff_eq_empty]

lemma ne_bot_iff_nonempty (U : opens α) : U ≠ ⊥ ↔ set.nonempty (U : set α) :=
by rw [ne.def, ← opens.not_nonempty_iff_eq_bot, not_not]

/-- An open set in the indiscrete topology is either empty or the whole space. -/
lemma eq_bot_or_top {α} [t : topological_space α] (h : t = ⊤) (U : opens α) : U = ⊥ ∨ U = ⊤ :=
begin
  simp only [← coe_inj],
  unfreezingI { subst h }, letI : topological_space α := ⊤,
  exact (is_open_top_iff _).1 U.2
end

/-- A set of `opens α` is a basis if the set of corresponding sets is a topological basis. -/
def is_basis (B : set (opens α)) : Prop := is_topological_basis ((coe : _ → set α) '' B)

lemma is_basis_iff_nbhd {B : set (opens α)} :
  is_basis B ↔ ∀ {U : opens α} {x}, x ∈ U → ∃ U' ∈ B, x ∈ U' ∧ U' ≤ U :=
begin
  split; intro h,
  { rintros ⟨sU, hU⟩ x hx,
    rcases h.mem_nhds_iff.mp (is_open.mem_nhds hU hx)
      with ⟨sV, ⟨⟨V, H₁, H₂⟩, hsV⟩⟩,
    refine ⟨V, H₁, _⟩,
    cases V, dsimp at H₂, subst H₂, exact hsV },
  { refine is_topological_basis_of_open_of_nhds _ _,
    { rintros sU ⟨U, ⟨H₁, rfl⟩⟩, exact U.2 },
    { intros x sU hx hsU,
      rcases @h (⟨sU, hsU⟩ : opens α) x hx with ⟨V, hV, H⟩,
      exact ⟨V, ⟨V, hV, rfl⟩, H⟩ } }
end

lemma is_basis_iff_cover {B : set (opens α)} :
  is_basis B ↔ ∀ U : opens α, ∃ Us ⊆ B, U = Sup Us :=
begin
  split,
  { intros hB U,
    refine ⟨{V : opens α | V ∈ B ∧ V ≤ U}, λ U hU, hU.left, _⟩,
    apply ext,
    rw [coe_Sup, hB.open_eq_sUnion' U.is_open],
    simp_rw [sUnion_eq_bUnion, Union, supr_and, supr_image],
    refl },
  { intro h,
    rw is_basis_iff_nbhd,
    intros U x hx,
    rcases h U with ⟨Us, hUs, rfl⟩,
    rcases mem_Sup.1 hx with ⟨U, Us, xU⟩,
    exact ⟨U, hUs Us, xU, le_Sup Us⟩ }
end

/-- If `α` has a basis consisting of compact opens, then an open set in `α` is compact open iff
  it is a finite union of some elements in the basis -/
lemma is_basis.is_compact_open_iff_eq_finite_Union
  {ι : Type*} (b : ι → opens α) (hb : is_basis (set.range b))
  (hb' : ∀ i, is_compact (b i : set α)) (U : set α) :
  is_compact U ∧ is_open U ↔ ∃ (s : set ι), s.finite ∧ U = ⋃ i ∈ s, b i :=
begin
  apply is_compact_open_iff_eq_finite_Union_of_is_topological_basis
    (λ i : ι, (b i).1),
  { convert hb, ext, simp },
  { exact hb' }
end

@[simp] lemma is_compact_element_iff (s : opens α) :
  complete_lattice.is_compact_element s ↔ is_compact (s : set α) :=
begin
  rw [is_compact_iff_finite_subcover, complete_lattice.is_compact_element_iff],
  refine ⟨_, λ H ι U hU, _⟩,
  { introv H hU hU',
    obtain ⟨t, ht⟩ := H ι (λ i, ⟨U i, hU i⟩) (by simpa),
    refine ⟨t, set.subset.trans ht _⟩,
    rw [coe_finset_sup, finset.sup_eq_supr],
    refl },
  { obtain ⟨t, ht⟩ := H (λ i, U i) (λ i, (U i).is_open)
      (by simpa using (show (s : set α) ⊆ ↑(supr U), from hU)),
    refine ⟨t, set.subset.trans ht _⟩,
    simp only [set.Union_subset_iff],
    show ∀ i ∈ t, U i ≤ t.sup U, from λ i, finset.le_sup }
end

/-- The preimage of an open set, as an open set. -/
def comap (f : C(α, β)) : frame_hom (opens β) (opens α) :=
{ to_fun := λ s, ⟨f ⁻¹' s, s.2.preimage f.continuous⟩,
  map_Sup' := λ s, ext $ by simp only [coe_Sup, preimage_Union, bUnion_image, coe_mk],
  map_inf' := λ a b, rfl,
  map_top' := rfl }

@[simp] lemma comap_id : comap (continuous_map.id α) = frame_hom.id _ :=
frame_hom.ext $ λ a, ext rfl

lemma comap_mono (f : C(α, β)) {s t : opens β} (h : s ≤ t) : comap f s ≤ comap f t :=
order_hom_class.mono (comap f) h

@[simp] lemma coe_comap (f : C(α, β)) (U : opens β) : ↑(comap f U) = f ⁻¹' U := rfl

protected lemma comap_comp (g : C(β, γ)) (f : C(α, β)) :
  comap (g.comp f) = (comap f).comp (comap g) := rfl

protected lemma comap_comap (g : C(β, γ)) (f : C(α, β)) (U : opens γ) :
  comap f (comap g U) = comap (g.comp f) U := rfl

lemma comap_injective [t0_space β] : injective (comap : C(α, β) → frame_hom (opens β) (opens α)) :=
λ f g h, continuous_map.ext $ λ a, inseparable.eq $ inseparable_iff_forall_open.2 $ λ s hs,
have comap f ⟨s, hs⟩ = comap g ⟨s, hs⟩, from fun_like.congr_fun h ⟨_, hs⟩,
show a ∈ f ⁻¹' s ↔ a ∈ g ⁻¹' s, from set.ext_iff.1 (coe_inj.2 this) a

/-- A homeomorphism induces an order-preserving equivalence on open sets, by taking comaps. -/
@[simps apply { fully_applied := ff }]
def _root_.homeomorph.opens_congr (f : α ≃ₜ β) : opens α ≃o opens β :=
{ to_fun := opens.comap f.symm.to_continuous_map,
  inv_fun := opens.comap f.to_continuous_map,
  left_inv := by { intro U, ext1, exact f.to_equiv.preimage_symm_preimage _ },
  right_inv := by { intro U, ext1, exact f.to_equiv.symm_preimage_preimage _ },
  map_rel_iff' := λ U V, by simp only [← set_like.coe_subset_coe];
    exact f.symm.surjective.preimage_subset_preimage_iff }

@[simp] lemma _root_.homeomorph.opens_congr_symm (f : α ≃ₜ β) :
  f.opens_congr.symm = f.symm.opens_congr :=
rfl

instance [finite α] : finite (opens α) := finite.of_injective _ set_like.coe_injective

end opens

/-- The open neighborhoods of a point. See also `opens` or `nhds`. -/
structure open_nhds_of (x : α) extends opens α :=
(mem' : x ∈ carrier)

namespace open_nhds_of

variables {x : α}

lemma to_opens_injective : injective (to_opens : open_nhds_of x → opens α)
| ⟨_, _⟩ ⟨_, _⟩ rfl := rfl

instance : set_like (open_nhds_of x) α :=
{ coe := λ U, U.1,
  coe_injective' := set_like.coe_injective.comp to_opens_injective }

instance can_lift_set : can_lift (set α) (open_nhds_of x) coe (λ s, is_open s ∧ x ∈ s) :=
⟨λ s hs, ⟨⟨⟨s, hs.1⟩, hs.2⟩, rfl⟩⟩

protected lemma mem (U : open_nhds_of x) : x ∈ U := U.mem'
protected lemma is_open (U : open_nhds_of x) : is_open (U : set α) := U.is_open'

instance : order_top (open_nhds_of x) :=
{ top := ⟨⊤, set.mem_univ _⟩,
  le_top := λ _, subset_univ _ }

instance : inhabited (open_nhds_of x) := ⟨⊤⟩

instance : has_inf (open_nhds_of x) := ⟨λ U V, ⟨U.1 ⊓ V.1, U.2, V.2⟩⟩

instance : has_sup (open_nhds_of x) := ⟨λ U V, ⟨U.1 ⊔ V.1, or.inl U.2⟩⟩

instance : distrib_lattice (open_nhds_of x) :=
to_opens_injective.distrib_lattice _ (λ _ _, rfl) (λ _ _, rfl)

lemma basis_nhds : (𝓝 x).has_basis (λ U : open_nhds_of x, true) coe :=
(nhds_basis_opens x).to_has_basis (λ U hU, ⟨⟨⟨U, hU.2⟩, hU.1⟩, trivial, subset.rfl⟩)
  (λ U _, ⟨U, ⟨⟨U.mem, U.is_open⟩, subset.rfl⟩⟩)

/-- Preimage of an open neighborhood of `f x` under a continuous map `f` as a `lattice_hom`. -/
def comap (f : C(α, β)) (x : α) : lattice_hom (open_nhds_of (f x)) (open_nhds_of x) :=
{ to_fun := λ U, ⟨opens.comap f U.1, U.mem⟩,
  map_sup' := λ U V, rfl,
  map_inf' := λ U V, rfl }

end open_nhds_of

end topological_space

namespace tactic

namespace auto_cases

/-- Find an `auto_cases_tac` which matches `topological_space.opens`. -/
meta def opens_find_tac : expr → option auto_cases_tac
| `(topological_space.opens _)     := tac_cases
| _ := none

end auto_cases

/-- A version of `tactic.auto_cases` that works for `topological_space.opens`. -/
@[hint_tactic]
meta def auto_cases_opens : tactic string :=
auto_cases tactic.auto_cases.opens_find_tac

end tactic
