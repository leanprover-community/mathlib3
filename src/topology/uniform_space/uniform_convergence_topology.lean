/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import topology.uniform_space.uniform_convergence
import topology.uniform_space.pi
import topology.uniform_space.equiv

/-!
# Topology and uniform structure of uniform convergence

This files endows `α → β` with the topologies / uniform structures of
- uniform convergence on `α` (in the `uniform_convergence` namespace)
- uniform convergence on a specified family `𝔖` of sets of `α`
  (in the `uniform_convergence_on` namespace), also called `𝔖`-convergence

Usual examples of the second construction include :
- the topology of compact convergence, when `𝔖` is the set of compacts of `α`
- the strong topology on the dual of a TVS `E`, when `𝔖` is the set of Von Neuman bounded subsets
  of `E`
- the weak-* topology on the dual of a TVS `E`, when `𝔖` is the set of singletons of `E`.

## Main definitions

* `uniform_convergence.gen` : basis sets for the uniformity of uniform convergence
* `uniform_convergence.uniform_space` : uniform structure of uniform convergence
* `uniform_convergence_on.uniform_space` : uniform structure of 𝔖-convergence

## Main statements

* `uniform_convergence.uniform_continuous_eval` : evaluation is uniformly continuous
* `uniform_convergence.t2_space` : the topology of uniform convergence on `α → β` is T2 if
  `β` is T2.
* `uniform_convergence.tendsto_iff_tendsto_uniformly` : `uniform_convergence.uniform_space` is
  indeed the uniform structure of uniform convergence

* `uniform_convergence_on.uniform_continuous_eval_of_mem` : evaluation at a point contained in a
  set of `𝔖` is uniformly continuous
* `uniform_convergence.t2_space` : the topology of `𝔖`-convergence on `α → β` is T2 if
  `β` is T2 and `𝔖` covers `α`
* `uniform_convergence_on.tendsto_iff_tendsto_uniformly_on` :
  `uniform_convergence_on.uniform_space` is indeed the uniform structure of `𝔖`-convergence

## Implementation details

We do not declare these structures as instances, since they would conflict with `Pi.uniform_space`.

## TODO

* Show that the uniform structure of `𝔖`-convergence is exactly the structure of `𝔖'`-convergence,
  where `𝔖'` is the bornology generated by `𝔖`.
* Add a type synonym for `α → β` endowed with the structures of uniform convergence

## References

* [N. Bourbaki, *General Topology*][bourbaki1966]

## Tags

uniform convergence
-/


noncomputable theory
open_locale topological_space classical uniformity filter

local attribute [-instance] Pi.uniform_space
local attribute [-instance] Pi.topological_space

open set filter

namespace uniform_convergence

variables (α β : Type*) {γ ι : Type*}
variables {F : ι → α → β} {f : α → β} {s s' : set α} {x : α} {p : filter ι} {g : ι → α}

/-- Basis sets for the uniformity of uniform convergence -/
protected def gen (V : set (β × β)) : set ((α → β) × (α → β)) :=
  {uv : (α → β) × (α → β) | ∀ x, (uv.1 x, uv.2 x) ∈ V}

protected lemma is_basis_gen (𝓑 : filter_basis $ β × β) :
  is_basis (λ V : set (β × β), V ∈ 𝓑) (uniform_convergence.gen α β) :=
⟨𝓑.nonempty, λ U V hU hV, let ⟨z, hz, hzUV⟩ := 𝓑.inter_sets hU hV in ⟨z, hz, λ uv huv,
  ⟨λ x, inter_subset_left _ _ $ hzUV (huv x), λ x, inter_subset_right _ _ $ hzUV (huv x)⟩⟩⟩

/-- Filter basis for the uniformity of uniform convergence -/
protected def basis (𝓑 : filter_basis $ β × β) : filter_basis ((α → β) × (α → β)) :=
(uniform_convergence.is_basis_gen α β 𝓑).filter_basis

/-- Uuniformity of uniform convergence -/
protected def filter (𝓑 : filter_basis $ β × β) : filter ((α → β) × (α → β)) :=
(uniform_convergence.basis α β 𝓑).filter

local notation `Φ` :=
  λ (α β : Type*) (uvx : ((α → β) × (α → β)) × α), (uvx.1.1 uvx.2, uvx.1.2 uvx.2)

/-- This is a lower adjoint to `uniform_convergence.filter` (see `uniform_convergence.gc`).
The exact definition is not really interesting, but this allows us to prove many properties of
the uniform structure of uniform convergence using only results about Galois connections. -/
protected def lower_adjoint (𝓐 : filter $ (α → β) × (α → β)) : filter (β × β) :=
(𝓐 ×ᶠ ⊤).map (Φ α β)

protected lemma gc : galois_connection (uniform_convergence.lower_adjoint α β)
  (λ 𝓑, uniform_convergence.filter α β 𝓑.as_basis) :=
begin
  intros 𝓐 𝓑,
  symmetry,
  calc 𝓐 ≤ uniform_convergence.filter α β 𝓑.as_basis
      ↔ (uniform_convergence.basis α β 𝓑.as_basis).sets ⊆ 𝓐.sets :
        by rw [uniform_convergence.filter, ← filter_basis.generate, sets_iff_generate]
  ... ↔ ∀ U ∈ 𝓑, uniform_convergence.gen α β U ∈ 𝓐 : image_subset_iff
  ... ↔ ∀ U ∈ 𝓑, {uv | ∀ x, (uv, x) ∈
          {t : ((α → β) × (α → β)) × α | (t.1.1 t.2, t.1.2 t.2) ∈ U}} ∈ 𝓐 : iff.rfl
  ... ↔ ∀ U ∈ 𝓑, {uvx : ((α → β) × (α → β)) × α | (uvx.1.1 uvx.2, uvx.1.2 uvx.2) ∈ U} ∈
          𝓐 ×ᶠ (⊤ : filter α) : forall₂_congr (λ U hU, mem_prod_top.symm)
  ... ↔ uniform_convergence.lower_adjoint α β 𝓐 ≤ 𝓑 : iff.rfl,
end

variables [uniform_space β]

/-- Core of the uniform structure of uniform convergence -/
protected def uniform_core : uniform_space.core (α → β) :=
uniform_space.core.mk_of_basis (uniform_convergence.basis α β (𝓤 β).as_basis)
  (λ U ⟨V, hV, hVU⟩ f, hVU ▸ λ x, refl_mem_uniformity hV)
  (λ U ⟨V, hV, hVU⟩, hVU ▸ ⟨uniform_convergence.gen α β (prod.swap ⁻¹' V),
    ⟨prod.swap ⁻¹' V, tendsto_swap_uniformity hV, rfl⟩, λ uv huv x, huv x⟩)
  (λ U ⟨V, hV, hVU⟩, hVU ▸ let ⟨W, hW, hWV⟩ := comp_mem_uniformity_sets hV in
    ⟨uniform_convergence.gen α β W, ⟨W, hW, rfl⟩, λ uv ⟨w, huw, hwv⟩ x, hWV
      ⟨w x, by exact ⟨huw x, hwv x⟩⟩⟩)

/-- Uniform structure of uniform convergence -/
protected def uniform_space : uniform_space (α → β) :=
uniform_space.of_core (uniform_convergence.uniform_core α β)

local attribute [instance] uniform_convergence.uniform_space

protected lemma has_basis_uniformity :
  (𝓤 (α → β)).has_basis (λ V, V ∈ 𝓤 β)
  (uniform_convergence.gen α β) :=
(uniform_convergence.is_basis_gen α β (𝓤 β).as_basis).has_basis

/-- Topology of uniform convergence -/
protected def topological_space : topological_space (α → β) :=
(uniform_convergence.uniform_space α β).to_topological_space

protected lemma has_basis_nhds :
  (𝓝 f).has_basis (λ V, V ∈ 𝓤 β)
  (λ V, {g | (g, f) ∈ uniform_convergence.gen α β V}) :=
nhds_basis_uniformity (uniform_convergence.has_basis_uniformity α β)

variables {α}

lemma uniform_continuous_eval (x : α) : uniform_continuous (function.eval x : (α → β) → β) :=
begin
  change _ ≤ _,
  rw [map_le_iff_le_comap,
      (uniform_convergence.has_basis_uniformity α β).le_basis_iff ((𝓤 _).basis_sets.comap _)],
  exact λ U hU, ⟨U, hU, λ uv huv, huv x⟩
end

variables {β}

protected lemma mono : monotone (@uniform_convergence.uniform_space α γ) :=
λ u₁ u₂ hu, (uniform_convergence.gc α γ).monotone_u hu

protected lemma infi_eq {u : ι → uniform_space γ} :
  (@uniform_convergence.uniform_space α γ (⨅ i, u i)) =
  ⨅ i, (@uniform_convergence.uniform_space α γ (u i)) :=
begin
  ext : 1,
  change uniform_convergence.filter α γ (@uniformity _ (⨅ i, u i)).as_basis =
    @uniformity _ (⨅ i, (@uniform_convergence.uniform_space α γ (u i))),
  rw [infi_uniformity', infi_uniformity'],
  exact (uniform_convergence.gc α γ).u_infi
end

protected lemma inf_eq {u₁ u₂ : uniform_space γ} :
  (@uniform_convergence.uniform_space α γ (u₁ ⊓ u₂)) =
  (@uniform_convergence.uniform_space α γ u₁) ⊓ (@uniform_convergence.uniform_space α γ u₂) :=
begin
  rw [inf_eq_infi, inf_eq_infi, uniform_convergence.infi_eq],
  refine infi_congr (λ i, _),
  cases i; refl
end

protected lemma comap_eq {f : γ → β} :
  (@uniform_convergence.uniform_space α γ (‹uniform_space β›.comap f)) =
  (uniform_convergence.uniform_space α β).comap ((∘) f) :=
begin
  letI : uniform_space γ := ‹uniform_space β›.comap f,
  ext : 1,
  change (uniform_convergence.filter α γ (((𝓤 β).comap _).as_basis)) =
    (uniform_convergence.filter α β ((𝓤 β).as_basis)).comap _,
  have h₁ := filter.gc_map_comap (prod.map ((∘) f) ((∘) f)),
  have h₂ := filter.gc_map_comap (prod.map f f),
  have h₃ := uniform_convergence.gc α β,
  have h₄ := uniform_convergence.gc α γ,
  refine galois_connection.u_comm_of_l_comm h₁ h₂ h₃ h₄ (λ 𝓐, _),
  have : prod.map f f ∘ (Φ α γ) =
    (Φ α β) ∘ prod.map (prod.map ((∘) f) ((∘) f)) id,
  { ext; refl },
  rw [uniform_convergence.lower_adjoint, uniform_convergence.lower_adjoint, map_map, this,
      ← map_map, ← prod_map_map_eq'],
  refl
end

protected lemma postcomp_uniform_continuous [uniform_space γ] {f : γ → β}
  (hf : uniform_continuous f):
  uniform_continuous ((∘) f : (α → γ) → α → β) :=
uniform_continuous_iff.mpr $
calc uniform_convergence.uniform_space α γ
    ≤ @uniform_convergence.uniform_space α γ (‹uniform_space β›.comap f) :
      uniform_convergence.mono (uniform_continuous_iff.mp hf)
... = (uniform_convergence.uniform_space α β).comap ((∘) f) :
      uniform_convergence.comap_eq

/-- Turn a uniform isomorphism `γ ≃ᵤ β` to a uniform isomorphism `(α → γ) ≃ᵤ (α → β)`, with the
uniform structures of uniform convergence, by post-composing. -/
protected def congr_right [uniform_space γ] (e : γ ≃ᵤ β) :
  (α → γ) ≃ᵤ (α → β) :=
{ uniform_continuous_to_fun :=
    uniform_convergence.postcomp_uniform_continuous e.uniform_continuous,
  uniform_continuous_inv_fun :=
    uniform_convergence.postcomp_uniform_continuous e.symm.uniform_continuous,
  .. equiv.Pi_congr_right (λ a, e.to_equiv) }

protected lemma precomp_uniform_continuous {f : γ → α} :
  uniform_continuous (λ g : α → β, g ∘ f) :=
begin
  rw uniform_continuous_iff,
  change 𝓤 (α → β) ≤ (𝓤 (γ → β)).comap (prod.map (λ g : α → β, g ∘ f) (λ g : α → β, g ∘ f)),
  rw (uniform_convergence.has_basis_uniformity α β).le_basis_iff
    ((uniform_convergence.has_basis_uniformity γ β).comap _),
  exact λ U hU, ⟨U, hU, λ uv huv x, huv (f x)⟩
end

/-- Turn a bijection `γ ≃ α` to a uniform isomorphism `(γ → β) ≃ᵤ (α → β)`, with the uniform
structures of uniform convergence, by pre-composing. -/
protected def congr_left (e : γ ≃ α) :
  (γ → β) ≃ᵤ (α → β) :=
{ uniform_continuous_to_fun :=
    uniform_convergence.precomp_uniform_continuous,
  uniform_continuous_inv_fun :=
    uniform_convergence.precomp_uniform_continuous,
  .. equiv.arrow_congr e (equiv.refl _) }

lemma t2_space [t2_space β] : t2_space (α → β) :=
{ t2 :=
  begin
    letI : uniform_space (α → β) := uniform_convergence.uniform_space α β,
    letI : topological_space (α → β) := uniform_convergence.topological_space α β,
    intros f g h,
    obtain ⟨x, hx⟩ := not_forall.mp (mt funext h),
    exact separated_by_continuous (uniform_continuous_eval β x).continuous hx
  end }

protected lemma le_Pi : uniform_convergence.uniform_space α β ≤ Pi.uniform_space (λ _, β) :=
begin
  rw [le_iff_uniform_continuous_id, uniform_continuous_pi],
  intros x,
  exact uniform_continuous_eval β x
end

protected lemma tendsto_iff_tendsto_uniformly :
  tendsto F p (𝓝 f) ↔
  tendsto_uniformly F f p :=
begin
  letI : uniform_space (α → β) := uniform_convergence.uniform_space α β,
  rw [(uniform_convergence.has_basis_nhds α β).tendsto_right_iff, tendsto_uniformly],
  split;
  { intros h U hU,
    filter_upwards [h (prod.swap ⁻¹' U) (tendsto_swap_uniformity hU)],
    exact λ n, id }
end

/-- If `α → β × γ`, `α → β` and `α → γ` are equipped with the uniform structures of uniform
convergence, then the natural bijection between `(α → β × γ)` and `((α → β) × (α → γ))` is a
uniform isomorphism. -/
protected def uniform_equiv_prod_arrow [uniform_space γ] :
  (α → β × γ) ≃ᵤ ((α → β) × (α → γ)) :=
(equiv.arrow_prod_equiv_prod_arrow _ _ _).to_uniform_equiv_of_uniform_inducing
begin
  split,
  change comap (prod.map (equiv.arrow_prod_equiv_prod_arrow _ _ _)
    (equiv.arrow_prod_equiv_prod_arrow _ _ _)) _ = _,
  rw ← uniformity_comap rfl,
  congr,
  rw [prod.uniform_space, uniform_space.of_core_eq_to_core, prod.uniform_space,
      uniform_space.of_core_eq_to_core, uniform_space.comap_inf, uniform_convergence.inf_eq],
  congr;
  rw [← uniform_space.comap_comap, uniform_convergence.comap_eq];
  refl
end

variables (α) (δ : ι → Type*) [Π i, uniform_space (δ i)]

local attribute [-instance] uniform_convergence.uniform_space

/-- If `α → Π i, δ i` and each `α → δ i` are equipped with the uniform structures of uniform
convergence, then "swapping the arguments" is a uniform isomorphism between `α → Π i, δ i` and
`Π i, α → δ i`. -/
protected def uniform_equiv_Pi_comm : @uniform_equiv (α → Π i, δ i) (Π i, α → δ i)
  (@uniform_convergence.uniform_space α (Π i, δ i) (Pi.uniform_space δ))
  (@Pi.uniform_space ι (λ i, α → δ i) (λ i, uniform_convergence.uniform_space α (δ i))) :=
@equiv.to_uniform_equiv_of_uniform_inducing _ _
  (@uniform_convergence.uniform_space α (Π i, δ i) (Pi.uniform_space δ))
  (@Pi.uniform_space ι (λ i, α → δ i) (λ i, uniform_convergence.uniform_space α (δ i)))
  (equiv.Pi_comm _)
begin
  split,
  change comap (prod.map function.swap function.swap) _ = _,
  rw ← uniformity_comap rfl,
  congr,
  rw [Pi.uniform_space, uniform_space.of_core_eq_to_core, Pi.uniform_space,
      uniform_space.of_core_eq_to_core, uniform_space.comap_infi, uniform_convergence.infi_eq],
  refine infi_congr (λ i, _),
  rw [← uniform_space.comap_comap, uniform_convergence.comap_eq]
end

end uniform_convergence

namespace uniform_convergence_on

variables (α β : Type*) {γ ι : Type*} [uniform_space β] (𝔖 : set (set α))
variables {F : ι → α → β} {f : α → β} {s s' : set α} {x : α} {p : filter ι} {g : ι → α}

/-- Uniform structure of uniform convergence on the sets of `𝔖`. -/
protected def uniform_space : uniform_space (α → β) :=
⨅ (s : set α) (hs : s ∈ 𝔖), uniform_space.comap (λ f, s.restrict f)
  (uniform_convergence.uniform_space s β)

/-- Topology of uniform convergence on the sets of `𝔖`. -/
protected def topological_space : topological_space (α → β) :=
(uniform_convergence_on.uniform_space α β 𝔖).to_topological_space

protected lemma topological_space_eq :
  uniform_convergence_on.topological_space α β 𝔖 = ⨅ (s : set α) (hs : s ∈ 𝔖),
  topological_space.induced (λ f, s.restrict f) (uniform_convergence.topological_space s β) :=
begin
  simp only [uniform_convergence_on.topological_space, to_topological_space_infi,
    to_topological_space_infi, to_topological_space_comap],
  refl
end

protected lemma uniform_continuous_restrict (h : s ∈ 𝔖) :
  @uniform_continuous _ _ (uniform_convergence_on.uniform_space α β 𝔖)
  (uniform_convergence.uniform_space s β) s.restrict :=
begin
  change _ ≤ _,
  rw [uniform_convergence_on.uniform_space, map_le_iff_le_comap, uniformity, infi_uniformity],
  refine infi_le_of_le s _,
  rw infi_uniformity,
  exact infi_le _ h,
end

variables {α}

protected lemma mono ⦃u₁ u₂ : uniform_space γ⦄ (hu : u₁ ≤ u₂) ⦃𝔖₁ 𝔖₂ : set (set α)⦄
  (h𝔖 : 𝔖₂ ⊆ 𝔖₁) :
  @uniform_convergence_on.uniform_space α γ u₁ 𝔖₁ ≤
  @uniform_convergence_on.uniform_space α γ u₂ 𝔖₂ :=
calc @uniform_convergence_on.uniform_space α γ u₁ 𝔖₁
    ≤ @uniform_convergence_on.uniform_space α γ u₁ 𝔖₂ : infi_le_infi_of_subset h𝔖
... ≤ @uniform_convergence_on.uniform_space α γ u₂ 𝔖₂ : infi₂_mono
        (λ i hi, uniform_space.comap_mono $ uniform_convergence.mono hu)

lemma uniform_continuous_eval_of_mem {x : α} (hxs : x ∈ s) (hs : s ∈ 𝔖) :
  @uniform_continuous _ _ (uniform_convergence_on.uniform_space α β 𝔖) _ (function.eval x) :=
begin
  change _ ≤ _,
  rw [map_le_iff_le_comap, ((𝓤 _).basis_sets.comap _).ge_iff,
      uniform_convergence_on.uniform_space, infi_uniformity'],
  intros U hU,
  refine mem_infi_of_mem s _,
  rw infi_uniformity',
  exact mem_infi_of_mem hs (mem_comap.mpr
    ⟨ uniform_convergence.gen s β U,
      (uniform_convergence.has_basis_uniformity s β).mem_of_mem hU,
      λ uv huv, huv ⟨x, hxs⟩ ⟩)
end

variables {β} {𝔖}

protected lemma infi_eq {u : ι → uniform_space γ} :
  (@uniform_convergence_on.uniform_space α γ (⨅ i, u i) 𝔖) =
  ⨅ i, (@uniform_convergence_on.uniform_space α γ (u i) 𝔖) :=
begin
  simp_rw [uniform_convergence_on.uniform_space, uniform_convergence.infi_eq,
    uniform_space.comap_infi],
  rw infi_comm,
  exact infi_congr (λ s, infi_comm)
end

protected lemma inf_eq {u₁ u₂ : uniform_space γ} :
  (@uniform_convergence_on.uniform_space α γ (u₁ ⊓ u₂) 𝔖) =
  (@uniform_convergence_on.uniform_space α γ u₁ 𝔖) ⊓
  (@uniform_convergence_on.uniform_space α γ u₂ 𝔖) :=
begin
  rw [inf_eq_infi, inf_eq_infi, uniform_convergence_on.infi_eq],
  refine infi_congr (λ i, _),
  cases i; refl
end

protected lemma comap_eq {f : γ → β} :
  (@uniform_convergence_on.uniform_space α γ (‹uniform_space β›.comap f) 𝔖) =
  (uniform_convergence_on.uniform_space α β 𝔖).comap ((∘) f) :=
begin
  simp_rw [uniform_convergence_on.uniform_space, uniform_space.comap_infi,
            uniform_convergence.comap_eq, ← uniform_space.comap_comap],
  refl
end

protected lemma postcomp_uniform_continuous [uniform_space γ] {f : γ → β}
  (hf : uniform_continuous f):
  @uniform_continuous (α → γ) (α → β)
  (uniform_convergence_on.uniform_space α γ 𝔖) (uniform_convergence_on.uniform_space α β 𝔖)
  ((∘) f) :=
begin
  rw uniform_continuous_iff,
  calc uniform_convergence_on.uniform_space α γ 𝔖
      ≤ @uniform_convergence_on.uniform_space α γ (‹uniform_space β›.comap f) 𝔖 :
        uniform_convergence_on.mono (uniform_continuous_iff.mp hf) (subset_rfl)
  ... = (uniform_convergence_on.uniform_space α β 𝔖).comap ((∘) f) :
        uniform_convergence_on.comap_eq
end

/-- Turn a uniform isomorphism `γ ≃ᵤ β` to a uniform isomorphism `(α → γ) ≃ᵤ (α → β)`, with the
uniform structures of `𝔖`-convergence, by post-composing. -/
protected def congr_right [uniform_space γ] (e : γ ≃ᵤ β) :
  @uniform_equiv (α → γ) (α → β)
  (uniform_convergence_on.uniform_space α γ 𝔖) (uniform_convergence_on.uniform_space α β 𝔖) :=
{ uniform_continuous_to_fun :=
    uniform_convergence_on.postcomp_uniform_continuous e.uniform_continuous,
  uniform_continuous_inv_fun :=
    uniform_convergence_on.postcomp_uniform_continuous e.symm.uniform_continuous,
  .. equiv.Pi_congr_right (λ a, e.to_equiv) }

protected lemma precomp_uniform_continuous {𝔗 : set (set γ)} {f : γ → α}
  (hf : 𝔗 ⊆ (image f) ⁻¹' 𝔖) :
  @uniform_continuous (α → β) (γ → β)
  (uniform_convergence_on.uniform_space α β 𝔖) (uniform_convergence_on.uniform_space γ β 𝔗)
  (λ g : α → β, g ∘ f) :=
begin
  simp_rw [uniform_continuous_iff, uniform_convergence_on.uniform_space, uniform_space.comap_infi],
  refine le_infi₂ (λ t ht, infi_le_of_le (f '' t) $ infi_le_of_le (hf ht) _),
  rw ← uniform_space.comap_comap,
  let f' : t → f '' t := (maps_to_image f t).restrict f t (f '' t),
  have : restrict t ∘ (λ g : α → β, g ∘ f) = (λ g : (f '' t) → β, g ∘ f') ∘ restrict (f '' t) :=
    rfl,
  rw [this, @uniform_space.comap_comap (α → β) ((f '' t) → β)],
  refine uniform_space.comap_mono _,
  rw ← uniform_continuous_iff,
  exact uniform_convergence.precomp_uniform_continuous
end

lemma t2_space_of_covering [t2_space β] (h : ⋃₀ 𝔖 = univ) :
  @t2_space _ (uniform_convergence_on.topological_space α β 𝔖) :=
{ t2 :=
  begin
    letI : uniform_space (α → β) := uniform_convergence_on.uniform_space α β 𝔖,
    letI : topological_space (α → β) := uniform_convergence_on.topological_space α β 𝔖,
    intros f g hfg,
    obtain ⟨x, hx⟩ := not_forall.mp (mt funext hfg),
    obtain ⟨s, hs, hxs⟩ : ∃ s ∈ 𝔖, x ∈ s := mem_sUnion.mp (h.symm ▸ true.intro),
    exact separated_by_continuous (uniform_continuous_eval_of_mem β 𝔖 hxs hs).continuous hx
  end }

protected lemma le_Pi_of_covering (h : ⋃₀ 𝔖 = univ) :
  uniform_convergence_on.uniform_space α β 𝔖 ≤ Pi.uniform_space (λ _, β) :=
begin
  rw [le_iff_uniform_continuous_id, uniform_continuous_pi],
  intros x,
  obtain ⟨s, hs, hxs⟩ : ∃ s ∈ 𝔖, x ∈ s := mem_sUnion.mp (h.symm ▸ true.intro),
  exact uniform_continuous_eval_of_mem β 𝔖 hxs hs
end

protected lemma tendsto_iff_tendsto_uniformly_on :
  tendsto F p (@nhds _ (uniform_convergence_on.topological_space α β 𝔖) f) ↔
  ∀ s ∈ 𝔖, tendsto_uniformly_on F f p s :=
begin
  letI : uniform_space (α → β) := uniform_convergence_on.uniform_space α β 𝔖,
  rw [uniform_convergence_on.topological_space_eq, nhds_infi, tendsto_infi],
  refine forall_congr (λ s, _),
  rw [nhds_infi, tendsto_infi],
  refine forall_congr (λ hs, _),
  rw [nhds_induced, tendsto_comap_iff, tendsto_uniformly_on_iff_tendsto_uniformly_comp_coe,
      uniform_convergence.tendsto_iff_tendsto_uniformly],
  refl
end

/-- If `α → β × γ`, `α → β` and `α → γ` are equipped with the uniform structures of
`𝔖`-convergence, then the natural bijection between `(α → β × γ)` and `((α → β) × (α → γ))` is a
uniform isomorphism. -/
protected def uniform_equiv_prod_arrow [uniform_space γ] :
  @uniform_equiv (α → β × γ) ((α → β) × (α → γ))
  (uniform_convergence_on.uniform_space α (β × γ) 𝔖)
  (@prod.uniform_space _ _ (uniform_convergence_on.uniform_space α β 𝔖)
    (uniform_convergence_on.uniform_space α γ 𝔖)) :=
@equiv.to_uniform_equiv_of_uniform_inducing _ _
  (uniform_convergence_on.uniform_space α (β × γ) 𝔖)
  (@prod.uniform_space _ _ (uniform_convergence_on.uniform_space α β 𝔖)
    (uniform_convergence_on.uniform_space α γ 𝔖))
  (equiv.arrow_prod_equiv_prod_arrow _ _ _)
begin
  split,
  change comap (prod.map (equiv.arrow_prod_equiv_prod_arrow _ _ _)
    (equiv.arrow_prod_equiv_prod_arrow _ _ _)) _ = _,
  rw ← uniformity_comap rfl,
  congr,
  rw [prod.uniform_space, uniform_space.of_core_eq_to_core, prod.uniform_space,
      uniform_space.of_core_eq_to_core, uniform_space.comap_inf, uniform_convergence_on.inf_eq],
  congr;
  rw [← uniform_space.comap_comap, uniform_convergence_on.comap_eq];
  refl
end

variables (𝔖) (δ : ι → Type*) [Π i, uniform_space (δ i)]

/-- If `α → Π i, δ i` and each `α → δ i` are equipped with the uniform structures of
`𝔖`-convergence, then "swapping the arguments" is a uniform isomorphism between `α → Π i, δ i` and
`Π i, α → δ i`. -/
protected def uniform_equiv_Pi_comm : @uniform_equiv (α → Π i, δ i) (Π i, α → δ i)
  (@uniform_convergence_on.uniform_space α (Π i, δ i) (Pi.uniform_space δ) 𝔖)
  (@Pi.uniform_space ι (λ i, α → δ i) (λ i, uniform_convergence_on.uniform_space α (δ i) 𝔖)) :=
@equiv.to_uniform_equiv_of_uniform_inducing _ _
  (@uniform_convergence_on.uniform_space α (Π i, δ i) (Pi.uniform_space δ) 𝔖)
  (@Pi.uniform_space ι (λ i, α → δ i) (λ i, uniform_convergence_on.uniform_space α (δ i) 𝔖))
  (equiv.Pi_comm _)
begin
  split,
  change comap (prod.map function.swap function.swap) _ = _,
  rw ← uniformity_comap rfl,
  congr,
  rw [Pi.uniform_space, uniform_space.of_core_eq_to_core, Pi.uniform_space,
      uniform_space.of_core_eq_to_core, uniform_space.comap_infi, uniform_convergence_on.infi_eq],
  refine infi_congr (λ i, _),
  rw [← uniform_space.comap_comap, uniform_convergence_on.comap_eq]
end

end uniform_convergence_on
