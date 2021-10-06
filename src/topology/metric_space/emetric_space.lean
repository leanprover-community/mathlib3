/-
Copyright (c) 2015, 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
import data.nat.interval
import data.real.ennreal
import topology.uniform_space.pi
import topology.uniform_space.uniform_convergence
import topology.uniform_space.uniform_embedding

/-!
# Extended metric spaces

This file is devoted to the definition and study of `emetric_spaces`, i.e., metric
spaces in which the distance is allowed to take the value ∞. This extended distance is
called `edist`, and takes values in `ℝ≥0∞`.

Many definitions and theorems expected on emetric spaces are already introduced on uniform spaces
and topological spaces. For example: open and closed sets, compactness, completeness, continuity and
uniform continuity.

The class `emetric_space` therefore extends `uniform_space` (and `topological_space`).

Since a lot of elementary properties don't require `eq_of_edist_eq_zero` we start setting up the
theory of `pseudo_emetric_space`, where we don't require `edist x y = 0 → x = y` and we specialize
to `emetric_space` at the end.
-/

open set filter classical
noncomputable theory

open_locale uniformity topological_space big_operators filter nnreal ennreal

universes u v w
variables {α : Type u} {β : Type v}

/-- Characterizing uniformities associated to a (generalized) distance function `D`
in terms of the elements of the uniformity. -/
theorem uniformity_dist_of_mem_uniformity [linear_order β] {U : filter (α × α)} (z : β)
  (D : α → α → β) (H : ∀ s, s ∈ U ↔ ∃ε>z, ∀{a b:α}, D a b < ε → (a, b) ∈ s) :
  U = ⨅ ε>z, 𝓟 {p:α×α | D p.1 p.2 < ε} :=
le_antisymm
  (le_infi $ λ ε, le_infi $ λ ε0, le_principal_iff.2 $ (H _).2 ⟨ε, ε0, λ a b, id⟩)
  (λ r ur, let ⟨ε, ε0, h⟩ := (H _).1 ur in
    mem_infi_of_mem ε $ mem_infi_of_mem ε0 $ mem_principal.2 $ λ ⟨a, b⟩, h)

/-- `has_edist α` means that `α` is equipped with an extended distance. -/
class has_edist (α : Type*) := (edist : α → α → ℝ≥0∞)
export has_edist (edist)

/-- Creating a uniform space from an extended distance. -/
def uniform_space_of_edist
  (edist : α → α → ℝ≥0∞)
  (edist_self : ∀ x : α, edist x x = 0)
  (edist_comm : ∀ x y : α, edist x y = edist y x)
  (edist_triangle : ∀ x y z : α, edist x z ≤ edist x y + edist y z) : uniform_space α :=
uniform_space.of_core {
  uniformity := (⨅ ε>0, 𝓟 {p:α×α | edist p.1 p.2 < ε}),
  refl       := le_infi $ assume ε, le_infi $
    by simp [set.subset_def, id_rel, edist_self, (>)] {contextual := tt},
  comp       :=
    le_infi $ assume ε, le_infi $ assume h,
    have (2 : ℝ≥0∞) = (2 : ℕ) := by simp,
    have A : 0 < ε / 2 := ennreal.div_pos_iff.2
      ⟨ne_of_gt h, by { convert ennreal.nat_ne_top 2 }⟩,
    lift'_le
    (mem_infi_of_mem (ε / 2) $ mem_infi_of_mem A (subset.refl _)) $
    have ∀ (a b c : α), edist a c < ε / 2 → edist c b < ε / 2 → edist a b < ε,
      from assume a b c hac hcb,
      calc edist a b ≤ edist a c + edist c b : edist_triangle _ _ _
        ... < ε / 2 + ε / 2 : ennreal.add_lt_add hac hcb
        ... = ε : by rw [ennreal.add_halves],
    by simpa [comp_rel],
  symm       := tendsto_infi.2 $ assume ε, tendsto_infi.2 $ assume h,
    tendsto_infi' ε $ tendsto_infi' h $ tendsto_principal_principal.2 $ by simp [edist_comm] }

-- the uniform structure is embedded in the emetric space structure
-- to avoid instance diamond issues. See Note [forgetful inheritance].

/-- Extended (pseudo) metric spaces, with an extended distance `edist` possibly taking the
value ∞

Each pseudo_emetric space induces a canonical `uniform_space` and hence a canonical
`topological_space`.
This is enforced in the type class definition, by extending the `uniform_space` structure. When
instantiating a `pseudo_emetric_space` structure, the uniformity fields are not necessary, they
will be filled in by default. There is a default value for the uniformity, that can be substituted
in cases of interest, for instance when instantiating a `pseudo_emetric_space` structure
on a product.

Continuity of `edist` is proved in `topology.instances.ennreal`
-/
class pseudo_emetric_space (α : Type u) extends has_edist α : Type u :=
(edist_self : ∀ x : α, edist x x = 0)
(edist_comm : ∀ x y : α, edist x y = edist y x)
(edist_triangle : ∀ x y z : α, edist x z ≤ edist x y + edist y z)
(to_uniform_space : uniform_space α :=
  uniform_space_of_edist edist edist_self edist_comm edist_triangle)
(uniformity_edist : 𝓤 α = ⨅ ε>0, 𝓟 {p:α×α | edist p.1 p.2 < ε} . control_laws_tac)

/- Pseudoemetric spaces are less common than metric spaces. Therefore, we work in a dedicated
namespace, while notions associated to metric spaces are mostly in the root namespace. -/
variables [pseudo_emetric_space α]

@[priority 100] -- see Note [lower instance priority]
instance pseudo_emetric_space.to_uniform_space' : uniform_space α :=
pseudo_emetric_space.to_uniform_space

export pseudo_emetric_space (edist_self edist_comm edist_triangle)

attribute [simp] edist_self

/-- Triangle inequality for the extended distance -/
theorem edist_triangle_left (x y z : α) : edist x y ≤ edist z x + edist z y :=
by rw edist_comm z; apply edist_triangle

theorem edist_triangle_right (x y z : α) : edist x y ≤ edist x z + edist y z :=
by rw edist_comm y; apply edist_triangle

lemma edist_triangle4 (x y z t : α) :
  edist x t ≤ edist x y + edist y z + edist z t :=
calc
  edist x t ≤ edist x z + edist z t : edist_triangle x z t
... ≤ (edist x y + edist y z) + edist z t : add_le_add_right (edist_triangle x y z) _

/-- The triangle (polygon) inequality for sequences of points; `finset.Ico` version. -/
lemma edist_le_Ico_sum_edist (f : ℕ → α) {m n} (h : m ≤ n) :
  edist (f m) (f n) ≤ ∑ i in finset.Ico m n, edist (f i) (f (i + 1)) :=
begin
  revert n,
  refine nat.le_induction _ _,
  { simp only [finset.sum_empty, finset.Ico_self, edist_self],
    -- TODO: Why doesn't Lean close this goal automatically? `apply le_refl` fails too.
    exact le_refl (0:ℝ≥0∞) },
  { assume n hn hrec,
    calc edist (f m) (f (n+1)) ≤ edist (f m) (f n) + edist (f n) (f (n+1)) : edist_triangle _ _ _
      ... ≤ ∑ i in finset.Ico m n, _ + _ : add_le_add hrec le_rfl
      ... = ∑ i in finset.Ico m (n+1), _ :
        by rw [nat.Ico_succ_right_eq_insert_Ico hn, finset.sum_insert, add_comm]; simp }
end

/-- The triangle (polygon) inequality for sequences of points; `finset.range` version. -/
lemma edist_le_range_sum_edist (f : ℕ → α) (n : ℕ) :
  edist (f 0) (f n) ≤ ∑ i in finset.range n, edist (f i) (f (i + 1)) :=
nat.Ico_zero_eq_range n ▸ edist_le_Ico_sum_edist f (nat.zero_le n)

/-- A version of `edist_le_Ico_sum_edist` with each intermediate distance replaced
with an upper estimate. -/
lemma edist_le_Ico_sum_of_edist_le {f : ℕ → α} {m n} (hmn : m ≤ n)
  {d : ℕ → ℝ≥0∞} (hd : ∀ {k}, m ≤ k → k < n → edist (f k) (f (k + 1)) ≤ d k) :
  edist (f m) (f n) ≤ ∑ i in finset.Ico m n, d i :=
le_trans (edist_le_Ico_sum_edist f hmn) $
finset.sum_le_sum $ λ k hk, hd (finset.mem_Ico.1 hk).1 (finset.mem_Ico.1 hk).2

/-- A version of `edist_le_range_sum_edist` with each intermediate distance replaced
with an upper estimate. -/
lemma edist_le_range_sum_of_edist_le {f : ℕ → α} (n : ℕ)
  {d : ℕ → ℝ≥0∞} (hd : ∀ {k}, k < n → edist (f k) (f (k + 1)) ≤ d k) :
  edist (f 0) (f n) ≤ ∑ i in finset.range n, d i :=
nat.Ico_zero_eq_range n ▸ edist_le_Ico_sum_of_edist_le (zero_le n) (λ _ _, hd)

/-- Reformulation of the uniform structure in terms of the extended distance -/
theorem uniformity_pseudoedist :
  𝓤 α = ⨅ ε>0, 𝓟 {p:α×α | edist p.1 p.2 < ε} :=
pseudo_emetric_space.uniformity_edist

theorem uniformity_basis_edist :
  (𝓤 α).has_basis (λ ε : ℝ≥0∞, 0 < ε) (λ ε, {p:α×α | edist p.1 p.2 < ε}) :=
(@uniformity_pseudoedist α _).symm ▸ has_basis_binfi_principal
  (λ r hr p hp, ⟨min r p, lt_min hr hp,
    λ x hx, lt_of_lt_of_le hx (min_le_left _ _),
    λ x hx, lt_of_lt_of_le hx (min_le_right _ _)⟩)
  ⟨1, ennreal.zero_lt_one⟩

/-- Characterization of the elements of the uniformity in terms of the extended distance -/
theorem mem_uniformity_edist {s : set (α×α)} :
  s ∈ 𝓤 α ↔ (∃ε>0, ∀{a b:α}, edist a b < ε → (a, b) ∈ s) :=
uniformity_basis_edist.mem_uniformity_iff

/-- Given `f : β → ℝ≥0∞`, if `f` sends `{i | p i}` to a set of positive numbers
accumulating to zero, then `f i`-neighborhoods of the diagonal form a basis of `𝓤 α`.

For specific bases see `uniformity_basis_edist`, `uniformity_basis_edist'`,
`uniformity_basis_edist_nnreal`, and `uniformity_basis_edist_inv_nat`. -/
protected theorem emetric.mk_uniformity_basis {β : Type*} {p : β → Prop} {f : β → ℝ≥0∞}
  (hf₀ : ∀ x, p x → 0 < f x) (hf : ∀ ε, 0 < ε → ∃ x (hx : p x), f x ≤ ε) :
  (𝓤 α).has_basis p (λ x, {p:α×α | edist p.1 p.2 < f x}) :=
begin
  refine ⟨λ s, uniformity_basis_edist.mem_iff.trans _⟩,
  split,
  { rintros ⟨ε, ε₀, hε⟩,
    rcases hf ε ε₀ with ⟨i, hi, H⟩,
    exact ⟨i, hi, λ x hx, hε $ lt_of_lt_of_le hx H⟩ },
  { exact λ ⟨i, hi, H⟩, ⟨f i, hf₀ i hi, H⟩ }
end

/-- Given `f : β → ℝ≥0∞`, if `f` sends `{i | p i}` to a set of positive numbers
accumulating to zero, then closed `f i`-neighborhoods of the diagonal form a basis of `𝓤 α`.

For specific bases see `uniformity_basis_edist_le` and `uniformity_basis_edist_le'`. -/
protected theorem emetric.mk_uniformity_basis_le {β : Type*} {p : β → Prop} {f : β → ℝ≥0∞}
  (hf₀ : ∀ x, p x → 0 < f x) (hf : ∀ ε, 0 < ε → ∃ x (hx : p x), f x ≤ ε) :
  (𝓤 α).has_basis p (λ x, {p:α×α | edist p.1 p.2 ≤ f x}) :=
begin
  refine ⟨λ s, uniformity_basis_edist.mem_iff.trans _⟩,
  split,
  { rintros ⟨ε, ε₀, hε⟩,
    rcases exists_between ε₀ with ⟨ε', hε'⟩,
    rcases hf ε' hε'.1 with ⟨i, hi, H⟩,
    exact ⟨i, hi, λ x hx, hε $ lt_of_le_of_lt (le_trans hx H) hε'.2⟩ },
  { exact λ ⟨i, hi, H⟩, ⟨f i, hf₀ i hi, λ x hx, H (le_of_lt hx)⟩ }
end

theorem uniformity_basis_edist_le :
  (𝓤 α).has_basis (λ ε : ℝ≥0∞, 0 < ε) (λ ε, {p:α×α | edist p.1 p.2 ≤ ε}) :=
emetric.mk_uniformity_basis_le (λ _, id) (λ ε ε₀, ⟨ε, ε₀, le_refl ε⟩)

theorem uniformity_basis_edist' (ε' : ℝ≥0∞) (hε' : 0 < ε') :
  (𝓤 α).has_basis (λ ε : ℝ≥0∞, ε ∈ Ioo 0 ε') (λ ε, {p:α×α | edist p.1 p.2 < ε}) :=
emetric.mk_uniformity_basis (λ _, and.left)
  (λ ε ε₀, let ⟨δ, hδ⟩ := exists_between hε' in
    ⟨min ε δ, ⟨lt_min ε₀ hδ.1, lt_of_le_of_lt (min_le_right _ _) hδ.2⟩, min_le_left _ _⟩)

theorem uniformity_basis_edist_le' (ε' : ℝ≥0∞) (hε' : 0 < ε') :
  (𝓤 α).has_basis (λ ε : ℝ≥0∞, ε ∈ Ioo 0 ε') (λ ε, {p:α×α | edist p.1 p.2 ≤ ε}) :=
emetric.mk_uniformity_basis_le (λ _, and.left)
  (λ ε ε₀, let ⟨δ, hδ⟩ := exists_between hε' in
    ⟨min ε δ, ⟨lt_min ε₀ hδ.1, lt_of_le_of_lt (min_le_right _ _) hδ.2⟩, min_le_left _ _⟩)

theorem uniformity_basis_edist_nnreal :
  (𝓤 α).has_basis (λ ε : ℝ≥0, 0 < ε) (λ ε, {p:α×α | edist p.1 p.2 < ε}) :=
emetric.mk_uniformity_basis (λ _, ennreal.coe_pos.2)
  (λ ε ε₀, let ⟨δ, hδ⟩ := ennreal.lt_iff_exists_nnreal_btwn.1 ε₀ in
  ⟨δ, ennreal.coe_pos.1 hδ.1, le_of_lt hδ.2⟩)

theorem uniformity_basis_edist_inv_nat :
  (𝓤 α).has_basis (λ _, true) (λ n:ℕ, {p:α×α | edist p.1 p.2 < (↑n)⁻¹}) :=
emetric.mk_uniformity_basis
  (λ n _, ennreal.inv_pos.2 $ ennreal.nat_ne_top n)
  (λ ε ε₀, let ⟨n, hn⟩ := ennreal.exists_inv_nat_lt (ne_of_gt ε₀) in ⟨n, trivial, le_of_lt hn⟩)

theorem uniformity_basis_edist_inv_two_pow :
  (𝓤 α).has_basis (λ _, true) (λ n:ℕ, {p:α×α | edist p.1 p.2 < 2⁻¹ ^ n}) :=
emetric.mk_uniformity_basis
  (λ n _, ennreal.pow_pos (ennreal.inv_pos.2 ennreal.two_ne_top) _)
  (λ ε ε₀, let ⟨n, hn⟩ := ennreal.exists_inv_two_pow_lt (ne_of_gt ε₀) in ⟨n, trivial, le_of_lt hn⟩)

/-- Fixed size neighborhoods of the diagonal belong to the uniform structure -/
theorem edist_mem_uniformity {ε:ℝ≥0∞} (ε0 : 0 < ε) :
  {p:α×α | edist p.1 p.2 < ε} ∈ 𝓤 α :=
mem_uniformity_edist.2 ⟨ε, ε0, λ a b, id⟩

namespace emetric

theorem uniformity_has_countable_basis : is_countably_generated (𝓤 α) :=
is_countably_generated_of_seq ⟨_, uniformity_basis_edist_inv_nat.eq_infi⟩

/-- ε-δ characterization of uniform continuity on a set for pseudoemetric spaces -/
theorem uniform_continuous_on_iff [pseudo_emetric_space β] {f : α → β} {s : set α} :
  uniform_continuous_on f s ↔ ∀ ε > 0, ∃ δ > 0,
    ∀{a b}, a ∈ s → b ∈ s → edist a b < δ → edist (f a) (f b) < ε :=
uniformity_basis_edist.uniform_continuous_on_iff uniformity_basis_edist

/-- ε-δ characterization of uniform continuity on pseudoemetric spaces -/
theorem uniform_continuous_iff [pseudo_emetric_space β] {f : α → β} :
  uniform_continuous f ↔ ∀ ε > 0, ∃ δ > 0,
    ∀{a b:α}, edist a b < δ → edist (f a) (f b) < ε :=
uniformity_basis_edist.uniform_continuous_iff uniformity_basis_edist

/-- ε-δ characterization of uniform embeddings on pseudoemetric spaces -/
theorem uniform_embedding_iff [pseudo_emetric_space β] {f : α → β} :
  uniform_embedding f ↔ function.injective f ∧ uniform_continuous f ∧
    ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, edist (f a) (f b) < ε → edist a b < δ :=
uniform_embedding_def'.trans $ and_congr iff.rfl $ and_congr iff.rfl
⟨λ H δ δ0, let ⟨t, tu, ht⟩ := H _ (edist_mem_uniformity δ0),
               ⟨ε, ε0, hε⟩ := mem_uniformity_edist.1 tu in
  ⟨ε, ε0, λ a b h, ht _ _ (hε h)⟩,
 λ H s su, let ⟨δ, δ0, hδ⟩ := mem_uniformity_edist.1 su, ⟨ε, ε0, hε⟩ := H _ δ0 in
  ⟨_, edist_mem_uniformity ε0, λ a b h, hδ (hε h)⟩⟩

/-- If a map between pseudoemetric spaces is a uniform embedding then the edistance between `f x`
and `f y` is controlled in terms of the distance between `x` and `y`. -/
theorem controlled_of_uniform_embedding [pseudo_emetric_space β] {f : α → β} :
  uniform_embedding f →
  (∀ ε > 0, ∃ δ > 0, ∀ {a b : α}, edist a b < δ → edist (f a) (f b) < ε) ∧
  (∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, edist (f a) (f b) < ε → edist a b < δ) :=
begin
  assume h,
    exact ⟨uniform_continuous_iff.1 (uniform_embedding_iff.1 h).2.1,
          (uniform_embedding_iff.1 h).2.2⟩,
end

/-- ε-δ characterization of Cauchy sequences on pseudoemetric spaces -/
protected lemma cauchy_iff {f : filter α} :
  cauchy f ↔ f ≠ ⊥ ∧ ∀ ε > 0, ∃ t ∈ f, ∀ x y ∈ t, edist x y < ε :=
by rw ← ne_bot_iff; exact uniformity_basis_edist.cauchy_iff

/-- A very useful criterion to show that a space is complete is to show that all sequences
which satisfy a bound of the form `edist (u n) (u m) < B N` for all `n m ≥ N` are
converging. This is often applied for `B N = 2^{-N}`, i.e., with a very fast convergence to
`0`, which makes it possible to use arguments of converging series, while this is impossible
to do in general for arbitrary Cauchy sequences. -/
theorem complete_of_convergent_controlled_sequences (B : ℕ → ℝ≥0∞) (hB : ∀n, 0 < B n)
  (H : ∀u : ℕ → α, (∀N n m : ℕ, N ≤ n → N ≤ m → edist (u n) (u m) < B N) →
    ∃x, tendsto u at_top (𝓝 x)) :
  complete_space α :=
uniform_space.complete_of_convergent_controlled_sequences
  uniformity_has_countable_basis
  (λ n, {p:α×α | edist p.1 p.2 < B n}) (λ n, edist_mem_uniformity $ hB n) H

/-- A sequentially complete pseudoemetric space is complete. -/
theorem complete_of_cauchy_seq_tendsto :
  (∀ u : ℕ → α, cauchy_seq u → ∃a, tendsto u at_top (𝓝 a)) → complete_space α :=
uniform_space.complete_of_cauchy_seq_tendsto uniformity_has_countable_basis

/-- Expressing locally uniform convergence on a set using `edist`. -/
lemma tendsto_locally_uniformly_on_iff {ι : Type*} [topological_space β]
  {F : ι → β → α} {f : β → α} {p : filter ι} {s : set β} :
  tendsto_locally_uniformly_on F f p s ↔
  ∀ ε > 0, ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, ∀ᶠ n in p, ∀ y ∈ t, edist (f y) (F n y) < ε :=
begin
  refine ⟨λ H ε hε, H _ (edist_mem_uniformity hε), λ H u hu x hx, _⟩,
  rcases mem_uniformity_edist.1 hu with ⟨ε, εpos, hε⟩,
  rcases H ε εpos x hx with ⟨t, ht, Ht⟩,
  exact ⟨t, ht, Ht.mono (λ n hs x hx, hε (hs x hx))⟩
end

/-- Expressing uniform convergence on a set using `edist`. -/
lemma tendsto_uniformly_on_iff {ι : Type*}
  {F : ι → β → α} {f : β → α} {p : filter ι} {s : set β} :
  tendsto_uniformly_on F f p s ↔ ∀ ε > 0, ∀ᶠ n in p, ∀ x ∈ s, edist (f x) (F n x) < ε :=
begin
  refine ⟨λ H ε hε, H _ (edist_mem_uniformity hε), λ H u hu, _⟩,
  rcases mem_uniformity_edist.1 hu with ⟨ε, εpos, hε⟩,
  exact (H ε εpos).mono (λ n hs x hx, hε (hs x hx))
end

/-- Expressing locally uniform convergence using `edist`. -/
lemma tendsto_locally_uniformly_iff {ι : Type*} [topological_space β]
  {F : ι → β → α} {f : β → α} {p : filter ι} :
  tendsto_locally_uniformly F f p ↔
  ∀ ε > 0, ∀ (x : β), ∃ t ∈ 𝓝 x, ∀ᶠ n in p, ∀ y ∈ t, edist (f y) (F n y) < ε :=
by simp only [← tendsto_locally_uniformly_on_univ, tendsto_locally_uniformly_on_iff,
  mem_univ, forall_const, exists_prop, nhds_within_univ]

/-- Expressing uniform convergence using `edist`. -/
lemma tendsto_uniformly_iff {ι : Type*}
  {F : ι → β → α} {f : β → α} {p : filter ι} :
  tendsto_uniformly F f p ↔ ∀ ε > 0, ∀ᶠ n in p, ∀ x, edist (f x) (F n x) < ε :=
by simp only [← tendsto_uniformly_on_univ, tendsto_uniformly_on_iff, mem_univ, forall_const]

end emetric

open emetric

/-- Auxiliary function to replace the uniformity on a pseudoemetric space with
a uniformity which is equal to the original one, but maybe not defeq.
This is useful if one wants to construct a pseudoemetric space with a
specified uniformity. See Note [forgetful inheritance] explaining why having definitionally
the right uniformity is often important.
-/
def pseudo_emetric_space.replace_uniformity {α} [U : uniform_space α] (m : pseudo_emetric_space α)
  (H : @uniformity _ U = @uniformity _ pseudo_emetric_space.to_uniform_space) :
  pseudo_emetric_space α :=
{ edist               := @edist _ m.to_has_edist,
  edist_self          := edist_self,
  edist_comm          := edist_comm,
  edist_triangle      := edist_triangle,
  to_uniform_space    := U,
  uniformity_edist    := H.trans (@pseudo_emetric_space.uniformity_edist α _) }

/-- The extended pseudometric induced by a function taking values in a pseudoemetric space. -/
def pseudo_emetric_space.induced {α β} (f : α → β)
  (m : pseudo_emetric_space β) : pseudo_emetric_space α :=
{ edist               := λ x y, edist (f x) (f y),
  edist_self          := λ x, edist_self _,
  edist_comm          := λ x y, edist_comm _ _,
  edist_triangle      := λ x y z, edist_triangle _ _ _,
  to_uniform_space    := uniform_space.comap f m.to_uniform_space,
  uniformity_edist    := begin
    apply @uniformity_dist_of_mem_uniformity _ _ _ _ _ (λ x y, edist (f x) (f y)),
    refine λ s, mem_comap.trans _,
    split; intro H,
    { rcases H with ⟨r, ru, rs⟩,
      rcases mem_uniformity_edist.1 ru with ⟨ε, ε0, hε⟩,
      refine ⟨ε, ε0, λ a b h, rs (hε _)⟩, exact h },
    { rcases H with ⟨ε, ε0, hε⟩,
      exact ⟨_, edist_mem_uniformity ε0, λ ⟨a, b⟩, hε⟩ }
  end }

/-- Pseudoemetric space instance on subsets of pseudoemetric spaces -/
instance {α : Type*} {p : α → Prop} [t : pseudo_emetric_space α] :
  pseudo_emetric_space (subtype p) := t.induced coe

/-- The extended psuedodistance on a subset of a pseudoemetric space is the restriction of
the original pseudodistance, by definition -/
theorem subtype.edist_eq {p : α → Prop} (x y : subtype p) : edist x y = edist (x : α) y := rfl

/-- The product of two pseudoemetric spaces, with the max distance, is an extended
pseudometric spaces. We make sure that the uniform structure thus constructed is the one
corresponding to the product of uniform spaces, to avoid diamond problems. -/
instance prod.pseudo_emetric_space_max [pseudo_emetric_space β] : pseudo_emetric_space (α × β) :=
{ edist := λ x y, max (edist x.1 y.1) (edist x.2 y.2),
  edist_self := λ x, by simp,
  edist_comm := λ x y, by simp [edist_comm],
  edist_triangle := λ x y z, max_le
    (le_trans (edist_triangle _ _ _) (add_le_add (le_max_left _ _) (le_max_left _ _)))
    (le_trans (edist_triangle _ _ _) (add_le_add (le_max_right _ _) (le_max_right _ _))),
  uniformity_edist := begin
    refine uniformity_prod.trans _,
    simp [pseudo_emetric_space.uniformity_edist, comap_infi],
    rw ← infi_inf_eq, congr, funext,
    rw ← infi_inf_eq, congr, funext,
    simp [inf_principal, ext_iff, max_lt_iff]
  end,
  to_uniform_space := prod.uniform_space }

lemma prod.edist_eq [pseudo_emetric_space β] (x y : α × β) :
  edist x y = max (edist x.1 y.1) (edist x.2 y.2) :=
rfl

section pi
open finset
variables {π : β → Type*} [fintype β]

/-- The product of a finite number of pseudoemetric spaces, with the max distance, is still
a pseudoemetric space.
This construction would also work for infinite products, but it would not give rise
to the product topology. Hence, we only formalize it in the good situation of finitely many
spaces. -/
instance pseudo_emetric_space_pi [∀b, pseudo_emetric_space (π b)] :
  pseudo_emetric_space (Πb, π b) :=
{ edist := λ f g, finset.sup univ (λb, edist (f b) (g b)),
  edist_self := assume f, bot_unique $ finset.sup_le $ by simp,
  edist_comm := assume f g, by unfold edist; congr; funext a; exact edist_comm _ _,
  edist_triangle := assume f g h,
    begin
      simp only [finset.sup_le_iff],
      assume b hb,
      exact le_trans (edist_triangle _ (g b) _) (add_le_add (le_sup hb) (le_sup hb))
    end,
  to_uniform_space := Pi.uniform_space _,
  uniformity_edist := begin
    simp only [Pi.uniformity, pseudo_emetric_space.uniformity_edist, comap_infi, gt_iff_lt,
      preimage_set_of_eq, comap_principal],
    rw infi_comm, congr, funext ε,
    rw infi_comm, congr, funext εpos,
    change 0 < ε at εpos,
    simp [set.ext_iff, εpos]
  end }

lemma edist_pi_def [Π b, pseudo_emetric_space (π b)] (f g : Π b, π b) :
  edist f g = finset.sup univ (λb, edist (f b) (g b)) := rfl

@[simp]
lemma edist_pi_const [nonempty β] (a b : α) :
  edist (λ x : β, a) (λ _, b) = edist a b := finset.sup_const univ_nonempty (edist a b)

lemma edist_le_pi_edist [Π b, pseudo_emetric_space (π b)] (f g : Π b, π b) (b : β) :
  edist (f b) (g b) ≤ edist f g :=
finset.le_sup (finset.mem_univ b)

lemma edist_pi_le_iff [Π b, pseudo_emetric_space (π b)] {f g : Π b, π b} {d : ℝ≥0∞} :
  edist f g ≤ d ↔ ∀ b, edist (f b) (g b) ≤ d :=
finset.sup_le_iff.trans $ by simp only [finset.mem_univ, forall_const]

end pi

namespace emetric
variables {x y z : α} {ε ε₁ ε₂ : ℝ≥0∞} {s : set α}

/-- `emetric.ball x ε` is the set of all points `y` with `edist y x < ε` -/
def ball (x : α) (ε : ℝ≥0∞) : set α := {y | edist y x < ε}

@[simp] theorem mem_ball : y ∈ ball x ε ↔ edist y x < ε := iff.rfl

theorem mem_ball' : y ∈ ball x ε ↔ edist x y < ε := by rw edist_comm; refl

/-- `emetric.closed_ball x ε` is the set of all points `y` with `edist y x ≤ ε` -/
def closed_ball (x : α) (ε : ℝ≥0∞) := {y | edist y x ≤ ε}

@[simp] theorem mem_closed_ball : y ∈ closed_ball x ε ↔ edist y x ≤ ε := iff.rfl

@[simp] theorem closed_ball_top (x : α) : closed_ball x ∞ = univ :=
eq_univ_of_forall $ λ y, @le_top _ _ (edist y x)

theorem ball_subset_closed_ball : ball x ε ⊆ closed_ball x ε :=
assume y hy, le_of_lt hy

theorem pos_of_mem_ball (hy : y ∈ ball x ε) : 0 < ε :=
lt_of_le_of_lt (zero_le _) hy

theorem mem_ball_self (h : 0 < ε) : x ∈ ball x ε :=
show edist x x < ε, by rw edist_self; assumption

theorem mem_closed_ball_self : x ∈ closed_ball x ε :=
show edist x x ≤ ε, by rw edist_self; exact bot_le

theorem mem_ball_comm : x ∈ ball y ε ↔ y ∈ ball x ε :=
by simp [edist_comm]

theorem ball_subset_ball (h : ε₁ ≤ ε₂) : ball x ε₁ ⊆ ball x ε₂ :=
λ y (yx : _ < ε₁), lt_of_lt_of_le yx h

theorem closed_ball_subset_closed_ball (h : ε₁ ≤ ε₂) :
  closed_ball x ε₁ ⊆ closed_ball x ε₂ :=
λ y (yx : _ ≤ ε₁), le_trans yx h

theorem ball_disjoint (h : ε₁ + ε₂ ≤ edist x y) : ball x ε₁ ∩ ball y ε₂ = ∅ :=
eq_empty_iff_forall_not_mem.2 $ λ z ⟨h₁, h₂⟩,
not_lt_of_le (edist_triangle_left x y z)
  (lt_of_lt_of_le (ennreal.add_lt_add h₁ h₂) h)

theorem ball_subset (h : edist x y + ε₁ ≤ ε₂) (h' : edist x y ≠ ∞) : ball x ε₁ ⊆ ball y ε₂ :=
λ z zx, calc
  edist z y ≤ edist z x + edist x y : edist_triangle _ _ _
  ... = edist x y + edist z x : add_comm _ _
  ... < edist x y + ε₁ : ennreal.add_lt_add_left h' zx
  ... ≤ ε₂ : h

theorem exists_ball_subset_ball (h : y ∈ ball x ε) : ∃ ε' > 0, ball y ε' ⊆ ball x ε :=
begin
  have : 0 < ε - edist y x := by simpa using h,
  refine ⟨ε - edist y x, this, ball_subset _ (ne_top_of_lt h)⟩,
  rw ennreal.add_sub_cancel_of_le (le_of_lt h),
  exact le_refl ε
end

theorem ball_eq_empty_iff : ball x ε = ∅ ↔ ε = 0 :=
eq_empty_iff_forall_not_mem.trans
⟨λh, le_bot_iff.1 (le_of_not_gt (λ ε0, h _ (mem_ball_self ε0))),
λε0 y h, not_lt_of_le (le_of_eq ε0) (pos_of_mem_ball h)⟩

/-- Relation “two points are at a finite edistance” is an equivalence relation. -/
def edist_lt_top_setoid : setoid α :=
{ r := λ x y, edist x y < ⊤,
  iseqv := ⟨λ x, by { rw edist_self, exact ennreal.coe_lt_top },
    λ x y h, by rwa edist_comm,
    λ x y z hxy hyz, lt_of_le_of_lt (edist_triangle x y z) (ennreal.add_lt_top.2 ⟨hxy, hyz⟩)⟩ }

@[simp] lemma ball_zero : ball x 0 = ∅ :=
by rw [emetric.ball_eq_empty_iff]

theorem nhds_basis_eball : (𝓝 x).has_basis (λ ε:ℝ≥0∞, 0 < ε) (ball x) :=
nhds_basis_uniformity uniformity_basis_edist

theorem nhds_basis_closed_eball : (𝓝 x).has_basis (λ ε:ℝ≥0∞, 0 < ε) (closed_ball x) :=
nhds_basis_uniformity uniformity_basis_edist_le

theorem nhds_eq : 𝓝 x = (⨅ε>0, 𝓟 (ball x ε)) :=
nhds_basis_eball.eq_binfi

theorem mem_nhds_iff : s ∈ 𝓝 x ↔ ∃ε>0, ball x ε ⊆ s := nhds_basis_eball.mem_iff

theorem is_open_iff : is_open s ↔ ∀x∈s, ∃ε>0, ball x ε ⊆ s :=
by simp [is_open_iff_nhds, mem_nhds_iff]

theorem is_open_ball : is_open (ball x ε) :=
is_open_iff.2 $ λ y, exists_ball_subset_ball

theorem is_closed_ball_top : is_closed (ball x ⊤) :=
is_open_compl_iff.1 $ is_open_iff.2 $ λ y hy, ⟨⊤, ennreal.coe_lt_top, subset_compl_iff_disjoint.2 $
  ball_disjoint $ by { rw ennreal.top_add, exact le_of_not_lt hy }⟩

theorem ball_mem_nhds (x : α) {ε : ℝ≥0∞} (ε0 : 0 < ε) : ball x ε ∈ 𝓝 x :=
is_open_ball.mem_nhds (mem_ball_self ε0)

theorem closed_ball_mem_nhds (x : α) {ε : ℝ≥0∞} (ε0 : 0 < ε) : closed_ball x ε ∈ 𝓝 x :=
mem_of_superset (ball_mem_nhds x ε0) ball_subset_closed_ball

theorem ball_prod_same [pseudo_emetric_space β] (x : α) (y : β) (r : ℝ≥0∞) :
  (ball x r).prod (ball y r) = ball (x, y) r :=
ext $ λ z, max_lt_iff.symm

theorem closed_ball_prod_same [pseudo_emetric_space β] (x : α) (y : β) (r : ℝ≥0∞) :
  (closed_ball x r).prod (closed_ball y r) = closed_ball (x, y) r :=
ext $ λ z, max_le_iff.symm

/-- ε-characterization of the closure in pseudoemetric spaces -/
theorem mem_closure_iff :
  x ∈ closure s ↔ ∀ε>0, ∃y ∈ s, edist x y < ε :=
(mem_closure_iff_nhds_basis nhds_basis_eball).trans $
  by simp only [mem_ball, edist_comm x]

theorem tendsto_nhds {f : filter β} {u : β → α} {a : α} :
  tendsto u f (𝓝 a) ↔ ∀ ε > 0, ∀ᶠ x in f, edist (u x) a < ε :=
nhds_basis_eball.tendsto_right_iff

theorem tendsto_at_top [nonempty β] [semilattice_sup β] {u : β → α} {a : α} :
  tendsto u at_top (𝓝 a) ↔ ∀ε>0, ∃N, ∀n≥N, edist (u n) a < ε :=
(at_top_basis.tendsto_iff nhds_basis_eball).trans $
  by simp only [exists_prop, true_and, mem_Ici, mem_ball]

/-- In a pseudoemetric space, Cauchy sequences are characterized by the fact that, eventually,
the pseudoedistance between its elements is arbitrarily small -/
@[nolint ge_or_gt] -- see Note [nolint_ge]
theorem cauchy_seq_iff [nonempty β] [semilattice_sup β] {u : β → α} :
  cauchy_seq u ↔ ∀ε>0, ∃N, ∀m n≥N, edist (u m) (u n) < ε :=
uniformity_basis_edist.cauchy_seq_iff

/-- A variation around the emetric characterization of Cauchy sequences -/
theorem cauchy_seq_iff' [nonempty β] [semilattice_sup β] {u : β → α} :
  cauchy_seq u ↔ ∀ε>(0 : ℝ≥0∞), ∃N, ∀n≥N, edist (u n) (u N) < ε :=
uniformity_basis_edist.cauchy_seq_iff'

/-- A variation of the emetric characterization of Cauchy sequences that deals with
`ℝ≥0` upper bounds. -/
theorem cauchy_seq_iff_nnreal [nonempty β] [semilattice_sup β] {u : β → α} :
  cauchy_seq u ↔ ∀ ε : ℝ≥0, 0 < ε → ∃ N, ∀ n, N ≤ n → edist (u n) (u N) < ε :=
uniformity_basis_edist_nnreal.cauchy_seq_iff'

theorem totally_bounded_iff {s : set α} :
  totally_bounded s ↔ ∀ ε > 0, ∃t : set α, finite t ∧ s ⊆ ⋃y∈t, ball y ε :=
⟨λ H ε ε0, H _ (edist_mem_uniformity ε0),
 λ H r ru, let ⟨ε, ε0, hε⟩ := mem_uniformity_edist.1 ru,
               ⟨t, ft, h⟩ := H ε ε0 in
  ⟨t, ft, subset.trans h $ Union_subset_Union $ λ y, Union_subset_Union $ λ yt z, hε⟩⟩

theorem totally_bounded_iff' {s : set α} :
  totally_bounded s ↔ ∀ ε > 0, ∃t⊆s, finite t ∧ s ⊆ ⋃y∈t, ball y ε :=
⟨λ H ε ε0, (totally_bounded_iff_subset.1 H) _ (edist_mem_uniformity ε0),
 λ H r ru, let ⟨ε, ε0, hε⟩ := mem_uniformity_edist.1 ru,
               ⟨t, _, ft, h⟩ := H ε ε0 in
  ⟨t, ft, subset.trans h $ Union_subset_Union $ λ y, Union_subset_Union $ λ yt z, hε⟩⟩

section first_countable

@[priority 100] -- see Note [lower instance priority]
instance (α : Type u) [pseudo_emetric_space α] :
  topological_space.first_countable_topology α :=
uniform_space.first_countable_topology uniformity_has_countable_basis

end first_countable

section compact

/-- For a set `s` in a pseudo emetric space, if for every `ε > 0` there exists a countable
set that is `ε`-dense in `s`, then there exists a countable subset `t ⊆ s` that is dense in `s`. -/
lemma subset_countable_closure_of_almost_dense_set (s : set α)
  (hs : ∀ ε > 0, ∃ t : set α, countable t ∧ s ⊆ ⋃ x ∈ t, closed_ball x ε) :
  ∃ t ⊆ s, (countable t ∧ s ⊆ closure t) :=
begin
  rcases s.eq_empty_or_nonempty with rfl|⟨x₀, hx₀⟩,
  { exact ⟨∅, empty_subset _, countable_empty, empty_subset _⟩ },
  choose! T hTc hsT using (λ n : ℕ, hs n⁻¹ (by simp)),
  have : ∀ r x, ∃ y ∈ s, closed_ball x r ∩ s ⊆ closed_ball y (r * 2),
  { intros r x,
    rcases (closed_ball x r ∩ s).eq_empty_or_nonempty with he|⟨y, hxy, hys⟩,
    { refine ⟨x₀, hx₀, _⟩, rw he, exact empty_subset _ },
    { refine ⟨y, hys, λ z hz, _⟩,
      calc edist z y ≤ edist z x + edist y x : edist_triangle_right _ _ _
      ... ≤ r + r : add_le_add hz.1 hxy
      ... = r * 2 : (mul_two r).symm } },
  choose f hfs hf,
  refine ⟨⋃ n : ℕ, (f n⁻¹) '' (T n), Union_subset $ λ n, image_subset_iff.2 (λ z hz, hfs _ _),
    countable_Union $ λ n, (hTc n).image _, _⟩,
  refine λ x hx, mem_closure_iff.2 (λ ε ε0, _),
  rcases ennreal.exists_inv_nat_lt (ennreal.half_pos ε0.lt.ne').ne' with ⟨n, hn⟩,
  rcases mem_bUnion_iff.1 (hsT n hx) with ⟨y, hyn, hyx⟩,
  refine ⟨f n⁻¹ y, mem_Union.2 ⟨n, mem_image_of_mem _ hyn⟩, _⟩,
  calc edist x (f n⁻¹ y) ≤ n⁻¹ * 2 : hf _ _ ⟨hyx, hx⟩
                     ... < ε      : ennreal.mul_lt_of_lt_div hn
end

/-- A compact set in a pseudo emetric space is separable, i.e., it is a subset of the closure of a
countable set.  -/
lemma subset_countable_closure_of_compact {s : set α} (hs : is_compact s) :
  ∃ t ⊆ s, (countable t ∧ s ⊆ closure t) :=
begin
  refine subset_countable_closure_of_almost_dense_set s (λ ε hε, _),
  rcases totally_bounded_iff'.1 hs.totally_bounded ε hε with ⟨t, hts, htf, hst⟩,
  exact ⟨t, htf.countable,
    subset.trans hst (bUnion_subset_bUnion_right $ λ _ _, ball_subset_closed_ball)⟩
end

end compact

section second_countable
open topological_space

variables (α)

/-- A separable pseudoemetric space is second countable: one obtains a countable basis by taking
the balls centered at points in a dense subset, and with rational radii. We do not register
this as an instance, as there is already an instance going in the other direction
from second countable spaces to separable spaces, and we want to avoid loops. -/
lemma second_countable_of_separable [separable_space α] :
  second_countable_topology α :=
uniform_space.second_countable_of_separable uniformity_has_countable_basis

/-- A sigma compact pseudo emetric space has second countable topology. This is not an instance
to avoid a loop with `sigma_compact_space_of_locally_compact_second_countable`.  -/
lemma second_countable_of_sigma_compact [sigma_compact_space α] :
  second_countable_topology α :=
begin
  suffices : separable_space α, by exactI second_countable_of_separable α,
  choose T hTsub hTc hsubT
    using λ n, subset_countable_closure_of_compact (is_compact_compact_covering α n),
  refine ⟨⟨⋃ n, T n, countable_Union hTc, λ x, _⟩⟩,
  rcases Union_eq_univ_iff.1 (Union_compact_covering α) x with ⟨n, hn⟩,
  exact closure_mono (subset_Union _ n) (hsubT _ hn)
end

variable {α}

lemma second_countable_of_almost_dense_set
  (hs : ∀ ε > 0, ∃ t : set α, countable t ∧ (⋃ x ∈ t, closed_ball x ε) = univ) :
  second_countable_topology α :=
begin
  suffices : separable_space α, by exactI second_countable_of_separable α,
  rcases subset_countable_closure_of_almost_dense_set (univ : set α) (λ ε ε0, _)
    with ⟨t, -, htc, ht⟩,
  { exact ⟨⟨t, htc, λ x, ht (mem_univ x)⟩⟩ },
  { rcases hs ε ε0 with ⟨t, htc, ht⟩,
    exact ⟨t, htc, univ_subset_iff.2 ht⟩ }
end

end second_countable

section diam

/-- The diameter of a set in a pseudoemetric space, named `emetric.diam` -/
def diam (s : set α) := ⨆ (x ∈ s) (y ∈ s), edist x y

lemma diam_le_iff {d : ℝ≥0∞} :
  diam s ≤ d ↔ ∀ (x ∈ s) (y ∈ s), edist x y ≤ d :=
by simp only [diam, supr_le_iff]

lemma diam_image_le_iff {d : ℝ≥0∞} {f : β → α} {s : set β} :
  diam (f '' s) ≤ d ↔ ∀ (x ∈ s) (y ∈ s), edist (f x) (f y) ≤ d :=
by simp only [diam_le_iff, ball_image_iff]

lemma edist_le_of_diam_le {d} (hx : x ∈ s) (hy : y ∈ s) (hd : diam s ≤ d) : edist x y ≤ d :=
diam_le_iff.1 hd x hx y hy

/-- If two points belong to some set, their edistance is bounded by the diameter of the set -/
lemma edist_le_diam_of_mem (hx : x ∈ s) (hy : y ∈ s) : edist x y ≤ diam s :=
edist_le_of_diam_le hx hy le_rfl

/-- If the distance between any two points in a set is bounded by some constant, this constant
bounds the diameter. -/
lemma diam_le {d : ℝ≥0∞} (h : ∀ (x ∈ s) (y ∈ s), edist x y ≤ d) : diam s ≤ d := diam_le_iff.2 h

/-- The diameter of a subsingleton vanishes. -/
lemma diam_subsingleton (hs : s.subsingleton) : diam s = 0 :=
nonpos_iff_eq_zero.1 $ diam_le $
λ x hx y hy, (hs hx hy).symm ▸ edist_self y ▸ le_rfl

/-- The diameter of the empty set vanishes -/
@[simp] lemma diam_empty : diam (∅ : set α) = 0 :=
diam_subsingleton subsingleton_empty

/-- The diameter of a singleton vanishes -/
@[simp] lemma diam_singleton : diam ({x} : set α) = 0 :=
diam_subsingleton subsingleton_singleton

lemma diam_Union_mem_option {ι : Type*} (o : option ι) (s : ι → set α) :
  diam (⋃ i ∈ o, s i) = ⨆ i ∈ o, diam (s i) :=
by cases o; simp

lemma diam_insert : diam (insert x s) = max (⨆ y ∈ s, edist x y) (diam s) :=
eq_of_forall_ge_iff $ λ d, by simp only [diam_le_iff, ball_insert_iff,
  edist_self, edist_comm x, max_le_iff, supr_le_iff, zero_le, true_and,
  forall_and_distrib, and_self, ← and_assoc]

lemma diam_pair : diam ({x, y} : set α) = edist x y :=
by simp only [supr_singleton, diam_insert, diam_singleton, ennreal.max_zero_right]

lemma diam_triple :
  diam ({x, y, z} : set α) = max (max (edist x y) (edist x z)) (edist y z) :=
by simp only [diam_insert, supr_insert, supr_singleton, diam_singleton,
  ennreal.max_zero_right, ennreal.sup_eq_max]

/-- The diameter is monotonous with respect to inclusion -/
lemma diam_mono {s t : set α} (h : s ⊆ t) : diam s ≤ diam t :=
diam_le $ λ x hx y hy, edist_le_diam_of_mem (h hx) (h hy)

/-- The diameter of a union is controlled by the diameter of the sets, and the edistance
between two points in the sets. -/
lemma diam_union {t : set α} (xs : x ∈ s) (yt : y ∈ t) :
  diam (s ∪ t) ≤ diam s + edist x y + diam t :=
begin
  have A : ∀a ∈ s, ∀b ∈ t, edist a b ≤ diam s + edist x y + diam t := λa ha b hb, calc
    edist a b ≤ edist a x + edist x y + edist y b : edist_triangle4 _ _ _ _
    ... ≤ diam s + edist x y + diam t :
      add_le_add (add_le_add (edist_le_diam_of_mem ha xs) (le_refl _)) (edist_le_diam_of_mem yt hb),
  refine diam_le (λa ha b hb, _),
  cases (mem_union _ _ _).1 ha with h'a h'a; cases (mem_union _ _ _).1 hb with h'b h'b,
  { calc edist a b ≤ diam s : edist_le_diam_of_mem h'a h'b
        ... ≤ diam s + (edist x y + diam t) : le_self_add
        ... = diam s + edist x y + diam t : (add_assoc _ _ _).symm },
  { exact A a h'a b h'b },
  { have Z := A b h'b a h'a, rwa [edist_comm] at Z },
  { calc edist a b ≤ diam t : edist_le_diam_of_mem h'a h'b
        ... ≤ (diam s + edist x y) + diam t : le_add_self }
end

lemma diam_union' {t : set α} (h : (s ∩ t).nonempty) : diam (s ∪ t) ≤ diam s + diam t :=
let ⟨x, ⟨xs, xt⟩⟩ := h in by simpa using diam_union xs xt

lemma diam_closed_ball {r : ℝ≥0∞} : diam (closed_ball x r) ≤ 2 * r :=
diam_le $ λa ha b hb, calc
  edist a b ≤ edist a x + edist b x : edist_triangle_right _ _ _
  ... ≤ r + r : add_le_add ha hb
  ... = 2 * r : (two_mul r).symm

lemma diam_ball {r : ℝ≥0∞} : diam (ball x r) ≤ 2 * r :=
le_trans (diam_mono ball_subset_closed_ball) diam_closed_ball

lemma diam_pi_le_of_le {π : β → Type*} [fintype β] [∀ b, pseudo_emetric_space (π b)]
  {s : Π (b : β), set (π b)} {c : ℝ≥0∞} (h : ∀ b, diam (s b) ≤ c) :
  diam (set.pi univ s) ≤ c :=
begin
  apply diam_le (λ x hx y hy, edist_pi_le_iff.mpr _),
  rw [mem_univ_pi] at hx hy,
  exact λ b, diam_le_iff.1 (h b) (x b) (hx b) (y b) (hy b),
end

end diam

end emetric --namespace

/-- We now define `emetric_space`, extending `pseudo_emetric_space`. -/

class emetric_space (α : Type u) extends pseudo_emetric_space α : Type u :=
(eq_of_edist_eq_zero : ∀ {x y : α}, edist x y = 0 → x = y)

variables {γ : Type w} [emetric_space γ]

@[priority 100] -- see Note [lower instance priority]
instance emetric_space.to_uniform_space' : uniform_space γ :=
pseudo_emetric_space.to_uniform_space

export emetric_space (eq_of_edist_eq_zero)

/-- Characterize the equality of points by the vanishing of their extended distance -/
@[simp] theorem edist_eq_zero {x y : γ} : edist x y = 0 ↔ x = y :=
iff.intro eq_of_edist_eq_zero (assume : x = y, this ▸ edist_self _)

@[simp] theorem zero_eq_edist {x y : γ} : 0 = edist x y ↔ x = y :=
iff.intro (assume h, eq_of_edist_eq_zero (h.symm))
          (assume : x = y, this ▸ (edist_self _).symm)

theorem edist_le_zero {x y : γ} : (edist x y ≤ 0) ↔ x = y :=
nonpos_iff_eq_zero.trans edist_eq_zero

@[simp] theorem edist_pos {x y : γ} : 0 < edist x y ↔ x ≠ y := by simp [← not_le]

/-- Two points coincide if their distance is `< ε` for all positive ε -/
theorem eq_of_forall_edist_le {x y : γ} (h : ∀ε > 0, edist x y ≤ ε) : x = y :=
eq_of_edist_eq_zero (eq_of_le_of_forall_le_of_dense bot_le h)

/-- A map between emetric spaces is a uniform embedding if and only if the edistance between `f x`
and `f y` is controlled in terms of the distance between `x` and `y` and conversely. -/
theorem uniform_embedding_iff' [emetric_space β] {f : γ → β} :
  uniform_embedding f ↔
  (∀ ε > 0, ∃ δ > 0, ∀ {a b : γ}, edist a b < δ → edist (f a) (f b) < ε) ∧
  (∀ δ > 0, ∃ ε > 0, ∀ {a b : γ}, edist (f a) (f b) < ε → edist a b < δ) :=
begin
  split,
  { assume h,
    exact ⟨emetric.uniform_continuous_iff.1 (uniform_embedding_iff.1 h).2.1,
          (uniform_embedding_iff.1 h).2.2⟩ },
  { rintros ⟨h₁, h₂⟩,
    refine uniform_embedding_iff.2 ⟨_, emetric.uniform_continuous_iff.2 h₁, h₂⟩,
    assume x y hxy,
    have : edist x y ≤ 0,
    { refine le_of_forall_lt' (λδ δpos, _),
      rcases h₂ δ δpos with ⟨ε, εpos, hε⟩,
      have : edist (f x) (f y) < ε, by simpa [hxy],
      exact hε this },
    simpa using this }
end

/-- An emetric space is separated -/
@[priority 100] -- see Note [lower instance priority]
instance to_separated : separated_space γ :=
separated_def.2 $ λ x y h, eq_of_forall_edist_le $
λ ε ε0, le_of_lt (h _ (edist_mem_uniformity ε0))

/-- If a  `pseudo_emetric_space` is separated, then it is an `emetric_space`. -/
def emetric_of_t2_pseudo_emetric_space {α : Type*} [pseudo_emetric_space α]
  (h : separated_space α) : emetric_space α :=
{ eq_of_edist_eq_zero := λ x y hdist,
  begin
    refine separated_def.1 h x y (λ s hs, _),
    obtain ⟨ε, hε, H⟩ := mem_uniformity_edist.1 hs,
    exact H (show edist x y < ε, by rwa [hdist])
  end
  ..‹pseudo_emetric_space α› }

/-- Auxiliary function to replace the uniformity on an emetric space with
a uniformity which is equal to the original one, but maybe not defeq.
This is useful if one wants to construct an emetric space with a
specified uniformity. See Note [forgetful inheritance] explaining why having definitionally
the right uniformity is often important.
-/
def emetric_space.replace_uniformity {γ} [U : uniform_space γ] (m : emetric_space γ)
  (H : @uniformity _ U = @uniformity _ pseudo_emetric_space.to_uniform_space) :
  emetric_space γ :=
{ edist               := @edist _ m.to_has_edist,
  edist_self          := edist_self,
  eq_of_edist_eq_zero := @eq_of_edist_eq_zero _ _,
  edist_comm          := edist_comm,
  edist_triangle      := edist_triangle,
  to_uniform_space    := U,
  uniformity_edist    := H.trans (@pseudo_emetric_space.uniformity_edist γ _) }

  /-- The extended metric induced by an injective function taking values in a emetric space. -/
def emetric_space.induced {γ β} (f : γ → β) (hf : function.injective f)
  (m : emetric_space β) : emetric_space γ :=
{ edist               := λ x y, edist (f x) (f y),
  edist_self          := λ x, edist_self _,
  eq_of_edist_eq_zero := λ x y h, hf (edist_eq_zero.1 h),
  edist_comm          := λ x y, edist_comm _ _,
  edist_triangle      := λ x y z, edist_triangle _ _ _,
  to_uniform_space    := uniform_space.comap f m.to_uniform_space,
  uniformity_edist    := begin
    apply @uniformity_dist_of_mem_uniformity _ _ _ _ _ (λ x y, edist (f x) (f y)),
    refine λ s, mem_comap.trans _,
    split; intro H,
    { rcases H with ⟨r, ru, rs⟩,
      rcases mem_uniformity_edist.1 ru with ⟨ε, ε0, hε⟩,
      refine ⟨ε, ε0, λ a b h, rs (hε _)⟩, exact h },
    { rcases H with ⟨ε, ε0, hε⟩,
      exact ⟨_, edist_mem_uniformity ε0, λ ⟨a, b⟩, hε⟩ }
  end }

/-- Emetric space instance on subsets of emetric spaces -/
instance {α : Type*} {p : α → Prop} [t : emetric_space α] : emetric_space (subtype p) :=
t.induced coe (λ x y, subtype.ext_iff_val.2)

/-- The product of two emetric spaces, with the max distance, is an extended
metric spaces. We make sure that the uniform structure thus constructed is the one
corresponding to the product of uniform spaces, to avoid diamond problems. -/
instance prod.emetric_space_max [emetric_space β] : emetric_space (γ × β) :=
{ eq_of_edist_eq_zero := λ x y h, begin
    cases max_le_iff.1 (le_of_eq h) with h₁ h₂,
    have A : x.fst = y.fst := edist_le_zero.1 h₁,
    have B : x.snd = y.snd := edist_le_zero.1 h₂,
    exact prod.ext_iff.2 ⟨A, B⟩
  end,
  ..prod.pseudo_emetric_space_max }

/-- Reformulation of the uniform structure in terms of the extended distance -/
theorem uniformity_edist :
  𝓤 γ = ⨅ ε>0, 𝓟 {p:γ×γ | edist p.1 p.2 < ε} :=
pseudo_emetric_space.uniformity_edist

section pi
open finset
variables {π : β → Type*} [fintype β]

/-- The product of a finite number of emetric spaces, with the max distance, is still
an emetric space.
This construction would also work for infinite products, but it would not give rise
to the product topology. Hence, we only formalize it in the good situation of finitely many
spaces. -/
instance emetric_space_pi [∀b, emetric_space (π b)] : emetric_space (Πb, π b) :=
{ eq_of_edist_eq_zero := assume f g eq0,
  begin
    have eq1 : sup univ (λ (b : β), edist (f b) (g b)) ≤ 0 := le_of_eq eq0,
    simp only [finset.sup_le_iff] at eq1,
    exact (funext $ assume b, edist_le_zero.1 $ eq1 b $ mem_univ b),
  end,
  ..pseudo_emetric_space_pi }

end pi

namespace emetric

/-- A compact set in an emetric space is separable, i.e., it is the closure of a countable set. -/
lemma countable_closure_of_compact {s : set γ} (hs : is_compact s) :
  ∃ t ⊆ s, (countable t ∧ s = closure t) :=
begin
  rcases subset_countable_closure_of_compact hs with ⟨t, hts, htc, hsub⟩,
  exact ⟨t, hts, htc, subset.antisymm hsub (closure_minimal hts hs.is_closed)⟩
end

section diam

variables {s : set γ}

lemma diam_eq_zero_iff : diam s = 0 ↔ s.subsingleton :=
⟨λ h x hx y hy, edist_le_zero.1 $ h ▸ edist_le_diam_of_mem hx hy, diam_subsingleton⟩

lemma diam_pos_iff : 0 < diam s ↔ ∃ (x ∈ s) (y ∈ s), x ≠ y :=
begin
  have := not_congr (@diam_eq_zero_iff _ _ s),
  dunfold set.subsingleton at this,
  push_neg at this,
  simpa only [pos_iff_ne_zero, exists_prop] using this
end

end diam

end emetric
