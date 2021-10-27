/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/

import topology.continuous_on
import topology.constructions

/-!
# Bases of topologies. Countability axioms.

A topological basis on a topological space `t` is a collection of sets,
such that all open sets can be generated as unions of these sets, without the need to take
finite intersections of them. This file introduces a framework for dealing with these collections,
and also what more we can say under certain countability conditions on bases,
which are referred to as first- and second-countable.
We also briefly cover the theory of separable spaces, which are those with a countable, dense
subset. If a space is second-countable, and also has a countably generated uniformity filter
(for example, if `t` is a metric space), it will automatically be separable (and indeed, these
conditions are equivalent in this case).

## Main definitions

* `is_topological_basis s`: The topological space `t` has basis `s`.
* `separable_space α`: The topological space `t` has a countable, dense subset.
* `first_countable_topology α`: A topology in which `𝓝 x` is countably generated for every `x`.
* `second_countable_topology α`: A topology which has a topological basis which is countable.

## Main results

* `first_countable_topology.tendsto_subseq`: In a first-countable space,
  cluster points are limits of subsequences.
* `second_countable_topology.is_open_Union_countable`: In a second-countable space, the union of
  arbitrarily-many open sets is equal to a sub-union of only countably many of these sets.
* `second_countable_topology.countable_cover_nhds`: Consider `f : α → set α` with the property that
  `f x ∈ 𝓝 x` for all `x`. Then there is some countable set `s` whose image covers the space.

## Implementation Notes
For our applications we are interested that there exists a countable basis, but we do not need the
concrete basis itself. This allows us to declare these type classes as `Prop` to use them as mixins.

### TODO:
More fine grained instances for `first_countable_topology`, `separable_space`, `t2_space`, and more
(see the comment below `subtype.second_countable_topology`.)
-/

open set filter classical
open_locale topological_space filter
noncomputable theory

namespace topological_space

universe u
variables {α : Type u} [t : topological_space α]
include t

/-- A topological basis is one that satisfies the necessary conditions so that
  it suffices to take unions of the basis sets to get a topology (without taking
  finite intersections as well). -/
structure is_topological_basis (s : set (set α)) : Prop :=
(exists_subset_inter : ∀t₁∈s, ∀t₂∈s, ∀ x ∈ t₁ ∩ t₂, ∃ t₃∈s, x ∈ t₃ ∧ t₃ ⊆ t₁ ∩ t₂)
(sUnion_eq : (⋃₀ s) = univ)
(eq_generate_from : t = generate_from s)

/-- If a family of sets `s` generates the topology, then nonempty intersections of finite
subcollections of `s` form a topological basis. -/
lemma is_topological_basis_of_subbasis {s : set (set α)} (hs : t = generate_from s) :
  is_topological_basis ((λ f, ⋂₀ f) '' {f : set (set α) | finite f ∧ f ⊆ s ∧ (⋂₀ f).nonempty}) :=
begin
  refine ⟨_, _, _⟩,
  { rintro _ ⟨t₁, ⟨hft₁, ht₁b, ht₁⟩, rfl⟩ _ ⟨t₂, ⟨hft₂, ht₂b, ht₂⟩, rfl⟩ x h,
    have : ⋂₀ (t₁ ∪ t₂) = ⋂₀ t₁ ∩ ⋂₀ t₂ := sInter_union t₁ t₂,
    exact ⟨_, ⟨t₁ ∪ t₂, ⟨hft₁.union hft₂, union_subset ht₁b ht₂b, this.symm ▸ ⟨x, h⟩⟩, this⟩, h,
      subset.rfl⟩ },
  { rw [sUnion_image, bUnion_eq_univ_iff],
    intro x, have : x ∈ ⋂₀ ∅, { rw sInter_empty, exact mem_univ x },
    exact ⟨∅, ⟨finite_empty, empty_subset _, x, this⟩, this⟩ },
  { rw hs,
    apply le_antisymm; apply le_generate_from,
    { rintro _ ⟨t, ⟨hft, htb, ht⟩, rfl⟩,
      exact @is_open_sInter _ (generate_from s) _ hft (λ s hs, generate_open.basic _ $ htb hs) },
    { intros t ht,
      rcases t.eq_empty_or_nonempty with rfl|hne, { apply @is_open_empty _ _ },
      rw ← sInter_singleton t at hne ⊢,
      exact generate_open.basic _ ⟨{t}, ⟨finite_singleton t, singleton_subset_iff.2 ht, hne⟩,
        rfl⟩ } }
end

/-- If a family of open sets `s` is such that every open neighbourhood contains some
member of `s`, then `s` is a topological basis. -/
lemma is_topological_basis_of_open_of_nhds {s : set (set α)}
  (h_open : ∀ u ∈ s, is_open u)
  (h_nhds : ∀(a:α) (u : set α), a ∈ u → is_open u → ∃v ∈ s, a ∈ v ∧ v ⊆ u) :
  is_topological_basis s :=
begin
  refine ⟨λ t₁ ht₁ t₂ ht₂ x hx, h_nhds _ _ hx (is_open.inter (h_open _ ht₁) (h_open _ ht₂)), _, _⟩,
  { refine sUnion_eq_univ_iff.2 (λ a, _),
    rcases h_nhds a univ trivial is_open_univ with ⟨u, h₁, h₂, -⟩,
    exact ⟨u, h₁, h₂⟩ },
  { refine (le_generate_from h_open).antisymm (λ u hu, _),
    refine (@is_open_iff_nhds α (generate_from s) u).mpr (λ a ha, _),
    rcases h_nhds a u ha hu with ⟨v, hvs, hav, hvu⟩,
    rw nhds_generate_from,
    exact binfi_le_of_le v ⟨hav, hvs⟩ (le_principal_iff.2 hvu) }
end

/-- A set `s` is in the neighbourhood of `a` iff there is some basis set `t`, which
contains `a` and is itself contained in `s`. -/
lemma is_topological_basis.mem_nhds_iff {a : α} {s : set α} {b : set (set α)}
  (hb : is_topological_basis b) : s ∈ 𝓝 a ↔ ∃t∈b, a ∈ t ∧ t ⊆ s :=
begin
  change s ∈ (𝓝 a).sets ↔ ∃t∈b, a ∈ t ∧ t ⊆ s,
  rw [hb.eq_generate_from, nhds_generate_from, binfi_sets_eq],
  { simp only [mem_bUnion_iff, exists_prop, mem_set_of_eq, and_assoc, and.left_comm], refl },
  { exact assume s ⟨hs₁, hs₂⟩ t ⟨ht₁, ht₂⟩,
      have a ∈ s ∩ t, from ⟨hs₁, ht₁⟩,
      let ⟨u, hu₁, hu₂, hu₃⟩ := hb.1 _ hs₂ _ ht₂ _ this in
      ⟨u, ⟨hu₂, hu₁⟩, le_principal_iff.2 (subset.trans hu₃ (inter_subset_left _ _)),
        le_principal_iff.2 (subset.trans hu₃ (inter_subset_right _ _))⟩ },
  { rcases eq_univ_iff_forall.1 hb.sUnion_eq a with ⟨i, h1, h2⟩,
    exact ⟨i, h2, h1⟩ }
end

lemma is_topological_basis.nhds_has_basis {b : set (set α)} (hb : is_topological_basis b) {a : α} :
  (𝓝 a).has_basis (λ t : set α, t ∈ b ∧ a ∈ t) (λ t, t) :=
⟨λ s, hb.mem_nhds_iff.trans $ by simp only [exists_prop, and_assoc]⟩

protected lemma is_topological_basis.is_open {s : set α} {b : set (set α)}
  (hb : is_topological_basis b) (hs : s ∈ b) : is_open s :=
by { rw hb.eq_generate_from, exact generate_open.basic s hs }

lemma is_topological_basis.exists_subset_of_mem_open {b : set (set α)}
  (hb : is_topological_basis b) {a:α} {u : set α} (au : a ∈ u)
  (ou : is_open u) : ∃v ∈ b, a ∈ v ∧ v ⊆ u :=
hb.mem_nhds_iff.1 $ is_open.mem_nhds ou au

 /-- Any open set is the union of the basis sets contained in it. -/
lemma is_topological_basis.open_eq_sUnion' {B : set (set α)}
  (hB : is_topological_basis B) {u : set α} (ou : is_open u) :
  u = ⋃₀ {s ∈ B | s ⊆ u} :=
ext $ λ a,
⟨λ ha, let ⟨b, hb, ab, bu⟩ := hB.exists_subset_of_mem_open ha ou in ⟨b, ⟨hb, bu⟩, ab⟩,
  λ ⟨b, ⟨hb, bu⟩, ab⟩, bu ab⟩

lemma is_topological_basis.open_eq_sUnion {B : set (set α)}
  (hB : is_topological_basis B) {u : set α} (ou : is_open u) :
  ∃ S ⊆ B, u = ⋃₀ S :=
⟨{s ∈ B | s ⊆ u}, λ s h, h.1, hB.open_eq_sUnion' ou⟩

lemma is_topological_basis.open_eq_Union {B : set (set α)}
  (hB : is_topological_basis B) {u : set α} (ou : is_open u) :
  ∃ (β : Type u) (f : β → set α), u = (⋃ i, f i) ∧ ∀ i, f i ∈ B :=
⟨↥{s ∈ B | s ⊆ u}, coe, by { rw ← sUnion_eq_Union, apply hB.open_eq_sUnion' ou }, λ s, and.left s.2⟩

 /-- A point `a` is in the closure of `s` iff all basis sets containing `a` intersect `s`. -/
lemma is_topological_basis.mem_closure_iff {b : set (set α)} (hb : is_topological_basis b)
  {s : set α} {a : α} :
  a ∈ closure s ↔ ∀ o ∈ b, a ∈ o → (o ∩ s).nonempty :=
(mem_closure_iff_nhds_basis' hb.nhds_has_basis).trans $ by simp only [and_imp]

 /-- A set is dense iff it has non-trivial intersection with all basis sets. -/
lemma is_topological_basis.dense_iff {b : set (set α)} (hb : is_topological_basis b) {s : set α} :
  dense s ↔ ∀ o ∈ b, set.nonempty o → (o ∩ s).nonempty :=
begin
  simp only [dense, hb.mem_closure_iff],
  exact ⟨λ h o hb ⟨a, ha⟩, h a o hb ha, λ h a o hb ha, h o hb ⟨a, ha⟩⟩
end

lemma is_topological_basis.is_open_map_iff {β} [topological_space β] {B : set (set α)}
  (hB : is_topological_basis B) {f : α → β} :
  is_open_map f ↔ ∀ s ∈ B, is_open (f '' s) :=
begin
  refine ⟨λ H o ho, H _ (hB.is_open ho), λ hf o ho, _⟩,
  rw [hB.open_eq_sUnion' ho, sUnion_eq_Union, image_Union],
  exact is_open_Union (λ s, hf s s.2.1)
end

lemma is_topological_basis.exists_nonempty_subset {B : set (set α)}
  (hb : is_topological_basis B) {u : set α} (hu : u.nonempty) (ou : is_open u) :
  ∃ v ∈ B, set.nonempty v ∧ v ⊆ u :=
begin
  cases hu with x hx,
  rw [hb.open_eq_sUnion' ou, mem_sUnion] at hx,
  rcases hx with ⟨v, hv, hxv⟩,
  exact ⟨v, hv.1, ⟨x, hxv⟩, hv.2⟩
end

lemma is_topological_basis_opens : is_topological_basis { U : set α | is_open U } :=
is_topological_basis_of_open_of_nhds (by tauto) (by tauto)

protected lemma is_topological_basis.prod {β} [topological_space β] {B₁ : set (set α)}
  {B₂ : set (set β)} (h₁ : is_topological_basis B₁) (h₂ : is_topological_basis B₂) :
  is_topological_basis (image2 set.prod B₁ B₂) :=
begin
  refine is_topological_basis_of_open_of_nhds _ _,
  { rintro _ ⟨u₁, u₂, hu₁, hu₂, rfl⟩,
    exact (h₁.is_open hu₁).prod (h₂.is_open hu₂) },
  { rintro ⟨a, b⟩ u hu uo,
    rcases (h₁.nhds_has_basis.prod_nhds h₂.nhds_has_basis).mem_iff.1 (is_open.mem_nhds uo hu)
      with ⟨⟨s, t⟩, ⟨⟨hs, ha⟩, ht, hb⟩, hu⟩,
    exact ⟨s.prod t, mem_image2_of_mem hs ht, ⟨ha, hb⟩, hu⟩ }
end

protected lemma is_topological_basis.inducing {β} [topological_space β]
  {f : α → β} {T : set (set β)} (hf : inducing f) (h : is_topological_basis T) :
  is_topological_basis (image (preimage f) T) :=
begin
  refine is_topological_basis_of_open_of_nhds _ _,
  { rintros _ ⟨V, hV, rfl⟩,
    rwa hf.is_open_iff,
    refine ⟨V, h.is_open hV, rfl⟩ },
  { intros a U ha hU,
    rw hf.is_open_iff at hU,
    obtain ⟨V, hV, rfl⟩ := hU,
    obtain ⟨S, hS, rfl⟩ := h.open_eq_sUnion hV,
    obtain ⟨W, hW, ha⟩ := ha,
    refine ⟨f ⁻¹' W, ⟨_, hS hW, rfl⟩, ha, set.preimage_mono $ set.subset_sUnion_of_mem hW⟩ }
end

lemma is_topological_basis_of_cover {ι} {U  : ι → set α} (Uo : ∀ i, is_open (U i))
  (Uc : (⋃ i, U i) = univ) {b : Π i, set (set (U i))} (hb : ∀ i, is_topological_basis (b i)) :
  is_topological_basis (⋃ i : ι, image (coe : U i → α) '' (b i)) :=
begin
  refine is_topological_basis_of_open_of_nhds (λ u hu, _) _,
  { simp only [mem_Union, mem_image] at hu,
    rcases hu with ⟨i, s, sb, rfl⟩,
    exact (Uo i).is_open_map_subtype_coe _ ((hb i).is_open sb) },
  { intros a u ha uo,
    rcases Union_eq_univ_iff.1 Uc a with ⟨i, hi⟩,
    lift a to ↥(U i) using hi,
    rcases (hb i).exists_subset_of_mem_open (by exact ha) (uo.preimage continuous_subtype_coe)
      with ⟨v, hvb, hav, hvu⟩,
    exact ⟨coe '' v, mem_Union.2 ⟨i, mem_image_of_mem _ hvb⟩, mem_image_of_mem _ hav,
      image_subset_iff.2 hvu⟩ }
end

protected lemma is_topological_basis.continuous {β : Type*} [topological_space β]
  {B : set (set β)} (hB : is_topological_basis B) (f : α → β) (hf : ∀ s ∈ B, is_open (f ⁻¹' s)) :
  continuous f :=
begin rw hB.eq_generate_from, exact continuous_generated_from hf end

variables (α)

/-- A separable space is one with a countable dense subset, available through
`topological_space.exists_countable_dense`. If `α` is also known to be nonempty, then
`topological_space.dense_seq` provides a sequence `ℕ → α` with dense range, see
`topological_space.dense_range_dense_seq`.

If `α` is a uniform space with countably generated uniformity filter (e.g., an `emetric_space`),
then this condition is equivalent to `topological_space.second_countable_topology α`. In this case
the latter should be used as a typeclass argument in theorems because Lean can automatically deduce
`separable_space` from `second_countable_topology` but it can't deduce `second_countable_topology`
and `emetric_space`. -/
class separable_space : Prop :=
(exists_countable_dense : ∃s:set α, countable s ∧ dense s)

lemma exists_countable_dense [separable_space α] :
  ∃ s : set α, countable s ∧ dense s :=
separable_space.exists_countable_dense

/-- A nonempty separable space admits a sequence with dense range. Instead of running `cases` on the
conclusion of this lemma, you might want to use `topological_space.dense_seq` and
`topological_space.dense_range_dense_seq`.

If `α` might be empty, then `exists_countable_dense` is the main way to use separability of `α`. -/
lemma exists_dense_seq [separable_space α] [nonempty α] : ∃ u : ℕ → α, dense_range u :=
begin
  obtain ⟨s : set α, hs, s_dense⟩ := exists_countable_dense α,
  cases countable_iff_exists_surjective.mp hs with u hu,
  exact ⟨u, s_dense.mono hu⟩,
end

/-- A dense sequence in a non-empty separable topological space.

If `α` might be empty, then `exists_countable_dense` is the main way to use separability of `α`. -/
def dense_seq [separable_space α] [nonempty α] : ℕ → α := classical.some (exists_dense_seq α)

/-- The sequence `dense_seq α` has dense range. -/
@[simp] lemma dense_range_dense_seq [separable_space α] [nonempty α] :
  dense_range (dense_seq α) := classical.some_spec (exists_dense_seq α)

variable {α}

/-- In a separable space, a family of nonempty disjoint open sets is countable. -/
lemma countable_of_is_open_of_disjoint [separable_space α] {β : Type*}
  (s : β → set α) {a : set β} (ha : ∀ i ∈ a, is_open (s i)) (h'a : ∀ i ∈ a, (s i).nonempty)
  (h : a.pairwise_on (disjoint on s)) :
  countable a :=
begin
  rcases eq_empty_or_nonempty a with rfl|H, { exact countable_empty },
  haveI : inhabited α,
  { choose i ia using H,
    choose y hy using h'a i ia,
    exact ⟨y⟩ },
  rcases exists_countable_dense α with ⟨u, u_count, u_dense⟩,
  have : ∀ i, i ∈ a → ∃ y, y ∈ s i ∩ u :=
    λ i hi, dense_iff_inter_open.1 u_dense (s i) (ha i hi) (h'a i hi),
  choose! f hf using this,
  have f_inj : inj_on f a,
  { assume i hi j hj hij,
    have : ¬disjoint (s i) (s j),
    { rw not_disjoint_iff_nonempty_inter,
      refine ⟨f i, (hf i hi).1, _⟩,
      rw hij,
      exact (hf j hj).1 },
    contrapose! this,
    exact h i hi j hj this },
  apply countable_of_injective_of_countable_image f_inj,
  apply u_count.mono _,
  exact image_subset_iff.2 (λ i hi, (hf i hi).2)
end

/-- In a separable space, a family of disjoint sets with nonempty interiors is countable. -/
lemma countable_of_nonempty_interior_of_disjoint [separable_space α] {β : Type*} (s : β → set α)
  {a : set β} (ha : ∀ i ∈ a, (interior (s i)).nonempty) (h : a.pairwise_on (disjoint on s)) :
  countable a :=
begin
  have : a.pairwise_on (disjoint on (λ i, interior (s i))) :=
    pairwise_on_disjoint_on_mono h (λ i hi, interior_subset),
  exact countable_of_is_open_of_disjoint (λ i, interior (s i)) (λ i hi, is_open_interior) ha this
end

end topological_space

open topological_space

lemma is_topological_basis_pi {ι : Type*} {X : ι → Type*}
  [∀ i, topological_space (X i)] {T : Π i, set (set (X i))}
  (cond : ∀ i, is_topological_basis (T i)) :
  is_topological_basis {S : set (Π i, X i) | ∃ (U : Π i, set (X i)) (F : finset ι),
    (∀ i, i ∈ F → (U i) ∈ T i) ∧ S = (F : set ι).pi U } :=
begin
  classical,
  refine is_topological_basis_of_open_of_nhds _ _,
  { rintro _ ⟨U, F, h1, rfl⟩,
    apply is_open_set_pi F.finite_to_set,
    intros i hi,
    exact is_topological_basis.is_open (cond i) (h1 i hi) },
  { intros a U ha hU,
    have : U ∈ nhds a := is_open.mem_nhds hU ha,
    rw [nhds_pi, filter.mem_infi] at this,
    obtain ⟨F, hF, V, hV1, rfl⟩ := this,
    choose U' hU' using hV1,
    obtain ⟨hU1, hU2⟩ := ⟨λ i, (hU' i).1, λ i, (hU' i).2⟩,
    have : ∀ j : F, ∃ (T' : set (X j)) (hT : T' ∈ T j), a j ∈ T' ∧ T' ⊆ U' j,
    { intros i,
      specialize hU1 i,
      rwa (cond i).mem_nhds_iff at hU1 },
    choose U'' hU'' using this,
    let U : Π (i : ι), set (X i) := λ i,
      if hi : i ∈ F then U'' ⟨i, hi⟩ else set.univ,
    refine ⟨F.pi U, ⟨U, hF.to_finset, λ i hi, _, by simp⟩, _, _⟩,
    { dsimp only [U],
      rw [dif_pos],
      swap, { simpa using hi },
      exact (hU'' _).1 },
    { rw set.mem_pi,
      intros i hi,
      dsimp only [U],
      rw dif_pos hi,
      exact (hU'' _).2.1 },
    { intros x hx,
      rintros - ⟨i, rfl⟩,
      refine hU2 i ((hU'' i).2.2 _),
      convert hx i i.2,
      rcases i with ⟨i, p⟩,
      dsimp [U],
      rw dif_pos p, } },
end

lemma is_topological_basis_infi {β : Type*} {ι : Type*} {X : ι → Type*}
  [t : ∀ i, topological_space (X i)] {T : Π i, set (set (X i))}
  (cond : ∀ i, is_topological_basis (T i)) (f : Π i, β → X i) :
  @is_topological_basis β (⨅ i, induced (f i) (t i))
  { S | ∃ (U : Π i, set (X i)) (F : finset ι),
    (∀ i, i ∈ F → U i ∈ T i) ∧ S = ⋂ i (hi : i ∈ F), (f i) ⁻¹' (U i) } :=
begin
  convert (is_topological_basis_pi cond).inducing (inducing_infi_to_pi _),
  ext V,
  split,
  { rintros ⟨U, F, h1, h2⟩,
    have : (F : set ι).pi U = (⋂ (i : ι) (hi : i ∈ F),
        (λ (z : Π j, X j), z i) ⁻¹' (U i)), by { ext, simp },
    refine ⟨(F : set ι).pi U, ⟨U, F, h1, rfl⟩, _⟩,
    rw [this, h2, set.preimage_Inter],
    congr' 1,
    ext1,
    rw set.preimage_Inter,
    refl },
  { rintros ⟨U, ⟨U, F, h1, rfl⟩, h⟩,
    refine ⟨U, F, h1, _⟩,
    have : (F : set ι).pi U = (⋂ (i : ι) (hi : i ∈ F),
        (λ (z : Π j, X j), z i) ⁻¹' (U i)), by { ext, simp },
    rw [← h, this, set.preimage_Inter],
    congr' 1,
    ext1,
    rw set.preimage_Inter,
    refl }
end

/-- If `α` is a separable space and `f : α → β` is a continuous map with dense range, then `β` is
a separable space as well. E.g., the completion of a separable uniform space is separable. -/
protected lemma dense_range.separable_space {α β : Type*} [topological_space α] [separable_space α]
  [topological_space β] {f : α → β} (h : dense_range f) (h' : continuous f) :
  separable_space β :=
let ⟨s, s_cnt, s_dense⟩ := exists_countable_dense α in
⟨⟨f '' s, countable.image s_cnt f, h.dense_image h' s_dense⟩⟩

lemma dense.exists_countable_dense_subset {α : Type*} [topological_space α]
  {s : set α} [separable_space s] (hs : dense s) :
  ∃ t ⊆ s, countable t ∧ dense t :=
let ⟨t, htc, htd⟩ := exists_countable_dense s
in ⟨coe '' t, image_subset_iff.2 $ λ x _, mem_preimage.2 $ subtype.coe_prop _, htc.image coe,
  hs.dense_range_coe.dense_image continuous_subtype_val htd⟩

namespace topological_space
universe u
variables (α : Type u) [t : topological_space α]
include t


/-- A first-countable space is one in which every point has a
  countable neighborhood basis. -/
class first_countable_topology : Prop :=
(nhds_generated_countable : ∀a:α, (𝓝 a).is_countably_generated)

attribute [instance] first_countable_topology.nhds_generated_countable

namespace first_countable_topology
variable {α}

/-- In a first-countable space, a cluster point `x` of a sequence
is the limit of some subsequence. -/
lemma tendsto_subseq [first_countable_topology α] {u : ℕ → α} {x : α}
  (hx : map_cluster_pt x at_top u) :
  ∃ (ψ : ℕ → ℕ), (strict_mono ψ) ∧ (tendsto (u ∘ ψ) at_top (𝓝 x)) :=
subseq_tendsto_of_ne_bot hx

end first_countable_topology

variables {α}

instance is_countably_generated_nhds_within (x : α) [is_countably_generated (𝓝 x)] (s : set α) :
  is_countably_generated (𝓝[s] x) :=
inf.is_countably_generated _ _

variable (α)

/-- A second-countable space is one with a countable basis. -/
class second_countable_topology : Prop :=
(is_open_generated_countable [] :
  ∃ b : set (set α), countable b ∧ t = topological_space.generate_from b)

variable {α}

protected lemma is_topological_basis.second_countable_topology
  {b : set (set α)} (hb : is_topological_basis b) (hc : countable b) :
  second_countable_topology α :=
⟨⟨b, hc, hb.eq_generate_from⟩⟩

variable (α)

lemma exists_countable_basis [second_countable_topology α] :
  ∃b:set (set α), countable b ∧ ∅ ∉ b ∧ is_topological_basis b :=
let ⟨b, hb₁, hb₂⟩ := second_countable_topology.is_open_generated_countable α in
let b' := (λs, ⋂₀ s) '' {s:set (set α) | finite s ∧ s ⊆ b ∧ (⋂₀ s).nonempty} in
⟨b',
  ((countable_set_of_finite_subset hb₁).mono
    (by { simp only [← and_assoc], apply inter_subset_left })).image _,
  assume ⟨s, ⟨_, _, hn⟩, hp⟩, absurd hn (not_nonempty_iff_eq_empty.2 hp),
  is_topological_basis_of_subbasis hb₂⟩

/-- A countable topological basis of `α`. -/
def countable_basis [second_countable_topology α] : set (set α) :=
(exists_countable_basis α).some

lemma countable_countable_basis [second_countable_topology α] : countable (countable_basis α) :=
(exists_countable_basis α).some_spec.1

instance encodable_countable_basis [second_countable_topology α] :
  encodable (countable_basis α) :=
(countable_countable_basis α).to_encodable

lemma empty_nmem_countable_basis [second_countable_topology α] : ∅ ∉ countable_basis α :=
(exists_countable_basis α).some_spec.2.1

lemma is_basis_countable_basis [second_countable_topology α] :
  is_topological_basis (countable_basis α) :=
(exists_countable_basis α).some_spec.2.2

lemma eq_generate_from_countable_basis [second_countable_topology α] :
  ‹topological_space α› = generate_from (countable_basis α) :=
(is_basis_countable_basis α).eq_generate_from

variable {α}

lemma is_open_of_mem_countable_basis [second_countable_topology α] {s : set α}
  (hs : s ∈ countable_basis α) : is_open s :=
(is_basis_countable_basis α).is_open hs

lemma nonempty_of_mem_countable_basis [second_countable_topology α] {s : set α}
  (hs : s ∈ countable_basis α) : s.nonempty :=
ne_empty_iff_nonempty.1 $ ne_of_mem_of_not_mem hs $ empty_nmem_countable_basis α

variable (α)

@[priority 100] -- see Note [lower instance priority]
instance second_countable_topology.to_first_countable_topology
  [second_countable_topology α] : first_countable_topology α :=
⟨λ x, has_countable_basis.is_countably_generated $
  ⟨(is_basis_countable_basis α).nhds_has_basis, (countable_countable_basis α).mono $
    inter_subset_left _ _⟩⟩

/-- If `β` is a second-countable space, then its induced topology
via `f` on `α` is also second-countable. -/
lemma second_countable_topology_induced (β)
  [t : topological_space β] [second_countable_topology β] (f : α → β) :
  @second_countable_topology α (t.induced f) :=
begin
  rcases second_countable_topology.is_open_generated_countable β with ⟨b, hb, eq⟩,
  refine { is_open_generated_countable := ⟨preimage f '' b, hb.image _, _⟩ },
  rw [eq, induced_generate_from_eq]
end

instance subtype.second_countable_topology (s : set α) [second_countable_topology α] :
  second_countable_topology s :=
second_countable_topology_induced s α coe

/- TODO: more fine grained instances for first_countable_topology, separable_space, t2_space, ... -/
instance {β : Type*} [topological_space β]
  [second_countable_topology α] [second_countable_topology β] : second_countable_topology (α × β) :=
((is_basis_countable_basis α).prod (is_basis_countable_basis β)).second_countable_topology $
  (countable_countable_basis α).image2 (countable_countable_basis β) _

instance second_countable_topology_fintype {ι : Type*} {π : ι → Type*}
  [fintype ι] [t : ∀a, topological_space (π a)] [sc : ∀a, second_countable_topology (π a)] :
  second_countable_topology (∀a, π a) :=
begin
  have : t = (λa, generate_from (countable_basis (π a))),
    from funext (assume a, (is_basis_countable_basis (π a)).eq_generate_from),
  rw this,
  constructor,
  refine ⟨pi univ '' pi univ (λ a, countable_basis (π a)), countable.image _ _, _⟩,
  { suffices : countable {f : Πa, set (π a) | ∀a, f a ∈ countable_basis (π a)}, { simpa [pi] },
    exact countable_pi (assume i, (countable_countable_basis _)), },
  rw [pi_generate_from_eq_fintype],
  { congr' 1 with f, simp [pi, eq_comm] },
  exact assume a, (is_basis_countable_basis (π a)).sUnion_eq
end

@[priority 100] -- see Note [lower instance priority]
instance second_countable_topology.to_separable_space
  [second_countable_topology α] : separable_space α :=
begin
  choose p hp using λ s : countable_basis α, nonempty_of_mem_countable_basis s.2,
  exact ⟨⟨range p, countable_range _,
    (is_basis_countable_basis α).dense_iff.2 $ λ o ho _, ⟨p ⟨o, ho⟩, hp _, mem_range_self _⟩⟩⟩
end

variables {α}

/-- A countable open cover induces a second-countable topology if all open covers
are themselves second countable. -/
lemma second_countable_topology_of_countable_cover {ι} [encodable ι] {U : ι → set α}
  [∀ i, second_countable_topology (U i)] (Uo : ∀ i, is_open (U i))  (hc : (⋃ i, U i) = univ) :
  second_countable_topology α :=
begin
  have : is_topological_basis (⋃ i, image (coe : U i → α) '' (countable_basis (U i))),
    from is_topological_basis_of_cover Uo hc (λ i, is_basis_countable_basis (U i)),
  exact this.second_countable_topology
    (countable_Union $ λ i, (countable_countable_basis _).image _)
end

/-- In a second-countable space, an open set, given as a union of open sets,
is equal to the union of countably many of those sets. -/
lemma is_open_Union_countable [second_countable_topology α]
  {ι} (s : ι → set α) (H : ∀ i, is_open (s i)) :
  ∃ T : set ι, countable T ∧ (⋃ i ∈ T, s i) = ⋃ i, s i :=
begin
  let B := {b ∈ countable_basis α | ∃ i, b ⊆ s i},
  choose f hf using λ b : B, b.2.2,
  haveI : encodable B := ((countable_countable_basis α).mono (sep_subset _ _)).to_encodable,
  refine ⟨_, countable_range f,
    subset.antisymm (bUnion_subset_Union _ _) (sUnion_subset _)⟩,
  rintro _ ⟨i, rfl⟩ x xs,
  rcases (is_basis_countable_basis α).exists_subset_of_mem_open xs (H _) with ⟨b, hb, xb, bs⟩,
  exact ⟨_, ⟨_, rfl⟩, _, ⟨⟨⟨_, hb, _, bs⟩, rfl⟩, rfl⟩, hf _ (by exact xb)⟩
end

lemma is_open_sUnion_countable [second_countable_topology α]
  (S : set (set α)) (H : ∀ s ∈ S, is_open s) :
  ∃ T : set (set α), countable T ∧ T ⊆ S ∧ ⋃₀ T = ⋃₀ S :=
let ⟨T, cT, hT⟩ := is_open_Union_countable (λ s:S, s.1) (λ s, H s.1 s.2) in
⟨subtype.val '' T, cT.image _,
  image_subset_iff.2 $ λ ⟨x, xs⟩ xt, xs,
  by rwa [sUnion_image, sUnion_eq_Union]⟩

/-- In a topological space with second countable topology, if `f` is a function that sends each
point `x` to a neighborhood of `x`, then for some countable set `s`, the neighborhoods `f x`,
`x ∈ s`, cover the whole space. -/
lemma countable_cover_nhds [second_countable_topology α] {f : α → set α}
  (hf : ∀ x, f x ∈ 𝓝 x) : ∃ s : set α, countable s ∧ (⋃ x ∈ s, f x) = univ :=
begin
  rcases is_open_Union_countable (λ x, interior (f x)) (λ x, is_open_interior) with ⟨s, hsc, hsU⟩,
  suffices : (⋃ x ∈ s, interior (f x)) = univ,
    from ⟨s, hsc, flip eq_univ_of_subset this (bUnion_mono $ λ _ _, interior_subset)⟩,
  simp only [hsU, eq_univ_iff_forall, mem_Union],
  exact λ x, ⟨x, mem_interior_iff_mem_nhds.2 (hf x)⟩
end

lemma countable_cover_nhds_within [second_countable_topology α] {f : α → set α} {s : set α}
  (hf : ∀ x ∈ s, f x ∈ 𝓝[s] x) : ∃ t ⊆ s, countable t ∧ s ⊆ (⋃ x ∈ t, f x) :=
begin
  have : ∀ x : s, coe ⁻¹' (f x) ∈ 𝓝 x, from λ x, preimage_coe_mem_nhds_subtype.2 (hf x x.2),
  rcases countable_cover_nhds this with ⟨t, htc, htU⟩,
  refine ⟨coe '' t, subtype.coe_image_subset _ _, htc.image _, λ x hx, _⟩,
  simp only [bUnion_image, eq_univ_iff_forall, ← preimage_Union, mem_preimage] at htU ⊢,
  exact htU ⟨x, hx⟩
end

end topological_space

open topological_space

variables {α β : Type*} [topological_space α] [topological_space β] {f : α → β}

protected lemma inducing.second_countable_topology [second_countable_topology β]
  (hf : inducing f) : second_countable_topology α :=
by { rw hf.1, exact second_countable_topology_induced α β f }

protected lemma embedding.second_countable_topology [second_countable_topology β]
  (hf : embedding f) : second_countable_topology α :=
hf.1.second_countable_topology
