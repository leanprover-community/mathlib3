/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Properties of subsets of topological spaces: compact, clopen, irreducible,
connected, totally disconnected, totally separated.
-/

import topology.basic

open set filter lattice classical
open_locale classical

universes u v
variables {α : Type u} {β : Type v} [topological_space α]

/- compact sets -/
section compact

/-- A set `s` is compact if for every filter `f` that contains `s`,
    every set of `f` also meets every neighborhood of some `a ∈ s`. -/
def compact (s : set α) := ∀f, f ≠ ⊥ → f ≤ principal s → ∃a∈s, f ⊓ nhds a ≠ ⊥

lemma compact_inter {s t : set α} (hs : compact s) (ht : is_closed t) : compact (s ∩ t) :=
assume f hnf hstf,
let ⟨a, hsa, (ha : f ⊓ nhds a ≠ ⊥)⟩ := hs f hnf (le_trans hstf (le_principal_iff.2 (inter_subset_left _ _))) in
have ∀a, principal t ⊓ nhds a ≠ ⊥ → a ∈ t,
  by intro a; rw [inf_comm]; rw [is_closed_iff_nhds] at ht; exact ht a,
have a ∈ t,
  from this a $ neq_bot_of_le_neq_bot ha $ inf_le_inf (le_trans hstf (le_principal_iff.2 (inter_subset_right _ _))) (le_refl _),
⟨a, ⟨hsa, this⟩, ha⟩

lemma compact_diff {s t : set α} (hs : compact s) (ht : is_open t) : compact (s \ t) :=
compact_inter hs (is_closed_compl_iff.mpr ht)

lemma compact_of_is_closed_subset {s t : set α}
  (hs : compact s) (ht : is_closed t) (h : t ⊆ s) : compact t :=
by convert ← compact_inter hs ht; exact inter_eq_self_of_subset_right h

lemma compact_adherence_nhdset {s t : set α} {f : filter α}
  (hs : compact s) (hf₂ : f ≤ principal s) (ht₁ : is_open t) (ht₂ : ∀a∈s, nhds a ⊓ f ≠ ⊥ → a ∈ t) :
  t ∈ f :=
classical.by_cases mem_sets_of_neq_bot $
  assume : f ⊓ principal (- t) ≠ ⊥,
  let ⟨a, ha, (hfa : f ⊓ principal (-t) ⊓ nhds a ≠ ⊥)⟩ := hs _ this $ inf_le_left_of_le hf₂ in
  have a ∈ t,
    from ht₂ a ha $ neq_bot_of_le_neq_bot hfa $ le_inf inf_le_right $ inf_le_left_of_le inf_le_left,
  have nhds a ⊓ principal (-t) ≠ ⊥,
    from neq_bot_of_le_neq_bot hfa $ le_inf inf_le_right $ inf_le_left_of_le inf_le_right,
  have ∀s∈(nhds a ⊓ principal (-t)).sets, s ≠ ∅,
    from forall_sets_neq_empty_iff_neq_bot.mpr this,
  have false,
    from this _ ⟨t, mem_nhds_sets ht₁ ‹a ∈ t›, -t, subset.refl _, subset.refl _⟩ (inter_compl_self _),
  by contradiction

lemma compact_iff_ultrafilter_le_nhds {s : set α} :
  compact s ↔ (∀f, is_ultrafilter f → f ≤ principal s → ∃a∈s, f ≤ nhds a) :=
⟨assume hs : compact s, assume f hf hfs,
  let ⟨a, ha, h⟩ := hs _ hf.left hfs in
  ⟨a, ha, le_of_ultrafilter hf h⟩,

  assume hs : (∀f, is_ultrafilter f → f ≤ principal s → ∃a∈s, f ≤ nhds a),
  assume f hf hfs,
  let ⟨a, ha, (h : ultrafilter_of f ≤ nhds a)⟩ :=
    hs (ultrafilter_of f) (ultrafilter_ultrafilter_of hf) (le_trans ultrafilter_of_le hfs) in
  have ultrafilter_of f ⊓ nhds a ≠ ⊥,
    by simp only [inf_of_le_left, h]; exact (ultrafilter_ultrafilter_of hf).left,
  ⟨a, ha, neq_bot_of_le_neq_bot this (inf_le_inf ultrafilter_of_le (le_refl _))⟩⟩

lemma compact_elim_finite_subcover {s : set α} {c : set (set α)}
  (hs : compact s) (hc₁ : ∀t∈c, is_open t) (hc₂ : s ⊆ ⋃₀ c) : ∃c'⊆c, finite c' ∧ s ⊆ ⋃₀ c' :=
classical.by_contradiction $ assume h,
  have h : ∀{c'}, c' ⊆ c → finite c' → ¬ s ⊆ ⋃₀ c',
    from assume c' h₁ h₂ h₃, h ⟨c', h₁, h₂, h₃⟩,
  let
    f : filter α := (⨅c':{c' : set (set α) // c' ⊆ c ∧ finite c'}, principal (s - ⋃₀ c')),
    ⟨a, ha⟩ := @exists_mem_of_ne_empty α s
      (assume h', h (empty_subset _) finite_empty $ h'.symm ▸ empty_subset _)
  in
  have f ≠ ⊥, from infi_neq_bot_of_directed ⟨a⟩
    (assume ⟨c₁, hc₁, hc'₁⟩ ⟨c₂, hc₂, hc'₂⟩, ⟨⟨c₁ ∪ c₂, union_subset hc₁ hc₂, finite_union hc'₁ hc'₂⟩,
      principal_mono.mpr $ diff_subset_diff_right $ sUnion_mono $ subset_union_left _ _,
      principal_mono.mpr $ diff_subset_diff_right $ sUnion_mono $ subset_union_right _ _⟩)
    (assume ⟨c', hc'₁, hc'₂⟩, show principal (s \ _) ≠ ⊥, by simp only [ne.def, principal_eq_bot_iff, diff_eq_empty]; exact h hc'₁ hc'₂),
  have f ≤ principal s, from infi_le_of_le ⟨∅, empty_subset _, finite_empty⟩ $
    show principal (s \ ⋃₀∅) ≤ principal s, from le_principal_iff.2 (diff_subset _ _),
  let
    ⟨a, ha, (h : f ⊓ nhds a ≠ ⊥)⟩ := hs f ‹f ≠ ⊥› this,
    ⟨t, ht₁, (ht₂ : a ∈ t)⟩ := hc₂ ha
  in
  have f ≤ principal (-t),
    from infi_le_of_le ⟨{t}, by rwa singleton_subset_iff, finite_insert _ finite_empty⟩ $
      principal_mono.mpr $
        show s - ⋃₀{t} ⊆ - t, begin rw sUnion_singleton; exact assume x ⟨_, hnt⟩, hnt end,
  have is_closed (- t), from is_open_compl_iff.mp $ by rw lattice.neg_neg; exact hc₁ t ht₁,
  have a ∈ - t, from is_closed_iff_nhds.mp this _ $ neq_bot_of_le_neq_bot h $
    le_inf inf_le_right (inf_le_left_of_le ‹f ≤ principal (- t)›),
  this ‹a ∈ t›

lemma compact_elim_finite_subcover_image {s : set α} {b : set β} {c : β → set α}
  (hs : compact s) (hc₁ : ∀i∈b, is_open (c i)) (hc₂ : s ⊆ ⋃i∈b, c i) :
  ∃b'⊆b, finite b' ∧ s ⊆ ⋃i∈b', c i :=
if h : b = ∅ then ⟨∅, empty_subset _, finite_empty, h ▸ hc₂⟩ else
let ⟨i, hi⟩ := exists_mem_of_ne_empty h in
have hc'₁ : ∀i∈c '' b, is_open i, from assume i ⟨j, hj, h⟩, h ▸ hc₁ _ hj,
have hc'₂ : s ⊆ ⋃₀ (c '' b), by rwa set.sUnion_image,
let ⟨d, hd₁, hd₂, hd₃⟩ := compact_elim_finite_subcover hs hc'₁ hc'₂ in
have ∀x : d, ∃i, i ∈ b ∧ c i = x, from assume ⟨x, hx⟩, hd₁ hx,
let ⟨f', hf⟩ := axiom_of_choice this,
    f := λx:set α, (if h : x ∈ d then f' ⟨x, h⟩ else i : β) in
have ∀(x : α) (i : set α), i ∈ d → x ∈ i → (∃ (i : β), i ∈ f '' d ∧ x ∈ c i),
  from assume x i hid hxi, ⟨f i, mem_image_of_mem f hid,
    by simpa only [f, dif_pos hid, (hf ⟨_, hid⟩).2] using hxi⟩,
⟨f '' d,
  assume i ⟨j, hj, h⟩,
  h ▸ by simpa only [f, dif_pos hj] using (hf ⟨_, hj⟩).1,
  finite_image f hd₂,
  subset.trans hd₃ $ by simpa only [subset_def, mem_sUnion, exists_imp_distrib, mem_Union, exists_prop, and_imp]⟩

lemma compact_of_finite_subcover {s : set α}
  (h : ∀c, (∀t∈c, is_open t) → s ⊆ ⋃₀ c → ∃c'⊆c, finite c' ∧ s ⊆ ⋃₀ c') : compact s :=
assume f hfn hfs, classical.by_contradiction $ assume : ¬ (∃x∈s, f ⊓ nhds x ≠ ⊥),
  have hf : ∀x∈s, nhds x ⊓ f = ⊥,
    by simpa only [not_exists, not_not, inf_comm],
  have ¬ ∃x∈s, ∀t∈f.sets, x ∈ closure t,
    from assume ⟨x, hxs, hx⟩,
    have ∅ ∈ nhds x ⊓ f, by rw [empty_in_sets_eq_bot, hf x hxs],
    let ⟨t₁, ht₁, t₂, ht₂, ht⟩ := by rw [mem_inf_sets] at this; exact this in
    have ∅ ∈ nhds x ⊓ principal t₂,
      from (nhds x ⊓ principal t₂).sets_of_superset (inter_mem_inf_sets ht₁ (subset.refl t₂)) ht,
    have nhds x ⊓ principal t₂ = ⊥,
      by rwa [empty_in_sets_eq_bot] at this,
    by simp only [closure_eq_nhds] at hx; exact hx t₂ ht₂ this,
  have ∀x∈s, ∃t∈f.sets, x ∉ closure t, by simpa only [not_exists, not_forall],
  let c := (λt, - closure t) '' f.sets, ⟨c', hcc', hcf, hsc'⟩ := h c
    (assume t ⟨s, hs, h⟩, h ▸ is_closed_closure) (by simpa only [subset_def, sUnion_image, mem_Union]) in
  let ⟨b, hb⟩ := axiom_of_choice $
    show ∀s:c', ∃t, t ∈ f ∧ - closure t = s,
      from assume ⟨x, hx⟩, hcc' hx in
  have (⋂s∈c', if h : s ∈ c' then b ⟨s, h⟩ else univ) ∈ f,
    from Inter_mem_sets hcf $ assume t ht, by rw [dif_pos ht]; exact (hb ⟨t, ht⟩).left,
  have s ∩ (⋂s∈c', if h : s ∈ c' then b ⟨s, h⟩ else univ) ∈ f,
    from inter_mem_sets (le_principal_iff.1 hfs) this,
  have ∅ ∈ f,
    from mem_sets_of_superset this $ assume x ⟨hxs, hxi⟩,
    let ⟨t, htc', hxt⟩ := (show ∃t ∈ c', x ∈ t, from hsc' hxs) in
    have -closure (b ⟨t, htc'⟩) = t, from (hb _).right,
    have x ∈ - t,
      from this ▸ (calc x ∈ b ⟨t, htc'⟩ : by rw mem_bInter_iff at hxi; have h := hxi t htc'; rwa [dif_pos htc'] at h
        ... ⊆ closure (b ⟨t, htc'⟩) : subset_closure
        ... ⊆ - - closure (b ⟨t, htc'⟩) : by rw lattice.neg_neg; exact subset.refl _),
    show false, from this hxt,
  hfn $ by rwa [empty_in_sets_eq_bot] at this

lemma compact_iff_finite_subcover {s : set α} :
  compact s ↔ (∀c, (∀t∈c, is_open t) → s ⊆ ⋃₀ c → ∃c'⊆c, finite c' ∧ s ⊆ ⋃₀ c') :=
⟨assume hc c, compact_elim_finite_subcover hc, compact_of_finite_subcover⟩

lemma compact_empty : compact (∅ : set α) :=
assume f hnf hsf, not.elim hnf $
empty_in_sets_eq_bot.1 $ le_principal_iff.1 hsf

lemma compact_singleton {a : α} : compact ({a} : set α) :=
compact_of_finite_subcover $ assume c hc₁ hc₂,
  let ⟨i, hic, hai⟩ := (show ∃i ∈ c, a ∈ i, from mem_sUnion.1 $ singleton_subset_iff.1 hc₂) in
  ⟨{i}, singleton_subset_iff.2 hic, finite_singleton _, by rwa [sUnion_singleton, singleton_subset_iff]⟩

lemma compact_bUnion_of_compact {s : set β} {f : β → set α} (hs : finite s) :
  (∀i ∈ s, compact (f i)) → compact (⋃i ∈ s, f i) :=
assume hf, compact_of_finite_subcover $ assume c c_open c_cover,
  have ∀i : subtype s, ∃c' ⊆ c, finite c' ∧ f i ⊆ ⋃₀ c', from
    assume ⟨i, hi⟩, compact_elim_finite_subcover (hf i hi) c_open
      (calc f i ⊆ ⋃i ∈ s, f i : subset_bUnion_of_mem hi
            ... ⊆ ⋃₀ c        : c_cover),
  let ⟨finite_subcovers, h⟩ := axiom_of_choice this in
  let c' := ⋃i, finite_subcovers i in
  have c' ⊆ c, from Union_subset (λi, (h i).fst),
  have finite c', from @finite_Union _ _ hs.fintype _ (λi, (h i).snd.1),
  have (⋃i ∈ s, f i) ⊆ ⋃₀ c', from bUnion_subset $ λi hi, calc
    f i ⊆ ⋃₀ finite_subcovers ⟨i,hi⟩ : (h ⟨i,hi⟩).snd.2
    ... ⊆ ⋃₀ c'                      : sUnion_mono (subset_Union _ _),
  ⟨c', ‹c' ⊆ c›, ‹finite c'›, this⟩

lemma compact_Union_of_compact {f : β → set α} [fintype β]
  (h : ∀i, compact (f i)) : compact (⋃i, f i) :=
by rw ← bUnion_univ; exact compact_bUnion_of_compact finite_univ (λ i _, h i)

lemma compact_of_finite {s : set α} (hs : finite s) : compact s :=
let s' : set α := ⋃i ∈ s, {i} in
have e : s' = s, from ext $ λi, by simp only [mem_bUnion_iff, mem_singleton_iff, exists_eq_right'],
have compact s', from compact_bUnion_of_compact hs (λ_ _, compact_singleton),
e ▸ this

lemma compact_union_of_compact {s t : set α} (hs : compact s) (ht : compact t) : compact (s ∪ t) :=
by rw union_eq_Union; exact compact_Union_of_compact (λ b, by cases b; assumption)

/-- Type class for compact spaces. Separation is sometimes included in the definition, especially
in the French literature, but we do not include it here. -/
class compact_space (α : Type*) [topological_space α] : Prop :=
(compact_univ : compact (univ : set α))

lemma compact_univ [topological_space α] [h : compact_space α] : compact (univ : set α) := h.compact_univ

lemma compact_of_closed [topological_space α] [compact_space α] {s : set α} (h : is_closed s) :
  compact s :=
compact_of_is_closed_subset compact_univ h (subset_univ _)

lemma compact_image [topological_space β] {s : set α} {f : α → β} (hs : compact s) (hf : continuous f) : compact (f '' s) :=
compact_of_finite_subcover $ assume c hco hcs,
  have hdo : ∀t∈c, is_open (f ⁻¹' t), from assume t' ht, hf _ $ hco _ ht,
  have hds : s ⊆ ⋃i∈c, f ⁻¹' i,
    by simpa [subset_def, -mem_image] using hcs,
  let ⟨d', hcd', hfd', hd'⟩ := compact_elim_finite_subcover_image hs hdo hds in
  ⟨d', hcd', hfd', by simpa [subset_def, -mem_image, image_subset_iff] using hd'⟩

lemma compact_range [compact_space α] [topological_space β] {f : α → β} (hf : continuous f) : compact (range f) :=
by rw ← image_univ; exact compact_image compact_univ hf

/-- There are various definitions of "locally compact space" in the literature, which agree for
Hausdorff spaces but not in general. This one is the precise condition on X needed for the
evaluation `map C(X, Y) × X → Y` to be continuous for all `Y` when `C(X, Y)` is given the
compact-open topology. -/
class locally_compact_space (α : Type*) [topological_space α] : Prop :=
(local_compact_nhds : ∀ (x : α) (n ∈ nhds x), ∃ s ∈ nhds x, s ⊆ n ∧ compact s)

end compact

section clopen

def is_clopen (s : set α) : Prop :=
is_open s ∧ is_closed s

theorem is_clopen_union {s t : set α} (hs : is_clopen s) (ht : is_clopen t) : is_clopen (s ∪ t) :=
⟨is_open_union hs.1 ht.1, is_closed_union hs.2 ht.2⟩

theorem is_clopen_inter {s t : set α} (hs : is_clopen s) (ht : is_clopen t) : is_clopen (s ∩ t) :=
⟨is_open_inter hs.1 ht.1, is_closed_inter hs.2 ht.2⟩

@[simp] theorem is_clopen_empty : is_clopen (∅ : set α) :=
⟨is_open_empty, is_closed_empty⟩

@[simp] theorem is_clopen_univ : is_clopen (univ : set α) :=
⟨is_open_univ, is_closed_univ⟩

theorem is_clopen_compl {s : set α} (hs : is_clopen s) : is_clopen (-s) :=
⟨hs.2, is_closed_compl_iff.2 hs.1⟩

@[simp] theorem is_clopen_compl_iff {s : set α} : is_clopen (-s) ↔ is_clopen s :=
⟨λ h, compl_compl s ▸ is_clopen_compl h, is_clopen_compl⟩

theorem is_clopen_diff {s t : set α} (hs : is_clopen s) (ht : is_clopen t) : is_clopen (s-t) :=
is_clopen_inter hs (is_clopen_compl ht)

end clopen

section irreducible

/-- A irreducible set is one where there is no non-trivial pair of disjoint opens. -/
def is_irreducible (s : set α) : Prop :=
∀ (u v : set α), is_open u → is_open v →
  (∃ x, x ∈ s ∩ u) → (∃ x, x ∈ s ∩ v) → ∃ x, x ∈ s ∩ (u ∩ v)

theorem is_irreducible_empty : is_irreducible (∅ : set α) :=
λ _ _ _ _ _ ⟨x, h1, h2⟩, h1.elim

theorem is_irreducible_singleton {x} : is_irreducible ({x} : set α) :=
λ u v _ _ ⟨y, h1, h2⟩ ⟨z, h3, h4⟩, by rw mem_singleton_iff at h1 h3;
substs y z; exact ⟨x, or.inl rfl, h2, h4⟩

theorem is_irreducible_closure {s : set α} (H : is_irreducible s) :
  is_irreducible (closure s) :=
λ u v hu hv ⟨y, hycs, hyu⟩ ⟨z, hzcs, hzv⟩,
let ⟨p, hpu, hps⟩ := exists_mem_of_ne_empty (mem_closure_iff.1 hycs u hu hyu) in
let ⟨q, hqv, hqs⟩ := exists_mem_of_ne_empty (mem_closure_iff.1 hzcs v hv hzv) in
let ⟨r, hrs, hruv⟩ := H u v hu hv ⟨p, hps, hpu⟩ ⟨q, hqs, hqv⟩ in
⟨r, subset_closure hrs, hruv⟩

theorem exists_irreducible (s : set α) (H : is_irreducible s) :
  ∃ t : set α, is_irreducible t ∧ s ⊆ t ∧ ∀ u, is_irreducible u → t ⊆ u → u = t :=
let ⟨m, hm, hsm, hmm⟩ := zorn.zorn_subset₀ { t : set α | is_irreducible t }
  (λ c hc hcc hcn, let ⟨t, htc⟩ := exists_mem_of_ne_empty hcn in
    ⟨⋃₀ c, λ u v hu hv ⟨y, hy, hyu⟩ ⟨z, hz, hzv⟩,
      let ⟨p, hpc, hyp⟩ := mem_sUnion.1 hy,
          ⟨q, hqc, hzq⟩ := mem_sUnion.1 hz in
      or.cases_on (zorn.chain.total hcc hpc hqc)
        (assume hpq : p ⊆ q, let ⟨x, hxp, hxuv⟩ := hc hqc u v hu hv
            ⟨y, hpq hyp, hyu⟩ ⟨z, hzq, hzv⟩ in
          ⟨x, mem_sUnion_of_mem hxp hqc, hxuv⟩)
        (assume hqp : q ⊆ p, let ⟨x, hxp, hxuv⟩ := hc hpc u v hu hv
            ⟨y, hyp, hyu⟩ ⟨z, hqp hzq, hzv⟩ in
          ⟨x, mem_sUnion_of_mem hxp hpc, hxuv⟩),
    λ x hxc, set.subset_sUnion_of_mem hxc⟩) s H in
⟨m, hm, hsm, λ u hu hmu, hmm _ hu hmu⟩

def irreducible_component (x : α) : set α :=
classical.some (exists_irreducible {x} is_irreducible_singleton)

theorem is_irreducible_irreducible_component {x : α} : is_irreducible (irreducible_component x) :=
(classical.some_spec (exists_irreducible {x} is_irreducible_singleton)).1

theorem mem_irreducible_component {x : α} : x ∈ irreducible_component x :=
singleton_subset_iff.1
  (classical.some_spec (exists_irreducible {x} is_irreducible_singleton)).2.1

theorem eq_irreducible_component {x : α} :
  ∀ {s : set α}, is_irreducible s → irreducible_component x ⊆ s → s = irreducible_component x :=
(classical.some_spec (exists_irreducible {x} is_irreducible_singleton)).2.2

theorem is_closed_irreducible_component {x : α} :
  is_closed (irreducible_component x) :=
closure_eq_iff_is_closed.1 $ eq_irreducible_component
  (is_irreducible_closure is_irreducible_irreducible_component)
  subset_closure

/-- A irreducible space is one where there is no non-trivial pair of disjoint opens. -/
class irreducible_space (α : Type u) [topological_space α] : Prop :=
(is_irreducible_univ : is_irreducible (univ : set α))

theorem irreducible_exists_mem_inter [irreducible_space α] {s t : set α} :
  is_open s → is_open t → (∃ x, x ∈ s) → (∃ x, x ∈ t) → ∃ x, x ∈ s ∩ t :=
by simpa only [univ_inter, univ_subset_iff] using
  @irreducible_space.is_irreducible_univ α _ _ s t

end irreducible

section connected

/-- A connected set is one where there is no non-trivial open partition. -/
def is_connected (s : set α) : Prop :=
∀ (u v : set α), is_open u → is_open v → s ⊆ u ∪ v →
  (∃ x, x ∈ s ∩ u) → (∃ x, x ∈ s ∩ v) → ∃ x, x ∈ s ∩ (u ∩ v)

theorem is_connected_of_is_irreducible {s : set α} (H : is_irreducible s) : is_connected s :=
λ _ _ hu hv _, H _ _ hu hv

theorem is_connected_empty : is_connected (∅ : set α) :=
is_connected_of_is_irreducible is_irreducible_empty

theorem is_connected_singleton {x} : is_connected ({x} : set α) :=
is_connected_of_is_irreducible is_irreducible_singleton

theorem is_connected_sUnion (x : α) (c : set (set α)) (H1 : ∀ s ∈ c, x ∈ s)
  (H2 : ∀ s ∈ c, is_connected s) : is_connected (⋃₀ c) :=
begin
  rintro u v hu hv hUcuv ⟨y, hyUc, hyu⟩ ⟨z, hzUc, hzv⟩,
  cases classical.em (c = ∅) with hc hc,
  { rw [hc, sUnion_empty] at hyUc, exact hyUc.elim },
  cases ne_empty_iff_exists_mem.1 hc with s hs,
  cases hUcuv (mem_sUnion_of_mem (H1 s hs) hs) with hxu hxv,
  { rcases hzUc with ⟨t, htc, hzt⟩,
    specialize H2 t htc u v hu hv (subset.trans (subset_sUnion_of_mem htc) hUcuv),
    cases H2 ⟨x, H1 t htc, hxu⟩ ⟨z, hzt, hzv⟩ with r hr,
    exact ⟨r, mem_sUnion_of_mem hr.1 htc, hr.2⟩ },
  { rcases hyUc with ⟨t, htc, hyt⟩,
    specialize H2 t htc u v hu hv (subset.trans (subset_sUnion_of_mem htc) hUcuv),
    cases H2 ⟨y, hyt, hyu⟩ ⟨x, H1 t htc, hxv⟩ with r hr,
    exact ⟨r, mem_sUnion_of_mem hr.1 htc, hr.2⟩ }
end

theorem is_connected_union (x : α) {s t : set α} (H1 : x ∈ s) (H2 : x ∈ t)
  (H3 : is_connected s) (H4 : is_connected t) : is_connected (s ∪ t) :=
have _ := is_connected_sUnion x {t,s}
  (by rintro r (rfl | rfl | h); [exact H1, exact H2, exact h.elim])
  (by rintro r (rfl | rfl | h); [exact H3, exact H4, exact h.elim]),
have h2 : ⋃₀ {t, s} = s ∪ t, from (sUnion_insert _ _).trans (by rw sUnion_singleton),
by rwa h2 at this

theorem is_connected_closure {s : set α} (H : is_connected s) :
  is_connected (closure s) :=
λ u v hu hv hcsuv ⟨y, hycs, hyu⟩ ⟨z, hzcs, hzv⟩,
let ⟨p, hpu, hps⟩ := exists_mem_of_ne_empty (mem_closure_iff.1 hycs u hu hyu) in
let ⟨q, hqv, hqs⟩ := exists_mem_of_ne_empty (mem_closure_iff.1 hzcs v hv hzv) in
let ⟨r, hrs, hruv⟩ := H u v hu hv (subset.trans subset_closure hcsuv) ⟨p, hps, hpu⟩ ⟨q, hqs, hqv⟩ in
⟨r, subset_closure hrs, hruv⟩

def connected_component (x : α) : set α :=
⋃₀ { s : set α | is_connected s ∧ x ∈ s }

theorem is_connected_connected_component {x : α} : is_connected (connected_component x) :=
is_connected_sUnion x _ (λ _, and.right) (λ _, and.left)

theorem mem_connected_component {x : α} : x ∈ connected_component x :=
mem_sUnion_of_mem (mem_singleton x) ⟨is_connected_singleton, mem_singleton x⟩

theorem subset_connected_component {x : α} {s : set α} (H1 : is_connected s) (H2 : x ∈ s) :
  s ⊆ connected_component x :=
λ z hz, mem_sUnion_of_mem hz ⟨H1, H2⟩

theorem is_closed_connected_component {x : α} :
  is_closed (connected_component x) :=
closure_eq_iff_is_closed.1 $ subset.antisymm
  (subset_connected_component
    (is_connected_closure is_connected_connected_component)
    (subset_closure mem_connected_component))
  subset_closure

theorem irreducible_component_subset_connected_component {x : α} :
  irreducible_component x ⊆ connected_component x :=
subset_connected_component
  (is_connected_of_is_irreducible is_irreducible_irreducible_component)
  mem_irreducible_component

/-- A connected space is one where there is no non-trivial open partition. -/
class connected_space (α : Type u) [topological_space α] : Prop :=
(is_connected_univ : is_connected (univ : set α))

instance irreducible_space.connected_space (α : Type u) [topological_space α]
  [irreducible_space α] : connected_space α :=
⟨is_connected_of_is_irreducible $ irreducible_space.is_irreducible_univ α⟩

theorem exists_mem_inter [connected_space α] {s t : set α} :
  is_open s → is_open t → s ∪ t = univ →
    (∃ x, x ∈ s) → (∃ x, x ∈ t) → ∃ x, x ∈ s ∩ t :=
by simpa only [univ_inter, univ_subset_iff] using
  @connected_space.is_connected_univ α _ _ s t

theorem is_clopen_iff [connected_space α] {s : set α} : is_clopen s ↔ s = ∅ ∨ s = univ :=
⟨λ hs, classical.by_contradiction $ λ h,
  have h1 : s ≠ ∅ ∧ -s ≠ ∅, from ⟨mt or.inl h,
    mt (λ h2, or.inr $ (by rw [← compl_compl s, h2, compl_empty] : s = univ)) h⟩,
  let ⟨_, h2, h3⟩ := exists_mem_inter hs.1 hs.2 (union_compl_self s)
    (ne_empty_iff_exists_mem.1 h1.1) (ne_empty_iff_exists_mem.1 h1.2) in
  h3 h2,
by rintro (rfl | rfl); [exact is_clopen_empty, exact is_clopen_univ]⟩

end connected

section totally_disconnected

def is_totally_disconnected (s : set α) : Prop :=
∀ t, t ⊆ s → is_connected t → subsingleton t

theorem is_totally_disconnected_empty : is_totally_disconnected (∅ : set α) :=
λ t ht _, ⟨λ ⟨_, h⟩, (ht h).elim⟩

theorem is_totally_disconnected_singleton {x} : is_totally_disconnected ({x} : set α) :=
λ t ht _, ⟨λ ⟨p, hp⟩ ⟨q, hq⟩, subtype.eq $ show p = q,
from (eq_of_mem_singleton (ht hp)).symm ▸ (eq_of_mem_singleton (ht hq)).symm⟩

class totally_disconnected_space (α : Type u) [topological_space α] : Prop :=
(is_totally_disconnected_univ : is_totally_disconnected (univ : set α))

end totally_disconnected

section totally_separated

def is_totally_separated (s : set α) : Prop :=
∀ x ∈ s, ∀ y ∈ s, x ≠ y → ∃ u v : set α, is_open u ∧ is_open v ∧
  x ∈ u ∧ y ∈ v ∧ s ⊆ u ∪ v ∧ u ∩ v = ∅

theorem is_totally_separated_empty : is_totally_separated (∅ : set α) :=
λ x, false.elim

theorem is_totally_separated_singleton {x} : is_totally_separated ({x} : set α) :=
λ p hp q hq hpq, (hpq $ (eq_of_mem_singleton hp).symm ▸ (eq_of_mem_singleton hq).symm).elim

theorem is_totally_disconnected_of_is_totally_separated {s : set α}
  (H : is_totally_separated s) : is_totally_disconnected s :=
λ t hts ht, ⟨λ ⟨x, hxt⟩ ⟨y, hyt⟩, subtype.eq $ classical.by_contradiction $
assume hxy : x ≠ y, let ⟨u, v, hu, hv, hxu, hyv, hsuv, huv⟩ := H x (hts hxt) y (hts hyt) hxy in
let ⟨r, hrt, hruv⟩ := ht u v hu hv (subset.trans hts hsuv) ⟨x, hxt, hxu⟩ ⟨y, hyt, hyv⟩ in
((ext_iff _ _).1 huv r).1 hruv⟩

class totally_separated_space (α : Type u) [topological_space α] : Prop :=
(is_totally_separated_univ : is_totally_separated (univ : set α))

instance totally_separated_space.totally_disconnected_space (α : Type u) [topological_space α]
  [totally_separated_space α] : totally_disconnected_space α :=
⟨is_totally_disconnected_of_is_totally_separated $ totally_separated_space.is_totally_separated_univ α⟩

end totally_separated
