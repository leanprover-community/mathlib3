/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import order.filter.basic
import data.set.countable
import data.pprod

/-!
# Filter bases

A filter basis `B : filter_basis α` on a type `α` is a nonempty collection of sets of `α`
such that the intersection of two elements of this collection contains some element of
the collection. Compared to filters, filter bases do not require that any set containing
an element of `B` belongs to `B`.
A filter basis `B` can be used to construct `B.filter : filter α` such that a set belongs
to `B.filter` if and only if it contains an element of `B`.

Given an indexing type `ι`, a predicate `p : ι → Prop`, and a map `s : ι → set α`,
the proposition `h : filter.is_basis p s` makes sure the range of `s` bounded by `p`
(ie. `s '' set_of p`) defines a filter basis `h.filter_basis`.

If one already has a filter `l` on `α`, `filter.has_basis l p s` (where `p : ι → Prop`
and `s : ι → set α` as above) means that a set belongs to `l` if and
only if it contains some `s i` with `p i`. It implies `h : filter.is_basis p s`, and
`l = h.filter_basis.filter`. The point of this definition is that checking statements
involving elements of `l` often reduces to checking them on the basis elements.

We define a function `has_basis.index (h : filter.has_basis l p s) (t) (ht : t ∈ l)` that returns
some index `i` such that `p i` and `s i ⊆ t`. This function can be useful to avoid manual
destruction of `h.mem_iff.mpr ht` using `cases` or `let`.

This file also introduces more restricted classes of bases, involving monotonicity or
countability. In particular, for `l : filter α`, `l.is_countably_generated` means
there is a countable set of sets which generates `s`. This is reformulated in term of bases,
and consequences are derived.

## Main statements

* `has_basis.mem_iff`, `has_basis.mem_of_superset`, `has_basis.mem_of_mem` : restate `t ∈ f`
  in terms of a basis;
* `basis_sets` : all sets of a filter form a basis;
* `has_basis.inf`, `has_basis.inf_principal`, `has_basis.prod`, `has_basis.prod_self`,
  `has_basis.map`, `has_basis.comap` : combinators to construct filters of `l ⊓ l'`,
  `l ⊓ 𝓟 t`, `l ×ᶠ l'`, `l ×ᶠ l`, `l.map f`, `l.comap f` respectively;
* `has_basis.le_iff`, `has_basis.ge_iff`, has_basis.le_basis_iff` : restate `l ≤ l'` in terms
  of bases.
* `has_basis.tendsto_right_iff`, `has_basis.tendsto_left_iff`, `has_basis.tendsto_iff` : restate
  `tendsto f l l'` in terms of bases.
* `is_countably_generated_iff_exists_antitone_basis` : proves a filter is
  countably generated if and only if it admits a basis parametrized by a
  decreasing sequence of sets indexed by `ℕ`.
* `tendsto_iff_seq_tendsto ` : an abstract version of "sequentially continuous implies continuous".

## Implementation notes

As with `Union`/`bUnion`/`sUnion`, there are three different approaches to filter bases:

* `has_basis l s`, `s : set (set α)`;
* `has_basis l s`, `s : ι → set α`;
* `has_basis l p s`, `p : ι → Prop`, `s : ι → set α`.

We use the latter one because, e.g., `𝓝 x` in an `emetric_space` or in a `metric_space` has a basis
of this form. The other two can be emulated using `s = id` or `p = λ _, true`.

With this approach sometimes one needs to `simp` the statement provided by the `has_basis`
machinery, e.g., `simp only [exists_prop, true_and]` or `simp only [forall_const]` can help
with the case `p = λ _, true`.
-/

open set filter
open_locale filter classical

section sort

variables {α β γ : Type*} {ι ι' : Sort*}

/-- A filter basis `B` on a type `α` is a nonempty collection of sets of `α`
such that the intersection of two elements of this collection contains some element
of the collection. -/
structure filter_basis (α : Type*) :=
(sets                   : set (set α))
(nonempty               : sets.nonempty)
(inter_sets {x y}       : x ∈ sets → y ∈ sets → ∃ z ∈ sets, z ⊆ x ∩ y)

instance filter_basis.nonempty_sets (B : filter_basis α) : nonempty B.sets := B.nonempty.to_subtype

/-- If `B` is a filter basis on `α`, and `U` a subset of `α` then we can write `U ∈ B` as
on paper. -/
@[reducible]
instance {α : Type*}: has_mem (set α) (filter_basis α) := ⟨λ U B, U ∈ B.sets⟩

-- For illustration purposes, the filter basis defining (at_top : filter ℕ)
instance : inhabited (filter_basis ℕ) :=
⟨{ sets := range Ici,
  nonempty := ⟨Ici 0, mem_range_self 0⟩,
  inter_sets := begin
    rintros _ _ ⟨n, rfl⟩ ⟨m, rfl⟩,
    refine ⟨Ici (max n m), mem_range_self _, _⟩,
    rintros p p_in,
    split ; rw mem_Ici at *,
    exact le_of_max_le_left p_in,
    exact le_of_max_le_right p_in,
  end }⟩

/-- `is_basis p s` means the image of `s` bounded by `p` is a filter basis. -/
protected structure filter.is_basis (p : ι → Prop) (s : ι → set α) : Prop :=
(nonempty : ∃ i, p i)
(inter : ∀ {i j}, p i → p j → ∃ k, p k ∧ s k ⊆ s i ∩ s j)

namespace filter
namespace is_basis

/-- Constructs a filter basis from an indexed family of sets satisfying `is_basis`. -/
protected def filter_basis {p : ι → Prop} {s : ι → set α} (h : is_basis p s) : filter_basis α :=
{ sets := {t | ∃ i, p i ∧ s i = t},
  nonempty := let ⟨i, hi⟩ := h.nonempty in ⟨s i, ⟨i, hi, rfl⟩⟩,
  inter_sets := by { rintros _ _ ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩,
                     rcases h.inter hi hj with ⟨k, hk, hk'⟩,
                     exact ⟨_, ⟨k, hk, rfl⟩, hk'⟩ } }

variables {p : ι → Prop} {s : ι → set α} (h : is_basis p s)

lemma mem_filter_basis_iff {U : set α} : U ∈ h.filter_basis ↔ ∃ i, p i ∧ s i = U :=
iff.rfl
end is_basis
end filter

namespace filter_basis

/-- The filter associated to a filter basis. -/
protected def filter (B : filter_basis α) : filter α :=
{ sets := {s | ∃ t ∈ B, t ⊆ s},
  univ_sets := let ⟨s, s_in⟩ := B.nonempty in ⟨s, s_in, s.subset_univ⟩,
  sets_of_superset := λ x y ⟨s, s_in, h⟩ hxy, ⟨s, s_in, set.subset.trans h hxy⟩,
  inter_sets := λ x y ⟨s, s_in, hs⟩ ⟨t, t_in, ht⟩,
                let ⟨u, u_in, u_sub⟩ := B.inter_sets s_in t_in in
                ⟨u, u_in, set.subset.trans u_sub $ set.inter_subset_inter hs ht⟩ }

lemma mem_filter_iff (B : filter_basis α) {U : set α} : U ∈ B.filter ↔ ∃ s ∈ B, s ⊆ U :=
iff.rfl

lemma mem_filter_of_mem (B : filter_basis α) {U : set α} : U ∈ B → U ∈ B.filter:=
λ U_in, ⟨U, U_in, subset.refl _⟩

lemma eq_infi_principal (B : filter_basis α) : B.filter = ⨅ s : B.sets, 𝓟 s :=
begin
  have : directed (≥) (λ (s : B.sets), 𝓟 (s : set α)),
  { rintros ⟨U, U_in⟩ ⟨V, V_in⟩,
    rcases B.inter_sets U_in V_in with ⟨W, W_in, W_sub⟩,
    use [W, W_in],
    simp only [ge_iff_le, le_principal_iff, mem_principal, subtype.coe_mk],
    exact subset_inter_iff.mp W_sub },
  ext U,
  simp [mem_filter_iff, mem_infi_of_directed this]
end

protected lemma generate (B : filter_basis α) : generate B.sets = B.filter :=
begin
  apply le_antisymm,
  { intros U U_in,
    rcases B.mem_filter_iff.mp U_in with ⟨V, V_in, h⟩,
    exact generate_sets.superset (generate_sets.basic V_in) h },
  { rw sets_iff_generate,
    apply mem_filter_of_mem }
end
end filter_basis

namespace filter
namespace is_basis
variables {p : ι → Prop} {s : ι → set α}

/-- Constructs a filter from an indexed family of sets satisfying `is_basis`. -/
protected def filter (h : is_basis p s) : filter α := h.filter_basis.filter

protected lemma mem_filter_iff (h : is_basis p s) {U : set α} :
  U ∈ h.filter ↔ ∃ i, p i ∧ s i ⊆ U :=
begin
  erw [h.filter_basis.mem_filter_iff],
  simp only [mem_filter_basis_iff h, exists_prop],
  split,
  { rintros ⟨_, ⟨i, pi, rfl⟩, h⟩,
    tauto },
  { tauto }
end

lemma filter_eq_generate (h : is_basis p s) : h.filter = generate {U | ∃ i, p i ∧ s i = U} :=
by erw h.filter_basis.generate ; refl
end is_basis

/-- We say that a filter `l` has a basis `s : ι → set α` bounded by `p : ι → Prop`,
if `t ∈ l` if and only if `t` includes `s i` for some `i` such that `p i`. -/
protected structure has_basis (l : filter α) (p : ι → Prop) (s : ι → set α) : Prop :=
(mem_iff' : ∀ (t : set α), t ∈ l ↔ ∃ i (hi : p i), s i ⊆ t)

section same_type

variables {l l' : filter α} {p : ι → Prop} {s : ι → set α} {t : set α} {i : ι}
  {p' : ι' → Prop} {s' : ι' → set α} {i' : ι'}

lemma has_basis_generate (s : set (set α)) :
  (generate s).has_basis (λ t, finite t ∧ t ⊆ s) (λ t, ⋂₀ t) :=
⟨begin
  intro U,
  rw mem_generate_iff,
  apply exists_congr,
  tauto
end⟩

/-- The smallest filter basis containing a given collection of sets. -/
def filter_basis.of_sets (s : set (set α)) : filter_basis α :=
{ sets := sInter '' { t | finite t ∧ t ⊆ s},
  nonempty := ⟨univ, ∅, ⟨⟨finite_empty, empty_subset s⟩, sInter_empty⟩⟩,
  inter_sets := begin
    rintros _ _ ⟨a, ⟨fina, suba⟩, rfl⟩ ⟨b, ⟨finb, subb⟩, rfl⟩,
    exact ⟨⋂₀ (a ∪ b), mem_image_of_mem _ ⟨fina.union finb, union_subset suba subb⟩,
           by rw sInter_union⟩,
  end }

/-- Definition of `has_basis` unfolded with implicit set argument. -/
lemma has_basis.mem_iff (hl : l.has_basis p s) : t ∈ l ↔ ∃ i (hi : p i), s i ⊆ t :=
hl.mem_iff' t

lemma has_basis.eq_of_same_basis (hl : l.has_basis p s) (hl' : l'.has_basis p s) : l = l' :=
begin
  ext t,
  rw [hl.mem_iff, hl'.mem_iff]
end

lemma has_basis_iff : l.has_basis p s ↔ ∀ t, t ∈ l ↔ ∃ i (hi : p i), s i ⊆ t :=
⟨λ ⟨h⟩, h, λ h, ⟨h⟩⟩

lemma has_basis.ex_mem (h : l.has_basis p s) : ∃ i, p i :=
let ⟨i, pi, h⟩ := h.mem_iff.mp univ_mem in ⟨i, pi⟩

protected lemma has_basis.nonempty (h : l.has_basis p s) : nonempty ι :=
nonempty_of_exists h.ex_mem

protected lemma is_basis.has_basis (h : is_basis p s) : has_basis h.filter p s :=
⟨λ t, by simp only [h.mem_filter_iff, exists_prop]⟩

lemma has_basis.mem_of_superset (hl : l.has_basis p s) (hi : p i) (ht : s i ⊆ t) : t ∈ l :=
(hl.mem_iff).2 ⟨i, hi, ht⟩

lemma has_basis.mem_of_mem (hl : l.has_basis p s) (hi : p i) : s i ∈ l :=
hl.mem_of_superset hi $ subset.refl _

/-- Index of a basis set such that `s i ⊆ t` as an element of `subtype p`. -/
noncomputable def has_basis.index (h : l.has_basis p s) (t : set α) (ht : t ∈ l) :
  {i : ι // p i} :=
⟨(h.mem_iff.1 ht).some, (h.mem_iff.1 ht).some_spec.fst⟩

lemma has_basis.property_index (h : l.has_basis p s) (ht : t ∈ l) : p (h.index t ht) :=
(h.index t ht).2

lemma has_basis.set_index_mem (h : l.has_basis p s) (ht : t ∈ l) : s (h.index t ht) ∈ l :=
h.mem_of_mem $ h.property_index _

lemma has_basis.set_index_subset (h : l.has_basis p s) (ht : t ∈ l) : s (h.index t ht) ⊆ t :=
(h.mem_iff.1 ht).some_spec.snd

lemma has_basis.is_basis (h : l.has_basis p s) : is_basis p s :=
{ nonempty := let ⟨i, hi, H⟩ := h.mem_iff.mp univ_mem in ⟨i, hi⟩,
  inter := λ i j hi hj, by simpa [h.mem_iff]
    using l.inter_sets (h.mem_of_mem hi) (h.mem_of_mem hj) }

lemma has_basis.filter_eq (h : l.has_basis p s) : h.is_basis.filter = l :=
by { ext U, simp [h.mem_iff, is_basis.mem_filter_iff] }

lemma has_basis.eq_generate (h : l.has_basis p s) : l = generate { U | ∃ i, p i ∧ s i = U } :=
by rw [← h.is_basis.filter_eq_generate, h.filter_eq]

lemma generate_eq_generate_inter (s : set (set α)) :
  generate s = generate (sInter '' { t | finite t ∧ t ⊆ s}) :=
by erw [(filter_basis.of_sets s).generate, ← (has_basis_generate s).filter_eq] ; refl

lemma of_sets_filter_eq_generate (s : set (set α)) : (filter_basis.of_sets s).filter = generate s :=
by rw [← (filter_basis.of_sets s).generate, generate_eq_generate_inter s] ; refl

protected lemma _root_.filter_basis.has_basis {α : Type*} (B : filter_basis α) :
  has_basis (B.filter) (λ s : set α, s ∈ B) id :=
⟨λ t, B.mem_filter_iff⟩

lemma has_basis.to_has_basis' (hl : l.has_basis p s) (h : ∀ i, p i → ∃ i', p' i' ∧ s' i' ⊆ s i)
  (h' : ∀ i', p' i' → s' i' ∈ l) : l.has_basis p' s' :=
begin
  refine ⟨λ t, ⟨λ ht, _, λ ⟨i', hi', ht⟩, mem_of_superset (h' i' hi') ht⟩⟩,
  rcases hl.mem_iff.1 ht with ⟨i, hi, ht⟩,
  rcases h i hi with ⟨i', hi', hs's⟩,
  exact ⟨i', hi', subset.trans hs's ht⟩
end

lemma has_basis.to_has_basis (hl : l.has_basis p s) (h : ∀ i, p i → ∃ i', p' i' ∧ s' i' ⊆ s i)
  (h' : ∀ i', p' i' → ∃ i, p i ∧ s i ⊆ s' i') : l.has_basis p' s' :=
hl.to_has_basis' h $ λ i' hi', let ⟨i, hi, hss'⟩ := h' i' hi' in hl.mem_iff.2 ⟨i, hi, hss'⟩

lemma has_basis.to_subset (hl : l.has_basis p s) {t : ι → set α} (h : ∀ i, p i → t i ⊆ s i)
  (ht : ∀ i, p i → t i ∈ l) : l.has_basis p t :=
hl.to_has_basis' (λ i hi, ⟨i, hi, h i hi⟩) ht

lemma has_basis.eventually_iff (hl : l.has_basis p s) {q : α → Prop} :
  (∀ᶠ x in l, q x) ↔ ∃ i, p i ∧ ∀ ⦃x⦄, x ∈ s i → q x :=
by simpa using hl.mem_iff

lemma has_basis.frequently_iff (hl : l.has_basis p s) {q : α → Prop} :
  (∃ᶠ x in l, q x) ↔ ∀ i, p i → ∃ x ∈ s i, q x :=
by simp [filter.frequently, hl.eventually_iff]

lemma has_basis.exists_iff (hl : l.has_basis p s) {P : set α → Prop}
  (mono : ∀ ⦃s t⦄, s ⊆ t → P t → P s) :
  (∃ s ∈ l, P s) ↔ ∃ (i) (hi : p i), P (s i) :=
⟨λ ⟨s, hs, hP⟩, let ⟨i, hi, his⟩ := hl.mem_iff.1 hs in ⟨i, hi, mono his hP⟩,
  λ ⟨i, hi, hP⟩, ⟨s i, hl.mem_of_mem hi, hP⟩⟩

lemma has_basis.forall_iff (hl : l.has_basis p s) {P : set α → Prop}
  (mono : ∀ ⦃s t⦄, s ⊆ t → P s → P t) :
  (∀ s ∈ l, P s) ↔ ∀ i, p i → P (s i) :=
⟨λ H i hi, H (s i) $ hl.mem_of_mem hi,
  λ H s hs, let ⟨i, hi, his⟩ := hl.mem_iff.1 hs in mono his (H i hi)⟩

lemma has_basis.ne_bot_iff (hl : l.has_basis p s) :
  ne_bot l ↔ (∀ {i}, p i → (s i).nonempty) :=
forall_mem_nonempty_iff_ne_bot.symm.trans $ hl.forall_iff $ λ _ _, nonempty.mono

lemma has_basis.eq_bot_iff (hl : l.has_basis p s) :
  l = ⊥ ↔ ∃ i, p i ∧ s i = ∅ :=
not_iff_not.1 $ ne_bot_iff.symm.trans $ hl.ne_bot_iff.trans $
by simp only [not_exists, not_and, ← ne_empty_iff_nonempty]

lemma basis_sets (l : filter α) : l.has_basis (λ s : set α, s ∈ l) id :=
⟨λ t, exists_mem_subset_iff.symm⟩

lemma has_basis_self {l : filter α} {P : set α → Prop} :
  has_basis l (λ s, s ∈ l ∧ P s) id ↔ ∀ t ∈ l, ∃ r ∈ l, P r ∧ r ⊆ t :=
begin
  simp only [has_basis_iff, exists_prop, id, and_assoc],
  exact forall_congr (λ s, ⟨λ h, h.1, λ h, ⟨h, λ ⟨t, hl, hP, hts⟩, mem_of_superset hl hts⟩⟩)
end

/-- If `{s i | p i}` is a basis of a filter `l` and each `s i` includes `s j` such that
`p j ∧ q j`, then `{s j | p j ∧ q j}` is a basis of `l`. -/
lemma has_basis.restrict (h : l.has_basis p s) {q : ι → Prop}
  (hq : ∀ i, p i → ∃ j, p j ∧ q j ∧ s j ⊆ s i) :
  l.has_basis (λ i, p i ∧ q i) s :=
begin
  refine ⟨λ t, ⟨λ ht, _, λ ⟨i, hpi, hti⟩, h.mem_iff.2 ⟨i, hpi.1, hti⟩⟩⟩,
  rcases h.mem_iff.1 ht with ⟨i, hpi, hti⟩,
  rcases hq i hpi with ⟨j, hpj, hqj, hji⟩,
  exact ⟨j, ⟨hpj, hqj⟩, subset.trans hji hti⟩
end

/-- If `{s i | p i}` is a basis of a filter `l` and `V ∈ l`, then `{s i | p i ∧ s i ⊆ V}`
is a basis of `l`. -/
lemma has_basis.restrict_subset (h : l.has_basis p s) {V : set α} (hV : V ∈ l) :
  l.has_basis (λ i, p i ∧ s i ⊆ V) s :=
h.restrict $ λ i hi, (h.mem_iff.1 (inter_mem hV (h.mem_of_mem hi))).imp $
  λ j hj, ⟨hj.fst, subset_inter_iff.1 hj.snd⟩

lemma has_basis.has_basis_self_subset {p : set α → Prop} (h : l.has_basis (λ s, s ∈ l ∧ p s) id)
  {V : set α} (hV : V ∈ l) : l.has_basis (λ s, s ∈ l ∧ p s ∧ s ⊆ V) id :=
by simpa only [and_assoc] using h.restrict_subset hV

theorem has_basis.ge_iff (hl' : l'.has_basis p' s')  : l ≤ l' ↔ ∀ i', p' i' → s' i' ∈ l :=
⟨λ h i' hi', h $ hl'.mem_of_mem hi',
  λ h s hs, let ⟨i', hi', hs⟩ := hl'.mem_iff.1 hs in mem_of_superset (h _ hi') hs⟩

theorem has_basis.le_iff (hl : l.has_basis p s) : l ≤ l' ↔ ∀ t ∈ l', ∃ i (hi : p i), s i ⊆ t :=
by simp only [le_def, hl.mem_iff]

theorem has_basis.le_basis_iff (hl : l.has_basis p s) (hl' : l'.has_basis p' s') :
  l ≤ l' ↔ ∀ i', p' i' → ∃ i (hi : p i), s i ⊆ s' i' :=
by simp only [hl'.ge_iff, hl.mem_iff]

lemma has_basis.ext (hl : l.has_basis p s) (hl' : l'.has_basis p' s')
  (h : ∀ i, p i → ∃ i', p' i' ∧ s' i' ⊆ s i)
  (h' : ∀ i', p' i' → ∃ i, p i ∧ s i ⊆ s' i') : l = l' :=
begin
  apply le_antisymm,
  { rw hl.le_basis_iff hl',
    simpa using h' },
  { rw hl'.le_basis_iff hl,
    simpa using h },
end

lemma has_basis.inf' (hl : l.has_basis p s) (hl' : l'.has_basis p' s') :
  (l ⊓ l').has_basis (λ i : pprod ι ι', p i.1 ∧ p' i.2) (λ i, s i.1 ∩ s' i.2) :=
⟨begin
  intro t,
  split,
  { simp only [mem_inf_iff, exists_prop, hl.mem_iff, hl'.mem_iff],
    rintros ⟨t, ⟨i, hi, ht⟩, t', ⟨i', hi', ht'⟩, rfl⟩,
    use [⟨i, i'⟩, ⟨hi, hi'⟩, inter_subset_inter ht ht'] },
  { rintros ⟨⟨i, i'⟩, ⟨hi, hi'⟩, H⟩,
    exact mem_inf_of_inter (hl.mem_of_mem hi) (hl'.mem_of_mem hi') H }
end⟩

lemma has_basis.inf {ι ι' : Type*} {p : ι → Prop} {s : ι → set α} {p' : ι' → Prop}
  {s' : ι' → set α} (hl : l.has_basis p s) (hl' : l'.has_basis p' s') :
  (l ⊓ l').has_basis (λ i : ι × ι', p i.1 ∧ p' i.2) (λ i, s i.1 ∩ s' i.2) :=
(hl.inf' hl').to_has_basis (λ i hi, ⟨⟨i.1, i.2⟩, hi, subset.rfl⟩)
  (λ i hi, ⟨⟨i.1, i.2⟩, hi, subset.rfl⟩)

lemma has_basis_principal (t : set α) : (𝓟 t).has_basis (λ i : unit, true) (λ i, t) :=
⟨λ U, by simp⟩

lemma has_basis_pure (x : α) : (pure x : filter α).has_basis (λ i : unit, true) (λ i, {x}) :=
by simp only [← principal_singleton, has_basis_principal]

lemma has_basis.sup' (hl : l.has_basis p s) (hl' : l'.has_basis p' s') :
  (l ⊔ l').has_basis (λ i : pprod ι ι', p i.1 ∧ p' i.2) (λ i, s i.1 ∪ s' i.2) :=
⟨begin
  intros t,
  simp only [mem_sup, hl.mem_iff, hl'.mem_iff, pprod.exists, union_subset_iff, exists_prop,
    and_assoc, exists_and_distrib_left],
  simp only [← and_assoc, exists_and_distrib_right, and_comm]
end⟩

lemma has_basis.sup {ι ι' : Type*} {p : ι → Prop} {s : ι → set α} {p' : ι' → Prop}
  {s' : ι' → set α} (hl : l.has_basis p s) (hl' : l'.has_basis p' s') :
  (l ⊔ l').has_basis (λ i : ι × ι', p i.1 ∧ p' i.2) (λ i, s i.1 ∪ s' i.2) :=
(hl.sup' hl').to_has_basis (λ i hi, ⟨⟨i.1, i.2⟩, hi, subset.rfl⟩)
  (λ i hi, ⟨⟨i.1, i.2⟩, hi, subset.rfl⟩)

lemma has_basis_supr {ι : Sort*} {ι' : ι → Type*} {l : ι → filter α}
  {p : Π i, ι' i → Prop} {s : Π i, ι' i → set α} (hl : ∀ i, (l i).has_basis (p i) (s i)) :
  (⨆ i, l i).has_basis (λ f : Π i, ι' i, ∀ i, p i (f i)) (λ f : Π i, ι' i, ⋃ i, s i (f i)) :=
has_basis_iff.mpr $ λ t, by simp only [has_basis_iff, (hl _).mem_iff, classical.skolem,
  forall_and_distrib, Union_subset_iff, mem_supr]

lemma has_basis.sup_principal (hl : l.has_basis p s) (t : set α) :
  (l ⊔ 𝓟 t).has_basis p (λ i, s i ∪ t) :=
⟨λ u, by simp only [(hl.sup' (has_basis_principal t)).mem_iff, pprod.exists, exists_prop, and_true,
  unique.exists_iff]⟩

lemma has_basis.sup_pure (hl : l.has_basis p s) (x : α) :
  (l ⊔ pure x).has_basis p (λ i, s i ∪ {x}) :=
by simp only [← principal_singleton, hl.sup_principal]

lemma has_basis.inf_principal (hl : l.has_basis p s) (s' : set α) :
  (l ⊓ 𝓟 s').has_basis p (λ i, s i ∩ s') :=
⟨λ t, by simp only [mem_inf_principal, hl.mem_iff, subset_def, mem_set_of_eq,
  mem_inter_iff, and_imp]⟩

lemma has_basis.inf_basis_ne_bot_iff (hl : l.has_basis p s) (hl' : l'.has_basis p' s') :
  ne_bot (l ⊓ l') ↔ ∀ ⦃i⦄ (hi : p i) ⦃i'⦄ (hi' : p' i'), (s i ∩ s' i').nonempty :=
(hl.inf' hl').ne_bot_iff.trans $ by simp [@forall_swap _ ι']

lemma has_basis.inf_ne_bot_iff (hl : l.has_basis p s) :
  ne_bot (l ⊓ l') ↔ ∀ ⦃i⦄ (hi : p i) ⦃s'⦄ (hs' : s' ∈ l'), (s i ∩ s').nonempty :=
hl.inf_basis_ne_bot_iff l'.basis_sets

lemma has_basis.inf_principal_ne_bot_iff (hl : l.has_basis p s) {t : set α} :
  ne_bot (l ⊓ 𝓟 t) ↔ ∀ ⦃i⦄ (hi : p i), (s i ∩ t).nonempty :=
(hl.inf_principal t).ne_bot_iff

lemma inf_ne_bot_iff :
  ne_bot (l ⊓ l') ↔ ∀ ⦃s : set α⦄ (hs : s ∈ l) ⦃s'⦄ (hs' : s' ∈ l'), (s ∩ s').nonempty :=
l.basis_sets.inf_ne_bot_iff

lemma inf_principal_ne_bot_iff {s : set α} :
  ne_bot (l ⊓ 𝓟 s) ↔ ∀ U ∈ l, (U ∩ s).nonempty :=
l.basis_sets.inf_principal_ne_bot_iff

lemma inf_eq_bot_iff {f g : filter α} :
  f ⊓ g = ⊥ ↔ ∃ (U ∈ f) (V ∈ g), U ∩ V = ∅ :=
not_iff_not.1 $ ne_bot_iff.symm.trans $ inf_ne_bot_iff.trans $
by simp [← ne_empty_iff_nonempty]

protected lemma disjoint_iff {f g : filter α} :
  disjoint f g ↔ ∃ (U ∈ f) (V ∈ g), U ∩ V = ∅ :=
disjoint_iff.trans inf_eq_bot_iff

lemma mem_iff_inf_principal_compl {f : filter α} {s : set α} :
  s ∈ f ↔ f ⊓ 𝓟 sᶜ = ⊥ :=
begin
  refine not_iff_not.1 ((inf_principal_ne_bot_iff.trans _).symm.trans ne_bot_iff),
  exact ⟨λ h hs, by simpa [empty_not_nonempty] using h s hs,
    λ hs t ht, inter_compl_nonempty_iff.2 $ λ hts, hs $ mem_of_superset ht hts⟩,
end

lemma not_mem_iff_inf_principal_compl {f : filter α} {s : set α} :
  s ∉ f ↔ ne_bot (f ⊓ 𝓟 sᶜ) :=
(not_congr mem_iff_inf_principal_compl).trans ne_bot_iff.symm

lemma mem_iff_disjoint_principal_compl {f : filter α} {s : set α} :
  s ∈ f ↔ disjoint f (𝓟 sᶜ) :=
mem_iff_inf_principal_compl.trans disjoint_iff.symm

lemma le_iff_forall_disjoint_principal_compl {f g : filter α} :
  f ≤ g ↔ ∀ V ∈ g, disjoint f (𝓟 Vᶜ) :=
forall_congr $ λ _, forall_congr $ λ _, mem_iff_disjoint_principal_compl

lemma le_iff_forall_inf_principal_compl {f g : filter α} :
  f ≤ g ↔ ∀ V ∈ g, f ⊓ 𝓟 Vᶜ = ⊥ :=
forall_congr $ λ _, forall_congr $ λ _, mem_iff_inf_principal_compl

lemma inf_ne_bot_iff_frequently_left {f g : filter α} :
  ne_bot (f ⊓ g) ↔ ∀ {p : α → Prop}, (∀ᶠ x in f, p x) → ∃ᶠ x in g, p x :=
by simpa only [inf_ne_bot_iff, frequently_iff, exists_prop, and_comm]

lemma inf_ne_bot_iff_frequently_right {f g : filter α} :
  ne_bot (f ⊓ g) ↔ ∀ {p : α → Prop}, (∀ᶠ x in g, p x) → ∃ᶠ x in f, p x :=
by { rw inf_comm, exact inf_ne_bot_iff_frequently_left }

lemma has_basis.eq_binfi (h : l.has_basis p s) :
  l = ⨅ i (_ : p i), 𝓟 (s i) :=
eq_binfi_of_mem_iff_exists_mem $ λ t, by simp only [h.mem_iff, mem_principal]

lemma has_basis.eq_infi (h : l.has_basis (λ _, true) s) :
  l = ⨅ i, 𝓟 (s i) :=
by simpa only [infi_true] using h.eq_binfi

lemma has_basis_infi_principal {s : ι → set α} (h : directed (≥) s) [nonempty ι] :
  (⨅ i, 𝓟 (s i)).has_basis (λ _, true) s :=
⟨begin
  refine λ t, (mem_infi_of_directed (h.mono_comp _ _) t).trans $
    by simp only [exists_prop, true_and, mem_principal],
  exact λ _ _, principal_mono.2
end⟩

/-- If `s : ι → set α` is an indexed family of sets, then finite intersections of `s i` form a basis
of `⨅ i, 𝓟 (s i)`.  -/
lemma has_basis_infi_principal_finite {ι : Type*} (s : ι → set α) :
  (⨅ i, 𝓟 (s i)).has_basis (λ t : set ι, finite t) (λ t, ⋂ i ∈ t, s i) :=
begin
  refine ⟨λ U, (mem_infi_finite _).trans _⟩,
  simp only [infi_principal_finset, mem_Union, mem_principal, exists_prop,
    exists_finite_iff_finset, finset.set_bInter_coe]
end

lemma has_basis_binfi_principal {s : β → set α} {S : set β} (h : directed_on (s ⁻¹'o (≥)) S)
  (ne : S.nonempty) :
  (⨅ i ∈ S, 𝓟 (s i)).has_basis (λ i, i ∈ S) s :=
⟨begin
  refine λ t, (mem_binfi_of_directed _ ne).trans $ by simp only [mem_principal],
  rw [directed_on_iff_directed, ← directed_comp, (∘)] at h ⊢,
  apply h.mono_comp _ _,
  exact λ _ _, principal_mono.2
end⟩

lemma has_basis_binfi_principal' {ι : Type*} {p : ι → Prop} {s : ι → set α}
  (h : ∀ i, p i → ∀ j, p j → ∃ k (h : p k), s k ⊆ s i ∧ s k ⊆ s j) (ne : ∃ i, p i) :
  (⨅ i (h : p i), 𝓟 (s i)).has_basis p s :=
filter.has_basis_binfi_principal h ne

lemma has_basis.map (f : α → β) (hl : l.has_basis p s) :
  (l.map f).has_basis p (λ i, f '' (s i)) :=
⟨λ t, by simp only [mem_map, image_subset_iff, hl.mem_iff, preimage]⟩

lemma has_basis.comap (f : β → α) (hl : l.has_basis p s) :
  (l.comap f).has_basis p (λ i, f ⁻¹' (s i)) :=
⟨begin
  intro t,
  simp only [mem_comap, exists_prop, hl.mem_iff],
  split,
  { rintros ⟨t', ⟨i, hi, ht'⟩, H⟩,
    exact ⟨i, hi, subset.trans (preimage_mono ht') H⟩ },
  { rintros ⟨i, hi, H⟩,
    exact ⟨s i, ⟨i, hi, subset.refl _⟩, H⟩ }
end⟩

lemma comap_has_basis (f : α → β) (l : filter β) :
  has_basis (comap f l) (λ s : set β, s ∈ l) (λ s, f ⁻¹' s) :=
⟨λ t, mem_comap⟩

lemma has_basis.prod_self (hl : l.has_basis p s) :
  (l ×ᶠ l).has_basis p (λ i, (s i).prod (s i)) :=
⟨begin
  intro t,
  apply mem_prod_iff.trans,
  split,
  { rintros ⟨t₁, ht₁, t₂, ht₂, H⟩,
    rcases hl.mem_iff.1 (inter_mem ht₁ ht₂) with ⟨i, hi, ht⟩,
    exact ⟨i, hi, λ p ⟨hp₁, hp₂⟩, H ⟨(ht hp₁).1, (ht hp₂).2⟩⟩ },
  { rintros ⟨i, hi, H⟩,
    exact ⟨s i, hl.mem_of_mem hi, s i, hl.mem_of_mem hi, H⟩ }
end⟩

lemma mem_prod_self_iff {s} : s ∈ l ×ᶠ l ↔ ∃ t ∈ l, set.prod t t ⊆ s :=
l.basis_sets.prod_self.mem_iff

lemma has_basis.sInter_sets (h : has_basis l p s) :
  ⋂₀ l.sets = ⋂ i (hi : p i), s i :=
begin
  ext x,
  suffices : (∀ t ∈ l, x ∈ t) ↔ ∀ i, p i → x ∈ s i,
    by simpa only [mem_Inter, mem_set_of_eq, mem_sInter],
  simp_rw h.mem_iff,
  split,
  { intros h i hi,
    exact h (s i) ⟨i, hi, subset.refl _⟩ },
  { rintros h _ ⟨i, hi, sub⟩,
    exact sub (h i hi) },
end

variables {ι'' : Type*} [preorder ι''] (l) (s'' : ι'' → set α)

/-- `is_antitone_basis s` means the image of `s` is a filter basis such that `s` is decreasing. -/
@[protect_proj] structure is_antitone_basis extends is_basis (λ _, true) s'' : Prop :=
(antitone : antitone s'')

/-- We say that a filter `l` has an antitone basis `s : ι → set α`, if `t ∈ l` if and only if `t`
includes `s i` for some `i`, and `s` is decreasing. -/
@[protect_proj] structure has_antitone_basis (l : filter α) (s : ι'' → set α)
  extends has_basis l (λ _, true) s : Prop :=
(antitone : antitone s)

end same_type

section two_types

variables {la : filter α} {pa : ι → Prop} {sa : ι → set α}
  {lb : filter β} {pb : ι' → Prop} {sb : ι' → set β} {f : α → β}

lemma has_basis.tendsto_left_iff (hla : la.has_basis pa sa) :
  tendsto f la lb ↔ ∀ t ∈ lb, ∃ i (hi : pa i), maps_to f (sa i) t :=
by { simp only [tendsto, (hla.map f).le_iff, image_subset_iff], refl }

lemma has_basis.tendsto_right_iff (hlb : lb.has_basis pb sb) :
  tendsto f la lb ↔ ∀ i (hi : pb i), ∀ᶠ x in la, f x ∈ sb i :=
by simpa only [tendsto, hlb.ge_iff, mem_map, filter.eventually]

lemma has_basis.tendsto_iff (hla : la.has_basis pa sa) (hlb : lb.has_basis pb sb) :
  tendsto f la lb ↔ ∀ ib (hib : pb ib), ∃ ia (hia : pa ia), ∀ x ∈ sa ia, f x ∈ sb ib :=
by simp [hlb.tendsto_right_iff, hla.eventually_iff]

lemma tendsto.basis_left (H : tendsto f la lb) (hla : la.has_basis pa sa) :
  ∀ t ∈ lb, ∃ i (hi : pa i), maps_to f (sa i) t :=
hla.tendsto_left_iff.1 H

lemma tendsto.basis_right (H : tendsto f la lb) (hlb : lb.has_basis pb sb) :
  ∀ i (hi : pb i), ∀ᶠ x in la, f x ∈ sb i :=
hlb.tendsto_right_iff.1 H

lemma tendsto.basis_both (H : tendsto f la lb) (hla : la.has_basis pa sa)
  (hlb : lb.has_basis pb sb) :
  ∀ ib (hib : pb ib), ∃ ia (hia : pa ia), ∀ x ∈ sa ia, f x ∈ sb ib :=
(hla.tendsto_iff hlb).1 H

lemma has_basis.prod'' (hla : la.has_basis pa sa) (hlb : lb.has_basis pb sb) :
  (la ×ᶠ lb).has_basis (λ i : pprod ι ι', pa i.1 ∧ pb i.2) (λ i, (sa i.1).prod (sb i.2)) :=
(hla.comap prod.fst).inf' (hlb.comap prod.snd)

lemma has_basis.prod {ι ι' : Type*} {pa : ι → Prop} {sa : ι → set α} {pb : ι' → Prop}
  {sb : ι' → set β} (hla : la.has_basis pa sa) (hlb : lb.has_basis pb sb) :
  (la ×ᶠ lb).has_basis (λ i : ι × ι', pa i.1 ∧ pb i.2) (λ i, (sa i.1).prod (sb i.2)) :=
(hla.comap prod.fst).inf (hlb.comap prod.snd)

lemma has_basis.prod' {la : filter α} {lb : filter β} {ι : Type*} {p : ι → Prop}
  {sa : ι → set α} {sb : ι → set β}
  (hla : la.has_basis p sa) (hlb : lb.has_basis p sb)
  (h_dir : ∀ {i j}, p i → p j → ∃ k, p k ∧ sa k ⊆ sa i ∧ sb k ⊆ sb j) :
  (la ×ᶠ lb).has_basis p (λ i, (sa i).prod (sb i)) :=
begin
  simp only [has_basis_iff, (hla.prod hlb).mem_iff],
  refine λ t, ⟨_, _⟩,
  { rintros ⟨⟨i, j⟩, ⟨hi, hj⟩, hsub : (sa i).prod (sb j) ⊆ t⟩,
    rcases h_dir hi hj with ⟨k, hk, ki, kj⟩,
    exact ⟨k, hk, (set.prod_mono ki kj).trans hsub⟩ },
  { rintro ⟨i, hi, h⟩,
    exact ⟨⟨i, i⟩, ⟨hi, hi⟩, h⟩ },
end

end two_types

end filter

end sort

namespace filter

variables {α β γ ι ι' : Type*}

/-- `is_countably_generated f` means `f = generate s` for some countable `s`. -/
class is_countably_generated (f : filter α) : Prop :=
(out [] : ∃ s : set (set α), countable s ∧ f = generate s)

/-- `is_countable_basis p s` means the image of `s` bounded by `p` is a countable filter basis. -/
structure is_countable_basis (p : ι → Prop) (s : ι → set α) extends is_basis p s : Prop :=
(countable : countable $ set_of p)

/-- We say that a filter `l` has a countable basis `s : ι → set α` bounded by `p : ι → Prop`,
if `t ∈ l` if and only if `t` includes `s i` for some `i` such that `p i`, and the set
defined by `p` is countable. -/
structure has_countable_basis (l : filter α) (p : ι → Prop) (s : ι → set α)
  extends has_basis l p s : Prop :=
(countable : countable $ set_of p)

/-- A countable filter basis `B` on a type `α` is a nonempty countable collection of sets of `α`
such that the intersection of two elements of this collection contains some element
of the collection. -/
structure countable_filter_basis (α : Type*) extends filter_basis α :=
(countable : countable sets)

-- For illustration purposes, the countable filter basis defining (at_top : filter ℕ)
instance nat.inhabited_countable_filter_basis : inhabited (countable_filter_basis ℕ) :=
⟨{ countable := countable_range (λ n, Ici n),
   ..(default $ filter_basis ℕ),}⟩

lemma has_countable_basis.is_countably_generated {f : filter α} {p : ι → Prop} {s : ι → set α}
  (h : f.has_countable_basis p s) :
  f.is_countably_generated :=
⟨⟨{t | ∃ i, p i ∧ s i = t}, h.countable.image s, h.to_has_basis.eq_generate⟩⟩

lemma antitone_seq_of_seq (s : ℕ → set α) :
  ∃ t : ℕ → set α, antitone t ∧ (⨅ i, 𝓟 $ s i) = ⨅ i, 𝓟 (t i) :=
begin
  use λ n, ⋂ m ≤ n, s m, split,
  { exact λ i j hij, bInter_mono' (Iic_subset_Iic.2 hij) (λ n hn, subset.refl _) },
  apply le_antisymm; rw le_infi_iff; intro i,
  { rw le_principal_iff, refine (bInter_mem (finite_le_nat _)).2 (λ j hji, _),
    rw ← le_principal_iff, apply infi_le_of_le j _, apply le_refl _ },
  { apply infi_le_of_le i _, rw principal_mono, intro a, simp, intro h, apply h, refl },
end

lemma countable_binfi_eq_infi_seq [complete_lattice α] {B : set ι} (Bcbl : countable B)
  (Bne : B.nonempty) (f : ι → α) :
  ∃ (x : ℕ → ι), (⨅ t ∈ B, f t) = ⨅ i, f (x i) :=
begin
  rw countable_iff_exists_surjective_to_subtype Bne at Bcbl,
  rcases Bcbl with ⟨g, gsurj⟩,
  rw infi_subtype',
  use (λ n, g n), apply le_antisymm; rw le_infi_iff,
  { intro i, apply infi_le_of_le (g i) _, apply le_refl _ },
  { intros a, rcases gsurj a with ⟨i, rfl⟩, apply infi_le }
end

lemma countable_binfi_eq_infi_seq' [complete_lattice α] {B : set ι} (Bcbl : countable B) (f : ι → α)
  {i₀ : ι} (h : f i₀ = ⊤) :
  ∃ (x : ℕ → ι), (⨅ t ∈ B, f t) = ⨅ i, f (x i) :=
begin
  cases B.eq_empty_or_nonempty with hB Bnonempty,
  { rw [hB, infi_emptyset],
    use λ n, i₀,
    simp [h] },
  { exact countable_binfi_eq_infi_seq Bcbl Bnonempty f }
end

lemma countable_binfi_principal_eq_seq_infi {B : set (set α)} (Bcbl : countable B) :
  ∃ (x : ℕ → set α), (⨅ t ∈ B, 𝓟 t) = ⨅ i, 𝓟 (x i) :=
countable_binfi_eq_infi_seq' Bcbl 𝓟 principal_univ

section is_countably_generated

/-- If `f` is countably generated and `f.has_basis p s`, then `f` admits a decreasing basis
enumerated by natural numbers such that all sets have the form `s i`. More precisely, there is a
sequence `i n` such that `p (i n)` for all `n` and `s (i n)` is a decreasing sequence of sets which
forms a basis of `f`-/
lemma has_basis.exists_antitone_subbasis {f : filter α} [h : f.is_countably_generated]
  {p : ι → Prop} {s : ι → set α} (hs : f.has_basis p s) :
  ∃ x : ℕ → ι, (∀ i, p (x i)) ∧ f.has_antitone_basis (λ i, s (x i)) :=
begin
  obtain ⟨x', hx'⟩ : ∃ x : ℕ → set α, f = ⨅ i, 𝓟 (x i),
  { unfreezingI { rcases h with ⟨s, hsc, rfl⟩ },
    rw generate_eq_binfi,
    exact countable_binfi_principal_eq_seq_infi hsc },
  have : ∀ i, x' i ∈ f := λ i, hx'.symm ▸ (infi_le (λ i, 𝓟 (x' i)) i) (mem_principal_self _),
  let x : ℕ → {i : ι // p i} := λ n, nat.rec_on n (hs.index _ $ this 0)
    (λ n xn, (hs.index _ $ inter_mem (this $ n + 1) (hs.mem_of_mem xn.coe_prop))),
  have x_mono : antitone (λ i, s (x i)),
  { refine antitone_nat_of_succ_le (λ i, _),
    exact (hs.set_index_subset _).trans (inter_subset_right _ _) },
  have x_subset : ∀ i, s (x i) ⊆ x' i,
  { rintro (_|i),
    exacts [hs.set_index_subset _, subset.trans (hs.set_index_subset _) (inter_subset_left _ _)] },
  refine ⟨λ i, x i, λ i, (x i).2, _⟩,
  have : (⨅ i, 𝓟 (s (x i))).has_antitone_basis (λ i, s (x i)) :=
    ⟨has_basis_infi_principal (directed_of_sup x_mono), x_mono⟩,
  convert this,
  exact le_antisymm (le_infi $ λ i, le_principal_iff.2 $ by cases i; apply hs.set_index_mem)
    (hx'.symm ▸ le_infi (λ i, le_principal_iff.2 $
      this.to_has_basis.mem_iff.2 ⟨i, trivial, x_subset i⟩))
end

/-- A countably generated filter admits a basis formed by an antitone sequence of sets. -/
lemma exists_antitone_basis (f : filter α) [f.is_countably_generated] :
  ∃ x : ℕ → set α, f.has_antitone_basis x :=
let ⟨x, hxf, hx⟩ := f.basis_sets.exists_antitone_subbasis in ⟨x, hx⟩

lemma exists_antitone_seq (f : filter α) [f.is_countably_generated] :
  ∃ x : ℕ → set α, antitone x ∧ ∀ {s}, (s ∈ f ↔ ∃ i, x i ⊆ s) :=
let ⟨x, hx⟩ := f.exists_antitone_basis in
⟨x, hx.antitone, λ s, by simp [hx.to_has_basis.mem_iff]⟩

instance inf.is_countably_generated (f g : filter α) [is_countably_generated f]
  [is_countably_generated g] :
  is_countably_generated (f ⊓ g) :=
begin
  rcases f.exists_antitone_basis with ⟨s, hs⟩,
  rcases g.exists_antitone_basis with ⟨t, ht⟩,
  exact has_countable_basis.is_countably_generated
    ⟨hs.to_has_basis.inf ht.to_has_basis, set.countable_encodable _⟩
end

instance comap.is_countably_generated (l : filter β) [l.is_countably_generated] (f : α → β) :
  (comap f l).is_countably_generated :=
let ⟨x, hxl⟩ := l.exists_antitone_basis in
has_countable_basis.is_countably_generated ⟨hxl.to_has_basis.comap _, countable_encodable _⟩

instance sup.is_countably_generated (f g : filter α) [is_countably_generated f]
  [is_countably_generated g] :
  is_countably_generated (f ⊔ g) :=
begin
  rcases f.exists_antitone_basis with ⟨s, hs⟩,
  rcases g.exists_antitone_basis with ⟨t, ht⟩,
  exact has_countable_basis.is_countably_generated
    ⟨hs.to_has_basis.sup ht.to_has_basis, set.countable_encodable _⟩
end

end is_countably_generated

@[instance] lemma is_countably_generated_seq [encodable β] (x : β → set α) :
  is_countably_generated (⨅ i, 𝓟 $ x i) :=
begin
  use [range x, countable_range x],
  rw [generate_eq_binfi, infi_range]
end

lemma is_countably_generated_of_seq {f : filter α} (h : ∃ x : ℕ → set α, f = ⨅ i, 𝓟 $ x i) :
  f.is_countably_generated  :=
let ⟨x, h⟩ := h in by rw h ; apply is_countably_generated_seq

lemma is_countably_generated_binfi_principal {B : set $ set α} (h : countable B) :
  is_countably_generated (⨅ (s ∈ B), 𝓟 s) :=
is_countably_generated_of_seq (countable_binfi_principal_eq_seq_infi h)

lemma is_countably_generated_iff_exists_antitone_basis {f : filter α} :
  is_countably_generated f ↔ ∃ x : ℕ → set α, f.has_antitone_basis x :=
begin
  split,
  { introI h, exact f.exists_antitone_basis },
  { rintros ⟨x, h⟩,
    rw h.to_has_basis.eq_infi,
    exact is_countably_generated_seq x },
end

@[instance] lemma is_countably_generated_principal (s : set α) : is_countably_generated (𝓟 s) :=
is_countably_generated_of_seq ⟨λ _, s, infi_const.symm⟩

@[instance] lemma is_countably_generated_bot : is_countably_generated (⊥ : filter α) :=
@principal_empty α ▸ is_countably_generated_principal _

@[instance] lemma is_countably_generated_top : is_countably_generated (⊤ : filter α) :=
@principal_univ α ▸ is_countably_generated_principal _

end filter
