/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury Kudryashov, Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import order.filter.at_top_bot
import data.set.countable

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

This file also introduces more restricted classes of bases, involving monotonicity or
countability. In particular, for `l : filter α`, `l.is_countably_generated` means
there is a countable set of sets which generates `s`. This is reformulated in term of bases,
and consequences are derived.

## Main statements

* `has_basis.mem_iff`, `has_basis.mem_of_superset`, `has_basis.mem_of_mem` : restate `t ∈ f` in terms
  of a basis;
* `basis_sets` : all sets of a filter form a basis;
* `has_basis.inf`, `has_basis.inf_principal`, `has_basis.prod`, `has_basis.prod_self`,
  `has_basis.map`, `has_basis.comap` : combinators to construct filters of `l ⊓ l'`,
  `l ⊓ 𝓟 t`, `l.prod l'`, `l.prod l`, `l.map f`, `l.comap f` respectively;
* `has_basis.le_iff`, `has_basis.ge_iff`, has_basis.le_basis_iff` : restate `l ≤ l'` in terms
  of bases.
* `has_basis.tendsto_right_iff`, `has_basis.tendsto_left_iff`, `has_basis.tendsto_iff` : restate
  `tendsto f l l'` in terms of bases.
* `is_countably_generated_iff_exists_antimono_basis` : proves a filter is
  countably generated if and only if it admis a basis parametrized by a
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
open_locale filter

variables {α : Type*} {β : Type*} {γ : Type*} {ι : Type*} {ι' : Type*}

/-- A filter basis `B` on a type `α` is a nonempty collection of sets of `α`
such that the intersection of two elements of this collection contains some element
of the collection. -/
structure filter_basis (α : Type*) :=
(sets                   : set (set α))
(nonempty               : sets.nonempty)
(inter_sets {x y}       : x ∈ sets → y ∈ sets → ∃ z ∈ sets, z ⊆ x ∩ y)

/-- If `B` is a filter basis on `α`, and `U` a subset of `α` then we can write `U ∈ B` as on paper. -/
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
{ sets := s '' set_of p,
  nonempty := let ⟨i, hi⟩ := h.nonempty in ⟨s i, mem_image_of_mem s hi⟩,
  inter_sets := by { rintros _ _ ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩,
                     rcases h.inter hi hj with ⟨k, hk, hk'⟩,
                     exact ⟨_, mem_image_of_mem s hk, hk'⟩ } }

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
  ext U,
  rw [mem_filter_iff, mem_infi],
  { simp },
  { rintros ⟨U, U_in⟩ ⟨V, V_in⟩,
    rcases B.inter_sets U_in V_in with ⟨W, W_in, W_sub⟩,
    use [W, W_in],
    finish },
  cases B.nonempty with U U_in,
  exact ⟨⟨U, U_in⟩⟩,
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

lemma has_basis_generate (s : set (set α)) : (generate s).has_basis (λ t, finite t ∧ t ⊆ s) (λ t, ⋂₀ t) :=
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

protected lemma is_basis.has_basis (h : is_basis p s) : has_basis h.filter p s :=
⟨λ t, by simp only [h.mem_filter_iff, exists_prop]⟩

lemma has_basis.mem_of_superset (hl : l.has_basis p s) (hi : p i) (ht : s i ⊆ t) : t ∈ l :=
(hl.mem_iff).2 ⟨i, hi, ht⟩

lemma has_basis.mem_of_mem (hl : l.has_basis p s) (hi : p i) : s i ∈ l :=
hl.mem_of_superset hi $ subset.refl _

lemma has_basis.is_basis (h : l.has_basis p s) : is_basis p s :=
{ nonempty := let ⟨i, hi, H⟩ := h.mem_iff.mp univ_mem_sets in ⟨i, hi⟩,
  inter := λ i j hi hj, by simpa [h.mem_iff] using l.inter_sets (h.mem_of_mem hi) (h.mem_of_mem hj) }

lemma has_basis.filter_eq (h : l.has_basis p s) : h.is_basis.filter = l :=
by { ext U, simp [h.mem_iff, is_basis.mem_filter_iff] }

lemma has_basis.eq_generate (h : l.has_basis p s) : l = generate { U | ∃ i, p i ∧ s i = U } :=
by rw [← h.is_basis.filter_eq_generate, h.filter_eq]

lemma generate_eq_generate_inter (s : set (set α)) : generate s = generate (sInter '' { t | finite t ∧ t ⊆ s}) :=
by erw [(filter_basis.of_sets s).generate, ← (has_basis_generate s).filter_eq] ; refl

lemma of_sets_filter_eq_generate (s : set (set α)) : (filter_basis.of_sets s).filter = generate s :=
by rw [← (filter_basis.of_sets s).generate, generate_eq_generate_inter s] ; refl

lemma has_basis.eventually_iff (hl : l.has_basis p s) {q : α → Prop} :
  (∀ᶠ x in l, q x) ↔ ∃ i, p i ∧ ∀ ⦃x⦄, x ∈ s i → q x :=
by simpa using hl.mem_iff

lemma has_basis.forall_nonempty_iff_ne_bot (hl : l.has_basis p s) :
  (∀ {i}, p i → (s i).nonempty) ↔ ne_bot l :=
⟨λ H, forall_sets_nonempty_iff_ne_bot.1 $
  λ s hs, let ⟨i, hi, his⟩ := hl.mem_iff.1 hs in (H hi).mono his,
  λ H i hi, H.nonempty_of_mem (hl.mem_of_mem hi)⟩

lemma basis_sets (l : filter α) : l.has_basis (λ s : set α, s ∈ l) id :=
⟨λ t, exists_sets_subset_iff.symm⟩

lemma has_basis_self {l : filter α} {P : set α → Prop} :
  has_basis l (λ s, s ∈ l ∧ P s) id ↔ ∀ t, (t ∈ l ↔ ∃ r ∈ l, P r ∧ r ⊆ t) :=
begin
  split,
  { rintros ⟨h⟩ t,
    convert h t,
    ext s,
    tauto, },
  { intro h,
    constructor,
    intro t,
    convert h t,
    ext s,
    tauto }
end

lemma at_top_basis [nonempty α] [semilattice_sup α] :
  (@at_top α _).has_basis (λ _, true) Ici :=
⟨λ t, by simpa only [exists_prop, true_and] using @mem_at_top_sets α _ _ t⟩

lemma at_top_basis' [semilattice_sup α] (a : α) :
  (@at_top α _).has_basis (λ x, a ≤ x) Ici :=
⟨λ t, (@at_top_basis α ⟨a⟩ _).mem_iff.trans
  ⟨λ ⟨x, _, hx⟩, ⟨x ⊔ a, le_sup_right, λ y hy, hx (le_trans le_sup_left hy)⟩,
    λ ⟨x, _, hx⟩, ⟨x, trivial, hx⟩⟩⟩

theorem has_basis.ge_iff (hl' : l'.has_basis p' s')  : l ≤ l' ↔ ∀ i', p' i' → s' i' ∈ l :=
⟨λ h i' hi', h $ hl'.mem_of_mem hi',
  λ h s hs, let ⟨i', hi', hs⟩ := hl'.mem_iff.1 hs in mem_sets_of_superset (h _ hi') hs⟩

theorem has_basis.le_iff (hl : l.has_basis p s) : l ≤ l' ↔ ∀ t ∈ l', ∃ i (hi : p i), s i ⊆ t :=
by simp only [le_def, hl.mem_iff]

theorem has_basis.le_basis_iff (hl : l.has_basis p s) (hl' : l'.has_basis p' s') :
  l ≤ l' ↔ ∀ i', p' i' → ∃ i (hi : p i), s i ⊆ s' i' :=
by simp only [hl'.ge_iff, hl.mem_iff]

lemma has_basis.inf (hl : l.has_basis p s) (hl' : l'.has_basis p' s') :
  (l ⊓ l').has_basis (λ i : ι × ι', p i.1 ∧ p' i.2) (λ i, s i.1 ∩ s' i.2) :=
⟨begin
  intro t,
  simp only [mem_inf_sets, exists_prop, hl.mem_iff, hl'.mem_iff],
  split,
  { rintros ⟨t, ⟨i, hi, ht⟩, t', ⟨i', hi', ht'⟩, H⟩,
    use [(i, i'), ⟨hi, hi'⟩, subset.trans (inter_subset_inter ht ht') H] },
  { rintros ⟨⟨i, i'⟩, ⟨hi, hi'⟩, H⟩,
    use [s i, i, hi, subset.refl _, s' i', i', hi', subset.refl _, H] }
end⟩

lemma has_basis.inf_principal (hl : l.has_basis p s) (s' : set α) :
  (l ⊓ 𝓟 s').has_basis p (λ i, s i ∩ s') :=
⟨λ t, by simp only [mem_inf_principal, hl.mem_iff, subset_def, mem_set_of_eq,
  mem_inter_iff, and_imp]⟩

lemma has_basis.eq_binfi (h : l.has_basis p s) :
  l = ⨅ i (_ : p i), 𝓟 (s i) :=
eq_binfi_of_mem_sets_iff_exists_mem $ λ t, by simp only [h.mem_iff, mem_principal_sets]

lemma has_basis.eq_infi (h : l.has_basis (λ _, true) s) :
  l = ⨅ i, 𝓟 (s i) :=
by simpa only [infi_true] using h.eq_binfi

@[nolint ge_or_gt] -- see Note [nolint_ge]
lemma has_basis_infi_principal {s : ι → set α} (h : directed (≥) s) (ne : nonempty ι) :
  (⨅ i, 𝓟 (s i)).has_basis (λ _, true) s :=
⟨begin
  refine λ t, (mem_infi (h.mono_comp _ _) ne t).trans $
    by simp only [exists_prop, true_and, mem_principal_sets],
  exact λ _ _, principal_mono.2
end⟩

@[nolint ge_or_gt] -- see Note [nolint_ge]
lemma has_basis_binfi_principal {s : β → set α} {S : set β} (h : directed_on (s ⁻¹'o (≥)) S)
  (ne : S.nonempty) :
  (⨅ i ∈ S, 𝓟 (s i)).has_basis (λ i, i ∈ S) s :=
⟨begin
  refine λ t, (mem_binfi _ ne).trans $ by simp only [mem_principal_sets],
  rw [directed_on_iff_directed, ← directed_comp, (∘)] at h ⊢,
  apply h.mono_comp _ _,
  exact λ _ _, principal_mono.2
end⟩

lemma has_basis.map (f : α → β) (hl : l.has_basis p s) :
  (l.map f).has_basis p (λ i, f '' (s i)) :=
⟨λ t, by simp only [mem_map, image_subset_iff, hl.mem_iff, preimage]⟩

lemma has_basis.comap (f : β → α) (hl : l.has_basis p s) :
  (l.comap f).has_basis p (λ i, f ⁻¹' (s i)) :=
⟨begin
  intro t,
  simp only [mem_comap_sets, exists_prop, hl.mem_iff],
  split,
  { rintros ⟨t', ⟨i, hi, ht'⟩, H⟩,
    exact ⟨i, hi, subset.trans (preimage_mono ht') H⟩ },
  { rintros ⟨i, hi, H⟩,
    exact ⟨s i, ⟨i, hi, subset.refl _⟩, H⟩ }
end⟩

lemma comap_has_basis (f : α → β) (l : filter β) :
  has_basis (comap f l) (λ s : set β, s ∈ l) (λ s, f ⁻¹' s) :=
⟨λ t, mem_comap_sets⟩

lemma has_basis.prod_self (hl : l.has_basis p s) :
  (l.prod l).has_basis p (λ i, (s i).prod (s i)) :=
⟨begin
  intro t,
  apply mem_prod_iff.trans,
  split,
  { rintros ⟨t₁, ht₁, t₂, ht₂, H⟩,
    rcases hl.mem_iff.1 (inter_mem_sets ht₁ ht₂) with ⟨i, hi, ht⟩,
    exact ⟨i, hi, λ p ⟨hp₁, hp₂⟩, H ⟨(ht hp₁).1, (ht hp₂).2⟩⟩ },
  { rintros ⟨i, hi, H⟩,
    exact ⟨s i, hl.mem_of_mem hi, s i, hl.mem_of_mem hi, H⟩ }
end⟩

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

lemma has_basis.sInter_sets (h : has_basis l p s) :
  ⋂₀ l.sets = ⋂ i ∈ set_of p, s i :=
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

variables [preorder ι] (l p s)

/-- `is_antimono_basis p s` means the image of `s` bounded by `p` is a filter basis
such that `s` is decreasing and `p` is increasing, ie `i ≤ j → p i → p j`. -/
structure is_antimono_basis extends is_basis p s : Prop :=
(decreasing : ∀ {i j}, p i → p j → i ≤ j → s j ⊆ s i)
(mono : monotone p)

/-- We say that a filter `l` has a antimono basis `s : ι → set α` bounded by `p : ι → Prop`,
if `t ∈ l` if and only if `t` includes `s i` for some `i` such that `p i`,
and `s` is decreasing and `p` is increasing, ie `i ≤ j → p i → p j`. -/
structure has_antimono_basis [preorder ι] (l : filter α) (p : ι → Prop) (s : ι → set α)
  extends has_basis l p s : Prop :=
(decreasing : ∀ {i j}, p i → p j → i ≤ j → s j ⊆ s i)
(mono : monotone p)

end same_type

section two_types

variables {la : filter α} {pa : ι → Prop} {sa : ι → set α}
  {lb : filter β} {pb : ι' → Prop} {sb : ι' → set β} {f : α → β}

lemma has_basis.tendsto_left_iff (hla : la.has_basis pa sa) :
  tendsto f la lb ↔ ∀ t ∈ lb, ∃ i (hi : pa i), ∀ x ∈ sa i, f x ∈ t :=
by { simp only [tendsto, (hla.map f).le_iff, image_subset_iff], refl }

lemma has_basis.tendsto_right_iff (hlb : lb.has_basis pb sb) :
  tendsto f la lb ↔ ∀ i (hi : pb i), ∀ᶠ x in la, f x ∈ sb i :=
by simp only [tendsto, hlb.ge_iff, mem_map, filter.eventually]

lemma has_basis.tendsto_iff (hla : la.has_basis pa sa) (hlb : lb.has_basis pb sb) :
  tendsto f la lb ↔ ∀ ib (hib : pb ib), ∃ ia (hia : pa ia), ∀ x ∈ sa ia, f x ∈ sb ib :=
by simp [hlb.tendsto_right_iff, hla.eventually_iff]

lemma tendsto.basis_left (H : tendsto f la lb) (hla : la.has_basis pa sa) :
  ∀ t ∈ lb, ∃ i (hi : pa i), ∀ x ∈ sa i, f x ∈ t :=
hla.tendsto_left_iff.1 H

lemma tendsto.basis_right (H : tendsto f la lb) (hlb : lb.has_basis pb sb) :
  ∀ i (hi : pb i), ∀ᶠ x in la, f x ∈ sb i :=
hlb.tendsto_right_iff.1 H

lemma tendsto.basis_both (H : tendsto f la lb) (hla : la.has_basis pa sa)
  (hlb : lb.has_basis pb sb) :
  ∀ ib (hib : pb ib), ∃ ia (hia : pa ia), ∀ x ∈ sa ia, f x ∈ sb ib :=
(hla.tendsto_iff hlb).1 H

lemma has_basis.prod (hla : la.has_basis pa sa) (hlb : lb.has_basis pb sb) :
  (la.prod lb).has_basis (λ i : ι × ι', pa i.1 ∧ pb i.2) (λ i, (sa i.1).prod (sb i.2)) :=
(hla.comap prod.fst).inf (hlb.comap prod.snd)

lemma has_basis.prod' {la : filter α} {lb : filter β} {ι : Type*} {p : ι → Prop}
  {sa : ι → set α} {sb : ι → set β}
  (hla : la.has_basis p sa) (hlb : lb.has_basis p sb)
  (h_dir : ∀ {i j}, p i → p j → ∃ k, p k ∧ sa k ⊆ sa i ∧ sb k ⊆ sb j) :
  (la.prod lb).has_basis p (λ i, (sa i).prod (sb i)) :=
⟨begin
  intros t,
  rw mem_prod_iff,
  split,
  { rintros ⟨u, u_in, v, v_in, huv⟩,
    rcases hla.mem_iff.mp u_in with ⟨i, hi, si⟩,
    rcases hlb.mem_iff.mp v_in with ⟨j, hj, sj⟩,
    rcases h_dir hi hj with ⟨k, hk, ki, kj⟩,
    use [k, hk],
    calc
    (sa k).prod (sb k) ⊆ (sa i).prod (sb j) : set.prod_mono ki kj
                   ... ⊆ u.prod v           : set.prod_mono si sj
                   ... ⊆ t                  : huv, },
  { rintro ⟨i, hi, h⟩,
    exact ⟨sa i, hla.mem_of_mem hi, sb i, hlb.mem_of_mem hi, h⟩ },
end⟩

lemma has_antimono_basis.tendsto [semilattice_sup ι] [nonempty ι] {l : filter α}
  {p : ι → Prop} {s : ι → set α} (hl : l.has_antimono_basis p s) {φ : ι → α}
  (h : ∀ i : ι, φ i ∈ s i) : tendsto φ at_top l  :=
begin
  rw hl.to_has_basis.tendsto_right_iff,
  intros i hi,
  rw eventually_at_top,
  exact ⟨i, λ j hij, hl.decreasing hi (hl.mono hij hi) hij (h j)⟩,
end

end two_types

/-- `is_countably_generated f` means `f = generate s` for some countable `s`. -/
def is_countably_generated (f : filter α) : Prop :=
∃ s : set (set α), countable s ∧ f = generate s

/-- `is_countable_basis p s` means the image of `s` bounded by `p` is a countable filter basis. -/
structure is_countable_basis (p : ι → Prop) (s : ι → set α) extends is_basis p s : Prop :=
(countable : countable $ set_of p)

/-- We say that a filter `l` has a countable basis `s : ι → set α` bounded by `p : ι → Prop`,
if `t ∈ l` if and only if `t` includes `s i` for some `i` such that `p i`, and the set
defined by `p` is countable. -/
structure has_countable_basis (l : filter α) (p : ι → Prop) (s : ι → set α) extends has_basis l p s : Prop :=
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

lemma antimono_seq_of_seq (s : ℕ → set α) :
  ∃ t : ℕ → set α, (∀ i j, i ≤ j → t j ⊆ t i) ∧ (⨅ i, 𝓟 $ s i) = ⨅ i, 𝓟 (t i) :=
begin
  use λ n, ⋂ m ≤ n, s m, split,
  { intros i j hij a, simp, intros h i' hi'i, apply h, transitivity; assumption },
    apply le_antisymm; rw le_infi_iff; intro i,
  { rw le_principal_iff, apply Inter_mem_sets (finite_le_nat _),
    intros j hji, rw ← le_principal_iff, apply infi_le_of_le j _, apply le_refl _ },
  { apply infi_le_of_le i _, rw principal_mono, intro a, simp, intro h, apply h, refl },
end

lemma countable_binfi_eq_infi_seq [complete_lattice α] {B : set ι} (Bcbl : countable B) (Bne : B.nonempty) (f : ι → α)
 : ∃ (x : ℕ → ι), (⨅ t ∈ B, f t) = ⨅ i, f (x i) :=
begin
  rw countable_iff_exists_surjective_to_subtype Bne at Bcbl,
  rcases Bcbl with ⟨g, gsurj⟩,
  rw infi_subtype',
  use (λ n, g n), apply le_antisymm; rw le_infi_iff,
  { intro i, apply infi_le_of_le (g i) _, apply le_refl _ },
  { intros a, rcases gsurj a with i, apply infi_le_of_le i _, subst h, apply le_refl _ }
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

namespace is_countably_generated

/-- A set generating a countably generated filter. -/
def generating_set {f : filter α} (h : is_countably_generated f) :=
classical.some h

lemma countable_generating_set {f : filter α} (h : is_countably_generated f) :
  countable h.generating_set :=
(classical.some_spec h).1

lemma eq_generate {f : filter α} (h : is_countably_generated f) :
  f = generate h.generating_set :=
(classical.some_spec h).2

/-- A countable filter basis for a countably generated filter. -/
def countable_filter_basis {l : filter α} (h : is_countably_generated l) :
  countable_filter_basis α :=
{ countable := (countable_set_of_finite_subset h.countable_generating_set).image _,
  ..filter_basis.of_sets (h.generating_set) }

lemma filter_basis_filter {l : filter α} (h : is_countably_generated l) :
h.countable_filter_basis.to_filter_basis.filter = l :=
begin
  conv_rhs { rw h.eq_generate },
  apply of_sets_filter_eq_generate,
end

lemma has_countable_basis {l : filter α} (h : is_countably_generated l) :
  l.has_countable_basis (λ t, finite t ∧ t ⊆ h.generating_set) (λ t, ⋂₀ t) :=
⟨by convert has_basis_generate _ ; exact h.eq_generate,
 countable_set_of_finite_subset h.countable_generating_set⟩

lemma exists_countable_infi_principal {f : filter α} (h : f.is_countably_generated) :
∃ s : set (set α), countable s ∧ f = ⨅ t ∈ s, 𝓟 t :=
begin
  let B := h.countable_filter_basis,
  use [B.sets, B.countable],
  rw ← h.filter_basis_filter,
  rw B.to_filter_basis.eq_infi_principal,
  rw infi_subtype''
end

lemma exists_seq {f : filter α} (cblb : f.is_countably_generated) :
    ∃ x : ℕ → set α, f = ⨅ i, 𝓟 (x i) :=
begin
  rcases cblb.exists_countable_infi_principal with ⟨B, Bcbl, rfl⟩,
  exact countable_binfi_principal_eq_seq_infi Bcbl,
end

lemma exists_antimono_seq {f : filter α} (cblb : f.is_countably_generated) :
  ∃ x : ℕ → set α, (∀ i j, i ≤ j → x j ⊆ x i) ∧ f = ⨅ i, 𝓟 (x i) :=
begin
  rcases cblb.exists_seq with ⟨x', hx'⟩,
  let x := λ n, ⋂ m ≤ n, x' m,
  use x, split,
  { intros i j hij a, simp [x], intros h i' hi'i, apply h, transitivity; assumption },
  subst hx', apply le_antisymm; rw le_infi_iff; intro i,
  { rw le_principal_iff, apply Inter_mem_sets (finite_le_nat _),
    intros j hji, rw ← le_principal_iff, apply infi_le_of_le j _, apply le_refl _ },
  { apply infi_le_of_le i _, rw principal_mono, intro a, simp [x], intro h, apply h, refl },
end

lemma has_antimono_basis {f : filter α} (h : f.is_countably_generated) :
 ∃ x : ℕ → set α, f.has_antimono_basis (λ _, true) x :=
begin
  rcases h.exists_antimono_seq with ⟨x, x_dec, rfl⟩,
  refine ⟨x, has_basis_infi_principal _ ⟨0⟩, _, monotone_const⟩,
  exacts [directed_of_sup x_dec, λ i j _ _, x_dec i j]
end

end is_countably_generated

lemma is_countably_generated_seq (x : ℕ → set α) : is_countably_generated (⨅ i, 𝓟 $ x i) :=
begin
  rcases antimono_seq_of_seq x with ⟨y, am, h⟩,
  rw h,
  use [range y, countable_range _],
  rw (has_basis_infi_principal _ _).eq_generate,
  { simp [range] },
  { exact directed_of_sup am },
  { use 0 },
end

lemma is_countably_generated_of_seq {f : filter α} (h : ∃ x : ℕ → set α, f = ⨅ i, 𝓟 $ x i) :
  f.is_countably_generated  :=
let ⟨x, h⟩ := h in by rw h ; apply is_countably_generated_seq

lemma is_countably_generated_binfi_principal {B : set $ set α} (h : countable B) :
  is_countably_generated (⨅ (s ∈ B), 𝓟 s) :=
is_countably_generated_of_seq (countable_binfi_principal_eq_seq_infi h)

lemma is_countably_generated_iff_exists_antimono_basis {f : filter α} : is_countably_generated f ↔
  ∃ x : ℕ → set α, f.has_antimono_basis (λ _, true) x :=
begin
  split,
  { intro h,
    exact h.has_antimono_basis },
  { rintros ⟨x, h⟩,
    rw h.to_has_basis.eq_infi,
    exact is_countably_generated_seq x },
end

namespace is_countably_generated

lemma exists_antimono_seq' {f : filter α} (cblb : f.is_countably_generated) :
  ∃ x : ℕ → set α, (∀ i j, i ≤ j → x j ⊆ x i) ∧ ∀ {s}, (s ∈ f ↔ ∃ i, x i ⊆ s) :=
let ⟨x, hx⟩ := is_countably_generated_iff_exists_antimono_basis.mp cblb in
⟨x, λ i j, hx.decreasing trivial trivial, λ s, by simp [hx.to_has_basis.mem_iff]⟩

protected lemma comap {l : filter β} (h : l.is_countably_generated) (f : α → β) :
  (comap f l).is_countably_generated :=
begin
  rcases h.exists_seq with ⟨x, hx⟩,
  apply is_countably_generated_of_seq,
  use λ i, f ⁻¹' x i,
  calc
    comap f l = comap f (⨅ i, 𝓟 (x i))   : by rw hx
          ... = (⨅ i, comap f $ 𝓟 $ x i) : comap_infi
          ... = (⨅ i, 𝓟 $ f ⁻¹' x i)     : by simp_rw comap_principal,
end

/-- An abstract version of continuity of sequentially continuous functions on metric spaces:
if a filter `k` is countably generated then `tendsto f k l` iff for every sequence `u`
converging to `k`, `f ∘ u` tends to `l`. -/
lemma tendsto_iff_seq_tendsto {f : α → β} {k : filter α} {l : filter β}
  (hcb : k.is_countably_generated) :
  tendsto f k l ↔ (∀ x : ℕ → α, tendsto x at_top k → tendsto (f ∘ x) at_top l) :=
suffices (∀ x : ℕ → α, tendsto x at_top k → tendsto (f ∘ x) at_top l) → tendsto f k l,
  from ⟨by intros; apply tendsto.comp; assumption, by assumption⟩,
begin
  rcases hcb.exists_antimono_seq with ⟨g, gmon, gbasis⟩,
  have gbasis : ∀ A, A ∈ k ↔ ∃ i, g i ⊆ A,
  { intro A,
    subst gbasis,
    rw mem_infi,
    { simp only [set.mem_Union, iff_self, filter.mem_principal_sets] },
    { exact directed_of_sup (λ i j h, principal_mono.mpr $ gmon _ _ h) },
    { apply_instance } },
  classical, contrapose,
  simp only [not_forall, not_imp, not_exists, subset_def, @tendsto_def _ _ f, gbasis],
  rintro ⟨B, hBl, hfBk⟩,
  choose x h using hfBk,
  use x, split,
  { simp only [tendsto_at_top', gbasis],
    rintros A ⟨i, hgiA⟩,
    use i,
    refine (λ j hj, hgiA $ gmon _ _ hj _),
    simp only [h] },
  { simp only [tendsto_at_top', (∘), not_forall, not_exists],
    use [B, hBl],
    intro i, use [i, (le_refl _)],
    apply (h i).right },
end

lemma tendsto_of_seq_tendsto {f : α → β} {k : filter α} {l : filter β}
  (hcb : k.is_countably_generated) :
  (∀ x : ℕ → α, tendsto x at_top k → tendsto (f ∘ x) at_top l) → tendsto f k l :=
hcb.tendsto_iff_seq_tendsto.2

lemma subseq_tendsto {f : filter α} (hf : is_countably_generated f)
  {u : ℕ → α}
  (hx : ne_bot (f ⊓ map u at_top)) :
  ∃ (θ : ℕ → ℕ), (strict_mono θ) ∧ (tendsto (u ∘ θ) at_top f) :=
begin
  rcases hf.has_antimono_basis with ⟨B, h⟩,
  have : ∀ N, ∃ n ≥ N, u n ∈ B N,
    from λ N, filter.inf_map_at_top_ne_bot_iff.mp hx _ (h.to_has_basis.mem_of_mem trivial) N,
  choose φ hφ using this,
  cases forall_and_distrib.mp hφ with φ_ge φ_in,
  have lim_uφ : tendsto (u ∘ φ) at_top f,
    from h.tendsto φ_in,
  have lim_φ : tendsto φ at_top at_top,
    from (tendsto_at_top_mono φ_ge tendsto_id),
  obtain ⟨ψ, hψ, hψφ⟩ : ∃ ψ : ℕ → ℕ, strict_mono ψ ∧ strict_mono (φ ∘ ψ),
    from strict_mono_subseq_of_tendsto_at_top lim_φ,
  exact ⟨φ ∘ ψ, hψφ, lim_uφ.comp $ strict_mono_tendsto_at_top hψ⟩,
end

end is_countably_generated

-- TODO : prove this for a encodable type
lemma is_countably_generated_at_top_finset_nat : (at_top : filter $ finset ℕ).is_countably_generated :=
begin
  apply is_countably_generated_of_seq,
  use λ N, Ici (finset.range N),
  apply eq_infi_of_mem_sets_iff_exists_mem,
  assume s,
  rw mem_at_top_sets,
  refine ⟨_, λ ⟨N, hN⟩, ⟨finset.range N, hN⟩⟩,
  rintros ⟨t, ht⟩,
  rcases mem_at_top_sets.1 (tendsto_finset_range (mem_at_top t)) with ⟨N, hN⟩,
  simp only [preimage, mem_set_of_eq] at hN,
  exact ⟨N, mem_principal_sets.2 $ λ t' ht', ht t' $ le_trans (hN _ $ le_refl N) ht'⟩
end
end filter
