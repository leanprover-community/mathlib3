/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import algebra.big_operators.basic
import data.finset.pairwise
import order.sup_indep

/-!
# Finite partitions

In this file, we define finite partitions. A finpartition of `a : α` is a finite set of pairwise
disjoint parts `parts : finset α` which does not contain `⊥` and whose supremum is `a`.

## Constructions

We provide many ways to build finpartitions:
* `finpartition.of_erase`: Builds a finpartition by erasing `⊥` for you.
* `finpartition.of_subset`: Builds a finpartition from a subset of the parts of a previous
  finpartition.
* `finpartition.empty`: The empty finpartition of `⊥`.
* `finpartition.indiscrete`: The indiscrete, aka trivial, aka pure, finpartition made of a single
  part.
* `finpartition.discrete`: The discrete finpartition of `s : finset α` made of singletons.
* `finpartition.bind`: Puts together the finpartitions of the parts of a finpartition into a new
  finpartition.
* `finpartition.atomise`: Makes a finpartition of `s : finset α` by breaking `s` along all finsets
  in `F : finset (finset α)`. Two elements of `s` belong to the same part iff they belong to the
  same elements of `F`.

`finpartition.indiscrete` and `finpartition.bind` together form the monadic structure of
`finpartition`.

## TODO

Link `finpartition` and `setoid.is_partition`.
-/

open finset function
open_locale big_operators

variables (ι : Type*) {ι' α : Type*} [fintype ι] [fintype ι']

/-- A finite partition of `a : α` is a sup-independent finite set of elements whose supremum is
`a`. We forbid `⊥` as a part. -/
@[ext] structure finpartition [lattice α] [order_bot α] (a : α) :=
(parts : ι → α)
(sup_indep : univ.sup_indep parts)
(sup_parts : univ.sup parts = a)
(ne_bot : ∀ i, parts i ≠ ⊥)

variables {ι}

-- instance [lattice α] [order_bot α] {a : α} : has_coe (finpartition ι a) (λ _, ι → α) :=
-- ⟨finpartition.parts⟩

attribute [protected] finpartition.sup_indep

namespace finpartition
section distrib_lattice_bot
variables [lattice α] [order_bot α]

/-- A `finpartition` constructor which does not insist on `⊥` not being a part. -/
@[simps] def of_erase [decidable_eq α] {a : α} (parts : ι → α) (disj : univ.sup_indep parts)
  (sup_parts : univ.sup parts = a) :
  finpartition {i // parts i ≠ ⊥} a :=
{ parts := parts ∘ coe,
  sup_indep := sup_indep_subtype.2 (disj.subset $ subset_univ _),
  sup_parts := begin
    classical,
    rw [←sup_parts, ←sup_image],
    conv_rhs { rw ←filter_union_filter_neg_eq (λ i, parts i = ⊥) univ },
    rw sup_union,
    have : (image coe (univ : finset {i // parts i ≠ ⊥})) = univ.filter (λ i, parts i ≠ ⊥),
    { ext, simp },
    rw ←this,
    convert bot_sup_eq.symm,
    rw eq_bot_iff,
    rw finset.sup_le_iff,
    simp,
  end,
  ne_bot := λ i, i.2 }

/-- A `finpartition` constructor from a bigger existing finpartition. -/
@[simps] def of_embedding {a b : α} (P : finpartition ι' a) (f : ι ↪ ι')
  (sup_parts : univ.sup (P.parts ∘ f) = b) :
  finpartition ι b :=
{ parts := P.parts ∘ f,
  sup_indep := by { rw ←sup_indep_map, exact P.sup_indep.subset (subset_univ _) },
  sup_parts := sup_parts,
  ne_bot := λ i, P.ne_bot _ }

variables (ι α)

/-- The empty finpartition. -/
@[simps] protected def empty [is_empty ι] : finpartition ι (⊥ : α) :=
{ parts := is_empty_elim,
  sup_indep := by { rw univ_eq_empty, exact sup_indep_empty _ },
  sup_parts := by rw [univ_eq_empty, sup_empty],
  ne_bot := is_empty_elim }

variables {ι α} {a : α}

/-- The finpartition in one part, aka indiscrete finpartition. -/
@[simps] def indiscrete [unique ι] (ha : a ≠ ⊥) : finpartition ι a :=
{ parts := λ _, a,
  sup_indep := by { rw univ_unique, exact sup_indep_singleton _ _ },
  sup_parts := by rw [univ_unique, sup_singleton],
  ne_bot := λ _, ha }

instance [is_empty ι] : inhabited (finpartition ι (⊥ : α)) := ⟨finpartition.empty ι α⟩

variables (P : finpartition ι a) {i : ι}

protected lemma le : P.parts i ≤ a := (le_sup $ mem_univ _).trans P.sup_parts.le

protected lemma bot_lt (P : finpartition ι a) [nonempty ι] : ⊥ < a :=
(P.ne_bot $ classical.arbitrary ι).bot_lt.trans_le $ (le_sup $ mem_univ _).trans P.sup_parts.le

protected lemma eq_bot (P : finpartition ι a) [is_empty ι] : a = ⊥ :=
by rw [←P.sup_parts, univ_eq_empty, sup_empty]

instance [is_empty ι] : unique (finpartition ι (⊥ : α)) :=
{ uniq := λ P, by { ext i, exact is_empty_elim i}, ..finpartition.inhabited }

variables {P}

/-- Given a finpartition `P` of `a` and finpartitions of each part of `P`, this yields the
finpartition of `a` obtained by juxtaposing all the subpartitions. -/
@[simps] def bind (P : finpartition ι a) (δ : ι → Type*) [Π i, fintype (δ i)]
  (Q : Π i, finpartition (δ i) (P.parts i)) :
  finpartition (Σ i, δ i) a :=
{ parts := λ i, (Q _).parts i.2,
  sup_indep := begin
    rw ←univ_sigma_univ,
    refine sup_indep.sigma _ (λ i _, (Q i).sup_indep),
    convert P.sup_indep,
    ext i,
    exact (Q i).sup_parts,
  end,
  sup_parts := begin
    rw [←univ_sigma_univ, sup_sigma],
    convert P.sup_parts,
    ext i,
    exact (Q _).sup_parts,
  end,
  ne_bot := λ i, (Q _).ne_bot _ }

/-- Adds `b` to a finpartition of `a` to make a finpartition of `a ⊔ b`. -/
@[simps] def extend [decidable_eq α] (P : finpartition ι a) {b c : α} (hb : b ≠ ⊥)
  (hab : disjoint a b) (hc : a ⊔ b = c) :
  finpartition (option ι) c :=
{ parts := λ i, option.elim i b P.parts,
  sup_indep :=
  begin
    rw univ_option,
    rw insert_none,
    dsimp,
    exact P.disjoint.insert (λ d hd hbd, hab.symm.mono_right $ P.le hd),
  end,
  sup_parts := by rwa [sup_insert, P.sup_parts, sup_comm],
  ne_bot := λ h, (mem_insert.1 h).elim hb.symm P.not_bot_mem }

end distrib_lattice_bot

section generalized_boolean_algebra
variables [generalized_boolean_algebra α] [decidable_eq α] {a : α} (P : finpartition a)

/-- Restricts a finpartition to avoid a given element. -/
def avoid (b : α) : finpartition (a \ b) :=
of_erase
  (P.parts.image (\ b))
  (P.disjoint.image_finset $ λ a, sdiff_le)
  (begin
    rw [sup_image, comp.left_id, finset.sup_sdiff_right],
    congr,
    exact P.sup_parts,
  end)

end generalized_boolean_algebra
end finpartition

/-! ### Finite partitions of finsets -/

namespace finpartition
variables [decidable_eq α] {s : finset α} (P : finpartition s)

lemma nonempty_of_mem_parts {a : finset α} (ha : a ∈ P.parts) : a.nonempty :=
nonempty_iff_ne_empty.2 $ P.ne_bot ha

lemma exists_mem {a : α} (ha : a ∈ s) : ∃ t ∈ P.parts, a ∈ t :=
by { simp_rw ←P.sup_parts at ha, exact mem_sup.1 ha }

lemma bUnion_parts : P.parts.bUnion id = s := (sup_eq_bUnion _ _).symm.trans P.sup_parts

lemma sum_card_parts : ∑ i in P.parts, i.card = s.card :=
begin
  rw ←card_bUnion P.disjoint,
  exact congr_arg finset.card P.bUnion_parts,
end

lemma parts_nonempty [nonempty α] [fintype α] (P : finpartition (univ : finset α)) :
  P.parts.nonempty :=
parts_nonempty_iff.2 univ_nonempty.ne_empty

/-- The partition in singletons. -/
@[simps] def discrete (s : finset α) : finpartition s :=
{ parts := s.map ⟨singleton, singleton_injective⟩,
  disjoint :=
    begin
      rw finset.coe_map,
      exact finset.pairwise_disjoint_range_singleton.subset (set.image_subset_range _ _),
    end,
  sup_parts := by rw [sup_map, comp.left_id, embedding.coe_fn_mk, finset.sup_singleton'],
  not_bot_mem := by simp }

lemma card_discrete : (discrete s).parts.card = s.card := finset.card_map _

section atomise

/-- Cuts `s` along the finsets in `F`: Two elements of `s` will be in the same part if they are
in the same finsets of `F`. -/
def atomise (s : finset α) (F : finset (finset α)) : finpartition s :=
of_erase
  (F.powerset.image $ λ Q, s.filter (λ i, ∀ t ∈ F, t ∈ Q ↔ i ∈ t))
  (λ x hx y hy h z hz, h begin
    rw [mem_coe, mem_image] at hx hy,
    obtain ⟨Q, hQ, rfl⟩ := hx,
    obtain ⟨R, hR, rfl⟩ := hy,
    suffices h : Q = R,
    { subst h },
    rw [inf_eq_inter, mem_inter, mem_filter, mem_filter] at hz,
    rw mem_powerset at hQ hR,
    ext i,
    refine ⟨λ hi, _, λ hi, _⟩,
    { rwa [hz.2.2 _ (hQ hi), ←hz.1.2 _ (hQ hi)] },
    { rwa [hz.1.2 _ (hR hi), ←hz.2.2 _ (hR hi)] }
  end)
  (begin
    refine (finset.sup_le $ λ t ht, _).antisymm (λ a ha, _),
    { rw mem_image at ht,
      obtain ⟨A, hA, rfl⟩ := ht,
      exact s.filter_subset _ },
    { rw [mem_sup],
      refine ⟨s.filter (λ i, ∀ t, t ∈ F → (t ∈ F.filter (λ u, a ∈ u) ↔ i ∈ t)),
        mem_image_of_mem _ (mem_powerset.2 $ filter_subset _ _), mem_filter.2 ⟨ha, λ t ht, _⟩⟩,
      rw mem_filter,
      exact and_iff_right ht }
  end)

variables {F : finset (finset α)}

lemma mem_atomise {t : finset α} :
  t ∈ (atomise s F).parts ↔ t.nonempty ∧ ∃ (Q ⊆ F), s.filter (λ i, ∀ u ∈ F, u ∈ Q ↔ i ∈ u) = t :=
by simp only [atomise, of_erase, bot_eq_empty, mem_erase, mem_image, nonempty_iff_ne_empty,
  mem_singleton, and_comm, mem_powerset, exists_prop]

lemma atomise_empty (hs : s.nonempty) : (atomise s ∅).parts = {s} :=
begin
  simp_rw [atomise, powerset_empty, image_singleton, not_mem_empty, forall_false_left,
    implies_true_iff, filter_true],
  exact erase_eq_of_not_mem (not_mem_singleton.2 hs.ne_empty.symm),
end

lemma card_atomise_le : (atomise s F).parts.card ≤ 2^F.card :=
(card_le_of_subset $ erase_subset _ _).trans $ finset.card_image_le.trans (card_powerset _).le

lemma bUnion_filter_atomise (t : finset α) (ht : t ∈ F) (hts : t ⊆ s) :
  ((atomise s F).parts.filter $ λ u, u ⊆ t).bUnion id = t :=
begin
  ext a,
  rw mem_bUnion,
  refine ⟨λ ⟨u, hu, ha⟩, (mem_filter.1 hu).2 ha, λ ha, _⟩,
  obtain ⟨u, hu, hau⟩ := (atomise s F).exists_mem (hts ha),
  refine ⟨u, mem_filter.2 ⟨hu, λ b hb, _⟩, hau⟩,
  obtain ⟨Q, hQ, rfl⟩ := (mem_atomise.1 hu).2,
  rw mem_filter at hau hb,
  rwa [←hb.2 _ ht, hau.2 _ ht]
end

end atomise
end finpartition
