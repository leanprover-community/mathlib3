/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Scott Morrison
-/
import algebra.big_operators.finsupp
import algebra.hom.group_action
import algebra.regular.smul
import data.finset.preimage
import data.rat.big_operators

/-!
# Miscellaneous definitions, lemmas, and constructions using finsupp

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main declarations

* `finsupp.graph`: the finset of input and output pairs with non-zero outputs.
* `finsupp.map_range.equiv`: `finsupp.map_range` as an equiv.
* `finsupp.map_domain`: maps the domain of a `finsupp` by a function and by summing.
* `finsupp.comap_domain`: postcomposition of a `finsupp` with a function injective on the preimage
  of its support.
* `finsupp.some`: restrict a finitely supported function on `option α` to a finitely supported
  function on `α`.
* `finsupp.filter`: `filter p f` is the finitely supported function that is `f a` if `p a` is true
  and 0 otherwise.
* `finsupp.frange`: the image of a finitely supported function on its support.
* `finsupp.subtype_domain`: the restriction of a finitely supported function `f` to a subtype.

## Implementation notes

This file is a `noncomputable theory` and uses classical logic throughout.

## TODO

* This file is currently ~1600 lines long and is quite a miscellany of definitions and lemmas,
  so it should be divided into smaller pieces.

* Expand the list of definitions and important lemmas to the module docstring.

-/

noncomputable theory

open finset function
open_locale big_operators

variables {α β γ ι M M' N P G H R S : Type*}

namespace finsupp

/-! ### Declarations about `graph` -/

section graph

variable [has_zero M]

/-- The graph of a finitely supported function over its support, i.e. the finset of input and output
pairs with non-zero outputs. -/
def graph (f : α →₀ M) : finset (α × M) :=
f.support.map ⟨λ a, prod.mk a (f a), λ x y h, (prod.mk.inj h).1⟩

lemma mk_mem_graph_iff {a : α} {m : M} {f : α →₀ M} : (a, m) ∈ f.graph ↔ f a = m ∧ m ≠ 0 :=
begin
  simp_rw [graph, mem_map, mem_support_iff],
  split,
  { rintro ⟨b, ha, rfl, -⟩,
    exact ⟨rfl, ha⟩ },
  { rintro ⟨rfl, ha⟩,
    exact ⟨a, ha, rfl⟩ }
end

@[simp] lemma mem_graph_iff {c : α × M} {f : α →₀ M} : c ∈ f.graph ↔ f c.1 = c.2 ∧ c.2 ≠ 0 :=
by { cases c, exact mk_mem_graph_iff }

lemma mk_mem_graph (f : α →₀ M) {a : α} (ha : a ∈ f.support) : (a, f a) ∈ f.graph :=
mk_mem_graph_iff.2 ⟨rfl, mem_support_iff.1 ha⟩

lemma apply_eq_of_mem_graph {a : α} {m : M} {f : α →₀ M} (h : (a, m) ∈ f.graph) : f a = m :=
(mem_graph_iff.1 h).1

@[simp] lemma not_mem_graph_snd_zero (a : α) (f : α →₀ M) : (a, (0 : M)) ∉ f.graph :=
λ h, (mem_graph_iff.1 h).2.irrefl

@[simp] lemma image_fst_graph [decidable_eq α] (f : α →₀ M) : f.graph.image prod.fst = f.support :=
begin
  classical,
  simp only [graph, map_eq_image, image_image, embedding.coe_fn_mk, (∘), image_id'],
end

lemma graph_injective (α M) [has_zero M] : injective (@graph α M _) :=
begin
  intros f g h,
  classical,
  have hsup : f.support = g.support, by rw [← image_fst_graph, h, image_fst_graph],
  refine ext_iff'.2 ⟨hsup, λ x hx, apply_eq_of_mem_graph $ h.symm ▸ _⟩,
  exact mk_mem_graph _ (hsup ▸ hx)
end

@[simp] lemma graph_inj {f g : α →₀ M} : f.graph = g.graph ↔ f = g :=
(graph_injective α M).eq_iff

@[simp] lemma graph_zero : graph (0 : α →₀ M) = ∅ := by simp [graph]

@[simp] lemma graph_eq_empty {f : α →₀ M} : f.graph = ∅ ↔ f = 0 :=
(graph_injective α M).eq_iff' graph_zero

end graph

end finsupp

/-! ### Declarations about `map_range` -/

section map_range

namespace finsupp

section equiv

variables [has_zero M] [has_zero N] [has_zero P]

/-- `finsupp.map_range` as an equiv. -/
@[simps apply]
def map_range.equiv (f : M ≃ N) (hf : f 0 = 0) (hf' : f.symm 0 = 0) : (α →₀ M) ≃ (α →₀ N) :=
{ to_fun := (map_range f hf : (α →₀ M) → (α →₀ N)),
  inv_fun := (map_range f.symm hf' : (α →₀ N) → (α →₀ M)),
  left_inv := λ x, begin
    rw ←map_range_comp _ _ _ _; simp_rw equiv.symm_comp_self,
    { exact map_range_id _ },
    { refl },
  end,
  right_inv := λ x, begin
    rw ←map_range_comp _ _ _ _; simp_rw equiv.self_comp_symm,
    { exact map_range_id _ },
    { refl },
  end }

@[simp]
lemma map_range.equiv_refl :
  map_range.equiv (equiv.refl M) rfl rfl = equiv.refl (α →₀ M) :=
equiv.ext map_range_id

lemma map_range.equiv_trans
  (f : M ≃ N) (hf : f 0 = 0) (hf') (f₂ : N ≃ P) (hf₂ : f₂ 0 = 0) (hf₂') :
  (map_range.equiv (f.trans f₂) (by rw [equiv.trans_apply, hf, hf₂])
    (by rw [equiv.symm_trans_apply, hf₂', hf']) : (α →₀ _) ≃ _) =
    (map_range.equiv f hf hf').trans (map_range.equiv f₂ hf₂ hf₂') :=
equiv.ext $ map_range_comp _ _ _ _ _

@[simp] lemma map_range.equiv_symm (f : M ≃ N) (hf hf') :
  ((map_range.equiv f hf hf').symm : (α →₀ _) ≃ _) = map_range.equiv f.symm hf' hf :=
equiv.ext $ λ x, rfl

end equiv

section zero_hom

variables [has_zero M] [has_zero N] [has_zero P]

/-- Composition with a fixed zero-preserving homomorphism is itself an zero-preserving homomorphism
on functions. -/
@[simps]
def map_range.zero_hom (f : zero_hom M N) : zero_hom (α →₀ M) (α →₀ N) :=
{ to_fun := (map_range f f.map_zero : (α →₀ M) → (α →₀ N)),
  map_zero' := map_range_zero }

@[simp]
lemma map_range.zero_hom_id :
  map_range.zero_hom (zero_hom.id M) = zero_hom.id (α →₀ M) := zero_hom.ext map_range_id

lemma map_range.zero_hom_comp (f : zero_hom N P) (f₂ : zero_hom M N) :
  (map_range.zero_hom (f.comp f₂) : zero_hom (α →₀ _) _) =
    (map_range.zero_hom f).comp (map_range.zero_hom f₂) :=
zero_hom.ext $ map_range_comp _ _ _ _ _

end zero_hom

section add_monoid_hom
variables [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P]

/--
Composition with a fixed additive homomorphism is itself an additive homomorphism on functions.
-/
@[simps]
def map_range.add_monoid_hom (f : M →+ N) : (α →₀ M) →+ (α →₀ N) :=
{ to_fun := (map_range f f.map_zero : (α →₀ M) → (α →₀ N)),
  map_zero' := map_range_zero,
  map_add' := λ a b, map_range_add f.map_add _ _ }

@[simp]
lemma map_range.add_monoid_hom_id :
  map_range.add_monoid_hom (add_monoid_hom.id M) = add_monoid_hom.id (α →₀ M) :=
add_monoid_hom.ext map_range_id

lemma map_range.add_monoid_hom_comp (f : N →+ P) (f₂ : M →+ N) :
  (map_range.add_monoid_hom (f.comp f₂) : (α →₀ _) →+ _) =
    (map_range.add_monoid_hom f).comp (map_range.add_monoid_hom f₂) :=
add_monoid_hom.ext $ map_range_comp _ _ _ _ _

@[simp]
lemma map_range.add_monoid_hom_to_zero_hom (f : M →+ N) :
  (map_range.add_monoid_hom f).to_zero_hom =
    (map_range.zero_hom f.to_zero_hom : zero_hom (α →₀ _) _) :=
zero_hom.ext $ λ _, rfl

lemma map_range_multiset_sum (f : M →+ N) (m : multiset (α →₀ M)) :
  map_range f f.map_zero m.sum = (m.map $ λx, map_range f f.map_zero x).sum :=
(map_range.add_monoid_hom f : (α →₀ _) →+ _).map_multiset_sum _

lemma map_range_finset_sum (f : M →+ N) (s : finset ι) (g : ι → (α →₀ M))  :
  map_range f f.map_zero (∑ x in s, g x) = ∑ x in s, map_range f f.map_zero (g x) :=
(map_range.add_monoid_hom f : (α →₀ _) →+ _).map_sum _ _

/-- `finsupp.map_range.add_monoid_hom` as an equiv. -/
@[simps apply]
def map_range.add_equiv (f : M ≃+ N) : (α →₀ M) ≃+ (α →₀ N) :=
{ to_fun := (map_range f f.map_zero : (α →₀ M) → (α →₀ N)),
  inv_fun := (map_range f.symm f.symm.map_zero : (α →₀ N) → (α →₀ M)),
  left_inv := λ x, begin
    rw ←map_range_comp _ _ _ _; simp_rw add_equiv.symm_comp_self,
    { exact map_range_id _ },
    { refl },
  end,
  right_inv := λ x, begin
    rw ←map_range_comp _ _ _ _; simp_rw add_equiv.self_comp_symm,
    { exact map_range_id _ },
    { refl },
  end,
  ..(map_range.add_monoid_hom f.to_add_monoid_hom) }

@[simp]
lemma map_range.add_equiv_refl :
  map_range.add_equiv (add_equiv.refl M) = add_equiv.refl (α →₀ M) :=
add_equiv.ext map_range_id

lemma map_range.add_equiv_trans (f : M ≃+ N) (f₂ : N ≃+ P) :
  (map_range.add_equiv (f.trans f₂) : (α →₀ _) ≃+ _) =
    (map_range.add_equiv f).trans (map_range.add_equiv f₂) :=
add_equiv.ext $ map_range_comp _ _ _ _ _

@[simp] lemma map_range.add_equiv_symm (f : M ≃+ N) :
  ((map_range.add_equiv f).symm : (α →₀ _) ≃+ _) = map_range.add_equiv f.symm :=
add_equiv.ext $ λ x, rfl

@[simp]
lemma map_range.add_equiv_to_add_monoid_hom (f : M ≃+ N) :
  (map_range.add_equiv f : (α →₀ _) ≃+ _).to_add_monoid_hom =
    (map_range.add_monoid_hom f.to_add_monoid_hom : (α →₀ _) →+ _) :=
add_monoid_hom.ext $ λ _, rfl

@[simp]
lemma map_range.add_equiv_to_equiv (f : M ≃+ N) :
  (map_range.add_equiv f).to_equiv =
    (map_range.equiv f.to_equiv f.map_zero f.symm.map_zero : (α →₀ _) ≃ _) :=
equiv.ext $ λ _, rfl

end add_monoid_hom

end finsupp

end map_range

/-! ### Declarations about `equiv_congr_left` -/

section equiv_congr_left
variable [has_zero M]

namespace finsupp

/-- Given `f : α ≃ β`, we can map `l : α →₀ M` to  `equiv_map_domain f l : β →₀ M` (computably)
by mapping the support forwards and the function backwards. -/
def equiv_map_domain (f : α ≃ β) (l : α →₀ M) : β →₀ M :=
{ support := l.support.map f.to_embedding,
  to_fun := λ a, l (f.symm a),
  mem_support_to_fun := λ a, by simp only [finset.mem_map_equiv, mem_support_to_fun]; refl }

@[simp] lemma equiv_map_domain_apply (f : α ≃ β) (l : α →₀ M) (b : β) :
  equiv_map_domain f l b = l (f.symm b) := rfl

lemma equiv_map_domain_symm_apply (f : α ≃ β) (l : β →₀ M) (a : α) :
  equiv_map_domain f.symm l a = l (f a) := rfl

@[simp] lemma equiv_map_domain_refl (l : α →₀ M) : equiv_map_domain (equiv.refl _) l = l :=
by ext x; refl

lemma equiv_map_domain_refl' : equiv_map_domain (equiv.refl _) = @id (α →₀ M) :=
by ext x; refl

lemma equiv_map_domain_trans (f : α ≃ β) (g : β ≃ γ) (l : α →₀ M) :
  equiv_map_domain (f.trans g) l = equiv_map_domain g (equiv_map_domain f l) := by ext x; refl

lemma equiv_map_domain_trans' (f : α ≃ β) (g : β ≃ γ) :
  @equiv_map_domain _ _ M _ (f.trans g) = equiv_map_domain g ∘ equiv_map_domain f := by ext x; refl

@[simp] lemma equiv_map_domain_single (f : α ≃ β) (a : α) (b : M) :
  equiv_map_domain f (single a b) = single (f a) b :=
begin
  classical,
  ext x,
  simp only [single_apply, equiv.apply_eq_iff_eq_symm_apply, equiv_map_domain_apply],
end

@[simp] lemma equiv_map_domain_zero {f : α ≃ β} : equiv_map_domain f (0 : α →₀ M) = (0 : β →₀ M) :=
by ext x; simp only [equiv_map_domain_apply, coe_zero, pi.zero_apply]

/-- Given `f : α ≃ β`, the finitely supported function spaces are also in bijection:
`(α →₀ M) ≃ (β →₀ M)`.

This is the finitely-supported version of `equiv.Pi_congr_left`. -/
def equiv_congr_left (f : α ≃ β) : (α →₀ M) ≃ (β →₀ M) :=
by refine ⟨equiv_map_domain f, equiv_map_domain f.symm, λ f, _, λ f, _⟩;
  ext x; simp only [equiv_map_domain_apply, equiv.symm_symm,
    equiv.symm_apply_apply, equiv.apply_symm_apply]

@[simp] lemma equiv_congr_left_apply (f : α ≃ β) (l : α →₀ M) :
  equiv_congr_left f l = equiv_map_domain f l := rfl

@[simp] lemma equiv_congr_left_symm (f : α ≃ β) :
  (@equiv_congr_left _ _ M _ f).symm = equiv_congr_left f.symm := rfl

end finsupp

end equiv_congr_left


section cast_finsupp
variables [has_zero M] (f : α →₀ M)

namespace nat

@[simp, norm_cast] lemma cast_finsupp_prod [comm_semiring R] (g : α → M → ℕ) :
  (↑(f.prod g) : R) = f.prod (λ a b, ↑(g a b)) :=
nat.cast_prod _ _

@[simp, norm_cast] lemma cast_finsupp_sum [comm_semiring R] (g : α → M → ℕ) :
  (↑(f.sum g) : R) = f.sum (λ a b, ↑(g a b)) :=
nat.cast_sum _ _

end nat

namespace int

@[simp, norm_cast] lemma cast_finsupp_prod [comm_ring R] (g : α → M → ℤ) :
  (↑(f.prod g) : R) = f.prod (λ a b, ↑(g a b)) :=
int.cast_prod _ _

@[simp, norm_cast] lemma cast_finsupp_sum [comm_ring R] (g : α → M → ℤ) :
  (↑(f.sum g) : R) = f.sum (λ a b, ↑(g a b)) :=
int.cast_sum _ _

end int

namespace rat

@[simp, norm_cast] lemma cast_finsupp_sum [division_ring R] [char_zero R] (g : α → M → ℚ) :
  (↑(f.sum g) : R) = f.sum (λ a b, g a b) :=
cast_sum _ _

@[simp, norm_cast] lemma cast_finsupp_prod [field R] [char_zero R] (g : α → M → ℚ) :
  (↑(f.prod g) : R) = f.prod (λ a b, g a b) :=
cast_prod _ _

end rat
end cast_finsupp




/-! ### Declarations about `map_domain` -/

namespace finsupp

section map_domain
variables [add_comm_monoid M] {v v₁ v₂ : α →₀ M}


/-- Given `f : α → β` and `v : α →₀ M`, `map_domain f v : β →₀ M`
  is the finitely supported function whose value at `a : β` is the sum
  of `v x` over all `x` such that `f x = a`. -/
def map_domain (f : α → β) (v : α →₀ M) : β →₀ M :=
v.sum $ λa, single (f a)

lemma map_domain_apply {f : α → β} (hf : function.injective f) (x : α →₀ M) (a : α) :
  map_domain f x (f a) = x a :=
begin
  rw [map_domain, sum_apply, sum, finset.sum_eq_single a, single_eq_same],
  { assume b _ hba, exact single_eq_of_ne (hf.ne hba) },
  { assume h, rw [not_mem_support_iff.1 h, single_zero, zero_apply] }
end

lemma map_domain_notin_range {f : α → β} (x : α →₀ M) (a : β) (h : a ∉ set.range f) :
  map_domain f x a = 0 :=
begin
  rw [map_domain, sum_apply, sum],
  exact finset.sum_eq_zero
    (assume a' h', single_eq_of_ne $ assume eq, h $ eq ▸ set.mem_range_self _)
end

@[simp]
lemma map_domain_id : map_domain id v = v :=
sum_single _

lemma map_domain_comp {f : α → β} {g : β → γ} :
  map_domain (g ∘ f) v = map_domain g (map_domain f v) :=
begin
  refine ((sum_sum_index _ _).trans _).symm,
  { intro, exact single_zero _ },
  { intro, exact single_add _ },
  refine sum_congr (λ _ _, sum_single_index _),
  { exact single_zero _ }
end

@[simp]
lemma map_domain_single {f : α → β} {a : α} {b : M} : map_domain f (single a b) = single (f a) b :=
sum_single_index $ single_zero _

@[simp] lemma map_domain_zero {f : α → β} : map_domain f (0 : α →₀ M) = (0 : β →₀ M) :=
sum_zero_index

lemma map_domain_congr {f g : α → β} (h : ∀x∈v.support, f x = g x) :
  v.map_domain f = v.map_domain g :=
finset.sum_congr rfl $ λ _ H, by simp only [h _ H]

lemma map_domain_add {f : α → β} : map_domain f (v₁ + v₂) = map_domain f v₁ + map_domain f v₂ :=
sum_add_index' (λ _, single_zero _) (λ _, single_add _)

@[simp] lemma map_domain_equiv_apply {f : α ≃ β} (x : α →₀ M) (a : β) :
  map_domain f x a = x (f.symm a) :=
begin
  conv_lhs { rw ←f.apply_symm_apply a },
  exact map_domain_apply f.injective _ _,
end

/-- `finsupp.map_domain` is an `add_monoid_hom`. -/
@[simps]
def map_domain.add_monoid_hom (f : α → β) : (α →₀ M) →+ (β →₀ M) :=
{ to_fun := map_domain f,
  map_zero' := map_domain_zero,
  map_add' := λ _ _, map_domain_add}

@[simp]
lemma map_domain.add_monoid_hom_id : map_domain.add_monoid_hom id = add_monoid_hom.id (α →₀ M) :=
add_monoid_hom.ext $ λ _, map_domain_id

lemma map_domain.add_monoid_hom_comp (f : β → γ) (g : α → β) :
  (map_domain.add_monoid_hom (f ∘ g) : (α →₀ M) →+ (γ →₀ M)) =
    (map_domain.add_monoid_hom f).comp (map_domain.add_monoid_hom g) :=
add_monoid_hom.ext $ λ _, map_domain_comp

lemma map_domain_finset_sum {f : α → β} {s : finset ι} {v : ι → α →₀ M} :
  map_domain f (∑ i in s, v i) = ∑ i in s, map_domain f (v i) :=
(map_domain.add_monoid_hom f : (α →₀ M) →+ β →₀ M).map_sum _ _

lemma map_domain_sum [has_zero N] {f : α → β} {s : α →₀ N} {v : α → N → α →₀ M} :
  map_domain f (s.sum v) = s.sum (λa b, map_domain f (v a b)) :=
(map_domain.add_monoid_hom f : (α →₀ M) →+ β →₀ M).map_finsupp_sum _ _

lemma map_domain_support [decidable_eq β] {f : α → β} {s : α →₀ M} :
  (s.map_domain f).support ⊆ s.support.image f :=
finset.subset.trans support_sum $
  finset.subset.trans (finset.bUnion_mono $ assume a ha, support_single_subset) $
  by rw [finset.bUnion_singleton]; exact subset.refl _

lemma map_domain_apply' (S : set α) {f : α → β} (x : α →₀ M)
  (hS : (x.support : set α) ⊆ S) (hf : set.inj_on f S) {a : α} (ha : a ∈ S) :
  map_domain f x (f a) = x a :=
begin
  classical,
  rw [map_domain, sum_apply, sum],
  simp_rw single_apply,
  by_cases hax : a ∈ x.support,
  { rw [← finset.add_sum_erase _ _ hax, if_pos rfl],
    convert add_zero _,
    refine finset.sum_eq_zero (λ i hi, if_neg _),
    exact (hf.mono hS).ne (finset.mem_of_mem_erase hi) hax (finset.ne_of_mem_erase hi), },
  { rw not_mem_support_iff.1 hax,
    refine finset.sum_eq_zero (λ i hi, if_neg _),
    exact hf.ne (hS hi) ha (ne_of_mem_of_not_mem hi hax) }
end

lemma map_domain_support_of_inj_on [decidable_eq β] {f : α → β} (s : α →₀ M)
  (hf : set.inj_on f s.support) : (map_domain f s).support = finset.image f s.support :=
finset.subset.antisymm map_domain_support $ begin
  intros x hx,
  simp only [mem_image, exists_prop, mem_support_iff, ne.def] at hx,
  rcases hx with ⟨hx_w, hx_h_left, rfl⟩,
  simp only [mem_support_iff, ne.def],
  rw map_domain_apply' (↑s.support : set _) _ _ hf,
  { exact hx_h_left, },
  { simp only [mem_coe, mem_support_iff, ne.def],
    exact hx_h_left, },
  { exact subset.refl _, },
end

lemma map_domain_support_of_injective [decidable_eq β] {f : α → β} (hf : function.injective f)
  (s : α →₀ M) : (map_domain f s).support = finset.image f s.support :=
map_domain_support_of_inj_on s (hf.inj_on _)

@[to_additive]
lemma prod_map_domain_index [comm_monoid N] {f : α → β} {s : α →₀ M}
  {h : β → M → N} (h_zero : ∀b, h b 0 = 1) (h_add : ∀b m₁ m₂, h b (m₁ + m₂) = h b m₁ * h b m₂) :
  (map_domain f s).prod h = s.prod (λa m, h (f a) m) :=
(prod_sum_index h_zero h_add).trans $ prod_congr $ λ _ _, prod_single_index (h_zero _)

/--
A version of `sum_map_domain_index` that takes a bundled `add_monoid_hom`,
rather than separate linearity hypotheses.
-/
-- Note that in `prod_map_domain_index`, `M` is still an additive monoid,
-- so there is no analogous version in terms of `monoid_hom`.
@[simp]
lemma sum_map_domain_index_add_monoid_hom [add_comm_monoid N] {f : α → β}
  {s : α →₀ M} (h : β → M →+ N) :
  (map_domain f s).sum (λ b m, h b m) = s.sum (λ a m, h (f a) m) :=
@sum_map_domain_index _ _ _ _ _ _ _ _
  (λ b m, h b m)
  (λ b, (h b).map_zero)
  (λ b m₁ m₂, (h b).map_add _ _)

lemma emb_domain_eq_map_domain (f : α ↪ β) (v : α →₀ M) :
  emb_domain f v = map_domain f v :=
begin
  ext a,
  by_cases a ∈ set.range f,
  { rcases h with ⟨a, rfl⟩,
    rw [map_domain_apply f.injective, emb_domain_apply] },
  { rw [map_domain_notin_range, emb_domain_notin_range]; assumption }
end

@[to_additive]
lemma prod_map_domain_index_inj [comm_monoid N] {f : α → β} {s : α →₀ M}
  {h : β → M → N} (hf : function.injective f) :
  (s.map_domain f).prod h = s.prod (λa b, h (f a) b) :=
by rw [←function.embedding.coe_fn_mk f hf, ←emb_domain_eq_map_domain, prod_emb_domain]

lemma map_domain_injective {f : α → β} (hf : function.injective f) :
  function.injective (map_domain f : (α →₀ M) → (β →₀ M)) :=
begin
  assume v₁ v₂ eq, ext a,
  have : map_domain f v₁ (f a) = map_domain f v₂ (f a), { rw eq },
  rwa [map_domain_apply hf, map_domain_apply hf] at this,
end

/-- When `f` is an embedding we have an embedding `(α →₀ ℕ)  ↪ (β →₀ ℕ)` given by `map_domain`. -/
@[simps] def map_domain_embedding {α β : Type*} (f : α ↪ β) : (α →₀ ℕ) ↪ β →₀ ℕ :=
⟨finsupp.map_domain f, finsupp.map_domain_injective f.injective⟩

lemma map_domain.add_monoid_hom_comp_map_range [add_comm_monoid N] (f : α → β) (g : M →+ N) :
  (map_domain.add_monoid_hom f).comp (map_range.add_monoid_hom g) =
    (map_range.add_monoid_hom g).comp (map_domain.add_monoid_hom f) :=
by { ext, simp }

/-- When `g` preserves addition, `map_range` and `map_domain` commute. -/
lemma map_domain_map_range [add_comm_monoid N] (f : α → β) (v : α →₀ M) (g : M → N)
  (h0 : g 0 = 0) (hadd : ∀ x y, g (x + y) = g x + g y) :
  map_domain f (map_range g h0 v) = map_range g h0 (map_domain f v) :=
let g' : M →+ N := { to_fun := g, map_zero' := h0, map_add' := hadd} in
add_monoid_hom.congr_fun (map_domain.add_monoid_hom_comp_map_range f g') v

lemma sum_update_add [add_comm_monoid α] [add_comm_monoid β]
  (f : ι →₀ α) (i : ι) (a : α) (g : ι → α → β) (hg : ∀ i, g i 0 = 0)
  (hgg : ∀ (j : ι) (a₁ a₂ : α), g j (a₁ + a₂) = g j a₁ + g j a₂) :
  (f.update i a).sum g + g i (f i) = f.sum g + g i a :=
begin
  rw [update_eq_erase_add_single, sum_add_index' hg hgg],
  conv_rhs { rw ← finsupp.update_self f i },
  rw [update_eq_erase_add_single, sum_add_index' hg hgg, add_assoc, add_assoc],
  congr' 1,
  rw [add_comm, sum_single_index (hg _), sum_single_index (hg _)],
end

lemma map_domain_inj_on (S : set α) {f : α → β}
  (hf : set.inj_on f S) :
  set.inj_on (map_domain f : (α →₀ M) → (β →₀ M)) {w | (w.support : set α) ⊆ S} :=
begin
  intros v₁ hv₁ v₂ hv₂ eq,
  ext a,
  classical,
  by_cases h : a ∈ v₁.support ∪ v₂.support,
  { rw [← map_domain_apply' S _ hv₁ hf _, ← map_domain_apply' S _ hv₂ hf _, eq];
    { apply set.union_subset hv₁ hv₂,
      exact_mod_cast h, }, },
  { simp only [decidable.not_or_iff_and_not, mem_union, not_not, mem_support_iff] at h,
    simp [h], },
end

lemma equiv_map_domain_eq_map_domain {M} [add_comm_monoid M] (f : α ≃ β) (l : α →₀ M) :
  equiv_map_domain f l = map_domain f l := by ext x; simp [map_domain_equiv_apply]

end map_domain


/-! ### Declarations about `comap_domain` -/

section comap_domain

/-- Given `f : α → β`, `l : β →₀ M` and a proof `hf` that `f` is injective on
the preimage of `l.support`, `comap_domain f l hf` is the finitely supported function
from `α` to `M` given by composing `l` with `f`. -/
@[simps support]
def comap_domain [has_zero M] (f : α → β) (l : β →₀ M) (hf : set.inj_on f (f ⁻¹' ↑l.support)) :
  α →₀ M :=
{ support := l.support.preimage f hf,
  to_fun := (λ a, l (f a)),
  mem_support_to_fun :=
    begin
      intros a,
      simp only [finset.mem_def.symm, finset.mem_preimage],
      exact l.mem_support_to_fun (f a),
    end }

@[simp]
lemma comap_domain_apply [has_zero M] (f : α → β) (l : β →₀ M)
  (hf : set.inj_on f (f ⁻¹' ↑l.support)) (a : α) :
  comap_domain f l hf a = l (f a) :=
rfl

lemma sum_comap_domain [has_zero M] [add_comm_monoid N]
  (f : α → β) (l : β →₀ M) (g : β → M → N)
  (hf : set.bij_on f (f ⁻¹' ↑l.support) ↑l.support) :
  (comap_domain f l hf.inj_on).sum (g ∘ f) = l.sum g :=
begin
  simp only [sum, comap_domain_apply, (∘)],
  simp [comap_domain, finset.sum_preimage_of_bij f _ _ (λ x, g x (l x))],
end

lemma eq_zero_of_comap_domain_eq_zero [add_comm_monoid M]
  (f : α → β) (l : β →₀ M) (hf : set.bij_on f (f ⁻¹' ↑l.support) ↑l.support) :
   comap_domain f l hf.inj_on = 0 → l = 0 :=
begin
  rw [← support_eq_empty, ← support_eq_empty, comap_domain],
  simp only [finset.ext_iff, finset.not_mem_empty, iff_false, mem_preimage],
  assume h a ha,
  cases hf.2.2 ha with b hb,
  exact h b (hb.2.symm ▸ ha)
end

section f_injective

section has_zero
variables [has_zero M]

/-- Note the `hif` argument is needed for this to work in `rw`. -/
@[simp] lemma comap_domain_zero (f : α → β)
  (hif : set.inj_on f (f ⁻¹' ↑((0 : β →₀ M).support)) := set.inj_on_empty _) :
  comap_domain f (0 : β →₀ M) hif = (0 : α →₀ M) :=
by { ext, refl }

@[simp] lemma comap_domain_single (f : α → β) (a : α) (m : M)
  (hif : set.inj_on f (f ⁻¹' (single (f a) m).support)) :
  comap_domain f (finsupp.single (f a) m) hif = finsupp.single a m :=
begin
  rcases eq_or_ne m 0 with rfl | hm,
  { simp only [single_zero, comap_domain_zero] },
  { rw [eq_single_iff, comap_domain_apply, comap_domain_support, ← finset.coe_subset, coe_preimage,
      support_single_ne_zero _ hm, coe_singleton, coe_singleton, single_eq_same],
    rw [support_single_ne_zero _ hm, coe_singleton] at hif,
    exact ⟨λ x hx, hif hx rfl hx, rfl⟩ }
end

end has_zero

section add_zero_class
variables [add_zero_class M] {f : α → β}

lemma comap_domain_add (v₁ v₂ : β →₀ M)
  (hv₁ : set.inj_on f (f ⁻¹' ↑(v₁.support))) (hv₂ : set.inj_on f (f ⁻¹' ↑(v₂.support)))
  (hv₁₂ : set.inj_on f (f ⁻¹' ↑((v₁ + v₂).support))) :
  comap_domain f (v₁ + v₂) hv₁₂ = comap_domain f v₁ hv₁ + comap_domain f v₂ hv₂ :=
by { ext, simp only [comap_domain_apply, coe_add, pi.add_apply] }

/-- A version of `finsupp.comap_domain_add` that's easier to use. -/
lemma comap_domain_add_of_injective (hf : function.injective f) (v₁ v₂ : β →₀ M) :
  comap_domain f (v₁ + v₂) (hf.inj_on _)
    = comap_domain f v₁ (hf.inj_on _) + comap_domain f v₂ (hf.inj_on _) :=
comap_domain_add _ _ _ _ _

/-- `finsupp.comap_domain` is an `add_monoid_hom`. -/
@[simps]
def comap_domain.add_monoid_hom (hf : function.injective f) : (β →₀ M) →+ (α →₀ M) :=
{ to_fun := λ x, comap_domain f x (hf.inj_on _),
  map_zero' := comap_domain_zero f,
  map_add' := comap_domain_add_of_injective hf }

end add_zero_class

variables [add_comm_monoid M] (f : α → β)

lemma map_domain_comap_domain
  (hf : function.injective f) (l : β →₀ M) (hl : ↑l.support ⊆ set.range f) :
  map_domain f (comap_domain f l (hf.inj_on _)) = l :=
begin
  ext a,
  by_cases h_cases: a ∈ set.range f,
  { rcases set.mem_range.1 h_cases with ⟨b, hb⟩,
    rw [hb.symm, map_domain_apply hf, comap_domain_apply] },
  { rw map_domain_notin_range _ _ h_cases,
    by_contra h_contr,
    apply h_cases (hl $ finset.mem_coe.2 $ mem_support_iff.2 $ λ h, h_contr h.symm) }
end

end f_injective

end comap_domain


/-! ### Declarations about finitely supported functions whose support is an `option` type -/

section option

/-- Restrict a finitely supported function on `option α` to a finitely supported function on `α`. -/
def some [has_zero M] (f : option α →₀ M) : α →₀ M :=
f.comap_domain option.some (λ _, by simp)

@[simp] lemma some_apply [has_zero M] (f : option α →₀ M) (a : α) :
  f.some a = f (option.some a) := rfl

@[simp] lemma some_zero [has_zero M] : (0 : option α →₀ M).some = 0 :=
by { ext, simp, }

@[simp] lemma some_add [add_comm_monoid M] (f g : option α →₀ M) : (f + g).some = f.some + g.some :=
by { ext, simp, }

@[simp] lemma some_single_none [has_zero M] (m : M) : (single none m : option α →₀ M).some = 0 :=
by { ext, simp, }

@[simp] lemma some_single_some [has_zero M] (a : α) (m : M) :
  (single (option.some a) m : option α →₀ M).some = single a m :=
by { classical, ext b, simp [single_apply], }

@[to_additive]
lemma prod_option_index [add_comm_monoid M] [comm_monoid N]
  (f : option α →₀ M) (b : option α → M → N) (h_zero : ∀ o, b o 0 = 1)
  (h_add : ∀ o m₁ m₂, b o (m₁ + m₂) = b o m₁ * b o m₂) :
  f.prod b = b none (f none) * f.some.prod (λ a, b (option.some a)) :=
begin
  classical,
  apply induction_linear f,
  { simp [some_zero, h_zero], },
  { intros f₁ f₂ h₁ h₂,
    rw [finsupp.prod_add_index, h₁, h₂, some_add, finsupp.prod_add_index],
    simp only [h_add, pi.add_apply, finsupp.coe_add],
    rw mul_mul_mul_comm,
    all_goals { simp [h_zero, h_add], }, },
  { rintros (_|a) m; simp [h_zero, h_add], }
end

lemma sum_option_index_smul [semiring R] [add_comm_monoid M] [module R M]
  (f : option α →₀ R) (b : option α → M) :
  f.sum (λ o r, r • b o) =
    f none • b none + f.some.sum (λ a r, r • b (option.some a)) :=
f.sum_option_index _ (λ _, zero_smul _ _) (λ _ _ _, add_smul _ _ _)

end option

/-! ### Declarations about `filter` -/

section filter
section has_zero
variables [has_zero M] (p : α → Prop) (f : α →₀ M)

/--
`filter p f` is the finitely supported function that is `f a` if `p a` is true and 0 otherwise. -/
def filter (p : α → Prop) (f : α →₀ M) : α →₀ M :=
{ to_fun := λ a, by haveI := classical.dec_pred p; exact if p a then f a else 0,
  support := by haveI := classical.dec_pred p; exact f.support.filter (λ a, p a),
  mem_support_to_fun := λ a, by split_ifs; { simp only [h, mem_filter, mem_support_iff], tauto } }

lemma filter_apply (a : α) [D : decidable (p a)] : f.filter p a = if p a then f a else 0 :=
by rw subsingleton.elim D; refl

lemma filter_eq_indicator : ⇑(f.filter p) = set.indicator {x | p x} f := rfl

lemma filter_eq_zero_iff : f.filter p = 0 ↔ ∀ x, p x → f x = 0 :=
by simp only [fun_like.ext_iff, filter_eq_indicator, zero_apply, set.indicator_apply_eq_zero,
  set.mem_set_of_eq]

lemma filter_eq_self_iff : f.filter p = f ↔ ∀ x, f x ≠ 0 → p x :=
by simp only [fun_like.ext_iff, filter_eq_indicator, set.indicator_apply_eq_self, set.mem_set_of_eq,
  not_imp_comm]

@[simp] lemma filter_apply_pos {a : α} (h : p a) : f.filter p a = f a :=
by { classical, convert if_pos h }

@[simp] lemma filter_apply_neg {a : α} (h : ¬ p a) : f.filter p a = 0 :=
by { classical, convert if_neg h }

@[simp] lemma support_filter [D : decidable_pred p] : (f.filter p).support = f.support.filter p :=
by rw subsingleton.elim D; refl

lemma filter_zero : (0 : α →₀ M).filter p = 0 :=
by { classical, rw [← support_eq_empty, support_filter, support_zero, finset.filter_empty] }

@[simp] lemma filter_single_of_pos {a : α} {b : M} (h : p a) :
  (single a b).filter p = single a b :=
(filter_eq_self_iff _ _).2 $ λ x hx, (single_apply_ne_zero.1 hx).1.symm ▸ h

@[simp] lemma filter_single_of_neg {a : α} {b : M} (h : ¬ p a) : (single a b).filter p = 0 :=
(filter_eq_zero_iff _ _).2 $ λ x hpx, single_apply_eq_zero.2 $ λ hxa, absurd hpx (hxa.symm ▸ h)

@[to_additive] lemma prod_filter_index [comm_monoid N] (g : α → M → N) :
  (f.filter p).prod g = ∏ x in (f.filter p).support, g x (f x) :=
begin
  classical,
  refine finset.prod_congr rfl (λ x hx, _),
  rw [support_filter, finset.mem_filter] at hx,
  rw [filter_apply_pos _ _ hx.2]
end

@[simp, to_additive] lemma prod_filter_mul_prod_filter_not [comm_monoid N] (g : α → M → N) :
  (f.filter p).prod g * (f.filter (λ a, ¬ p a)).prod g = f.prod g :=
begin
  classical,
  simp_rw [prod_filter_index, support_filter, prod_filter_mul_prod_filter_not, finsupp.prod]
end

@[simp, to_additive] lemma prod_div_prod_filter [comm_group G] (g : α → M → G) :
  f.prod g / (f.filter p).prod g = (f.filter (λ a, ¬p a)).prod g :=
div_eq_of_eq_mul' (prod_filter_mul_prod_filter_not _ _ _).symm

end has_zero

lemma filter_pos_add_filter_neg [add_zero_class M] (f : α →₀ M) (p : α → Prop) :
  f.filter p + f.filter (λa, ¬ p a) = f :=
coe_fn_injective $ set.indicator_self_add_compl {x | p x} f

end filter

/-! ### Declarations about `frange` -/

section frange
variables [has_zero M]

/-- `frange f` is the image of `f` on the support of `f`. -/
def frange (f : α →₀ M) : finset M :=
by haveI := classical.dec_eq M; exact finset.image f f.support

theorem mem_frange {f : α →₀ M} {y : M} :
  y ∈ f.frange ↔ y ≠ 0 ∧ ∃ x, f x = y :=
by classical; exact finset.mem_image.trans
⟨λ ⟨x, hx1, hx2⟩, ⟨hx2 ▸ mem_support_iff.1 hx1, x, hx2⟩,
λ ⟨hy, x, hx⟩, ⟨x, mem_support_iff.2 (hx.symm ▸ hy), hx⟩⟩

theorem zero_not_mem_frange {f : α →₀ M} : (0:M) ∉ f.frange :=
λ H, (mem_frange.1 H).1 rfl

theorem frange_single {x : α} {y : M} : frange (single x y) ⊆ {y} :=
λ r hr, let ⟨t, ht1, ht2⟩ := mem_frange.1 hr in ht2 ▸ begin
  classical,
  rw single_apply at ht2 ⊢,
  split_ifs at ht2 ⊢,
  { exact finset.mem_singleton_self _ },
  { exact (t ht2.symm).elim }
end

end frange

/-! ### Declarations about `subtype_domain` -/

section subtype_domain

section zero

variables [has_zero M] {p : α → Prop}

/--
`subtype_domain p f` is the restriction of the finitely supported function `f` to subtype `p`. -/
def subtype_domain (p : α → Prop) (f : α →₀ M) : (subtype p →₀ M) :=
{ support := by haveI := classical.dec_pred p; exact f.support.subtype p,
  to_fun := f ∘ coe,
  mem_support_to_fun := λ a, by simp only [mem_subtype, mem_support_iff] }

@[simp] lemma support_subtype_domain [D : decidable_pred p] {f : α →₀ M} :
  (subtype_domain p f).support = f.support.subtype p :=
by rw subsingleton.elim D; refl

@[simp] lemma subtype_domain_apply {a : subtype p} {v : α →₀ M} :
  (subtype_domain p v) a = v (a.val) :=
rfl

@[simp] lemma subtype_domain_zero : subtype_domain p (0 : α →₀ M) = 0 :=
rfl

lemma subtype_domain_eq_zero_iff' {f : α →₀ M} :
  f.subtype_domain p = 0 ↔ ∀ x, p x → f x = 0 :=
begin
  classical,
  simp_rw [← support_eq_empty, support_subtype_domain, subtype_eq_empty, not_mem_support_iff]
end

lemma subtype_domain_eq_zero_iff {f : α →₀ M} (hf : ∀ x ∈ f.support , p x) :
  f.subtype_domain p = 0 ↔ f = 0 :=
subtype_domain_eq_zero_iff'.trans ⟨λ H, ext $ λ x,
  by classical; exact
    if hx : p x then H x hx else not_mem_support_iff.1 $ mt (hf x) hx, λ H x _, by simp [H]⟩

@[to_additive]
lemma prod_subtype_domain_index [comm_monoid N] {v : α →₀ M}
  {h : α → M → N} (hp : ∀x∈v.support, p x) :
  (v.subtype_domain p).prod (λa b, h a b) = v.prod h :=
prod_bij (λp _, p.val)
  (λ _, by classical; exact mem_subtype.1)
  (λ _ _, rfl)
  (λ _ _ _ _, subtype.eq)
  (λ b hb, ⟨⟨b, hp b hb⟩, by classical; exact mem_subtype.2 hb, rfl⟩)

end zero

section add_zero_class
variables [add_zero_class M] {p : α → Prop} {v v' : α →₀ M}

@[simp] lemma subtype_domain_add {v v' : α →₀ M} :
  (v + v').subtype_domain p = v.subtype_domain p + v'.subtype_domain p :=
ext $ λ _, rfl

/-- `subtype_domain` but as an `add_monoid_hom`. -/
def subtype_domain_add_monoid_hom : (α →₀ M) →+ subtype p →₀ M :=
{ to_fun := subtype_domain p,
  map_zero' := subtype_domain_zero,
  map_add' := λ _ _, subtype_domain_add }

/-- `finsupp.filter` as an `add_monoid_hom`. -/
def filter_add_hom (p : α → Prop) : (α →₀ M) →+ (α →₀ M) :=
{ to_fun := filter p,
  map_zero' := filter_zero p,
  map_add' := λ f g, coe_fn_injective $ set.indicator_add {x | p x} f g }

@[simp] lemma filter_add {v v' : α →₀ M} : (v + v').filter p = v.filter p + v'.filter p :=
(filter_add_hom p).map_add v v'

end add_zero_class

section comm_monoid
variables [add_comm_monoid M] {p : α → Prop}

lemma subtype_domain_sum {s : finset ι} {h : ι → α →₀ M} :
  (∑ c in s, h c).subtype_domain p = ∑ c in s, (h c).subtype_domain p :=
(subtype_domain_add_monoid_hom : _ →+ subtype p →₀ M).map_sum _ s

lemma subtype_domain_finsupp_sum [has_zero N] {s : β →₀ N} {h : β → N → α →₀ M} :
  (s.sum h).subtype_domain p = s.sum (λc d, (h c d).subtype_domain p) :=
subtype_domain_sum

lemma filter_sum (s : finset ι) (f : ι → α →₀ M) :
  (∑ a in s, f a).filter p = ∑ a in s, filter p (f a) :=
(filter_add_hom p : (α →₀ M) →+ _).map_sum f s

lemma filter_eq_sum (p : α → Prop) [D : decidable_pred p] (f : α →₀ M) :
  f.filter p = ∑ i in f.support.filter p, single i (f i) :=
(f.filter p).sum_single.symm.trans $ finset.sum_congr (by rw subsingleton.elim D; refl) $
  λ x hx, by rw [filter_apply_pos _ _ (mem_filter.1 hx).2]

end comm_monoid

section group
variables [add_group G] {p : α → Prop} {v v' : α →₀ G}

@[simp] lemma subtype_domain_neg : (- v).subtype_domain p = - v.subtype_domain p :=
ext $ λ _, rfl

@[simp] lemma subtype_domain_sub :
  (v - v').subtype_domain p = v.subtype_domain p - v'.subtype_domain p :=
ext $ λ _, rfl

@[simp] lemma single_neg (a : α) (b : G) : single a (-b) = -single a b :=
(single_add_hom a : G →+ _).map_neg b

@[simp] lemma single_sub (a : α) (b₁ b₂ : G) : single a (b₁ - b₂) = single a b₁ - single a b₂ :=
(single_add_hom a : G →+ _).map_sub b₁ b₂

@[simp] lemma erase_neg (a : α) (f : α →₀ G) : erase a (-f) = -erase a f :=
(erase_add_hom a : (_ →₀ G) →+ _).map_neg f

@[simp] lemma erase_sub (a : α) (f₁ f₂ : α →₀ G) : erase a (f₁ - f₂) = erase a f₁ - erase a f₂ :=
(erase_add_hom a : (_ →₀ G) →+ _).map_sub f₁ f₂

@[simp] lemma filter_neg (p : α → Prop) (f : α →₀ G) : filter p (-f) = -filter p f :=
(filter_add_hom p : (_ →₀ G) →+ _).map_neg f

@[simp] lemma filter_sub (p : α → Prop) (f₁ f₂ : α →₀ G) :
  filter p (f₁ - f₂) = filter p f₁ - filter p f₂ :=
(filter_add_hom p : (_ →₀ G) →+ _).map_sub f₁ f₂

end group

end subtype_domain

lemma mem_support_multiset_sum [add_comm_monoid M]
  {s : multiset (α →₀ M)} (a : α) :
  a ∈ s.sum.support → ∃f∈s, a ∈ (f : α →₀ M).support :=
multiset.induction_on s false.elim
  begin
    assume f s ih ha,
    by_cases a ∈ f.support,
    { exact ⟨f, multiset.mem_cons_self _ _, h⟩ },
    { simp only [multiset.sum_cons, mem_support_iff, add_apply,
        not_mem_support_iff.1 h, zero_add] at ha,
      rcases ih (mem_support_iff.2 ha) with ⟨f', h₀, h₁⟩,
      exact ⟨f', multiset.mem_cons_of_mem h₀, h₁⟩ }
  end

lemma mem_support_finset_sum [add_comm_monoid M]
  {s : finset ι} {h : ι → α →₀ M} (a : α) (ha : a ∈ (∑ c in s, h c).support) :
  ∃ c ∈ s, a ∈ (h c).support :=
let ⟨f, hf, hfa⟩ := mem_support_multiset_sum a ha in
let ⟨c, hc, eq⟩ := multiset.mem_map.1 hf in
⟨c, hc, eq.symm ▸ hfa⟩


/-! ### Declarations about `curry` and `uncurry` -/

section curry_uncurry

variables [add_comm_monoid M] [add_comm_monoid N]

/-- Given a finitely supported function `f` from a product type `α × β` to `γ`,
`curry f` is the "curried" finitely supported function from `α` to the type of
finitely supported functions from `β` to `γ`. -/
protected def curry (f : (α × β) →₀ M) : α →₀ (β →₀ M) :=
f.sum $ λp c, single p.1 (single p.2 c)

@[simp] lemma curry_apply (f : (α × β) →₀ M) (x : α) (y : β) :
  f.curry x y = f (x, y) :=
begin
  classical,
  have : ∀ (b : α × β), single b.fst (single b.snd (f b)) x y = if b = (x, y) then f b else 0,
  { rintros ⟨b₁, b₂⟩,
    simp [single_apply, ite_apply, prod.ext_iff, ite_and],
    split_ifs; simp [single_apply, *] },
  rw [finsupp.curry, sum_apply, sum_apply, finsupp.sum, finset.sum_eq_single, this, if_pos rfl],
  { intros b hb b_ne, rw [this b, if_neg b_ne] },
  { intros hxy, rw [this (x, y), if_pos rfl, not_mem_support_iff.mp hxy] }
end

lemma sum_curry_index (f : (α × β) →₀ M) (g : α → β → M → N)
  (hg₀ : ∀ a b, g a b 0 = 0) (hg₁ : ∀a b c₀ c₁, g a b (c₀ + c₁) = g a b c₀ + g a b c₁) :
  f.curry.sum (λa f, f.sum (g a)) = f.sum (λp c, g p.1 p.2 c) :=
begin
  rw [finsupp.curry],
  transitivity,
  { exact sum_sum_index (assume a, sum_zero_index)
      (assume a b₀ b₁, sum_add_index' (assume a, hg₀ _ _) (assume c d₀ d₁, hg₁ _ _ _ _)) },
  congr, funext p c,
  transitivity,
  { exact sum_single_index sum_zero_index },
  exact sum_single_index (hg₀ _ _)
end

/-- Given a finitely supported function `f` from `α` to the type of
finitely supported functions from `β` to `M`,
`uncurry f` is the "uncurried" finitely supported function from `α × β` to `M`. -/
protected def uncurry (f : α →₀ (β →₀ M)) : (α × β) →₀ M :=
f.sum $ λa g, g.sum $ λb c, single (a, b) c

/-- `finsupp_prod_equiv` defines the `equiv` between `((α × β) →₀ M)` and `(α →₀ (β →₀ M))` given by
currying and uncurrying. -/
def finsupp_prod_equiv : ((α × β) →₀ M) ≃ (α →₀ (β →₀ M)) :=
{ to_fun := finsupp.curry,
  inv_fun := finsupp.uncurry,
  left_inv := λ f, begin
    rw [finsupp.uncurry, sum_curry_index],
    { simp_rw [prod.mk.eta, sum_single], },
    { intros, apply single_zero },
    { intros, apply single_add }
  end,
  right_inv := λ f, by simp only [
    finsupp.curry, finsupp.uncurry, sum_sum_index, sum_zero_index, sum_add_index,
    sum_single_index, single_zero, single_add, eq_self_iff_true, forall_true_iff,
    forall_3_true_iff, prod.mk.eta, (single_sum _ _ _).symm, sum_single] }

lemma filter_curry (f : α × β →₀ M) (p : α → Prop) :
  (f.filter (λa:α×β, p a.1)).curry = f.curry.filter p :=
begin
  classical,
  rw [finsupp.curry, finsupp.curry, finsupp.sum, finsupp.sum, filter_sum, support_filter,
    sum_filter],
  refine finset.sum_congr rfl _,
  rintros ⟨a₁, a₂⟩ ha,
  dsimp only,
  split_ifs,
  { rw [filter_apply_pos, filter_single_of_pos]; exact h },
  { rwa [filter_single_of_neg] }
end

lemma support_curry [decidable_eq α] (f : α × β →₀ M) :
  f.curry.support ⊆ f.support.image prod.fst :=
begin
  rw ← finset.bUnion_singleton,
  refine finset.subset.trans support_sum _,
  refine finset.bUnion_mono (assume a _, support_single_subset)
end

end curry_uncurry

/-! ### Declarations about finitely supported functions whose support is a `sum` type -/

section sum

/-- `finsupp.sum_elim f g` maps `inl x` to `f x` and `inr y` to `g y`. -/
def sum_elim {α β γ : Type*} [has_zero γ]
  (f : α →₀ γ) (g : β →₀ γ) : α ⊕ β →₀ γ :=
on_finset
  (by haveI := classical.dec_eq α; haveI := classical.dec_eq β;
    exact (f.support.map ⟨_, sum.inl_injective⟩) ∪ g.support.map ⟨_, sum.inr_injective⟩)
  (sum.elim f g)
  (λ ab h, by { cases ab with a b; simp only [sum.elim_inl, sum.elim_inr] at h; simpa })

@[simp] lemma coe_sum_elim {α β γ : Type*} [has_zero γ]
  (f : α →₀ γ) (g : β →₀ γ) : ⇑(sum_elim f g) = sum.elim f g := rfl

lemma sum_elim_apply {α β γ : Type*} [has_zero γ]
  (f : α →₀ γ) (g : β →₀ γ) (x : α ⊕ β) : sum_elim f g x = sum.elim f g x := rfl

lemma sum_elim_inl {α β γ : Type*} [has_zero γ]
  (f : α →₀ γ) (g : β →₀ γ) (x : α) : sum_elim f g (sum.inl x) = f x := rfl

lemma sum_elim_inr {α β γ : Type*} [has_zero γ]
  (f : α →₀ γ) (g : β →₀ γ) (x : β) : sum_elim f g (sum.inr x) = g x := rfl

/-- The equivalence between `(α ⊕ β) →₀ γ` and `(α →₀ γ) × (β →₀ γ)`.

This is the `finsupp` version of `equiv.sum_arrow_equiv_prod_arrow`. -/
@[simps apply symm_apply]
def sum_finsupp_equiv_prod_finsupp {α β γ : Type*} [has_zero γ] :
  ((α ⊕ β) →₀ γ) ≃ (α →₀ γ) × (β →₀ γ) :=
{ to_fun := λ f,
    ⟨f.comap_domain sum.inl (sum.inl_injective.inj_on _),
     f.comap_domain sum.inr (sum.inr_injective.inj_on _)⟩,
  inv_fun := λ fg, sum_elim fg.1 fg.2,
  left_inv := λ f, by { ext ab, cases ab with a b; simp },
  right_inv := λ fg, by { ext; simp } }

lemma fst_sum_finsupp_equiv_prod_finsupp {α β γ : Type*} [has_zero γ]
  (f : (α ⊕ β) →₀ γ) (x : α) :
  (sum_finsupp_equiv_prod_finsupp f).1 x = f (sum.inl x) :=
rfl

lemma snd_sum_finsupp_equiv_prod_finsupp {α β γ : Type*} [has_zero γ]
  (f : (α ⊕ β) →₀ γ) (y : β) :
  (sum_finsupp_equiv_prod_finsupp f).2 y = f (sum.inr y) :=
rfl

lemma sum_finsupp_equiv_prod_finsupp_symm_inl {α β γ : Type*} [has_zero γ]
  (fg : (α →₀ γ) × (β →₀ γ)) (x : α) :
  (sum_finsupp_equiv_prod_finsupp.symm fg) (sum.inl x) = fg.1 x :=
rfl

lemma sum_finsupp_equiv_prod_finsupp_symm_inr {α β γ : Type*} [has_zero γ]
  (fg : (α →₀ γ) × (β →₀ γ)) (y : β) :
  (sum_finsupp_equiv_prod_finsupp.symm fg) (sum.inr y) = fg.2 y :=
rfl

variables [add_monoid M]

/-- The additive equivalence between `(α ⊕ β) →₀ M` and `(α →₀ M) × (β →₀ M)`.

This is the `finsupp` version of `equiv.sum_arrow_equiv_prod_arrow`. -/
@[simps apply symm_apply] def sum_finsupp_add_equiv_prod_finsupp {α β : Type*} :
  ((α ⊕ β) →₀ M) ≃+ (α →₀ M) × (β →₀ M) :=
{ map_add' :=
    by { intros, ext;
          simp only [equiv.to_fun_as_coe, prod.fst_add, prod.snd_add, add_apply,
              snd_sum_finsupp_equiv_prod_finsupp, fst_sum_finsupp_equiv_prod_finsupp] },
  .. sum_finsupp_equiv_prod_finsupp }

lemma fst_sum_finsupp_add_equiv_prod_finsupp {α β : Type*}
  (f : (α ⊕ β) →₀ M) (x : α) :
  (sum_finsupp_add_equiv_prod_finsupp f).1 x = f (sum.inl x) :=
rfl

lemma snd_sum_finsupp_add_equiv_prod_finsupp {α β : Type*}
  (f : (α ⊕ β) →₀ M) (y : β) :
  (sum_finsupp_add_equiv_prod_finsupp f).2 y = f (sum.inr y) :=
rfl

lemma sum_finsupp_add_equiv_prod_finsupp_symm_inl {α β : Type*}
  (fg : (α →₀ M) × (β →₀ M)) (x : α) :
  (sum_finsupp_add_equiv_prod_finsupp.symm fg) (sum.inl x) = fg.1 x :=
rfl

lemma sum_finsupp_add_equiv_prod_finsupp_symm_inr {α β : Type*}
  (fg : (α →₀ M) × (β →₀ M)) (y : β) :
  (sum_finsupp_add_equiv_prod_finsupp.symm fg) (sum.inr y) = fg.2 y :=
rfl

end sum

/-! ### Declarations about scalar multiplication -/

section
variables [has_zero M] [monoid_with_zero R] [mul_action_with_zero R M]

@[simp] lemma single_smul (a b : α) (f : α → M) (r : R) :
  (single a r b) • (f a) = single a (r • f b) b :=
by by_cases a = b; simp [h]

end

section
variables [monoid G] [mul_action G α] [add_comm_monoid M]

/-- Scalar multiplication acting on the domain.

This is not an instance as it would conflict with the action on the range.
See the `instance_diamonds` test for examples of such conflicts. -/
def comap_has_smul : has_smul G (α →₀ M) :=
{ smul := λ g, map_domain ((•) g) }

local attribute [instance] comap_has_smul

lemma comap_smul_def (g : G) (f : α →₀ M) : g • f = map_domain ((•) g) f := rfl

@[simp] lemma comap_smul_single (g : G) (a : α) (b : M) :
  g • single a b = single (g • a) b :=
map_domain_single

/-- `finsupp.comap_has_smul` is multiplicative -/
def comap_mul_action : mul_action G (α →₀ M) :=
{ one_smul := λ f, by  rw [comap_smul_def, one_smul_eq_id, map_domain_id],
  mul_smul := λ g g' f, by rw [comap_smul_def, comap_smul_def, comap_smul_def, ←comp_smul_left,
    map_domain_comp], }

local attribute [instance] comap_mul_action

/-- `finsupp.comap_has_smul` is distributive -/
def comap_distrib_mul_action :
  distrib_mul_action G (α →₀ M) :=
{ smul_zero := λ g, by { ext, dsimp [(•)], simp, },
  smul_add := λ g f f', by { ext, dsimp [(•)], simp [map_domain_add], }, }

end

section
variables [group G] [mul_action G α] [add_comm_monoid M]

local attribute [instance] comap_has_smul comap_mul_action comap_distrib_mul_action

/-- When `G` is a group, `finsupp.comap_has_smul` acts by precomposition with the action of `g⁻¹`.
-/
@[simp] lemma comap_smul_apply (g : G) (f : α →₀ M) (a : α) :
  (g • f) a = f (g⁻¹ • a) :=
begin
  conv_lhs { rw ←smul_inv_smul g a },
  exact map_domain_apply (mul_action.injective g) _ (g⁻¹ • a),
end

end

section

instance [has_zero M] [smul_zero_class R M] : smul_zero_class R (α →₀ M) :=
{ smul := λ a v, v.map_range ((•) a) (smul_zero _),
  smul_zero := λ a, by { ext, apply smul_zero } }

/-!
Throughout this section, some `monoid` and `semiring` arguments are specified with `{}` instead of
`[]`. See note [implicit instance arguments].
-/

@[simp] lemma coe_smul [add_monoid M] [distrib_smul R M]
  (b : R) (v : α →₀ M) : ⇑(b • v) = b • v := rfl
lemma smul_apply [add_monoid M] [distrib_smul R M]
  (b : R) (v : α →₀ M) (a : α) : (b • v) a = b • (v a) := rfl

lemma _root_.is_smul_regular.finsupp [add_monoid M] [distrib_smul R M] {k : R}
  (hk : is_smul_regular M k) : is_smul_regular (α →₀ M) k :=
λ _ _ h, ext $ λ i, hk (congr_fun h i)

instance [nonempty α] [add_monoid M] [distrib_smul R M] [has_faithful_smul R M] :
  has_faithful_smul R (α →₀ M) :=
{ eq_of_smul_eq_smul := λ r₁ r₂ h, let ⟨a⟩ := ‹nonempty α› in eq_of_smul_eq_smul $ λ m : M,
    by simpa using congr_fun (h (single a m)) a }

variables (α M)

instance [add_zero_class M] [distrib_smul R M] : distrib_smul R (α →₀ M) :=
{ smul      := (•),
  smul_add  := λ a x y, ext $ λ _, smul_add _ _ _,
  smul_zero := λ x, ext $ λ _, smul_zero _ }

instance [monoid R] [add_monoid M] [distrib_mul_action R M] : distrib_mul_action R (α →₀ M) :=
{ smul      := (•),
  one_smul  := λ x, ext $ λ _, one_smul _ _,
  mul_smul  := λ r s x, ext $ λ _, mul_smul _ _ _,
  ..finsupp.distrib_smul _ _ }

instance [monoid R] [monoid S] [add_monoid M] [distrib_mul_action R M] [distrib_mul_action S M]
  [has_smul R S] [is_scalar_tower R S M] :
  is_scalar_tower R S (α →₀ M) :=
{ smul_assoc := λ r s a, ext $ λ _, smul_assoc _ _ _ }

instance [monoid R] [monoid S] [add_monoid M] [distrib_mul_action R M] [distrib_mul_action S M]
  [smul_comm_class R S M] :
  smul_comm_class R S (α →₀ M) :=
{ smul_comm := λ r s a, ext $ λ _, smul_comm _ _ _ }

instance [monoid R] [add_monoid M] [distrib_mul_action R M] [distrib_mul_action Rᵐᵒᵖ M]
  [is_central_scalar R M] : is_central_scalar R (α →₀ M) :=
{ op_smul_eq_smul := λ r a, ext $ λ _, op_smul_eq_smul _ _ }

instance [semiring R] [add_comm_monoid M] [module R M] : module R (α →₀ M) :=
{ smul      := (•),
  zero_smul := λ x, ext $ λ _, zero_smul _ _,
  add_smul  := λ a x y, ext $ λ _, add_smul _ _ _,
  .. finsupp.distrib_mul_action α M }

variables {α M} {R}

lemma support_smul {_ : monoid R} [add_monoid M] [distrib_mul_action R M] {b : R} {g : α →₀ M} :
  (b • g).support ⊆ g.support :=
λ a, by { simp only [smul_apply, mem_support_iff, ne.def], exact mt (λ h, h.symm ▸ smul_zero _) }

@[simp]
lemma support_smul_eq [semiring R] [add_comm_monoid M] [module R M]
  [no_zero_smul_divisors R M] {b : R} (hb : b ≠ 0) {g : α →₀ M} :
  (b • g).support = g.support :=
finset.ext (λ a, by simp [finsupp.smul_apply, hb])

section

variables {p : α → Prop}

@[simp] lemma filter_smul {_ : monoid R} [add_monoid M] [distrib_mul_action R M]
  {b : R} {v : α →₀ M} : (b • v).filter p = b • v.filter p :=
coe_fn_injective $ set.indicator_const_smul {x | p x} b v

end

lemma map_domain_smul {_ : monoid R} [add_comm_monoid M] [distrib_mul_action R M]
   {f : α → β} (b : R) (v : α →₀ M) : map_domain f (b • v) = b • map_domain f v :=
map_domain_map_range _ _ _ _ (smul_add b)

@[simp] lemma smul_single {_ : monoid R} [add_monoid M] [distrib_mul_action R M]
  (c : R) (a : α) (b : M) : c • finsupp.single a b = finsupp.single a (c • b) :=
map_range_single

@[simp] lemma smul_single' {_ : semiring R}
  (c : R) (a : α) (b : R) : c • finsupp.single a b = finsupp.single a (c * b) :=
smul_single _ _ _

lemma map_range_smul {_ : monoid R} [add_monoid M] [distrib_mul_action R M]
  [add_monoid N] [distrib_mul_action R N]
  {f : M → N} {hf : f 0 = 0} (c : R) (v : α →₀ M) (hsmul : ∀ x, f (c • x) = c • f x) :
  map_range f hf (c • v) = c • map_range f hf v :=
begin
  erw ←map_range_comp,
  have : (f ∘ (•) c) = ((•) c ∘ f) := funext hsmul,
  simp_rw this,
  apply map_range_comp,
  rw [function.comp_apply, smul_zero, hf],
end

lemma smul_single_one [semiring R] (a : α) (b : R) : b • single a 1 = single a b :=
by rw [smul_single, smul_eq_mul, mul_one]

lemma comap_domain_smul [add_monoid M] [monoid R] [distrib_mul_action R M]
  {f : α → β} (r : R) (v : β →₀ M)
  (hfv : set.inj_on f (f ⁻¹' ↑(v.support)))
  (hfrv : set.inj_on f (f ⁻¹' ↑((r • v).support)) :=
    hfv.mono $ set.preimage_mono $ finset.coe_subset.mpr support_smul):
  comap_domain f (r • v) hfrv = r • comap_domain f v hfv :=
by { ext, refl }

/-- A version of `finsupp.comap_domain_smul` that's easier to use. -/
lemma comap_domain_smul_of_injective [add_monoid M] [monoid R] [distrib_mul_action R M]
  {f : α → β} (hf : function.injective f) (r : R) (v : β →₀ M) :
  comap_domain f (r • v) (hf.inj_on _) = r • comap_domain f v (hf.inj_on _) :=
comap_domain_smul _ _ _ _

end

lemma sum_smul_index [semiring R] [add_comm_monoid M] {g : α →₀ R} {b : R} {h : α → R → M}
  (h0 : ∀i, h i 0 = 0) : (b • g).sum h = g.sum (λi a, h i (b * a)) :=
finsupp.sum_map_range_index h0

lemma sum_smul_index' [add_monoid M] [distrib_smul R M] [add_comm_monoid N]
  {g : α →₀ M} {b : R} {h : α → M → N} (h0 : ∀i, h i 0 = 0) :
  (b • g).sum h = g.sum (λi c, h i (b • c)) :=
finsupp.sum_map_range_index h0

/-- A version of `finsupp.sum_smul_index'` for bundled additive maps. -/
lemma sum_smul_index_add_monoid_hom
  [add_monoid M] [add_comm_monoid N] [distrib_smul R M]
  {g : α →₀ M} {b : R} {h : α → M →+ N} :
  (b • g).sum (λ a, h a) = g.sum (λ i c, h i (b • c)) :=
sum_map_range_index (λ i, (h i).map_zero)

instance [semiring R] [add_comm_monoid M] [module R M] {ι : Type*}
  [no_zero_smul_divisors R M] : no_zero_smul_divisors R (ι →₀ M) :=
⟨λ c f h, or_iff_not_imp_left.mpr (λ hc, finsupp.ext
  (λ i, (smul_eq_zero.mp (finsupp.ext_iff.mp h i)).resolve_left hc))⟩

section distrib_mul_action_hom

variables [semiring R]
variables [add_comm_monoid M] [add_comm_monoid N] [distrib_mul_action R M] [distrib_mul_action R N]

/-- `finsupp.single` as a `distrib_mul_action_hom`.

See also `finsupp.lsingle` for the version as a linear map. -/
def distrib_mul_action_hom.single (a : α) : M →+[R] (α →₀ M) :=
{ map_smul' :=
    λ k m, by simp only [add_monoid_hom.to_fun_eq_coe, single_add_hom_apply, smul_single],
  .. single_add_hom a }

lemma distrib_mul_action_hom_ext {f g : (α →₀ M) →+[R] N}
  (h : ∀ (a : α) (m : M), f (single a m) = g (single a m)) :
  f = g :=
distrib_mul_action_hom.to_add_monoid_hom_injective $ add_hom_ext h

/-- See note [partially-applied ext lemmas]. -/
@[ext] lemma distrib_mul_action_hom_ext' {f g : (α →₀ M) →+[R] N}
  (h : ∀ (a : α), f.comp (distrib_mul_action_hom.single a) =
                  g.comp (distrib_mul_action_hom.single a)) :
  f = g :=
distrib_mul_action_hom_ext $ λ a, distrib_mul_action_hom.congr_fun (h a)

end distrib_mul_action_hom

section
variables [has_zero R]

/-- The `finsupp` version of `pi.unique`. -/
instance unique_of_right [subsingleton R] : unique (α →₀ R) := fun_like.coe_injective.unique

/-- The `finsupp` version of `pi.unique_of_is_empty`. -/
instance unique_of_left [is_empty α] : unique (α →₀ R) := fun_like.coe_injective.unique

end

/-- Given an `add_comm_monoid M` and `s : set α`, `restrict_support_equiv s M` is the `equiv`
between the subtype of finitely supported functions with support contained in `s` and
the type of finitely supported functions from `s`. -/
def restrict_support_equiv (s : set α) (M : Type*) [add_comm_monoid M] :
  {f : α →₀ M // ↑f.support ⊆ s } ≃ (s →₀ M) :=
{ to_fun := λ f, subtype_domain (λ x, x ∈ s) f.1,
  inv_fun := λ f, ⟨f.map_domain subtype.val, begin
    classical,
    refine set.subset.trans (finset.coe_subset.2 map_domain_support) _,
    rw [finset.coe_image, set.image_subset_iff],
    exact assume x hx, x.2,
  end⟩,
  left_inv := begin
    rintros ⟨f, hf⟩,
    apply subtype.eq,
    ext a,
    dsimp only,
    refine classical.by_cases (assume h : a ∈ set.range (subtype.val : s → α), _) (assume h, _),
    { rcases h with ⟨x, rfl⟩,
      rw [map_domain_apply subtype.val_injective, subtype_domain_apply] },
    { convert map_domain_notin_range _ _ h,
      rw [← not_mem_support_iff],
      refine mt _ h,
      exact assume ha, ⟨⟨a, hf ha⟩, rfl⟩ }
  end,
  right_inv := λ f, begin
    ext ⟨a, ha⟩,
    dsimp only,
    rw [subtype_domain_apply, map_domain_apply subtype.val_injective]
  end }

/-- Given `add_comm_monoid M` and `e : α ≃ β`, `dom_congr e` is the corresponding `equiv` between
`α →₀ M` and `β →₀ M`.

This is `finsupp.equiv_congr_left` as an `add_equiv`. -/
@[simps apply]
protected def dom_congr [add_comm_monoid M] (e : α ≃ β) : (α →₀ M) ≃+ (β →₀ M) :=
{ to_fun := equiv_map_domain e,
  inv_fun := equiv_map_domain e.symm,
  left_inv := λ v, begin
    simp only [← equiv_map_domain_trans, equiv.self_trans_symm],
    exact equiv_map_domain_refl _
  end,
  right_inv := begin
    assume v,
    simp only [← equiv_map_domain_trans, equiv.symm_trans_self],
    exact equiv_map_domain_refl _
  end,
  map_add' := λ a b, by simp only [equiv_map_domain_eq_map_domain]; exact map_domain_add }

@[simp] lemma dom_congr_refl [add_comm_monoid M] :
  finsupp.dom_congr (equiv.refl α) = add_equiv.refl (α →₀ M) :=
add_equiv.ext $ λ _, equiv_map_domain_refl _

@[simp] lemma dom_congr_symm [add_comm_monoid M] (e : α ≃ β) :
  (finsupp.dom_congr e).symm = (finsupp.dom_congr e.symm : (β →₀ M) ≃+ (α →₀ M)):=
add_equiv.ext $ λ _, rfl

@[simp] lemma dom_congr_trans [add_comm_monoid M] (e : α ≃ β) (f : β ≃ γ) :
  (finsupp.dom_congr e).trans (finsupp.dom_congr f) =
    (finsupp.dom_congr (e.trans f) : (α →₀ M) ≃+ _) :=
add_equiv.ext $ λ _, (equiv_map_domain_trans _ _ _).symm

end finsupp

namespace finsupp

/-! ### Declarations about sigma types -/

section sigma

variables {αs : ι → Type*} [has_zero M] (l : (Σ i, αs i) →₀ M)

/-- Given `l`, a finitely supported function from the sigma type `Σ (i : ι), αs i` to `M` and
an index element `i : ι`, `split l i` is the `i`th component of `l`,
a finitely supported function from `as i` to `M`.

This is the `finsupp` version of `sigma.curry`.
-/
def split (i : ι) : αs i →₀ M :=
l.comap_domain (sigma.mk i) (λ x1 x2 _ _ hx, heq_iff_eq.1 (sigma.mk.inj hx).2)

lemma split_apply (i : ι) (x : αs i) : split l i x = l ⟨i, x⟩ :=
begin
  dunfold split,
  rw comap_domain_apply
end

/-- Given `l`, a finitely supported function from the sigma type `Σ (i : ι), αs i` to `β`,
`split_support l` is the finset of indices in `ι` that appear in the support of `l`. -/
def split_support (l : (Σ i, αs i) →₀ M) : finset ι :=
by haveI := classical.dec_eq ι; exact l.support.image sigma.fst

lemma mem_split_support_iff_nonzero (i : ι) :
  i ∈ split_support l ↔ split l i ≠ 0 :=
begin
  rw [split_support, mem_image, ne.def, ← support_eq_empty, ← ne.def,
    ← finset.nonempty_iff_ne_empty, split, comap_domain, finset.nonempty],
  simp only [exists_prop, finset.mem_preimage, exists_and_distrib_right, exists_eq_right,
    mem_support_iff, sigma.exists, ne.def]
end

/-- Given `l`, a finitely supported function from the sigma type `Σ i, αs i` to `β` and
an `ι`-indexed family `g` of functions from `(αs i →₀ β)` to `γ`, `split_comp` defines a
finitely supported function from the index type `ι` to `γ` given by composing `g i` with
`split l i`. -/
def split_comp [has_zero N] (g : Π i, (αs i →₀ M) → N)
  (hg : ∀ i x, x = 0 ↔ g i x = 0) : ι →₀ N :=
{ support := split_support l,
  to_fun := λ i, g i (split l i),
  mem_support_to_fun :=
  begin
    intros i,
    rw [mem_split_support_iff_nonzero, not_iff_not, hg],
  end }

lemma sigma_support : l.support = l.split_support.sigma (λ i, (l.split i).support) :=
by simp only [finset.ext_iff, split_support, split, comap_domain, mem_image,
  mem_preimage, sigma.forall, mem_sigma]; tauto

lemma sigma_sum [add_comm_monoid N] (f : (Σ (i : ι), αs i) → M → N) :
  l.sum f = ∑ i in split_support l, (split l i).sum (λ (a : αs i) b, f ⟨i, a⟩ b) :=
by simp only [sum, sigma_support, sum_sigma, split_apply]

variables {η : Type*} [fintype η] {ιs : η → Type*} [has_zero α]

/-- On a `fintype η`, `finsupp.split` is an equivalence between `(Σ (j : η), ιs j) →₀ α`
and `Π j, (ιs j →₀ α)`.

This is the `finsupp` version of `equiv.Pi_curry`. -/
noncomputable def sigma_finsupp_equiv_pi_finsupp :
  ((Σ j, ιs j) →₀ α) ≃ Π j, (ιs j →₀ α) :=
{ to_fun := split,
  inv_fun := λ f, on_finset
    (finset.univ.sigma (λ j, (f j).support))
    (λ ji, f ji.1 ji.2)
    (λ g hg, finset.mem_sigma.mpr ⟨finset.mem_univ _, mem_support_iff.mpr hg⟩),
  left_inv := λ f, by { ext, simp [split] },
  right_inv := λ f, by { ext, simp [split] } }

@[simp] lemma sigma_finsupp_equiv_pi_finsupp_apply
  (f : (Σ j, ιs j) →₀ α) (j i) :
sigma_finsupp_equiv_pi_finsupp f j i = f ⟨j, i⟩ := rfl

/-- On a `fintype η`, `finsupp.split` is an additive equivalence between
`(Σ (j : η), ιs j) →₀ α` and `Π j, (ιs j →₀ α)`.

This is the `add_equiv` version of `finsupp.sigma_finsupp_equiv_pi_finsupp`.
-/
noncomputable def sigma_finsupp_add_equiv_pi_finsupp
  {α : Type*} {ιs : η → Type*} [add_monoid α] :
  ((Σ j, ιs j) →₀ α) ≃+ Π j, (ιs j →₀ α) :=
{ map_add' := λ f g, by { ext, simp },
  .. sigma_finsupp_equiv_pi_finsupp }

@[simp] lemma sigma_finsupp_add_equiv_pi_finsupp_apply
  {α : Type*} {ιs : η → Type*} [add_monoid α] (f : (Σ j, ιs j) →₀ α) (j i) :
sigma_finsupp_add_equiv_pi_finsupp f j i = f ⟨j, i⟩ := rfl

end sigma

/-! ### Meta declarations -/

/-- Stringify a `finsupp` as a sequence of `finsupp.single` terms.

Note this is `meta` as it has to choose some order for the terms. -/
meta instance (ι α : Type*) [has_zero α] [has_repr ι] [has_repr α] :
  has_repr (ι →₀ α) :=
{ repr := λ f,
  if f.support.card = 0 then "0"
  else " + ".intercalate $
    f.support.val.unquot.map (λ i, "finsupp.single " ++ repr i ++ " " ++ repr (f i)) }

end finsupp
