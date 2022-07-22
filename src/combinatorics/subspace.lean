/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn, Peter Nelson
-/
import data.fintype.basic
import algebra.big_operators.basic

/-!
# Combinatorial lines and subspaces

This file defines *combinatorial lines* and *combinatorial subspaces*, and gives basic examples,
instances and lemmas that relate these objects and their colourings. This file gives the
infrastructure necessary to state and prove Hales-Jewett-type theorems, which appear in
`combinatorics.hales_jewett`.

Informally, a combinatorial line is a set of words over an alphabet `A`, that is described by a word
`w` over the alphabet `A ∪ {*}`, where `*` is a 'wildcard' symbol that appears at least once in `w`.
The line described by `w` is the set of all words over `A` that can be obtained by choosing some
`x ∈ A`, and replacing all instances of `*` with `x` in `w`. For example, if `A = {a,b,c}`, the
line corresponding to the word `ac**c*` is the set `{acaaca, acbbcb, accccc}`. If `A` is finite,
this line will have `|A|` elements. A combinatorial subspace is a generalization of this notion to
an arbitrary set `{*₁, *₂, ...}` of wildcard symbols that can vary independently and which all
appear in `w`; if there are `d` wildcard symbols, the subspace corresponding to `w` has 'dimension'
`d` and has size `|A|^d`.

Formally, we define a combinatorial subspace over an alphabet type `α`, an index type `ι`, and
a wildcard type `ν`, none of which needs to be finite. The word `w` is encoded as a function
`idx_fun : ι → (α ⊕ ν)` whose range contains `inr n` for all `n : ν`, and, via a coercion, we view
a subspace `s` itself as a function from `(ν → α)` to `(ι → α)`, whose range is the set of elements
in the subspace as defined earlier.

Combinatorial lines can be seen as the special case where `ν` is a type with one element, but are
defined as separate objects with `idx_fun : ι → option α` and with their own API, to make working
with lines by themselves more concrete and involve less reindexing.

# Main definitions

- `line α ι` : a combinatorial line over the alphabet `α` with words indexed by `ι`
- `subspace α ι ν` : a combinatorial subspace over the alphabet `α` with words indexed
    by `ι` and wildcards indexed by `ν`.
- `subspace.equiv_line` : The equivalence between `line α ι` and `subspace α ι ν` for
    a one-element type `ν`'.
- `subspace.prod s s'` : the product of subspaces `s : subspace α ι ν` and
    `s' : subspace α ι' ν'`. This has type `subspace α (ι ⊕ ι') (ν ⊕ ν')`.
- `subspace.equiv_of_wildcard_equiv` : The equivalence between the types `(subspace α ι ν)` and
    `(subspace α ι ν')` induced by an equivalence `(e : ν ≃ ν')`.

## Tags

combinatorial line, combinatorial subspace
-/

open_locale classical
open_locale big_operators

universes u v

namespace combinatorics

/-- The type of combinatorial lines. A line `l : line α ι` in the hypercube `ι → α` defines a
function `α → ι → α` from `α` to the hypercube, such that for each coordinate `i : ι`, the function
`λ x, l x i` is either `id` or constant. We require lines to be nontrivial in the sense that
`λ x, l x i` is `id` for at least one `i`.

Formally, a line is represented by the function `l.idx_fun : ι → option α` which says whether
`λ x, l x i` is `id` (corresponding to `l.idx_fun i = none`) or constantly `y` (corresponding to
`l.idx_fun i = some y`).

When `α` has size `1` there can be many elements of `line α ι` defining the same function. -/
structure line (α ι : Type*) :=
(idx_fun : ι → option α)
(proper : ∃ i, idx_fun i = none)

namespace line

/- This lets us treat a line `l : line α ι` as a function `α → ι → α`. -/
instance (α ι) : has_coe_to_fun (line α ι) (λ _, α → ι → α) :=
⟨λ l x i, (l.idx_fun i).get_or_else x⟩

/-- A line is monochromatic if all its points are the same color. -/
def is_mono {α ι κ} (C : (ι → α) → κ) (l : line α ι) : Prop :=
∃ c, ∀ x, C (l x) = c

/-- The diagonal line. It is the identity at every coordinate. -/
def diagonal (α ι) [nonempty ι] : line α ι :=
{ idx_fun := λ _, none,
  proper  := ⟨classical.arbitrary ι, rfl⟩ }

instance (α ι) [nonempty ι] : inhabited (line α ι) := ⟨diagonal α ι⟩

/-- A function `f : α → α'` determines a function `line α ι → line α' ι`. For a coordinate `i`,
`l.map f` is the identity at `i` if `l` is, and constantly `f y` if `l` is constantly `y` at `i`. -/
def map {α α' ι} (f : α → α') (l : line α ι) : line α' ι :=
{ idx_fun := λ i, (l.idx_fun i).map f,
  proper  := ⟨l.proper.some, by rw [l.proper.some_spec, option.map_none'] ⟩ }

/-- A point in `ι → α` and a line in `ι' → α` determine a line in `ι ⊕ ι' → α`. -/
def vertical {α ι ι'} (v : ι → α) (l : line α ι') : line α (ι ⊕ ι') :=
{ idx_fun := sum.elim (some ∘ v) l.idx_fun,
  proper  := ⟨sum.inr l.proper.some, l.proper.some_spec⟩ }

/-- A line in `ι → α` and a point in `ι' → α` determine a line in `ι ⊕ ι' → α`. -/
def horizontal {α ι ι'} (l : line α ι) (v : ι' → α) : line α (ι ⊕ ι') :=
{ idx_fun := sum.elim l.idx_fun (some ∘ v),
  proper  := ⟨sum.inl l.proper.some, l.proper.some_spec⟩ }

/-- One line in `ι → α` and one in `ι' → α` together determine a line in `ι ⊕ ι' → α`. -/
def prod {α ι ι'} (l : line α ι) (l' : line α ι') : line α (ι ⊕ ι') :=
{ idx_fun := sum.elim l.idx_fun l'.idx_fun,
  proper  := ⟨sum.inl l.proper.some, l.proper.some_spec⟩ }

lemma apply {α ι} (l : line α ι) (x : α) : l x = λ i, (l.idx_fun i).get_or_else x := rfl

lemma apply_none {α ι} (l : line α ι) (x : α) (i : ι) (h : l.idx_fun i = none) : l x i = x :=
by simp only [option.get_or_else_none, h, l.apply]

lemma apply_of_ne_none {α ι} (l : line α ι) (x : α) (i : ι) (h : l.idx_fun i ≠ none) :
  some (l x i) = l.idx_fun i :=
by rw [l.apply, option.get_or_else_of_ne_none h]

@[simp] lemma map_apply {α α' ι} (f : α → α') (l : line α ι) (x : α) :
  l.map f (f x) = f ∘ l x :=
by simp only [line.apply, line.map, option.get_or_else_map]

@[simp] lemma vertical_apply {α ι ι'} (v : ι → α) (l : line α ι') (x : α) :
  l.vertical v x = sum.elim v (l x) :=
by { funext i, cases i; refl }

@[simp] lemma horizontal_apply {α ι ι'} (l : line α ι) (v : ι' → α) (x : α) :
  l.horizontal v x = sum.elim (l x) v :=
by { funext i, cases i; refl }

@[simp] lemma prod_apply {α ι ι'} (l : line α ι) (l' : line α ι') (x : α) :
  l.prod l' x = sum.elim (l x) (l' x) :=
by { funext i, cases i; refl }

@[simp] lemma diagonal_apply {α ι} [nonempty ι] (x : α) :
  line.diagonal α ι x = λ i, x :=
by simp_rw [line.apply, line.diagonal, option.get_or_else_none]

end line

/-- A combinatorial subspace of `ι`-indexed words over an alphabet `α`, with wildcard type `ν`. -/
@[ext] structure subspace (α ι ν : Type*) :=
(idx_fun : ι → (α ⊕ ν))
(proper : ∀ n, ∃ i, idx_fun i = sum.inr n)

namespace subspace

variables {α ι ι' ν ν' κ : Type*}

/-- A subspace `s` gives a map from `ν`-indexed words over `α` to `ι`-indexed words over `α`. -/
instance (α ι ν) : has_coe_to_fun (subspace α ι ν) (λ _, (ν → α) → (ι → α)) :=
⟨λ s x, λ i, sum.cases_on (s.idx_fun i) id x⟩

lemma coe_eq (s : subspace α ι ν) (w : ν → α) : s w = λ i, sum.cases_on (s.idx_fun i) id w := rfl

/-- A subspace with empty wildcard type is a single word. -/
def zero_dim [is_empty ν] (x : ι → α) : subspace α ι ν := ⟨(λ i, sum.inl (x i)), is_empty_elim⟩

/-- A bijection between `ι` and `ν` gives rise to a subspace over an arbitrary alphabet. -/
def wildcard_equiv_index (α : Type*) (e : ι ≃ ν): subspace α ι ν :=
⟨sum.inr ∘ e, λ n, ⟨e.symm n, by simp⟩⟩

/-- Every type `ν` gives rise to a subspace in which `ν` is both the wildcard and index type -/
def wildcard_eq_index (α ν : Type*) : subspace α ν ν := wildcard_equiv_index α (equiv.refl ν)

noncomputable instance [fintype α] [fintype ι] [fintype ν] : fintype (subspace α ι ν) :=
@fintype.of_bijective {f : ι → (α ⊕ ν) // ∀ n, ∃ i, f i = sum.inr n} _ _
  (λ f, (⟨f.1,f.2⟩ : subspace α ι ν))
  ⟨λ f f' h, by {cases f, cases f', simpa using h}, λ s, ⟨⟨s.idx_fun, s.proper⟩,by {cases s, simp}⟩⟩

lemma nonempty_iff :
  nonempty (subspace α ι ν) ↔ (nonempty (ν ↪ ι)) ∧ (nonempty (α ⊕ ν) ∨ (is_empty ν ∧ is_empty ι)) :=
begin
  split,
  { rintro ⟨s⟩,
    have h1 : nonempty (ν ↪ ι),
      { obtain ⟨f,hf⟩ := classical.axiom_of_choice s.proper,
      exact ⟨⟨f, λ n n' h, @sum.inr_injective α _ _ _ (by rw [←hf n, ←hf n',h])⟩⟩},
    exact ⟨h1, (is_empty_or_nonempty ι).elim (λ ⟨hι⟩, or.inr ⟨⟨λ n, h1.elim (λ f, hι (f n))⟩,⟨hι⟩⟩)
      (λ h, or.inl (h.elim (λ i, ⟨s.idx_fun i⟩)))⟩},
  rintros ⟨⟨f⟩, (⟨⟨a⟩⟩ |⟨hν, hι⟩)⟩, swap, exact ⟨⟨@is_empty_elim _ hι _, @is_empty_elim _ hν _⟩⟩,
  set g := function.partial_inv f with hg,
  set idx : ι → (α ⊕ ν) := λ i, option.cases_on (g i) a sum.inr with hidx,
  have proper : ∀ n, ∃ i, idx i = sum.inr n,
  { intro n, refine ⟨f n, _⟩, rw [hidx, hg],
    simp only, rw [function.partial_inv_left (f : ν ↪ ι).injective]},
  exact ⟨⟨idx, proper⟩⟩,
end

/-- This lemma cannot be upgraded into an `inhabited` instance, since the injection cannot
be constructively inverted.  -/
lemma nonempty_of_nonempty (h : nonempty (α ⊕ ν)) (h' : nonempty (ν ↪ ι)) :
  nonempty (subspace α ι ν) :=
nonempty_iff.mpr ⟨h', or.inl h⟩

instance inhabited_of_unique [unique ν] [inhabited ι] : inhabited (subspace α ι ν) :=
 ⟨⟨λ i, sum.inr default, λ n, ⟨default, by rw unique.eq_default n⟩⟩⟩

instance inhabited_of_empty_empty [is_empty ι] [is_empty ν] : inhabited (subspace α ι ν) :=
⟨⟨is_empty_elim,is_empty_elim⟩⟩

instance inhabited_of_wildcard_eq : inhabited (subspace α ν ν) := ⟨wildcard_eq_index _ _⟩

/- #### Colourings -/

/-- A subspace is monochromatic wrt `C` if any two of its words are assigned the same colour by `C`.
  The definition is phrased to also apply in the degenerate case where `ι` and `κ` are empty. -/
def is_mono (C : (ι → α) → κ) (s : subspace α ι ν) := ∀ (w w' : ν → α), C (s w) = C (s w')

lemma mono_of_exists {C : (ι → α) → κ} {s : subspace α ι ν} {k : κ} (h : ∀ v, C (s v) = k) :
  is_mono C s :=
λ _ _, by rw [h,h]

lemma mono_of_empty [h : is_empty α] (C : (ι → α) → κ) (s : subspace α ι ν) : is_mono C s :=
λ w w', by convert rfl

lemma is_mono_iff' [nonempty κ] {C : (ι → α) → κ} {s : subspace α ι ν} :
  is_mono C s ↔ ∃ k, ∀ v, C (s v) = k :=
begin
  split,
  refine λ h, (is_empty_or_nonempty (ν → α)).elim
    (λ h', (infer_instance : nonempty κ).elim (λ k, ⟨k, h'.elim⟩)) (λ h', _),
  obtain ⟨v⟩ := h',
  exact ⟨C (s v), λ v', h _ v⟩,
  rintros ⟨k, hk⟩ v v', rw [hk,hk],
end

lemma is_mono_iff [nonempty α] {C : (ι → α) → κ} {s : subspace α ι ν} :
  is_mono C s ↔ ∃ k, ∀ v, C (s v) = k :=
@is_mono_iff' _ _ _ _ (by {inhabit α, exact ⟨C default⟩}) _ _

/- #### Products -/

/-- The product of two subspaces is a subspace -/
def prod (s : subspace α ι ν) (s' : subspace α ι' ν') : subspace α (ι ⊕ ι') (ν ⊕ ν') :=
{ idx_fun := λ i, sum.cases_on i
  (λ i₁, sum.cases_on (s.idx_fun i₁) sum.inl (sum.inr ∘ sum.inl))
  (λ i₁, sum.cases_on (s'.idx_fun i₁) sum.inl (sum.inr ∘ sum.inr)),
  proper :=
  begin
    rintros (n | n),
    { obtain ⟨i,hi⟩ := s.proper n,
      exact ⟨sum.inl i, by {dsimp only [function.comp_app], rw hi}⟩},
    obtain ⟨i,hi⟩ := s'.proper n,
    exact ⟨sum.inr i, by {dsimp only [function.comp_app], rw hi}⟩,
  end  }

lemma prod_idx_apply_left (s : subspace α ι ν) (s' : subspace α ι' ν') (i : ι) :
  (prod s s').idx_fun (sum.inl i) = sum.cases_on (s.idx_fun i) sum.inl (sum.inr ∘ sum.inl) := rfl

lemma prod_idx_apply_right (s : subspace α ι ν) (s' : subspace α ι' ν') (i : ι') :
  (prod s s').idx_fun (sum.inr i) = sum.cases_on (s'.idx_fun i) sum.inl (sum.inr ∘ sum.inr) := rfl

@[simp] lemma prod_coe_comp_inl_apply (s : subspace α ι ν) (s' : subspace α ι' ν') (v : ν ⊕ ν' → α)
(i : ι):
  ((prod s s') v) (sum.inl i) = s (v ∘ sum.inl) i :=
by {simp only [coe_eq, id.def, function.comp_app], rw prod_idx_apply_left, cases s.idx_fun i; refl}

@[simp] lemma prod_coe_comp_inr_apply (s : subspace α ι ν) (s' : subspace α ι' ν') (v : ν ⊕ ν' → α)
(i : ι'):
  ((prod s s') v) (sum.inr i) = s' (v ∘ sum.inr) i :=
by {simp only [coe_eq, id.def, function.comp_app],rw prod_idx_apply_right, cases s'.idx_fun i; refl}

@[simp] lemma prod_coe_comp_inl_eq (s : subspace α ι ν) (s' : subspace α ι' ν') (v : ν ⊕ ν' → α) :
  ((prod s s') v) ∘ sum.inl = s (v ∘ sum.inl) :=
by {ext, simp}

@[simp] lemma prod_coe_comp_inr_eq (s : subspace α ι ν) (s' : subspace α ι' ν') (v : ν ⊕ ν' → α) :
  ((prod s s') v) ∘ sum.inr = s' (v ∘ sum.inr) :=
by {ext, simp}

@[simp] lemma prod_coe_elim_left {ι' ν' : Type*} (s : subspace α ι ν) (s' : subspace α ι' ν')
(v : ν → α) (v' : ν' → α) :
  (prod s s') (sum.elim v v') ∘ sum.inl = s v :=
by {ext, simp}

@[simp] lemma prod_coe_elim_right {ι' ν' : Type*} (s : subspace α ι ν) (s' : subspace α ι' ν')
(v : ν → α) (v' : ν' → α) :
  (prod s s') (sum.elim v v') ∘ sum.inr = s' v' :=
by {ext, simp}

/- #### Subspaces and lines -/

/-- Produces a line from a nontrivial subspace by merging its wildcards. -/
def to_line [inhabited ν] (s : subspace α ι ν) : line α ι :=
{ idx_fun := λ i, sum.cases_on (s.idx_fun i) some (λ _, none),
  proper  := (s.proper default).imp (λ i hi, by rw [hi])}

/-- The one-dimenional subspace corresponding to a line, given a `unique` wildcard type. -/
def of_line_of_dim_one (ν : Type*) [unique ν] (l : line α ι) : subspace α ι ν :=
{ idx_fun := λ i, option.cases_on (l.idx_fun i) (sum.inr default) sum.inl,
  proper := λ n, l.proper.imp (λ i hi, by {rw hi, simp})}

/-- Once a `unique` wildcard type is specified, one-dimensional subspaces are the same as lines. -/
@[simps apply]
def equiv_line [unique ν] : subspace α ι ν ≃ line α ι :=
{ to_fun := to_line,
  inv_fun := of_line_of_dim_one ν,
  left_inv := λ ⟨lf, _⟩,
    by {ext, dsimp only [of_line_of_dim_one, to_line], cases (lf x); simp},
  right_inv := λ ⟨sf, _⟩,
    by {simp only [of_line_of_dim_one, to_line], dsimp only, ext i, cases (sf i); refl}}

lemma coe_eq_coe_of_dim_one [unique ν] (s : subspace α ι ν) (x : α) :
  (s (λ _, x) = equiv_line s x) :=
begin
  ext i, unfold_coes,
  simp only [to_line, id.def, equiv.to_fun_as_coe, equiv_line_apply],
  obtain (a | n) := s.idx_fun i; refl,
end

lemma mono_iff_line_mono [nonempty α] [unique ν] {C : (ι → α) → κ} {s : subspace α ι ν} :
  is_mono C s ↔ line.is_mono C (equiv_line s) :=
begin
  inhabit α,
  split, exact λ hs, ⟨C (s (λ _, default)), λ x, by {rw ←coe_eq_coe_of_dim_one, exact hs _ _}⟩,
  rintros ⟨k,hk⟩ w w',
  rw [(by {ext x, rw unique.eq_default x} : w = λ _, w default),
    (by {ext x, rw unique.eq_default x} : w' = λ _, w' default),
    coe_eq_coe_of_dim_one, coe_eq_coe_of_dim_one, hk, hk],
end

/- #### Reindexing -/

/-- Reindexes the wildcards in a subspace. -/
def equiv_of_wildcard_equiv (e : ν ≃ ν') : (subspace α ι ν) ≃ (subspace α ι ν') :=
{ to_fun := λ s, ⟨λ i, @equiv.sum_congr α _ _ _ (equiv.refl α) e (s.idx_fun i),
    λ n, (s.proper (e.symm n)).imp (λ i hi, by simp [hi])⟩,
  inv_fun := λ s, ⟨λ i, @equiv.sum_congr α _ _ _ (equiv.refl α) e.symm (s.idx_fun i),
    λ n, (s.proper (e n)).imp (λ i hi, by simp [hi])⟩,
  left_inv := λ s, by {cases s, simp},
  right_inv := λ s, by {cases s, simp} }

lemma equiv_of_wildcard_equiv_idx_apply (e : ν ≃ ν') (s : subspace α ι ν) (i : ι):
  ((equiv_of_wildcard_equiv e) s).idx_fun i = sum.cases_on (s.idx_fun i) sum.inl (sum.inr ∘ e) :=
rfl

lemma equiv_of_wildcard_equiv_idx_apply_inv (e : ν ≃ ν') (s : subspace α ι ν') (i : ι):
  ((equiv_of_wildcard_equiv e).symm s).idx_fun i
    = sum.cases_on (s.idx_fun i) sum.inl (sum.inr ∘ e.symm) := rfl

@[simp] lemma coe_wildcard_equiv_apply (e : ν ≃ ν') (s : subspace α ι ν) (v : ν → α) :
  (equiv_of_wildcard_equiv e s) (λ n, v (e.symm n)) = s v :=
begin
  ext i,
  simp only [coe_eq, id.def],
  rw equiv_of_wildcard_equiv_idx_apply,
  obtain a | n := s.idx_fun i, refl, simp,
end

@[simp] lemma coe_wildcard_equiv_apply_inv (e : ν ≃ ν') (s : subspace α ι ν) (v : ν' → α) :
  (equiv_of_wildcard_equiv e s) v = s (λ n, v (e n)) :=
by {rw [←coe_wildcard_equiv_apply e _ (λ n, v (e n))], simp}

@[simp] lemma mono_iff_wildcard_equiv_mono {e : ν ≃ ν'} {s : subspace α ι ν} {C : (ι → α) → κ}:
  is_mono C (equiv_of_wildcard_equiv e s) ↔ is_mono C s :=
begin
  refine (is_empty_or_nonempty α).elim
    (λ h, ⟨λ _, @mono_of_empty _ _ _ _ h _ _, λ _, @mono_of_empty _ _ _ _ h _ _⟩) _,
  introI,
  rw [iff.comm, is_mono_iff, is_mono_iff], simp_rw [coe_wildcard_equiv_apply_inv],
  exact exists_congr (λ k, equiv.forall_congr (equiv.Pi_congr_left' (λ _, α) e) (λ _, by simp)),
end

end subspace
end combinatorics
