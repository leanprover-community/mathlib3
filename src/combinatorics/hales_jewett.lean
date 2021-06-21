/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import data.fintype.basic
import algebra.big_operators.basic
import data.equiv.fin

/-!
# The Hales-Jewett theorem

We prove the Hales-Jewett theorem and deduce Van der Waerden's theorem as a corollary.

We consistently work with finite types instead of natural numbers. That is, we write `α, ι, κ` for
(finite) types where one might traditionally use natural numbers `n, H, c`. This allows us to
work directly with `α`, `option α`, `(ι → α) → κ`, and `ι ⊕ ι'` instead of `fin n`, `fin (n+1)`,
`fin (c^(n^H))`, and `fin (H + H')`.

We do not prove the finitary version of Van der Waerden's theorem (which is equivalent to the
infinite one by compactness), although it follows from the same proof.

In principle our proof should give explicit upper bounds on the numbers `HJ(α, κ)`, but this would
require rewriting the proof and the upper bounds are enormous anyway.

## Main results

- `combinatorics.line.exists_mono_in_high_dimension α κ`: the Hales-Jewett theorem.
- `combinatorics.exists_mono_homothetic_copy M S f κ C`: a generalization of Van der Waerden's
theorem to an arbitrary commutative monoid. The proof is a simple application of Hales-Jewett.

## Tags

combinatorial line, Ramsey theory, arithmetic progession

### References

* https://en.wikipedia.org/wiki/Hales%E2%80%93Jewett_theorem

Note that this file does not use the same notation as Wikipedia.

-/

open_locale classical
open_locale big_operators

/-- An induction principle for finite types. It effectively says that any finite type is equivalent
to either `empty`, `unit`, or `option α` where `α` is nonempty. -/
lemma fintype_induction {P : Type → Prop} (of_equiv : ∀ {α β}, α ≃ β → P α → P β)
  (h_empty : P empty) (h_unit : P unit)
  (h_option : ∀ {α} [fintype α] [nonempty α], P α → P (option α))
  (α) [fintype α] : P α :=
begin
  suffices : ∀ ι : nat, P (fin ι),
  { refine of_equiv (fintype.equiv_fin α).symm (this _), },
  rintro (_ | ι),
  { apply of_equiv fin_zero_equiv.symm h_empty },
  induction ι with ι ih,
  { apply of_equiv fin_one_equiv.symm h_unit },
  { apply of_equiv (fin_succ_equiv _).symm (h_option ih), }
end

namespace combinatorics

/-- The type of combinatorial lines. A line `l : line α ι` in the hypercube `ι → α` defines a
function `α → (ι → α)` to the hypercube, such that for each coordinate `i : ι`, the function
`l x i` is either identically `x` or constant. We require lines to be nontrivial, in the sense
that `l x i` is identically `x` for at least one `i`.

Formally, a line is represented by the function `l.idx_fun : ι → option α` which says whether
`l x i` is identically `x` (corresponding to `l.idx_fun i = none`) or constantly `y`
(corresponding to `l.idx_fun i = some y`). When `α` has size `1` there can be many elements of
`line α ι` defining the same function. -/
structure line (α ι : Type*) :=
(idx_fun : ι → option α)
(proper : ∃ i, idx_fun i = none)

namespace line

/- This lets us treat a line `l : line α ι` as a function `α → (ι → α)`. -/
instance (α ι) : has_coe_to_fun (line α ι) :=
⟨λ _, α → ι → α, λ l x i, (l.idx_fun i).get_or_else x⟩

/-- The type of lines that are only one color except possibly at their endpoints. -/
@[nolint has_inhabited_instance]
structure almost_mono {α ι κ : Type*} (C : (ι → option α) → κ) :=
(line : line (option α) ι)
(color : κ)
(has_color : ∀ x : α, C (line (some x)) = color)

/-- The type of families of lines such that
- each line is only one color except possibly at its endpoint
- the lines all have the same endpoint
- the colors of the lines are distinct.
Used in the proof `exists_mono_in_high_dimension`. -/
structure color_focused {α ι κ : Type*} (C : (ι → option α) → κ) :=
(lines : multiset (almost_mono C))
(focus : ι → option α)
(is_focused : ∀ p : almost_mono C, p ∈ lines → p.line none = focus)
(distinct_colors : (lines.map almost_mono.color).nodup)

instance {α ι κ} (C : (ι → option α) → κ) : inhabited (color_focused C) :=
⟨⟨0, λ _, none, λ _, false.elim, multiset.nodup_zero⟩⟩

/-- The diagonal line. It is the identity at every coordinate. -/
def diagonal (α ι) [nonempty ι] : line α ι :=
{ idx_fun := λ _, none,
  proper  := ⟨classical.arbitrary ι, rfl⟩ }

instance (α ι) [nonempty ι] : inhabited (line α ι) := ⟨diagonal α ι⟩

/-- A line is monochromatic if all its points are the same color. -/
def is_mono {α ι κ} (C : (ι → α) → κ) (l : line α ι) : Prop :=
∃ c, ∀ x, C (l x) = c

/-- A function `α → α'` determines a function `line α ι → line α' ι`. For a coordinate `i`,
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

@[simp] lemma apply_none {α ι} (l : line α ι) (x : α) (i : ι)
  (h : l.idx_fun i = none) : l x i = x :=
by simp only [option.get_or_else_none, h, l.apply]

@[simp] lemma apply_of_ne_none {α ι} (l : line α ι) (x : α) (i : ι)
  (h : l.idx_fun i ≠ none) : some (l x i) = l.idx_fun i :=
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

/-- The Hales-Jewett theorem: for any finite types `α` and `κ` with `α` nonempty, there exists
another finite type `ι` such that whenever the hypercube `ι → α` is `κ`-colored, there is
a monochromatic combinatorial line. -/
theorem exists_mono_in_high_dimension : ∀ (α : Type) [fintype α] (κ : Type) [fintype κ],
  ∃ (ι : Type) [fintype ι], ∀ C : (ι → α) → κ, ∃ l : line α ι, l.is_mono C :=
-- The proof proceeds by induction on `α`.
fintype_induction
-- We have to show that the theorem is invariant under `α ≃ α'` for the induction to work.
(λ α α' e, forall_imp $ λ κ, forall_imp $ λ _, Exists.imp $ λ ι, Exists.imp $ λ _ h C,
  let ⟨l, c, lc⟩ := h (λ v, C (e ∘ v)) in
  ⟨l.map e, c, e.forall_congr_left.mp $ λ x, by rw [←lc x, line.map_apply]⟩)
-- This deals with the degenerate case where `α` is empty.
(λ κ hκ, ⟨κ, hκ, λ C, begin
    haveI : nonempty κ := not_is_empty_iff.mp (λ ⟨h⟩, h (C $ λ i, (h i).elim)),
    exact ⟨default _, classical.arbitrary κ, empty.rec _⟩
  end⟩)
-- The base case `α = unit` is easy since any line is monochromatic.
(λ κ _, ⟨unit, infer_instance, λ C, ⟨diagonal _ _, C (λ _, ()), λ ⟨⟩, rfl⟩⟩)
begin -- Now we have to show that the theorem holds for `option α` if it holds for `α`.
  introsI α _ _ ihα κ _,
-- The key idea is to show that for every `r`, in high dimension we can either find
-- `r` color focused lines or a monochromatic line.
  suffices key : ∀ r : ℕ, ∃ (ι : Type) [fintype ι], ∀ C : (ι → (option α)) → κ,
    (∃ s : color_focused C, s.lines.card = r) ∨ (∃ l, is_mono C l),
-- Given the key claim, we simply take `r = |κ| + 1`. We cannot have this many distinct colors so
-- we must be in the second case, where there is a monochromatic line.
  { obtain ⟨ι, _inst, hι⟩ := key (fintype.card κ + 1),
    refine ⟨ι, _inst, λ C, (hι C).resolve_left _⟩,
    rintro ⟨s, sr⟩,
    apply nat.not_succ_le_self (fintype.card κ),
    rw [←nat.add_one, ←sr, ←multiset.card_map, ←finset.card_mk],
    exact finset.card_le_univ ⟨_, s.distinct_colors⟩ },
-- We now prove the key claim, by induction on `r`.
  intro r,
  induction r with r ihr,
-- The base case `r = 0` is trivial as the empty collection is color-focused.
  { exact ⟨empty, infer_instance, λ C, or.inl ⟨default _, multiset.card_zero⟩⟩, },
-- Supposing the key claim holds for `r`, we need to show it for `r+1`. First pick a high enough
-- dimension `ι` for `r`.
  obtain ⟨ι, _inst, hι⟩ := ihr,
  resetI,
-- Then since the theorem holds for `α` with and number of colors, pick a dimension `ι'` such that
-- `ι' → α` always has a monochromatic line whenever it is colored with `(ι → α) → κ` colors.
  specialize ihα ((ι → option α) → κ),
  obtain ⟨ι', _inst, hι'⟩ := ihα,
  resetI,
-- We claim that `ι ⊕ ι'` works for `unit α`.
  refine ⟨ι ⊕ ι', infer_instance, _⟩,
  intro C,
-- A `κ`-coloring of `ι ⊕ ι' → α` induces a `(ι → α) → κ`-coloring of `ι' → α`.
  specialize hι' (λ v' v, C (sum.elim v (some ∘ v'))),
-- By choice of `ι'` this coloring has a monochromatic line `l'` with color class `C'`, where
-- `C'` is a `κ`-coloring of `ι → α`.
  obtain ⟨l', C', hl'⟩ := hι',
-- If `C'` has a monochromatic line, then so does `C`. We use this in two places below.
  have mono_of_mono : (∃ l, is_mono C' l) → (∃ l, is_mono C l),
  { rintro ⟨l, c, hl⟩,
    refine ⟨l.horizontal (some ∘ l' (classical.arbitrary α)), c, λ x, _⟩,
    rw [line.horizontal_apply, ←hl, ←hl'], },
-- By choice of `ι`, `C'` either has `r` color focused lines or a monochromatic line.
  specialize hι C',
  rcases hι with ⟨s, sr⟩ | _,
-- By above, we are done if `C'` has a monochromatic line.
  work_on_goal 1 { exact or.inr (mono_of_mono hι) },
-- Here we assume `C'` has `r` color focused lines. We split into cases depending on whether one of
-- these `r` lines has the same color as the focus point. -/
  by_cases h : ∃ p ∈ s.lines, (p : almost_mono _).color = C' s.focus,
-- If so then this is a `C'`-monochromatic line and we are done.
  { obtain ⟨p, p_mem, hp⟩ := h,
    refine or.inr (mono_of_mono ⟨p.line, p.color, _⟩),
    rintro (_ | _), rw [hp, s.is_focused p p_mem], apply p.has_color, },
-- If not, we get `r+1` color focused lines by taking the product of the `r` lines with `l'` and
-- adding to this the vertical line obtained by the focus point and `l`.
  refine or.inl ⟨⟨(s.lines.map _).cons ⟨(l'.map some).vertical s.focus, C' s.focus, λ x, _⟩,
    sum.elim s.focus (l'.map some none), _, _⟩, _⟩,
-- The vertical line is almost monochromatic.
  { rw [vertical_apply, ←congr_fun (hl' x), line.map_apply], },
  { refine λ p, ⟨p.line.prod (l'.map some), p.color, λ x, _⟩,
-- The product lines are almost monochromatic.
    rw [line.prod_apply, line.map_apply, ←p.has_color, ←congr_fun (hl' x)], },
-- Our `r+1` lines have the same endpoint.
  { simp_rw [multiset.mem_cons, multiset.mem_map],
    rintros _ (rfl | ⟨q, hq, rfl⟩),
    { rw line.vertical_apply, },
    { rw [line.prod_apply, s.is_focused q hq], }, },
-- Our `r+1` lines have distinct colors (this is why we needed to split into cases above).
  { rw [multiset.map_cons, multiset.map_map, multiset.nodup_cons, multiset.mem_map],
    exact ⟨λ ⟨q, hq, he⟩, h ⟨q, hq, he⟩, s.distinct_colors⟩, },
-- Finally, we really do have `r+1` lines!
  { rw [multiset.card_cons, multiset.card_map, sr], },
end

end line

/-- A generalization of Van der Waerden's theorem: if `M` is a finitely colored commutative
monoid, and `S` is a finite subset, then there exists a monochromatic homothetic copy of `S`.
Formally, instead of taking `S` to be a subset we take it to be a finite type with a function
`S → M`.

This theorem is equivalent to Gallai's higher-dimensional version of Van der Waerden for the
monoids `ℕ^d`.
-/
theorem exists_mono_homothetic_copy (M) (S : Type) (f : S → M) [fintype S] [add_comm_monoid M]
  (κ : Type) [fintype κ] (C : M → κ) :
  ∃ (a > 0) (b : M) (c : κ), ∀ s, C (a • (f s) + b) = c :=
begin
  obtain ⟨ι, _inst, hι⟩ := line.exists_mono_in_high_dimension S κ,
  resetI,
  specialize hι (λ v, C $ ∑ i, f (v i)),
  obtain ⟨l, c, hl⟩ := hι,
  set s : finset ι := { i ∈ finset.univ | l.idx_fun i = none } with hs,
  refine ⟨s.card, finset.card_pos.mpr ⟨l.proper.some, _⟩,
    ∑ i in sᶜ, ((l.idx_fun i).map f).get_or_else 0, c, _⟩,
  { rw [hs, finset.sep_def, finset.mem_filter], exact ⟨finset.mem_univ _, l.proper.some_spec⟩, },
  intro x,
  rw ←hl x,
  clear hl, dsimp, congr,
  rw ←finset.sum_add_sum_compl s,
  congr' 1,
  { rw ←finset.sum_const,
    apply finset.sum_congr rfl,
    intros i hi,
    rw [hs, finset.sep_def, finset.mem_filter] at hi,
    rw l.apply_none _ _ hi.right, },
  { apply finset.sum_congr rfl,
    intros i hi,
    rw [hs, finset.sep_def, finset.compl_filter, finset.mem_filter] at hi,
    obtain ⟨y, hy⟩ := option.ne_none_iff_exists.mp hi.right,
    simp_rw [line.apply, ←hy, option.map_some', option.get_or_else_some], },
end

end combinatorics
