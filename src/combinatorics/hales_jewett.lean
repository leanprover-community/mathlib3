/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import data.fintype.basic
import algebra.big_operators.basic

/-!
# The Hales-Jewett theorem

We prove the Hales-Jewett theorem. We deduce Van der Waerden's theorem and the extended Hales-Jewett
theorm as corollaries.

The Hales-Jewett theorem is a result in Ramsey theory dealing with *combinatorial lines*. Given
an 'alphabet' `α : Type*` and `a b : α`, an example of a combinatorial line in `α^5` is
`{ (a, x, x, b, x) | x : α }`. See `combinatorics.line` for a precise general definition. The
Hales-Jewett theorem states that for any fixed finite types `α` and `κ`, there exists a (potentially
huge) finite type `ι` such that whenever `ι → α` is `κ`-colored (i.e. for any coloring
`C : (ι → α) → κ`), there exists a monochromatic line. We prove the Hales-Jewett theorem using
the idea of *color focusing* and a *product argument*. See the proof of
`combinatorics.line.exists_mono_in_high_dimension'` for details.

*Combinatorial subspaces* are higher-dimensional analogues of combinatorial lines, defined in
`combinatorics.subspace`. The extended Hales-Jewett theorem generalises the statement above from
combinatorial lines to combinatorial subspaces of a fixed dimension.

The version of Van der Waerden's theorem in this file states that whenever a commutative monoid `M`
is finitely colored and `S` is a finite subset, there exists a monochromatic homothetic copy of `S`.
This follows from the Hales-Jewett theorem by considering the map `(ι → S) → M` sending `v`
to `∑ i : ι, v i`, which sends a combinatorial line to a homothetic copy of `S`.

## Main results

- `combinatorics.line.exists_mono_in_high_dimension`: the Hales-Jewett theorem.
- `combinatorics.subspace.exists_mono_in_high_dimension`: the extended Hales-Jewett theorem.
- `combinatorics.exists_mono_homothetic_copy`: a generalization of Van der Waerden's theorem.

## Implementation details

For convenience, we work directly with finite types instead of natural numbers. That is, we write
`α, ι, κ` for (finite) types where one might traditionally use natural numbers `n, H, c`. This
allows us to work directly with `α`, `option α`, `(ι → α) → κ`, and `ι ⊕ ι'` instead of `fin n`,
`fin (n+1)`, `fin (c^(n^H))`, and `fin (H + H')`.

## Todo

- Prove a finitary version of Van der Waerden's theorem (either by compactness or by modifying the
current proof).

- One could reformulate the proof of Hales-Jewett to give explicit upper bounds on the number of
coordinates needed.

## Tags

combinatorial line, Ramsey theory, arithmetic progession

### References

* https://en.wikipedia.org/wiki/Hales%E2%80%93Jewett_theorem

-/

open_locale classical
open_locale big_operators

universes u v w

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

/-- The type of lines that are only one color except possibly at their endpoints. -/
structure almost_mono {α ι κ : Type*} (C : (ι → option α) → κ) :=
(line : line (option α) ι)
(color : κ)
(has_color : ∀ x : α, C (line (some x)) = color)

instance {α ι κ : Type*} [nonempty ι] [inhabited κ] :
  inhabited (almost_mono (λ v : ι → option α, (default : κ))) :=
⟨{ line      := default,
   color     := default,
   has_color := λ _, rfl }⟩

/-- The type of collections of lines such that
- each line is only one color except possibly at its endpoint
- the lines all have the same endpoint
- the colors of the lines are distinct.
Used in the proof `exists_mono_in_high_dimension`. -/
structure color_focused {α ι κ : Type*} (C : (ι → option α) → κ) :=
(lines : multiset (almost_mono C))
(focus : ι → option α)
(is_focused : ∀ p ∈ lines, almost_mono.line p none = focus)
(distinct_colors : (lines.map almost_mono.color).nodup)

instance {α ι κ} (C : (ι → option α) → κ) : inhabited (color_focused C) :=
⟨⟨0, λ _, none, λ _, false.elim, multiset.nodup_zero⟩⟩

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

lemma apply_def {α ι} (l : line α ι) (x : α) : l x = λ i, (l.idx_fun i).get_or_else x := rfl

lemma apply_none {α ι} (l : line α ι) (x : α) (i : ι) (h : l.idx_fun i = none) : l x i = x :=
by simp only [option.get_or_else_none, h, l.apply_def]

lemma apply_some {α ι} (l : line α ι) {x a : α} {i : ι} (h : l.idx_fun i = some a) : l x i = a :=
by simp_rw [l.apply_def, option.mem_def.mp h, option.get_or_else_some]

@[simp] lemma map_apply {α α' ι} (f : α → α') (l : line α ι) (x : α) :
  l.map f (f x) = f ∘ l x :=
by simp only [line.apply_def, line.map, option.get_or_else_map]

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
by simp_rw [line.apply_def, line.diagonal, option.get_or_else_none]

/-- The Hales-Jewett theorem. This version has a restriction on universe levels which is necessary
for the proof. See `exists_mono_in_high_dimension` for a fully universe-polymorphic version. -/
private theorem exists_mono_in_high_dimension' :
  ∀ (α : Type u) [fintype α] (κ : Type (max v u)) [fintype κ],
  ∃ (ι : Type) (_ : fintype ι), ∀ C : (ι → α) → κ, ∃ l : line α ι, l.is_mono C :=
-- The proof proceeds by induction on `α`.
fintype.induction_empty_option
-- We have to show that the theorem is invariant under `α ≃ α'` for the induction to work.
(λ α α' e, forall_imp $ λ κ, forall_imp $ λ _, Exists.imp $ λ ι, Exists.imp $ λ _ h C,
  let ⟨l, c, lc⟩ := h (λ v, C (e ∘ v)) in
  ⟨l.map e, c, e.forall_congr_left.mp $ λ x, by rw [←lc x, line.map_apply]⟩)
begin -- This deals with the degenerate case where `α` is empty.
  introsI κ _,
  by_cases h : nonempty κ,
  { resetI, exact ⟨unit, infer_instance, λ C, ⟨default, classical.arbitrary _, pempty.rec _⟩⟩, },
  { exact ⟨empty, infer_instance, λ C, (h ⟨C (empty.rec _)⟩).elim⟩, }
end
begin -- Now we have to show that the theorem holds for `option α` if it holds for `α`.
  introsI α _ ihα κ _,
-- Later we'll need `α` to be nonempty. So we first deal with the trivial case where `α` is empty.
-- Then `option α` has only one element, so any line is monochromatic.
  by_cases h : nonempty α,
  work_on_goal 1 { refine ⟨unit, infer_instance, λ C, ⟨diagonal _ _, C (λ _, none), _⟩⟩,
    rintros (_ | ⟨a⟩), refl, exact (h ⟨a⟩).elim, },
-- The key idea is to show that for every `r`, in high dimension we can either find
-- `r` color focused lines or a monochromatic line.
  suffices key : ∀ r : ℕ, ∃ (ι : Type) (_ : fintype ι), ∀ C : (ι → (option α)) → κ,
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
  { exact ⟨empty, infer_instance, λ C, or.inl ⟨default, multiset.card_zero⟩⟩, },
-- Supposing the key claim holds for `r`, we need to show it for `r+1`. First pick a high enough
-- dimension `ι` for `r`.
  obtain ⟨ι, _inst, hι⟩ := ihr,
  resetI,
-- Then since the theorem holds for `α` with any number of colors, pick a dimension `ι'` such that
-- `ι' → α` always has a monochromatic line whenever it is `(ι → option α) → κ`-colored.
  specialize ihα ((ι → option α) → κ),
  obtain ⟨ι', _inst, hι'⟩ := ihα,
  resetI,
-- We claim that `ι ⊕ ι'` works for `option α` and `κ`-coloring.
  refine ⟨ι ⊕ ι', infer_instance, _⟩,
  intro C,
-- A `κ`-coloring of `ι ⊕ ι' → option α` induces an `(ι → option α) → κ`-coloring of `ι' → α`.
  specialize hι' (λ v' v, C (sum.elim v (some ∘ v'))),
-- By choice of `ι'` this coloring has a monochromatic line `l'` with color class `C'`, where
-- `C'` is a `κ`-coloring of `ι → α`.
  obtain ⟨l', C', hl'⟩ := hι',
-- If `C'` has a monochromatic line, then so does `C`. We use this in two places below.
  have mono_of_mono : (∃ l, is_mono C' l) → (∃ l, is_mono C l),
  { rintro ⟨l, c, hl⟩,
    refine ⟨l.horizontal (some ∘ l' (classical.arbitrary α)), c, λ x, _⟩,
    rw [line.horizontal_apply, ←hl, ←hl'], },
-- By choice of `ι`, `C'` either has `r` color-focused lines or a monochromatic line.
  specialize hι C',
  rcases hι with ⟨s, sr⟩ | _,
-- By above, we are done if `C'` has a monochromatic line.
  work_on_goal 1 { exact or.inr (mono_of_mono hι) },
-- Here we assume `C'` has `r` color focused lines. We split into cases depending on whether one of
-- these `r` lines has the same color as the focus point.
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

/-- The **Hales-Jewett theorem**: for any finite types `α` and `κ`, there exists a finite type `ι`
such that whenever the hypercube `ι → α` is `κ`-colored, there is a monochromatic combinatorial
line. -/
theorem exists_mono_in_high_dimension (α : Type u) [fintype α] (κ : Type v) [fintype κ] :
  ∃ (ι : Type) [fintype ι], ∀ C : (ι → α) → κ, ∃ l : line α ι, l.is_mono C :=
let ⟨ι, ιfin, hι⟩ := exists_mono_in_high_dimension' α (ulift κ)
in ⟨ι, ιfin, λ C, let ⟨l, c, hc⟩ := hι (ulift.up ∘ C) in ⟨l, c.down, λ x, by rw ←hc⟩ ⟩

end line

/-- A generalization of **Van der Waerden's theorem**: if `M` is a finitely colored commutative
monoid, and `S` is a finite subset, then there exists a monochromatic homothetic copy of `S`. -/
theorem exists_mono_homothetic_copy
  {M κ} [add_comm_monoid M] (S : finset M) [fintype κ] (C : M → κ) :
  ∃ (a > 0) (b : M) (c : κ), ∀ s ∈ S, C (a • s + b) = c :=
begin
  obtain ⟨ι, _inst, hι⟩ := line.exists_mono_in_high_dimension S κ,
  resetI,
  specialize hι (λ v, C $ ∑ i, v i),
  obtain ⟨l, c, hl⟩ := hι,
  set s : finset ι := { i ∈ finset.univ | l.idx_fun i = none } with hs,
  refine ⟨s.card, finset.card_pos.mpr ⟨l.proper.some, _⟩,
    ∑ i in sᶜ, ((l.idx_fun i).map coe).get_or_else 0, c, _⟩,
  { rw [hs, finset.sep_def, finset.mem_filter], exact ⟨finset.mem_univ _, l.proper.some_spec⟩, },
  intros x xs,
  rw ←hl ⟨x, xs⟩,
  clear hl, congr,
  rw ←finset.sum_add_sum_compl s,
  congr' 1,
  { rw ←finset.sum_const,
    apply finset.sum_congr rfl,
    intros i hi,
    rw [hs, finset.sep_def, finset.mem_filter] at hi,
    rw [l.apply_none _ _ hi.right, subtype.coe_mk], },
  { apply finset.sum_congr rfl,
    intros i hi,
    rw [hs, finset.sep_def, finset.compl_filter, finset.mem_filter] at hi,
    obtain ⟨y, hy⟩ := option.ne_none_iff_exists.mp hi.right,
    rw [l.apply_some hy.symm, ←hy, option.map_some', option.get_or_else_some] }
end

/-- `subspace η α ι` is the type of `η`-dimensional *combinatorial subspaces* of `ι → α`. We do not
allow degenerate subspaces. -/
structure subspace (η α ι : Type*) :=
(idx_fun : ι → α ⊕ η)
(proper : ∀ e, ∃ i, idx_fun i = sum.inr e)

namespace subspace

/-- The combinatorial subspace corresponding to the identity embedding `(ι → α) → (ι → α)`. -/
instance {α ι} : inhabited (subspace ι α ι) := ⟨⟨sum.inr, λ i, ⟨i, rfl⟩⟩⟩

instance (η α ι) : has_coe_to_fun (subspace η α ι) (λ _, (η → α) → ι → α) :=
⟨λ l x i, (l.idx_fun i).elim id x⟩

lemma apply_def {η α ι} (l : subspace η α ι) (x : η → α) (i : ι) :
  l x i = (l.idx_fun i).elim id x := rfl

lemma apply_inl {η α ι} {l : subspace η α ι} {x : η → α} {i : ι} {y : α}
  (h : l.idx_fun i = sum.inl y) : l x i = y :=
by rw [l.apply_def, h, sum.elim_inl, id.def]

lemma apply_inr {η α ι} {l : subspace η α ι} {x : η → α} {i : ι} {j : η}
  (h : l.idx_fun i = sum.inr j) : l x i = x j :=
by rw [l.apply_def, h, sum.elim_inr]

/-- Given a coloring `C` of `ι → α` and a combinatorial subspace `l` of `ι → α`, `l.is_mono C` means
that `l` is monochromatic with regard to `C`. -/
def is_mono {η α ι κ} (C : (ι → α) → κ) (l : subspace η α ι) : Prop :=
∃ c, ∀ x, C (l x) = c

/-- The **extended Hales-Jewett theorem**. We deduce it from the ordinary Hales-Jewett theorem. -/
theorem exists_mono_in_high_dimension (α κ) (η : Type u) [fintype α] [fintype κ] [fintype η] :
  ∃ (ι : Type u) (_ : fintype ι), ∀ C : (ι → α) → κ, ∃ l : subspace η α ι, l.is_mono C :=
begin
  obtain ⟨ι, ιfin, hι⟩ := line.exists_mono_in_high_dimension (η → α) κ,
  resetI,
  refine ⟨ι × η, infer_instance, _⟩,
  intro C,
  specialize hι (C ∘ function.uncurry),
  obtain ⟨l, c, lC⟩ := hι,
  refine ⟨⟨λ p, (l.idx_fun p.fst).elim (sum.inr p.snd) (λ x, sum.inl (x p.snd)), _⟩, c, _⟩,
  { intro e, obtain ⟨i, hi⟩ := l.proper, use (i, e), rw [hi, option.elim] },
  intro x,
  specialize lC x,
  convert lC,
  funext,
  cases i with i e,
  dsimp only [function.uncurry_apply_pair, line.apply_def, subspace.apply_def],
  cases l.idx_fun i with o,
  { simp only [option.elim, option.get_or_else_none, sum.elim_inr], },
  { simp only [option.get_or_else_some, option.elim, sum.elim_inl, id.def], }
end

/-- A variant of the extended Hales-Jewett theorem `exists_mono_in_high_dimension` where the
returned type is some `fin n` instead of a general fintype. -/
theorem exists_mono_in_high_dimension_fin (α κ η) [fintype α] [fintype κ] [fintype η] :
  ∃ n, ∀ C : (fin n → α) → κ, ∃ l : subspace η α (fin n), l.is_mono C :=
begin
  obtain ⟨ι, ιfin, hι⟩ := exists_mono_in_high_dimension α κ η,
  resetI,
  refine ⟨fintype.card ι, λ C, _⟩,
  specialize hι (λ v, C (v ∘ (fintype.equiv_fin _).symm)),
  obtain ⟨l, c, cl⟩ := hι,
  refine ⟨⟨l.idx_fun ∘ (fintype.equiv_fin _).symm, _⟩, c, cl⟩,
  intro e,
  obtain ⟨i, hi⟩ := l.proper e,
  use fintype.equiv_fin _ i,
  simpa only [equiv.symm_apply_apply, function.comp_app] using hi,
end

end subspace
end combinatorics
