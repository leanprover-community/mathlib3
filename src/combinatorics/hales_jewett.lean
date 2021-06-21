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

We consistently work with finite types instead of natural numbers. That is, we write `m, n, k` for
(finite) types where one might traditionally take `m, n, k` to be natural numbers. This allows us to
work directly with `m`, `option m`, `(n → m) → k`, and `n ⊕ n'` instead of `fin m`, `fin (m+1)`,
`fin (k^(m^n))`, and `fin (n + n')`.

We take '`X` is monochromatic' to mean 'there exists a color `c` such that every point of `X` has
the color `c`' as opposed to 'any `x y : X` have the same color' since the former is generally
easier to work with. This means that our formulation of Hales-Jewett would be false when `m` and `k`
are both empty (then there can be a coloring even though there is no color). Thus we require `m` to
be nonempty in the statement of `exists_mono_in_high_dimension`.

We do not prove the finitary version of Van der Waerden's theorem (which is equivalent to the
infinite one by compactness), although it follows from the same proof.

In principle our proof should give computable upper bounds on the numbers `HJ(m, k)`, but this would
require rewriting the proof to avoid `Prop`, and the upper bounds are enormous anyway.

## Main results

- `combinatorics.line.exists_mono_in_high_dimension m k`: the Hales-Jewett theorem.
- `combinatorics.exists_mono_homothetic_copy M S f k C`: a generalization of Van der Waerden's
theorem to an arbitrary commutative monoid. The proof is a simple application of Hales-Jewett.

## Tags

combinatorial line, Ramsey theory, arithmetic progession

### References

* https://en.wikipedia.org/wiki/Hales%E2%80%93Jewett_theorem

Note that this file does not use the same notation as Wikipedia.

-/

open_locale classical
open_locale big_operators

instance (n : pnat) : nonempty (fin n) := ⟨⟨0, n.pos⟩⟩

/-- An induction principle for types analogous to `pnat.rec_on`. To prove a statement about
all nonempty finite types, it suffices to consider `unit` and `option α` where we know the
statement for `α`, provided that our statement is preserved by `≃`.-/
lemma fintype_induction {P : Type → Prop} (of_equiv : ∀ {α β}, α ≃ β → P α → P β)
  (h_unit : P unit) (h_option : ∀ {α} [fintype α] [nonempty α], P α → P (option α))
  (α) [fintype α] [nonempty α] : P α :=
begin
  suffices : ∀ n : pnat, P (fin n),
  { refine of_equiv (fintype.equiv_fin α).symm
      (this ⟨fintype.card α, finset.card_pos.mpr finset.univ_nonempty⟩), },
  intro n, apply n.rec_on,
  exact of_equiv fin_one_equiv.symm h_unit,
  exact λ _ ih, of_equiv (fin_succ_equiv _).symm (h_option ih),
end

namespace combinatorics

/-- The type of combinatorial lines. A line `l : line m n` in the hypercube `n → m` defines a
function `m → (n → m)` to the hypercube, such that for each coordinate `i : n`, the function
`l x i` is either identically `x` or constant. We require lines to be nontrivial, in the sense
that `l x i` is identically `x` for at least one `i`.

Formally, a line is represented by the function `l.idx_fun : n → option m` which says whether
`l x i` is identically `x` (corresponding to `l.idx_fun i = none`) or constantly `y`
(corresponding to `l.idx_fun i = some y`). When `m` has size `1` there can be many elements of
`line m n` defining the same function. -/
structure line (m n : Type) : Type :=
(idx_fun : n → option m)
(proper : ∃ i, idx_fun i = none)

namespace line

/- This lets us treat a line `l : line m n` as a function `m → (n → m)`. -/
instance (m n) : has_coe_to_fun (line m n) :=
⟨λ _, m → n → m, λ l x i, (l.idx_fun i).get_or_else x⟩

/-- The type of lines that are only one color except possibly at their endpoints. -/
@[nolint has_inhabited_instance]
structure almost_mono {m n k : Type} (C : (n → option m) → k) :=
(line : line (option m) n)
(color : k)
(has_color : ∀ x : m, C (line (some x)) = color)

/-- The type of families of lines such that
- each line is only one color except possibly at its endpoint
- the lines all have the same endpoint
- the colors of the lines are distinct.
Used in the proof `exists_mono_in_high_dimension`. -/
structure color_focused {m n k} (C : (n → option m) → k) :=
(lines : multiset (almost_mono C))
(focus : n → option m)
(is_focused : ∀ p : almost_mono C, p ∈ lines → p.line none = focus)
(distinct_colors : (lines.map almost_mono.color).nodup)

instance {m n k} (C : (n → option m) → k) : inhabited (color_focused C) :=
⟨⟨0, λ _, none, λ _, false.elim, multiset.nodup_zero⟩⟩

/-- The diagonal line. It is the identity at every coordinate. -/
def diagonal (m n) [nonempty n] : line m n :=
{ idx_fun := λ _, none,
  proper  := ⟨classical.arbitrary n, rfl⟩ }

instance (m n) [nonempty n] : inhabited (line m n) := ⟨diagonal m n⟩

/-- A line is monochromatic if all its points are the same color. -/
def is_mono {m n k : Type} (C : (n → m) → k) (l : line m n) : Prop :=
∃ c, ∀ x, C (l x) = c

/-- A function `m → m'` determines a function `line m n → line m' n`. For a coordinate `i`,
`l.map f` is the identity at `i` if `l` is, and constantly `f y` if `l` is constantly `y` at `i`. -/
def map {m m' n} (f : m → m') (l : line m n) : line m' n :=
{ idx_fun := λ i, (l.idx_fun i).map f,
  proper  := ⟨l.proper.some, by rw [l.proper.some_spec, option.map_none'] ⟩ }

/-- A point in `n → m` and a line in `n' → m` determine a line in `n ⊕ n' → m`. -/
def vertical {m n n'} (v : n → m) (l : line m n') : line m (n ⊕ n') :=
{ idx_fun := sum.elim (some ∘ v) l.idx_fun,
  proper  := ⟨sum.inr l.proper.some, l.proper.some_spec⟩ }

/-- A line in `n → m` and a point in `n' → m` determine a line in `n ⊕ n' → m`. -/
def horizontal {m n n'} (l : line m n) (v : n' → m) : line m (n ⊕ n') :=
{ idx_fun := sum.elim l.idx_fun (some ∘ v),
  proper  := ⟨sum.inl l.proper.some, l.proper.some_spec⟩ }

/-- One line in `n → m` and one in `n' → m` together determine a line in `n ⊕ n' → m`. -/
def prod {m n n'} (l : line m n) (l' : line m n') : line m (n ⊕ n') :=
{ idx_fun := sum.elim l.idx_fun l'.idx_fun,
  proper  := ⟨sum.inl l.proper.some, l.proper.some_spec⟩ }

lemma apply {m n} (l : line m n) (x : m) : l x = λ i, (l.idx_fun i).get_or_else x := rfl

@[simp] lemma apply_none {m n} (l : line m n) (x : m) (i : n)
  (h : l.idx_fun i = none) : l x i = x :=
by simp only [option.get_or_else_none, h, l.apply]

@[simp] lemma apply_of_ne_none {m n} (l : line m n) (x : m) (i : n)
  (h : l.idx_fun i ≠ none) : some (l x i) = l.idx_fun i :=
by rw [l.apply, option.get_or_else_of_ne_none h]

@[simp] lemma map_apply {m m' n} (f : m → m') (l : line m n) (x : m) :
  l.map f (f x) = f ∘ l x :=
by simp only [line.apply, line.map, option.get_or_else_map]

@[simp] lemma vertical_apply {m n n'} (v : n → m) (l : line m n') (x : m) :
  l.vertical v x = sum.elim v (l x) :=
by { funext i, cases i; refl }

@[simp] lemma horizontal_apply {m n n'} (l : line m n) (v : n' → m) (x : m) :
  l.horizontal v x = sum.elim (l x) v :=
by { funext i, cases i; refl }

@[simp] lemma prod_apply {m n n'} (l : line m n) (l' : line m n') (x : m) :
  l.prod l' x = sum.elim (l x) (l' x) :=
by { funext i, cases i; refl }

/-- The Hales-Jewett theorem: for any finite types `m` and `k` with `m` nonempty, there exists
another finite type `n` such that whenever the hypercube `n → m` is `k`-colored, there is
a monochromatic combinatorial line. -/
theorem exists_mono_in_high_dimension : ∀ m [fintype m] [nonempty m] k [fintype k],
  ∃ n [fintype n], ∀ C : (n → m) → k, ∃ l : line m n, l.is_mono C :=
-- The proof proceeds by induction on `m`.
fintype_induction
-- We have to show that the theorem is invariant under `m ≃ m'` for the induction to work.
(λ m m' e, forall_imp $ λ k, forall_imp $ λ _, Exists.imp $ λ n, Exists.imp $ λ _ h C,
  let ⟨l, c, lc⟩ := h (λ v, C (e ∘ v)) in
  ⟨l.map e, c, e.forall_congr_left.mp $ λ x, by rw [←lc x, line.map_apply]⟩)
-- The base case `m = unit` is easy since any line is monochromatic.
(λ k _, ⟨unit, infer_instance, λ C, ⟨diagonal _ _, C (λ _, unit.star), λ ⟨⟩, rfl⟩⟩)
begin -- Now we have to show that the theorem holds for `unit m` if it holds for `m`.
  introsI m _ _ ihm k _,
-- The key idea is to show that for every `r`, in high dimension we can either find
-- `r` color focused lines or a monochromatic line.
  suffices key : ∀ r : ℕ, ∃ (n : Type) [fintype n], ∀ C : (n → (option m)) → k,
    (∃ s : color_focused C, s.lines.card = r) ∨ (∃ l, is_mono C l),
-- Given the key claim, we simply take `r = |k| + 1`. We cannot have this many distinct colors so
-- we must be in the second case, where there is a monochromatic line.
  { obtain ⟨n, nn, hn⟩ := key (fintype.card k + 1),
    refine ⟨n, nn, λ C, (hn C).resolve_left _⟩,
    rintro ⟨s, sr⟩,
    apply nat.not_succ_le_self (fintype.card k),
    rw [←nat.add_one, ←sr, ←multiset.card_map, ←finset.card_mk],
    exact finset.card_le_univ ⟨_, s.distinct_colors⟩ },
-- We now prove the key claim, by induction on `r`.
  intro r,
  induction r with r ihr,
-- The base case `r = 0` is trivial as the empty collection is color-focused.
  { exact ⟨empty, infer_instance, λ C, or.inl ⟨default _, multiset.card_zero⟩⟩, },
-- Supposing the key claim holds for `r`, we need to show it for `r+1`. First pick a high enough
-- dimension `n` for `r`.
  obtain ⟨n, _inst, hn⟩ := ihr,
  resetI,
-- Then since the theorem holds for `m` with and number of colors, pick a dimension `n'` such that
-- `n' → m` always has a monochromatic line whenever it is colored with `(n → m) → k` colors.
  specialize ihm ((n → option m) → k),
  obtain ⟨n', _inst, hn'⟩ := ihm,
  resetI,
-- We claim that `n ⊕ n'` works for `unit m`.
  refine ⟨n ⊕ n', infer_instance, _⟩,
  intro C,
-- A `k`-coloring of `n ⊕ n' → m` induces a `(n → m) → k`-coloring of `n' → m`.
  specialize hn' (λ v' v, C (sum.elim v (some ∘ v'))),
-- By choice of `n'` this coloring has a monochromatic line `l'` with color class `C'`, where
-- `C'` is a `k`-coloring of `n → m`.
  obtain ⟨l', C', hl'⟩ := hn',
-- If `C'` has a monochromatic line, then so does `C`. We will use this twice.
  have mono_of_mono : (∃ l, is_mono C' l) → (∃ l, is_mono C l),
  { rintro ⟨l, c, hl⟩,
    refine ⟨l.horizontal (some ∘ l' (classical.arbitrary m)), c, λ x, _⟩,
    rw [line.horizontal_apply, ←hl, ←hl'], },
-- By choice of `n`, `C'` either has `r` color focused lines or a monochromatic line.
  specialize hn C',
  rcases hn with ⟨s, sr⟩ | _,
-- By above, we are done if `C'` has a monochromatic line.
  work_on_goal 1 { exact or.inr (mono_of_mono hn) },
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
  (k : Type) [fintype k] (C : M → k) :
  ∃ (a : pnat) (b : M) (c : k), ∀ s, C ((a : ℕ) • (f s) + b) = c :=
begin
  by_cases hS : nonempty S,
  work_on_goal 1 { exact ⟨1, 0, (C 0), λ s, (hS ⟨s⟩).elim⟩, },
  resetI,
  obtain ⟨n, _inst, hn⟩ := line.exists_mono_in_high_dimension S k,
  resetI,
  specialize hn (λ v, C $ ∑ i, f (v i)),
  obtain ⟨l, c, hl⟩ := hn,
  set s : finset n := { i ∈ finset.univ | l.idx_fun i = none } with hs,
  refine ⟨⟨s.card, finset.card_pos.mpr ⟨l.proper.some, _⟩⟩,
    ∑ i in sᶜ, f (l (classical.arbitrary S) i), c, _⟩,
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
    congr' 1, apply option.some_injective,
    rw [hs, finset.sep_def, finset.compl_filter, finset.mem_filter] at hi,
    simp only [l.apply_of_ne_none _ _ hi.right], },
end

end combinatorics
