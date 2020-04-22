/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import analysis.analytic.composition

noncomputable theory

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{F : Type*} [normed_group F] [normed_space 𝕜 F]
{G : Type*} [normed_group G] [normed_space 𝕜 G]
{H : Type*} [normed_group H] [normed_space 𝕜 H]

open filter list
open_locale topological_space classical

/-- Rewriting equality in the dependent type `Σ (a : composition n), composition a.length)` in
non-dependent terms with lists, requiring that the blocks coincide. -/
lemma composition_sigma_composition_eq_iff {n : ℕ}
  (i j : Σ (a : composition n), composition a.length) :
  i = j ↔ i.1.blocks = j.1.blocks ∧ i.2.blocks = j.2.blocks :=
begin
  split,
  { assume H,
    rw H,
    simp only [eq_self_iff_true, and_self] },
  { rcases i with ⟨a, b⟩,
    rcases j with ⟨a', b'⟩,
    rintros ⟨h, h'⟩,
    have H : a = a', by { ext1, exact h },
    induction H,
    simp only [true_and, eq_self_iff_true, heq_iff_eq],
    ext1,
    exact h' }
end

/-- Rewriting equality in the dependent type
`Σ (c : composition n), Π (i : fin c.length), composition (c.blocks_fun i)` in
non-dependent terms with lists, requiring that the lists of blocks coincide. -/
lemma composition_sigma_pi_composition_eq_iff {n : ℕ}
  (u v : Σ (c : composition n), Π (i : fin c.length), composition (c.blocks_fun i)) :
  u = v ↔ of_fn (λ i, (u.2 i).blocks) = of_fn (λ i, (v.2 i).blocks) :=
begin
  refine ⟨λ H, by rw H, λ H, _⟩,
  rcases u with ⟨a, b⟩,
  rcases v with ⟨a', b'⟩,
  dsimp at H,
  have h : a = a',
  { ext1,
    have : map list.sum (of_fn (λ (i : fin (composition.length a)), (b i).blocks)) =
      map list.sum (of_fn (λ (i : fin (composition.length a')), (b' i).blocks)), by rw H,
    simp only [map_of_fn] at this,
    change of_fn (λ (i : fin (composition.length a)), (b i).blocks.sum) =
      of_fn (λ (i : fin (composition.length a')), (b' i).blocks.sum) at this,
    simpa [composition.blocks_sum, composition.of_fn_blocks_fun] using this },
  induction h,
  simp only [true_and, eq_self_iff_true, heq_iff_eq],
  ext i : 2,
  have : nth_le (of_fn (λ (i : fin (composition.length a)), (b i).blocks)) i.1 (by simp [i.2]) =
         nth_le (of_fn (λ (i : fin (composition.length a)), (b' i).blocks)) i.1 (by simp [i.2]) :=
    nth_le_of_eq H _,
  rwa [nth_le_of_fn, nth_le_of_fn] at this
end

def composition_sigma_composition_equiv_composition_sigma_pi_composition (n : ℕ) :
  (Σ (a : composition n), composition a.length) ≃
  (Σ (c : composition n), Π (i : fin c.length), composition (c.blocks_fun i)) :=
{ to_fun := λ i, begin
    rcases i with ⟨a, b⟩,
    let l := a.blocks.split_wrt_composition b,
    let c : composition n :=
    { blocks := l.map sum,
      blocks_pos := begin
        refine forall_mem_map_iff.2 (λ j hj, _),
        refine lt_of_lt_of_le (length_pos_of_mem_split_wrt_composition hj)
          (length_le_sum_of_one_le _ (λ i hi, _)),
        have : i ∈ a.blocks,
        { rw ← a.blocks.join_split_wrt_composition b,
          exact mem_join_of_mem hj hi },
        exact composition.one_le_blocks a this
      end,
      blocks_sum := by { rw [← sum_join, join_split_wrt_composition], exact a.blocks_sum } },
    exact ⟨c, λ i,
    { blocks := nth_le l i.val begin
        have : c.length = l.length,
          by { change length (map list.sum l) = l.length, exact length_map _ _ },
        rw ← this,
        exact i.2
      end,
      blocks_pos := begin
        assume i hi,
        have : i ∈ l.join := mem_join_of_mem (nth_le_mem _ _ _) hi,
        rw join_split_wrt_composition at this,
        exact a.blocks_pos this
      end,
      blocks_sum := by simp [composition.blocks_fun] }⟩
  end,
  inv_fun := λ i, begin
    rcases i with ⟨c, d⟩,
    let a : composition n :=
    { blocks := (of_fn (λ i, (d i).blocks)).join,
      blocks_pos := begin
        simp only [and_imp, mem_join, exists_imp_distrib, forall_mem_of_fn_iff],
        exact λ i j hj, composition.blocks_pos _ hj
      end,
      blocks_sum := by simp [sum_of_fn, composition.blocks_sum, composition.sum_blocks_fun] },
    let b : composition a.length :=
    { blocks := of_fn (λ i, (d i).length),
      blocks_pos := begin
        refine forall_mem_of_fn_iff.2 (λ j, composition.length_pos_of_pos _ _),
        exact composition.blocks_pos' _ _ _
      end,
      blocks_sum := begin
        change _ = (join (of_fn (λ (i : fin (composition.length c)), (d i).blocks))).length,
        simp [sum_of_fn]
      end },
    exact ⟨a, b⟩
  end,
  left_inv := begin
    -- the fact that we have a left inverse is essentially contained in
    -- `join_split_wrt_composition`, but we need to massage it to take care of the dependent
    -- setting.
    rintros ⟨a, b⟩,
    rw composition_sigma_composition_eq_iff,
    split,
    { dsimp,
      conv_rhs { rw [← join_split_wrt_composition a.blocks b,
        ← of_fn_nth_le (split_wrt_composition a.blocks b)] },
      have A := length_map list.sum (split_wrt_composition a.blocks b),
      congr,
      exact A,
      rw fin.heq_fun_iff A,
      assume i,
      refl },
    { dsimp,
      conv_rhs { rw [← of_fn_nth_le b.blocks] },
      congr' 1,
      { dsimp only [composition.length],
        simp only [composition.blocks_length, length_map, length_split_wrt_composition] },
      { rw fin.heq_fun_iff,
        { assume i,
          dsimp only [composition.length],
          rw [nth_le_map_rev length, nth_le_of_eq (map_length_split_wrt_composition _ _)] },
        { dsimp only [composition.length],
          simp only [composition.blocks_length, length_map, length_split_wrt_composition] } } }
  end,
  right_inv := begin
    -- the fact that we have a right inverse is essentially contained in
    -- `split_wrt_composition_join`, but we need to massage it to take care of the dependent
    -- setting.
    rintros ⟨c, d⟩,
    have : map list.sum (of_fn (λ (i : fin (composition.length c)), (d i).blocks)) = c.blocks,
      by simp [map_of_fn, (∘), composition.blocks_sum, composition.of_fn_blocks_fun],
    rw composition_sigma_pi_composition_eq_iff,
    dsimp,
    congr,
    { ext1,
      dsimp,
      rwa split_wrt_composition_join,
      simp [(∘)] },
    { rw fin.heq_fun_iff,
      { assume i,
        rw nth_le_of_eq (split_wrt_composition_join _ _ _),
        { simp },
        { simp [(∘)] } },
      { congr,
        ext1,
        dsimp,
        rwa split_wrt_composition_join,
        simp [(∘)] } }
  end }

/-! ### Composing formal multilinear series -/

namespace formal_multilinear_series

/- Let us prove the associativity of the composition of formal power series. By definition,
```
(r.comp q).comp p n v
= ∑_{i₁ + ... + iₖ = n} (r.comp q)ₖ (p_{i₁} (v₀, ..., v_{i₁ -1}), p_{i₂} (...), ..., p_{iₖ}(...))
= ∑_{a : composition n} (r.comp q) a.length (apply_composition p a v)
```
decomposing `r.comp q` in the same way, we get
```
(r.comp q).comp p n v
= ∑_{a : composition n} ∑_{b : composition a.length}
  r b.length (apply_composition q b (apply_composition p a v))
```
On the other hand,
```
r.comp (q.comp p) n v = ∑_{c : composition n} r c.length (apply_composition (q.comp p) c v)
```
Here, `apply_composition (q.comp p) c v` is a vector of length `c.length`, whose `i`-th term is
given by `(q.comp p) (c.blocks_fun i) (v_l, v_{l+1}, ..., v_{m-1})` where `{l, ..., m-1}` is the
`i`-th block in the composition `c`, of length `c.blocks_fun i` by definition. To compute this term,
we expand it as `∑_{dᵢ : composition (c.blocks_fun i)} q dᵢ.length (apply_composition p dᵢ v')`,
where `v' = (v_l, v_{l+1}, ..., v_{m-1})`. Therefore, we get
```
r.comp (q.comp p) n v =
∑_{c : composition n} ∑_{d₀ : composition (c.blocks_fun 0),
  ..., d_{c.length - 1} : composition (c.blocks_fun (c.length - 1))}
  r c.length (λ i, q dᵢ.length (apply_composition p dᵢ v'ᵢ))
```
To show that these terms coincide, we need to explain how to reindex the sums to put them in
bijection (and then the terms we are summing will correspond to each other). Suppose we have a
composition `a` of `n`, and a composition `b` of `a.length`. Then `b` indicates how to group
together some blocks of `a`, giving altogether `b.length` blocks of blocks. These blocks of blocks
can be called `d₀, ..., d_{a.length - 1}`, and one obtains a composition `c` of `n` by saying that
each `dᵢ` is one single block. Conversely, if one starts from `c` and the `dᵢ`s, one can concatenate
the `dᵢ`s to obtain a composition `a` of `n`, and register the lengths of the `dᵢ`s in a composition
`b` of `a.length`.

An example might be enlightening. Suppose `a = [2, 2, 3, 4, 2]`. It is a composition of
length 5 of 13. The content of the blocks may be represented as `0011222333344`.
Now take `b = [2, 3]` as a composition of `a.length = 5`. It says that the first 2 blocks of `a`
should be merged, and the last 3 blocks of `a` should be merged, giving a new composition of `13`
made of two blocks of length `4` and `9`, i.e., `c = [4, 7]`. But one can also remember that
the new first block was initially made of two blocks of size `2`, so `d₀ = [2, 2]`, and the new
second block was initially made of three blocks of size `3`, `4` and `2`, so `d₁ = [3, 4, 2]`.
-/

theorem comp_assoc (r : formal_multilinear_series 𝕜 G H) (q : formal_multilinear_series 𝕜 F G)
  (p : formal_multilinear_series 𝕜 E F) :
  (r.comp q).comp p = r.comp (q.comp p) :=
begin
  ext n v,
  /- First, rewrite the two compositions appearing in the theorem as two sums over complicated
  sigma types, as in the description of the proof above. -/
  let f : (Σ (a : composition n), composition a.length) → H :=
    λ ⟨a, b⟩, r b.length (apply_composition q b (apply_composition p a v)),
  let g : (Σ (c : composition n), Π (i : fin c.length), composition (c.blocks_fun i)) → H :=
    λ ⟨c, d⟩, r c.length
      (λ (i : fin c.length), q (d i).length (apply_composition p (d i) (v ∘ c.embedding i))),
  suffices A : finset.univ.sum f = finset.univ.sum g,
  { dsimp [formal_multilinear_series.comp],
    simp only [continuous_multilinear_map.sum_apply, comp_along_composition_apply],
    rw ← @finset.sum_sigma _ _ _ _ (finset.univ : finset (composition n)) _ f,
    dsimp [apply_composition],
    simp only [continuous_multilinear_map.sum_apply, comp_along_composition_apply,
      continuous_multilinear_map.map_sum],
    rw ← @finset.sum_sigma _ _ _ _ (finset.univ : finset (composition n)) _ g,
    exact A },
  /- Now, we should construct a bijection between these two types, to show that the sums
  coincide. -/


end



end formal_multilinear_series
