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

open filter
open_locale topological_space classical


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
made of two blocks of length `4` and `7`, i.e., `c = [4, 7]`. But one can also remember that
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
