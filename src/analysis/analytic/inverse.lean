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

@[to_additive]
lemma fin.prod_univ_eq_prod_range {α : Type*} [comm_monoid α] (f : ℕ → α) (n : ℕ) :
  finset.univ.prod (λ (i : fin n), f i.val) = (finset.range n).prod f :=
begin
  apply finset.prod_bij (λ (a : fin n) ha, a.val),
  { assume a ha, simp [a.2] },
  { assume a ha, refl },
  { assume a b ha hb H, exact (fin.ext_iff _ _).2 H },
  { assume b hb, exact ⟨⟨b, list.mem_range.mp hb⟩, finset.mem_univ _, rfl⟩, }
end

/-- A telescoping sum along `{0, ..., n-1}` reduces to the difference of the last and first terms
when the function we are summing is monotone. -/
lemma sum_range_sub_of_monotone {f : ℕ → ℕ} (h : monotone f) (n : ℕ) :
  (finset.range n).sum (λ i, f (i+1) - f i) = f n - f 0 :=
begin
  induction n with n IH,
  simp,
  rw [finset.sum_range_succ, IH, nat.succ_eq_add_one],
  have : f n ≤ f (n+1) := h (nat.le_succ _),
  have : f 0 ≤ f n := h (nat.zero_le _),
  omega
end

.

namespace list

variable {α : Type*}

@[simp] lemma forall_mem_map_iff {β : Type*} {l : list α} {f : α → β} {P : β → Prop} :
  (∀ i ∈ l.map f, P i) ↔ ∀ j ∈ l, P (f j) :=
begin
  split,
  { assume H j hj,
    exact H (f j) (mem_map_of_mem f hj) },
  { assume H i hi,
    rcases mem_map.1 hi with ⟨j, hj, ji⟩,
    rw ← ji,
    exact H j hj }
end

/-- Taking the first `l₁.length + i` elements in `l₁ ++ l₂` is the same as appending the first
`i` elements of `l₂` to `l₁`. -/
lemma take_append {l₁ l₂ : list α} (i : ℕ) :
  take (l₁.length + i) (l₁ ++ l₂) = l₁ ++ (take i l₂) :=
begin
  induction l₁, { simp },
  have : length l₁_tl + 1 + i = (length l₁_tl + i).succ, by { rw nat.succ_eq_add_one, abel },
  simp only [cons_append, length, this, take_cons, l₁_ih, eq_self_iff_true, and_self]
end

/-- Taking the elements starting from `l₁.length + i` in `l₁ + l₂` is the same as taking the
elements starting from `i` in `l₂`. -/
lemma drop_append {l₁ l₂ : list α} (i : ℕ) :
  drop (l₁.length + i) (l₁ ++ l₂) = drop i l₂ :=
begin
  induction l₁, { simp },
  have : length l₁_tl + 1 + i = (length l₁_tl + i).succ, by { rw nat.succ_eq_add_one, abel },
  simp only [cons_append, length, this, drop, l₁_ih]
end

/-- In a join, taking the first elements up to an index which is the sum of the lengths of the
first `i` sublists, is the same as taking the join of the first `i` sublists. -/
lemma take_sum_join (L : list (list α)) (i : ℕ) :
  L.join.take ((L.map length).take i).sum = (L.take i).join :=
begin
  induction L generalizing i, { simp },
  cases i, { simp },
  simp [take_append, L_ih]
end

/-- In a join, taking all the elements starting from an index which is the sum of the lengths of the
first `i` sublists, is the same as taking the join of the sublists starting from the `i`-th one. -/
lemma drop_sum_join (L : list (list α)) (i : ℕ) :
  L.join.drop ((L.map length).take i).sum = (L.drop i).join :=
begin
  induction L generalizing i, { simp },
  cases i, { simp },
  simp [drop_append, L_ih],
end

/-- Taking only the first `i+1` elements in a list, and then removing the first `i` ones, one is
left with a list of length `1` made of the `i`-th element of the original list. -/
lemma drop_take_succ_eq_cons_nth_le (L : list α) {i : ℕ} (hi : i < L.length) :
  (L.take (i+1)).drop i = [nth_le L i hi] :=
begin
  induction L generalizing i,
  { simp only [length] at hi, exact (nat.not_succ_le_zero i hi).elim },
  cases i, { simp },
  have : i < L_tl.length,
  { simp at hi,
    exact nat.lt_of_succ_lt_succ hi },
  simp [L_ih this],
  refl
end

/-- If two lists coincide, then their `i`-th elements coincide. To speak about the `i`-th element
in a list, one needs to know that `i` is at most the length of the list. In this lemma, we provide
as an assumption that `i` is smaller than the length of the first list, and a proof that it is
smaller than the length of the second list is constructed. This is useful for rewrites, avoiding
dependent types issues. -/
lemma nth_le_of_eq {L L' : list α} (h : L = L') {i : ℕ} (hi : i < L.length) :
  nth_le L i hi = nth_le L' i (h ▸ hi) :=
by { congr, exact h}

/-- The `i`-th element of a list coincides with the `i`-th element of any of its prefixes of
length `> i`. -/
lemma nth_le_take (L : list α) {i j : ℕ} (hi : i < L.length) (hj : i < j) :
  nth_le L i hi = nth_le (L.take j) i (by { rw length_take, exact lt_min hj hi }) :=
by { rw nth_le_of_eq (take_append_drop j L).symm hi, exact nth_le_append _ _ }

/-- The `i + j`-th element of a list coincides with the `j`-th element of the list obtained by
dropping the first `i` elements. -/
lemma nth_le_drop (L : list α) {i j : ℕ} (h : i + j < L.length) :
  nth_le L (i + j) h = nth_le (L.drop i) j
begin
  have A : i < L.length := lt_of_le_of_lt (nat.le.intro rfl) h,
  rw (take_append_drop i L).symm at h,
  simpa only [le_of_lt A, min_eq_left, add_lt_add_iff_left, length_take, length_append] using h
end :=
begin
  have A : length (take i L) = i, by simp [le_of_lt (lt_of_le_of_lt (nat.le.intro rfl) h)],
  rw [nth_le_of_eq (take_append_drop i L).symm h, nth_le_append_right];
  simp [A]
end

/-- In a join of sublists, taking the slice between the indices `A` and `B - 1` gives back the
original sublist of index `i` if `A` is the sum of the lenghts of sublists of index `< i`, and
`B` is the sum of the lengths of sublists of index `≤ i`. -/
lemma drop_take_succ_join_eq_nth_le (L : list (list α)) {i : ℕ} (hi : i < L.length) :
  (L.join.take ((L.map length).take (i+1)).sum).drop ((L.map length).take i).sum = nth_le L i hi :=
begin
  have : (L.map length).take i = ((L.take (i+1)).map length).take i, by simp [map_take, take_take],
  simp [take_sum_join, this, drop_sum_join, drop_take_succ_eq_cons_nth_le _ hi]
end

/-- Auxiliary lemma to control elements in a join. -/
lemma sum_take_map_length_lt1 (L : list (list α)) {i j : ℕ}
  (hi : i < L.length) (hj : j < (nth_le L i hi).length) :
  ((L.map length).take i).sum + j < ((L.map length).take (i+1)).sum :=
by simp [hi, sum_take_succ, hj]

/-- Auxiliary lemma to control elements in a join. -/
lemma sum_take_map_length_lt2 (L : list (list α)) {i j : ℕ}
  (hi : i < L.length) (hj : j < (nth_le L i hi).length) :
  ((L.map length).take i).sum + j < L.join.length :=
begin
  convert lt_of_lt_of_le (sum_take_map_length_lt1 L hi hj) (monotone_sum_take _ hi),
  have : L.length = (L.map length).length, by simp,
  simp [this, -length_map]
end

/-- The `n`-th element in a join of sublists is the `j`-th element of the `i`th sublist,
where `n` can be obtained in terms of `i` and `j` by adding the lengths of all the sublists
of index `< i`, and adding `j`. -/
lemma nth_le_join (L : list (list α)) {i j : ℕ}
  (hi : i < L.length) (hj : j < (nth_le L i hi).length) :
  nth_le L.join (((L.map length).take i).sum + j) (sum_take_map_length_lt2 L hi hj) =
  nth_le (nth_le L i hi) j hj :=
by rw [nth_le_take L.join (sum_take_map_length_lt2 L hi hj) (sum_take_map_length_lt1 L hi hj),
  nth_le_drop, nth_le_of_eq (drop_take_succ_join_eq_nth_le L hi)]


variable {n : ℕ}

/-- Given a list of length `n` and a composition `[i₁, ..., iₖ]` of `n`, split `l` into a list of
`k` lists corresponding to the blocks of the composition, of respective lengths `i₁`, ..., `iₖ`.
This makes sense mostly when `n = l.length`, but this is not necessary for the definition. -/
def split_along_composition (l : list α) (c : composition l.length) : list (list α) :=
of_fn (λ (i : fin c.length), (l.take (c.size_up_to (i.val+1))).drop (c.size_up_to i.val))

/-- When one splits a list along a composition `c`, the number of sublists thus created is
`c.length`. -/
@[simp] lemma length_split_along_composition (l : list α) (c : composition l.length) :
  length (l.split_along_composition c) = c.length :=
by simp [split_along_composition]

/-- When one splits a list along a composition `c`, the lengths of the sublists thus created are
given by the block sizes in `c`. -/
lemma map_length_split_along_composition (l : list α) (c : composition l.length) :
  map length (l.split_along_composition c) = c.blocks :=
begin
  refine ext_le (by simp) (λ i h₁ h₂, _),
  simp [split_along_composition, composition.size_up_to_le c, min_eq_left, nth_le_of_fn',
             map_of_fn, function.comp_app, length_drop, length_take],
  rw c.blocks_length at h₂,
  simp only [composition.size_up_to_succ c h₂, nat.add_sub_cancel_left],
  refl
end

lemma length_pos_of_mem_split_along_composition {l l' : list α} {c : composition l.length}
  (h : l' ∈ l.split_along_composition c) :
  0 < length l' :=
begin
  have : l'.length ∈ (l.split_along_composition c).map list.length :=
    list.mem_map_of_mem list.length h,
  rw list.map_length_split_along_composition at this,
  exact c.blocks_pos this
end

lemma sum_take_map_length_split_along_composition
  (l : list α) (c : composition l.length) (i : ℕ) :
  (((l.split_along_composition c).map length).take i).sum = c.size_up_to i :=
by { congr, exact map_length_split_along_composition l c }

/-- The `i`-th sublist in the splitting of a list `l` along a composition `c`, is the slice of `l`
between the indices `c.size_up_to i` and `c.size_up_to (i+1)`, i.e., the indices in the `i`-th
block of the composition. -/
lemma nth_le_split_along_composition (l : list α) (c : composition l.length)
  {i : ℕ} (hi : i < (l.split_along_composition c).length) :
  nth_le (l.split_along_composition c) i hi = (l.take (c.size_up_to (i+1))).drop (c.size_up_to i) :=
by simp [split_along_composition]

/-- If one splits a list along a composition, and then joins the sublists, one gets back the
original list. -/
theorem join_split_along_composition (l : list α) (c : composition l.length) :
  (l.split_along_composition c).join = l :=
begin
  /- The proof is naive, direct, and tedious: show that the `k`-th elements are the same.
  To do this, we identify to which block `k` belongs (its index is `c.index k` by definition),
  and then express the `k`-th element of the join as some element in a sublist, which in turn can
  be expressed as an element of `l`. -/
  let L := l.split_along_composition c,
  have A : length (join L) = length l,
    by simp [L, split_along_composition, sum_of_fn, c.size_up_to_le,
      fin.sum_univ_eq_sum_range ((λ (x : ℕ), c.size_up_to (x + 1) - c.size_up_to x)) c.length,
      sum_range_sub_of_monotone, c.size_up_to_length, c.size_up_to_zero, c.monotone_size_up_to],
  apply ext_le A (λ k h₁ h₂, _),
  let i := c.index ⟨k, h₂⟩,
  have i_lt : i.val < L.length, by { convert i.2, simp },
  have le_k : c.size_up_to i.val ≤ k := c.size_up_to_index_le ⟨k, h₂⟩,
  have k_lt : k < c.size_up_to (i.val + 1) := c.lt_size_up_to_index_succ ⟨k, h₂⟩,
  set j := k - c.size_up_to i.val with hj,
  have k_eq' : k = c.size_up_to i.val + j := (nat.add_sub_of_le le_k).symm,
  rw [k_eq'] at k_lt,
  have k_eq : k = ((L.map length).take i.val).sum + j,
    by rwa sum_take_map_length_split_along_composition l c,
  have j_lt : j < length (nth_le L i.val i_lt),
  { rw length_split_along_composition at i_lt,
    rw [c.size_up_to_succ i_lt, add_lt_add_iff_left] at k_lt,
    convert k_lt,
    rw nth_le_of_eq (map_length_split_along_composition l c).symm,
    simp },
  have : nth_le (join L) k h₁ = nth_le (join L) (((L.map length).take i.val).sum + j) (k_eq ▸ h₁),
    by { congr, exact k_eq },
  rw [this, nth_le_join _ i_lt j_lt],
  dsimp [L],
  rw nth_le_of_eq (nth_le_split_along_composition l c i_lt),
  have B : c.size_up_to i.val + j < (l.take (c.size_up_to (i.val + 1))).length,
  { convert k_lt,
    simp [c.size_up_to_le] },
  rw [← nth_le_drop _ B, ← nth_le_take _ (lt_of_lt_of_le k_lt (c.size_up_to_le _)) k_lt],
  congr,
  exact k_eq'.symm
end

theorem eq_iff_join_eq (L L' : list (list α)) :
  L = L' ↔ L.join = L'.join ∧ map length L = map length L' :=
begin
  refine ⟨λ H, by simp [H], _⟩,
  rintros ⟨join_eq, length_eq⟩,
  apply ext_le,
  { have : length (map length L) = length (map length L'), by rw length_eq,
    simpa using this },
  { assume n h₁ h₂,
    rw [← drop_take_succ_join_eq_nth_le, ← drop_take_succ_join_eq_nth_le, join_eq, length_eq] }
end

theorem split_along_composition_join (L : list (list α)) (c : composition L.join.length)
  (h : map length L = c.blocks) : split_along_composition (join L) c = L :=
begin
  rw [eq_iff_join_eq, join_split_along_composition, map_length_split_along_composition, h],
  simp only [eq_self_iff_true, and_self]
end

end list

open list

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
    let l := a.blocks.split_along_composition b,
    let c : composition n :=
    { blocks := l.map sum,
      blocks_pos := begin
        refine forall_mem_map_iff.2 (λ j hj, _),
        refine lt_of_lt_of_le (length_pos_of_mem_split_along_composition hj)
          (length_le_sum_of_one_le _ (λ i hi, _)),
        have : i ∈ a.blocks,
        { rw ← a.blocks.join_split_along_composition b,
          exact mem_join_of_mem hj hi },
        exact composition.one_le_blocks a this
      end,
      blocks_sum := by { rw [← sum_join, join_split_along_composition], exact a.blocks_sum } },
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
        rw join_split_along_composition at this,
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
    -- `join_split_along_composition`, but we need to massage it to take care of the dependent
    -- setting.
    rintros ⟨a, b⟩,
    rw composition_sigma_composition_eq_iff,
    split,
    { dsimp,
      conv_rhs { rw [← join_split_along_composition a.blocks b,
        ← of_fn_nth_le (split_along_composition a.blocks b)] },
      have A := length_map list.sum (split_along_composition a.blocks b),
      congr,
      exact A,
      rw fin.heq_fun_iff A,
      assume i,
      refl },
    { dsimp,
      conv_rhs { rw [← of_fn_nth_le b.blocks] },
      congr' 1,
      { dsimp only [composition.length],
        simp only [composition.blocks_length, length_map, length_split_along_composition] },
      { rw fin.heq_fun_iff,
        { assume i,
          dsimp only [composition.length],
          rw [nth_le_map_rev length, nth_le_of_eq (map_length_split_along_composition _ _)] },
        { dsimp only [composition.length],
          simp only [composition.blocks_length, length_map, length_split_along_composition] } } }
  end,
  right_inv := begin
    -- the fact that we have a right inverse is essentially contained in
    -- `split_along_composition_join`, but we need to massage it to take care of the dependent
    -- setting.
    rintros ⟨c, d⟩,
    have : map list.sum (of_fn (λ (i : fin (composition.length c)), (d i).blocks)) = c.blocks,
      by simp [map_of_fn, (∘), composition.blocks_sum, composition.of_fn_blocks_fun],
    rw composition_sigma_pi_composition_eq_iff,
    dsimp,
    congr,
    { ext1,
      dsimp,
      rwa split_along_composition_join,
      simp [(∘)] },
    { rw fin.heq_fun_iff,
      { assume i,
        rw nth_le_of_eq (split_along_composition_join _ _ _),
        { simp },
        { simp [(∘)] } },
      { congr,
        ext1,
        dsimp,
        rwa split_along_composition_join,
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
