/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import data.list.basic

/-!
# Permutations of a list

In this file we define `l.permutations` to be a list of all permutations of `l : list α`.

## Order of the permutations

Designed for performance, the order in which the permutations appear in `list.permutations` is
rather intricate and not very amenable to induction. That's why we also provide `list.permutations'`
as a less efficient but more straightforward way of listing permutations.

### `list.permutations`

TODO. In the meantime, you can try decrypting the docstrings.

### `list.permutations'`

The list of partitions is built by recursion. The permutations of `[]` are `[[]]`. Then, the
permutations of `a :: l` are obtained by taking all permutations of `l` in order and adding `a` in
all positions. Hence, to build `[0, 1, 2, 3].permutations'`, it does
* `[[]]`
* `[[3]]`
* `[[2, 3], [3, 2]]]`
* `[[1, 2, 3], [2, 1, 3], [2, 3, 1], [1, 3, 2], [3, 1, 2], [3, 2, 1]]`
* `[[0, 1, 2, 3], [1, 0, 2, 3], [1, 2, 0, 3], [1, 2, 3, 0],`
   `[0, 2, 1, 3], [2, 0, 1, 3], [2, 1, 0, 3], [2, 1, 3, 0],`
   `[0, 2, 3, 1], [2, 0, 3, 1], [2, 3, 0, 1], [2, 3, 1, 0],`
   `[0, 1, 3, 2], [1, 0, 3, 2], [1, 3, 0, 2], [1, 3, 2, 0],`
   `[0, 3, 1, 2], [3, 0, 1, 2], [3, 1, 0, 2], [3, 1, 2, 0],`
   `[0, 3, 2, 1], [3, 0, 2, 1], [3, 2, 0, 1], [3, 2, 1, 0]]`

## TODO

Show that `l.nodup → l.permutations.nodup`. See `data.fintype.list`.
-/

open nat

variables {α β : Type*}

namespace list

/-- An auxiliary function for defining `permutations`. `permutations_aux2 t ts r ys f` is equal to
`(ys ++ ts, (insert_left ys t ts).map f ++ r)`, where `insert_left ys t ts` (not explicitly
defined) is the list of lists of the form `insert_nth n t (ys ++ ts)` for `0 ≤ n < length ys`.

    permutations_aux2 10 [4, 5, 6] [] [1, 2, 3] id =
      ([1, 2, 3, 4, 5, 6],
       [[10, 1, 2, 3, 4, 5, 6],
        [1, 10, 2, 3, 4, 5, 6],
        [1, 2, 10, 3, 4, 5, 6]]) -/
def permutations_aux2 (t : α) (ts : list α) (r : list β) : list α → (list α → β) → list α × list β
| []      f := (ts, r)
| (y::ys) f := let (us, zs) := permutations_aux2 ys (λx : list α, f (y::x)) in
               (y :: us, f (t :: y :: us) :: zs)

private def meas : (Σ'_:list α, list α) → ℕ × ℕ | ⟨l, i⟩ := (length l + length i, length l)

local infix ` ≺ `:50 := inv_image (prod.lex (<) (<)) meas

/-- A recursor for pairs of lists. To have `C l₁ l₂` for all `l₁`, `l₂`, it suffices to have it for
`l₂ = []` and to be able to pour the elements of `l₁` into `l₂`. -/
@[elab_as_eliminator] def permutations_aux.rec {C : list α → list α → Sort*}
  (H0 : ∀ is, C [] is)
  (H1 : ∀ t ts is, C ts (t::is) → C is [] → C (t::ts) is) : ∀ l₁ l₂, C l₁ l₂
| []      is := H0 is
| (t::ts) is :=
  have h1 : ⟨ts, t :: is⟩ ≺ ⟨t :: ts, is⟩, from
    show prod.lex _ _ (succ (length ts + length is), length ts) (succ (length ts) + length is,
      length (t :: ts)),
    by rw nat.succ_add; exact prod.lex.right _ (lt_succ_self _),
  have h2 : ⟨is, []⟩ ≺ ⟨t :: ts, is⟩, from prod.lex.left _ _ (nat.lt_add_of_pos_left (succ_pos _)),
  H1 t ts is (permutations_aux.rec ts (t::is)) (permutations_aux.rec is [])
using_well_founded {
  dec_tac := tactic.assumption,
  rel_tac := λ _ _, `[exact ⟨(≺), @inv_image.wf _ _ _ meas (prod.lex_wf lt_wf lt_wf)⟩] }

/-- An auxiliary function for defining `permutations`. `permutations_aux ts is` is the set of all
permutations of `is ++ ts` that do not fix `ts`. -/
def permutations_aux : list α → list α → list (list α) :=
@@permutations_aux.rec (λ _ _, list (list α)) (λ is, [])
  (λ t ts is IH1 IH2, foldr (λy r, (permutations_aux2 t ts r y id).2) IH1 (is :: IH2))

/-- List of all permutations of `l`.

     permutations [1, 2, 3] =
       [[1, 2, 3], [2, 1, 3], [3, 2, 1],
        [2, 3, 1], [3, 1, 2], [1, 3, 2]] -/
def permutations (l : list α) : list (list α) :=
l :: permutations_aux l []

/-- `permutations'_aux t ts` inserts `t` into every position in `ts`, including the last.
This function is intended for use in specifications, so it is simpler than `permutations_aux2`,
which plays roughly the same role in `permutations`.

Note that `(permutations_aux2 t [] [] ts id).2` is similar to this function, but skips the last
position:

    permutations'_aux 10 [1, 2, 3] =
      [[10, 1, 2, 3], [1, 10, 2, 3], [1, 2, 10, 3], [1, 2, 3, 10]]
    (permutations_aux2 10 [] [] [1, 2, 3] id).2 =
      [[10, 1, 2, 3], [1, 10, 2, 3], [1, 2, 10, 3]] -/
@[simp] def permutations'_aux (t : α) : list α → list (list α)
| []      := [[t]]
| (y::ys) := (t :: y :: ys) :: (permutations'_aux ys).map (cons y)

/-- List of all permutations of `l`. This version of `permutations` is less efficient but has
simpler definitional equations. The permutations are in a different order,
but are equal up to permutation, as shown by `list.permutations_perm_permutations'`.

     permutations [1, 2, 3] =
       [[1, 2, 3], [2, 1, 3], [2, 3, 1],
        [1, 3, 2], [3, 1, 2], [3, 2, 1]] -/
@[simp] def permutations' : list α → list (list α)
| [] := [[]]
| (t::ts) := (permutations' ts).bind $ permutations'_aux t

lemma permutations_aux2_fst (t : α) (ts : list α) (r : list β) : ∀ (ys : list α) (f : list α → β),
  (permutations_aux2 t ts r ys f).1 = ys ++ ts
| []      f := rfl
| (y::ys) f := match _, permutations_aux2_fst ys _ : ∀ o : list α × list β, o.1 = ys ++ ts →
      (permutations_aux2._match_1 t y f o).1 = y :: ys ++ ts with
  | ⟨_, zs⟩, rfl := rfl
  end

@[simp] lemma permutations_aux2_snd_nil (t : α) (ts : list α) (r : list β) (f : list α → β) :
  (permutations_aux2 t ts r [] f).2 = r := rfl

@[simp] lemma permutations_aux2_snd_cons (t : α) (ts : list α) (r : list β) (y : α) (ys : list α)
  (f : list α → β) :
  (permutations_aux2 t ts r (y::ys) f).2 = f (t :: y :: ys ++ ts) ::
    (permutations_aux2 t ts r ys (λx : list α, f (y::x))).2 :=
match _, permutations_aux2_fst t ts r _ _ : ∀ o : list α × list β, o.1 = ys ++ ts →
   (permutations_aux2._match_1 t y f o).2 = f (t :: y :: ys ++ ts) :: o.2 with
| ⟨_, zs⟩, rfl := rfl
end

/-- The `r` argument to `permutations_aux2` is the same as appending. -/
lemma permutations_aux2_append (t : α) (ts : list α) (r : list β) (ys : list α) (f : list α → β) :
  (permutations_aux2 t ts nil ys f).2 ++ r = (permutations_aux2 t ts r ys f).2 :=
by induction ys generalizing f; simp *

/-- The `ts` argument to `permutations_aux2` can be folded into the `f` argument. -/
lemma permutations_aux2_comp_append {t : α} {ts ys : list α} {r : list β} (f : list α → β) :
  (permutations_aux2 t [] r ys $ λ x, f (x ++ ts)).2 = (permutations_aux2 t ts r ys f).2 :=
begin
  induction ys generalizing f,
  { simp },
  { simp [ys_ih (λ xs, f (ys_hd :: xs))] },
end

lemma map_permutations_aux2' {α β α' β'} (g : α → α') (g' : β → β')
  (t : α) (ts ys : list α) (r : list β) (f : list α → β) (f' : list α' → β')
  (H : ∀ a, g' (f a) = f' (map g a)) :
  map g' (permutations_aux2 t ts r ys f).2 =
  (permutations_aux2 (g t) (map g ts) (map g' r) (map g ys) f').2 :=
begin
  induction ys generalizing f f'; simp *,
  apply ys_ih, simp [H],
end

/-- The `f` argument to `permutations_aux2` when `r = []` can be eliminated. -/
lemma map_permutations_aux2 (t : α) (ts : list α) (ys : list α) (f : list α → β) :
  (permutations_aux2 t ts [] ys id).2.map f = (permutations_aux2 t ts [] ys f).2 :=
begin
  convert map_permutations_aux2' id _ _ _ _ _ _ _ _; simp only [map_id, id.def],
  exact (λ _, rfl)
end

/-- An expository lemma to show how all of `ts`, `r`, and `f` can be eliminated from
`permutations_aux2`.

`(permutations_aux2 t [] [] ys id).2`, which appears on the RHS, is a list whose elements are
produced by inserting `t` into every non-terminal position of `ys` in order. As an example:
```lean
#eval permutations_aux2 1 [] [] [2, 3, 4] id
-- [[1, 2, 3, 4], [2, 1, 3, 4], [2, 3, 1, 4]]
```
-/
lemma permutations_aux2_snd_eq (t : α) (ts : list α) (r : list β) (ys : list α) (f : list α → β) :
  (permutations_aux2 t ts r ys f).2 =
    (permutations_aux2 t [] [] ys id).2.map (λ x, f (x ++ ts)) ++ r :=
by rw [← permutations_aux2_append, map_permutations_aux2, permutations_aux2_comp_append]

lemma map_map_permutations_aux2 {α α'} (g : α → α') (t : α) (ts ys : list α) :
  map (map g) (permutations_aux2 t ts [] ys id).2 =
  (permutations_aux2 (g t) (map g ts) [] (map g ys) id).2 :=
map_permutations_aux2' _ _ _ _ _ _ _ _ (λ _, rfl)

lemma map_map_permutations'_aux (f : α → β) (t : α) (ts : list α) :
  map (map f) (permutations'_aux t ts) = permutations'_aux (f t) (map f ts) :=
by induction ts with a ts ih; [refl, {simp [← ih], refl}]

lemma permutations'_aux_eq_permutations_aux2 (t : α) (ts : list α) :
  permutations'_aux t ts = (permutations_aux2 t [] [ts ++ [t]] ts id).2 :=
begin
  induction ts with a ts ih, {refl},
  simp [permutations'_aux, permutations_aux2_snd_cons, ih],
  simp only [← permutations_aux2_append] {single_pass := tt},
  simp [map_permutations_aux2],
end

lemma mem_permutations_aux2 {t : α} {ts : list α} {ys : list α} {l l' : list α} :
  l' ∈ (permutations_aux2 t ts [] ys (append l)).2 ↔
    ∃ l₁ l₂, l₂ ≠ [] ∧ ys = l₁ ++ l₂ ∧ l' = l ++ l₁ ++ t :: l₂ ++ ts :=
begin
  induction ys with y ys ih generalizing l,
  { simp {contextual := tt} },
  rw [permutations_aux2_snd_cons, show (λ (x : list α), l ++ y :: x) = append (l ++ [y]),
      by funext; simp, mem_cons_iff, ih], split,
  { rintro (e | ⟨l₁, l₂, l0, ye, _⟩),
    { subst l', exact ⟨[], y::ys, by simp⟩ },
    { substs l' ys, exact ⟨y::l₁, l₂, l0, by simp⟩ } },
  { rintro ⟨_ | ⟨y', l₁⟩, l₂, l0, ye, rfl⟩,
    { simp [ye] },
    { simp only [cons_append] at ye, rcases ye with ⟨rfl, rfl⟩,
      exact or.inr ⟨l₁, l₂, l0, by simp⟩ } }
end

lemma mem_permutations_aux2' {t : α} {ts : list α} {ys : list α} {l : list α} :
  l ∈ (permutations_aux2 t ts [] ys id).2 ↔
    ∃ l₁ l₂, l₂ ≠ [] ∧ ys = l₁ ++ l₂ ∧ l = l₁ ++ t :: l₂ ++ ts :=
by rw [show @id (list α) = append nil, by funext; refl]; apply mem_permutations_aux2

lemma length_permutations_aux2 (t : α) (ts : list α) (ys : list α) (f : list α → β) :
  length (permutations_aux2 t ts [] ys f).2 = length ys :=
by induction ys generalizing f; simp *

lemma foldr_permutations_aux2 (t : α) (ts : list α) (r L : list (list α)) :
  foldr (λy r, (permutations_aux2 t ts r y id).2) r L =
    L.bind (λ y, (permutations_aux2 t ts [] y id).2) ++ r :=
by induction L with l L ih; [refl, {simp [ih], rw ← permutations_aux2_append}]

lemma mem_foldr_permutations_aux2 {t : α} {ts : list α} {r L : list (list α)} {l' : list α} :
  l' ∈ foldr (λy r, (permutations_aux2 t ts r y id).2) r L ↔
    l' ∈ r ∨ ∃ l₁ l₂, l₁ ++ l₂ ∈ L ∧ l₂ ≠ [] ∧ l' = l₁ ++ t :: l₂ ++ ts :=
have (∃ (a : list α), a ∈ L ∧
    ∃ (l₁ l₂ : list α), ¬l₂ = nil ∧ a = l₁ ++ l₂ ∧ l' = l₁ ++ t :: (l₂ ++ ts)) ↔
    ∃ (l₁ l₂ : list α), ¬l₂ = nil ∧ l₁ ++ l₂ ∈ L ∧ l' = l₁ ++ t :: (l₂ ++ ts),
from ⟨λ ⟨a, aL, l₁, l₂, l0, e, h⟩, ⟨l₁, l₂, l0, e ▸ aL, h⟩,
      λ ⟨l₁, l₂, l0, aL, h⟩, ⟨_, aL, l₁, l₂, l0, rfl, h⟩⟩,
by rw foldr_permutations_aux2; simp [mem_permutations_aux2', this,
  or.comm, or.left_comm, or.assoc, and.comm, and.left_comm, and.assoc]

lemma length_foldr_permutations_aux2 (t : α) (ts : list α) (r L : list (list α)) :
  length (foldr (λy r, (permutations_aux2 t ts r y id).2) r L) = sum (map length L) + length r :=
by simp [foldr_permutations_aux2, (∘), length_permutations_aux2]

lemma length_foldr_permutations_aux2' (t : α) (ts : list α) (r L : list (list α))
  (n) (H : ∀ l ∈ L, length l = n) :
  length (foldr (λy r, (permutations_aux2 t ts r y id).2) r L) = n * length L + length r :=
begin
  rw [length_foldr_permutations_aux2, (_ : sum (map length L) = n * length L)],
  induction L with l L ih, {simp},
  have sum_map : sum (map length L) = n * length L :=
    ih (λ l m, H l (mem_cons_of_mem _ m)),
  have length_l : length l = n := H _ (mem_cons_self _ _),
  simp [sum_map, length_l, mul_add, add_comm]
end

@[simp] lemma permutations_aux_nil (is : list α) : permutations_aux [] is = [] :=
by rw [permutations_aux, permutations_aux.rec]

@[simp] lemma permutations_aux_cons (t : α) (ts is : list α) :
  permutations_aux (t :: ts) is = foldr (λy r, (permutations_aux2 t ts r y id).2)
    (permutations_aux ts (t::is)) (permutations is) :=
by rw [permutations_aux, permutations_aux.rec]; refl

@[simp] lemma permutations_nil : permutations ([] : list α) = [[]] :=
by rw [permutations, permutations_aux_nil]

lemma map_permutations_aux (f : α → β) : ∀ (ts is : list α),
  map (map f) (permutations_aux ts is) = permutations_aux (map f ts) (map f is) :=
begin
  refine permutations_aux.rec (by simp) _,
  introv IH1 IH2, rw map at IH2,
  simp only [foldr_permutations_aux2, map_append, map, map_map_permutations_aux2, permutations,
    bind_map, IH1, append_assoc, permutations_aux_cons, cons_bind, ← IH2, map_bind],
end

lemma map_permutations (f : α → β) (ts : list α) :
  map (map f) (permutations ts) = permutations (map f ts) :=
by rw [permutations, permutations, map, map_permutations_aux, map]

lemma map_permutations' (f : α → β) (ts : list α) :
  map (map f) (permutations' ts) = permutations' (map f ts) :=
by induction ts with t ts ih; [refl, simp [← ih, map_bind, ← map_map_permutations'_aux, bind_map]]

lemma permutations_aux_append (is is' ts : list α) :
  permutations_aux (is ++ ts) is' =
  (permutations_aux is is').map (++ ts) ++ permutations_aux ts (is.reverse ++ is') :=
begin
  induction is with t is ih generalizing is', {simp},
  simp [foldr_permutations_aux2, ih, bind_map],
  congr' 2, funext ys, rw [map_permutations_aux2],
  simp only [← permutations_aux2_comp_append] {single_pass := tt},
  simp only [id, append_assoc],
end

lemma permutations_append (is ts : list α) :
  permutations (is ++ ts) = (permutations is).map (++ ts) ++ permutations_aux ts is.reverse :=
by simp [permutations, permutations_aux_append]

end list
