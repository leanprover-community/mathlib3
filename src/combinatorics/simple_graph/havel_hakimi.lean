/- 30 Aug 2019 -/
-- degree
-- incidence matrix
-- adjacency matrix

/-
## Definitions:
* A sequence of nonnegative integers is called `graphic` if it is the degree
  sequence of a simple graph.

how does one write dn where n is a subscript?

Havel-Hakimi Theorem: Let d_1 ≥ d_2 ≥ ... ≥ d_n ≥ 0 be a (finite) sequence of
nonnegative integers. The sequence is graphic iff the sequence
  d_2 - 1, ... , d_(t + 1) - 1, d_(t + 2), ... , d_n, where t = d_1, is graphic.


Let 0 ≤ d_1 ≤ d_2 ≤ ... ≤ d_n be a (finite) sequence of
nonnegative integers. The sequence is graphic iff the sequence
  d_2 - 1, ... , d_(t + 1) - 1, d_(t + 2), ... , d_n, where t = d_1 is graphic.
-/

import data.list.sort
import combinatorics.simple_graph.basic
import data.multiset.sort

universe u
variables (V : Type u) [fintype V]

-- what type should i use?
  -- `list.sorted` or `list.pairwise`
-- i think i can just use nat since that includes zero

-- oh god i need some kind of counter? or index
-- copy over the sequence except erase largest element and
  -- subtract one from the n next largest elements
def sub_one_n_times' (n : ℕ) (l : list ℕ) : list ℕ :=
(l.take n).map (nat.pred) ++ l.drop n
-- this one works i think, but ordering does matter

/-def list.pos_filter (l : list ℕ) : list ℕ := l.filter (λ n, 0 < n)
-- this probably already exists, just don't feel like looking it up

def n_pos_list_check (n : ℕ) (l : list ℕ) : Prop := n ≤ l.pos_filter.length-/

-- def nth_is_pos (n : ℕ) (l : list ℕ) [l.sorted (≤)] : Prop := 0 < (l.nth n)
-- bad

def sub_one_n_times (n : ℕ) (l : list ℕ) (h : l.sorted (≥)) : option (list ℕ) :=
  if n ≤ (l.filter (λ n, 0 < n)).length then some (sub_one_n_times' n l) else none

def havel_hakimi' (l : list ℕ) (h : l.sorted (≥)) : option (list ℕ) :=
  if (l.filter (λ n, 0 < n)) = [] then some [] else sub_one_n_times l.head l.tail h.tail
-- you can't get the empty list out of applying sub_one_n_times and removing the largest degree repeatedly, so when
  -- you get the empty list, you're done
-- is there another way of doing it? is there something else i can return
-- also need to re-sort

def havel_hakimi_step (l : list ℕ) (h : l.sorted (≥)) : multiset ℕ := sub_one_n_times' l.head l.tail

-- ideas for degree sequence
  -- multiset of vertices, take the image
  -- `multiset.sort` to get sorted list
variables {V}

def simple_graph.degree_multiset (G : simple_graph V) [decidable_rel G.adj] : multiset ℕ := finset.univ.val.map (λ v, G.degree v)

def simple_graph.degree_sequence (G : simple_graph V) [decidable_rel G.adj] : list ℕ := G.degree_multiset.sort (≥)
-- test out definition - good for algebraic graph theory? - look through lecture notes

--variables (l : list ℕ) [l.sorted (≥)]

-- in pseudocode,
-- a multiset ℕ is graphic if it is the degree sequence of some graph `G`
def graphic' (s : multiset ℕ) : Prop := ∃ (G : simple_graph V) [decidable_rel G.adj], by exactI s = G.degree_multiset

-- a sorted list is graphic if blah blah
def graphic (l : list ℕ) : Prop := ∃ (n : ℕ) (G : simple_graph $ fin n) [decidable_rel G.adj], by exactI l = G.degree_sequence

-- theorem statement from wikipedia:
/-
Let `S = (d_{1},\dots ,d_{n})` be a finite list of nonnegative integers that is nonincreasing.
List `S` is graphic if and only if the finite list `S' = (d_{2}-1,d_{3}-1,\dots ,d_{{d_{1}+1}}-1,d_{{d_{1}+2}},\dots ,d_{n})`
has nonnegative integers and is graphic.
-/
variables (S : list ℕ) (h : S.sorted (≥))

def simple_graph.degree' (G : simple_graph V) [decidable_rel G.adj] : V → ℕ := λ v, G.degree v

theorem havel_hakimi_A : graphic S → (S.head ≤ (S.filter (λ n, 0 < n)).length) ∧ graphic ((havel_hakimi_step S h).sort (≥)) :=
begin
  intros h2,
  split,
  { -- this is just the fact that S.head is largest degree, so the vertex with that degree is adjacent
    -- to S.head many vertices, which then means that they have degree at least 1
    rcases h2 with ⟨n, G, hdec, hds⟩,
    have h3 : S.head = (@simple_graph.degree_sequence (fin n) _ G hdec).head,
    exact congr_arg list.head hds,
    let d1 := (@simple_graph.degree_sequence (fin n) _ G hdec).head,
    -- let v1 := simple_graph.degree_multiset⁻¹ G d1, -- how to get to the preimage of the map in degree_multiset
    sorry },
  { -- the proof here is that performing the algorithm step is allowed because you can do the edge swap
    sorry },
end

lemma havel_hakimi_B : (S.head ≤ (S.filter (λ n, 0 < n)).length) ∧ graphic ((havel_hakimi_step S h).sort (≥)) →  graphic S :=
begin
  intros h2,
  rcases h2 with ⟨hnneg, n, G, hdec, hds⟩,
  sorry,
end

theorem havel_hakimi : graphic S ↔ (S.head ≤ (S.filter (λ n, 0 < n)).length) ∧ graphic ((havel_hakimi_step S h).sort (≥)) :=
 ⟨havel_hakimi_A S h, havel_hakimi_B S h⟩

variables (G : simple_graph V) [decidable_eq V] (v w x y : V)
variables (h1 : G.adj v w) (h2 : G.adj x y) (hn1 : ¬ G.adj v x) (hn2 : ¬ G.adj w y)

/-def new_graph : simple_graph V :=
{ adj := λ a b, if (((a = v) ∧ (b = w)) ∨ ((a = v) ∧ (b = x)) ∨ (((a = w) ∧ (b = y)) ∨ ((a = x) ∧ (b = y)))) then ¬ G.adj a b
                else G.adj a b,
  -- there's gotta be a better way of doing this
  sym := λ a b,
  begin
    simp,
    intros h,
    sorry,
  end,
  loopless := sorry, }-/

/-def new_graph : simple_graph V :=
{ adj := λ a b, if ((a ≠ v) ∧ (a ≠ w)) ∨ ((b ≠ x) ∧ (b ≠ y)) then G.adj a b
                else ¬ G.adj a b,
  -- there's gotta be a better way of doing this
  sym := λ a b,
  begin
    simp,
    intros h,
  end,
  loopless := _ }-/

-- okay shit this is gonna be annoying

-- going to need to show that the max degree is le the number of remaining vertices

-- sequence D is graphic if ∃ (G : simple_graph V), D is deg seq for G

-- for proof, need to define swapping edge algo
