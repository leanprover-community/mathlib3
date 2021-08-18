/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kyle Miller
-/
import combinatorics.simple_graph.basic

/-!
# Walks and paths

A walk in a simple graph is a finite sequence of adjacent vertices.  A path is a walk that visits
each vertex only once.

## Main definitions

* `simple_graph.walk` is the type of walks between pairs of vertices
* `simple_graph.walk.is_path` is a predicate that determines whether a walk is a path.
* `simple_graph.walk.to_path` constructs a path from a walk with the same endpoints.
* `simple_graph.exists_walk` is the walk-connectivity relation.
* `simple_graph.connected_components` is the quotient of the vertex type by walk-connectivity.
* `simple_graph.exists_walk_eq_exists_path` and `simple_graph.exists_walk_eq_eqv_gen` give that
  walk-connectivity, path-connectivity, and `eqv_gen G.adj` are the each the same relation.
* `simple_graph.walk.get_vert` parameterizes the vertices of a walk by natural numbers.
* `simple_graph.walk.is_path_iff` characterizes paths as walks for which `get_vert` is injective.

## Tags

walks, paths
-/

universes u

namespace simple_graph

variables {V : Type u} (G : simple_graph V)

/-- A walk is a sequence of incident edges in a graph, represented here as a sequence of adjacent
vertices. -/
inductive walk : V → V → Type u
| nil {u : V} : walk u u
| cons {u v w : V} (h : G.adj u v) (p : walk v w) : walk u w

attribute [refl] walk.nil

instance walk.inhabited (v : V) : inhabited (G.walk v v) := ⟨walk.nil⟩

namespace walk
variables {G}

/-- The length of a walk is the number of edges along it. -/
def length : Π {u v : V}, G.walk u v → ℕ
| _ _ nil := 0
| _ _ (cons _ q) := q.length.succ

/-- The concatenation of two compatible walks. -/
@[trans]
def concat : Π {u v w : V}, G.walk u v → G.walk v w → G.walk u w
| _ _ _ nil q := q
| _ _ _ (cons h p) q := cons h (concat p q)

/-- The concatenation of the reverse of the first walk with the second walk. -/
protected def reverse_aux : Π {u v w : V}, G.walk u v → G.walk u w → G.walk v w
| _ _ _ nil q := q
| _ _ _ (cons h p) q := reverse_aux p (cons (G.sym h) q)

/-- Reverse the orientation of a walk. -/
@[symm]
def reverse {u v : V} (w : G.walk u v) : G.walk v u := w.reverse_aux nil

/-- Get the nth vertex from a path, where if i is greater than the length of the path
the result is the endpoint of the path. -/
def get_vert : Π {u v : V} (p : G.walk u v) (i : ℕ), V
| u v nil _ := u
| u v (cons _ _) 0 := u
| u v (cons _ q) (i+1) := q.get_vert i

variables [decidable_eq V]

/-- The support of a walk is the finite set of vertices it visits. -/
def support : Π {u v : V}, G.walk u v → finset V
| u v nil := {u}
| u v (cons h p) := insert u p.support

/-- A path is a walk that visits each vertex at most once. -/
def is_path : Π {u v : V}, G.walk u v → Prop
| u v nil := true
| u v (cons h p) := p.is_path ∧ ¬ u ∈ p.support

end walk

/-- The relation on vertices of whether there exists a walk between them.
This is an equivalence relation. -/
def exists_walk : V → V → Prop := λ v w, nonempty (G.walk v w)

/-- The relation on vertices of whether there exists a path between them.
This is equal to `simple_graph.exists_walk`. -/
def exists_path [decidable_eq V]: V → V → Prop := λ v w, ∃ (p : G.walk v w), p.is_path

@[refl] lemma exists_walk.refl (v : V) : G.exists_walk v v :=
by { fsplit, refl, }

@[symm] lemma exists_walk.symm ⦃v w : V⦄ (hvw : G.exists_walk v w) : G.exists_walk w v :=
by { tactic.unfreeze_local_instances, cases hvw, use hvw.reverse, }

@[trans] lemma exists_walk.trans ⦃u v w : V⦄ (huv : G.exists_walk u v) (hvw : G.exists_walk v w) :
  G.exists_walk u w :=
by { tactic.unfreeze_local_instances, cases hvw, cases huv, use huv.concat hvw, }

lemma exists_walk.is_equivalence : equivalence G.exists_walk :=
mk_equivalence _ (exists_walk.refl G) (exists_walk.symm G) (exists_walk.trans G)

/-- The equivalence relation on vertices given by `simple_graph.exists_walk`. -/
def exists_walk.setoid : setoid V := setoid.mk _ (exists_walk.is_equivalence G)

/-- A connected component is an element of the quotient of the vertex type by the relation
`simple_graph.exists_walk`. -/
def connected_components := quotient (exists_walk.setoid G)

/-- A graph is connected if every vertex is connected to every other by a walk. -/
def is_connected : Prop := ∀ v w, exists_walk G v w

instance connected_components.inhabited [inhabited V]: inhabited G.connected_components :=
⟨@quotient.mk _ (exists_walk.setoid G) (default _)⟩

namespace walk

variables {G}

@[simp] lemma nil_length {u : V} : (nil : G.walk u u).length = 0 := rfl

@[simp] lemma cons_length {u v w : V} (h : G.adj u v) (p : G.walk v w) :
  (cons h p).length = p.length + 1 := rfl

@[simp] lemma nil_reverse {u : V} : (nil : G.walk u u).reverse = nil := rfl

lemma singleton_reverse {u v : V} (h : G.adj u v) :
  (cons h nil).reverse = cons (G.sym h) nil := rfl

@[simp] lemma cons_concat {u v w x : V} (h : G.adj u v) (p : G.walk v w) (q : G.walk w x) :
  (cons h p).concat q = cons h (p.concat q) := rfl

lemma cons_as_concat {u v w : V} (h : G.adj u v) (p : G.walk v w) :
  cons h p = concat (cons h nil) p := rfl

@[simp] lemma concat_nil : Π {u v : V} (p : G.walk u v), p.concat nil = p
| _ _ nil := rfl
| _ _ (cons h p) := by rw [cons_concat, concat_nil]

@[simp] lemma nil_concat {u v : V} (p : G.walk u v) : nil.concat p = p := rfl

lemma concat_assoc : Π {u v w x : V} (p : G.walk u v) (q : G.walk v w) (r : G.walk w x),
  p.concat (q.concat r) = (p.concat q).concat r
| _ _ _ _ nil _ _ := rfl
| _ _ _ _ (cons h p') q r := by { dsimp only [concat], rw concat_assoc, }

@[simp]
protected lemma reverse_aux_eq_reverse_concat {u v w : V} (p : G.walk u v) (q : G.walk u w) :
  p.reverse_aux q = p.reverse.concat q :=
begin
  induction p generalizing q w,
  { refl },
  { dsimp [walk.reverse_aux, walk.reverse],
    repeat { rw p_ih },
    rw ←concat_assoc,
    refl, }
end

@[simp] lemma concat_reverse {u v w : V} (p : G.walk u v) (q : G.walk v w) :
  (p.concat q).reverse = q.reverse.concat p.reverse :=
begin
  induction p generalizing q w,
  { simp },
  { dsimp only [cons_concat, reverse, walk.reverse_aux],
    simp only [p_ih, walk.reverse_aux_eq_reverse_concat, concat_nil],
    rw concat_assoc, }
end

@[simp] lemma cons_reverse {u v w : V} (h : G.adj u v) (p : G.walk v w) :
  (cons h p).reverse = p.reverse.concat (cons (G.sym h) nil) :=
begin
  dsimp [reverse, walk.reverse_aux],
  simp only [walk.reverse_aux_eq_reverse_concat, concat_nil],
end

@[simp] lemma reverse_reverse : Π {u v : V} (p : G.walk u v), p.reverse.reverse = p
| _ _ nil := rfl
| _ _ (cons h p) := by simp [reverse_reverse]

@[simp] lemma concat_length : Π {u v w : V} (p : G.walk u v) (q : G.walk v w),
  (p.concat q).length = p.length + q.length
| _ _ _ nil _ := by simp
| _ _ _ (cons _ p') _ := by simp [concat_length, add_left_comm, add_comm]

protected lemma reverse_aux_length {u v w : V} (p : G.walk u v) (q : G.walk u w) :
  (p.reverse_aux q).length = p.length + q.length :=
begin
  induction p,
  { dunfold walk.reverse_aux, simp, },
  { dunfold reverse_aux, rw p_ih, simp only [cons_length], ring, },
end

@[simp] lemma reverse_length {u v : V} (p : G.walk u v) : p.reverse.length = p.length :=
by { convert walk.reverse_aux_length p nil }

@[simp] lemma get_vert_0 {u v : V} (p : G.walk u v) : p.get_vert 0 = u :=
by { cases p; refl }

@[simp] lemma get_vert_n {u v : V} (p : G.walk u v) : p.get_vert p.length = v :=
by { induction p, refl, exact p_ih }

@[simp] lemma get_vert_nil {u : V} (i : ℕ) : (nil : G.walk u u).get_vert i = u :=
by cases i; simp [get_vert]

@[simp] lemma get_vert_cons {u v w : V} (h : G.adj u v) (p : G.walk v w) (i : ℕ) :
  (cons h p).get_vert (i + 1) = p.get_vert i := rfl

lemma concat_get_vert {u v w : V} (p : G.walk u v) (p' : G.walk v w) (i : ℕ) :
  (p.concat p').get_vert i = if i ≤ p.length then p.get_vert i else p'.get_vert (i - p.length) :=
begin
  induction p generalizing i,
  { simp only [get_vert_nil, le_zero_iff_eq, nil_length, nil_concat, nat.sub_zero],
    split_ifs,
    { subst i, simp, },
    { refl } },
  { simp only [cons_length, cons_concat],
    cases i,
    { simp, },
    { simp [p_ih, nat.succ_le_succ_iff], } }
end

@[simp] lemma get_vert_reverse {u v : V} (p : G.walk u v) (i : ℕ) :
  p.reverse.get_vert i = p.get_vert (p.length - i) :=
begin
  induction i generalizing u v,
  { simp },
  { induction p,
    { simp },
    { simp only [cons_reverse, concat_get_vert, p_ih, i_ih,
                 cons_length, reverse_length, nat.succ_sub_succ_eq_sub, cons_reverse],
      split_ifs,
      { have h' : p_p.length - i_n = (p_p.length - i_n.succ).succ := by omega,
        simp [h'], },
      { have h' : p_p.length - i_n = 0 := by omega,
        have h'' : i_n.succ - p_p.length = (i_n - p_p.length).succ := by omega,
        simp [h', h''], } } }
end

protected lemma ext_aux : Π {u v : V} (n : ℕ) (p p' : G.walk u v)
  (h₁ : p.length = n) (h₁' : p'.length = n)
  (h₂ : ∀ i, i ≤ n → p.get_vert i = p'.get_vert i), p = p'
| _ _ 0 nil nil _ _ _ := rfl
| u v (n+1) (@cons _ _ _ w _ huw q) (@cons _ _ _ w' _ huw' q') h₁ h₁' h₂ :=
begin
  have hw : w = w',
  { specialize h₂ 1 (nat.le_add_left _ _),
    simpa using h₂, },
  subst w',
  congr,
  apply ext_aux n q q' (nat.succ.inj h₁) (nat.succ.inj h₁'),
  intros i h,
  exact h₂ i.succ (nat.succ_le_succ h),
end

@[ext]
lemma ext {u v : V} (p p' : G.walk u v)
  (h₁ : p.length = p'.length)
  (h₂ : ∀ i, i ≤ p.length → p.get_vert i = p'.get_vert i) :
  p = p' :=
walk.ext_aux p.length p p' rfl h₁.symm h₂

lemma adj_get_vert : Π {u v : V} (p : G.walk u v) (i : ℕ) (h : i < p.length),
  G.adj (p.get_vert i) (p.get_vert (i + 1))
| u v (cons huv p) 0 _ := by simp [huv]
| u v (cons huv p) (i+1) h := begin
  rw cons_length at h,
  simp only [get_vert_cons],
  exact adj_get_vert _ i (nat.lt_of_succ_lt_succ h),
end

section paths
variables [decidable_eq V]

@[simp] lemma nil_support {u : V} : (nil : G.walk u u).support = {u} := rfl

@[simp] lemma cons_support {u v w : V} (h : G.adj u v) (p : G.walk v w) :
  (cons h p).support = insert u p.support := rfl

@[simp] lemma start_mem_support {u v : V} (p : G.walk u v) : u ∈ p.support :=
by cases p; simp [support]

@[simp] lemma end_mem_support {u v : V} (p : G.walk u v) : v ∈ p.support :=
begin
  induction p,
  { simp [support], },
  { simp [support, p_ih], },
end

/-- Given a walk and a vertex in that walk, give a sub-walk starting at that vertex. -/
def subwalk_from : Π {u v w : V} (p : G.walk u v), w ∈ p.support → G.walk w v
| _ _ w nil h := by { rw [nil_support, finset.mem_singleton] at h, subst w }
| u v w (@cons _ _ _ x _ ha p) hs := begin
  rw [cons_support, finset.mem_insert] at hs,
  by_cases hw : w = u,
  { subst w, exact cons ha p },
  { have : w ∈ p.support, { cases hs, exact false.elim (hw hs), exact hs },
    exact p.subwalk_from this, },
end

lemma subwalk_from_path_is_path {u v w : V} (p : G.walk u v) (h : p.is_path) (hs : w ∈ p.support) :
  (p.subwalk_from hs).is_path :=
begin
  induction p,
  { rw [nil_support, finset.mem_singleton] at hs,
    subst w,
    trivial },
  { rw [cons_support, finset.mem_insert] at hs,
    dsimp only [is_path] at h,
    simp only [subwalk_from],
    split_ifs,
    { subst p_u,
      simp [is_path, h] },
    { cases hs,
      { exact false.elim (h_1 hs_1), },
      { exact p_ih h.1 _, } } },
end

/-- Given a walk, form a path between the same endpoints by splicing out unnecessary detours.
See `simple_graph.walk.to_path_is_path` -/
def to_path : Π {u v : V}, G.walk u v → G.walk u v
| u v nil := nil
| u v (@cons _ _ _ x _ ha p) :=
  let p' := p.to_path
  in if hs : u ∈ p'.support
     then p'.subwalk_from hs
     else cons ha p'

lemma subwalk_from_support_subset.aux (n' : ℕ) :
  Π {u v w : V} (p : G.walk u v) (hl : p.length = n') (h : w ∈ p.support),
    (p.subwalk_from h).support ⊆ p.support :=
begin
  refine nat.strong_induction_on n' (λ n ih, _),
  intros u v w p hl h,
  cases p,
  { rw [nil_support, finset.mem_singleton] at h,
    subst w,
    trivial, },
  { dsimp only [subwalk_from, support],
    rw [cons_support, finset.mem_insert] at h,
    split_ifs,
    { subst h_1,
      simp, },
    { have h' : w ∈ p_p.support := by cc,
      refine finset.subset.trans _ (finset.subset_insert _ _),
      convert_to (p_p.subwalk_from h').support ⊆ p_p.support,
      rw cons_length at hl,
      apply ih p_p.length (by linarith) _ rfl, }, },
end

lemma subwalk_from_support_subset {u v w : V} (p : G.walk u v) (h : w ∈ p.support) :
  (p.subwalk_from h).support ⊆ p.support :=
subwalk_from_support_subset.aux p.length p rfl h

lemma to_path_support_subset {u v : V} (p : G.walk u v) : p.to_path.support ⊆ p.support :=
begin
  induction p,
  { trivial, },
  { dsimp only [to_path, support],
    split_ifs,
    { refine finset.subset.trans (finset.subset.trans _ p_ih) (finset.subset_insert _ _),
      apply subwalk_from_support_subset, },
    { intro x,
      simp only [cons_support, finset.mem_insert],
      intro h,
      cases h,
      { subst p_u,
        exact or.inl rfl, },
      { exact or.inr (p_ih h_1), }, }, },
end

lemma to_path_is_path {u v : V} (p : G.walk u v) : p.to_path.is_path :=
begin
  induction p,
  { trivial, },
  { dsimp [to_path, is_path],
    split_ifs,
    { apply subwalk_from_path_is_path _ p_ih, },
    { use p_ih, }, },
end

@[simp] lemma nil_is_path {u : V} : (nil : G.walk u u).is_path := by trivial

@[simp] lemma singleton_is_path {u v : V} (h : G.adj u v) : (cons h nil).is_path :=
begin
  simp only [is_path, true_and, nil_support, finset.mem_singleton],
  intro h',
  subst u,
  exact G.loopless _ h,
end


@[simp]
lemma concat_support {u v w : V} (p : G.walk u v) (p' : G.walk v w) :
  (p.concat p').support = p.support ∪ p'.support :=
begin
  induction p generalizing p' w,
  { simp, },
  { simp only [finset.insert_union, cons_concat, cons_support],
    apply congr_arg _ (p_ih _), },
end

@[simp]
lemma reverse_support {u v : V} (p : G.walk u v) : p.reverse.support = p.support :=
begin
  induction p,
  { trivial, },
  { simp only [support, finset.insert_eq_of_mem, end_mem_support, concat_support,
               true_or, cons_reverse, finset.mem_union, finset.union_insert],
    rw [finset.union_comm, ←finset.insert_eq],
    apply congr_arg _ p_ih, },
end

lemma get_vert_mem_support {u v} (p : G.walk u v) (i : ℕ) : p.get_vert i ∈ p.support :=
begin
  induction p generalizing i,
  { simp, },
  { cases i,
    { simp, },
    { simp only [cons_support, finset.mem_insert, get_vert_cons],
      right,
      apply p_ih, }, },
end

lemma mem_support_exists_get_vert {u v w} (p : G.walk u v) (h : w ∈ p.support) :
  ∃ i, i ≤ p.length ∧ p.get_vert i = w :=
begin
  induction p,
  { rw [nil_support, finset.mem_singleton] at h,
    subst w,
    simp, },
  { rw [cons_support, finset.mem_insert] at h,
    cases h,
    { subst w, use 0, simp, },
    { specialize p_ih h,
      rcases p_ih with ⟨i, hi, hv⟩,
      use i+1, subst w, simp [hi],}, },
end

protected lemma is_path_iff.aux {u v : V} (p : G.walk u v) :
  p.is_path ↔ ∀ (i k : ℕ) (hi : i ≤ p.length) (hk : i + k ≤ p.length),
                 p.get_vert i = p.get_vert (i + k) → k = 0 :=
begin
  split,
  { intros hp i,
    induction i generalizing u v,
    { intro k,
      induction k generalizing u v,
      { simp },
      { simp only [forall_prop_of_true, get_vert_0, zero_le, zero_add],
        intros hk hu,
        cases p,
        { simpa using hk },
        { simp only [get_vert_cons] at hu,
          subst u,
          exact false.elim (hp.2 (get_vert_mem_support _ _)) } } },
    { cases p,
      { simp, },
      { simp only [cons_length, get_vert_cons],
        simp only [is_path] at hp,
        intros k hi hk,
        rw [add_comm, nat.add_succ], simp [get_vert],
        intro hv,
        rw [add_comm, nat.add_succ, add_comm] at hk,
        apply i_ih p_p hp.1 _ (nat.succ_le_succ_iff.mp hi) (nat.succ_le_succ_iff.mp hk),
        rw [hv, add_comm], } } },
  { intro h,
    induction p,
    { simp },
    { simp only [is_path],
      split,
      { apply p_ih,
        intros i k hi hk hv,
        apply h i.succ k (nat.succ_le_succ hi) _,
        rw [add_comm, nat.add_succ, add_comm],
        simp only [get_vert, hv, cons_length],
        rw [add_comm, nat.add_succ, add_comm],
        exact nat.succ_le_succ hk, },
      { intro hs,
        rcases mem_support_exists_get_vert _ hs with ⟨i, hl, rfl⟩,
        have h' := h 0 i.succ,
        simp only [cons_length, forall_prop_of_true, get_vert_0,
                   zero_le, zero_add, get_vert_cons] at h',
        specialize h' (nat.succ_le_succ hl),
        exact nat.succ_ne_zero _ h', } } }
end

lemma is_path_iff {u v : V} (p : G.walk u v) :
  p.is_path ↔ ∀ (i j : ℕ) (hi : i ≤ p.length) (hj : j ≤ p.length),
                 p.get_vert i = p.get_vert j → i = j :=
begin
  convert walk.is_path_iff.aux p,
  simp only [eq_iff_iff],
  split,
  { intros h i k hi hk hv,
    specialize h i (i+k) hi hk hv,
    linarith, },
  { intros h i j hi hj hv,
    wlog : i ≤ j using i j,
    specialize h i (j-i) hi,
    rw nat.add_sub_of_le case at h,
    specialize h hj hv,
    rw [(nat.sub_eq_iff_eq_add case).mp h, zero_add], }
end

lemma reverse_path {u v : V} (p : G.walk u v) (h : p.is_path) : p.reverse.is_path :=
begin
  rw is_path_iff,
  simp only [reverse_length, get_vert_reverse],
  intros i j hi hj hp,
  have hi' : p.length - i ≤ p.length := by omega,
  have hj' : p.length - j ≤ p.length := by omega,
  have h' := (is_path_iff p).mp h _ _ hi' hj' hp,
  omega,
end

lemma is_path_if_concat_is_path {u v w} (p : G.walk u v) (p' : G.walk v w)
  (h : (p.concat p').is_path) : p.is_path :=
begin
  rw is_path_iff at h,
  rw is_path_iff,
  simp only [concat_get_vert, concat_length] at h,
  intros i j hi hj hp,
  specialize h i j (by omega) (by omega),
  simp only [hi, hj, if_true] at h,
  exact h hp,
end

lemma get_vert_image {u v} (p : G.walk u v) :
  finset.image (λ i, p.get_vert i) (finset.range (p.length + 1)) = p.support :=
begin
  ext w,
  simp only [exists_prop, finset.mem_image, finset.mem_range],
  split,
  { simp only [and_imp, exists_imp_distrib],
    rintros i ih rfl,
    apply get_vert_mem_support, },
  { intro hw,
    rcases mem_support_exists_get_vert p hw with ⟨i, hi, hw'⟩,
    exact ⟨i, by linarith, hw'⟩, },
end

end paths

end walk

variables (G)

lemma exists_walk_eq_exists_path [decidable_eq V] : exists_walk G = exists_path G :=
begin
  ext u v,
  dsimp [exists_walk, exists_path],
  split,
  { intro p, cases p, fsplit, use p.to_path, apply walk.to_path_is_path, },
  { intro p, cases p, fsplit, use p_w, },
end

lemma exists_walk_eq_eqv_gen : exists_walk G = eqv_gen G.adj :=
begin
  ext v w,
  split,
  { intro h,
    cases h,
    induction h,
    { exact eqv_gen.refl _ },
    { exact eqv_gen.trans _ _ _ (eqv_gen.rel _ _ h_h) h_ih } },
  { intro h,
    induction h with x y h _ x y he h_ih x y z hxy hyz hxy_ih hyz_ih,
    { exact ⟨walk.cons h walk.nil⟩, },
    { refl, },
    { cases h_ih,
      exact ⟨h_ih.reverse⟩, },
    { cases hxy_ih,
      cases hyz_ih,
      exact ⟨hxy_ih.concat hyz_ih⟩, } }
end

end simple_graph
