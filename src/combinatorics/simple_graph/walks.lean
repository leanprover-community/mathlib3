import data.finset.basic
import combinatorics.simple_graph.basic

universes u

namespace simple_graph

variables {V : Type u} (G : simple_graph V)

inductive walk : V → V → Type u
| nil {u : V} : walk u u
| cons {u v w : V} (h : G.adj u v) (p : walk v w) : walk u w

/-- The type of all walks -/
structure walk' :=
(s t : V)
(w : G.walk s t)

variables {G}

namespace walk
variables [decidable_eq V]

/-- Get the set of vertices along the path. -/
def support : Π {u v : V}, G.walk u v → finset V
| u v nil := {u}
| u v (cons h p) := insert u p.support

/-- Check whether each vertex appears only once along the path. -/
def is_path : Π {u v : V}, G.walk u v → Prop
| u v nil := true
| u v (cons h p) := p.is_path ∧ ¬ u ∈ p.support

section paths

@[simp]
lemma nil_support {u : V} : (nil : G.walk u u).support = {u} := rfl
@[simp]
lemma cons_support {u v w : V} (h : G.adj u v) (p : G.walk v w) : (cons h p).support = insert u p.support := rfl

/--
The length of a walk is the number of edges along it.
-/
def length : Π {u v : V}, G.walk u v → ℕ
| _ _ nil := 0
| _ _ (cons _ q) := q.length.succ

@[simp]
lemma nil_length {u : V} : (nil : G.walk u u).length = 0 := rfl

@[simp]
lemma cons_length {u v w : V} (h : G.adj u v) (p : G.walk v w) : (cons h p).length = p.length + 1 := rfl


/--
Given a walk and a vertex in that walk, give a sub-walk starting at that vertex.
-/
def extract : Π {u v w : V} (p : G.walk u v), w ∈ p.support → G.walk w v
| u v w nil h := by { simp at h, rw h, exact nil }
| u v w (@cons _ _ _ x _ ha p) hs := begin
  simp at hs,
  by_cases hw : w = u,
  { subst w, exact cons ha p },
  { have : w ∈ p.support, { cases hs, exfalso, exact hw hs, exact hs },
    exact p.extract this, },
end

lemma extract_path_is_path {u v w : V} (p : G.walk u v) (h : p.is_path) (hs : w ∈ p.support) : (p.extract hs).is_path :=
begin
  induction p,
  { simp at hs, subst w, trivial },
  { simp at hs, simp [is_path] at h, simp [extract, is_path],
    split_ifs,
    { subst p_u, simp [is_path, h] },
    { cases hs, exfalso, exact h_1 hs_1,
      apply p_ih, exact h.1, }, },
end

/--
Given a walk, remove duplicate internal vertices.
-/
def to_path : Π {u v : V}, G.walk u v → G.walk u v
| u v nil := nil
| u v (@cons _ _ _ x _ ha p) :=
  let p' := p.to_path
  in if hs : u ∈ p'.support
     then p'.extract hs
     else cons ha p'

lemma extract_support_subset_aux (n' : ℕ) {u v w : V} (p : G.walk u v) (hl : p.length = n') (h : w ∈ p.support) :
  (p.extract h).support ⊆ p.support :=
begin
  revert u v w p hl h,
  refine nat.strong_induction_on n' (λ n ih, _),
  intros,
  induction p, simp at h, subst w, trivial,
  simp [extract, support], simp at hl, simp at h,
  split_ifs,
  { subst p_u, simp, },
  { have h' : w ∈ p_p.support := by cc,
    refine finset.subset.trans _ (finset.subset_insert _ _),
    convert_to (p_p.extract h').support ⊆ p_p.support,
    apply ih p_p.length (by linarith) _ rfl, },
end

lemma extract_support_subset {u v w : V} (p : G.walk u v) (h : w ∈ p.support) :
  (p.extract h).support ⊆ p.support :=
extract_support_subset_aux p.length p rfl h

lemma to_path_support_subset {u v : V} (p : G.walk u v) : p.to_path.support ⊆ p.support :=
begin
  induction p,
  trivial,
  simp [to_path, support],
  split_ifs,
  { refine finset.subset.trans _ (finset.subset_insert _ _),
    refine finset.subset.trans _ p_ih,
    apply extract_support_subset, },
  { simp [support],
    intro x, simp,
    intro h,
    cases h,
    { subst p_u, exact or.inl rfl, },
    { right, exact p_ih h_1, }, },
end

lemma to_path_is_path {u v : V} (p : G.walk u v) : p.to_path.is_path :=
begin
  induction p,
  trivial,
  dsimp [to_path,is_path],
  split_ifs,
  { apply extract_path_is_path _ p_ih, },
  { simp [is_path], use p_ih, },
end

end paths



--/-- Produce a singleton path from a pair of adjacent vertices -/
--@[reducible]
--def of_adj {u v : V} (h : G.adj u v) : G.walk u v := cons h nil

protected def reverse_aux : Π {u v w : V}, G.walk u v → G.walk u w → G.walk v w
| _ _ _ nil q := q
| _ _ _ (cons h p) q := reverse_aux p (cons (G.sym h) q)

/-- Reverse the orientation of a walk. -/
@[symm]
def reverse {u v : V} (w : G.walk u v) : G.walk v u := w.reverse_aux nil

@[simp] lemma nil_reverse {u : V} : (nil : G.walk u u).reverse = nil := rfl

@[simp]
lemma singleton_reverse {u v : V} (h : G.adj u v): (cons h nil).reverse = cons (G.sym h) nil := rfl

@[trans]
def concat : Π {u v w : V}, G.walk u v → G.walk v w → G.walk u w
| _ _ _ nil q := q
| _ _ _ (cons h p) q := cons h (concat p q)

@[simp]
lemma cons_concat {u v w x : V} (h : G.adj u v) (p : G.walk v w) (q : G.walk w x) :
  (cons h p).concat q = cons h (p.concat q) := rfl

@[simp]
lemma concat_nil {u v : V} (p : G.walk u v) : p.concat nil = p :=
by { induction p, refl, dsimp [concat], rw p_ih, }

@[simp]
lemma nil_concat {u v : V} (p : G.walk u v) : nil.concat p = p := rfl

lemma concat_assoc {u v w x : V} (p : G.walk u v) (q : G.walk v w) (r : G.walk w x) :
  p.concat (q.concat r) = (p.concat q).concat r :=
by { induction p, refl, dsimp [concat], rw p_ih, }

/--
This lemma has a `cons` as the second argument to avoid rewriting when it's `nil`.
-/
@[simp]
protected
lemma reverse_aux_extract {u v w x : V} (p : G.walk u v) (h : G.adj u w) (q : G.walk w x) :
  p.reverse_aux (cons h q) = (p.reverse_aux nil).concat (cons h q) :=
begin
  induction p generalizing q h w x,
  { refl },
  { dsimp [walk.reverse_aux],
    rw p_ih, conv_rhs { rw p_ih },
    rw ←concat_assoc, simp, }
end

@[simp]
protected
lemma concat_reverse_aux {u v w : V} (p : G.walk v u) (q : G.walk v w) :
  p.reverse_aux q = p.reverse.concat q :=
by { cases q, rw concat_nil, refl, rw walk.reverse_aux_extract, refl }

@[simp]
lemma concat_reverse {u v w : V} (p : G.walk u v) (q : G.walk v w) :
  (p.concat q).reverse = q.reverse.concat p.reverse :=
begin
  induction p generalizing q w,
  { simp },
  { rw cons_concat, dsimp [reverse, walk.reverse_aux],
    simp only [walk.reverse_aux_extract, walk.concat_reverse_aux, concat_nil],
    rw [p_ih, concat_assoc], }
end

@[simp]
lemma reverse_invol {u v : V} (p : G.walk u v) : p.reverse.reverse = p :=
begin
  induction p,
  { refl },
  { dsimp [reverse, walk.reverse_aux],
    simp [p_ih], }
end


@[simp]
lemma concat_length {u v w : V} (p : G.walk u v) (q : G.walk v w) :
  (p.concat q).length = p.length + q.length :=
begin
  induction p, simp,
  dsimp [concat, length], rw p_ih, repeat { rw nat.succ_eq_add_one }, ring,
end

protected
lemma reverse_aux_length {u v w : V} (p : G.walk u v) (q : G.walk u w) :
  (p.reverse_aux q).length = p.length + q.length :=
begin
  induction p,
  { dunfold walk.reverse_aux, simp, },
  { dunfold reverse_aux, rw p_ih, simp only [cons_length], ring, },
end

@[simp]
lemma reverse_length {u v : V} (p : G.walk u v) : p.reverse.length = p.length :=
by { convert walk.reverse_aux_length p nil }

/-- Get the nth vertex from a path, where if i is greater than the length of the path
the result is the endpoint of the path. -/
def get_vert : Π {u v : V} (i : ℕ) (p : G.walk u v), V
| u v 0 _ := u
| _ v (i+1) (cons _ q) := get_vert i q
| _ v (i+1) nil := v

@[simp]
lemma get_vert_0 {u v : V} (p : G.walk u v) : p.get_vert 0 = u := rfl

@[simp]
lemma get_vert_n {u v : V} (p : G.walk u v) : p.get_vert p.length = v :=
by { induction p, refl, exact p_ih }

@[simp]
lemma get_vert_nil {u : V} (i : ℕ) : (nil : G.walk u u).get_vert i = u :=
by { cases i, simp, dsimp [get_vert], refl, }

@[simp]
lemma get_vert_cons {u v w : V} (h : G.adj u v) (p : G.walk v w) (i : ℕ) :
  (cons h p).get_vert (i + 1) = p.get_vert i := rfl

lemma walk_ext_aux {u v : V} (n : ℕ) (p p' : G.walk u v)
  (h₁ : p.length = n) (h₁' : p'.length = n)
  (h₂ : ∀ i, i < n + 1 → p.get_vert i = p'.get_vert i) :
  p = p' :=
begin
  induction n generalizing u v p p',
  { cases p, cases p', refl, exfalso, simpa using h₁', exfalso, simpa using h₁, },
  cases p, cases p', refl,
  rw ←h₁ at h₁', exfalso, simpa using h₁',
  cases p',
  rw ←h₁ at h₁', exfalso, simpa using h₁',
  have key₁ := h₂ 1 (by { change 1 < n_n + 1 + 1, linarith }),
  dsimp [get_vert] at key₁,
  subst p'_v,
  rw cons_length at h₁ h₁',
  congr, apply n_ih p_p p'_p (nat.succ.inj h₁) (nat.succ.inj h₁'),
  intros i h,
  exact h₂ (i + 1) (by { change _ < n_n + 1 + 1, linarith }),
end

lemma walk_ext {u v : V} (p p' : G.walk u v)
  (h₁ : p.length = p'.length)
  (h₂ : ∀ i, i < p.length + 1 → p.get_vert i = p'.get_vert i) :
  p = p' :=
walk_ext_aux p.length p p' rfl h₁.symm h₂

lemma get_vert_rel {u v : V} (p : G.walk u v) (i : ℕ) (h : i < p.length) :
  G.adj (p.get_vert i) (p.get_vert (i + 1)) :=
begin
  induction i generalizing u v p,
  { cases p, exfalso, change 0 < 0 at h, linarith,
    cases p_p, exact p_h,
    exact p_h, },
  cases p,
  exfalso, change _ < 0 at h, linarith,
  cases p_p, exfalso, change _ + 1 < 1 at h, linarith,
  change G.adj ((cons p_p_h p_p_p).get_vert i_n) ((cons p_p_h p_p_p).get_vert i_n.succ),
  apply i_ih,
  change i_n + 1 < p_p_p.length.succ + 1 at h,
  dsimp [length], linarith,
end

section dependent_equality
variables {G}
/-! This may or may not be useful -/

def walk.deq {u v u' v' : V} (w : G.walk u v) (w' : G.walk u' v') : Prop :=
walk.mk u v w = walk.mk u' v' w'

local infix ` === `:50 := walk.deq

@[refl]
def walk.deq.refl {u v : V} {w : G.walk u v} : w === w := rfl

@[symm]
lemma walk.deq.symm {u v u' v' : V} {p : G.walk u v} {p' : G.walk u' v'} :
  p === p' → p' === p := eq.symm

@[trans]
lemma walk.deq.trans {u v u' v' u'' v'' : V}
  {p : G.walk u v} {p' : G.walk u' v'} {p'' : G.walk u'' v''}:
  p === p' → p' === p'' → p === p'' := eq.trans

lemma walk.deq.of_eq {u v : V} (p p' : G.walk u v) (h : p = p') : p === p' :=
by { subst p }

end dependent_equality

end walk

variables (G) [decidable_eq V]
def exists_walk : V → V → Prop := λ v w, nonempty (G.walk v w)
def exists_path : V → V → Prop := λ v w, nonempty {p : G.walk v w // p.is_path }

lemma exists_walk_eq_exists_path : exists_walk G = exists_path G :=
begin
  ext u v,
  dsimp [exists_walk, exists_path],
  split,
  { intro p, cases p, fsplit, use p.to_path, apply walk.to_path_is_path, },
  { intro p, cases p, fsplit, use p, },
end

@[refl] lemma exists_walk.refl (v : V) : G.exists_walk v v :=
by { use walk.nil, }

@[symm] lemma exists_walk.symm ⦃v w : V⦄ (hvw : G.exists_walk v w) : G.exists_walk w v :=
by { tactic.unfreeze_local_instances, cases hvw, use hvw.reverse, }

@[trans] lemma exists_walk.trans ⦃u v w : V⦄ (huv : G.exists_walk u v) (hvw : G.exists_walk v w) : G.exists_walk u w :=
begin
  tactic.unfreeze_local_instances, cases hvw,
  tactic.unfreeze_local_instances, cases huv,
  use huv.concat hvw,
end

lemma exists_walk.is_equivalence : equivalence G.exists_walk :=
mk_equivalence _ (exists_walk.refl G) (exists_walk.symm G) (exists_walk.trans G)

def exists_walk.setoid : setoid V := setoid.mk _ (exists_walk.is_equivalence G)

/--
Quotient of the vertex type by existence of walks.
-/
def connected_components := quotient (exists_walk.setoid G)

/-- Determines if a graph is connected -/
def is_connected : Prop := ∀ v w, exists_walk G v w

lemma exists_walk_eq_eqv_gen : exists_walk G = eqv_gen G.adj :=
begin
  ext v w,
  sorry
end

end simple_graph
