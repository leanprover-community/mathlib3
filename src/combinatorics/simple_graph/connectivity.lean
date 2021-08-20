/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kyle Miller
-/
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.subgraph
import data.list.cycle
import data.list.chain
import tactic.omega
/-!

# Graph connectivity

In a simple graph,

* A *walk* is a finite sequence of adjacent vertices, and can be
  thought of equally well as a sequence of edges.

* A *trail* is a walk whose edges each appear no more than once.

* A *path* is a trail whose vertices appear no more than once.

* A *cycle* is a nonempty trail whose first and last vertices are the
  same and whose vertices except for the first appear no more than once.

**Warning:** graph theorists mean something different by "path" than do
homotopy theorists.  A "walk" in graph theory is a "path" in homotopy
theory.

Some definitions and theorems have inspiration from multigraph
counterparts in [Chou1994].

## Main definitions

* `simple_graph.walk`

## Tags
walks

-/

universes u

namespace option

variables {α β : Type*}

@[simp] lemma pbind_eq_some_iff {s : option α} {f : Π x (hx : x ∈ s), option β} {b : β} :
  s.pbind f = some b ↔ ∃ (a : α) (ha : s = some a), f a ha = some b :=
begin
  cases s,
  { simp },
  { simp only [pbind],
    refine ⟨λ h, ⟨s, _, h⟩, _⟩,
    rintro ⟨a, ha, ha'⟩,
    rw some_inj at ha,
    simpa [←ha', ha] }
end

@[simp] lemma pbind_eq_none_iff {s : option α} {f : Π x (hx : x ∈ s), option β} :
  s.pbind f = none ↔ s = none ∨ ∃ (a : α) (ha : a ∈ s), f a ha = none :=
begin
  cases s,
  { simp },
  { simp only [pbind, mem_def, pbind, false_or],
    refine ⟨λ h, ⟨s, _, h⟩, _⟩,
    rintro ⟨a, ha, ha'⟩,
    simp only [mem_def] at ha,
    simp [←ha', ha] }
end

end option

namespace list

variables {α : Type*}

@[simp] theorem head'_is_none :
  ∀ {l : list α}, (head' l).is_none ↔ l = []
| [] := by simp
| [a] := by simp
| (a::b::l) := by simp [@head'_is_none (b::l)]

@[simp] theorem head'_is_some : ∀ {l : list α}, l.head'.is_some ↔ l ≠ []
| [] := by simp
| [a] := by simp
| (a::b::l) := by simp [@head'_is_some (b::l)]

@[simp] lemma last'_eq_some_last (l : list α) (h : l ≠ []) :
  l.last' = some (l.last h) :=
begin
  rw ←last'_is_some at h,
  obtain ⟨x, hx⟩ := option.is_some_iff_exists.mp h,
  obtain ⟨h', rfl⟩ := mem_last'_eq_last hx,
  exact hx
end

@[simp] theorem head'_eq_none_iff {l : list α} :
  head' l = none ↔ l = [] :=
begin
  refine iff.trans _ head'_is_none,
  cases l.head';
  simp
end

@[simp] theorem last'_eq_none_iff {l : list α} :
  last' l = none ↔ l = [] :=
begin
  refine iff.trans _ last'_is_none,
  cases l.last';
  simp
end

lemma tail_eq_drop (l : list α) :
  l.tail = l.drop 1 :=
by { cases l; simp }

lemma mem_of_mem_tail (l : list α) (x : α) (h : x ∈ l.tail) : x ∈ l :=
begin
  cases l,
  { cases h },
  { exact mem_cons_of_mem _ h }
end

@[simp] lemma nth_le_tail (l : list α) (n : ℕ)
  (h : n < l.tail.length)
  (h' : n + 1 < l.length := by cases l; simpa using h) :
  l.tail.nth_le n h = l.nth_le (n + 1) h' :=
by simp_rw [list.tail_eq_drop, nth_le_drop', add_comm]

@[simp] theorem last_append' (l l' : list α)
  (h : l ++ l' ≠ []) (hl' : l' ≠ []) :
  last (l ++ l') h = l'.last hl' :=
begin
  induction l' using list.reverse_rec_on,
  { exact absurd rfl hl' },
  { simp_rw [←append_assoc, last_append] }
end

lemma reverse_take' (l : list α) (n : ℕ) (h : n ≤ l.length) :
  (l.take n).reverse = l.reverse.drop (l.length - n) :=
begin
  induction l with hd tl IH generalizing n,
  { simp },
  { cases n,
    { simp },
    { simp only [nat.succ_le_succ_iff, list.length] at h,
      simp only [reverse_cons, nat.succ_sub_succ_eq_sub, list.length, take],
      rw [IH _ h, drop_append_of_le_length],
      simpa using nat.sub_le _ _ } }
end

lemma reverse_init (l : list α) :
  l.init.reverse = l.reverse.tail :=
begin
  rw [init_eq_take, list.reverse_take' l _ (nat.pred_le _), list.tail_eq_drop],
  cases l;
  simp
end

lemma last_reverse (l : list α) (h : l.reverse ≠ [])
  (h' : 0 < l.length := (length_pos_of_ne_nil h).trans_le (length_reverse l).le) :
  l.reverse.last h = l.nth_le 0 h' :=
begin
  cases l,
  { exact absurd rfl h },
  { simp }
end

@[simp] lemma option_to_list_eq_nil_iff {s : option α} :
  s.to_list = [] ↔ s = none :=
by { cases s; simp [option.to_list] }

@[simp] lemma option_to_list_eq_singleton_iff {s : option α} {a : α} :
  s.to_list = [a] ↔ s = some a :=
by { cases s; simp [option.to_list] }

lemma length_option_to_list {s : option α} :
  s.to_list.length = if s.is_some then 1 else 0 :=
by { cases s; simp [option.to_list] }

@[simp] lemma length_option_to_list_eq_zero_iff {s : option α} :
  s.to_list.length = 0 ↔ s = none :=
by simp [length_eq_zero]

@[simp] lemma length_option_to_list_eq_one_iff {s : option α} :
  s.to_list.length = 1 ↔ ∃ (a : α), s = some a :=
by { cases s; simp [option.to_list] }

lemma nth_le_option_to_list (s : option α) (n : ℕ) (hn : n < s.to_list.length)
  (a : α) (h : s = some a) :
  s.to_list.nth_le n hn = a :=
by simp [h, option.to_list]

@[simp] lemma append_eq_append (l l' : list α) :
  l.append l' = l ++ l' := rfl

section pmap

variables {β : Type*} {R : α → α → Prop} {l : list α}

/-- Transform a `l : list α`, when `chain' R l`, in a dependent fashion using a function over
`x y : α` that requires membership in the list `x ∈ l` `y ∈ l` and the relation `R x y`.
See `list.chain.pmap` for the transformation that does not require list membership. -/
def chain'.pmap' : Π {l : list α} (h : chain' R l) (f : Π (a ∈ l) (b ∈ l) (h : R a b), β), list β
| []            _ _ := []
| [hd]          _ _ := []
| (x :: y :: l) h f :=
  f x (mem_cons_self _ _) y (mem_cons_of_mem _ (mem_cons_self _ _)) (chain'_cons.mp h).left ::
    chain'.pmap' (chain'_cons.mp h).right
      (λ a ha b hb hab, f a (mem_cons_of_mem _ ha) b (mem_cons_of_mem _ hb) hab)

@[simp] lemma chain'.pmap'_nil (h : chain' R [])
  (f : Π (a ∈ ([] : list α)) (b ∈ ([] : list α)) (h : R a b), β) : h.pmap' f = [] := rfl

@[simp] lemma chain'.pmap'_singleton {x : α} (h : chain' R [x])
  (f : Π (a ∈ [x]) (b ∈ [x]) (h : R a b), β) : h.pmap' f = [] := rfl

@[simp] lemma chain'.pmap'_cons_cons {x y : α} {l : list α} (h : chain' R (x :: y :: l))
  (f : Π (a ∈ (x :: y :: l)) (b ∈ (x :: y :: l)) (h : R a b), β) :
h.pmap' f =
  f x (mem_cons_self _ _) y (mem_cons_of_mem _ (mem_cons_self _ _)) (chain'_cons.mp h).left ::
    chain'.pmap' (chain'_cons.mp h).right
      (λ a ha b hb hab, f a (mem_cons_of_mem _ ha) b (mem_cons_of_mem _ hb) hab) := rfl

lemma chain'.of_mem_pmap' (h : chain' R l) (f : Π (a ∈ l) (b ∈ l) (h : R a b), β) (b : β)
  (hb : b ∈ h.pmap' f) : ∃ (x ∈ l) (y ∈ l) (hxy : R x y), b = f x ‹_› y ‹_› hxy :=
begin
  cases l with xl l,
  { simpa using hb },
  induction l with yl l IH generalizing xl,
  { simpa using hb },
  { simp only [mem_cons_iff, chain'.pmap'_cons_cons] at hb,
    rcases hb with rfl|hb,
    { exact ⟨xl, _, yl, _, _, rfl⟩ },
    { obtain ⟨xl', hx, yl', hy, hxy', rfl⟩ := IH _ _ _ hb,
      exact ⟨xl', _, yl', _, _, rfl⟩ } }
end

@[simp] lemma chain'.tail_pmap' (h : chain' R l) (f : Π (a ∈ l) (b ∈ l) (h : R a b), β) :
  (h.pmap' f).tail =
    h.tail.pmap' (λ a ha b hb hab, f a (mem_of_mem_tail l a ha) b (mem_of_mem_tail _ _ hb) hab) :=
begin
  rcases l with (_ | ⟨_, (_ | _)⟩);
  simpa only [chain'.pmap'_cons_cons, tail]
end

@[simp] lemma chain'.length_pmap' (h : chain' R l) (f : Π (a ∈ l) (b ∈ l) (h : R a b), β) :
  (h.pmap' f).length = length l - 1 :=
begin
  cases l with xl l,
  { simp },
  induction l with yl l IH generalizing xl,
  { simp },
  { simpa using IH _ _ _ }
end

@[simp] lemma chain'.nth_le_pmap' (h : chain' R l) (f : Π (a ∈ l) (b ∈ l) (h : R a b), β)
  (n : ℕ) (hnp : n < length (h.pmap' f))
  (hn : n + 1 < length l := by simpa [←nat.lt_pred_iff] using hnp)
  (hn' : n < length l := (nat.lt_succ_self _).trans hn) :
  (h.pmap' f).nth_le n hnp = f (l.nth_le n hn') (nth_le_mem _ _ _) (l.nth_le (n + 1) hn)
    (nth_le_mem _ _ _) (chain'_iff_nth_le.mp h n (lt_of_lt_of_le hnp (h.length_pmap' f).le)) :=
begin
  cases l with xl l,
  { simpa using hn },
  induction l with yl l IH generalizing xl n,
  { simpa using hn },
  { cases n,
    { simp, },
    { simpa using IH _ _ _ _ _ _ } }
end

@[simp] lemma chain'.pmap'_append {l' : list α} (h : chain' R l) (h' : chain' R l')
  (hl : ∀ x (hx : x ∈ l.last') y (hy : y ∈ l'.head'), R x y)
  (f : Π (a ∈ (l ++ l')) (b ∈ (l ++ l')) (h : R a b), β) :
  (h.append h' hl).pmap' f =
    h.pmap' (λ a ha b hb hab, f a (mem_append_left _ ha) b (mem_append_left _ hb) hab) ++
    (l.last'.pbind (λ a ha, l'.head'.pbind (λ b hb, some
      (f a (mem_append_left _ (mem_of_mem_last' ha))
        b (mem_append_right _ (mem_of_mem_head' hb)) (hl a ha b hb))))).to_list ++
    (h'.pmap' (λ a ha b hb hab, f a (mem_append_right _ ha) b (mem_append_right _ hb) hab)) :=
begin
  cases l with xl l,
  { convert (nil_append _).symm },
  induction l with yl l IH generalizing xl l',
  { cases l',
    { convert (append_nil _).symm },
    { simpa } },
  { cases l' with xl' l',
    { simp only [cons_append, chain'.pmap'_cons_cons, chain'.pmap'_nil, append_nil],
      refine ⟨rfl, _⟩,
      apply ext_le,
      { simp },
      { intros n hn hn',
        rw [chain'.nth_le_pmap', nth_le_append, chain'.nth_le_pmap'],
        { congr;
          exact append_nil l },
        { simp only [nat.add_succ_sub_one, add_zero, length, chain'.length_pmap'] at hn ⊢,
          convert hn,
          exact (append_nil l).symm } } },
    { simp only [cons_append, append_assoc, chain'.pmap'_cons_cons],
      refine ⟨rfl, _⟩,
      simp_rw ←append_assoc,
      convert IH _ h' _ _ _,
      rw chain'_cons at h,
      exact h.right } }
end

@[simp] lemma chain'.reverse_pmap' (h : chain' R l)
  (f : Π (a ∈ l) (b ∈ l) (h : R a b), β)
  (h' : chain' (flip R) l.reverse := chain'_reverse.mp ((reverse_reverse l).symm ▸ h)) :
  (h.pmap' f).reverse = chain'.pmap' h' (λ a ha b hb hab,
    f b (mem_reverse.mp hb) a (mem_reverse.mp ha) hab) :=
begin
  apply ext_le,
  { simp },
  { intros n hn hn',
    rw [chain'.nth_le_pmap', nth_le_reverse', chain'.nth_le_pmap'],
    { have : n + 1 < l.length,
      { simpa [←nat.lt_pred_iff] using hn },
      simp only [chain'.length_pmap'],
      rcases hL : l.length with _|_|L,
      { simpa [hL] using this },
      { simpa [hL] using this },
      congr' 1,
      { simp [nth_le_reverse' _ _ _ (nat.sub_one_sub_lt this), hL] },
      { rw [nth_le_reverse' _ _ _ (nat.sub_one_sub_lt (n.lt_succ_self.trans this))],
        congr' 1,
        rw ←nat.sub_add_comm,
        { simp [hL] },
        { refine nat.le_pred_of_lt _,
          simpa [hL] using hn } },
    { refine nat.sub_one_sub_lt _,
      simpa using hn } } }
end

@[simp] lemma chain'.pmap'_reverse (h : chain' R l.reverse)
  (f : Π (a ∈ l.reverse) (b ∈ l.reverse) (h : R a b), β)
  (h' : chain' (flip R) l := chain'_reverse.mp ((reverse_reverse l).symm ▸ h)) :
  (h.pmap' f) = (chain'.pmap' h' (λ a ha b hb hab,
    f b (mem_reverse.mpr hb) a (mem_reverse.mpr ha) hab)).reverse :=
begin
  rw chain'.reverse_pmap',
  congr
end

@[simp] def chain'.pmap'_eq_nil_iff {h : chain' R l} {f : Π (a ∈ l) (b ∈ l) (h : R a b), β} :
  h.pmap' f = [] ↔ length l ≤ 1 :=
begin
  rcases l with (_ | ⟨_, (_ | _)⟩);
  simp
end

/-- Transform a `l : list α`, when `chain' R l`, in a dependent fashion using a function over
`x y : α` that requires the relation `R x y`.
See `list.chain.pmap'` for the transformation that requires list membership. -/
def chain'.pmap (h : chain' R l) (f : Π (a b : α) (h : R a b), β) : list β :=
h.pmap' (λ a ha b hb h, f a b h)

@[simp] lemma chain'.pmap_nil (h : chain' R [])
  (f : Π (a b : α) (h : R a b), β) : h.pmap f = [] := rfl

@[simp] lemma chain'.pmap_singleton {x : α} (h : chain' R [x])
  (f : Π (a b : α) (h : R a b), β) : h.pmap f = [] := rfl

@[simp] lemma chain'.pmap_cons_cons {x y : α} {l : list α} (h : chain' R (x :: y :: l))
  (f : Π (a b : α) (h : R a b), β) :
h.pmap f = f x y (chain'_cons.mp h).left :: chain'.pmap (chain'_cons.mp h).right f := rfl

lemma chain'.of_mem_pmap (h : chain' R l) (f : Π (a b : α) (h : R a b), β) (b : β)
  (hb : b ∈ h.pmap f) : ∃ (x ∈ l) (y ∈ l) (hxy : R x y), b = f x y hxy :=
h.of_mem_pmap' _ _ hb

@[simp] lemma chain'.tail_pmap (h : chain' R l) (f : Π (a b : α) (h : R a b), β) :
  (h.pmap f).tail = h.tail.pmap f :=
h.tail_pmap' _

@[simp] lemma chain'.length_pmap (h : chain' R l) (f : Π (a b : α) (h : R a b), β) :
  (h.pmap f).length = length l - 1 :=
h.length_pmap' _

@[simp] lemma chain'.nth_le_pmap (h : chain' R l) (f : Π (a b : α) (h : R a b), β)
  (n : ℕ)
  (hnp : n < length (h.pmap f)) (hn : n + 1 < length l := by simpa [←nat.lt_pred_iff] using hnp)
  (hn' : n < length l := (nat.lt_succ_self _).trans hn) :
  (h.pmap f).nth_le n hnp = f (l.nth_le n hn') (l.nth_le (n + 1) hn)
    (chain'_iff_nth_le.mp h n (lt_of_lt_of_le hnp (h.length_pmap f).le)) :=
h.nth_le_pmap' _ _ _ _ _

@[simp] lemma chain'.pmap_append {l' : list α} (h : chain' R l) (h' : chain' R l')
  (hl : ∀ x (hx : x ∈ l.last') y (hy : y ∈ l'.head'), R x y) (f : Π (a b : α) (h : R a b), β) :
  (h.append h' hl).pmap f = h.pmap f ++
    (l.last'.pbind (λ a ha, l'.head'.pbind (λ b hb, some (f a b (hl a ha b hb))))).to_list ++
    (h'.pmap f) :=
chain'.pmap'_append _ _ _ _

@[simp] lemma chain'.reverse_pmap (h : chain' R l)
  (f : Π (a b : α) (h : R a b), β)
  (h' : chain' (flip R) l.reverse := chain'_reverse.mp ((reverse_reverse l).symm ▸ h)) :
  (h.pmap f).reverse = chain'.pmap h' (λ a b hab, f b a hab) :=
chain'.reverse_pmap' _ _

@[simp] lemma chain'.pmap_reverse (h : chain' R l.reverse)
  (f : Π (a b : α) (h : R a b), β)
  (h' : chain' (flip R) l := chain'_reverse.mp ((reverse_reverse l).symm ▸ h)) :
  (h.pmap f) = (chain'.pmap h' (λ a b hab, f b a hab)).reverse :=
chain'.pmap'_reverse _ _

@[simp] def chain'.pmap_eq_nil_iff {h : chain' R l} {f : Π (a b : α) (h : R a b), β} :
  h.pmap f = [] ↔ length l ≤ 1 :=
chain'.pmap'_eq_nil_iff

end pmap

end list

open list
namespace simple_graph
variables {V : Type u} (G : simple_graph V)

/-- A walk is a sequence of adjacent vertices.  For vertex `v : V`,
the type `walk v` consists of all walks starting at `v`.

We say that a walk *visits* the vertices it contains.  The set of vertices a
walk visits is `simple_graph.walk.support`. -/
structure walk (start : V) (terminal : V) :=
(support' : list V)
(walked : chain' G.adj (start :: support'))
(terminates : last (start :: support') (λ H, list.no_confusion H) = terminal)

/-- The empty walk is solely the start vertex. -/
@[refl] def walk.nil (v : V) : G.walk v v :=
⟨[], chain.nil, last_singleton _ _⟩

instance walk.inhabited (v : V) : inhabited (G.walk v v) := ⟨by refl⟩

namespace walk
variables {G} {u v : V} (w : G.walk u v)

/-- The `support` of a walk is the list of vertices it visits. -/
def support : list V := u :: w.support'

lemma support_def : w.support = u :: w.support' := rfl

lemma tail_support : w.support.tail = w.support' := rfl

lemma walked_support : chain' G.adj w.support := w.walked

@[simp] lemma support_ne_nil : w.support ≠ [] := λ H, list.no_confusion H

@[simp] lemma last_support : last w.support w.support_ne_nil = v := w.terminates

@[simp] lemma last_support' (h : w.support' ≠ []) : last w.support' h = v :=
by { convert w.last_support using 1, simp_rw [support_def], rw last_cons }

lemma support_eq_init_append : w.support = w.support.init ++ [v] :=
by simp_rw [←w.last_support, init_append_last]

lemma support'_eq_nil_iff {w : G.walk u v} : w.support' = [] ↔ w.support = [u] :=
by simp [support_def]

lemma last'_support : w.support.last' = some v :=
by simp [w.last_support]

@[simp] lemma head'_support : w.support.head' = some u := rfl

lemma support_nth_le_zero :
  w.support.nth_le 0 (length_pos_of_ne_nil w.support_ne_nil) = u := rfl

lemma vertex_congr_left {u v w x : V} {p : G.walk u v} {q : G.walk w x}
  (h : p.support = q.support) : u = w :=
begin
  simp only [support_def] at h,
  exact h.left
end

lemma vertex_congr_right {u v w x : V} {p : G.walk u v} {q : G.walk w x}
  (h : p.support = q.support) : v = x :=
begin
  have h' := id h,
  rw [p.support_eq_init_append, q.support_eq_init_append, h, append_right_inj] at h',
  simpa using h'
end

lemma nil_vertex_congr (w : G.walk u v) (h : w.support.length = 1) :
  u = v :=
begin
  obtain ⟨x, hx⟩ : ∃ (x : V), w.support = [x] := length_eq_one.mp h,
  simp [←w.last_support, ←w.support_nth_le_zero, hx]
end

@[ext] lemma ext {p q : G.walk u v} (h : p.support = q.support) :
  p = q :=
by { cases p, cases q, simpa [support_def] using h }

lemma ext_iff {p q : G.walk u v} :
  p = q ↔ p.support = q.support :=
⟨λ h, congr_arg _ h, ext⟩

@[simp] lemma support_nil (v : V) : support (nil G v) = [v] := rfl

@[simp] lemma support'_nil (v : V) : support' (nil G v) = [] := rfl

@[simp] lemma support'_nth_le (n : ℕ)
  (h : n < w.support'.length)
  (h' : n + 1 < w.support.length := nat.succ_le_succ h) :
  w.support'.nth_le n h = w.support.nth_le (n + 1) h' := rfl

/-- The `edges` of a walk is the list of edges it visits. -/
def edges : list G.edge_set :=
w.walked_support.pmap (λ a b h, ⟨⟦(a, b)⟧, h⟩)

@[simp] lemma edges_nil : edges (nil G u) = [] := rfl

/-- The length of a walk is the number of edges along it. -/
def length : ℕ := w.support'.length

/-- The concatenation of two compatible walks. -/
@[trans]
def concat {u v w : V} (p : G.walk u v) (q : G.walk v w) : G.walk u w :=
⟨p.support' ++ q.support',
  p.walked.append q.walked.tail
  (by { suffices : ∀ (a : 0 < q.support'.length), G.adj v (q.support'.nth_le 0 a),
        { simpa [←support_def, nth_eq_some, ←nth_zero] },
        convert λ h, chain'_iff_nth_le.mp q.walked_support 0 h }),
  by { cases h : q.support' with hd tl,
        { have : q.support.length = 1,
          { rw [support_def, h, length_singleton] },
          simpa [←support_def] using q.nil_vertex_congr this },
        { convert q.last_support using 1,
          simp_rw [←cons_append, list.last_append' (u :: p.support') (hd :: tl) _ (by simp),
                   ←h, last_support, last_support'] } }⟩

@[simp] lemma support_concat {u v w : V} (p : G.walk u v) (q : G.walk v w) :
  (p.concat q).support = p.support ++ q.support' := rfl

@[simp] lemma support'_concat {u v w : V} (p : G.walk u v) (q : G.walk v w) :
  (p.concat q).support' = p.support' ++ q.support' := rfl

/-- Reverse the orientation of a walk. -/
@[symm]
def reverse {u v : V} (w : G.walk u v) : G.walk v u :=
⟨w.support.init.reverse, by {
  convert chain'_reverse.mpr w.walked,
  { ext,
    exact adj_comm G _ _ },
  { rw ←reverse_eq_iff,
    simpa [w.support_def] using w.support_eq_init_append.symm } },
  by { simp_rw [←w.support_nth_le_zero],
       rw ←list.last_reverse,
       { congr,
         rw ←reverse_eq_iff,
         simpa [w.support_def] using w.support_eq_init_append.symm },
       { simp } }⟩

@[simp] lemma support'_reverse (w : G.walk u v) : support' w.reverse = w.support.init.reverse := rfl

@[simp] lemma support_reverse (w : G.walk u v) : support w.reverse = w.support.reverse :=
by rw [←reverse_eq_iff, support_def, reverse_cons, support'_reverse, reverse_reverse,
       ←support_eq_init_append]

/-- Get the `n`th vertex from a path, where `n` is generally expected to be
between `0` and `p.length`, inclusive.
If `n` is greater than the length of the path, the result is the path's endpoint. -/
def get_vert (p : G.walk u v) (n : ℕ) : V :=
if h : n < p.support.length then p.support.nth_le n h else v

/-- Prepend a vertex to a walk, given that it is adjacent to the start of the walk. -/
def cons {u v w : V} (p : G.walk v w) (h : G.adj u v) : G.walk u w :=
⟨p.support, p.walked_support.cons h, by rw [last_cons _ p.support_ne_nil, p.last_support]⟩

@[simp] lemma support_cons {u v w : V} (p : G.walk v w) (h : G.adj u v) :
  support (cons p h) = u :: support p := rfl

@[simp] lemma support'_cons {u v w : V} (p : G.walk v w) (h : G.adj u v) :
  support' (cons p h) = support p := rfl

@[simp] lemma edges_cons {u v w : V} (p : G.walk v w) (h : G.adj u v) :
  edges (cons p h) = ⟨⟦(u, v)⟧, h⟩ :: edges p := rfl

/-- Append a vertex to a walk, given that it is adjacent to the terminal of the walk. -/
def snoc {u v w : V} (p : G.walk u v) (h : G.adj v w) : G.walk u w :=
⟨p.support' ++ [w],
  by { refine p.walked.append (chain'_singleton w) _, simpa [←support_def] },
  by { rw [last_cons, list.last_append', last_singleton]; simp }⟩

@[simp] lemma support_snoc {u v w : V} (p : G.walk u v) (h : G.adj v w) :
  support (snoc p h) = support p ++ [w] := rfl

@[simp] lemma support'_snoc {u v w : V} (p : G.walk u v) (h : G.adj v w) :
  support' (snoc p h) = support' p ++ [w] := rfl

@[simp] lemma cons_concat {u v w x : V} (h : G.adj u v) (p : G.walk v w) (q : G.walk w x) :
  (p.cons h).concat q = (p.concat q).cons h := rfl

@[simp] lemma cons_nil_concat {u v w : V} (h : G.adj u v) (p : G.walk v w) :
  (cons (nil _ _) h).concat p = p.cons h := rfl

@[simp] lemma concat_nil {u v : V} (p : G.walk u v) : p.concat (nil _ _) = p :=
ext (by simp)

@[simp] lemma nil_concat {u v : V} (p : G.walk u v) : (nil _ _).concat p = p :=
ext (by simp [←support_def])

lemma concat_assoc {u v w x : V} (p : G.walk u v) (q : G.walk v w) (r : G.walk w x) :
  p.concat (q.concat r) = (p.concat q).concat r :=
ext (by simp)

@[simp] lemma nil_reverse (u : V) : (nil G u).reverse = nil G u := rfl

lemma singleton_reverse {u v : V} (h : G.adj u v) :
  (cons (nil _ _) h).reverse = cons (nil _ _) (G.sym h) := rfl

@[simp] lemma concat_reverse {u v w : V} (p : G.walk u v) (q : G.walk v w) :
  (p.concat q).reverse = q.reverse.concat p.reverse :=
ext
  (by simpa [q.support_def, append_right_inj, reverse_eq_iff] using p.support_eq_init_append)

@[simp] lemma cons_reverse {u v w : V} (h : G.adj u v) (p : G.walk v w) :
  (cons p h).reverse = p.reverse.concat (cons (nil _ _) (G.sym h)) :=
ext (by simp)

@[simp] lemma reverse_reverse {u v : V} (p : G.walk u v) : p.reverse.reverse = p :=
ext (by simp)

@[simp] lemma nil_length {u : V} : (nil G u).length = 0 := rfl

@[simp] lemma cons_length {u v w : V} (h : G.adj u v) (p : G.walk v w) :
  (cons p h).length = p.length + 1 := rfl

@[simp] lemma concat_length {u v w : V} (p : G.walk u v) (q : G.walk v w) :
  (p.concat q).length = p.length + q.length :=
by simp [length]

@[simp] lemma reverse_length {u v : V} (p : G.walk u v) : p.reverse.length = p.length :=
by simp [length, p.support_def]

variables [decidable_eq V]

lemma edge_vert_mem_support {t u v w : V} (ha : G.adj t u) (p : G.walk v w)
  (he : (⟨⟦(t, u)⟧, ha⟩ : G.edge_set) ∈ p.edges) :
  t ∈ p.support :=
begin
  obtain ⟨x, hx, y, hy, hxy, hxy'⟩ := chain'.of_mem_pmap _ _ _ he,
  simp only [quotient.eq] at hxy',
  cases hxy',
  { exact hx },
  { exact hy }
end

@[simp] lemma length_edges : w.edges.length = w.support.length - 1 :=
w.walked_support.length_pmap _

@[simp] lemma nth_le_edges (n : ℕ) (hn : n < w.edges.length)
  (hns' : n + 1 < w.support.length := by simpa [←nat.lt_pred_iff] using hn)
  (hns : n < w.support.length := (nat.lt_succ_self _).trans hns') :
  w.edges.nth_le n hn =
    ⟨⟦(w.support.nth_le n hns, w.support.nth_le (n + 1) hns')⟧,
     by simpa using (chain'_iff_nth_le.mp w.walked_support) _ (hn.trans_le w.length_edges.le)⟩ :=
w.walked_support.nth_le_pmap _ _ _

@[simp]
lemma edges_concat {u v w : V} (p : G.walk u v) (p' : G.walk v w) :
  (p.concat p').edges = p.edges ++ p'.edges :=
begin
  simp only [edges],
  generalize_proofs h h' h'',
  rw [support_def, chain'_cons'] at h'',
  convert (chain'.pmap_append h' h''.right (by simpa using h''.left) _) using 1,
  rw [append_assoc, append_right_inj],
  rcases H : p'.support with (_ | ⟨x, (_ | ⟨y, l⟩)⟩),
  { simpa using H },
  { convert (chain'.pmap_singleton _ _),
    { simp only [support_def] at H,
      simp [H.right] },
    { rw ←H,
      exact p'.walked_support } },
  { convert (chain'.pmap_cons_cons _ _),
    { convert singleton_append,
      { suffices : ∃ (a : V), p'.support'.head' = some a ∧ (v, a) ≈ (x, y),
        { simpa },
        simp only [support_def] at H,
        simp [H.left, H.right] },
      { simp only [support_def] at H,
        simp [H.right] } },
    { rw ←H,
      exact p'.walked_support } }
end

@[simp]
lemma edges_reverse {u v : V} (p : G.walk u v) : p.reverse.edges = p.edges.reverse :=
begin
  simp_rw edges,
  convert chain'.pmap_reverse _ _,
  { simp },
  { funext,
    simpa using adj_comm G _ _ },
  { refine function.hfunext rfl _,
    intros a a' ha,
    refine function.hfunext rfl _,
    intros b b' hb,
    refine congr_arg_heq subtype.mk _,
    simp only [heq_iff_eq] at ha hb,
    simpa [ha, hb] using sym2.eq_swap },
  { simpa using p.reverse.walked_support }
end

/-- A *trail* is a walk with no repeating edges. -/
def is_trail {u v : V} (p : G.walk u v) : Prop := p.edges.nodup

/-- A *path* is a trail with no repeating vertices. -/
def is_path {u v : V} (p : G.walk u v) : Prop := p.is_trail ∧ p.support.nodup

/-- A *cycle* at `u : V` is a nonempty trail whose only repeating vertex is `u`. -/
def is_cycle {u : V} (p : G.walk u u) : Prop :=
p ≠ nil _ _ ∧ p.is_trail ∧ (p.support.erase u).nodup

lemma is_path.is_trail {u : V} {p : G.walk u u} (h : p.is_path) : p.is_trail := h.1

lemma is_cycle.is_trail {u : V} {p : G.walk u u} (h : p.is_cycle) : p.is_trail := h.2.1

lemma is_trail.count_le_one {u v : V} {p : G.walk u v} (h : p.is_trail) (e : G.edge_set) :
  p.edges.count e ≤ 1 :=
nodup_iff_count_le_one.mp h _

lemma is_trail.count_eq_one {u v : V} {p : G.walk u v} (h : p.is_trail) {e : G.edge_set}
  (he : e ∈ p.edges) :
  p.edges.count e = 1 :=
count_eq_one_of_mem h he

@[simp] lemma nil_is_trail {u : V} : (nil G u).is_trail :=
by simp [is_trail]

@[simp] lemma nil_is_path {u : V} : (nil G u).is_path :=
by simp [is_path, support]

lemma is_trail_of_is_trail_cons {u v w : V} {h : G.adj u v} {p : G.walk v w} (h : (cons p h).is_trail) :
  p.is_trail :=
begin
  rw [is_trail, edges_cons, nodup_cons] at h,
  exact h.2
end

lemma is_path_of_is_path_cons {u v w : V} {h : G.adj u v} {p : G.walk v w} (h : (cons p h).is_path) :
  p.is_path :=
begin
  rw [is_path, support_cons, nodup_cons] at h,
  exact ⟨is_trail_of_is_trail_cons h.1, h.2.2⟩
end

lemma is_trail_cons_iff {u v w : V} (h : G.adj u v) (p : G.walk v w) :
  (cons p h).is_trail ↔ p.is_trail ∧ (⟨⟦(u, v)⟧, h⟩ : G.edge_set) ∉ p.edges :=
by simp only [is_trail, and_comm, iff_self, edges_cons, nodup_cons]

lemma is_path_cons_iff {u v w : V} (h : G.adj u v) (p : G.walk v w) :
  (cons p h).is_path ↔ p.is_path ∧ u ∉ p.support :=
begin
  simp only [is_path, and_comm, and.left_comm, is_trail_cons_iff, support_cons, nodup_cons,
             and_iff_left_iff_imp, and.congr_right_iff],
  intros hn ht hs H,
  exact hs (edge_vert_mem_support _ _ H)
end

end walk

/-- Two vertices are *reachable* if there is a walk between them. -/
def reachable (u v : V) : Prop := nonempty (G.walk u v)

variables {G}

protected lemma reachable.elim {p : Prop} {u v : V}
  (h : G.reachable u v) (hp : G.walk u v → p) : p :=
nonempty.elim h hp

@[refl] lemma reachable.refl {u : V} : G.reachable u u := by { fsplit, refl }

@[symm] lemma reachable.symm {u v : V} (huv : G.reachable u v) : G.reachable v u :=
huv.elim (λ p, ⟨p.reverse⟩)

@[trans] lemma reachable.trans {u v w : V} (huv : G.reachable u v) (hvw : G.reachable v w) :
  G.reachable u w :=
huv.elim (λ puv, hvw.elim (λ pvw, ⟨puv.concat pvw⟩))

variables (G)

lemma reachable_is_equivalence : equivalence G.reachable :=
mk_equivalence _ (@reachable.refl _ G) (@reachable.symm _ G) (@reachable.trans _ G)

/-- The equivalence relation on vertices given by `simple_graph.reachable`. -/
def reachable_setoid : setoid V := setoid.mk _ G.reachable_is_equivalence

/-- The connected components of a graph are elements of the quotient of vertices by
the `simple_graph.reachable` relation. -/
def connected_component := quot G.reachable

/-- A graph is connected is every pair of vertices is reachable from one another. -/
def is_connected : Prop := ∀ (u v : V), G.reachable u v

/-- Gives the connected component containing a particular vertex. -/
def connected_component_of (v : V) : G.connected_component := quot.mk G.reachable v

instance connected_components.inhabited [inhabited V] : inhabited G.connected_component :=
⟨G.connected_component_of (default _)⟩

lemma connected_component.subsingleton_of_is_connected (h : G.is_connected) :
  subsingleton G.connected_component :=
⟨λ c d, quot.ind (λ v d, quot.ind (λ w, quot.sound (h v w)) d) c d⟩

section walk_to_path

/-- The type of paths between two vertices. -/
abbreviation path [decidable_eq V] (u v : V) := {p : G.walk u v // p.is_path}

#exit

namespace walk
variables {G}

/-- Given a walk and a vertex in the walk's support, create a walk starting from that vertex.

The resulting walk begins at the last instance of that vertex in the original walk. -/
def subwalk_from : Π {u v w : V} (p : G.walk u v), w ∈ p.support → G.walk w v
| _ _ w nil h :=
  by { rw [nil_support, multiset.singleton_eq_singleton, multiset.mem_singleton] at h, subst w }
| u v w (@cons _ _ _ x _ ha p) hs := begin
  rw [cons_support, multiset.mem_cons] at hs,
  by_cases hw : w = u,
  { subst w,
    exact cons ha p, },
  { have : w ∈ p.support := hs.cases_on (λ hw', (hw hw').elim) id,
    exact p.subwalk_from this, },
end

/-- Given a walk, produces a walk with the same endpoints and no repeated vertices or edges. -/
def to_path_aux : Π {u v : V}, G.walk u v → G.walk u v
| u v nil := nil
| u v (@cons _ _ _ x _ ha p) :=
  let p' := p.to_path_aux
  in if hs : u ∈ p'.support
     then p'.subwalk_from hs
     else cons ha p'

lemma subwalk_from_is_path {u v w : V} (p : G.walk u v) (h : p.is_path) (hs : w ∈ p.support) :
  (p.subwalk_from hs).is_path :=
begin
  induction p,
  { rw [nil_support, multiset.singleton_eq_singleton, multiset.mem_singleton] at hs,
    subst w,
    exact h, },
  { rw [cons_support, multiset.mem_cons] at hs,
    simp only [subwalk_from],
    split_ifs with hw hw,
    { subst w,
      exact h, },
    { cases hs with hs₁ hs₂,
      { exact (hw hs₁).elim },
      { apply p_ih,
        exact is_path_of_cons_is_path h, }, }, },
end

lemma to_path_aux_is_path {u v : V} (p : G.walk u v) : p.to_path_aux.is_path :=
begin
  induction p,
  { simp [to_path_aux], },
  { simp [to_path_aux],
    split_ifs,
    { exact subwalk_from_is_path _ p_ih _, },
    { rw cons_is_path_iff,
      exact ⟨p_ih, h⟩, }, },
end

/-- Given a walk, produces a path with the same endpoints using `simple_graph.walk.to_path_aux`. -/
def to_path {u v : V} (p : G.walk u v) : G.path u v := ⟨p.to_path_aux, to_path_aux_is_path p⟩

@[simp] lemma path_is_path {u v : V} (p : G.path u v) : is_path (p : G.walk u v) := p.property

@[simp] lemma path_is_trail {u v : V} (p : G.path u v) : is_trail (p : G.walk u v) := p.property.1

lemma to_path_avoids.aux1 {u v w : V} (e : G.edge_set)
  (p : G.walk v w) (hp : e ∉ p.edges) (hu : u ∈ p.support) :
  e ∉ walk.edges (walk.subwalk_from p hu) :=
begin
  induction p,
  { simp [subwalk_from],
    generalize_proofs,
    subst u,
    exact hp, },
  { simp [subwalk_from],
    split_ifs,
    { subst u,
      simpa using hp, },
    { apply p_ih,
      simp at hp,
      push_neg at hp,
      exact hp.2, }, },
end

lemma to_path_avoids {v w : V} (e : G.edge_set)
  (p : G.walk v w) (hp : e ∉ p.edges) :
  e ∉ walk.edges (p.to_path : G.walk v w) :=
begin
  simp only [to_path, subtype.coe_mk],
  induction p,
  { simp [to_path_aux], },
  { simp [to_path_aux],
    split_ifs,
    { apply to_path_avoids.aux1,
      apply p_ih,
      simp at hp,
      push_neg at hp,
      exact hp.2, },
    { simp [to_path_aux],
      push_neg,
      simp at hp,
      push_neg at hp,
      use hp.1,
      apply p_ih,
      exact hp.2, }, },
end


lemma reverse_trail {u v : V} (p : G.walk u v) (h : p.is_trail) : p.reverse.is_trail :=
by simpa [is_trail] using h

@[simp] lemma reverse_trail_iff {u v : V} (p : G.walk u v) : p.reverse.is_trail ↔ p.is_trail :=
begin
  split,
  { intro h,
    convert reverse_trail _ h,
    rw reverse_reverse, },
  { exact reverse_trail p, },
end

lemma is_trail_of_concat_left {u v w : V} (p : G.walk u v) (q : G.walk v w) (h : (p.concat q).is_trail) :
  p.is_trail :=
begin
  induction p,
  { simp, },
  { simp [cons_is_trail_iff],
    simp [cons_is_trail_iff] at h,
    split,
    apply p_ih _ h.1,
    intro h',
    apply h.2,
    exact or.inl h', },
end

lemma is_trail_of_concat_right {u v w : V} (p : G.walk u v) (q : G.walk v w) (h : (p.concat q).is_trail) :
  q.is_trail :=
begin
  rw [←reverse_trail_iff, concat_reverse] at h,
  rw ←reverse_trail_iff,
  exact is_trail_of_concat_left _ _ h,
end

lemma reverse_path {u v : V} (p : G.walk u v) (h : p.is_path) : p.reverse.is_path :=
by simpa [is_path] using h

@[simp] lemma reverse_path_iff {u v : V} (p : G.walk u v) : p.reverse.is_path ↔ p.is_path :=
begin
  split,
  { intro h,
    convert reverse_path _ h,
    rw reverse_reverse, },
  { exact reverse_path p, },
end

def split_at_vertex_fst : Π {v w : V} (p : G.walk v w) (u : V) (h : u ∈ p.support), G.walk v u
| v w nil u h := begin
  simp only [multiset.singleton_eq_singleton, nil_support, multiset.mem_singleton] at h,
  subst h,
end
| v w (cons r p) u h :=
  if hx : v = u then
    by subst u
  else
  begin
    simp only [multiset.mem_cons, cons_support] at h,
    have : u ∈ p.support := h.cases_on (λ h', (hx h'.symm).elim) id,
    exact cons r (split_at_vertex_fst p _ this),
  end

def split_at_vertex_snd : Π {v w : V} (p : G.walk v w) (u : V) (h : u ∈ p.support), G.walk u w
| v w nil u h := begin
  simp only [multiset.singleton_eq_singleton, nil_support, multiset.mem_singleton] at h,
  subst h,
end
| v w (cons r p) u h :=
  if hx : v = u then
    by { subst u, exact cons r p }
  else
  begin
    simp only [multiset.mem_cons, cons_support] at h,
    have : u ∈ p.support := h.cases_on (λ h', (hx h'.symm).elim) id,
    exact split_at_vertex_snd p _ this,
  end

@[simp]
lemma split_at_vertex_spec {u v w : V} (p : G.walk v w) (h : u ∈ p.support) :
  (p.split_at_vertex_fst u h).concat (p.split_at_vertex_snd u h) = p :=
begin
  induction p,
  { simp only [split_at_vertex_fst, split_at_vertex_snd],
    generalize_proofs,
    subst u,
    refl, },
  { simp at h,
    cases h,
    { subst u,
      simp [split_at_vertex_fst, split_at_vertex_snd], },
    { by_cases hvu : p_u = u,
      subst p_u,
      simp [split_at_vertex_fst, split_at_vertex_snd],
      simp [split_at_vertex_fst, split_at_vertex_snd, hvu, p_ih], }, },
end

lemma split_at_vertex_support {u v w : V} (p : G.walk v w) (h : u ∈ p.support) :
  (p.split_at_vertex_fst u h).support + (p.split_at_vertex_snd u h).support
    = p.support + {u} :=
begin
  induction p,
  { simp [split_at_vertex_fst, split_at_vertex_snd],
    generalize_proofs,
    subst p,
    refl, },
  { simp [split_at_vertex_fst, split_at_vertex_snd],
    split_ifs,
    { subst p_u,
      simp, },
    { simp [p_ih],
      rw multiset.cons_swap, }, },
end

lemma split_at_vertex_edges {u v w : V} (p : G.walk v w) (h : u ∈ p.support) :
  (p.split_at_vertex_fst u h).edges + (p.split_at_vertex_snd u h).edges
    = p.edges :=
begin
  induction p,
  { simp [split_at_vertex_fst, split_at_vertex_snd],
    generalize_proofs,
    subst p,
    simp, },
  { simp [split_at_vertex_fst, split_at_vertex_snd],
    split_ifs,
    { subst p_u,
      simp, },
    { simp [p_ih], }, },
end

lemma split_at_vertex_fst_is_trail {u v w : V} (p : G.walk v w) (hc : p.is_trail) (h : u ∈ p.support) :
  (p.split_at_vertex_fst u h).is_trail :=
begin
  induction p,
  { simp [split_at_vertex_fst],
    generalize_proofs,
    subst p,
    exact hc, },
  { simp [split_at_vertex_fst],
    split_ifs,
    { subst u,
      simp, },
    { simp [cons_is_trail_iff] at hc ⊢,
      simp at h,
      cases h,
      { exact (h_1 h_2.symm).elim, },
      { cases hc with hc1 hc2,
        simp [p_ih hc1 h_2],
        rw ←split_at_vertex_edges _ h_2 at hc2,
        intro h,
        apply hc2,
        rw multiset.mem_add,
        exact or.inl h, }, }, },
end

lemma split_at_vertex_snd_is_trail {u v w : V} (p : G.walk v w) (hc : p.is_trail) (h : u ∈ p.support) :
  (p.split_at_vertex_snd u h).is_trail :=
begin
  induction p,
  { simp [split_at_vertex_snd],
    generalize_proofs,
    subst p,
    exact hc, },
  { simp [split_at_vertex_snd],
    split_ifs,
    { subst u,
      simp [hc], },
    { simp [cons_is_trail_iff] at hc ⊢,
      simp at h,
      cases h,
      { exact (h_1 h_2.symm).elim, },
      { cases hc with hc1 hc2,
        simp [p_ih hc1 h_2], }, }, },
end

/-- Rotate a loop walk such that it is centered at the given vertex. -/
def rotate {u v : V} (c : G.walk v v) (h : u ∈ c.support) : G.walk u u :=
(c.split_at_vertex_snd u h).concat (c.split_at_vertex_fst u h)

@[simp]
lemma rotate_support {u v : V} (c : G.walk v v) (h : u ∈ c.support) :
  (c.rotate h).support = c.support + {u} - {v} :=
begin
  simp only [rotate, multiset.singleton_eq_singleton, add_zero, multiset.sub_zero,
    concat_support, multiset.sub_cons, multiset.add_cons],
  rw [add_comm, split_at_vertex_support, add_comm],
  refl,
end

@[simp]
lemma rotate_edges {u v : V} (c : G.walk v v) (h : u ∈ c.support) :
  (c.rotate h).edges = c.edges :=
begin
  simp [rotate, concat_edges],
  rw [add_comm, split_at_vertex_edges],
end

lemma rotate_trail {u v : V} (c : G.walk v v) (hc : c.is_trail) (h : u ∈ c.support) :
  (c.rotate h).is_trail :=
by simpa [is_trail] using hc

lemma rotate_cycle {u v : V} (c : G.walk v v) (hc : c.is_cycle) (h : u ∈ c.support) :
  (c.rotate h).is_cycle :=
begin
  split,
  { cases c,
    { exfalso,
      simpa [is_cycle] using hc, },
    { simp [rotate, split_at_vertex_snd, split_at_vertex_fst],
      split_ifs,
      { subst u,
        simp, },
      { intro hcon,
        have hcon' := congr_arg walk.length hcon,
        simpa using hcon', }, }, },
  split,
  { apply rotate_trail,
    exact is_trail_of_cycle hc, },
  { simp,
    by_cases huv : u = v; simp [huv, hc.2.2], },
end

/-- Get the vertex immediately after the split point, where if the very last vertex was the split
point we use the first vertex (wrapping around). -/
def vertex_after_split {u v w : V} (c : G.walk v w) (h : u ∈ c.support) : V :=
match v, w, c.split_at_vertex_snd u h with
| _, _, nil := v
| _, _, (@cons _ _ _ x _ r p) := x
end

end walk

namespace path
variables {G}

/-- The empty path at a vertex. -/
@[refl] def nil {u : V} : G.path u u := ⟨walk.nil, by simp⟩

/-- The length-1 path given by a pair of adjacent vertices. -/
def singleton {u v : V} (h : G.adj u v) : G.path u v :=
⟨walk.cons h walk.nil, by simp [walk.is_path, walk.is_trail, walk.edges, G.ne_of_adj h]⟩

@[symm] def reverse {u v : V} (p : G.path u v) : G.path v u :=
⟨walk.reverse p, walk.reverse_path p p.property⟩

end path

section map
variables {G} {V' : Type*} {G' : simple_graph V'} [decidable_eq V']

/-- Given a graph homomorphism, map walks to walks. -/
def walk.map (f : G →g G') : Π {u v : V}, G.walk u v → G'.walk (f u) (f v)
| _ _ walk.nil := walk.nil
| _ _ (walk.cons p h) := walk.cons (f.map_adj h) (walk.map p)

lemma walk.map_concat (f : G →g G') {u v w : V} (p : G.walk u v) (q : G.walk v w) :
  (p.concat q).map f = (p.map f).concat (q.map f) :=
begin
  induction p,
  { refl, },
  { simp [walk.map, p_ih], },
end

@[simp]
lemma walk.map_support_eq (f : G →g G') {u v : V} (p : G.walk u v) :
  (p.map f).support = p.support.map f :=
begin
  induction p,
  { refl, },
  { simp [walk.map, p_ih], },
end

@[simp]
lemma walk.map_edges_eq (f : G →g G') {u v : V} (p : G.walk u v) :
  (p.map f).edges = p.edges.map f.map_edge_set :=
begin
  induction p,
  { refl, },
  { simp only [walk.map, walk.edges, p_ih, multiset.map_cons, multiset.cons_inj_left],
    refl, },
end

/-- Given an injective graph homomorphism, map paths to paths. -/
def path.map (f : G →g G') (hinj : function.injective f) {u v : V} (p : G.path u v) :
  G'.path (f u) (f v) :=
⟨walk.map f p, begin
  cases p with p hp,
  induction p,
  { simp [walk.map], },
  { rw walk.cons_is_path_iff at hp,
    specialize p_ih hp.1,
    rw subtype.coe_mk at p_ih,
    simp only [walk.map, walk.cons_is_path_iff, p_ih, not_exists, true_and,
      walk.map_support_eq, not_and, multiset.mem_map, subtype.coe_mk],
    intros x hx hf,
    have := hinj hf,
    subst x,
    exact hp.2 hx, },
end⟩

end map

end walk_to_path

namespace walk
variables {G}

/-- Whether or not the path `p` is a prefix of the path `q`. -/
def prefix_of [decidable_eq V] : Π {u v w : V} (p : G.walk u v) (q : G.walk u w), Prop
| u v w nil _ := true
| u v w (cons _ _) nil := false
| u v w (@cons _ _ _ x _ r p) (@cons _ _ _ y _ s q) :=
  if h : x = y
  then by { subst y, exact prefix_of p q }
  else false

end walk

section
variables [decidable_eq V]

/-- A graph is *acyclic* (or a *forest*) if it has no cycles.

A characterization: `simple_graph.is_acyclic_iff`.-/
def is_acyclic : Prop := ∀ (v : V) (c : G.walk v v), ¬c.is_cycle

/-- A *tree* is a connected acyclic graph. -/
def is_tree : Prop := G.is_connected ∧ G.is_acyclic

namespace subgraph
variables {G} (H : subgraph G)

/-- A subgraph is connected if it is connected as a simple graph. -/
abbreviation is_connected : Prop := H.coe.is_connected

/-- An edge of a subgraph is a bridge edge if, after removing it, its incident vertices
are no longer reachable. -/
def is_bridge {v w : V} (h : H.adj v w) : Prop :=
¬(H.delete_edges {⟦(v, w)⟧}).spanning_coe.reachable v w

end subgraph

/-- An edge of a graph is a bridge if, after removing it, its incident vertices
are no longer reachable.

Characterizations of bridges:
`simple_graph.is_bridge_iff_walks_contain`
`is_bridge_iff_no_cycle_contains` -/
def is_bridge {v w : V} (h : G.adj v w) : Prop := (⊤ : G.subgraph).is_bridge h

/-- Given a walk that avoids an edge, create a walk in the subgraph with that deleted. -/
def walk_of_avoiding_walk {v w : V} (e : G.edge_set)
  (p : G.walk v w) (hp : e ∉ p.edges) :
  ((⊤ : G.subgraph).delete_edges {e}).spanning_coe.walk v w :=
begin
  induction p,
  { refl, },
  { cases e with e he,
    simp only [walk.edges, multiset.mem_cons, subtype.mk_eq_mk] at hp,
    push_neg at hp,
    apply walk.cons _ (p_ih _),
    use p_h,
    simp only [set.mem_singleton_iff, subtype.coe_mk],
    exact hp.1.symm,
    exact hp.2, },
end

lemma is_bridge_iff_walks_contain {v w : V} (h : G.adj v w) :
  G.is_bridge h ↔ ∀ (p : G.walk v w), (⟨⟦(v, w)⟧, h⟩ : G.edge_set) ∈ p.edges :=
begin
  split,
  { intros hb p,
    by_contra he,
    apply hb,
    exact ⟨walk_of_avoiding_walk _ _ p he⟩, },
  { intro hpe,
    rintro ⟨p'⟩,
    specialize hpe (p'.map (subgraph.map_spanning_top _)),
    simp only [set_coe.exists, walk.map_edges_eq, multiset.mem_map] at hpe,
    obtain ⟨z, zmem, he, hd⟩ := hpe,
    simp only [subgraph.map_spanning_top, hom.map_edge_set, rel_hom.coe_fn_mk,
      id.def, subtype.coe_mk, sym2.map_id] at hd,
    subst z,
    simpa [subgraph.spanning_coe] using zmem, },
end

lemma is_bridge_iff_no_cycle_contains.aux1
  {u v w : V}
  (h : G.adj v w)
  (c : G.walk u u)
  (he : (⟨⟦(v, w)⟧, h⟩ : G.edge_set) ∈ c.edges)
  (hb : ∀ (p : G.walk v w), (⟨⟦(v, w)⟧, h⟩ : G.edge_set) ∈ p.edges)
  (hc : c.is_trail)
  (hv : v ∈ c.support)
  (hw : w ∈ (c.split_at_vertex_fst v hv).support) :
  false :=
begin
  let p1 := c.split_at_vertex_fst v hv,
  let p2 := c.split_at_vertex_snd v hv,
  let p11 := p1.split_at_vertex_fst w hw,
  let p12 := p1.split_at_vertex_snd w hw,
  have : (p11.concat p12).concat p2 = c := by simp,
  let q := p2.concat p11,
  have hbq := hb (p2.concat p11),
  have hpq' := hb p12.reverse,
  have this' : multiset.count (⟨⟦(v, w)⟧, h⟩ : G.edge_set) (p2.edges + p11.edges + p12.edges) = 1,
  { convert_to multiset.count (⟨⟦(v, w)⟧, h⟩ : G.edge_set) c.edges = _,
    congr,
    rw ←this,
    simp_rw [walk.concat_edges],
    rw [add_assoc p11.edges, add_comm p12.edges, ←add_assoc],
    congr' 1,
    rw add_comm,
    apply c.trail_count_eq_one hc he, },
  have this'' : multiset.count (⟨⟦(v, w)⟧, h⟩ : G.edge_set) (p2.concat p11).edges + multiset.count (⟨⟦(v, w)⟧, h⟩ : G.edge_set) p12.edges = 1,
  { convert this',
    rw walk.concat_edges,
    symmetry,
    apply multiset.count_add, },
  have hA : multiset.count (⟨⟦(v, w)⟧, h⟩ : G.edge_set) (p2.concat p11).edges = 1,
  { apply walk.trail_count_eq_one,
    have hr := c.rotate_trail hc hv,
    have : c.rotate hv = (p2.concat p11).concat p12,
    { simp [walk.rotate],
      rw ←walk.concat_assoc,
      congr' 1,
      simp, },
    rw this at hr,
    apply walk.is_trail_of_concat_left _ _ hr,
    assumption, },
  have hB : multiset.count (⟨⟦(v, w)⟧, h⟩ : G.edge_set) p12.edges = 1,
  { apply walk.trail_count_eq_one,
    apply walk.is_trail_of_concat_right,
    apply walk.is_trail_of_concat_left,
    rw this,
    exact hc,
    simpa using hpq', },
  rw [hA, hB] at this'',
  simpa using this'',
end

lemma mem_concat_support {u v w : V} (p : G.walk u v) (p' : G.walk v u) (h : w ∈ p.support) :
  w ∈ (p.concat p').support :=
begin
  rw [walk.concat_support, ←multiset.count_pos, multiset.count_sub, multiset.count_add],
  by_cases hwv : w = v,
  { subst w,
    have hp : 0 < multiset.count v p.support := by simp [multiset.count_pos],
    have hp' : 0 < multiset.count v p'.support := by simp [multiset.count_pos],
    simp,
    omega, },
  { simp [hwv],
    have hp : 0 < multiset.count w p.support := by simp [multiset.count_pos, h],
    omega, },
end

lemma is_bridge_iff_no_cycle_contains {v w : V} (h : G.adj v w) :
  G.is_bridge h ↔ ∀ {u : V} (p : G.walk u u), p.is_cycle → (⟨⟦(v, w)⟧, h⟩ : G.edge_set) ∉ p.edges :=
begin
  split,
  { intros hb u c hc he,
    rw is_bridge_iff_walks_contain at hb,
    simp [walk.is_cycle] at hc,
    have hv : v ∈ c.support := walk.edge_vert_mem_support h c he,
    have hh : (⟨⟦(w, v)⟧, G.sym h⟩ : G.edge_set) = ⟨⟦(v, w)⟧, h⟩ := by simp [sym2.eq_swap],
    have hwc : w ∈ c.support := walk.edge_vert_mem_support (G.sym h) c (by { rw hh, exact he, }),
    let p1 := c.split_at_vertex_fst v hv,
    let p2 := c.split_at_vertex_snd v hv,
    by_cases hw : w ∈ p1.support,
    { exact is_bridge_iff_no_cycle_contains.aux1 G h c he hb hc.2.1 hv hw, },
    { have hw' : w ∈ p2.support,
      { have : c = p1.concat p2 := by simp,
        rw [this, walk.concat_support] at hwc,
        simp at hwc,
        rw multiset.mem_erase_of_ne at hwc,
        rw multiset.mem_add at hwc,
        cases hwc,
        { exact (hw hwc).elim },
        { exact hwc },
        exact (G.ne_of_adj h).symm, },
      apply is_bridge_iff_no_cycle_contains.aux1 G (G.sym h) (p2.concat p1)
        (by { rw [walk.concat_edges, add_comm, ←walk.concat_edges, walk.split_at_vertex_spec], rw hh, exact he })
        _ (walk.rotate_trail _ hc.2.1 hv),
      swap,
      { apply mem_concat_support,
        exact hw', },
      { simp, },
      { intro p,
        specialize hb p.reverse,
        rw hh,
        simpa using hb, }, }, },
  { intro hc,
    rw is_bridge_iff_walks_contain,
    intro p,
    by_contra hne,
    specialize hc (walk.cons (G.sym h) p.to_path) _,
    { simp [walk.is_cycle, walk.cons_is_trail_iff],
      split,
      { apply walk.to_path_avoids,
        convert hne using 3,
        rw sym2.eq_swap, },
      { exact p.to_path.property.2, }, },
    simp [-quotient.eq] at hc,
    push_neg at hc,
    apply hc.1,
    rw sym2.eq_swap, },
end

lemma is_acyclic_iff_all_bridges : G.is_acyclic ↔ ∀ {v w : V} (h : G.adj v w), G.is_bridge h :=
begin
  split,
  { intros ha v w hvw,
    rw is_bridge_iff_no_cycle_contains,
    intros u p hp,
    exact (ha _ p hp).elim, },
  { intros hb v p hp,
    cases p,
    { simpa [walk.is_cycle] using hp, },
    { specialize hb p_h,
      rw is_bridge_iff_no_cycle_contains at hb,
      apply hb _ hp,
      simp, }, },
end

lemma unique_path_if_is_acyclic (h : G.is_acyclic) {v w : V} (p q : G.path v w) : p = q :=
begin
  obtain ⟨p, hp⟩ := p,
  obtain ⟨q, hq⟩ := q,
  simp only,
  induction p generalizing q,
  { by_cases hnq : q = walk.nil,
    { subst q, },
    { exfalso,
      cases q,
      exact (hnq rfl).elim,
      simpa [walk.is_path] using hq, }, },
  { rw is_acyclic_iff_all_bridges at h,
    specialize h p_h,
    rw is_bridge_iff_walks_contain at h,
    specialize h (q.concat p_p.reverse),
    simp at h,
    cases h,
    { cases q,
      { exfalso,
        simpa [walk.is_path] using hp, },
      { rw walk.cons_is_path_iff at hp hq,
        simp [walk.edges] at h,
        cases h,
        { cases h,
          { congr,
            exact p_ih hp.1 _ hq.1, },
          { exfalso,
            apply hq.2,
            simp, }, },
        { exfalso,
          apply hq.2 (walk.edge_vert_mem_support _ _ h), }, }, },
    { rw walk.cons_is_path_iff at hp,
      exact (hp.2 (walk.edge_vert_mem_support _ _ h)).elim, }, },
end

lemma is_acyclic_if_unique_path (h : ∀ (v w : V) (p q : G.path v w), p = q) : G.is_acyclic :=
begin
  intros v c hc,
  simp [walk.is_cycle] at hc,
  cases c,
  { exact (hc.1 rfl).elim },
  { simp [walk.cons_is_trail_iff] at hc,
    have hp : c_p.is_path,
    { cases_matching* [_ ∧ _],
      simp only [walk.is_path],
      split; assumption, },
    specialize h _ _ ⟨c_p, hp⟩ (path.singleton (G.sym c_h)),
    simp [path.singleton] at h,
    subst c_p,
    simpa [walk.edges, -quotient.eq, sym2.eq_swap] using hc, },
end

lemma is_acyclic_iff : G.is_acyclic ↔ ∀ (v w : V) (p q : G.path v w), p = q :=
begin
  split,
  { apply unique_path_if_is_acyclic, },
  { apply is_acyclic_if_unique_path, },
end

lemma is_tree_iff : G.is_tree ↔ ∀ (v w : V), ∃!(p : G.walk v w), p.is_path :=
begin
  simp only [is_tree, is_acyclic_iff],
  split,
  { rintro ⟨hc, hu⟩ v w,
    let q := (hc v w).some.to_path,
    use q,
    simp only [true_and, walk.path_is_path],
    intros p hp,
    specialize hu v w ⟨p, hp⟩ q,
    rw ←hu,
    refl, },
  { intro h,
    split,
    { intros v w,
      obtain ⟨p, hp⟩ := h v w,
      use p, },
    { rintros v w ⟨p, hp⟩ ⟨q, hq⟩,
      simp only,
      exact unique_of_exists_unique (h v w) hp hq, }, },
end

/-- Get the unique path between two vertices in the tree. -/
noncomputable abbreviation tree_path (h : G.is_tree) (v w : V) : G.path v w :=
⟨((G.is_tree_iff.mp h) v w).some, ((G.is_tree_iff.mp h) v w).some_spec.1⟩

lemma tree_path_spec {h : G.is_tree} {v w : V} (p : G.path v w) : p = G.tree_path h v w :=
begin
  cases p,
  have := ((G.is_tree_iff.mp h) v w).some_spec,
  simp only [this.2 p_val p_property],
end

/-- The tree metric, which is the length of the path between any two vertices.

Fixing a vertex as the root, then `G.tree_dist h root` gives the depth of each node with
respect to the root. -/
noncomputable def tree_dist (h : G.is_tree) (v w : V) : ℕ :=
walk.length (G.tree_path h v w : G.walk v w)

variables {G} [decidable_eq V]

/-- Given a tree and a choice of root, then we can tell whether a given path
from `v` is a *rootward* path based on whether or not it is a prefix of the unique
path from `v` to the root. This gives paths a canonical orientation in a rooted tree. -/
def path.is_rootward (h : G.is_tree) (root : V) {v w : V} (p : G.path v w) : Prop :=
walk.prefix_of (p : G.walk v w) (G.tree_path h v root : G.walk v root)

lemma path.is_rootward_or_reverse (h : G.is_tree) (root : V) {v w : V} (p : G.path v w) :
  p.is_rootward h root ∨ p.reverse.is_rootward h root :=
begin
  sorry,
end

end

end simple_graph
