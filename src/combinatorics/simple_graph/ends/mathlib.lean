import data.set.finite
import data.sym.sym2
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
import topology.metric_space.basic
import data.setoid.partition

open function
open finset
open set
open classical
open simple_graph.walk
open relation

universes u v w



noncomputable theory

--local attribute [instance] prop_decidable

variables  {V : Type u}
           (G : simple_graph V)
           --[preconnected G]
           --[locally_finite G]
           [decidable_eq V]

namespace simple_graph

lemma walk.mem_support_iff_exists_append  {V : Type u} {G : simple_graph V} {u v w : V} {p : G.walk u v} :
  w ∈ p.support ↔ ∃ (q : G.walk u w) (r : G.walk w v), p = q.append r := sorry

lemma walk.support_append_subset_left {V : Type u} {G : simple_graph V} {u v w : V} (p : G.walk u v) (q : G.walk v w) :
  p.support ⊆ (p.append q).support := by simp only [walk.support_append,list.subset_append_left]

lemma walk.support_append_subset_right {V : Type u} {G : simple_graph V} {u v w : V} (p : G.walk u v) (q : G.walk v w) :
  q.support ⊆ (p.append q).support := by {
    rw walk.support_append,
    induction q,
    {simp only [support_nil, list.tail_cons, list.append_nil, list.cons_subset, end_mem_support, list.nil_subset, and_self],},
    {simp only [support_cons, list.tail_cons, list.cons_subset, list.mem_append, end_mem_support, true_or, list.subset_append_right,and_self],},
  }

end simple_graph


namespace list

-- And this for lists:
lemma to_finset_tail {α : Type u} [decidable_eq α] (l : list α) : l.tail.to_finset ⊆ l.to_finset :=
match l with
| list.nil := by {simp only [list.tail_nil, list.to_finset_nil, finset.empty_subset],}
| list.cons h l := by {simp only [list.tail_cons, list.to_finset_cons], exact finset.subset_insert _ _}
end

lemma to_finset_subset_to_finset {α : Type u} [decidable_eq α] (l₁ l₂ : list α) (h : l₁ ⊆ l₂) : l₁.to_finset ⊆ l₂.to_finset :=
begin
  revert l₂,
  induction l₁,
  { intros l₂ h, simp only [list.to_finset_nil, finset.empty_subset], },
  { intros l₂ h,
    simp at h, cases h,
    simp only [list.to_finset_cons, finset.insert_subset],
    split,
    {
      revert h_left, generalizes [l₁_hd = a, l₂ = l],
      intro h, cases l,
      {simp at h, contradiction,},
      {simp at h ⊢, assumption, }
    },
    {apply l₁_ih, assumption, } }
end

lemma list.map_to_finset {α β : Type*}  [decidable_eq α]  [decidable_eq β] (f : α → β) (l : list α) :
  (l.map f).to_finset = finset.image f l.to_finset :=
list.rec_on l (by {simp}) (λ h t hyp, by {simp,rw hyp,})

end list


namespace simple_graph


lemma transitive_to_good_automs [locally_finite G] [G.preconnected]
  (trans : ∀ u v : V, ∃ φ : G ≃g G, φ u = v)
  (Vinf : (@set.univ V).infinite) :
   ∀ K :finset V, ∃ φ : G ≃g G, disjoint K (finset.image φ K) :=
begin
  sorry
end



lemma conn_adj_conn_to_conn {X Y : set V}
  (Xconn : ∀ x y ∈ X, ∃ w : G.walk x y, (w.support.to_finset : set V) ⊆ X )
  (Yconn : ∀ x y ∈ Y, ∃ w : G.walk x y, (w.support.to_finset : set V) ⊆ Y )
  (XYadj : ∃ (x ∈ X) (y ∈ Y), G.adj x y) :
   ∀ x y ∈ X∪Y, ∃ w : G.walk x y, (w.support.to_finset : set V) ⊆ X∪Y :=
begin
  rintros x xU y yU,
  rcases xU with xX|xY,
  { rcases yU with yX|yY,
    { rcases Xconn x xX y yX with ⟨w,wX⟩, exact ⟨w,wX.trans (set.subset_union_left X Y)⟩},
    { rcases XYadj with ⟨a,aX,b,bY,adj⟩,
      rcases Xconn a aX x xX with ⟨u,uX⟩,
      rcases Yconn b bY y yY with ⟨w,wY⟩,
      use (w.reverse.append (cons adj.symm u)).reverse,
      rw [walk.support_reverse,list.to_finset_reverse,walk.support_append, walk.support_cons,list.tail_cons, list.to_finset_append],
      simp only [support_reverse, list.to_finset_reverse, coe_union, set.union_subset_iff],
      split,
      {exact wY.trans (set.subset_union_right X Y),},
      {exact uX.trans (set.subset_union_left X Y),},},
  },
  { rcases yU with yX|yY,
    { rcases XYadj with ⟨a,aX,b,bY,adj⟩,
      rcases Xconn a aX y yX with ⟨u,uX⟩,
      rcases Yconn b bY x xY with ⟨w,wY⟩,
      use (w.reverse.append (cons adj.symm u)),
      rw [walk.support_append, walk.support_cons,list.tail_cons, list.to_finset_append],
      simp only [support_reverse, list.to_finset_reverse, coe_union, set.union_subset_iff],
      split,
      {exact wY.trans (set.subset_union_right X Y),},
      {exact uX.trans (set.subset_union_left X Y),},},
    { rcases Yconn x xY y yY with ⟨w,wY⟩, exact ⟨w,wY.trans (set.subset_union_right X Y)⟩},
  }
,
end

end simple_graph
