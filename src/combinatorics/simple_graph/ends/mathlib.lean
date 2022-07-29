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
local attribute [instance] prop_decidable
-- to make every proposition decidable

variables  {V : Type u}
           (G : simple_graph V)
           --[preconnected G]
           --[locally_finite G]

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


lemma walk.pred_adj_non_pred {V : Type u} {G : simple_graph V} :
∀ (u v : V) (p : G.walk u v) (pred : V → Prop) (upred : pred u) (vnpred : ¬ pred v),
  ∃ (x y : V), G.adj x y ∧ pred x ∧ ¬ pred y
| _ _ nil p up vnp := (vnp up).elim
| _ _ (cons' x y z a q) p up vnp := if h : p y then walk.pred_adj_non_pred y z q p h vnp else ⟨x,y,a,up,h⟩

/-
def is_prefix {V : Type*} {G : simple_graph V} {u v w : V} (r : G.walk u w) (p : G.walk u v) :=
  ∃ q : G.walk w v, p = r.append q

infix ` ≤w ` : 50 := is_prefix

def longest_prefix {V : Type*} {G : simple_graph V}
  {u v w : V} {p : G.walk u v} {r : G.walk u w} (pre : r ≤w p)
  (pred : ∀ (z : V) (q : G.walk u z), q ≤w p → Prop) (pred_r : pred w r pre) : (Σ (z : V), G.walk u z) := sorry

def longest_prefix.prefix {V : Type*} {G : simple_graph V}
  {u v w : V} {p : G.walk u v} {r : G.walk u w} (pre : r ≤w p)
  (pred : ∀ (z : V) (q : G.walk u z), q ≤w p → Prop) (pred_r : pred w r pre) :
  (longest_prefix pre pred pred_r).2 ≤w p

def longest_prefix.spec {V : Type*} {G : simple_graph V}
  {u v w : V} {p : G.walk u v} {r : G.walk u w} (pre : r ≤w p)
  (pred : ∀ (z : V) (q : G.walk u z), q ≤w p → Prop) (pred_r : pred w r pre) := sorry

def longest_prefix.longest {V : Type*} {G : simple_graph V}
  {u v w : V} {p : G.walk u v} {r : G.walk u w} (pre : r ≤w p)
  (pred : ∀ (z : V) (q : G.walk u z), q ≤w p → Prop) (pred_r : pred w r pre) :
  ∀ (z : V) (q : G.walk u z) (preq : q ≤w p), pred z q preq → q ≤w (longest_prefix pre pred pred_r).2 := sorry
-/

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

lemma map_to_finset {α β : Type*}  [decidable_eq α]  [decidable_eq β] (f : α → β) (l : list α) :
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

-- This should be made compatible with the `simple_graph` API but for now we leave it aside
def subconnected (X : set V) := ∀ x y ∈ X, ∃ w : G.walk x y, ↑w.support.to_finset ⊆ X

lemma subconnected.of_adj_pair (x y : V) (e : G.adj x y) : subconnected G {x,y} :=
begin
  rintros a ain b bin,
  rcases ain with ⟨x,rfl⟩|⟨y,rfl⟩,
  { rcases bin with ⟨x,rfl⟩|⟨y,rfl⟩,
    { use walk.nil,simp,},
    { use walk.cons e (walk.nil), simp,},
  },
  { rcases bin with ⟨x,rfl⟩|⟨y,rfl⟩,
    { use walk.cons e.symm (walk.nil), rw [←list.to_finset_reverse,←walk.support_reverse],simp,},
    { use walk.nil,simp,},
  }
end

lemma subconnected.of_intersecting_subconnected {X Y : set V}
  (hX : subconnected G X )
  (hY : subconnected G Y )
  (hXY : ¬ disjoint X Y) : subconnected G (X∪Y) :=
begin
  rcases set.not_disjoint_iff.mp hXY with ⟨p,pX,pY⟩,
  rintros a aZ b bZ,
  rcases aZ with aX|aY,
  { rcases bZ with bX|bY,
    { rcases hX a aX b bX with ⟨w,wX⟩,
      exact ⟨w,wX.trans (set.subset_union_left X Y)⟩,},
    { rcases hX a aX p pX with ⟨w,wX⟩,
      rcases hY p pY b bY with ⟨u,uY⟩,
      use w.append u,
      rw [walk.support_append, list.to_finset_append,finset.coe_union],
      apply set.union_subset_union wX (set.subset.trans _ uY),
      apply list.to_finset_tail,
    },
  },
  { rcases bZ with bX|bY,
    { rcases hY a aY p pY with ⟨u,uY⟩,
      rcases hX p pX b bX with ⟨w,wX⟩,
      use u.append w,
      rw [walk.support_append, list.to_finset_append,finset.coe_union,set.union_comm],
      apply set.union_subset_union (set.subset.trans _ wX) uY,
      apply list.to_finset_tail,
    },
    { rcases hY a aY b bY with ⟨w,wY⟩,
      exact ⟨w,wY.trans (set.subset_union_right X Y)⟩,},
  },
end

lemma subconnected.of_adj_subconnected {X Y : set V}
  (hX : subconnected G X )
  (hY : subconnected G Y )
  (XYadj : ∃ (x ∈ X) (y ∈ Y), G.adj x y) : subconnected G (X∪Y) :=
begin
  rcases XYadj with ⟨x,xX,y,yY,e⟩,
  let E : set V := {x,y},
  have : X∪Y = (E ∪ X) ∪ Y, by { simp *,sorry}, -- too lazy now
  rw this,
  apply subconnected.of_intersecting_subconnected,
  { apply subconnected.of_intersecting_subconnected,
    { exact subconnected.of_adj_pair G x y e, },
    { exact hX, },
    { exact set.not_disjoint_iff.mpr ⟨x,by simp,xX⟩},
  },
  { exact hY,},
  { exact set.not_disjoint_iff.mpr ⟨y,by simp,yY⟩}

end

lemma subconnected.image {U : Type*} (H : simple_graph U) (φ : G →g H)
  {X : finset V} (hX : subconnected G X) : (subconnected H (finset.image φ X)) :=
begin
    rintros φx xφ φy yφ,
    simp at xφ,
    simp at yφ,
    rcases xφ with ⟨x,⟨xK,rfl⟩⟩,
    rcases yφ with ⟨y,⟨yK,rfl⟩⟩,
    rcases hX x xK y yK with ⟨w,wgood⟩,
    rw finset.coe_subset at wgood,
    let φw := w.map φ,
    use φw,
    rw [walk.support_map,list.map_to_finset,finset.coe_subset],
    apply finset.image_subset_image wgood,
end

lemma subconnected.of_walk {x y : V} (w : G.walk x y) : subconnected G w.support.to_finset :=
begin
  rintros a ah b bh,
  simp at ah,
  simp at bh,
  rcases walk.mem_support_iff_exists_append.mp ah with ⟨wa,wa',eqa⟩,
  rcases walk.mem_support_iff_exists_append.mp bh with ⟨wb,wb',eqb⟩,
  use wa.reverse.append wb,
  simp,
  rw walk.support_append,
  rw list.to_finset_append,
  rw walk.support_reverse,
  rw list.to_finset_reverse,
  apply finset.union_subset,
  { rw eqa, apply list.to_finset_subset_to_finset, apply walk.support_append_subset_left,},
  { rw eqb,
    apply (list.to_finset_tail wb.support).trans _,
    apply list.to_finset_subset_to_finset,
    exact walk.support_append_subset_left wb wb',},
end

lemma subconnected.of_common_mem_sUnion (v : V) {F : set (set V)}
  (mem : ∀ S ∈ F, v ∈ S) (subconn : ∀ S ∈ F, subconnected G S) : subconnected G (⋃₀ F) :=
begin
  rintros x xh y yh,
  rcases xh with ⟨S,SF,xS⟩,
  rcases yh with ⟨T,TF,yT⟩,
  rcases subconnected.of_intersecting_subconnected G
         (subconn S SF)
         (subconn T TF)
         (set.not_disjoint_iff.mpr ⟨v,⟨mem S SF,mem T TF⟩⟩)
         x (by {simp *,})
         y (by {simp *,})
  with ⟨w,wgood⟩,
  use w,
  have : S ∪ T ⊆ ⋃₀ F, by {simp,exact ⟨subset_sUnion_of_mem SF,subset_sUnion_of_mem TF⟩},
  exact wgood.trans this,
end




end simple_graph
