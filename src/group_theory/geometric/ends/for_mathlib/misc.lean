import data.set.finite
import data.sym.sym2
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
import combinatorics.simple_graph.prod
import combinatorics.simple_graph.metric

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

namespace list

-- And this for lists:
@[simp]
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


section

lemma  equiv.of_bijective_trans {α β γ : Type*} {f : α → β} {g : β → γ}
  (hf : function.bijective f) (hg : function.bijective g) :
(equiv.of_bijective f hf).trans (equiv.of_bijective g hg) = equiv.of_bijective (g ∘ f) (function.bijective.comp hg hf) :=
begin
  ext, simp,
end

lemma  equiv.of_bijective_inj {α β γ : Type*} {f : α → β}
  (h₁ h₂ : function.bijective f) :
(equiv.of_bijective f h₁) = (equiv.of_bijective f h₂) :=
begin
  ext, simp,
end

lemma disjoint.preimage' {α β : Type*} {f : α → β} (s : set α) (t : set β) :
  disjoint s (set.preimage f t) → disjoint (f '' s) t :=
begin
  simp only [set.disjoint_iff],
  rintro dis, rintro y ⟨⟨x,⟨a,rfl⟩⟩,b⟩,
  apply dis ⟨a,b⟩,
end

end



namespace simple_graph

variables  {V : Type u} (G : simple_graph V)

lemma walk.split_along_set {V : Type u} {G : simple_graph V} :
∀ {u v : V} (p : G.walk u v) (S : set V) (uS : u ∈ S) (vS : v ∉ S),
  ∃ (x y : V) (w : G.walk u x) (a : G.adj x y) (w' : G.walk y v), p = w.append (cons a w') ∧  (w.support.to_finset : set V) ⊆ S ∧ y ∉ S
| _ _ nil p uS vnS := (vnS uS).elim
| _ _ (cons' u x v a w) S uS vnS := by
{ by_cases h : S x,
  { obtain ⟨x',y,w',a',w'',weq,wS,ynS⟩ := walk.split_along_set w S h vnS,
    use [x',y,cons a w',a',w''],
    split,
    { simp only [cons_append,weq], },
    { simp only [support_cons, list.to_finset_cons, coe_insert,set.insert_subset],
      exact ⟨⟨uS,wS⟩,ynS⟩,}
  },
  { use [u,x,nil,a,w],
    simp only [nil_append, eq_self_iff_true, support_nil, list.to_finset_cons,
      list.to_finset_nil, insert_emptyc_eq, coe_singleton, set.singleton_subset_iff,true_and],
    exact ⟨uS,h⟩, }
}


lemma walk.mem_support_to_exists_append  {V : Type u} {G : simple_graph V} {u v w : V} {p : G.walk u v} (h : w ∈ p.support) :
  ∃ (q : G.walk u w) (r : G.walk w v), p = q.append r :=
match u, v, w, p, h with
| _, _, _, (nil' x), e            := by { simp at e, induction e, use nil, use nil, simp, }
| _, _, _, (cons' x y z a p'), e := by {
  simp at e,
  induction e,
  { rcases e with rfl,
    use nil, simp,
  },
  { rcases _match _ _ _ p' e with ⟨r',q',e'⟩,
    use cons a r', use q',simp only [e', cons_append],},
}
end

lemma walk.mem_support_iff_exists_append  {V : Type u} {G : simple_graph V} {u v w : V} {p : G.walk u v} :
  w ∈ p.support ↔ ∃ (q : G.walk u w) (r : G.walk w v), p = q.append r :=
begin
  split,
  { exact walk.mem_support_to_exists_append },
  { rintros ⟨q,r,rfl⟩,simp only [mem_support_append_iff, end_mem_support, start_mem_support, or_self],},
end

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
∀ (u v : V) (p : G.walk u v) (S : set V) (upred : u ∈ S) (vnpred : v ∉ S),
  ∃ (x y : V), G.adj x y ∧ x ∈ S ∧ y ∉ S
| _ _ nil p up vnp := (vnp up).elim
| _ _ (cons' x y z a q) p up vnp := if h : p y then walk.pred_adj_non_pred y z q p h vnp else ⟨x,y,a,up,h⟩


lemma simple_graph.walk.support_box_prod_left {α : Type*} {β : Type*}
  {G : simple_graph α} (H : simple_graph β) {a₁ a₂ : α} (b : β) (w : G.walk a₁ a₂) :
  (walk.box_prod_left H b w).support = w.support.map (λ x, ⟨x,b⟩) := sorry

lemma simple_graph.walk.support_box_prod_right {α : Type*} {β : Type*}
  (G : simple_graph α) {H : simple_graph β} {b₁ b₂ : β} (a : α)
  (w : H.walk b₁ b₂) : (walk.box_prod_right G a w).support = w.support.map (λ x, ⟨a,x⟩) := sorry



def is_prefix {V : Type*} {G : simple_graph V} : Π {u v w : V} (r : G.walk u w) (p : G.walk u v), Prop
| _ _ _ nil nil := true
| _ _ _ nil (cons _ _) := true
| u v w (cons _ _) nil := false
| u _ _ (cons' x yr v a r') (cons' xp yp w b p') := ∃ (e : yr = yp), @is_prefix yp w v (eq.rec r' e) p'

infix ` ≤w ` : 50 := is_prefix

lemma is_prefix_to_exists_suffix  {V : Type*} {G : simple_graph V} :
  Π {u v w : V} (r : G.walk u w) (p : G.walk u v),  r ≤w p → ∃ q : G.walk w v, r.append q = p
| _ _ _ nil nil := by {rintro _, use nil, simp,}
| _ _ _ nil (cons a p) := by { rintro _, use cons a p, simp,}
| u v w (cons _ _) nil := by {rintro f,unfold is_prefix at f,exfalso,exact f}
| u _ _ (cons' x yr v a r') (cons' xp yp w b p') := by { rintro le, unfold is_prefix at le, rcases le with ⟨rfl,le'⟩, simp at le',rcases is_prefix_to_exists_suffix r' p' le' with ⟨q,rfl⟩,use q,simp,}

lemma is_prefix_of_exists_suffix  {V : Type*} {G : simple_graph V} :
  Π {u v w : V} (r : G.walk u w) (p : G.walk u v),  (∃ q : G.walk w v, r.append q = p) → r ≤w p
| _ _ _ nil nil := by {simp,}
| _ _ _ nil (cons a p) := by {simp,}
| u v w (cons _ _) nil := by {simp,}
| u _ _ (cons' x yr v a r') (cons' xp yp w b p') := by { rintros ⟨q,qeq⟩,
  induction qeq,
  rcases is_prefix_of_exists_suffix r' (r'.append q) ⟨q,rfl⟩ with le,
  exact ⟨rfl,le⟩,
  }

lemma is_prefix.nil  {V : Type*} {G : simple_graph V} :
  Π {u w : V} (r : G.walk u w), nil ≤w r
| _ _ nil := trivial
| _ _ (cons _ _) := trivial


lemma is_prefix.refl  {V : Type*} {G : simple_graph V} :
  Π {u w : V} (r : G.walk u w), r ≤w r
| _ _ nil := trivial
| _ _ (cons' x y z a p) := ⟨rfl,is_prefix.refl p⟩

lemma is_prefix.rfl  {V : Type*} {G : simple_graph V} :
  Π {u w : V} {r : G.walk u w}, r ≤w r := λ u w r, is_prefix.refl r

lemma is_prefix.trans  {V : Type*} {G : simple_graph V} :
  Π {u v w z : V} {r : G.walk u v} {p : G.walk u w} {q : G.walk u z}, r ≤w p → p ≤w q → r ≤w q
| _ _ _ _ nil nil nil e f := trivial
| _ _ _ _ nil nil (cons _ _) e f := trivial
| _ _ _ _ nil (cons _ _) nil e f := f.elim
| _ _ _ _ nil (cons _ _) (cons _ _) e f := trivial
| _ _ _ _ (cons _ _) nil nil e f := e.elim
| _ _ _ _ (cons _ _) nil (cons _ _) e f := e.elim
| _ _ _ _ (cons _ _) (cons _ _) nil e f := f.elim
| _ _ _ _ (cons' xr yr zr ar r) (cons' xp yp zp ap p) (cons' xq yq zq aq q) e f := by {
   rcases e with ⟨rfl,e'⟩,
   rcases f with ⟨rfl,f'⟩,
   refine ⟨rfl,_⟩,
   --squeeze_simp,
   --simp at e',
   --simp at f',
   exact is_prefix.trans e' f',}

def is_prefix.eq_nil_of_nil  {V : Type*} {G : simple_graph V} :
  Π {u v : V} {r : G.walk u v} (pfx : r ≤w nil), ∃ (e : v = u), @eq.rec V v (λ x, G.walk u x) r u e = nil' u
| _ _ (nil' u) pfx := ⟨rfl,rfl⟩
| _ _ (cons' u v w a r) pfx := pfx.elim

-- Don't kill my darlings :'(
noncomputable def longest_prefix_all {V : Type*} {G : simple_graph V} :
Π {u v: V} (p : G.walk u v) (pred : ∀ (z : V) (q : G.walk u z), q ≤w p → Prop) ,
psum
  { R : Σ (z : V), G.walk u z | ∃ (pfxR : R.2 ≤w p) (predR : pred R.1 R.2 pfxR),
                                ∀ z (q : G.walk u z) (pfxq : q ≤w p), pred z q pfxq → q ≤w R.2 }
  (∀ (z : V) (q : G.walk u z) (pfx : q ≤w p), ¬ pred z q pfx)
| _ _ (nil' x) pred := by {
  simp only [exists_prop, exists_and_distrib_right, coe_set_of] at *,
  by_cases h : pred x (nil' x) (is_prefix.rfl),
  { left,
    use [x,is_prefix.rfl,h],
    rintros z q pfx hh,
    exact pfx,},
  { right,
    rintros z q pfx,
    rcases is_prefix.eq_nil_of_nil pfx with ⟨rfl,eq'⟩,
    induction eq',
    exact h,}
  }
| _ _ (cons' x y z a p) pred := by {
  let pred' :  ∀ (w : V) (q : G.walk y w), q ≤w p → Prop
            := λ w q pfx, pred w (cons' x y w a q) (by { refine ⟨rfl,_⟩, exact pfx,}), -- why need to refine
  rcases longest_prefix_all p pred' with ⟨⟨t,r⟩,good⟩|bad,
  { left,
    use ⟨t,cons a r⟩,
    rcases good with ⟨pfxr,predr,maxr⟩, -- Can only split here since otherwise we're not in a Prop yet
    use [⟨rfl,pfxr⟩,predr],
    rintros z q pfxq predq ,
    cases q,
    { simp only, },
    { rcases pfxq with ⟨rfl,pfxq'⟩,
      exact ⟨rfl,maxr _ _ pfxq' predq⟩,},
  },
  { by_cases h : pred x nil (is_prefix.nil (cons a p)),
    { left,
      use [⟨x,nil⟩,is_prefix.nil (cons a p),h],
      rintros z q pfxq predq,
      cases q,
      { simp only, },
      { rcases pfxq with ⟨rfl,pfxq'⟩, exact (bad z q_p pfxq' predq).elim,},},
    { right, rintro z q pfxq,
      cases q,
      { exact h, },
      { rcases pfxq with ⟨rfl,pfxq'⟩, exact bad _ q_p pfxq',},},
  },
}


def thicken  {V : Type*} (G : simple_graph V) (K : set V) :
  set V := K ∪ {v : V | ∃ k : K, G.adj k v}

lemma thicken.finite {V : Type*} (G : simple_graph V) [Glf : G.locally_finite]  (K : finset V) :
  (thicken G K).finite :=
begin
  have : G.thicken K = K ∪ (set.Union (λ x : K, G.neighbor_set x)), by {
    simp only [thicken,neighbor_set], apply congr_arg _,
    ext, rw mem_Union, simp only [mem_set_of_eq], refl,},
  rw this,
  apply set.finite_union.mpr, split, exact set.to_finite K,
  haveI : finite (↥K), by {apply finite_coe_iff.mpr, exact to_finite K,},
  apply set.finite_Union, rintro ⟨x,xk⟩,
  apply set.finite_def.mpr, constructor, exact Glf x,
end

lemma thicken.of_all_adj {V : Type*} (G : simple_graph V) (K : set V) (Kadj : ∀ k ∈ K, ∃ k' ∈ K, G.adj k k') : thicken G K = {v : V | ∃ k ∈ K, G.adj v k} :=
begin
  unfold thicken,
  ext,
  split,
  {
    intro h,
    cases h,
    { exact Kadj _ h,},
    -- tidy
    { cases h, cases h_w, dsimp at *, simp at *, fsplit, work_on_goal 2 { fsplit, work_on_goal 1 { assumption }, solve_by_elim }},
  },
  { intro h, right,
    -- tidy
    {cases h, cases h_h, dsimp at *, simp at *, fsplit, work_on_goal 2 { fsplit, work_on_goal 1 { assumption }, solve_by_elim }}}
end

lemma thicken.of_connected {V : Type*} (G : simple_graph V) (K : set V) (Kconn : (G.induce K).connected) : thicken G K = {v : V | ∃ k ∈ K, G.adj v k} :=
begin
  refine thicken.of_all_adj G K _,
  intros k hkK,
  cases Kconn,
  apply Kconn_nonempty.elim,
  rintro k',
  let p := (Kconn_preconnected ⟨k, hkK⟩ k').some,
  sorry,
end

--mathlib (it seems mathlib only has this for subgraph with subset of vertices ?)
def is_subgraph.hom {G G' : simple_graph V} (h : G ≤ G') : G →g G' := ⟨id, h⟩

-- not really needed, but anyway
lemma transitive_to_good_automs [locally_finite G] [G.preconnected]
  (trans : ∀ u v : V, ∃ φ : G ≃g G, φ u = v)
  (Vinf : (@set.univ V).infinite) :
   ∀ K :finset V, ∃ φ : G ≃g G, disjoint K (finset.image φ K) :=
begin
  sorry
end





-- This should all be srteamlined: balls are the same thing as `thicken_` which is a generalization
-- of `thicken`, but it would be better to use definitions from `metric_space` instead of rolling
-- our own

def ball (v : V) (m : ℕ) := {u : V | G.dist v u ≤ m}

lemma balls_zero (Gc : G.connected) (v : V) :
  G.ball v 0 = {v} := by
{ unfold ball,
  simp only [le_zero_iff, connected.dist_eq_zero_iff Gc,set_of_eq_eq_singleton'], }

-- Not the right approach it feels
lemma balls_succ (Gc : G.connected) (v : V) (m : ℕ) :
  G.ball v (m+1) = G.ball v m ∪ (⋃ w ∈ G.ball v m, G.neighbor_set w) := by
{ unfold ball,
  ext u, split,
  { rintro xms,
    simp at xms,
    obtain ⟨p,plen⟩ := connected.exists_walk_of_dist Gc v u,
    cases p,
    {simp at plen, left, simp, sorry,},
    {rw walk.length_cons at plen,sorry,},},
  { rintro xU,sorry},
}

lemma finite_balls (Gpc : G.preconnected) (Glf : G.locally_finite) (v : V) (m : ℕ) :
  set.finite (G.ball v m) :=
begin
  have : G.connected, by {rw connected_iff, use Gpc, use ⟨v⟩,},
  induction m,
  { rw simple_graph.balls_zero G this v, simp only [finite_singleton],  },
  { rw simple_graph.balls_succ G this v m_n,
    apply set.finite.union,
    apply m_ih,
    apply set.finite.bUnion,
    apply m_ih,
    rintro w hw,
    exact (neighbor_set G w).to_finite,
  }
end

def thicken_ (G : simple_graph V) (K : finset V) (m : ℕ) : finset V :=
begin
  let K'set := {v : V | ∃ k ∈ K, G.dist v k ≤ m},
  have : K'set.finite := sorry, -- locally finite TODO: WIP approach above
  exact this.to_finset,
end

lemma thicken_.sub (G : simple_graph V) (K : finset V) (m : ℕ) :
  K ⊆ thicken_ G K m :=
begin
  rintro k kK,
  dsimp [thicken_],
  simp only [finite.mem_to_finset, mem_set_of_eq, exists_prop],
  use k, split, exact kK,
  have : G.dist k k = 0 := by sorry {exact dist_self _},
  rw this,
  apply zero_le,
end

lemma thicken_.eq (G : simple_graph V) (K : finset V) (m : ℕ) :
  (thicken_ G K m : set V) = {v : V | ∃ k ∈ K, G.dist v k ≤ m} := sorry


end simple_graph


-- necessary lemma
--mathlib
lemma sInter_of_directed_nonempty {α : Type*} [fintype α] [nonempty α] (S : set (set α))
  (allsnempty : ∀ s ∈ S, set.nonempty s) (dir : directed_on (⊇) S) : set.nonempty (S.sInter) :=
begin

  let mcard : set α → ℕ := λs,  fintype.card s,

  by_cases Snempty : S.nonempty,
  { let s₀ := function.argmin_on (mcard) (nat.lt_wf) S Snempty,
    let hs₀ := function.argmin_on_mem (mcard) (nat.lt_wf) S Snempty,
    suffices : s₀ = S.sInter,
    { rw ←this,
      exact allsnempty s₀ hs₀,},
    apply set.ext,
    rintro x,
    split,
    { rintro xs₀,
      rintro s hs,
      rcases dir s₀ hs₀ s hs with ⟨t,ht,ts₀,ts⟩,
      suffices : t = s₀,
      { rw this at ts,
        exact ts xs₀,},
      have : mcard s₀ ≤ mcard t, from function.argmin_on_le (mcard) (nat.lt_wf) S ht,
      exact set.eq_of_subset_of_card_le ts₀ this, },
    { rintro xI, exact set.mem_sInter.mp xI s₀ hs₀, },},
  { rw set.not_nonempty_iff_eq_empty at Snempty,
    simp only [Snempty, set.sInter_empty, set.univ_nonempty],},
end
