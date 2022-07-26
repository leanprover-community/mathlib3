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

namespace simple_graph


variables  {V : Type u}
           (G : simple_graph V)
           --[preconnected G]
           --[locally_finite G]
           [decidable_eq V]


def connected_outside (K : finset V) (x y : V) : Prop :=
  ∃ w : walk G x y, disjoint (K : finset V) w.support.to_finset

namespace connected_outside

def c_o := connected_outside G

lemma monotone {K K' : finset V} (hK : K ⊆ K') (x y : V) :
  c_o G K' x y → c_o G K x y :=
λ ⟨w,dis⟩, ⟨w,disjoint_of_subset_left hK dis⟩

lemma not_in {K : finset V} {x y : V} (conn : c_o G K x y) : x ∉ K ∧ y ∉ K  :=
begin
  rcases conn with ⟨xy, dis⟩,
  have x_in : x ∈ ↑(xy.support.to_finset),
    by {rw [mem_coe, list.mem_to_finset], apply walk.start_mem_support},
  have y_in : y ∈ ↑(xy.support.to_finset),
    by {rw [mem_coe, list.mem_to_finset], apply walk.end_mem_support},
  exact ⟨finset.disjoint_right.mp dis x_in,finset.disjoint_right.mp dis y_in⟩,
end

@[protected]
lemma refl {K : finset V} (x : V) (hx : x ∉ K) : c_o G K x x :=
⟨walk.nil, by { rw [walk.support_nil,list.to_finset_cons,list.to_finset_nil],simpa only [insert_emptyc_eq, coe_singleton, finset.disjoint_singleton_right],}⟩

lemma of_adj_outside (K : finset V) (x y : V) (hx : x ∉ K) (hy : y ∉ K) :
  G.adj x y → c_o G K x y :=
begin
  intro a,
  use (walk.cons a walk.nil),
  rw [walk.support_cons,walk.support_nil,list.to_finset_cons,list.to_finset_cons,list.to_finset_nil],
  simp only [insert_emptyc_eq, coe_insert, coe_singleton],
  rw [finset.disjoint_iff_inter_eq_empty,
      finset.inter_comm,
      finset.insert_inter_of_not_mem hx,
      finset.singleton_inter_of_not_mem hy],
end

@[protected]
lemma symm  {K : finset V} : symmetric (c_o G K) :=
λ x y, λ ⟨w,dis⟩, ⟨w.reverse, by {rw [walk.support_reverse,list.to_finset_reverse],exact dis}⟩

@[protected]
lemma trans {K : finset V} : transitive (c_o G K)
| x y z ⟨xy,disxy⟩ ⟨yz,disyz⟩ :=
begin
  use xy.append yz,
  rw walk.support_append,
  rw list.to_finset_append,
  simp only [coe_union, finset.disjoint_union_right],
  refine ⟨disxy,_⟩,
  { have : ↑(yz.support.tail.to_finset) ⊆ ↑(yz.support.to_finset), by
    { rw walk.support_eq_cons, simp, rw finset.coe_insert, exact set.subset_insert y (↑(yz.support.tail.to_finset)),},
    exact @finset.disjoint_of_subset_right V _ K yz.support.tail.to_finset yz.support.to_finset this disyz}
end


end connected_outside









open simple_graph.connected_outside

def components (K : finset V) : set (set V) := {C : set V | ∃ x ∈ C, C = {y : V | c_o G K x y}}

namespace component

variable (K : finset V)

def of (x : V) : (set V) := {y : V | c_o G K x y}

lemma of_in_components (x : V) (hx : x ∉ K) : of G K x ∈ components G K :=
⟨x,connected_outside.refl G x hx,rfl⟩

lemma mem_of (x : V) (hx : x ∉ K) : x ∈ (of G K x) := connected_outside.refl G x hx

lemma nempty (C : set V) : C ∈ components G K → set.nonempty C
| ⟨x,x_in_C,sat⟩ := ⟨x,x_in_C⟩

lemma is_c_o (C : set V) : C ∈ components G K →  ∀ x y ∈ C, c_o G K x y
| ⟨z,z_in,eq⟩ x x_in y y_in :=
begin
  rw eq at x_in y_in,
  exact connected_outside.trans G (connected_outside.symm G x_in) y_in,
end

lemma not_in_of_in_comp (C : set V) (hC : C ∈ components G K) (x : V) (hx : x ∈ C) : x ∉ K :=
(not_in G (is_c_o G K C hC x hx x hx)).1

lemma conn_sub (P : set V)
  (Pnempty : set.nonempty P) (P_c_o : ∀ x y ∈ P, c_o G K x y) :
  ∃ C : set V, C ∈ components G K ∧ P ⊆ C :=
begin
  rcases Pnempty with ⟨p,p_in_P⟩,
  have p_notin_K : p ∉ K := (not_in G (P_c_o p p_in_P p p_in_P)).1,
  let p_in_Cp := mem_of G K p p_notin_K,
  use [of G K p, of_in_components G K p p_notin_K],
  rw set.subset_def,
  exact λ x x_in_P, P_c_o p p_in_P x x_in_P,
end


-- This one could probably use `conn_sub` but I'm too lazy/stupid to figure the neatest way to do things
lemma eq_of_common_mem (C D : set V) (hC : C ∈ components G K) (hD : D ∈ components G K)
  (x : V) (x_in_C : x ∈ C) (x_in_D : x ∈ D) : C = D :=
begin
  rcases hC with ⟨y,y_in_C,rfl⟩,
  rcases hD with ⟨z,z_in_D,rfl⟩,
  apply set.ext,
  intro w,
  have y_c_o_z : c_o G K y z, from connected_outside.trans G x_in_C (connected_outside.symm G x_in_D),
  split,
  from λ w_in_C, connected_outside.trans G (connected_outside.symm G y_c_o_z) w_in_C,
  from λ w_in_D, connected_outside.trans G y_c_o_z w_in_D,
end

lemma mem_of_mem_of_conn (C : set V) (hC : C ∈ components G K)
  (x y : V) (x_in_C : x ∈ C) (x_conn_y : c_o G K x y) : y ∈ C :=
begin
  rcases hC with ⟨c,c_in_C,rfl⟩,
  exact connected_outside.trans G x_in_C x_conn_y,
end

lemma mem_of_mem_of_adj (C : set V) (hC : C ∈ components G K)
  (x y : V) (x_in_C : x ∈ C) (y_notin_K : y ∉ K) (adj : G.adj x y) : y ∈ C :=
mem_of_mem_of_conn G K C hC x y x_in_C $ of_adj_outside G K x y (not_in_of_in_comp G K C hC x x_in_C) y_notin_K adj

lemma eq_of_adj_mem
  (C : set V) (hC : C ∈ components G K)
  (D : set V) (hD : D ∈ components G K)
  (x y : V) (x_in_C : x ∈ C) (y_in_D : y ∈ D) (adj : G.adj x y) : C = D :=
begin
  have y_in_C : y ∈ C, from mem_of_mem_of_adj G K C hC x y x_in_C (not_in_of_in_comp G K D hD y y_in_D) adj,
  exact (eq_of_common_mem G K C D hC hD y y_in_C y_in_D),
end



lemma conn_sub_unique (P : set V)
  (Pnempty : set.nonempty P) (P_c_o : ∀ x y ∈ P, c_o G K x y) : ∃! C : set V, C ∈ components G K ∧ P ⊆ C :=
begin
  rcases conn_sub G K P Pnempty P_c_o with ⟨C,⟨C_comp,P_sub_C⟩⟩,
  use C,
  split,
  exact ⟨C_comp,P_sub_C⟩,
  rintros D ⟨D_comp,P_sub_D⟩,
  rcases Pnempty with ⟨p,p_in_P⟩,
  exact (eq_of_common_mem G K C D C_comp D_comp p (P_sub_C p_in_P) (P_sub_D p_in_P)).symm,
end

lemma sub_of_conn_intersects
  (P : set V) (Pnempty : set.nonempty P) (P_c_o : ∀ x y ∈ P, c_o G K x y)
  (C ∈ components G K) (inter : (P ∩ C).nonempty) : P ⊆ C :=
begin
  sorry -- todo
end

lemma walk_outside_is_contained (C : set V) (hC : C ∈ components G K) :
  Π (x y : V), Π (w : G.walk x y), x ∈ C → y ∈ C → disjoint K w.support.to_finset → (w.support.to_finset : set V) ⊆ C
| x _ nil             hx hy _  := by {simp only [support_nil, list.to_finset_cons, list.to_finset_nil, insert_emptyc_eq, coe_singleton, set.singleton_subset_iff],exact hx}
| x y (@cons V G _ z _ adj tail) hx hy hw := by {
  rw [walk.support,list.to_finset_cons],
  simp only [coe_insert],
  rw set.insert_subset,
  split,
  exact hx,
  have : z ∈ (cons adj tail).support.to_finset, by simp only [support_cons, list.to_finset_cons, finset.mem_insert, list.mem_to_finset, start_mem_support, or_true],
  have : z ∉ K, from finset.disjoint_right.mp hw this,
  have : z ∈ C, from mem_of_mem_of_adj G K C hC x z hx ‹z∉K› adj,
  have : disjoint K tail.support.to_finset, {
    apply finset.disjoint_of_subset_right _ hw,
    simp only [support_cons, list.to_finset_cons, coe_insert, finset.subset_insert],
  },
  exact walk_outside_is_contained z y tail ‹z∈C› hy this,
}


lemma is_connected (C : set V) (hC : C ∈ components G K) (x : V) (hx : x ∈ C) (y : V) (hy : y ∈ C) :
  ∃ w : G.walk x y, (w.support.to_finset : set V) ⊆ C :=
begin
  rcases is_c_o G K C hC x hx y hy with ⟨w,dis_K⟩,
  exact ⟨w,walk_outside_is_contained G K C hC x y w hx hy dis_K⟩,
end

lemma c_o_of_connected_disjoint  (P : set V)
  (dis : disjoint P K)
  (conn : ∀ x y ∈ P, ∃ w : G.walk x y, (w.support.to_finset : set V) ⊆ P) : ∀ x y ∈ P, c_o G K x y :=
begin
  rintros x hx y hy,
  unfold c_o,
  unfold connected_outside,
  rcases conn x hx y hy with ⟨w,wgood⟩,
  use w,
  exact disjoint_coe.mp (set.disjoint_of_subset_left wgood dis).symm,
end

lemma conn_sub_of_connected_disjoint (P : set V)
  (Pnempty : set.nonempty P)
  (dis : disjoint P K)
  (conn : ∀ x y ∈ P, ∃ w : G.walk x y, (w.support.to_finset : set V) ⊆ P) :
  ∃ C : set V, C ∈ components G K ∧ P ⊆ C :=
conn_sub G K P Pnempty (component.c_o_of_connected_disjoint G K P dis conn)


--only used in next lemma
private def walks (C : set V) (k : V) := Σ (x : C), G.walk x k
private def w_len  (C : set V) (k : V) :  walks G C k → ℕ := λ w, w.2.length
private def w_min (C : set V) (k : V) := @function.argmin _ _ (w_len G C k) _ nat.lt_wf
private def w_min_spec (C : set V) (k : V) := @function.argmin_le _ _ (w_len G C k) _ nat.lt_wf

lemma adjacent_to (Knempty: K.nonempty) (C : set V) (hC : C ∈ components G K) :
∃ (v k : V), k ∈ K ∧ v ∈ C ∧ G.adj k v :=
begin
  rcases Knempty with ⟨k,k_in_K⟩,
  have nemptywalks : nonempty (walks G C k), by {
    rcases nempty G K C hC with ⟨x,x_in_C⟩,
    have w : G.walk x k := sorry, -- it's in the hypotheses!!
    exact nonempty.intro ⟨⟨x,x_in_C⟩,w⟩,},
  rcases hhh : @w_min V G _ C k nemptywalks with ⟨x, min_walk⟩,
  have x_notin_K : x.val ∉ K, from (not_in G (is_c_o G K C hC x.val x.prop x.val x.prop)).1,
  rcases min_walk with nil|⟨_,y,_,x_adj_y,y_walk_k⟩,
  { exfalso,
    have : c_o G K x x, from is_c_o G K C hC x.val x.prop x.val x.prop,
    exact x_notin_K k_in_K,},
  { by_cases h : y ∈ K,
    { use x, use y, use h, use x.prop, exact (x_adj_y).symm,},
    { have : c_o G K x y, from connected_outside.of_adj_outside G K x y x_notin_K h x_adj_y,
      have : y ∈ C, from mem_of_mem_of_conn G K C hC x.val y x.prop this,
      let subwalk : walks G C k := ⟨⟨y,this⟩,y_walk_k⟩,
      have min_is_min := @w_min_spec V G _  C k subwalk (nemptywalks),
      have len_subwalk : (w_len G C k subwalk) + 1 = w_len G C k (@w_min V G _  C k nemptywalks), by {
        unfold w_len at *,
        rw [hhh,←simple_graph.walk.length_cons],
      },
      have : (w_len G C k subwalk) < (w_len G C k subwalk) + 1, from lt_add_one (w_len G C k subwalk),
      rw len_subwalk at this,
      exfalso,
      haveI : nonempty (walks G C k), by sorry,
      have ok : argmin (w_len G C k) nat.lt_wf = w_min G C k, by simpa, -- can I do this without simpa?
      rw ok at min_is_min,
      exact (lt_iff_not_ge _ _).mp this min_is_min,},}
end

def bdry : set V := {x : V | x ∉ K ∧ ∃ k ∈ K, G.adj x k}
lemma bdry_subset_union_neighbors : (bdry G K: set V) ⊆ set.Union (λ x : K, G.neighbor_set x) :=
begin
  unfold bdry,
  rw set.subset_def,
  rintros x ⟨not_in_K,k,k_in_K,adj⟩,
  rw set.mem_Union,
  exact ⟨⟨k,k_in_K⟩,adj.symm⟩,
end

lemma bdry_finite [locally_finite G] : (bdry G K).finite :=
begin
  apply set.finite.subset _ (bdry_subset_union_neighbors G K),
  apply set.finite.sUnion,
  apply set.finite_range,
  rintros nbd ⟨k,k_to_nbd⟩,
  simp only at k_to_nbd,
  rw k_to_nbd.symm,
  exact (neighbor_set G ↑k).to_finite, -- lol thanks library_search
end

def to_bdry_point (Knempty: K.nonempty) : components G K → V :=
λ C, some $ adjacent_to G K Knempty C.val C.prop

def to_bdry_point_spec (Knempty: K.nonempty) (C : components G K) :
  let v := (to_bdry_point G K Knempty C) in ∃ k : V, k ∈ K ∧ v ∈ C.val ∧ G.adj k v :=
some_spec (adjacent_to G K Knempty C.val C.prop)

lemma to_bdry_point_inj (Knempty: K.nonempty) :
  function.injective $ to_bdry_point G K Knempty :=
begin
  rintros C D c_eq_d,
  rcases to_bdry_point_spec G K Knempty C with ⟨k,kK,cC,k_adj_c⟩,
  rcases to_bdry_point_spec G K Knempty D with ⟨l,lK,dD,l_adj_d⟩,
  exact subtype.eq ( eq_of_common_mem G K C.val D.val C.prop D.prop _ cC (c_eq_d.symm ▸ dD)),
end

lemma to_bdry_point_in_bdry  (Knempty: K.nonempty) :
  range (to_bdry_point G K Knempty) ⊆ bdry G K :=
begin
  rw set.subset_def,
  rintros _ ⟨C,rfl⟩,
  rcases to_bdry_point_spec G K Knempty C with ⟨k,kK,cC,k_adj_c⟩,
  have := not_in_of_in_comp G K C.val C.prop _ cC,
  exact ⟨this,⟨k,⟨kK,k_adj_c.symm⟩⟩⟩,
end

lemma finite [locally_finite G] : (components G K).finite :=
begin
  by_cases Knempty : K.nonempty,
  { by_contra comps_inf,
    haveI : infinite (subtype (components G K)), from infinite_coe_iff.mpr comps_inf,
    have := @set.infinite_range_of_injective (subtype (components G K)) V (_inst) (to_bdry_point G K Knempty) (to_bdry_point_inj G K Knempty),
    have : (bdry G K).infinite, from set.infinite.mono (to_bdry_point_in_bdry G K Knempty) this,
    exact this (bdry_finite G K),},
  { sorry,}
  -- If K is not nonempty, it is empty. This means, since G is assumed connected,
  -- that components G K is just {G}, i.e. a singleton, hence finite
end


lemma autom [locally_finite G] [G.preconnected] (K : finset V) (φ : G ≃g G) :
  components G (finset.image φ K) = set.image (λ C, φ '' C) (components G K) :=
begin
  apply set.ext,
  intro C,
  split,
  { intro C_comp_im,sorry},
  {sorry},
end




end component







def inf_components (K : finset V) := {C : set V | C ∈ components G K ∧ C.infinite}
def fin_components (K : finset V) := {C : set V | C ∈ components G K ∧ C.finite}



section inf_components

variables {K L L' M : finset V}
          (K_sub_L : K ⊆ L) (L_sub_M : L ⊆ M)
          (K_sub_L' : K ⊆ L') (L'_sub_M : L' ⊆ M)


lemma inf_components_subset (K : finset V) : inf_components G K ⊆ components G K := λ C h, h.1
lemma fin_components_subset (K : finset V) : fin_components G K ⊆ components G K := λ C h, h.1


lemma infinite_graph_to_inf_components_nonempty (Vinfinite : (@set.univ V).infinite) : (inf_components G K).nonempty :=
begin
  sorry,
  -- K is finite, hence its boundary too, and there can only be a finite number of components
  -- if all are finite, then their union is finite, so that V is finite too
end

instance inf_components_finite [locally_finite G] : fintype (inf_components G K) :=
(set.finite.subset (component.finite G K) (inf_components_subset G K)).fintype

def component_is_still_conn (D : set V) (D_comp : D ∈ components G L) :
  ∀ x y ∈ D, c_o G K x y :=
λ x xD y yD, connected_outside.monotone G K_sub_L x y (component.is_c_o G L D D_comp x xD y yD)



lemma conn_adj_conn_to_conn {X Y : set V}
    (Xconn : ∀ x y ∈ X, ∃ w : G.walk x y, (w.support.to_finset : set V) ⊆ X )
    (Yconn : ∀ x y ∈ Y, ∃ w : G.walk x y, (w.support.to_finset : set V) ⊆ Y )
    (XYadj : ∃ (x ∈ X) (y ∈ Y), G.adj x y) :
     ∀ x y ∈ X∪Y, ∃ w : G.walk x y, (w.support.to_finset : set V) ⊆ X∪Y := sorry


def extend_conn_to_finite_comps [locally_finite G] [Knempty : K.nonempty]
  (Kconn : ∀ x y ∈ K, ∃ w : G.walk x y, w.support.to_finset ⊆ K ) :
  {K' : finset V | K ⊆ K'
                 ∧ (∀ x y ∈ K', ∃ w : G.walk x y, w.support.to_finset ⊆ K')
                 ∧ (∀ C : components G K', C.val.infinite)
  --               ∧ components G K' = inf_components G K
  } :=
begin
  let finite_pieces : set V := ⋃₀ fin_components G K,
  have : set.finite finite_pieces, by {
    apply set.finite.sUnion,
    {exact set.finite.subset (component.finite G K) (fin_components_subset G K)},
    {rintros C Cgood, exact Cgood.2,}},

  let K' := K ∪ this.to_finset,
  use K',
  simp,
  split,
  { exact finset.subset_union_left _ _,},
  { split,
    { rintros x xK' y yK',
      rcases xK' with xK | ⟨C,⟨Ccomp,Cfin⟩,xC⟩,
      { rcases yK' with yK | ⟨D,⟨Dcomp,Dfin⟩,yD⟩,
        { rcases (Kconn x xK y yK) with ⟨w,wK⟩,
          use w,
          exact wK.trans (finset.subset_union_left _ _),
        },
        {
          let Dconn := component.is_connected G K D Dcomp,
          let d := component.to_bdry_point G K (sorry) ⟨D,Dcomp⟩,
          rcases component.to_bdry_point_spec G K (sorry) ⟨D,Dcomp⟩ with ⟨k,kK,dD,adj⟩,
          --rcases conn_adj_conn_to_conn G K D Kconn Dconn adj x xK y yD,
          sorry,
        },
      },
      { rcases yK' with yK | ⟨D,Dfin,yD⟩,
        {sorry},
        {sorry},
      },
    },
    { rintros C CcompK',
      by_contradiction Cfin,
      rw set.not_infinite at Cfin,
      sorry, -- and then what?!
    },
  }

end


-- I would need this from the simple_graph api
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

-- And this for lists:
lemma list.to_finset_tail {α : Type u} [decidable_eq α] (l : list α) : l.tail.to_finset ⊆ l.to_finset :=
match l with
| list.nil := by {simp only [list.tail_nil, list.to_finset_nil, finset.empty_subset],}
| list.cons h l := by {simp only [list.tail_cons, list.to_finset_cons], exact finset.subset_insert _ _}
end

lemma list.to_finset_subset_to_finset {α : Type u} [decidable_eq α] (l₁ l₂ : list α) (l₁ ⊆ l₂) : l₁.to_finset ⊆ l₂.to_finset := sorry


def extend_to_conn [Gconn : preconnected G] [locally_finite G] [Vnempty : nonempty V] :
  {K' : finset V | K ⊆ K'
                 ∧ ∀ (x y ∈ K'), ∃ (w : G.walk x y), w.support.to_finset ⊆ K' } :=
begin
  let v₀ : V := Vnempty.some,
  let path_to_v₀ := λ (k : V), (Gconn k v₀).some.support.to_finset,
  let K' := finset.bUnion K path_to_v₀,
  use K',
  split,
  { rintros k kK,
    apply finset.mem_bUnion.mpr,
    use [k,kK],
    simp only [list.mem_to_finset, start_mem_support],},
  { rintros x xK' y yK',
    rcases finset.mem_bUnion.mp xK' with ⟨kx,kxK,xwalk⟩,
    rcases finset.mem_bUnion.mp yK' with ⟨ky,kyK,ywalk⟩,
    rw list.mem_to_finset at xwalk,
    rw list.mem_to_finset at ywalk,
    rcases walk.mem_support_iff_exists_append.mp xwalk with ⟨qx,rx,xwalk'⟩,
    rcases walk.mem_support_iff_exists_append.mp ywalk with ⟨qy,ry,ywalk'⟩,
    let w := rx.append ry.reverse,
    use w,
    rw walk.support_append,
    rw list.to_finset_append,
    apply finset.union_subset,
    { have := finset.subset_bUnion_of_mem (λ k, (Gconn k v₀).some.support.to_finset) kxK,
      have : rx.support.to_finset ⊆ K', by {
        apply finset.subset.trans _ this,
        simp only,
        rw xwalk',
        apply list.to_finset_subset_to_finset ry.support (qx.append rx).support ,
        exact walk.support_append_subset_right qx rx,
      },
      exact finset.subset.trans (finset.subset.refl _) this,
    },
    { have := finset.subset_bUnion_of_mem (λ k, (Gconn k v₀).some.support.to_finset) kyK,
      have : ry.reverse.support.to_finset ⊆ K', by {
        apply finset.subset.trans _ this,
        simp only [support_reverse, list.to_finset_reverse],
        rw ywalk',
        apply list.to_finset_subset_to_finset ry.support (qy.append ry).support ,
        exact walk.support_append_subset_right qy ry,
      },
      apply finset.subset.trans _ this,
      rw walk.support_reverse,
      exact list.to_finset_tail (ry.support.reverse),},


  },
end




-- TODO: maybe, define bwd_map for (potentially finite) components and then restrict it

def bwd_map : inf_components G L → inf_components G K :=
λ D,
let
  itexists := component.conn_sub G
              K D.val
              (component.nempty G L D.val D.prop.1)
              (component_is_still_conn G K_sub_L D.val D.prop.1)
, C := some itexists
, C_prop := some_spec itexists
in
  ⟨C,C_prop.1, λ fin, D.prop.2 (set.finite.subset fin C_prop.2)⟩


def bwd_map_def (D : inf_components G L) (C : inf_components G K) :
  bwd_map G K_sub_L D = C ↔ D.val ⊆ C.val :=
let
  itexists := component.conn_sub G K D (component.nempty G L D.val D.prop.1) (component_is_still_conn G K_sub_L D.val D.prop.1),
  C' := some itexists,
  C_prop' := some_spec itexists
in
  begin
    have eqdef : bwd_map G K_sub_L D =
           ⟨C',C_prop'.1, λ fin, D.prop.2 (set.finite.subset fin C_prop'.2)⟩, by
    { unfold bwd_map, dsimp,simpa,},
    split,
    { intro eq, cases eq, exact C_prop'.2,},
    { intro sub,
      have lol := component.conn_sub_unique G K D (component.nempty G L D.val D.prop.1) (component_is_still_conn G K_sub_L D.val D.prop.1), -- the fact that D is still connected wrt K … should be easy
      rcases lol with ⟨uniqueC,uniqueC_is_good,unicity⟩,
      rw eqdef,
      apply subtype.ext_val, simp,
      rw (unicity C' C_prop'),
      rw (unicity C.val ⟨C.prop.1,sub⟩).symm,simp,
    }
  end

def bwd_map_sub (D : inf_components G L) : D.val ⊆ (bwd_map G K_sub_L D).val :=
begin
  apply (bwd_map_def G K_sub_L D (bwd_map G K_sub_L D)).mp,
  reflexivity,
end

lemma bwd_map_refl (C : inf_components G K) : bwd_map G (set.subset.refl K) C = C :=
by {rw bwd_map_def}

lemma subcomponents_cover (K_sub_L : K ⊆ L) (C : set V) (hC : C ∈ components G K) :
  C ⊆ L ∪ (⋃₀ { D : set V | D ∈ components G L ∧ D ⊆ C}) :=
begin
  rintro x x_in_C,
  by_cases h: x∈L,
  { left,exact h},
  { right,
    let D := component.of G L x,
    have : x ∈ D, from component.mem_of G L x h,
    rw set.mem_sUnion,
    use D,
    split,
    { split,
      exact component.of_in_components G L x h,
      let D_comp := component.of_in_components G L x h,
      exact component.sub_of_conn_intersects G K D
        (component.nempty G L D D_comp)
        (component_is_still_conn G K_sub_L D D_comp)
        C hC ( set.nonempty_inter_iff_exists_left.mpr ⟨⟨x,‹x∈D›⟩,x_in_C⟩  : (D ∩ C).nonempty),
    },
    from component.mem_of G L x h,
  }
end

lemma bwd_map_surjective [locally_finite G] : surjective (bwd_map G K_sub_L) :=
begin
  unfold surjective,
  rintros ⟨C,C_comp,C_inf⟩,
  let L_comps := components G L,
  let L_comps_in_C := { D : set V | D ∈ components G L ∧ D ⊆ C},
  have sub : L_comps_in_C ⊆ L_comps, from (λ D ⟨a,b⟩,  a),
  have : L_comps_in_C.finite, from set.finite.subset (component.finite G L) sub,
  have : (⋃₀ L_comps_in_C).infinite, by {
    rintro hfin,
    have lol := set.infinite.mono (subcomponents_cover G K_sub_L C C_comp) C_inf,
    have := set.finite_union.mpr ⟨(sorry : (L : set V).finite),hfin⟩,
    exact lol this,
  },
    --λ fin, C_inf ((sorry : (L : set V).finite).union fin).subset (subcomponents_cover G K_sub_L C C_comp)),

  have : ∃ D : set V, D ∈ L_comps_in_C ∧ D.infinite, by {
    by_contra' all_fin,
    simp at all_fin,
    exact this ( set.finite.sUnion
                 ‹L_comps_in_C.finite›
                 ( λ D ⟨D_comp,D_sub_C⟩, all_fin D D_comp D_sub_C) ),},
  rcases this with ⟨D,⟨D_comp_L,D_sub_C⟩,D_inf⟩,
  use ⟨D,D_comp_L,D_inf⟩,
  rw (bwd_map_def G K_sub_L ⟨D,D_comp_L,D_inf⟩ ⟨C,C_comp,C_inf⟩),
  exact D_sub_C,
end


def bwd_map_comp :
  (bwd_map G K_sub_L) ∘ (bwd_map G L_sub_M) = (bwd_map G (K_sub_L.trans L_sub_M)) :=
begin
  apply funext,
  rintro E,
  let D := bwd_map G L_sub_M E,
  let C := bwd_map G K_sub_L D,
  apply eq.symm,
  unfold function.comp,
  apply (bwd_map_def G (K_sub_L.trans L_sub_M) E C).mpr,
  exact (bwd_map_sub G L_sub_M E).trans (bwd_map_sub G K_sub_L D),
end

def bwd_map_comp' (E : inf_components G M) :
  bwd_map G K_sub_L (bwd_map G L_sub_M E) = bwd_map G (K_sub_L.trans L_sub_M) E :=
begin
  let D := bwd_map G L_sub_M E,
  let C := bwd_map G K_sub_L D,
  apply eq.symm,
  apply (bwd_map_def G (K_sub_L.trans L_sub_M) E C).mpr,
  exact (bwd_map_sub G L_sub_M E).trans (bwd_map_sub G K_sub_L D),
end

def bwd_map_diamond (E : inf_components G M) :
  bwd_map G K_sub_L (bwd_map G L_sub_M E) = bwd_map G K_sub_L' (bwd_map G L'_sub_M E) :=
by rw [bwd_map_comp',bwd_map_comp']


-- Towards Hopf-Freudenthal

lemma bwd_map_non_inj [locally_finite G] (H K : finset V) (C : inf_components G H)
  (D D' : inf_components G K)
  (Ddist : D ≠ D')
  (h : D.val ⊆ C.val) (h' : D'.val ⊆ C.val) :
  ¬ injective (bwd_map G (finset.subset_union_left H K : H ⊆ H ∪ K)) :=
begin
  rcases bwd_map_surjective G (finset.subset_union_right H K) D  with ⟨E,rfl⟩,
  rcases bwd_map_surjective G (finset.subset_union_right H K) D' with ⟨E',rfl⟩,
  have Edist : E ≠ E', by {rintro Eeq, rw Eeq at Ddist,exact Ddist (refl _)},
  have : bwd_map G (finset.subset_union_left H K) E = bwd_map G (finset.subset_union_left H K) E', by {
    have : E.val ⊆ C.val, by {apply set.subset.trans (bwd_map_sub G _ E) h,},
    have : E'.val ⊆ C.val, by {apply set.subset.trans (bwd_map_sub G _ E') h',},
    rw (bwd_map_def G (finset.subset_union_left H K) E C).mpr ‹E.val ⊆ C.val›,
    rw ←(bwd_map_def G (finset.subset_union_left H K) E' C).mpr ‹E'.val ⊆ C.val›,
  },
  rintro inj,
  exact Edist (inj this),
end

lemma nicely_arranged [locally_finite G] (H K : finset V)
  (Hnempty : H.nonempty) (Knempty : K.nonempty)
  (E E' : inf_components G H) (En : E ≠ E')
  (F : inf_components G K)
  (H_F : (H : set V) ⊆ F.val)
  (K_E : (K : set V) ⊆ E.val) : E'.val ⊆ F.val :=
begin
  by_cases h : (E'.val ∩ K).nonempty,
  { rcases h with ⟨v,v_in⟩,
    have vE' : v ∈ E'.val, from ((set.mem_inter_iff v E'.val K).mp v_in).left,
    have vE : v ∈ E.val, from  K_E ((set.mem_inter_iff v E'.val K).mp v_in).right,
    have := component.eq_of_common_mem G H E.val E'.val E.prop.1 E'.prop.1 v vE vE',
    exfalso,
    exact En (subtype.eq this),},
  {
    have : ∃ F' : inf_components G K, E'.val ⊆ F'.val, by {
      rcases component.conn_sub_of_connected_disjoint G K E'.val
             (set.infinite.nonempty E'.prop.2)
             (sorry) -- empty intersection means disjoint
             (component.is_connected G H E' E'.prop.1) with ⟨F',F'comp,sub⟩,
      have F'inf : F'.infinite, from set.infinite.mono sub E'.prop.2,
      use ⟨F',F'comp,F'inf⟩,
      exact sub,
    },
    rcases this with ⟨F',E'_sub_F'⟩,
    by_cases Fe : F' = F,
    { exact Fe ▸ E'_sub_F',},
    { rcases component.adjacent_to G H Hnempty E'.val E'.prop.1 with ⟨v,vh,vhH,vF',adj⟩,
      have : vh ∈ F.val, from H_F vhH,
      have : F.val = F'.val,
        from component.eq_of_adj_mem G K F.val F.prop.1 F'.val F'.prop.1 vh v this (E'_sub_F' vF') adj,
      exfalso,
      exact Fe (subtype.eq this).symm,
    },
  },
end

lemma nicely_arranged_bwd_map_not_inj [locally_finite G] (H K : finset V)
  (Hnempty : H.nonempty) (Knempty : K.nonempty)
  (E : inf_components G H) (inf_comp_H_large : fintype.card (inf_components G H) ≥ 3)
  (F : inf_components G K)
  (H_F : (H : set V) ⊆ F.val)
  (K_E : (K : set V) ⊆ E.val) : ¬ injective (bwd_map G (finset.subset_union_left K H : K ⊆ K ∪ H)) :=
begin
  let E₁ : inf_components G H := sorry,
  let E₂ : inf_components G H := sorry,
  have : E ≠ E₁, by sorry,
  have : E ≠ E₂, by sorry,
  have : E₁ ≠ E₂, by sorry,
  -- This follows from the cardinality, but not sure how to do that in lean
  apply bwd_map_non_inj G K H F E₁ E₂ ‹E₁ ≠ E₂› _ _,
  {exact nicely_arranged G H K Hnempty Knempty E E₁ ‹E ≠ E₁› F H_F K_E,},
  {exact nicely_arranged G H K Hnempty Knempty E E₂ ‹E ≠ E₂› F H_F K_E,},
end





end inf_components

section ends

variables {K L L' M : finset V}
          (K_sub_L : K ⊆ L) (L_sub_M : L ⊆ M)
          (K_sub_L' : K ⊆ L') (L'_sub_M : L' ⊆ M)




private def up (K : finset V) := {L : finset V | K ⊆ L}
private lemma in_up  (K : finset V) : K ∈ (up K) := finset.subset.refl K
private lemma up_cofin  (K : finset V) :
  ∀ M : finset V, ∃ L : finset V, L ∈ up K ∧  M ⊆ L := λ M, ⟨M ∪ K,⟨subset_union_right M K,subset_union_left M K⟩⟩




private structure fam :=
  (fam: set (finset V))
  (cof: ∀ K : finset V, ∃ F : finset V, F ∈ fam ∧ K ⊆ F)
private def fin_fam : fam := ⟨@set.univ (finset V),(λ K, ⟨K,trivial,finset.subset.refl K⟩)⟩
private def fin_fam_up (K : finset V) : fam := ⟨up K, up_cofin K⟩

private def mem_fin_fam {ℱ : @fam V _} (K : ℱ.fam) : (@fin_fam V _).fam := ⟨↑K,trivial⟩


def ends_for (ℱ : fam) :=
{ f : Π (K : ℱ.fam), inf_components G K.val | ∀ K L : ℱ.fam, ∀ h : K.val ⊆ L.val, bwd_map G h (f L) = (f K) }

lemma ends_for_directed  (ℱ : fam)
  (g : ends_for G ℱ) (K L : ℱ.fam) :
  ∃ (F : ℱ.fam) (hK : K.val ⊆ F.val) (hL : L.val ⊆ F.val),
    g.1 K = bwd_map G hK (g.1 F) ∧ g.1 L = bwd_map G hL (g.1 F) :=
begin
  rcases (ℱ.cof (↑K ∪ ↑L)) with ⟨F,F_fam,sub_F⟩,
  use F,
  use F_fam,
  use ((finset.subset_union_left K.val L.val).trans sub_F),
  use ((finset.subset_union_right K.val L.val).trans sub_F),
  split;
  { apply eq.symm,
    apply g.2,}
 end

def ends := ends_for G fin_fam


def to_ends_for (ℱ : fam) : ends G → ends_for G ℱ :=
λ f : ends G, ⟨ λ K, f.1 (mem_fin_fam K)
              , λ K L h, f.2 (mem_fin_fam K) (mem_fin_fam L) h⟩

def to_ends_for_def (ℱ : fam) (e : ends G) (K : ℱ.fam) :
  e.val (mem_fin_fam K) = (to_ends_for G ℱ e).val K := refl _


def of_ends_for_fun (ℱ : fam) (e : ends_for G ℱ) : Π (K : (fin_fam).fam), inf_components G K.val := λ K,
let
  F :=  (ℱ.cof K).some
, F_fam := (ℱ.cof K).some_spec.1
, K_sub_F := (ℱ.cof K).some_spec.2
in
  bwd_map G K_sub_F (e.1 ⟨F,F_fam⟩)

def of_ends_for_comm (ℱ : fam) (e : ends_for G ℱ) :
  ∀ K L : (fin_fam).fam, ∀ h : K.val ⊆ L.val, bwd_map G h ((of_ends_for_fun G ℱ) e L) = (of_ends_for_fun G ℱ) e K :=
λ K L hKL, by {
      rcases (ℱ.cof K) with ⟨FK,⟨FK_fam,K_FK⟩⟩,
      rcases (ℱ.cof L) with ⟨FL,⟨FL_fam,L_FL⟩⟩,
      rcases ends_for_directed G ℱ e ⟨FK,FK_fam⟩ ⟨FL,FL_fam⟩ with ⟨M,FK_M,FL_M,backK,backL⟩,
      have hey : of_ends_for_fun G ℱ e K = bwd_map G K_FK (e.1 ⟨FK,FK_fam⟩), by {sorry},
      have hoo : of_ends_for_fun G ℱ e L = bwd_map G L_FL (e.1 ⟨FL,FL_fam⟩), by {sorry},
      rw [hey,hoo,backK,backL,bwd_map_comp',bwd_map_comp',bwd_map_comp'],
}


def of_ends_for (ℱ : fam) : ends_for G ℱ → ends G :=
λ e, ⟨of_ends_for_fun G ℱ e, of_ends_for_comm G ℱ e⟩

lemma of_ends_for.preserves (ℱ : fam) (K : ℱ.fam) (e : ends_for G ℱ) :
  e.val K = (of_ends_for G ℱ e).val (mem_fin_fam K) := sorry

lemma to_ends_for.preserves (ℱ : fam) (K : ℱ.fam) (e : ends G) :
  e.val (mem_fin_fam K) = (to_ends_for G ℱ e).val K := sorry

-- Thanks Kyle Miller
def equiv_ends_for (ℱ : fam) : ends G ≃ ends_for G ℱ :=
{ to_fun := to_ends_for G ℱ,
  inv_fun := of_ends_for G ℱ,
  left_inv := begin
    rintro ⟨g, g_comm⟩,
    simp only [of_ends_for, to_ends_for, comp_app, id.def, subtype.mk_eq_mk],
    ext1 F,
    apply g_comm,
  end,
  right_inv := begin
    rintro ⟨g, g_comm⟩,
    simp only [of_ends_for, to_ends_for, comp_app, id.def, subtype.mk_eq_mk],
    ext1 F,
    apply g_comm,
  end }


lemma ends_empty_graph : is_empty V → is_empty (ends G) :=
begin
  rintros ⟨no_V⟩,
  apply is_empty.mk,
  rintros ⟨f,f_comm⟩,
  rcases f ⟨@finset.empty V,trivial⟩ with ⟨_,⟨b,_⟩,_⟩,
  exact no_V b,
end

lemma ends_finite_graph  (Vfinite : (@set.univ V).finite) : is_empty (ends G) :=
begin
  apply is_empty.mk,
  rintros ⟨f,f_comm⟩,
  rcases f ⟨set.finite.to_finset Vfinite,trivial⟩ with ⟨C,⟨_,_⟩,C_inf⟩,
  exact C_inf (set.finite.subset Vfinite (set.subset_univ C)),
end


def eval_for (ℱ : fam) (K : ℱ.fam):
  ends_for G ℱ → inf_components G K := λ e, e.val K


def eval (K : finset V) : ends G → inf_components G K := eval_for G fin_fam ⟨K,trivial⟩


def eval_comm  (ℱ : fam) (K : ℱ.fam) (e : ends G) :
  eval_for G ℱ K (equiv_ends_for G ℱ e) = eval G K.val e :=
begin
  simp only [eval, eval_for, equiv_ends_for, equiv.coe_fn_mk],
  rw [←to_ends_for_def],
  simpa only,
end



lemma eval_injective_for_up (K : finset V)
  (inj_from_K : ∀ L : finset V, K ⊆ L → injective (bwd_map G ‹K⊆L›)) :
  injective (eval_for G (fin_fam_up K) ⟨K,in_up K⟩) :=
begin
  rintros e₁ e₂,
  simp only [eval_for, subtype.val_eq_coe],
  rintro same,
  apply subtype.eq,
  ext1 L,
  simp only [subtype.val_eq_coe],
  apply inj_from_K L L.prop,
  rw [e₁.prop ⟨K,in_up K⟩ L L.prop, e₂.prop ⟨K,in_up K⟩ L L.prop],
  assumption,
end


/-
  This shows that if K is such that the "backward maps" to K are all injective, then so is
  the evaluation map.
  It should eventually be used to bound the number of ends from above in certain cases.
  Say, when G is the grid ℤ²,
-/
lemma eval_injective (K : finset V)
  (inj_from_K : ∀ L : finset V, K ⊆ L → injective (bwd_map G ‹K⊆L›)) :
  injective (eval G K) :=
begin
  rintros e₁ e₂ same,
  let f₁ := (equiv_ends_for G (fin_fam_up K)) e₁,
  let f₂ := (equiv_ends_for G (fin_fam_up K)) e₂,
  have : f₁ = f₂, by {
    apply eval_injective_for_up G K inj_from_K,
    rw [ eval_comm G (fin_fam_up K) ⟨K,in_up K⟩ e₁,
         eval_comm G (fin_fam_up K) ⟨K,in_up K⟩ e₂],
    exact same,
  },
  simpa only [embedding_like.apply_eq_iff_eq],
end

lemma eval_injective' (K : finset V)
  (inj_from_K : ∀ L : finset V, K ⊆ L →
                ∃ L' : finset V, ∃ hL : (L ⊆ L'),
                injective (bwd_map G (‹K⊆L›.trans hL))) :
  injective (eval G K) :=
begin
  /-
    Idea:
    By the above, need only to show that given L with K ⊆ L, we have injective (bwd_map G ‹K⊆L›).
    But (bwd_map G ‹K⊆L›) ∘ (bwd_map G ‹L⊆L'›) = (bwd_map G ‹K⊆L'›)
    Since the RHS is injective by our assumption, then so is (bwd_map G ‹K⊆L›) and we're happy.
  -/
  sorry
end





/-
  The goal now would be to be able to bound the number of ends from below.
  The number of ends is at least the number of infinite components outside of K, for any given K,
  i.e. it cannot decrease.
  The construction to show this needs to extend each infinite component outside of K into an end.
  This is done by taking a family indexed over ℕ and by iteratively extending.
-/

lemma end_from_component [preconnected G] [locally_finite G] (K : finset V) (C : inf_components G K) :
  ∃ e : (ends G), e.val ⟨K,trivial⟩ = C := sorry


lemma eval_surjective [preconnected G] [locally_finite G] (K : finset V):
  surjective (eval G K) :=
begin
  unfold surjective,
  intro C,
  -- rcases end_from_component G K C with ⟨e,egood⟩,
  sorry,
end

@[instance]
lemma fintype_inf_connected_components  [preconnected G] [locally_finite G] [fintype (ends G)]
  (K : finset V) : fintype (inf_components G K) :=
@fintype.of_surjective _ _ (sorry) _ (eval G K) (@eval_surjective V G _ (sorry) _ K)


lemma finite_ends_to_inj [preconnected G] [locally_finite G] [fintype (ends G)] (Vnempty : nonempty V) :
  ∃ K : finset V, K.nonempty ∧ ∀ (L : finset V) (sub : K ⊆ L), injective (bwd_map G sub) :=
begin
  let v : V := Vnempty.some,
  let M := fintype.card (ends G),
  have all_fin : ∀ K : finset V, fintype (inf_components G K), from
    λ K, @fintype.of_surjective _ _ (sorry) _ (eval G K) (@eval_surjective V G _ (sorry) _ K),
  have all_le_M :=
    λ K, @fintype.card_le_of_surjective _ _ _ (all_fin K) (eval G K) (@eval_surjective V G _ (sorry) _ K),
  have  : ∃ K : finset V, ∀ K' : finset V, fintype.card (inf_components G K') ≤ fintype.card (inf_components G K), by sorry,
  rcases this with ⟨K,Kmax⟩,
  let Kv := insert v K,
  let KsubKv := finset.subset_insert v K,
  use Kv,
  split,
  { exact finset.insert_nonempty v K, },
  { rintros L KvsubL,
    by_contradiction notinj,
    have lol := @fintype.card_lt_of_surjective_not_injective _ _ (all_fin L) (all_fin Kv) (bwd_map G KvsubL) (bwd_map_surjective G KvsubL) notinj,
    have lol2 := @fintype.card_le_of_surjective _ _ (all_fin Kv) (all_fin K) (bwd_map G KsubKv) (bwd_map_surjective G KsubKv),
    have lol3 := lt_of_le_of_lt lol2 lol,
    have lol4 := Kmax L,
    have lol5 := lol4.not_lt,
    --exact lol5 lol3, -- it's not happy!
    sorry
  },

end
-- Choose K maximizing `inf_components G K`.




-- should be pretty much only λ C, end_of component G kfinite C
-- theorem `card_components_mon` saying htat `λ K, card (inf_components G K)` is monotone
-- theorem `finite_ends_iff` saying that `ends` is finite iff the supremum `λ K, card (inf_components G K)` is finite
-- theorem `finite_ends_card_eq` saying that if `ends` is finite, the cardinality is the sup
-- theorem `zero_ends_iff` saying that `ends = ∅` iff `V` is finite



--lemma ends_eq_disjoints_ends_of (Knempty : K.nonempty) (Kfinite : K.finite) : ends G = disjoint union of the ends of G-K


section transitivity

lemma transitive_to_good_automs [locally_finite G] [G.preconnected]
  (trans : ∀ u v : V, ∃ φ : G ≃g G, φ u = v)
  (Vinf : (@set.univ V).infinite) :
   ∀ K :finset V, ∃ φ : G ≃g G, disjoint K (finset.image φ K) :=
begin
  sorry
end

/-
  This is the key part of Hopf-Freudenthal
  Assuming this is proved:
  As long as K has at least three infinite connected components, then so does K', and
  bwd_map ‹K'⊆L› is not injective, hence the graph has more than three ends.
-/
lemma good_autom_bwd_map_not_inj [locally_finite G] [G.preconnected]
  (auts : ∀ K :finset V, ∃ φ : G ≃g G, disjoint K (finset.image φ K))
  (K : finset V) (Knempty : K.nonempty)
  (inf_comp_K_large : fintype.card (inf_components G K) ≥ 3) :
  ∃ (K' L : finset V) (hK' : K ⊆ K') (hL : K' ⊆ L),  ¬ injective (bwd_map G ‹K' ⊆ L›) :=
begin
  rcases @extend_to_conn V G _ K (sorry) _ (nonempty.intro Knempty.some) with ⟨Kp,KKp,Kpconn⟩ ,
  rcases @extend_conn_to_finite_comps V G _ Kp _ Kpconn with ⟨K',KK',K'conn,finn⟩,
  rcases auts K' with ⟨φ,φgood⟩,

  let φK' := finset.image φ K',
  let K'nempty := finset.nonempty.mono (KKp.trans KK') Knempty,
  let φK'nempty := finset.nonempty.image K'nempty φ,
  let L := K' ∪ φK',
  use [K',L,KKp.trans KK',finset.subset_union_left  K' (φK')],


  have φK'conn : ∀ x y ∈ φK', ∃ w : G.walk x y, w.support.to_finset ⊆ φK', by sorry,

  rcases component.conn_sub_of_connected_disjoint G K' φK' φK'nempty (finset.disjoint_coe.mpr φgood.symm) φK'conn with ⟨E,Ecomp,Esub⟩,
  rcases component.conn_sub_of_connected_disjoint G φK' K' K'nempty (finset.disjoint_coe.mpr φgood) K'conn with ⟨F,Fcomp,Fsub⟩,

  have Einf : E.infinite := finn ⟨E,Ecomp⟩,
  have Finf : F.infinite, by {
    have : F ∈ set.image (λ C, φ '' C) (components G K'), by {
      rw (@component.autom V G _ _ (sorry) K'  φ) at Fcomp,
      simpa only,},
    rcases this with ⟨FF,FFcomp,rfl⟩,
    have φ_inj_FF : set.inj_on φ FF, by {sorry},
    exact (set.infinite_image_iff φ_inj_FF).mpr (finn ⟨FF,FFcomp⟩),},

  apply nicely_arranged_bwd_map_not_inj G φK' K' (φK'nempty) (K'nempty) ⟨F,Fcomp,Finf⟩ _ ⟨E,Ecomp,Einf⟩ Esub Fsub,

  sorry,
end


lemma HopfFreudenthal [locally_finite G] [G.preconnected]
  (auts : ∀ K :finset V, ∃ φ : G ≃g G, disjoint K (finset.image φ K))
  [fintype (ends G)] : (fintype.card (ends G)) ≤ 2 :=
begin
  by_contradiction h,
  have many_ends : 3 ≤ (fintype.card (ends G)) := (nat.succ_le_iff.mpr (not_le.mp h)),
  rcases @finite_ends_to_inj V G _ (sorry) _ _ with ⟨K,Knempty,Kinj⟩,

  have : fintype.card ↥(G.inf_components K) ≥ 3, by {
    have := fintype.card_le_of_injective (eval G K) (eval_injective G K Kinj),
    exact many_ends.trans this,
  },

  rcases (@good_autom_bwd_map_not_inj V G _ _ (sorry) auts K Knempty this) with ⟨K',L,hK',hL,bwd_K_not_inj⟩,

  have : injective (bwd_map G hL) := by {
    let llo := Kinj  L (hK'.trans hL),
    rw ((bwd_map_comp G hK' hL).symm) at llo,
    exact injective.of_comp llo,
  },
  exact bwd_K_not_inj this,
end


end transitivity


end ends




end simple_graph


-/
