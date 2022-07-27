import data.set.finite
import data.sym.sym2
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
import topology.metric_space.basic
import data.setoid.partition

import .mathlib

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


lemma bij_components_of_autom [locally_finite G] [G.preconnected] (K : finset V) (φ : G ≃g G) :
  set.bij_on (λ C, φ '' C) (G.components K) (G.components (finset.image φ K)) := sorry






def inf_components (K : finset V) := {C : set V | C ∈ components G K ∧ C.infinite}
def fin_components (K : finset V) := {C : set V | C ∈ components G K ∧ C.finite}


section inf_components

variables {L L' M : finset V}
          (K_sub_L : K ⊆ L) (L_sub_M : L ⊆ M)
          (K_sub_L' : K ⊆ L') (L'_sub_M : L' ⊆ M)


lemma inf_components_subset (K : finset V) : inf_components G K ⊆ components G K := λ C h, h.1
lemma fin_components_subset (K : finset V) : fin_components G K ⊆ components G K := λ C h, h.1


lemma bij_inf_components_of_autom [locally_finite G] [G.preconnected] (K : finset V) (φ : G ≃g G) :
  set.bij_on (λ C, φ '' C) (inf_components G K) (inf_components G (finset.image φ K)) := sorry



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


def extend_to_fin_components [locally_finite G] (K : finset V) : finset V :=
begin
let finite_pieces : set V := ⋃₀ fin_components G K,
  have : set.finite finite_pieces, by {
    apply set.finite.sUnion,
    {exact set.finite.subset (component.finite G K) (fin_components_subset G K)},
    {rintros C Cgood, exact Cgood.2,}},
  exact K ∪ this.to_finset,
end

lemma extend_to_fin_components.sub [locally_finite G] (K : finset V) :
K ⊆ extend_to_fin_components G K := finset.subset_union_left _ _

lemma extend_to_fin_components.inf_components [locally_finite G] (K : finset V) :
  components G (extend_to_fin_components G K) = inf_components G K :=
begin
  let L := extend_to_fin_components G K,
  apply set.ext,
  rintros C,
  split,
  { rintro C_L,
    /-
    C_L : C ∈ components L
    Thus, C is connected (since it's a component) and does not intersect L, hence does not intersect K.
    Therefore, C is contained in a unique D ∈ components K.
    Since C does not intersect L, it does not intersect any D' ∈ fin_components K, hence cannot be contained in one.
    Hence, D ∈ inf_components K.
    Let us show C = D. We already know C ⊆ D, remains the other inclusion.
    Fix some c ∈ C and any d ∈ D.
    There is a path w from c to d entirely contained in D, hence not intersecting any D' ∈ fin_components K, and not intersecting K either.#check
    w is therefore outside of K', which by definition means that `co_o c d`, and thus d lies in C.
    -/
    sorry,
  },
  { rintro C_K,
    /-
    C_K : C ∈ inf_components K.
    Thus, C is connected, and disjoint from K and from any other C' ∈ components K.
    In particular, C is disjoint from L, and, being connected, it is contained in a unique D ∈ components L.
    Again, to show C = D, it suffices to choose some c ∈ C and show that any d ∈ D lies in C.
    Take a path w from c to d, entirely contained in D. By hypothesis, w does not intersect K, which implies that `co_o c d` and d lies in C.
    -/
    sorry,},
end

lemma extend_to_fin_components.connected_of_connected  [locally_finite G]
  (K : finset V)
  (Kconn : ∀ x y ∈ K, ∃ w : G.walk x y, w.support.to_finset ⊆ K ) :
  ∀ x y ∈ extend_to_fin_components G K, ∃ w : G.walk x y, w.support.to_finset ⊆ extend_to_fin_components G K :=
begin
  -- Sorry
  sorry,
end


def extend_connected_to_fin_components [locally_finite G] [Knempty : K.nonempty]
  (Kconn : ∀ x y ∈ K, ∃ w : G.walk x y, w.support.to_finset ⊆ K ) :
  {K' : finset V | K ⊆ K'
                 ∧ (∀ x y ∈ K', ∃ w : G.walk x y, w.support.to_finset ⊆ K')
                 ∧ (∀ C : components G K', C.val.infinite)
  } :=
begin
  use extend_to_fin_components G K,
  use extend_to_fin_components.sub G K,
  use extend_to_fin_components.connected_of_connected G K Kconn,
  rintros ⟨C,CK'⟩,
  rw extend_to_fin_components.inf_components G K at CK',
  exact CK'.2,
end

/-
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
          rcases conn_adj_conn_to_conn G Kconn Dconn (⟨k,kK,d,dD,adj⟩) x (set.subset_union_left K D xK) y (set.subset_union_right K D yD) with ⟨w,wgood⟩,
          use w,
          -- w is supported on K ∪ D, which is clearly contained in K ⋃ {all the Ds}
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
-/




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
        -- throws an error - failed to unify
        -- apply list.to_finset_subset_to_finset ry.support (qx.append rx).support ,
        -- exact walk.support_append_subset_right qx rx,
        admit,
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
        (component_is_still_conn G K K_sub_L D D_comp)
        C hC ( set.nonempty_inter_iff_exists_left.mpr ⟨⟨x,‹x∈D›⟩,x_in_C⟩  : (D ∩ C).nonempty),
    },
    from component.mem_of G L x h,
  }
end

end inf_components

end component


end simple_graph
