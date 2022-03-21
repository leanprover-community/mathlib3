import data.rel
import data.set.finite
import data.sym.sym2
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
import topology.metric_space.basic
import data.setoid.partition
import logic.relation

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

section ends

parameters {V : Type u}
           {G : simple_graph V}
           {G_is_conn : ∀ x y : V, nonempty (G.walk x y)}
           [has_inter (finset V)]
           [decidable_eq  V]
           [has_compl V]
           [locally_finite G]


def connected_outside (K : set V) (x y : V) : Prop :=
  ∃ w : walk G x y, disjoint K w.support.to_finset

namespace connected_outside

def c_o := connected_outside

lemma monotone {K K' : set V} (hK : K ⊆ K') (x y : V) :
  connected_outside K' x y → connected_outside K x y :=
λ ⟨w,dis⟩, ⟨w,disjoint_of_subset_left hK dis⟩

lemma not_in  {K : set V} {x y : V} (conn : connected_outside K x y) : x ∉ K ∧ y ∉ K  :=
begin
  rcases conn with ⟨xy, dis⟩,
  have x_in : x ∈ ↑(xy.support.to_finset),
    by {rw [mem_coe, list.mem_to_finset], apply walk.start_mem_support},
  have y_in : y ∈ ↑(xy.support.to_finset),
    by {rw [mem_coe, list.mem_to_finset], apply walk.end_mem_support},
  split,
  { exact set.disjoint_right.mp dis x_in,},
  { exact set.disjoint_right.mp dis y_in,}
end

@[protected]
lemma refl {K : set V} (x : V) (hx : x ∉ K) : connected_outside K x x :=
⟨walk.nil, by { rw [walk.support_nil,list.to_finset_cons,list.to_finset_nil],simpa}⟩

lemma of_adj_outside (K : set V) (x y : V) (hx : x ∉ K) (hy : y ∉ K) :
  G.adj x y → connected_outside K x y :=
begin
  intro a,
  unfold connected_outside,
  use (walk.cons a walk.nil),
  rw [walk.support_cons,walk.support_nil,list.to_finset_cons,list.to_finset_cons,list.to_finset_nil],
  simp,
  rw [set.disjoint_iff_inter_eq_empty,
      set.inter_comm,
      set.insert_inter_of_not_mem hx,
      set.singleton_inter_eq_empty.mpr hy],
end

@[protected]
lemma symm  {K : set V} : symmetric (connected_outside K) :=
λ x y, λ ⟨w,dis⟩, ⟨w.reverse, by {rw [walk.support_reverse,list.to_finset_reverse],exact dis}⟩

@[protected]
lemma trans {K : set V} : transitive (connected_outside K) :=
λ x y z,
begin
  rintros ⟨xy,disxy⟩ ⟨yz,disyz⟩,
  use xy.append yz,
  rw walk.support_append,
  rw list.to_finset_append,
  simp,
  split,
  { exact disxy },
  { have : ↑(yz.support.tail.to_finset) ⊆ ↑(yz.support.to_finset), by
    { rw walk.support_eq_cons, simp, rw finset.coe_insert, exact set.subset_insert y (↑(yz.support.tail.to_finset)),},
    apply @set.disjoint_of_subset_right V K ↑(yz.support.tail.to_finset) ↑(yz.support.to_finset) this,
    exact disyz,}
end

section K_fixed

parameter (K : set V)

def components: set (set V) := {C : set V | ∃ x ∈ C, C = {y : V | c_o K x y}}

namespace component

def of (x : V) : (set V) := {y : V | c_o K x y}

lemma of_in_components (x : V) (hx : x ∉ K) : of x ∈ components :=
begin
  have : c_o K x x, from @connected_outside.refl V G _ _ _ _ K x hx,
  use x,
  split,
  exact this,
  simpa,
end

lemma mem_of (x : V) (hx : x ∉ K) : x ∈ (of x) :=
begin
  have : c_o K x x, from @connected_outside.refl V G _ _ _ _ K x hx,
  exact this,
end


lemma nempty (C : set V) (hC : C ∈ components) : set.nonempty C :=
begin
  rcases hC with ⟨x,x_in_C,sat⟩,
  exact ⟨x,x_in_C⟩,
end

lemma is_conn (C : set V) (hC : C ∈ components) : ∀ x y ∈ C, c_o K x y :=
begin
  rintros x x_in y y_in,
  rcases hC with ⟨z,z_in_C,rfl⟩,
  exact connected_outside.trans (x_in.symm) y_in,
end

lemma not_in_of_in_comp (C : set V) (hC : C ∈ components) (x : V) (hx : x ∈ C) : x ∉ K :=
(not_in (is_conn C hC x hx x hx)).1

lemma conn_sub (P : set V)
  (Pnempty : set.nonempty P) (Pconn : ∀ x y ∈ P, c_o K x y) : ∃ C : set V, C ∈ components ∧ P ⊆ C :=
begin
  rcases Pnempty with ⟨p,p_in_P⟩,
  have p_notin_K : p ∉ K := (not_in (Pconn p p_in_P p p_in_P)).1,
  let Cp := @of V G _ _ _ _ K p, -- why do I need to provide K here???
  let p_in_Cp := @mem_of V G _ _ _ _ K p p_notin_K,
  let Cp_comp := @of_in_components V G _ _ _ _ K p p_notin_K,
  use Cp,
  use Cp_comp,
  simp *,
  rw set.subset_def,
  exact λ x x_in_P, Pconn p p_in_P x x_in_P,
end



-- This one could probably use `conn_sub` but I'm too lazy/stupid to figure the neatest way to do things
lemma eq_of_common_mem (C D : set V) (hC : C ∈ components) (hD : D ∈ components)
  (x : V) (x_in_C : x ∈ C) (x_in_D : x ∈ D) : C = D :=
begin
  rcases hC with ⟨y,y_in_C,rfl⟩,
  rcases hD with ⟨z,z_in_D,rfl⟩,
  apply set.ext,
  intro w,
  have y_c_o_z : c_o K y z, from connected_outside.trans x_in_C x_in_D.symm,
  split,
  from λ w_in_C, connected_outside.trans y_c_o_z.symm w_in_C,
  from λ w_in_D, connected_outside.trans y_c_o_z w_in_D,
end

lemma mem_of_mem_of_conn (C : set V) (hC : C ∈ components)
  (x y : V) (x_in_C : x ∈ C) (x_conn_y : c_o K x y) : y ∈ C :=
begin
  rcases hC with ⟨c,c_in_C,rfl⟩,
  exact connected_outside.trans x_in_C x_conn_y,
end

lemma mem_of_mem_of_adj (C : set V) (hC : C ∈ components)
  (x y : V) (x_in_C : x ∈ C) (y_notin_K : y ∉ K) (adj : G.adj x y) : y ∈ C :=
mem_of_mem_of_conn C hC x y x_in_C $ of_adj_outside K x y (not_in_of_in_comp C hC x x_in_C) y_notin_K adj


lemma conn_sub_unique (P : set V)
  (Pnempty : set.nonempty P) (Pconn : ∀ x y ∈ P, c_o K x y) : ∃! C : set V, C ∈ components ∧ P ⊆ C :=
begin
  rcases conn_sub K P Pnempty Pconn with ⟨C,⟨C_comp,P_sub_C⟩⟩,
  use C,
  split,split,
  exact C_comp,
  exact P_sub_C,
  rintros D ⟨D_comp,P_sub_D⟩,
  rcases Pnempty with ⟨p,p_in_P⟩,
  exact (eq_of_common_mem K C D C_comp D_comp p (P_sub_C p_in_P) (P_sub_D p_in_P)).symm,
end

lemma sub_of_conn_intersects
  (P : set V) (Pnempty : set.nonempty P) (Pconn : ∀ x y ∈ P, c_o K x y)
  (C ∈ components) (inter : (P ∩ C).nonempty) : P ⊆ C :=
begin
  sorry -- todo
end

lemma walk_outside_is_contained (C : set V) (hC : C ∈ components) :
  Π (x y : V), Π (w : G.walk x y), x ∈ C → y ∈ C → disjoint K w.support.to_finset → (w.support.to_finset : set V) ⊆ C
| x _ nil             hx hy _  := by {simp,exact hx}
| x y (@cons V G _ z _ adj tail) hx hy hw := by {
  rw walk.support,
  rw list.to_finset_cons,
  simp,
  rw set.insert_subset,
  split,
  exact hx,
  have : z ∈ (cons adj tail).support.to_finset, by simp,
  have : z ∉ K, from set.disjoint_right.mp hw this,
  have : z ∈ C, from mem_of_mem_of_adj K C hC x z hx ‹z∉K› adj,
  have : disjoint K tail.support.to_finset, {
    apply set.disjoint_of_subset_right _ hw,
    simp,
  },
  exact walk_outside_is_contained z y tail ‹z∈C› hy this,
}


lemma is_connected (C : set V) (hC : C ∈ components) (x y : V) (hx : x ∈ C) (hy : y ∈ C) :
  ∃ w : G.walk x y, (w.support.to_finset : set V) ⊆ C :=
begin
  rcases is_conn K C hC x hx y hy with ⟨w,dis_K⟩,
  use w,
  exact walk_outside_is_contained K C hC x y w hx hy dis_K,
end



--only used in next lemma
private def walks (C : set V) (k : V) := Σ (x : C), G.walk x k
private def w_len  (C : set V) (k : V) :  walks C k → ℕ := λ w, w.2.length
private def w_min (C : set V) (k : V) := @function.argmin _ _ (w_len C k) _ nat.lt_wf
private def w_min_spec (C : set V) (k : V) := @function.argmin_le _ _ (w_len C k) _ nat.lt_wf

lemma adjacent_to (Knempty: K.nonempty) (C : set V) (hC : C ∈ components) :
∃ (v k : V), k ∈ K ∧ v ∈ C ∧ G.adj k v :=
begin
  rcases Knempty with ⟨k,k_in_K⟩,
  have nemptywalks : nonempty (@walks V G _ _ _ _ C k), by {
    rcases nempty K C hC with ⟨x,x_in_C⟩,
    let w : G.walk x k := sorry, -- G_is_conn x k,
    exact nonempty.intro ⟨⟨x,x_in_C⟩,w⟩,},
  rcases hhh : @w_min V G _ _ _ _ C k nemptywalks with ⟨x, min_walk⟩,
  have x_notin_K : x.val ∉ K, from (not_in (is_conn K C hC x.val x.prop x.val x.prop)).1,
  rcases min_walk with nil|⟨_,y,_,x_adj_y,y_walk_k⟩,
  { exfalso,
    have : c_o K x x, from is_conn K C hC x.val x.prop x.val x.prop,
    exact x_notin_K k_in_K,},
  { by_cases h : y ∈ K,
    { use x, use y, use h, use x.prop, exact (x_adj_y).symm,},
    { have : c_o K x y, from connected_outside.of_adj_outside K x y x_notin_K h x_adj_y,
      have : y ∈ C, from mem_of_mem_of_conn K C hC x.val y x.prop this,
      let subwalk : @walks V G _ _ _ _ C k := ⟨⟨y,this⟩,y_walk_k⟩,
      have min_is_min := @w_min_spec V G _ _ _ _ C k subwalk (nemptywalks),
      have len_subwalk : (w_len C k subwalk) + 1 = w_len C k (w_min C k), by {
        unfold w_len at *,
        rw [hhh,←simple_graph.walk.length_cons],
      },
      have : (w_len C k subwalk) < (w_len C k subwalk) + 1, from lt_add_one (w_len C k subwalk),
      rw len_subwalk at this,
      exfalso,
      have ok : argmin (w_len C k) nat.lt_wf = w_min C k, by simpa, -- can I do this without simpa?
      rw ok at min_is_min,
      exact (lt_iff_not_ge _ _).mp this min_is_min,},}
end

def bdry : set V := {x : V | x ∉ K ∧ ∃ k ∈ K, G.adj x k}
lemma bdry_subset_union_neighbors : bdry ⊆ set.Union (λ x : K, G.neighbor_set x) :=
begin
  unfold bdry,
  rw set.subset_def,

  rintros x,
  rintros ⟨not_in_K,k,k_in_K,adj⟩,
  rw set.mem_Union,
  use [k,k_in_K],
  exact adj.symm,
end

lemma bdry_finite (Kfin : K.finite) : finite bdry :=
begin
  apply set.finite.subset _ (bdry_subset_union_neighbors K),
  apply set.finite.sUnion,
  haveI : fintype ↥K, from finite.fintype Kfin,
  apply set.finite_range,
  rintros nbd ⟨k,k_to_nbd⟩,
  simp at k_to_nbd,
  rw k_to_nbd.symm,
  exact finite.intro (_inst_4 ↑k), -- lol thanks library_search
end

def to_bdry_point (Knempty: K.nonempty) (Kfinite: K.finite) : components → V :=
λ C, some $ adjacent_to Knempty C.val C.prop

def to_bdry_point_spec (Knempty: K.nonempty) (Kfinite: K.finite) (C : components) :
  let v := (to_bdry_point Knempty Kfinite C) in ∃ k : V, k ∈ K ∧ v ∈ C.val ∧ G.adj k v :=
begin
  exact some_spec (@adjacent_to V G _ _ _ _ K Knempty C.val C.prop),
end

lemma to_bdry_point_inj (Knempty: K.nonempty) (Kfinite: K.finite) :
  function.injective $ to_bdry_point Knempty Kfinite :=
begin
  rintros C D c_eq_d,
  rcases to_bdry_point_spec K Knempty Kfinite C with ⟨k,kK,cC,k_adj_c⟩,
  rcases to_bdry_point_spec K Knempty Kfinite D with ⟨l,lK,dD,l_adj_d⟩,
  exact subtype.eq ( eq_of_common_mem K C.val D.val C.prop D.prop _ cC (c_eq_d.symm ▸ dD)),
end

lemma to_bdry_point_in_bdry  (Knempty: K.nonempty) (Kfinite: K.finite) :
  range (to_bdry_point Knempty Kfinite) ⊆ bdry :=
begin
  rw set.subset_def,
  rintros _ ⟨C,rfl⟩,
  rcases to_bdry_point_spec K Knempty Kfinite C with ⟨k,kK,cC,k_adj_c⟩,
  unfold bdry,
  have := not_in_of_in_comp K C.val C.prop _ cC,
  exact ⟨this,⟨k,⟨kK,k_adj_c.symm⟩⟩⟩,
end

lemma finite (Knempty: K.nonempty) (Kfinite: K.finite) : components.finite :=
begin
  by_contra comps_inf,
  haveI : infinite (subtype (components K)), from infinite_coe_iff.mpr comps_inf,
  have := @set.infinite_range_of_injective (subtype (components K)) V (_inst) (to_bdry_point K Knempty Kfinite) (to_bdry_point_inj K Knempty Kfinite),
  have : (bdry K).infinite, from set.infinite.mono (to_bdry_point_in_bdry K Knempty Kfinite) this,
  exact this (bdry_finite K Kfinite),
end

end component

end K_fixed

def inf_components (K : set V) := {C : set V | C ∈ components K ∧ C.infinite}

section KL_fixed

parameters {K L M : set V} (K_sub_L : K ⊆ L) (L_sub_M : L ⊆ M)

def component_is_still_conn (D : set V) (D_comp : D ∈ components L) :
  ∀ x y ∈ D, connected_outside K x y :=
λ x xD y yD, monotone K_sub_L x y (component.is_conn L D D_comp x xD y yD)


def bwd_map : inf_components L → inf_components K :=
λ D,
let
  itexists := component.conn_sub
              K D.val
              (component.nempty L D.val D.prop.1)
              (component_is_still_conn D.val D.prop.1)
, C := some itexists
, C_prop := some_spec itexists
in
  ⟨C,C_prop.1, λ fin, D.prop.2 (set.finite.subset fin C_prop.2)⟩


def bwd_map_def (D : inf_components L) (C : inf_components K) :
  bwd_map D = C ↔ D.val ⊆ C.val :=
let
  itexists := component.conn_sub K D (component.nempty L D.val D.prop.1) (component_is_still_conn D.val D.prop.1),
  C' := some itexists,
  C_prop' := some_spec itexists
in
  begin
    have eqdef : bwd_map K_sub_L D =
           ⟨C',C_prop'.1, λ fin, D.prop.2 (set.finite.subset fin C_prop'.2)⟩, by
    { unfold bwd_map, dsimp,simpa,},
    split,
    { intro eq, cases eq, exact C_prop'.2,},
    { intro sub,
      have lol := component.conn_sub_unique K D (component.nempty L D.val D.prop.1) (component_is_still_conn K_sub_L D.val D.prop.1), -- the fact that D is still connected wrt K … should be easy
      rcases lol with ⟨uniqueC,uniqueC_is_good,unicity⟩,
      rw eqdef,
      apply subtype.ext_val, simp,
      rw (unicity C' C_prop'),
      rw (unicity C.val ⟨C.prop.1,sub⟩).symm,simp,
    }
  end

def bwd_map_sub (D : inf_components L) : D.val ⊆ (bwd_map D).val :=
begin
  apply (bwd_map_def K_sub_L D (bwd_map K_sub_L D)).mp,
  reflexivity,
end

lemma subcomponents_cover (K_sub_L : K ⊆ L) (C : set V) (hC : C ∈ components K) :
  C ⊆ L ∪ (⋃₀ { D : set V | D ∈ components L ∧ D ⊆ C}) :=
begin
  rintro x x_in_C,
  by_cases h: x∈L,
  { left,exact h},
  { right,
    let D := @component.of V G _ _ _ _ L x,
    have : x ∈ D, from @component.mem_of V G _ _ _ _ L x h,
    rw set.mem_sUnion,
    use D,
    split,
    { split,
      exact @component.of_in_components V G _ _ _ _ L x h,
      let D_comp := @component.of_in_components V G _ _ _ _ L x h,
      exact component.sub_of_conn_intersects K D
        (component.nempty L D D_comp)
        (component_is_still_conn K_sub_L D D_comp)
        C hC ( set.nonempty_inter_iff_exists_left.mpr ⟨⟨x,‹x∈D›⟩,x_in_C⟩  : (D ∩ C).nonempty),
    },
    from @component.mem_of V G _ _ _ _ L x h,
  }
end

lemma bwd_map_surjective
  (Knempty : K.nonempty) (Kfinite : K.finite)
  (Lnempty : L.nonempty) (Lfinite : L.finite)
  : surjective (bwd_map) :=
begin
  unfold surjective,
  rintros ⟨C,C_comp,C_inf⟩,
  let L_comps := @components V G _ _ _ _ L,
  let L_comps_in_C := { D : set V | D ∈ @components V G _ _ _ _ L ∧ D ⊆ C},
  have sub : L_comps_in_C ⊆ L_comps, from (λ D ⟨a,b⟩,  a),
  have : L_comps_in_C.finite, from set.finite.subset (component.finite L Lnempty Lfinite) sub,
  have : (⋃₀ L_comps_in_C).infinite, from
    λ fin, C_inf ((Lfinite.union fin).subset (subcomponents_cover K_sub_L C C_comp)),

  have : ∃ D : set V, D ∈ L_comps_in_C ∧ D.infinite, by {
    by_contra' all_fin,
    simp at all_fin,
    exact this ( set.finite.sUnion
                 ‹L_comps_in_C.finite›
                 ( λ D ⟨D_comp,D_sub_C⟩, all_fin D D_comp D_sub_C) ),},
  rcases this with ⟨D,⟨D_comp_L,D_sub_C⟩,D_inf⟩,
  use ⟨D,D_comp_L,D_inf⟩,
  rw (bwd_map_def K_sub_L ⟨D,D_comp_L,D_inf⟩ ⟨C,C_comp,C_inf⟩),
  exact D_sub_C,
end



end KL_fixed

section dunno

variables {K L L' M : set V}
          (K_sub_L : K ⊆ L) (L_sub_M : L ⊆ M)
          (K_sub_L' : K ⊆ L') (L'_sub_M : L' ⊆ M)

def bwd_map_comp :
  (bwd_map K_sub_L ) ∘ (bwd_map L_sub_M) = (bwd_map (K_sub_L.trans L_sub_M)) :=
begin
  apply funext,
  rintro E,
  let D := bwd_map L_sub_M E,
  let C := bwd_map K_sub_L D,
  apply eq.symm,
  unfold function.comp,
  apply (bwd_map_def (K_sub_L.trans L_sub_M) E C).mpr,
  exact (bwd_map_sub L_sub_M E).trans (bwd_map_sub K_sub_L D),
end

def bwd_map_comp' (E : inf_components M) :
  bwd_map K_sub_L (bwd_map L_sub_M E) = bwd_map (K_sub_L.trans L_sub_M) E :=
begin
  let D := bwd_map L_sub_M E,
  let C := bwd_map K_sub_L D,
  apply eq.symm,
  apply (bwd_map_def (K_sub_L.trans L_sub_M) E C).mpr,
  exact (bwd_map_sub L_sub_M E).trans (bwd_map_sub K_sub_L D),
end

def bwd_map_diamond (E : inf_components M) :
  bwd_map K_sub_L (bwd_map L_sub_M E) = bwd_map K_sub_L' (bwd_map L'_sub_M E) :=
by rw [bwd_map_comp',bwd_map_comp']


end dunno


private def finsubsets := {K : set V | K.finite}

def ends_for (ℱ ⊆ finsubsets) (ℱ_cofin : ∀ K : finsubsets, ∃ F : ℱ, K.val ⊆ F.val) :=
{ f : Π (K : ℱ), inf_components K | ∀ K L : ℱ, ∀ h : ↑K ⊆ ↑L, bwd_map h (f L) = (f K) }

lemma ends_for_directed (ℱ ⊆ finsubsets) (ℱ_cofin : ∀ K : finsubsets, ∃ F : ℱ, K.val ⊆ F.val)
  (g : ends_for ℱ H ℱ_cofin) (K L : ℱ) :
  ∃ (F : ℱ) (hK : K.val ⊆ F.val) (hL : L.val ⊆ F.val),
    g.1 K = bwd_map hK (g.1 F) ∧ g.1 L = bwd_map hL (g.1 F) :=
begin
  rcases (ℱ_cofin ⟨K.val∪L.val,set.finite_union.mpr ⟨(H K.prop),(H L.prop)⟩⟩) with ⟨F,F_good⟩,
  use F,
  use (set.subset_union_left K.val L.val).trans F_good,
  use (set.subset_union_right K.val L.val).trans F_good,
  split;
  { apply eq.symm,
    apply g.2,}
 end

def ends := ends_for finsubsets (λ K Kfin, Kfin) (λ K, ⟨K,set.subset.refl K.val⟩)

namespace ends

-- #print prefix simple_graph.connected_outside.ends.to_ends_for





def to_ends_for (ℱ ⊆ finsubsets) (ℱ_cofin : ∀ K : finsubsets, ∃ F : ℱ, K.val ⊆ F.val) :
  ends → ends_for ℱ H ℱ_cofin
| ⟨f,f_comm⟩ := ⟨ λ K, f ⟨K, H K.property⟩
                , λ K L hKL, f_comm (set.inclusion H K) (set.inclusion H L) hKL⟩


def of_ends_for (ℱ ⊆ finsubsets) (ℱ_cofin : ∀ K : finsubsets, ∃ F : ℱ, K.val ⊆ F.val) :
  ends_for ℱ H ℱ_cofin → ends :=
λ g,
  let
    f : Π (K : finsubsets), inf_components K := λ K,
      let
        F := classical.some (ℱ_cofin K)
      , K_sub_F := classical.some_spec (ℱ_cofin K)
      in
        bwd_map K_sub_F (g.1 F)
  , f_comm : ∀ K L : finsubsets, ∀ h : ↑K ⊆ ↑L, bwd_map h (f L) = (f K) := λ K L hKL, by
    { --simp *,
      let FK := some (ℱ_cofin K),
      let K_FK := some_spec (ℱ_cofin K),
      let FL := some (ℱ_cofin L),
      let L_FL := some_spec (ℱ_cofin L),
      rcases ends_for_directed ℱ H ℱ_cofin g FK FL with ⟨M,FK_M,FL_M,backK,backL⟩,
      have hey : f K = bwd_map K_FK (g.1 FK), by simpa,
      have hoo : f L = bwd_map L_FL (g.1 FL), by simpa,
      rw [hey,hoo,backK,backL,bwd_map_comp',bwd_map_comp',bwd_map_comp'],}
  in
    ⟨f,f_comm⟩


-- Kyle Miller
def to_ends_for' (ℱ ⊆ finsubsets) (ℱ_cofin : ∀ K : finsubsets, ∃ F : ℱ, K.val ⊆ F.val) :
  ends ≃ ends_for ℱ H ℱ_cofin :=
{ to_fun := to_ends_for ℱ H ℱ_cofin,
  inv_fun := of_ends_for ℱ H ℱ_cofin,
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




end ends

-- theorem `card_components_mon` saying htat `λ K, card (inf_components K)` is monotone
-- theorem `finite_ends_iff` saying that `ends` is finite iff the supremum `λ K, card (inf_components K)` is finite
-- theorem `finite_ends_card_eq` saying that if `ends` is finite, the cardinality is the sup
-- theorem `zero_ends_iff` saying that `ends = ∅` iff `V` is finite


end ends

end connected_outside


end simple_graph
