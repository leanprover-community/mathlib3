/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Kyle Miller, Alena Gusakov, Hunter Monroe
-/
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

lemma has_walks_contained (C : set V) (hC : C ∈ components) (x y : V) (hx : x ∈ C) (hy : y ∈ C) :
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

parameters (K L M : set V) (K_sub_L : K ⊆ L) (L_sub_M : L ⊆ M)

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
    have eqdef : bwd_map K L K_sub_L D =
           ⟨C',C_prop'.1, λ fin, D.prop.2 (set.finite.subset fin C_prop'.2)⟩, by
    { unfold bwd_map, dsimp,simpa,},
    split,
    { intro eq, cases eq, exact C_prop'.2,},
    { intro sub,
      have lol := component.conn_sub_unique K D (component.nempty L D.val D.prop.1) (sorry), -- the fact that D is still connected wrt K … should be easy
      rcases lol with ⟨uniqueC,uniqueC_is_good,unicity⟩,
      rw eqdef,
      apply subtype.ext_val, simp,
      rw (unicity C' C_prop'),
      rw (unicity C.val ⟨C.prop.1,sub⟩).symm,simp,
    }
  end



lemma subcomponents_cover (C : set V) (hC : C ∈ components K) :
  C ⊆ (L \ K) ∪ (⋃₀ { D : set V | D ∈ components L ∧ D ⊆ C}) :=
begin
sorry
end

end KL_fixed


/-

@[protected]
lemma not_refl  {K : set V} (x : V) (x_in_K : x ∈ K) : ¬ connected_outside K x x :=
not_K_outside x x x_in_K

def rel (K : set V) := relation.refl_gen (connected_outside K)
lemma rel_refl (K : set V) : reflexive (rel K) := refl_gen.reflexive
lemma rel_symm (K : set V) : symmetric (rel K) := refl_gen.symmetric symm
lemma rel_trans (K : set V) : (transitive (rel K)) := refl_gen.transitive trans
def rel_eqv (K : set V) : equivalence (rel K) := ⟨rel_refl K, rel_symm K, rel_trans K⟩

lemma rel_monotone {K K' : set V} (hK : K ⊆ K') (x y : V) : rel K' x y → rel K x y := refl_gen.monotone (monotone hK) x y

def connected_outside_setoid (K : set V) := setoid.mk (rel K) (rel_eqv K)

def connected_outside_components (K : set V) : set (set V) :=
setoid.classes (setoid.mk (rel K) (rel_eqv K))



def costd := connected_outside_setoid
def coc := connected_outside_components
def coc_dis (K : set V) := {C ∈ coc K | disjoint C K}
def coc_inf (K : set V) := {C ∈ coc K | set.infinite C}

lemma costd_rel_eq_rel (K : set V) : (costd K).rel = (rel K) :=
begin
  unfold costd,
  unfold connected_outside_setoid,
  simpa,
end




def coc_dis_of (K : set V) (x : V) (x_notin_K : x ∉ K) : coc_dis K := sorry
def mem_coc_dis_of (K : set V) (x : V) (x_notin_K : x ∉ K) : x ∈ (coc_dis_of K x x_notin_K : set V) := sorry
def eq_of_common_mem (K : set V) (C D ∈ coc K) (x : V) : x ∈ C ∧ x ∈ D → C = D := sorry
lemma coc_nonempty (K : set V) (C ∈ coc K) : C.nonempty :=
by apply setoid.nonempty_of_mem_partition (setoid.is_partition_classes _) H
def coc_conn (K : set V) (C ∈ coc K) : ∀ x y ∈ C, (rel K) x y :=
begin
  rintros x x_in_C y y_in_C,
  rw ←(costd_rel_eq_rel K),
  rw (costd K).rel_iff_exists_classes,
  use [C,H], split, {exact x_in_C,}, {exact y_in_C,},
end


lemma intersects_K_iff_singleton_mem_K (K : set V) :
  ∀ C ∈ coc K, (¬ disjoint C K) ↔ ∃ k ∈ K, C = {k} :=
begin
  rintros C CcocK,
  split,
  { intro Hdisjoint,
    rcases set.not_disjoint_iff.mp Hdisjoint with ⟨k,k_in_C,k_in_K⟩,
    use [k,k_in_K],
    rw set.eq_singleton_iff_unique_mem,
    use k_in_C,
    rintro x x_in_C,
    have xrk : @rel V G _ _ _ K x k, from
      (costd K).rel_iff_exists_classes.mpr ⟨C,CcocK,x_in_C,k_in_C⟩,
    cases xrk,
    { reflexivity,},
    { by_cases h : x = k,
      { exact h},
      { exfalso, apply not_K_outside x k k_in_K, assumption,}}},
  { rintros kkk,
    rcases kkk with ⟨k,k_in_K,C_eq_sing_k⟩,
    rw set.not_disjoint_iff,
    use k, split,
    { rw C_eq_sing_k,simp,},
    { exact k_in_K,}},
end

lemma disjoint_of_infinite (K : set V) (C ∈ coc_inf K) : disjoint C K :=
begin
  by_contradiction,
  rw (intersects_K_iff_singleton_mem_K K C) at h,
  rcases h with ⟨k,k_good,rfl⟩,
  rcases H with ⟨iscoc,isinf⟩,
  have := set.finite_singleton k,
  sorry,
  --apply (eq_sing.symm ▸ (set.finite_singleton k)),
  exact H,
  exact G,
end


lemma eq_of_adjacent_disjoint_K (K : set V) :
  ∀ (C ∈ coc_dis K) (D ∈ coc_dis K), (∃ (x ∈ C) (y ∈ D), G.adj x y) → C = D :=
begin
  rintros C C_coc_out D D_coc_out,
  unfold coc_dis at *,
  intros existsstuff,
  rcases existsstuff with ⟨x,x_in_C,y,y_in_D,x_adj_y⟩,
  rcases C_coc_out with ⟨C_coc,C_dis⟩,
  rcases D_coc_out with ⟨D_coc,D_dis⟩,

  have : x ∉ K, from set.disjoint_left.mp C_dis x_in_C,
  have : y ∉ K, from set.disjoint_left.mp D_dis y_in_D,
  have : rel K x y, from refl_gen.single (of_adj_outside K x y ‹x∉K› ‹y∉K› x_adj_y),
  rcases (costd K).rel_iff_exists_classes.mp ‹rel K x y› with ⟨E,E_coc,x_in_E,y_in_E⟩,

  calc C = E : setoid.eq_of_mem_classes C_coc x_in_C E_coc x_in_E
     ... = D : setoid.eq_of_mem_classes E_coc y_in_E D_coc y_in_D,
end

private def C_walk_k (C : set V) (k : V)  := Σ x : C,  G.walk x k
private lemma C_walk_k_nempty (C : set V) (Cnempty : C.nonempty) (k : V) :
  nonempty (C_walk_k C k) :=
begin
  rcases Cnempty with ⟨x,x_in_C⟩,
  have w : G.walk x k, by sorry,--from (is_conn x k),
  exact nonempty.intro (⟨⟨x,x_in_C⟩,w⟩ : C_walk_k C k),
end
private def C_walk_k_len  (C : set V) (k : V) : C_walk_k C k → ℕ := λ W, W.2.length

def bdry (K : set V) : set V := {x : V | x ∉ K ∧ ∃ k ∈ K, G.adj x k}


lemma connected_outside_adjacent_to
  (K : set V) (Knempty : K.nonempty) (C ∈ coc_dis K) :
∃ x : bdry K, ↑x ∈ C :=
begin
  rcases H with ⟨C_coc,C_dis⟩,
  rcases Knempty with ⟨k,k_in_K⟩,
  rcases argmin (C_walk_k_len C k) nat.lt_wf with ⟨⟨x,x_in_C⟩,w⟩,
  { let min_walk : C_walk_k C k := ⟨⟨x,x_in_C⟩,w⟩,
    cases w,
    { exfalso,
      exact set.not_disjoint_iff.mpr ⟨k,x_in_C,k_in_K⟩ C_dis,},
    { by_cases h : w_v ∈ K,
      { -- use [x,x_in_C,w_v,h],
        -- exact w_h,
        sorry },
      { have : w_v ∈ C, by sorry,
        --let shorter_walk : C_walk_k C k := ⟨⟨w_v,‹w_v∈C›⟩,w_p⟩,
        --let shorter_walk : C_walk_k C k := ⟨⟨w_v,h⟩,w_p⟩,
        --have : C_walk_k_len C k shorter_walk < C_walk_k_len C k min_walk, by sorry,
        --have := argmin_le (C_walk_k_len C k) nat.lt_wf shorter_walk,
        sorry, -- Should be simple: shorter_walk is subwalk, contradicting minimality
      }
    },
    exact G, -- what?
  },
  apply C_walk_k_nempty C _ k, -- Similarly, needs to ensure `C_walk_k` is not empty
  apply connected_outside_components_nonempty K C C_coc,
end


lemma bdry_subset_union_neighbors (K : set V) : (bdry K) ⊆ set.Union (λ x : K, G.neighbor_set x) :=
begin
  unfold bdry,
  rw set.subset_def,

  rintros x,
  rintros ⟨not_in_K,k,k_in_K,adj⟩,
  rw set.mem_Union,
  use [k,k_in_K],
  exact adj.symm,
end

lemma bdry_finite (K : set V) (Kfin : K.finite) : finite (bdry K) :=
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

def coc_dis_to_bdry (K : set V)  (Knempty : K.nonempty) :
 (subtype $ coc_dis K) → (bdry K)  :=
λ C, some $ connected_outside_adjacent_to K Knempty C.val C.prop


lemma coc_dis_to_bdry_inj (K : set V)  (Knempty : K.nonempty) :
  injective (coc_dis_to_bdry K Knempty) :=
begin
  unfold injective,
  rintros ⟨C,C_coc,C_dis⟩ ⟨D,D_coc,D_dis⟩,
  intro same_point,
  let xx := connected_outside_adjacent_to K Knempty C ⟨C_coc,C_dis⟩,
  let yy := connected_outside_adjacent_to K Knempty D ⟨D_coc,D_dis⟩,
  let x := some xx,
  let y := some yy,
  have x_eq_y : x = y, by simpa,
  have x_in_C : ↑x ∈ C, from some_spec xx,
  have y_in_D : ↑y ∈ D, from some_spec yy,
  unfold coc_dis_to_bdry at *,
  apply subtype.eq,
  apply eq_of_common_mem K C C_coc D D_coc x,
  split,
  exact x_in_C,
  rw x_eq_y,
  exact y_in_D,
end

lemma coc_dis_finite (K : set V) (Kfin : K.finite) (Knempty : K.nonempty) : finite (coc_dis K) :=
begin
  have : finite (bdry K), from @bdry_finite V G _ _ _ _ K Kfin,
  have fin_bdry : fintype (subtype $ bdry K), from finite.fintype this,
  have : injective (coc_dis_to_bdry K Knempty),
    from @coc_dis_to_bdry_inj V G _ _ _ _ K Knempty,
  apply finite.intro,
  exact @fintype.of_injective _ _ fin_bdry  (coc_dis_to_bdry K Knempty)  this,
  assumption,
end

lemma coc_inf_sub_coc_dis (K : set V) : (coc_inf K) ⊆ (coc_dis K) :=
λ C ⟨C_coc,C_inf⟩, ⟨C_coc,disjoint_of_infinite K C ⟨C_coc,C_inf⟩⟩

lemma coc_inf_finite (K : set V) (Kfin : K.finite) (Knempty : K.nonempty) : finite (coc_inf K) :=
finite.subset (coc_dis_finite K Kfin Knempty) (coc_inf_sub_coc_dis K)

lemma conn_in_unique_class {α : Type*} (r : setoid α) (s : set α)
  (snempty : s.nonempty) (sconn : ∀ (x y ∈ s), r.rel x y) : ∃! c ∈ r.classes, s ⊆ c :=
begin
  rcases snempty with ⟨x,x_in_s⟩,
  let c := {y : α | r.rel y x},
  have c_coc : c ∈ r.classes, from setoid.mem_classes r x,
  use c,simp,
  split,
  split,
  { exact c_coc},
  { rintros y y_in_s, exact (sconn y y_in_s x x_in_s),},
  { rintros d d_coc s_sub_d,
    have : x ∈ d, from mem_of_mem_of_subset x_in_s s_sub_d,
    have : x ∈ c, by simp, -- just because r.rel x x holds by reflectivity
    have lol := (setoid.is_partition_classes r).pairwise_disjoint.elim c_coc d_coc,
    have : ¬ disjoint c d, from set.not_disjoint_iff.mpr ⟨x, ‹x∈c›,‹x∈d›⟩,
    exact (lol this).symm,
  }



end

lemma coc_dis_exists_unique_containing
  (K : set V) (Kfin : K.finite) (Knempty : K.nonempty)
  (L : set V) (Lfin : L.finite) (Lnempty : L.nonempty)
  (K_sub_L : K ⊆ L) (C ∈ coc_dis L) : ∃! D ∈ coc_dis K, C ⊆ D :=
begin
  rcases H with ⟨C_coc_L,C_dis_L⟩,
  have C_conn_L : ∀ x y ∈ C, (costd L).rel x y, from coc_conn L C C_coc_L,
  have C_conn_K : ∀ (x y ∈ C), (costd K).rel x y, from λ x y ∈ C, rel_monotone K_sub_L  x y (C_conn_L x ‹x∈C› y ‹y∈C›),
  rcases conn_in_unique_class (costd K) (C) (coc_nonempty L C C_coc_L) C_conn_K with ⟨D,⟨D_coc_K,C_sub_D⟩,D_unique⟩,
  simp at C_sub_D,
  simp at D_unique,
  have C_not_sing_L : ¬ (∃ k ∈ L, C = {k}), from λ lol, (intersects_K_iff_singleton_mem_K L C C_coc_L).mpr lol C_dis_L,
  have D_not_sing_K : ¬ (∃ k ∈ K, D = {k}), by
  { rintros ⟨k,k_in_K,D_eq_sing_k⟩,
    have : C ⊆ {k}, from D_eq_sing_k ▸ C_sub_D,
    rcases set.subset_singleton_iff_eq.mp this,
    { have := (coc_nonempty L C C_coc_L), rw h at this, exact empty_not_nonempty this,},
    { cases h, have : ¬ disjoint {k} L, from set.not_disjoint_iff.mpr ⟨k,set.mem_singleton k,K_sub_L k_in_K⟩, exact this C_dis_L,}
  },
  have D_dis_K : disjoint D K, from (not_iff_comm.mp (intersects_K_iff_singleton_mem_K K D D_coc_K)).mp D_not_sing_K,
  use D,
  split,
  split,
  simp,
  exact C_sub_D,
  exact ⟨D_coc_K,D_dis_K⟩,
  rintros D' ⟨⟨D'_coc_K,D'_dis_K⟩,C_sub_D',D'_good⟩,
  exact D_unique D' D'_coc_K C_sub_D',
end

def coc_inf_backwards
  (K : set V) (Kfin : K.finite) (Knempty : K.nonempty)
  (L : set V) (Lfin : L.finite) (Lnempty : L.nonempty)
  (K_sub_L: K ⊆ L) :
coc_inf L → coc_inf K :=
begin
  rintros ⟨C,C_coc_L,C_inf⟩,
  have C_dis_L : disjoint C L, from disjoint_of_infinite L C ⟨C_coc_L,C_inf⟩,
  let good := (coc_dis_exists_unique_containing K Kfin Knempty L Lfin Lnempty K_sub_L C ⟨C_coc_L,C_dis_L⟩),
  have existsD : ∃ D : set V, D ∈ coc K ∧ disjoint D K ∧ C ⊆ D, by {
    sorry,
  },
  let D := some existsD,
  rcases some_spec existsD with ⟨D_coc_K,D_dis_K,C_sub_D⟩,
  have D_coc_K : D ∈ coc K, by simpa,
  have : D.infinite, from λ D_fin, C_inf (set.finite.subset D_fin C_sub_D),
  { use D, split, /-exact D_coc_K-/ sorry , exact ‹D.infinite›,}
end

lemma coc_inf_backwards_surjective
  (K : set V) (Kfin : K.finite) (Knempty : K.nonempty)
  (L : set V) (Lfin : L.finite) (Lnempty : L.nonempty)
  (K_sub_L: K ⊆ L) :
function.surjective (coc_inf_backwards K Kfin Knempty L Lfin Lnempty) :=
begin

end

-/

end connected_outside

end ends

end simple_graph
