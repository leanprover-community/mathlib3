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
local attribute [instance] prop_decidable


namespace simple_graph


variables  {V : Type u}
           (G : simple_graph V)
           [Glf : locally_finite G]
           --(Gpc : G.preconnected)



def reachable_outside (K : finset V) (x y : V) : Prop :=
  ∃ w : walk G x y, disjoint (K : finset V) w.support.to_finset

namespace reachable_outside

lemma monotone {K K' : finset V} (hK : K ⊆ K') (x y : V) :
  reachable_outside G K' x y → reachable_outside G K x y :=
λ ⟨w,dis⟩, ⟨w,disjoint_of_subset_left hK dis⟩

lemma not_in {K : finset V} {x y : V} (conn : reachable_outside G K x y) : x ∉ K ∧ y ∉ K  :=
begin
  rcases conn with ⟨xy, dis⟩,
  have x_in : x ∈ ↑(xy.support.to_finset),
    by {rw [mem_coe, list.mem_to_finset], apply walk.start_mem_support},
  have y_in : y ∈ ↑(xy.support.to_finset),
    by {rw [mem_coe, list.mem_to_finset], apply walk.end_mem_support},
  exact ⟨finset.disjoint_right.mp dis x_in,finset.disjoint_right.mp dis y_in⟩,
end

@[protected]
lemma refl {K : finset V} (x : V) (hx : x ∉ K) : reachable_outside G K x x :=
⟨walk.nil, by { rw [walk.support_nil,list.to_finset_cons,list.to_finset_nil],simpa only [insert_emptyc_eq, coe_singleton, finset.disjoint_singleton_right],}⟩

lemma of_adj_outside (K : finset V) (x y : V) (hx : x ∉ K) (hy : y ∉ K) :
  G.adj x y → reachable_outside G K x y :=
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
lemma symm  {K : finset V} : symmetric (reachable_outside G K) :=
λ x y, λ ⟨w,dis⟩, ⟨w.reverse, by {rw [walk.support_reverse,list.to_finset_reverse],exact dis}⟩

@[protected]
lemma trans {K : finset V} : transitive (reachable_outside G K)
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

end reachable_outside



open simple_graph.reachable_outside

def ro_components (K : finset V) : set (set V) := {C : set V | ∃ x ∈ C, C = {y : V | reachable_outside G K x y}}
def inf_ro_components (K : finset V) := {C : set V | C ∈ ro_components G K ∧ C.infinite}
def fin_ro_components (K : finset V) := {C : set V | C ∈ ro_components G K ∧ C.finite}


namespace ro_component

def ι (K : finset V) : inf_ro_components G K → ro_components G K :=
      λ ⟨s, ⟨h_ro, c⟩⟩, ⟨s, h_ro⟩
--variable (K : finset V)

def of (K : finset V) (x : V) : (set V) := {y : V | reachable_outside G K x y}

lemma of_in_components (K : finset V) (x : V) (hx : x ∉ K) : of G K x ∈ ro_components G K :=
⟨x,reachable_outside.refl G x hx,rfl⟩

lemma mem_of (K : finset V) (x : V) (hx : x ∉ K) : x ∈ (of G K x) := reachable_outside.refl G x hx

lemma nempty (K : finset V) (C : set V) : C ∈ ro_components G K → set.nonempty C
| ⟨x,x_in_C,sat⟩ := ⟨x,x_in_C⟩

lemma is_ro (K : finset V) (C : set V) : C ∈ ro_components G K →  ∀ x y ∈ C, reachable_outside G K x y
| ⟨z,z_in,eq⟩ x x_in y y_in :=
begin
  rw eq at x_in y_in,
  exact reachable_outside.trans G (reachable_outside.symm G x_in) y_in,
end

lemma not_in_of_in_comp (K : finset V) (C : set V) (hC : C ∈ ro_components G K) (x : V) (hx : x ∈ C) : x ∉ K :=
(not_in G (is_ro G K C hC x hx x hx)).1

lemma not_in_comp_of_in (K : finset V) (C : set V) (hC : C ∈ ro_components G K) (x : V) (hx : x ∈ K) : x ∉ C :=
begin
  intro xC,
  exact not_in_of_in_comp G K C hC x xC hx,
end

lemma of_ro_set (K : finset V) (P : set V) -- nonemptiness probably not needed
  (Pnempty : set.nonempty P) (P_ro : ∀ x y ∈ P, reachable_outside G K x y) :
  ∃ C : set V, C ∈ ro_components G K ∧ P ⊆ C :=
begin
  rcases Pnempty with ⟨p,p_in_P⟩,
  have p_notin_K : p ∉ K := (not_in G (P_ro p p_in_P p p_in_P)).1,
  let p_in_Cp := mem_of G K p p_notin_K,
  use [of G K p, of_in_components G K p p_notin_K],
  rw set.subset_def,
  exact λ x x_in_P, P_ro p p_in_P x x_in_P,
end

lemma ι_inj (K : finset V) : function.injective (ι G K) := by {rintros ⟨_, _, _⟩ ⟨_, _, _⟩, simp_rw [ι], tidy,}

-- This one could probably use `of_ro_set` but I'm too lazy/stupid to figure the neatest way to do things
lemma eq_of_common_mem (K : finset V) (C D : set V) (hC : C ∈ ro_components G K) (hD : D ∈ ro_components G K)
  (x : V) (x_in_C : x ∈ C) (x_in_D : x ∈ D) : C = D :=
begin
  rcases hC with ⟨y,y_in_C,rfl⟩,
  rcases hD with ⟨z,z_in_D,rfl⟩,
  apply set.ext,
  intro w,
  have y_c_o_z : reachable_outside G K y z, from reachable_outside.trans G x_in_C (reachable_outside.symm G x_in_D),
  split,
  from λ w_in_C, reachable_outside.trans G (reachable_outside.symm G y_c_o_z) w_in_C,
  from λ w_in_D, reachable_outside.trans G y_c_o_z w_in_D,
end

lemma mem_of_mem_of_ro (K : finset V) (C : set V) (hC : C ∈ ro_components G K)
  (x y : V) (x_in_C : x ∈ C) (x_ro_y : reachable_outside G K x y) : y ∈ C :=
begin
  rcases hC with ⟨c,c_in_C,rfl⟩,
  exact reachable_outside.trans G x_in_C x_ro_y,
end

lemma mem_of_mem_of_adj (K : finset V) (C : set V) (hC : C ∈ ro_components G K)
  (x y : V) (x_in_C : x ∈ C) (y_notin_K : y ∉ K) (adj : G.adj x y) : y ∈ C :=
mem_of_mem_of_ro G K C hC x y x_in_C $ of_adj_outside G K x y (not_in_of_in_comp G K C hC x x_in_C) y_notin_K adj

lemma eq_of_adj_mem (K : finset V)
  (C : set V) (hC : C ∈ ro_components G K)
  (D : set V) (hD : D ∈ ro_components G K)
  (x y : V) (x_in_C : x ∈ C) (y_in_D : y ∈ D) (adj : G.adj x y) : C = D :=
begin
  have y_in_C : y ∈ C, from mem_of_mem_of_adj G K C hC x y x_in_C (not_in_of_in_comp G K D hD y y_in_D) adj,
  exact (eq_of_common_mem G K C D hC hD y y_in_C y_in_D),
end


lemma unique_of_ro_set  (K : finset V) (P : set V)
  (Pnempty : set.nonempty P) (P_ro : ∀ x y ∈ P, reachable_outside G K x y) : ∃! C : set V, C ∈ ro_components G K ∧ P ⊆ C :=
begin
  rcases of_ro_set G K P Pnempty P_ro with ⟨C,⟨C_comp,P_sub_C⟩⟩,
  use C,
  split,
  exact ⟨C_comp,P_sub_C⟩,
  rintros D ⟨D_comp,P_sub_D⟩,
  rcases Pnempty with ⟨p,p_in_P⟩,
  exact (eq_of_common_mem G K C D C_comp D_comp p (P_sub_C p_in_P) (P_sub_D p_in_P)).symm,
end

-- the `Pnempty` assumption is not strictly required
lemma sub_ro_component_of_ro_of_intersects (K : finset V)
  (P : set V) (Pnempty : set.nonempty P) (P_ro : ∀ x y ∈ P, reachable_outside G K x y)
  (C ∈ ro_components G K) (inter : (P ∩ C).nonempty) : P ⊆ C :=
begin
  rcases H with ⟨x, ⟨hxC, hconnC⟩⟩, subst hconnC,
  rcases (set.nonempty_def.mp inter) with ⟨x', ⟨hx'P, path_xx'⟩⟩,
  intros p hpP,
  have path_x'p := P_ro x' hx'P p hpP,
  exact reachable_outside.trans G path_xx' path_x'p,
end

lemma walk_outside_is_contained (K : finset V) (C : set V) (hC : C ∈ ro_components G K) (x y : V)  (w : G.walk x y)
 (hx: x ∈ C) (hy: y ∈ C) (dis : disjoint K w.support.to_finset) : (w.support.to_finset : set V) ⊆ C :=
begin
  rintros z zin,
  rw finset.mem_coe at zin,
  rw list.mem_to_finset at zin,
  rcases walk.mem_support_iff_exists_append.mp zin with ⟨q,r,rfl⟩,
  have : disjoint K q.support.to_finset, from disjoint.mono_right (list.to_finset_subset_to_finset _ _ (walk.support_append_subset_left q r)) dis,
  rcases hC with ⟨c,cC,rfl⟩,
  exact reachable_outside.trans G hx ⟨q,this⟩,
end


lemma to_subconnected (K : finset V) (C : set V) (hC : C ∈ ro_components G K) : simple_graph.subconnected G C :=
begin
  rintros x hx y hy,
  rcases is_ro G K C hC x hx y hy with ⟨w,dis_K⟩,
  exact ⟨w,walk_outside_is_contained G K C hC x y w hx hy dis_K⟩,
end

lemma ro_of_subconnected_disjoint (K : finset V) (P : set V) (dis : disjoint P K)
  (conn : subconnected G P) : ∀ x y ∈ P, reachable_outside G K x y :=
begin
  rintros x hx y hy,
  unfold reachable_outside,
  rcases conn x hx y hy with ⟨w,wgood⟩,
  use w,
  exact disjoint_coe.mp (set.disjoint_of_subset_left wgood dis).symm,
end

lemma of_subconnected_disjoint (K : finset V) (P : set V)
  (Pnempty : set.nonempty P)
  (dis : disjoint P K)
  (conn : simple_graph.subconnected G P) :
  ∃ C : set V, C ∈ ro_components G K ∧ P ⊆ C :=
of_ro_set G K P Pnempty (ro_component.ro_of_subconnected_disjoint G K P dis conn)



lemma adjacent_to (Gpc : G.preconnected) (K : finset V) (Knempty: K.nonempty) (C : set V) (hC : C ∈ ro_components G K) :
∃ (v k : V), k ∈ K ∧ v ∈ C ∧ G.adj k v :=
begin
  rcases Knempty with ⟨k,kK⟩,
  rcases nempty G K C hC with ⟨x,xC⟩,
  let w := (Gpc x k).some,
  have : k ∉ C, from not_in_comp_of_in G K C hC k kK,
  rcases walk.pred_adj_non_pred x k w  (λ x, x ∈ C) xC ‹k∉C› with ⟨u,v,adj,uC,vnC⟩,
  by_cases h : v ∈ K,
  { use [u,v,h,uC,adj.symm],},
  { have : v ∈ C, from mem_of_mem_of_adj G K C hC u v uC h adj,
    exfalso,
    exact vnC this,
  },
end

def bdry (K : finset V) : set V := {x : V | x ∉ K ∧ ∃ k ∈ K, G.adj x k}
lemma bdry_subset_union_neighbors (K : finset V) : (bdry G K: set V) ⊆ set.Union (λ x : K, G.neighbor_set x) :=
begin
  unfold bdry,
  rw set.subset_def,
  rintros x ⟨not_in_K,k,k_in_K,adj⟩,
  rw set.mem_Union,
  exact ⟨⟨k,k_in_K⟩,adj.symm⟩,
end

lemma bdry_finite [locally_finite G] (K : finset V) : (bdry G K).finite :=
begin
  apply set.finite.subset _ (bdry_subset_union_neighbors G K),
  apply set.finite.sUnion,
  apply set.finite_range,
  rintros nbd ⟨k,k_to_nbd⟩,
  simp only at k_to_nbd,
  rw k_to_nbd.symm,
  exact (neighbor_set G ↑k).to_finite, -- lol thanks library_search
end

def to_bdry_point (Gpc : G.preconnected) (K : finset V) (Knempty: K.nonempty) : ro_components G K → V :=
λ C, some $ adjacent_to G Gpc K Knempty C.val C.prop

def to_bdry_point_spec  (Gpc : G.preconnected) (K : finset V) (Knempty: K.nonempty) (C : ro_components G K) :
  let v := (to_bdry_point G Gpc K Knempty C) in ∃ k : V, k ∈ K ∧ v ∈ C.val ∧ G.adj k v :=
some_spec (adjacent_to G Gpc K Knempty C.val C.prop)

lemma to_bdry_point_inj (Gpc : G.preconnected) (K : finset V)  (Knempty: K.nonempty) :
  function.injective $ to_bdry_point G Gpc K Knempty :=
begin
  rintros C D c_eq_d,
  rcases to_bdry_point_spec G Gpc K Knempty C with ⟨k,kK,cC,k_adj_c⟩,
  rcases to_bdry_point_spec G Gpc K Knempty D with ⟨l,lK,dD,l_adj_d⟩,
  exact subtype.eq ( eq_of_common_mem G K C.val D.val C.prop D.prop _ cC (c_eq_d.symm ▸ dD)),
end

lemma to_bdry_point_in_bdry (Gpc : G.preconnected) (K : finset V) (Knempty: K.nonempty) :
  range (to_bdry_point G Gpc K Knempty) ⊆ bdry G K :=
begin
  rw set.subset_def,
  rintros _ ⟨C,rfl⟩,
  rcases to_bdry_point_spec G Gpc K Knempty C with ⟨k,kK,cC,k_adj_c⟩,
  have := not_in_of_in_comp G K C.val C.prop _ cC,
  exact ⟨this,⟨k,⟨kK,k_adj_c.symm⟩⟩⟩,
end

lemma finite [locally_finite G] (Gpc : G.preconnected) (K : finset V) : (ro_components G K).finite :=
begin
  by_cases Knempty : K.nonempty,
  { by_contra comps_inf,
    haveI : infinite (subtype (ro_components G K)), from infinite_coe_iff.mpr comps_inf,
    have := @set.infinite_range_of_injective (subtype (ro_components G K)) V (_inst) (to_bdry_point G Gpc K Knempty) (to_bdry_point_inj G Gpc K Knempty),
    have : (bdry G K).infinite, from set.infinite.mono (to_bdry_point_in_bdry G Gpc K Knempty) this,
    exact this (bdry_finite G K),},
  { rw [finset.not_nonempty_iff_eq_empty] at Knempty,
    apply set.subsingleton.finite,
    have components_eq_univ : ∀ C ∈ G.ro_components K, C = set.univ := by {
        rintros C ⟨v, hvC, hconn⟩,
        subst hconn,
        ext, simp,
        rcases (set.nonempty_def.mp (simple_graph.reachable_iff_nonempty_univ.mp (Gpc v x))) with ⟨w, hw⟩,
        use w, subst K, simp,},
    intros C₁ hC₁ C₂ hC₂,
    exact eq.trans (components_eq_univ C₁ hC₁) (eq.symm (components_eq_univ C₂ hC₂)),
  }
  -- If K is not nonempty, it is empty. This means, since G is assumed connected,
  -- that ro_components G K is just {G}, i.e. a singleton, hence finite
end

instance ro_components_fintype [locally_finite G] (Gpc : G.preconnected) (K : finset V) : fintype (ro_components G K) := set.finite.fintype (finite G Gpc K)

@[instance] lemma inf_ro_components_fintype [locally_finite G] (Gpc : G.preconnected) (K : finset V) : fintype (inf_ro_components G K) :=
@fintype.of_injective _ _ (ro_component.ro_components_fintype G Gpc K) (ι G K) (ι_inj G K)

/-A graph is the union of the part `K` and all the ro_components in its complement-/
lemma graph_eq_part_union_ro_comp (K : finset V) : ↑K ∪ (⋃₀ ro_components G K) = set.univ :=
begin
  ext,
  simp,
  by_cases x_in_K : x ∈ K,
  {tauto,},
  { right,
    have : ∀ (S : set V), x ∈ S ↔ {x} ⊆ S := by {simp at *},
    simp_rw this, apply of_subconnected_disjoint,
    {finish,},
    { tidy },
    { rw [subconnected], intros, simp at *, subst H, subst H_1, use walk.nil, finish, }}
end

def ro_of_ro_component (Gpc : G.preconnected) (K : finset V) (L : finset V) (K_sub_L : K ⊆ L) (D : set V) (D_comp : D ∈ ro_components G L) :
  ∀ x y ∈ D, reachable_outside G K x y :=
λ x xD y yD, reachable_outside.monotone G K_sub_L x y (ro_component.is_ro G L D D_comp x xD y yD)

lemma sub_ro_components_cover  (Gpc : G.preconnected) (K : finset V) (L : finset V) (K_sub_L : K ⊆ L) (C : set V) (hC : C ∈ ro_components G K) :
  C ⊆ L ∪ (⋃₀ { D : set V | D ∈ ro_components G L ∧ D ⊆ C}) :=
begin
  rintro x x_in_C,
  by_cases h: x∈L,
  { left,exact h},
  { right,
    let D := ro_component.of G L x,
    have : x ∈ D, from ro_component.mem_of G L x h,
    rw set.mem_sUnion,
    use D,
    split,
    { split,
      exact ro_component.of_in_components G L x h,
      let D_comp := ro_component.of_in_components G L x h,
      exact ro_component.sub_ro_component_of_ro_of_intersects G K D
        (ro_component.nempty G L D D_comp)
        (ro_of_ro_component G Gpc K L K_sub_L D D_comp)
        C hC ( set.nonempty_inter_iff_exists_left.mpr ⟨⟨x,‹x∈D›⟩,x_in_C⟩  : (D ∩ C).nonempty),
    },
    from ro_component.mem_of G L x h,
  }
end



lemma img_ro_of_ro_of_embedding {U : Type*} (H : simple_graph U) (K : finset V)
  (φ : G ↪g H) {v v' : V} :
G.reachable_outside K v v' → H.reachable_outside (image φ K) (φ v) (φ v') :=
begin
  rintros ⟨w,wgood⟩,
  use w.map (φ.to_hom),
  rw [walk.support_map,list.map_to_finset,←finset.disjoint_coe,finset.coe_image,finset.coe_image],
  rw ←finset.disjoint_coe at wgood,
  exact set.disjoint_image_of_injective (rel_embedding.injective φ) wgood,
end

lemma ro_iff_img_ro_of_isom {U : Type*} (H : simple_graph U) (K : finset V) (φ : G ≃g H) {v v' : V} :
  G.reachable_outside K v v' ↔ H.reachable_outside (image ⇑φ K) (φ v) (φ v') :=
begin
  split,
  { exact img_ro_of_ro_of_embedding G H K φ, },
  { rintros Hro,
    have : K = finset.image ⇑(φ.symm) (finset.image ⇑φ K), by {
      rw [←finset.coe_inj,finset.coe_image,finset.coe_image],
      apply eq.symm,
      apply equiv.symm_image_image,},
    rw this,
    have : v = (φ.symm) (φ v), by {simp only [rel_iso.symm_apply_apply],},
    rw this,
    have : v' = (φ.symm) (φ v'), by {simp only [rel_iso.symm_apply_apply],},
    rw this,
    exact img_ro_of_ro_of_embedding H G (image ⇑φ K) φ.symm Hro,
  }
end


lemma ro_component_to_ro_component_of_isom {U : Type*} (H : simple_graph U) (K : finset V)
  (φ : G ≃g H) :
  set.maps_to (λ C, φ '' C) (G.ro_components K) (H.ro_components (finset.image φ K)) :=
begin
  rw [set.maps_to'],
  intro S, simp, intro T,
  rintro ⟨v, hvT, hTconn⟩,
  intro himg, rw [← himg], clear himg,
  use φ v, refine ⟨set.mem_image_of_mem φ hvT, _⟩,
  ext, subst hTconn, simp,
  split,
  { rintro ⟨v', hreach, himg⟩, rw [← himg, ← ro_iff_img_ro_of_isom], assumption, },
  {
    have x_val : x = φ (φ.symm x) := by { apply eq.symm, apply rel_iso.apply_symm_apply,},
    rw [x_val],
    intro h,
    use φ.symm x,
    simp,
    rw [ro_iff_img_ro_of_isom], assumption,
  }
end

lemma bij_ro_components_of_isom {U : Type*} (H : simple_graph U) (K : finset V) (φ : G ≃g H) :
  set.bij_on (λ C, φ '' C) (G.ro_components K) (H.ro_components (finset.image φ K)) :=
  begin
    apply bij_on.mk,
    -- the remaining two parts should trivially follow from the fact that `φ` is a bijection
    {apply ro_component_to_ro_component_of_isom,},
    { intros C₁ hC₁ C₂ hC₂,
      simp, rw [set.image_eq_image], exact id,
      exact rel_iso.injective φ, },
    { rintros C ⟨x, hxC, hconnC⟩, -- this may be more low-level than it needs to be
      use φ⁻¹' C,
      split,
      {
        --use φ.symm x,
        sorry, -- this should probably be a lemma
      },
      {simp, rw [← set.eq_preimage_iff_image_eq], exact rel_iso.bijective φ,}
    }
  end





section inf_ro_components

lemma inf_ro_components_subset (Gpc : G.preconnected) (K : finset V) : inf_ro_components G K ⊆ ro_components G K := λ C h, h.1
lemma fin_ro_components_subset (Gpc : G.preconnected) (K : finset V) : fin_ro_components G K ⊆ ro_components G K := λ C h, h.1


lemma bij_inf_ro_components_of_isom {U : Type*} (H : simple_graph U) (K : finset V) (φ : G ≃g H) :
  set.bij_on (λ C, φ '' C) (G.inf_ro_components K) (H.inf_ro_components (finset.image φ K)) :=
begin
  sorry,
end
-- Should use bij_ro_components_of_isom plus the obvious fact that φ being a bijection, it preserves infinite-ness.
-- Some additional lemmas may be needed to make the above argument go through as is

@[instance] lemma infinite_graph_to_inf_components_nonempty [locally_finite G] (Gpc : G.preconnected) (K : finset V)  (Vinfinite : (@set.univ V).infinite) :
 nonempty (inf_ro_components G K) :=
begin
  by_contradiction,
  rw [not_nonempty_iff, inf_ro_components] at h,
  apply Vinfinite,
  rw [← graph_eq_part_union_ro_comp G K],
  apply set.finite.union,
  { exact (↑K : set V).to_finite,}, -- from library_search
  {
    apply set.finite.sUnion,
    { apply finite G Gpc,},
    { intros C hC,
      by_contradiction hCinf,
      rw [is_empty_iff] at h,
      apply h,
      split, split, all_goals {assumption},
    }
  }
  -- K is finite, hence its boundary too, and there can only be a finite number of ro_components
  -- if all are finite, then their union is finite, so that V is finite too
end

instance inf_components_finite [locally_finite G] (Gpc : G.preconnected) (K : finset V) : fintype (inf_ro_components G K) :=
(set.finite.subset (ro_component.finite G Gpc K) (inf_ro_components_subset G Gpc K)).fintype

lemma inf_components_finite' [locally_finite G] (Gpc : G.preconnected) (K : finset V) : fintype (inf_ro_components G K) :=
(set.finite.subset (ro_component.finite G Gpc K) (inf_ro_components_subset G Gpc K)).fintype




def extend_to_fin_ro_components [locally_finite G] (Gpc : G.preconnected) (K : finset V) : finset V :=
begin
let finite_pieces : set V := ⋃₀ fin_ro_components G K,
  have : set.finite finite_pieces, by {
    apply set.finite.sUnion,
    {exact set.finite.subset (ro_component.finite G Gpc K) (fin_ro_components_subset G Gpc K)},
    {rintros C Cgood, exact Cgood.2,}},
  exact K ∪ this.to_finset,
end

lemma extend_to_fin_ro_components.sub [locally_finite G]  (Gpc : G.preconnected) (K : finset V) :
K ⊆ extend_to_fin_ro_components G Gpc K := finset.subset_union_left _ _

lemma extend_to_fin_ro_components.ro  [locally_finite G] (Gpc : G.preconnected) (K : finset V):
  ro_components G (extend_to_fin_ro_components G Gpc K ) = inf_ro_components G K :=
begin
  let L := extend_to_fin_ro_components G Gpc K,
  apply set.ext,
  rintros C,
  split,
  { rintro C_L,
    /-
    C_L : C ∈ ro_components L
    Thus, C is connected (since it's a ro_component) and does not intersect L, hence does not intersect K.
    Therefore, C is contained in a unique D ∈ ro_components K.
    Since C does not intersect L, it does not intersect any D' ∈ ro_ K, hence cannot be contained in one.
    Hence, D ∈ ro_
   K.
    Let us show C = D. We already know C ⊆ D, remains the other inclusion.
    Fix some c ∈ C and any d ∈ D.
    There is a path w from c to d entirely contained in D, hence not intersecting any D' ∈ ro_ K, and not intersecting K either.#check
    w is therefore outside of K', which by definition means that `co_o c d`, and thus d lies in C.
    -/
    sorry,
  },
  { rintro C_K,
    /-
    C_K : C ∈ ro_
   K.
    Thus, C is connected, and disjoint from K and from any other C' ∈ ro_components K.
    In particular, C is disjoint from L, and, being connected, it is contained in a unique D ∈ ro_components L.
    Again, to show C = D, it suffices to choose some c ∈ C and show that any d ∈ D lies in C.
    Take a path w from c to d, entirely contained in D. By hypothesis, w does not intersect K, which implies that `co_o c d` and d lies in C.
    -/
    sorry,},
end

lemma extend_to_fin_ro_components.subconnected_of_subconnected [locally_finite G] (Gpc : G.preconnected)
  (K : finset V)
  (Knempty : K.nonempty)
  (Kconn : subconnected G K) :
  subconnected G (extend_to_fin_ro_components G Gpc K) :=
begin

  let k := Knempty.some,
  let KC' := (set.image (λ (C : set V), (K : set V) ∪ C) (fin_ro_components G K)),
  have : ↑(extend_to_fin_ro_components G Gpc K) = (K : set V) ∪ (⋃₀ KC'), by {
    apply set.ext,
    rintros x,
    split,
    { rintros xE,
      simp,
      simp at xE,
      unfold extend_to_fin_ro_components at xE,
      simp at xE,
      cases xE,
      { left, exact xE, },
      { right, rcases xE with ⟨C,Ccomp,xC⟩,use C,use Ccomp,right,exact xC, },
    },
    { rintros xC,
      simp,
      simp at xC,
      unfold extend_to_fin_ro_components,
      simp,
      cases xC,
      { left, exact xC },
      { rcases xC with ⟨C,Ccomp,hh⟩, cases hh, {left,exact hh}, {right, use C, use Ccomp,exact hh} },

    },
  },
  have conn : ∀ C ∈ KC', subconnected G C, by {
    rintros C hC,
    simp at hC,
    rcases hC with ⟨CC,⟨CComp,Cfin⟩,rfl⟩,
    apply subconnected.of_adj_subconnected G Kconn (to_subconnected G K CC CComp),
    let d := ro_component.to_bdry_point G Gpc K Knempty ⟨CC,CComp⟩,
    rcases ro_component.to_bdry_point_spec G Gpc K Knempty ⟨CC,CComp⟩ with ⟨k,kK,dC,adj⟩,
    use [k,kK,d,dC,adj],
  },
  rw this,
  by_cases KC'.nonempty,
  { apply subconnected.of_intersecting_subconnected G Kconn,
    { apply subconnected.of_common_mem_sUnion G k _ conn,
      rintros C ⟨CC,⟨CComp,Cfin⟩,rfl⟩,
      simp,
      left,
      exact Knempty.some_spec,
    },
    { apply set.not_disjoint_iff.mpr,
      refine ⟨k,⟨Knempty.some_spec,_⟩⟩,
      simp,
      rcases h.some_spec with ⟨C,lol,lal⟩,
      use C,
      use lol,
      left,
      exact Knempty.some_spec,
    }
  },
  { rw set.not_nonempty_iff_eq_empty at h, rw h, simp, exact Kconn, }
end


def extend_subconnected_to_fin_ro_components [locally_finite G] (Gpc : G.preconnected) (K : finset V) (Knempty : K.nonempty)
  (Kconn : subconnected G K ) :
  {K' : finset V | K ⊆ K' ∧ (subconnected G K') ∧ (∀ C : ro_components G K', C.val.infinite) } :=
begin
  use extend_to_fin_ro_components G Gpc K,
  use extend_to_fin_ro_components.sub G Gpc K,
  use extend_to_fin_ro_components.subconnected_of_subconnected G Gpc K Knempty Kconn,
  rintros ⟨C,CK'⟩,
  rw extend_to_fin_ro_components.ro G Gpc K at CK',
  exact CK'.2,
end


def extend_to_subconnected [locally_finite G]  (Gpc : G.preconnected) (K : finset V) (Vnempty : nonempty V) :
  {K' : finset V | K ⊆ K' ∧ subconnected G K' } :=
begin
  let v₀ : V := Vnempty.some,
  let path_to_v₀ := λ (k : V), (Gpc k v₀).some.support.to_finset,
  let path_to_v₀' := λ (k : V), ((Gpc k v₀).some.support.to_finset : set V),
  let K' := finset.bUnion K path_to_v₀,
  use K',
  split,
  { rintros k kK,
    apply finset.mem_bUnion.mpr,
    use [k,kK],
    simp only [list.mem_to_finset, start_mem_support],},
  { let K'' := ⋃₀ (path_to_v₀' '' K),
    have : ↑K' = K'', by {
      simp only [coe_bUnion, mem_coe],
      simp only [*, sUnion_image, mem_coe],
    },
    rw this,
    apply subconnected.of_common_mem_sUnion G v₀ _ _,
    { rintros S ⟨k,kK,rfl⟩, simp,},
    { rintros S ⟨k,kK,rfl⟩, simp *, apply subconnected.of_walk,},
  },
end







end inf_ro_components

end ro_component


end simple_graph
