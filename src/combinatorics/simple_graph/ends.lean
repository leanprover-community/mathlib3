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


namespace refl_gen

open relation
open relation.refl_gen

variables {α : Type*} {r : α → α → Prop} {s : α → α → Prop}

@[protected]
lemma reflexive : reflexive (refl_gen r) := λ x, refl_gen.refl

@[protected]
lemma symmetric (h : symmetric r) : symmetric (refl_gen r)
| x _ refl_gen.refl := refl_gen.refl
| x y (single rr) := single (h rr)

@[protected]
lemma transitive (h :transitive r) : (transitive (refl_gen r))
| x _ z refl_gen.refl ss := ss
| x y _ rr refl_gen.refl := rr
| x y z (single rr) (single ss) := single (h rr ss)

@[protected]
lemma monotone (mon : ∀ x y, r x y → s x y) : (∀ x y, refl_gen r x y → refl_gen s x y)
| x _ refl_gen.refl := refl_gen.refl
| x y (single rr) := single (mon x y rr)

end refl_gen

noncomputable theory

--local attribute [instance] prop_decidable

namespace simple_graph

section ends

parameters {V : Type u}
           {G : simple_graph V}
           (is_conn : ∀ x y : V, nonempty (walk G x y))
           [has_inter (finset V)]
           [decidable_eq  V]
           [has_compl V]
           [locally_finite G]

def connected_outside (K : set V) (x y : V) : Prop :=
  ∃ w : walk G x y, disjoint K w.support.to_finset

namespace connected_outside

lemma monotone {K K' : set V} (hK : K ⊆ K') (x y : V) :
  connected_outside K' x y → connected_outside K x y :=
λ ⟨w,dis⟩, ⟨w,disjoint_of_subset_left hK dis⟩

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
  {exact disxy},
  { have : ↑(yz.support.tail.to_finset) ⊆ ↑(yz.support.to_finset), by
    { rw walk.support_eq_cons, simp, rw finset.coe_insert, exact set.subset_insert y (↑(yz.support.tail.to_finset)),},
    apply @set.disjoint_of_subset_right V K ↑(yz.support.tail.to_finset) ↑(yz.support.to_finset) this,
    exact disyz,}
end

@[protected]
lemma refl {K : set V} (x : V) (x ∉ K) : connected_outside K x x :=
⟨walk.nil, by { rw [walk.support_nil,list.to_finset_cons,list.to_finset_nil],simpa}⟩


lemma not_K_outside  {K : set V} (x : V) (k ∈ K) : ¬ connected_outside K x k :=
begin
  rintros ⟨xx,disxx⟩,
  have : k ∈ ↑(xx.support.to_finset),
    by {rw [mem_coe, list.mem_to_finset], apply walk.end_mem_support},
  have : k ∈ K ∩ ↑(xx.support.to_finset), by simpa,
  rw set.disjoint_iff_inter_eq_empty at disxx,
  apply set.not_mem_empty k,
  rw ←disxx,
  simpa,
end

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
        sorry, -- Should be simple: shorter_walk is shorter, contradicting minimality
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

end connected_outside

end ends



end simple_graph
