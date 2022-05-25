import .misc 
import tactic
import algebra.big_operators.finprod 
import set_theory.cardinal.finite
import logic.equiv.fin

open_locale classical big_operators
noncomputable theory 

--lemma finset.card_coe_sort {α : Type*}[fintype α] (s : set α):
--  fintype.card (↥s) = set.to_finset_card


variables {V E : Type*} {u v w x y : V} {e f g : E} {i j : fin 2}

structure digraph (V E : Type*) :=
  (ends : fin 2 → E → V)

namespace digraph

variable {G : digraph V E}

section basic 

def head (G : digraph V E) (e : E) : V := 
  G.ends 0 e 

def tail (G : digraph V E) (e : E) : V := 
  G.ends 1 e 

def dir_adj (G : digraph V E) (u v : V) : Prop := 
  ∃ e : E, G.ends 0 e = u ∧ G.ends 1 e = v 

def inc (G : digraph V E)(v : V)(e : E) : Prop := 
  ∃ i, G.ends i e = v

def other_end (G : digraph V E)(u : V)(e : E) : V := 
  if G.ends 0 e = u then G.ends 1 e else if G.ends 1 e = u then G.ends 0 e else u 
  
def is_loop (G : digraph V E)(e : E) : Prop := 
  G.ends 0 e = G.ends 1 e

def ends_set (G : digraph V E)(e : E) : set V := 
  {G.ends 0 e, G.ends 1 e}

def ends_finset (G : digraph V E) (e : E) : finset V := 
  {G.ends 0 e, G.ends 1 e}

def dir_edge_nhd (G : digraph V E)(i : fin 2)(v : V) : set E := 
  {e : E | G.ends i e = v}

def in_edge_nhd (G : digraph V E)(v : V) : set E := 
  G.dir_edge_nhd 0 v 

def out_edge_nhd (G : digraph V E)(v : V) : set E := 
  G.dir_edge_nhd 1 v

def edge_nhd (G: digraph V E)(v : V) : set E := 
  ⋃ (i : fin 2), (G.dir_edge_nhd i v) 

def loops_at (G : digraph V E) (v : V) : set E := 
  ⋂ (i : fin 2), (G.dir_edge_nhd i v)

def adj (G: digraph V E)(u v : V) : Prop := 
  ∃ e i, G.ends i e = u ∧ G.ends (i+1) e = v   

class finite_at (G : digraph V E) (v : V) := 
  (fin : ∀ (i : fin 2), fintype (G.dir_edge_nhd i v))

class locally_finite (G : digraph V E) := 
  (fins : ∀  (v : V), G.finite_at v)

instance [G.finite_at v] : fintype (G.dir_edge_nhd i v) := 
  finite_at.fin i

instance loc_fin [locally_finite G] : G.finite_at v := 
  locally_finite.fins v 

instance [G.finite_at v]: fintype (G.edge_nhd v) := 
  set.fintype_Union (λ i, dir_edge_nhd G i v)

instance [G.finite_at v]: fintype (G.loops_at v) := 
  set.fintype_subset _ (set.Inter_subset (λ i, dir_edge_nhd G i v) 0)

instance finite_at_of_fintype [fintype E] : G.finite_at v := 
  ⟨λ v, infer_instance⟩

instance loc_finite_of_fintype [fintype E] : locally_finite G := 
  ⟨λ v, infer_instance⟩

lemma dir_edge_nhd_finite_of_locally_finite (G : digraph V E) [locally_finite G] (i : fin 2) (v : V):
  (G.dir_edge_nhd i v).finite := 
set.finite.intro (infer_instance)  

instance finite_at_of_edge_nhd_finite (h : (G.edge_nhd v).finite) : G.finite_at v :=
  { fin := λ i, @set.fintype_subset _ (G.edge_nhd v) _ h.fintype _ (set.subset_Union _ _)}  

def dir_edge_nhd_finset (G : digraph V E) (i : fin 2) (v : V) [G.finite_at v]  : finset E := 
  (G.dir_edge_nhd i v).to_finset 

def in_edge_nhd_finset (G : digraph V E) (v : V) [G.finite_at v] : finset E := 
  G.dir_edge_nhd_finset 0 v

def out_edge_nhd_finset (G : digraph V E) (v : V) [G.finite_at v]: finset E := 
  G.dir_edge_nhd_finset 1 v

def edge_nhd_finset (G: digraph V E) (v : V) [G.finite_at v] : finset E := 
  (G.edge_nhd v).to_finset 

def loops_at_finset (G : digraph V E) (v : V) [G.finite_at v] : finset E := 
  (G.loops_at v).to_finset 

def nhd (G : digraph V E)(u : V) : set V := 
  {v : V | G.adj u v}

def nhd_finset (G : digraph V E)(u : V)[fintype (G.nhd v)] : finset V := 
  (G.nhd v).to_finset 

lemma is_loop_def:
  G.is_loop e ↔ G.ends 0 e = G.ends 1 e :=
iff.rfl 

lemma adj_def:
  G.adj u v ↔ ∃ e i, G.ends i e = u ∧ G.ends (i+1) e = v   :=
iff.rfl 

lemma inc_def {G : digraph V E} {v : V} {e : E}: 
  G.inc v e ↔ ∃ i, G.ends i e = v := 
iff.rfl 

lemma dir_edge_nhd_def (G : digraph V E) (i : fin 2) (v : V):
  G.dir_edge_nhd i v = {e : E | G.ends i e = v} := 
rfl 

lemma edge_nhd_def (G : digraph V E) (v : V):
  G.edge_nhd v = ⋃ (i : fin 2), (G.dir_edge_nhd i v) := 
rfl 

lemma loops_at_def (G : digraph V E) (v : V):
  G.loops_at v = ⋂ (i : fin 2), (G.dir_edge_nhd i v) :=
rfl 

lemma dir_edge_nhd_finset_def [G.finite_at v]:
  G.dir_edge_nhd_finset i v = (G.dir_edge_nhd i v).to_finset :=
rfl 

lemma edge_nhd_finset_def [G.finite_at v]:
  G.edge_nhd_finset v = (G.edge_nhd v).to_finset :=
rfl 

lemma loops_at_finset_def [G.finite_at v]:
  G.loops_at_finset v = (G.loops_at v).to_finset :=
rfl 

@[simp] lemma edge_nhd_eq_union : 
  G.edge_nhd v = G.dir_edge_nhd 0 v ∪ G.dir_edge_nhd 1 v := 
by {ext, rw [set.mem_union, edge_nhd_def, set.mem_Union, fin.exists_fin_two]}

@[simp] lemma loops_at_eq_inter :
  G.loops_at v = G.dir_edge_nhd 0 v ∩ G.dir_edge_nhd 1 v :=
by {ext, rw [set.mem_inter_iff, loops_at_def, set.mem_Inter, fin.forall_fin_two] }

lemma is_loop_of_mem_loops_at :
  e ∈ G.loops_at v → G.is_loop e := 
begin
  simp_rw [is_loop_def, loops_at_def, set.mem_Inter, dir_edge_nhd_def, set.mem_set_of], 
  exact λ h, by rw [h 0, h 1], 
end 

lemma mem_loops_at_iff_is_loop_inc : 
  e ∈ G.loops_at v ↔ G.is_loop e ∧ G.inc v e :=
begin
  refine ⟨λ h, ⟨is_loop_of_mem_loops_at h, _⟩, λ h, _⟩, 
  { rw [loops_at_def, set.mem_Inter] at h,    
    simp_rw [dir_edge_nhd_def, set.mem_set_of] at h, 
    exact ⟨0, by rw [h 0]⟩}, 
  simp_rw [loops_at_def, set.mem_Inter, fin.forall_fin_two, dir_edge_nhd_def, set.mem_set_of], 
  cases h with h1 h2, 
  rw [inc_def, fin.exists_fin_two, is_loop_def.mp h1, or_self] at h2, 
  rwa [is_loop_def.mp h1, and_self], 
end 


lemma adj_iff_nhd_inter (huv : u ≠ v): 
  G.adj u v ↔ ((G.edge_nhd u) ∩ (G.edge_nhd v)).nonempty := 
begin
  refine ⟨λ h, _, λ h, _⟩, 
  { rcases h with ⟨e,⟨i,hi1,hi2⟩⟩, 
    exact ⟨e, set.mem_inter (set.mem_Union.mpr ⟨i,set.mem_set_of.mpr hi1⟩) (set.mem_Union.mpr ⟨i+1,set.mem_set_of.mpr hi2⟩)⟩}, 
  cases h with e he, 
  rw [set.mem_inter_iff, edge_nhd_def, edge_nhd_def, set.mem_Union, set.mem_Union] at he, 
  rcases he with ⟨⟨iu,hu⟩,⟨iv,hv⟩⟩, 
  rw [dir_edge_nhd_def, set.mem_set_of] at hu hv, 
  refine ⟨e,iu,hu,_⟩, 
  cases fin.fin_two_eq_or_eq_add_one iv iu, 
  { exact false.elim (huv (by rw [←hu, ←hv, h]))},
  rw [←h, ←hv], 
end 

lemma adj_self_iff_exists_loop :
  G.adj u u ↔ (G.loops_at u).nonempty := 
begin
  refine ⟨λ h, _, λ h, _⟩, 
  { rcases h with ⟨e, ⟨i,h1,h2⟩⟩, 
    refine ⟨e, mem_loops_at_iff_is_loop_inc.mpr ⟨_,set.mem_set_of.mpr ⟨i, h1⟩⟩⟩,
    rw is_loop_def,
    cases fin.zero_or_one_of_fin_two i,  
      { subst h, rw h1, exact h2.symm,},
      subst h, rw h1, exact h2, 
  },
  cases h with e h, 
  rw [mem_loops_at_iff_is_loop_inc, is_loop_def, inc_def] at h, 
  refine ⟨e, 0, _⟩, 
  rcases h with ⟨h1, ⟨j, h2⟩⟩, 
  cases fin.zero_or_one_of_fin_two j with h, 
  { subst h, 
    rw [h1, zero_add, ←h2, h1, and_self]},
  subst h, 
  rw [h1, zero_add, h2, and_self], 
end 

lemma adj_symm (u v : V) :
  G.adj u v → G.adj v u := 
begin
  by_cases u = v, 
  { subst h, exact id},
  rw [adj_iff_nhd_inter h, adj_iff_nhd_inter (ne.symm h), set.inter_comm], 
  exact id, 
end


lemma ends_adj (e : E):
  G.adj (G.ends 0 e) (G.ends 1 e) :=
⟨e,0,⟨rfl,rfl⟩⟩

lemma ends_adj' (e : E) (i : fin 2):
  G.adj (G.ends i e) (G.ends (i + 1) e) := 
begin
  cases fin.zero_or_one_of_fin_two i with h, 
  { subst h, apply ends_adj},
  subst h, 
  exact adj_symm _ _ (ends_adj _), 
end 


lemma edge_nhd_eq_in_edge_nhd_union_out_edge_nhd (G : digraph V E)(v : V):
  (G.edge_nhd v) = G.in_edge_nhd v ∪ G.out_edge_nhd v := 
begin
  ext x, 
  unfold edge_nhd in_edge_nhd out_edge_nhd, 
  simp only [set.mem_Union, set.mem_union_eq], apply fin.exists_fin_two, 
end 

lemma dir_nhds_pairwise_disjoint (G : digraph V E)(i : fin 2): 
  (set.univ : set V).pairwise_disjoint (λ v, G.dir_edge_nhd i v) := 
begin
  refine λ x _ y _ hxy e he, false.elim _, 
  dsimp [dir_edge_nhd] at he, 
  rw [←he.1, ←he.2] at hxy, 
  exact hxy rfl, 
end 

lemma Union_dir_nhds_eq_univ (G : digraph V E)(i : fin 2):
  (⋃ (x : V), (G.dir_edge_nhd i x : set E)) = set.univ := 
set.Union_eq_univ_iff.mpr (λ e, ⟨G.ends i e, set.mem_set_of.mpr rfl⟩)
  
lemma sUnion_dir_nhds_eq_univ (G : digraph V E)(i : fin 2):
  ⋃₀ ((G.dir_edge_nhd i) '' set.univ) = (set.univ : set E) := 
set.sUnion_eq_univ_iff.mpr (λ e, ⟨G.dir_edge_nhd i (G.ends i e), by {simp only [dir_edge_nhd, set.mem_image, 
                                                                      set.mem_univ, true_and, exists_apply_eq_apply, set.mem_set_of_eq], } ⟩ ) 

lemma other_end_def (v : V) (e : E):
  G.other_end v e = if G.ends 0 e = v then G.ends 1 e else if G.ends 1 e = v then G.ends 0 e else v  :=
rfl 

lemma other_end_idem (v : V) (e : E):
  G.other_end (G.other_end v e) e = v := 
begin
  simp_rw digraph.other_end, 
  split_ifs, 
    rwa ←h_1,  
    assumption, 
    assumption, 
    refl, 
end 

lemma other_end_eq (e : E) (i : fin 2): 
  G.other_end (G.ends i e) e = G.ends (i+1) e := 
begin
  rw [other_end_def], 
  cases fin.zero_or_one_of_fin_two i, 
  { subst h, simp}, 
  subst h, simp only [eq_self_iff_true, if_true], 
  split_ifs, 
  { rw ← h, refl,},
  refl,
end 

lemma other_end_adj (hve : G.inc u e):
  G.adj u (G.other_end u e) :=
by {cases hve with i h, rw [← h, other_end_eq],  apply ends_adj'}


lemma edge_nhd_eq_inc (G : digraph V E) (v : V):
  G.edge_nhd v = {e | G.inc v e} :=
begin
  rw [edge_nhd_eq_union, dir_edge_nhd_def, dir_edge_nhd_def], 
  ext, 
  simp [inc_def, fin.exists_fin_two], 
end 

lemma dir_edge_nhd_subset_edge_nhd (G : digraph V E)(i : fin 2)(v : V):
  G.dir_edge_nhd i v ⊆ G.edge_nhd v := 
set.subset_Union (λ j, G.dir_edge_nhd j v) i

lemma loops_at_subset_dir_edge_nhd (G : digraph V E)(i : fin 2)(v : V):
  G.loops_at v ⊆ G.dir_edge_nhd i v := 
set.Inter_subset _ _

lemma loops_at_subset_edge_nhd (G : digraph V E)(v : V):
  G.loops_at v ⊆ G.edge_nhd v :=
subset_trans (G.loops_at_subset_dir_edge_nhd 0 v) (G.dir_edge_nhd_subset_edge_nhd 0 v)

lemma ends_set_nonempty(G : digraph V E)(e : E):
  (G.ends_set e).nonempty :=
by simp [ends_set] 

lemma ends_finset_nonempty(G : digraph V E)(e : E):
  (G.ends_finset e).nonempty :=
by simp [ends_finset, ends_set] 

lemma card_ends_finset_le_two (G : digraph V E)(e : E): 
  (G.ends_finset e).card ≤ 2 := 
by {simp only [ends_finset, ends_set, set.insert_to_finset], apply finset.card_insert_le}

lemma card_ends_finset_pos (G : digraph V E)(e : E): 
  0 < (G.ends_finset e).card :=
finset.nonempty.card_pos (G.ends_finset_nonempty e) 

lemma card_ends_finset_eq_one_of_loop (h : G.is_loop e):
  (G.ends_finset e).card = 1 :=
by {rw is_loop at h, rw [ends_finset,h,finset.pair_self_eq, finset.card_singleton], }

lemma loop_of_card_ends_finset_eq_one (h : (G.ends_finset e).card = 1): 
  G.is_loop e := 
by {rw [is_loop], by_contradiction h', rw [ends_finset, finset.card_doubleton h'] at h, linarith}

lemma card_ends_finset_eq_one_iff_loop:
  G.is_loop e ↔ (G.ends_finset e).card = 1 := 
⟨card_ends_finset_eq_one_of_loop, loop_of_card_ends_finset_eq_one⟩

lemma card_ends_finset_eq_two_of_nonloop (h : ¬(G.is_loop e)):
  (G.ends_finset e).card = 2 := 
begin
  have := nat.lt_of_le_and_ne (nat.add_one_le_iff.mpr (G.card_ends_finset_pos e)), 
  rw [nat.zero_add, ne_comm] at this, 
  linarith [this (λ h', h (loop_of_card_ends_finset_eq_one h')), G.card_ends_finset_le_two e], 
end 

lemma nonloop_of_card_ends_finset_eq_two (h : (G.ends_finset e).card = 2):
  ¬G.is_loop e := 
begin
  rw is_loop, intro h_loop, 
  rw [ends_finset, h_loop] at h, 
  simp only [finset.pair_self_eq, finset.card_singleton, nat.one_ne_bit0] at h, 
  assumption, 
end

lemma card_ends_finset_eq_two_iff_nonloop:
  (G.ends_finset e).card = 2 ↔ ¬ G.is_loop e :=
⟨nonloop_of_card_ends_finset_eq_two, card_ends_finset_eq_two_of_nonloop⟩ 

end basic

section degree

def dir_deg (G : digraph V E) (i : fin 2) (v : V) : ℕ := 
  nat.card (G.dir_edge_nhd i v)

def in_deg (G : digraph V E) (v : V) : ℕ := 
  G.dir_deg 0 v

def out_deg (G : digraph V E) (v : V) : ℕ := 
  G.dir_deg 1 v

def deg (G : digraph V E)(v : V) : ℕ := 
  nat.card ((G.dir_edge_nhd 0 v) ⊕ (G.dir_edge_nhd 1 v))

lemma dir_deg_def (G : digraph V E) (i : fin 2) (v : V) :
  G.dir_deg i v = nat.card (G.dir_edge_nhd i v) := 
rfl 

lemma deg_def (G : digraph V E)(v : V)[G.finite_at v]:
  G.deg v = G.dir_deg 0 v + G.dir_deg 1 v := 
by simp [deg, dir_deg]

lemma dir_deg_eq_finset_card (G: digraph V E) (i : fin 2) (v : V) [G.finite_at v] :
  G.dir_deg i v = (G.dir_edge_nhd_finset i v).card :=
begin
  unfold dir_deg dir_edge_nhd_finset, 
  rw [nat.card_eq_fintype_card, eq_comm, set.to_finset_card], 
end 

lemma deg_eq_sum_card_nhd_card_loops (G : digraph V E) (v : V) [G.finite_at v] :
  G.deg v = (G.edge_nhd_finset v).card + (G.loops_at_finset v).card :=
begin
  rw [deg_def, dir_deg_eq_finset_card, dir_deg_eq_finset_card, eq_comm],
  convert finset.card_union_add_card_inter _ _, 
  rw [edge_nhd_finset_def, dir_edge_nhd_finset_def, dir_edge_nhd_finset_def, 
      ←set.to_finset_union, set.to_finset_inj, edge_nhd_eq_union], 
  rw [loops_at_finset_def, dir_edge_nhd_finset_def, dir_edge_nhd_finset_def, 
    ←set.to_finset_inter, set.to_finset_inj, loops_at_eq_inter], 
end 

def deg_eq_zero_of_edge_nhd_infinite (h : (G.edge_nhd v).infinite): 
  G.deg v = 0 :=
begin
  apply @nat.card_eq_zero_of_infinite _ _, 
  rw [infinite_sum, set.infinite_coe_iff, set.infinite_coe_iff], 
  rwa [edge_nhd, fin.Union_fin_two, set.infinite_union] at h, 
end 


--lemma deg_ (G : digraph V E) (v : V):
  

variables [fintype V][fintype E]

lemma dir_handshake (G : digraph V E) (i : fin 2): 
  ∑ᶠ (v : V), (G.dir_deg i v) = fintype.card E := 
begin
  simp_rw dir_deg_def, 
  rw [←finsum_mem_univ, eq_comm],  
  convert @finsum_mem_bUnion _ _ _ _ 1 _ _ (G.dir_nhds_pairwise_disjoint i) set.finite_univ (λ x hx, set.finite.of_fintype _), 
  { convert (finsum_mem_ones_eq_card _).symm,
    simp only [finsum_mem_ones_eq_card, nat.card_eq_fintype_card, ←finset.card_univ, set.bUnion_univ, G.Union_dir_nhds_eq_univ, 
      ←set.to_finset_card, set.to_finset_univ],
  },
  simp only [pi.one_apply, finsum_mem_ones_eq_card], 
end 

theorem handshake (G : digraph V E): 
  ∑ᶠ (v : V), G.deg v = 2 * (fintype.card E) := 
begin
  simp_rw deg_def, 
  rw [finsum_add_distrib (set.finite.of_fintype _) (set.finite.of_fintype _), dir_handshake, dir_handshake, ←two_mul];
  apply_instance, 
end 
  
end degree


section reorientation 

variables {G₁ G₂ G₃ : digraph V E}

def orientation_equiv (G G' : digraph V E) : Prop := 
  ∀ (e : E), ∃ (φ : fin 2 ≃ fin 2), ∀ (i : fin 2), G.ends i e = G'.ends (φ i) e 

infix `~` := orientation_equiv

lemma orientation_equiv.refl: 
  ∀ G : digraph V E, G ~ G := 
λ G e, ⟨1, λ i, rfl⟩

lemma orientation_equiv.symm: 
  ∀ G₁ G₂ : digraph V E, G₁ ~ G₂ → G₂ ~ G₁ := 
begin
  intros G₁ G₂ h e, 
  cases h e with φ hφ, 
  exact ⟨φ.symm, λ i, by rw [hφ, equiv.apply_symm_apply]⟩
end 

lemma orientation_equiv.trans: 
  ∀ G₁ G₂ G₃ : digraph V E, G₁ ~ G₂ → G₂ ~ G₃ → G₁ ~ G₃ :=
begin
  rintros G₁ G₂ G₃ h h' e, 
  cases h e with φ hφ, 
  cases h' e with φ' hφ', 
  exact ⟨φ.trans φ', λ i, by rw [equiv.coe_trans, function.comp_app, hφ, hφ']⟩, 
end  

lemma is_equivalence (V E : Type*) : 
  equivalence (@orientation_equiv V E) := 
mk_equivalence 
  (@orientation_equiv V E)
  (@orientation_equiv.refl V E) 
  (@orientation_equiv.symm V E)
  (@orientation_equiv.trans V E)


lemma orientation_equiv_iff_shift :
  G₁ ~ G₂ ↔ ∀ e, ∃ j, ∀ i, G₁.ends i e  = G₂.ends (i+j) e :=
begin
  refine ⟨λ h e, _,  λ h e, _⟩, 
  { cases h e with φ hφ, 
    cases equiv.eq_add_of_equiv_fin_two φ with j hj, 
    exact ⟨j, λ i, by rw [← hj i, ← hφ i]⟩},
  cases h e with j hj, 
  cases fin.zero_or_one_of_fin_two j with hj_eq hj_eq, 
  { subst hj_eq, 
    exact ⟨equiv.refl (fin 2), λ i, by simp [hj]⟩}, 
  subst hj_eq, 
  exact ⟨fin_rotate 2, (λ i, by simp [hj])⟩, 
end 


lemma inc_respects: 
  G₁ ~ G₂ → G₁.inc = G₂.inc := 
begin
  refine λ h, funext (λ v, funext (λ e, iff_iff_eq.mp _)), 
  cases orientation_equiv_iff_shift.mp h e with j hj, 
  simp_rw [inc_def, hj], 
  refine ⟨λ h, _, λ h, _⟩, 
  { cases h with i hi, 
    exact ⟨i+j, by assumption⟩},
  cases h with i hi, 
  exact ⟨i-j, by simp [←hi]⟩, 
end 

lemma is_loop_respects:
  G₁ ~ G₂ → G₁.is_loop = G₂.is_loop :=
begin
  refine λ h, funext (λ e, iff_iff_eq.mp _), 
  cases orientation_equiv_iff_shift.mp h e with j hj, 
  rw [is_loop_def, is_loop_def, hj 0, hj 1], 
  cases fin.zero_or_one_of_fin_two j with hj hj, 
  { subst hj, tauto,},
  subst hj, tauto, 
end

lemma edge_nhd_respects:
  G₁ ~ G₂ → G₁.edge_nhd = G₂.edge_nhd :=
λ h, funext (λ x, by simp_rw [edge_nhd_eq_inc, inc_respects h])
  
lemma loops_at_respects:
  G₁ ~ G₂ → G₁.loops_at = G₂.loops_at :=
λ h, funext (λ v, set.ext (λ e, by simp_rw [mem_loops_at_iff_is_loop_inc, is_loop_respects h, inc_respects h])) 
   
lemma adj_of_adj_equiv (u v : V): 
  G₁ ~ G₂ → G₁.adj u v → G₂.adj u v := 
begin
  refine classical.by_cases (λ huv : (u = v), λ h h', _) (λ huv : (u ≠ v), λ h h', _) ,  
  { subst huv,
    rw adj_self_iff_exists_loop at h' ⊢, 
    cases h' with e he, 
    refine ⟨e,_⟩, 
    rw [mem_loops_at_iff_is_loop_inc] at he ⊢, 
    rwa [←is_loop_respects h, ←inc_respects h]},
  rw adj_iff_nhd_inter huv at h' ⊢,
  rwa [←edge_nhd_respects h], 
end 

lemma adj_respects:
  G₁ ~ G₂ → G₁.adj = G₂.adj := 
begin
  intro h, 
  ext x y, 
  split; apply digraph.adj_of_adj_equiv, 
  assumption, 
  apply orientation_equiv.symm, 
  assumption, 
end 

lemma other_end_respects:
  G₁ ~ G₂ → G₁.other_end = G₂.other_end := 
begin
  refine (λ h, funext (λ v, funext (λ e, _))), 
  cases orientation_equiv_iff_shift.mp h e with j hj, 
  simp_rw [other_end_def, hj, zero_add],
  cases fin.zero_or_one_of_fin_two j with hj hj;
  simp only [hj, fin.fin_two_one_add_one], 
  split_ifs, 
  all_goals {try {refl}}, 
  { rw [add_zero] at h_2, 
    rw [eq_comm, ite_eq_iff],
    tauto  },
  split_ifs, 
  all_goals {try {refl}},
  { rw [h_1, h_2] },
  rw [eq_comm, ite_eq_iff], 
  tauto, 
end 

lemma deg_respects:
  G₁ ~ G₂ → G₁.deg = G₂.deg := 
begin
  refine (λ h, funext (λ v, _)), 
  cases @set.finite_or_infinite _ (G₁.edge_nhd v) with hfin hinf,
  { haveI := digraph.finite_at_of_edge_nhd_finite hfin, 
    rw edge_nhd_respects h at hfin, 
    haveI := digraph.finite_at_of_edge_nhd_finite hfin, 
    simp_rw [deg_eq_sum_card_nhd_card_loops, edge_nhd_finset_def, loops_at_finset_def, edge_nhd_respects h, loops_at_respects h], }, 
  have hinf2 := hinf,
  rw [edge_nhd_respects h] at hinf2,
  rw [deg_eq_zero_of_edge_nhd_infinite hinf, deg_eq_zero_of_edge_nhd_infinite hinf2],  
end 

end reorientation

end digraph





 

