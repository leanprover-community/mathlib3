import .misc
import tactic
import algebra.big_operators.finprod
import set_theory.cardinal.finite
import logic.equiv.fin

open_locale classical big_operators
noncomputable theory

universes u v w

variables {V : Type u}{E : Type v} {x y z : V} {e f g : E} {i j : fin 2}

structure digraph (V : Type u)(E : Type v) :=
  (ends : fin 2 → E → V)

namespace digraph

variable {G : digraph V E}

section basic

def head (G : digraph V E) (e : E) : V :=
  G.ends 0 e

def tail (G : digraph V E) (e : E) : V :=
  G.ends 1 e

def dir_adj (G : digraph V E) (x y : V) : Prop :=
  ∃ e : E, G.ends 0 e = x ∧ G.ends 1 e = y

def inc (G : digraph V E)(x : V)(e : E) : Prop :=
  ∃ i, G.ends i e = x

def other_end (G : digraph V E) (x : V) (e : E) : V :=
  if G.ends 0 e = x then G.ends 1 e else if G.ends 1 e = x then G.ends 0 e else x

def is_loop (G : digraph V E) (e : E) : Prop :=
  G.ends 0 e = G.ends 1 e

def ends_set (G : digraph V E) (e : E) : set V :=
  {x : V | G.inc x e}

def ends_finset (G : digraph V E) (e : E) : finset V :=
  {G.ends 0 e, G.ends 1 e}

def dir_edge_nhd (G : digraph V E) (i : fin 2) (x : V) : set E :=
  {e : E | G.ends i e = x}

def in_edge_nhd (G : digraph V E) (x : V) : set E :=
  G.dir_edge_nhd 0 x

def out_edge_nhd (G : digraph V E)(x : V) : set E :=
  G.dir_edge_nhd 1 x

def edge_nhd (G: digraph V E)(x : V) : set E :=
  ⋃ (i : fin 2), (G.dir_edge_nhd i x)

def loops_at (G : digraph V E) (x : V) : set E :=
  ⋂ (i : fin 2), (G.dir_edge_nhd i x)

def adj (G: digraph V E) (x y : V) : Prop :=
  ∃ e i, G.ends i e = x ∧ G.ends (i+1) e = y

@[reducible] def finite_at' (G : digraph V E) (x : V) :=
  ∀ (i : fin 2), (G.dir_edge_nhd i x).finite

@[reducible] def locally_finite' (G : digraph V E) :=
  ∀ (x : V), G.finite_at' x

instance fintype_of_finite_at' [G.finite_at' x] : fintype (G.dir_edge_nhd i x) :=
  set.finite.fintype (‹G.finite_at' x› i)

--instance blah [locally_finite' G] : G.finite_at' x :=
--  λ i, (‹locally_finite' G› x i)

--#check λ {inst : locally_finite' G} (i : fin 2),
def blah := (λ {V E : Type*} (G : digraph V E), locally_finite' G)

class finite_at (G : digraph V E) (x : V) : Prop :=
  (fin : ∀ (i : fin 2), (G.dir_edge_nhd i x).finite)

class locally_finite (G : digraph V E) : Prop :=
  (fins : ∀  (x : V), G.finite_at x)

instance [G.finite_at x] : fintype (G.dir_edge_nhd i x) :=
  set.finite.fintype (finite_at.fin i)

instance loc_fin [locally_finite G] {x : V}: G.finite_at x :=
  locally_finite.fins x

instance [G.finite_at x]: fintype (G.edge_nhd x) :=
  set.fintype_Union (λ i, dir_edge_nhd G i x)

instance [G.finite_at x]: fintype (G.loops_at x) :=
  set.fintype_subset _ (set.Inter_subset (λ i, dir_edge_nhd G i x) 0)

instance finite_at_of_fintype [fintype E] : G.finite_at x :=
  ⟨λ x, ⟨infer_instance⟩⟩

instance loc_finite_of_fintype [fintype E] : locally_finite G :=
  ⟨λ x, infer_instance⟩

lemma dir_edge_nhd_finite_of_loc_finite (G : digraph V E) [locally_finite G] (i : fin 2) (x : V):
  (G.dir_edge_nhd i x).finite :=
set.finite.intro (infer_instance)

instance finite_at_of_edge_nhd_finite (h : (G.edge_nhd x).finite) : G.finite_at x :=
  {fin := λ i, ⟨@set.fintype_subset _ (G.edge_nhd x) _ h.fintype _ (set.subset_Union _ _)⟩}

def dir_edge_nhd_finset (G : digraph V E) (i : fin 2) (x : V) [G.finite_at x]  : finset E :=
  (G.dir_edge_nhd i x).to_finset

def in_edge_nhd_finset (G : digraph V E) (x : V) [G.finite_at x] : finset E :=
  G.dir_edge_nhd_finset 0 x

def out_edge_nhd_finset (G : digraph V E) (x : V) [G.finite_at x]: finset E :=
  G.dir_edge_nhd_finset 1 x

def edge_nhd_finset (G: digraph V E) (x : V) [G.finite_at x] : finset E :=
  (G.edge_nhd x).to_finset

def loops_at_finset (G : digraph V E) (x : V) [G.finite_at x] : finset E :=
  (G.loops_at x).to_finset

def nhd (G : digraph V E) (x : V) : set V :=
  {y : V | G.adj x y}

def nhd_finset (G : digraph V E)(x : V)[fintype (G.nhd x)] : finset V :=
  (G.nhd x).to_finset

lemma is_loop_def:
  G.is_loop e ↔ G.ends 0 e = G.ends 1 e :=
iff.rfl

lemma adj_def:
  G.adj x y ↔ ∃ e i, G.ends i e = x ∧ G.ends (i+1) e = y  :=
iff.rfl

lemma inc_def {G : digraph V E} {x : V} {e : E}:
  G.inc x e ↔ ∃ i, G.ends i e = x :=
iff.rfl

lemma dir_edge_nhd_def (G : digraph V E) (i : fin 2) (x : V):
  G.dir_edge_nhd i x = {e : E | G.ends i e = x} :=
rfl

lemma edge_nhd_def (G : digraph V E) (x : V):
  G.edge_nhd x = ⋃ (i : fin 2), (G.dir_edge_nhd i x) :=
rfl

lemma loops_at_def (G : digraph V E) (x : V):
  G.loops_at x = ⋂ (i : fin 2), (G.dir_edge_nhd i x) :=
rfl

lemma dir_edge_nhd_finset_def [G.finite_at x]:
  G.dir_edge_nhd_finset i x = (G.dir_edge_nhd i x).to_finset :=
rfl

lemma edge_nhd_finset_def [G.finite_at x]:
  G.edge_nhd_finset x = (G.edge_nhd x).to_finset :=
rfl

lemma loops_at_finset_def [G.finite_at x]:
  G.loops_at_finset x = (G.loops_at x).to_finset :=
rfl

@[simp] lemma edge_nhd_eq_union :
  G.edge_nhd x = G.dir_edge_nhd 0 x ∪ G.dir_edge_nhd 1 x :=
by {ext, rw [set.mem_union, edge_nhd_def, set.mem_Union, fin.exists_fin_two]}

@[simp] lemma loops_at_eq_inter :
  G.loops_at x = G.dir_edge_nhd 0 x ∩ G.dir_edge_nhd 1 x :=
by {ext, rw [set.mem_inter_iff, loops_at_def, set.mem_Inter, fin.forall_fin_two] }

lemma finite_at_iff_edge_nhd_finite:
  G.finite_at x ↔ (G.edge_nhd x).finite :=
⟨λ h, by {rw [edge_nhd_def, fin.Union_fin_two], cases h, exact set.finite.union (h 0) (h 1)},
 λ h, digraph.finite_at_of_edge_nhd_finite h⟩

lemma is_loop_of_mem_loops_at :
  e ∈ G.loops_at x → G.is_loop e :=
begin
  simp_rw [is_loop_def, loops_at_def, set.mem_Inter, dir_edge_nhd_def, set.mem_set_of],
  exact λ h, by rw [h 0, h 1],
end

lemma mem_loops_at_iff_is_loop_inc :
  e ∈ G.loops_at x ↔ G.is_loop e ∧ G.inc x e :=
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

lemma adj_iff_nhd_inter (huv : x ≠ y):
  G.adj x y ↔ ((G.edge_nhd x) ∩ (G.edge_nhd y)).nonempty :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { rcases h with ⟨e,⟨i,hi1,hi2⟩⟩,
    exact ⟨e, set.mem_inter (set.mem_Union.mpr ⟨i,set.mem_set_of.mpr hi1⟩)
      (set.mem_Union.mpr ⟨i+1,set.mem_set_of.mpr hi2⟩)⟩},
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
  G.adj x x ↔ (G.loops_at x).nonempty :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { rcases h with ⟨e, ⟨i,h1,h2⟩⟩,
    refine ⟨e, mem_loops_at_iff_is_loop_inc.mpr ⟨_,set.mem_set_of.mpr ⟨i, h1⟩⟩⟩,
    rw is_loop_def,
    cases fin.fin_two_eq_zero_or_one i,
      { subst h, rw h1, exact h2.symm,},
      subst h, rw h1, exact h2,
  },
  cases h with e h,
  rw [mem_loops_at_iff_is_loop_inc, is_loop_def, inc_def] at h,
  refine ⟨e, 0, _⟩,
  rcases h with ⟨h1, ⟨j, h2⟩⟩,
  cases fin.fin_two_eq_zero_or_one j with h,
  { subst h,
    rw [h1, zero_add, ←h2, h1, and_self]},
  subst h,
  rw [h1, zero_add, h2, and_self],
end

lemma adj_symm (x y : V) :
  G.adj x y → G.adj y x :=
begin
  by_cases x = y,
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
  cases fin.fin_two_eq_zero_or_one i with h,
  { subst h, apply ends_adj},
  subst h,
  exact adj_symm _ _ (ends_adj _),
end

lemma edge_nhd_eq_in_edge_nhd_union_out_edge_nhd (G : digraph V E)(x : V):
  (G.edge_nhd x) = G.in_edge_nhd x ∪ G.out_edge_nhd x :=
begin
  ext x,
  unfold edge_nhd in_edge_nhd out_edge_nhd,
  simp only [set.mem_Union, set.mem_union_eq], apply fin.exists_fin_two,
end

lemma dir_nhds_pairwise_disjoint (G : digraph V E)(i : fin 2):
  (set.univ : set V).pairwise_disjoint (λ x, G.dir_edge_nhd i x) :=
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
set.sUnion_eq_univ_iff.mpr (λ e, ⟨G.dir_edge_nhd i (G.ends i e), by simp [dir_edge_nhd_def] ⟩ )

lemma other_end_def (x : V) (e : E):
  G.other_end x e =
  if G.ends 0 e = x then G.ends 1 e else if G.ends 1 e = x then G.ends 0 e else x  :=
rfl

lemma other_end_idem (x : V) (e : E):
  G.other_end (G.other_end x e) e = x :=
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
  cases fin.fin_two_eq_zero_or_one i,
  { subst h, simp},
  subst h, simp only [eq_self_iff_true, if_true],
  split_ifs,
  { rw ← h, refl,},
  refl,
end

lemma other_end_adj (hve : G.inc x e):
  G.adj x (G.other_end x e) :=
by {cases hve with i h, rw [← h, other_end_eq],  apply ends_adj'}


lemma edge_nhd_eq_inc (G : digraph V E) (x : V):
  G.edge_nhd x = {e | G.inc x e} :=
begin
  rw [edge_nhd_eq_union, dir_edge_nhd_def, dir_edge_nhd_def],
  ext,
  simp [inc_def, fin.exists_fin_two],
end

lemma dir_edge_nhd_subset_edge_nhd (G : digraph V E)(i : fin 2)(x : V):
  G.dir_edge_nhd i x ⊆ G.edge_nhd x :=
set.subset_Union (λ j, G.dir_edge_nhd j x) i

lemma loops_at_subset_dir_edge_nhd (G : digraph V E)(i : fin 2)(x : V):
  G.loops_at x ⊆ G.dir_edge_nhd i x :=
set.Inter_subset _ _

lemma loops_at_subset_edge_nhd (G : digraph V E)(x : V):
  G.loops_at x ⊆ G.edge_nhd x :=
subset_trans (G.loops_at_subset_dir_edge_nhd 0 x) (G.dir_edge_nhd_subset_edge_nhd 0 x)

lemma ends_set_nonempty(G : digraph V E)(e : E):
  (G.ends_set e).nonempty :=
⟨G.ends 0 e, set.mem_set_of.mpr ⟨0, rfl⟩⟩

lemma ends_finset_nonempty(G : digraph V E)(e : E):
  (G.ends_finset e).nonempty :=
by simp [ends_finset, ends_set]

lemma card_ends_finset_le_two (G : digraph V E)(e : E):
  (G.ends_finset e).card ≤ 2 :=
by {simp only [ends_finset, ends_set], apply finset.card_insert_le}

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

def dir_deg (G : digraph V E) (i : fin 2) (x : V) : ℕ :=
  nat.card (G.dir_edge_nhd i x)

def in_deg (G : digraph V E) (x : V) : ℕ :=
  G.dir_deg 0 x

def out_deg (G : digraph V E) (x : V) : ℕ :=
  G.dir_deg 1 x

def deg (G : digraph V E)(x : V) : ℕ :=
  nat.card ((G.dir_edge_nhd 0 x) ⊕ (G.dir_edge_nhd 1 x))

lemma dir_deg_def (G : digraph V E) (i : fin 2) (x : V) :
  G.dir_deg i x = nat.card (G.dir_edge_nhd i x) :=
rfl

lemma deg_def (G : digraph V E)(x : V)[G.finite_at x]:
  G.deg x = G.dir_deg 0 x + G.dir_deg 1 x :=
by simp [deg, dir_deg]

lemma dir_deg_eq_finset_card (G: digraph V E) (i : fin 2) (x : V) [G.finite_at x] :
  G.dir_deg i x = (G.dir_edge_nhd_finset i x).card :=
begin
  unfold dir_deg dir_edge_nhd_finset,
  rw [nat.card_eq_fintype_card, eq_comm, set.to_finset_card],
end

lemma deg_eq_sum_card_nhd_card_loops (G : digraph V E) (x : V) [G.finite_at x] :
  G.deg x = (G.edge_nhd_finset x).card + (G.loops_at_finset x).card :=
begin
  rw [deg_def, dir_deg_eq_finset_card, dir_deg_eq_finset_card, eq_comm],
  convert finset.card_union_add_card_inter _ _,
  rw [edge_nhd_finset_def, dir_edge_nhd_finset_def, dir_edge_nhd_finset_def,
      ←set.to_finset_union, set.to_finset_inj, edge_nhd_eq_union],
  rw [loops_at_finset_def, dir_edge_nhd_finset_def, dir_edge_nhd_finset_def,
    ←set.to_finset_inter, set.to_finset_inj, loops_at_eq_inter],
end

def deg_eq_zero_of_edge_nhd_infinite (h : (G.edge_nhd x).infinite):
  G.deg x = 0 :=
begin
  apply @nat.card_eq_zero_of_infinite _ _,
  rw [infinite_sum, set.infinite_coe_iff, set.infinite_coe_iff],
  rwa [edge_nhd, fin.Union_fin_two, set.infinite_union] at h,
end

variables [fintype V][fintype E]

lemma dir_handshake (G : digraph V E) (i : fin 2):
  ∑ᶠ (x : V), (G.dir_deg i x) = fintype.card E :=
begin
  simp_rw dir_deg_def,
  rw [←finsum_mem_univ, eq_comm],
  convert @finsum_mem_bUnion _ _ _ _ 1 _ _
    (G.dir_nhds_pairwise_disjoint i)
    set.finite_univ (λ x hx, set.finite.of_fintype _),
  { convert (finsum_mem_ones_eq_card _).symm,
    simp only [finsum_mem_ones_eq_card, nat.card_eq_fintype_card, ←finset.card_univ,
    set.bUnion_univ, G.Union_dir_nhds_eq_univ, ←set.to_finset_card, set.to_finset_univ],
  },
  simp only [pi.one_apply, finsum_mem_ones_eq_card],
end

theorem handshake (G : digraph V E):
  ∑ᶠ (x : V), G.deg x = 2 * (fintype.card E) :=
begin
  simp_rw deg_def,
  rw [finsum_add_distrib (set.finite.of_fintype _) (set.finite.of_fintype _), dir_handshake,
    dir_handshake, ←two_mul];
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
  cases fin.fin_two_eq_zero_or_one j with hj_eq hj_eq,
  { subst hj_eq,
    exact ⟨equiv.refl (fin 2), λ i, by simp [hj]⟩},
  subst hj_eq,
  exact ⟨fin_rotate 2, (λ i, by simp [hj])⟩,
end


lemma inc_respects:
  G₁ ~ G₂ → G₁.inc = G₂.inc :=
begin
  refine λ h, funext (λ x, funext (λ e, iff_iff_eq.mp _)),
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
  cases fin.fin_two_eq_zero_or_one j with hj hj,
  { subst hj, tauto,},
  subst hj, tauto,
end

lemma edge_nhd_respects:
  G₁ ~ G₂ → G₁.edge_nhd = G₂.edge_nhd :=
λ h, funext (λ x, by simp_rw [edge_nhd_eq_inc, inc_respects h])

lemma loops_at_respects:
  G₁ ~ G₂ → G₁.loops_at = G₂.loops_at :=
λ h, funext (λ x, set.ext (λ e,
  by simp_rw [mem_loops_at_iff_is_loop_inc, is_loop_respects h, inc_respects h]))

lemma adj_of_adj_equiv (x y : V):
  G₁ ~ G₂ → G₁.adj x y → G₂.adj x y :=
begin
  refine classical.by_cases (λ huv : (x = y), λ h h', _) (λ huv : (x ≠ y), λ h h', _) ,
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
  refine (λ h, funext (λ x, funext (λ e, _))),
  cases orientation_equiv_iff_shift.mp h e with j hj,
  simp_rw [other_end_def, hj, zero_add],
  cases fin.fin_two_eq_zero_or_one j with hj hj;
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
  refine (λ h, funext (λ x, _)),
  cases @set.finite_or_infinite _ (G₁.edge_nhd x) with hfin hinf,
  { haveI := digraph.finite_at_of_edge_nhd_finite hfin,
    rw edge_nhd_respects h at hfin,
    haveI := digraph.finite_at_of_edge_nhd_finite hfin,
    simp_rw [deg_eq_sum_card_nhd_card_loops, edge_nhd_finset_def, loops_at_finset_def,
      edge_nhd_respects h, loops_at_respects h], },
  have hinf2 := hinf,
  rw [edge_nhd_respects h] at hinf2,
  rw [deg_eq_zero_of_edge_nhd_infinite hinf, deg_eq_zero_of_edge_nhd_infinite hinf2],
end

lemma ends_set_respects:
  G₁ ~ G₂ → G₁.ends_set = G₂.ends_set :=
λ h, funext (λ x, by simp_rw [ends_set, inc_respects h])

lemma finite_at_respects :
  G₁ ~ G₂ → (G₁.finite_at x ↔ G₂.finite_at x) :=
begin
  simp_rw finite_at_iff_edge_nhd_finite,
  exact λ h, ⟨λ h1, by rwa [←edge_nhd_respects h], λ h2, by rwa[edge_nhd_respects h]⟩,
end

lemma locally_finite_respects:
  G₁ ~ G₂ → (G₁.locally_finite ↔ G₂.locally_finite) :=
begin
  refine λ h, ⟨λ h1, ⟨λ x, _⟩, λ h1, ⟨λ x, _⟩⟩,
  all_goals { have := (h1.fins : _) x},
     rwa ← finite_at_respects h,
  rwa finite_at_respects h,
end

--begin
--  refine ⟨λ h, λ x, _, λ h, λ x, _⟩,
--end

end reorientation

end digraph
