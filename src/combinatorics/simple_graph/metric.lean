/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Vincent Beffara
-/
import combinatorics.simple_graph.connectivity
import data.nat.lattice
import data.enat.lattice
import algebra.order.pointwise
import topology.metric_space.emetric_space
import topology.metric_space.lipschitz
import data.real.enat_ennreal

open_locale ennreal

namespace enat

lemma add_one_lt_add_one {a b : ℕ∞} (ab : a < b) : a + 1 < b + 1 := sorry
lemma le_add (n m : ℕ∞) : n ≤ n + m := sorry
lemma add_le_add {n n' m m' : ℕ∞} (hn : n ≤ n') (hm : m ≤ m') : n + m ≤ n' + m' := sorry
lemma lt_add_one_iff_le {n m : ℕ∞} (h : m ≠ ⊤) : n < m + 1 ↔ n ≤ m  := sorry

lemma coe_ennreal_inj {n m : ℕ∞} : (↑n : ℝ≥0∞) = ↑m ↔ n = m := sorry

end enat

namespace simple_graph
variables {V V' : Type*} (G : simple_graph V) (G' : simple_graph V')

/-! ## Metric -/

noncomputable
def edist (u v : V) : ℕ∞ := ⨅ w : G.walk u v, w.length

variables {G}

protected
lemma reachable.exists_walk {u v : V} (h : G.reachable u v) :
  ∃ (p : G.walk u v), (p.length : ℕ∞) = G.edist u v :=
begin
  haveI : nonempty (G.walk u v) := h,
  refine ⟨function.argmin (λ w : G.walk u v, (w.length : ℕ)) nat.lt_wf,
          le_antisymm (le_infi (λ w', _)) (infi_le _ _)⟩,
  simp only [nat.cast_le, function.argmin_le],
end

lemma reachable_iff_exists_walk {u v : V} :
  G.reachable u v ↔ ∃ (p : G.walk u v), (p.length : ℕ∞) = G.edist u v :=
⟨reachable.exists_walk, λ p, ⟨p.some⟩⟩

lemma not_reachable_iff_edist_eq_top {u v : V} :
  ¬ G.reachable u v ↔ G.edist u v = ⊤ :=
begin
  rw [edist, reachable, not_nonempty_iff, infi_eq_top],
  exact ⟨λ h p, h.elim p, λ h, ⟨λ p,  with_top.nat_ne_top _ (h p)⟩⟩,
end

lemma reachable_iff_edist_ne_top {u v : V} :
  G.reachable u v ↔ G.edist u v ≠ ⊤ :=
by rw [←not_iff_not, not_reachable_iff_edist_eq_top, not_not]

lemma exists_walk_iff_edist_ne_top {u v : V} :
  (∃ (p : G.walk u v), (p.length : ℕ∞) = G.edist u v) ↔ G.edist u v ≠ ⊤ :=
by rw [←reachable_iff_edist_ne_top, ←reachable_iff_exists_walk]

lemma exists_walk_of_edist_eq_nat {u v : V} {n : ℕ} (h : G.edist u v = n) :
  (∃ (p : G.walk u v), p.length = n) :=
begin
  have : ∃ (p : G.walk u v), ↑(p.length) = G.edist u v, by
  { rw [exists_walk_iff_edist_ne_top, h],
    apply with_top.nat_ne_top _, },
  rw h at this,
  obtain ⟨w, hw⟩ := this,
  simp only [nat.cast_inj] at hw,
  exact ⟨w, hw⟩,
end


lemma edist_le {u v : V} (p : G.walk u v) : G.edist u v ≤ p.length := infi_le _ p

lemma le_edist {u v : V} {n : ℕ} (h : ∀ p : G.walk u v, n ≤ p.length) : (n : ℕ∞) ≤ G.edist u v :=
le_infi (λ p, nat.cast_le.mpr $ h p)

@[simp]
lemma edist_self {v : V} : edist G v v = 0 := by
begin
  convert le_antisymm (infi_le _ (walk.nil' v)) _,
  simp only [walk.length_nil, enat.coe_zero, zero_le],
end

lemma edist_comm {u v : V} : edist G u v = edist G v u :=
begin
  dsimp [edist],
  refine le_antisymm (le_infi (λ w, _)) (le_infi (λ w, _));
  { rw ←walk.length_reverse,
    apply infi_le _ _, }
end

lemma edist_triangle {u v w : V} :
  G.edist u w ≤ G.edist u v + G.edist v w :=
begin
  by_cases huv : nonempty (G.walk u v),
  by_cases hvw : nonempty (G.walk v w),
  { obtain ⟨p, hp⟩ := reachable.exists_walk huv,
    obtain ⟨q, hq⟩ := reachable.exists_walk hvw,
    rw [←hp, ←hq, ←enat.coe_add, ←walk.length_append],
    apply edist_le, },
  { simp only [not_reachable_iff_edist_eq_top.mp hvw, with_top.add_top, le_top], },
  { simp only [not_reachable_iff_edist_eq_top.mp huv, with_top.top_add, le_top], },
end

@[simp] lemma edist_eq_zero_iff_eq {u v : V} : G.edist u v = 0 ↔ u = v :=
⟨λ h, walk.eq_of_length_eq_zero (exists_walk_of_edist_eq_nat h).some_spec, λ h, h ▸ edist_self⟩

@[simp]
lemma edist_eq_one_iff_adj {u v : V} : G.edist u v = 1 ↔ G.adj u v :=
begin
  split,
  { rintro h,
    obtain ⟨w, hw⟩ := exists_walk_of_edist_eq_nat h,
    exact walk.adj_of_length_eq_one hw, },
  { refine λ a, le_antisymm (edist_le (walk.cons a walk.nil)) (le_edist (λ w, _)),
    simp only [nat.one_le_iff_ne_zero, walk.length_cons, walk.length_nil, ne.def],
    exact λ h, (a.ne $ walk.eq_of_length_eq_zero h), },
end

lemma exists_edist_eq_of_edist_eq_succ {u v : V} {n : ℕ} (h : G.edist u v = n+1) :
  ∃ w, G.edist w v = n ∧ G.edist u w = 1 :=
begin
  obtain ⟨p, hp⟩ := exists_walk_of_edist_eq_nat h,
  cases p with _ u w v a q,
  { simpa only using hp, },
  { simp only [edist_eq_one_iff_adj],
    refine ⟨w, _, a⟩,
    simp only [walk.length_cons, add_left_inj] at hp,
    refine le_antisymm (hp ▸ edist_le _) _,
    { by_contra' h',
      rw ←edist_eq_one_iff_adj at a,
      refine ((enat.add_one_lt_add_one h').trans_le (_ : ↑n + 1 ≤ G.edist w v + 1)).ne rfl,
      rw [←h, ←a, add_comm],
      apply edist_triangle, }, },
end

@[reducible]
def closed_ball (G : simple_graph V) (v : V) (n : ℕ) := {u | G.edist u v ≤ n}

lemma closed_ball_zero_eq (v : V) : G.closed_ball v 0 = {v} :=
by simp only [closed_ball, edist_eq_zero_iff_eq, enat.coe_zero, nonpos_iff_eq_zero,
              set.set_of_eq_eq_singleton]

lemma closed_ball_succ_eq  (v : V) (n : ℕ) :
  G.closed_ball v (n+1) = G.closed_ball v n ∪ (⋃ u ∈ G.closed_ball v n, G.neighbor_set u) :=
begin
  ext x,
  simp only [enat.coe_add, enat.coe_one, set.mem_set_of_eq, set.mem_union, set.mem_Union,
             mem_neighbor_set, exists_prop],
  split,
  { rintro hx, rw [le_iff_eq_or_lt] at hx,
    rcases hx with (he|hlt),
    { obtain ⟨_|⟨a, w⟩, h⟩ := exists_walk_of_edist_eq_nat he,
      { simp, },
      { simp only [walk.length_cons, add_left_inj] at h,
        rw ←h,
        refine or.inr ⟨_, edist_le _, a.symm⟩, } },
    { rw enat.lt_add_one_iff_le (with_top.nat_ne_top n) at hlt,
      exact or.inl hlt, }  },
  { rintro (hx|⟨u, hu, a⟩),
    { exact hx.trans (enat.le_add _ _), },
    { apply (@edist_triangle _ G x u v).trans _,
      rw add_comm _ (1 : ℕ∞),
      apply enat.add_le_add (eq.le _) hu,
      simpa using a.symm, }, }
end

instance fintype_closed_ball [lf : locally_finite G] [decidable_eq V] (v : V) (n : ℕ) :
  fintype (G.closed_ball v n) :=
begin
  induction n,
  { rw closed_ball_zero_eq,
    apply set.fintype_singleton, },
  { rw closed_ball_succ_eq,
    haveI := n_ih,
    apply set.fintype_union, },
end

variables {G} {G'}

lemma hom.edist_le (φ : G →g G') (x y : V) : G'.edist (φ x) (φ y) ≤ G.edist x y :=
begin
  obtain (h|h) := eq_or_ne (G.edist x y) ⊤,
  { simp [h], },
  { obtain ⟨p, h⟩ := exists_walk_iff_edist_ne_top.mpr h,
    rw [←h, ←walk.length_map φ p],
    apply edist_le, },
end

lemma iso.edist_eq (φ : G ≃g G') (x y : V) : G'.edist (φ x) (φ y) = G.edist x y :=
begin
  refine le_antisymm (hom.edist_le φ.to_hom x y) _,
  convert (hom.edist_le φ.symm.to_hom (φ x) (φ y)),
  exacts [(φ.left_inv x).symm, (φ.left_inv y).symm],
end

variables (G) (G')

lemma closed_ball_ne_univ_of_infinite [lf : locally_finite G] [hV : infinite V]
  (v : V) (n : ℕ) : G.closed_ball v n ≠ set.univ :=
begin
  classical,
  rintro h,
  haveI : fintype (@set.univ V), by rw ←h; exact (@simple_graph.fintype_closed_ball _ G lf _ v n),
  apply hV.not_finite (finite.of_finite_univ (set.univ : set V).to_finite),
end

@[reducible]
def closed_neighborhood (s : set V) (n : ℕ) := ⋃ v ∈ s, G.closed_ball v n

lemma subset_closed_neighborhood  (s : set V) (n : ℕ) :
  s ⊆ G.closed_neighborhood s n :=
begin
  rintro u us,
  simp only [set.mem_Union, set.mem_set_of_eq, exists_prop],
  refine ⟨u, us, _⟩,
  simp only [edist_self, with_top.coe_nonneg, zero_le'],
end

lemma closed_neighborhood_finite [locally_finite G] {s : set V} (fs : s.finite) (n : ℕ) :
  (G.closed_neighborhood s n).finite :=
begin
  classical,
  apply set.finite.bUnion fs (λ u us, _),
  exact ⟨simple_graph.fintype_closed_ball u n⟩,
end

def path_metric (G : simple_graph V) := V

noncomputable instance (G : simple_graph V) : emetric_space (path_metric G) :=
{ edist := λ x y, (G.edist x y : ℝ≥0∞),
  edist_self := λ x, by simp only [←enat.coe_ennreal_zero, edist_self],
  edist_comm := λ x y, by simp only [edist_comm],
  edist_triangle := λ x y z, by
    { simp only [←enat.coe_ennreal_add, enat.coe_ennreal_le, edist_triangle], },
  eq_of_edist_eq_zero := λ x y, by
    { simp only [←enat.coe_ennreal_zero, edist_eq_zero_iff_eq, enat.coe_ennreal_inj, imp_self], } }

variables {G} {G'}

def hom.to_path_metric (φ : G →g G') : (path_metric G) → (path_metric G') := φ.to_fun

lemma hom.to_path_metric_nonexpanding (φ : G →g G') : lipschitz_with 1 (φ.to_path_metric) :=
begin
  intros x y,
  simp only [has_edist.edist, ennreal.coe_one, one_mul, enat.coe_ennreal_le],
  apply φ.edist_le,
end

section preconnected

lemma preconnected.exists_walk (G : simple_graph V) [hc : fact G.preconnected] (u v : V) :
  ∃ (p : G.walk u v), (p.length : ℕ∞) = G.edist u v :=
(hc.out u v).exists_walk

noncomputable def dist (G : simple_graph V)
  [hc : fact $ G.preconnected] (u v : V) : ℕ :=
well_founded.min nat.lt_wf (set.range (walk.length : G.walk u v → ℕ))
  (@set.range_nonempty _ _ (hc.out u v) _)

@[simp]
lemma coe_dist_eq [hc : fact G.preconnected] (u v : V) :
  (dist G u v : ℕ∞) = G.edist u v :=
begin
  apply le_antisymm,
  { apply le_edist, rintro p, apply well_founded.min_le, exact ⟨p, rfl⟩, },
  { obtain ⟨p,h⟩ := well_founded.min_mem nat.lt_wf (set.range (walk.length : G.walk u v → ℕ))
                                                   (@set.range_nonempty _ _ (hc.out u v) _),
    rw [dist, ←h],
    exact (edist_le p), }
end

noncomputable
instance (G : simple_graph V) [hc : fact G.preconnected] : metric_space (path_metric G) :=
emetric_space.to_metric_space_of_dist (λ u v, (G.dist u v : ℝ))
  (λ u v, by
    { simp only [has_edist.edist, ne, ←enat.coe_ennreal_top, enat.coe_ennreal_inj],
      exact reachable_iff_edist_ne_top.mp (hc.out u v), })
  (λ u v, by simp only [has_edist.edist, ←coe_dist_eq,enat.coe_ennreal_coe, ennreal.to_real_nat])

end preconnected


lemma enough_space_of_transitive [lf : locally_finite G] [hV : infinite V] [decidable_eq V]
  [Gpc : fact G.preconnected] (ht : ∀ u v, ∃ φ : G ≃g G, φ u = v) (K : finset V) :
  ∃ φ : G ≃g G, disjoint (K.image φ) K :=
begin
  obtain (rfl|⟨u, uK⟩) := finset.eq_empty_or_nonempty K,
  { simp, },
  { let m := (K.image (λ y, G.dist u y)).max' (finset.nonempty.image ⟨u, uK⟩ _),
    have Km : ∀ ⦃y⦄, y ∈ K → G.edist u y ≤ m := λ y yK, by
    { rw [←coe_dist_eq, nat.cast_le],
      refine finset.le_max' _ _ (finset.mem_image_of_mem _ yK), },
    obtain ⟨v, hv⟩ := set.nonempty_compl.mpr (G.closed_ball_ne_univ_of_infinite u (m + m)),
    obtain ⟨φ, rfl⟩ := ht u v,
    have φKm : ∀ ⦃y⦄, y ∈ K.image φ →  G.edist (φ u) y ≤ m,
    { simp only [finset.mem_image],
      rintro _ ⟨y, yK, rfl⟩,
      exact (iso.edist_eq φ u y).symm ▸ (Km yK), },
    simp only [finset.disjoint_left, set.mem_compl_iff, set.mem_set_of_eq, enat.coe_add] at hv ⊢,
    exact ⟨φ, λ x xφK xK, hv (edist_triangle.trans $ enat.add_le_add
                             (φKm xφK) (by { rw edist_comm, exact Km xK, }))⟩, }
end

end simple_graph
