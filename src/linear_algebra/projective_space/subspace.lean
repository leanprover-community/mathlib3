import linear_algebra.projective_space.dependent
import linear_algebra
import linear_algebra.finsupp
import linear_algebra.finite_dimensional
import algebra.module.submodule.basic
import tactic

variables (K V : Type*) [field K] [add_comm_group V] [module K V]

namespace projectivization



@[ext] structure subspace :=
(carrier : set (ℙ K V))
(mem_of_add' (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v + w ≠ 0) :
  mk K v hv ∈ carrier → mk K w hw ∈ carrier → mk K (v + w) (hvw) ∈ carrier)

namespace subspace

variables {K V}

instance : set_like (subspace K V) (ℙ K V) :=
{ coe := carrier,
  coe_injective' := λ A B, by { cases A, cases B, simp } }

lemma mem_add (T : subspace K V) (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v + w ≠ 0) :
  projectivization.mk K v hv ∈ T → projectivization.mk K w hw ∈ T →
  projectivization.mk K (v + w) (hvw) ∈ T :=
  T.mem_of_add' v w hv hw hvw


open_locale big_operators
lemma mem_sum (T : subspace K V) {ι : Type*} [fintype ι] {f : ι → V} (hf : ∀ i : ι, f i ≠ 0)
  (hs : (∑ i : ι, f i) ≠ 0) (h : ∀ i : ι, projectivization.mk K (f i) (hf i) ∈ T) :
  projectivization.mk K (∑ i : ι, f i) (hs) ∈ T := sorry

lemma mem_of_dependent (T : subspace K V) (x y z : ℙ K V)
  (h : x ≠ y) (hdep : dependent ![x,y,z]) (hx : x ∈ T) (hy : y ∈ T) :
  z ∈ T := sorry



inductive span_carrier (S : set (ℙ K V)) : set (ℙ K V)
| of (x : ℙ K V) (hx : x ∈ S) : span_carrier x
| mem_of_add (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v + w ≠ 0) : span_carrier (projectivization.mk K v hv)  →
  span_carrier (projectivization.mk K w hw) → span_carrier (projectivization.mk K (v + w) (hvw))


def span (S : set (ℙ K V)) : subspace K V :=
{ carrier := span_carrier S,
  mem_of_add' := λ v w hv hw hvw,
    span_carrier.mem_of_add v w hv hw hvw }

lemma subset_span (S : set (ℙ K V)) : S ⊆ span S :=
λ x hx, span_carrier.of _ hx

@[simp] lemma span_subspace_self (W : subspace K V) : span ↑W = W :=
begin
  ext, split; intro hx,
  { induction hx,
    exact hx_hx,
    refine W.mem_of_dependent hx_x hx_y hx_z hx_h _ _ _, assumption' },
  { exact subset_span W hx  },
end

def gi : galois_insertion (span : set (ℙ K V) → subspace K V) coe :=
{ choice := λ S hS, span S,
  gc := λ A B, ⟨λ h, le_trans (subset_span _) h, begin
    intros h x hx,
    induction hx,
    { apply h, assumption },
    { apply B.mem_of_dependent, assumption' }
  end⟩,
  le_l_u := λ S, subset_span _,
  choice_eq := λ _ _, rfl }

instance : complete_lattice (subspace K V) :=
gi.lift_complete_lattice

/- The intersection of two subspaces is a subspace-/
instance : has_inter (subspace K V) :=
{ inter := λ W T,
  { carrier := W.carrier ∩ T.carrier,
    mem_of_dependent' := λ x y z h hdep hx hy,
      ⟨W.mem_of_dependent x y z h hdep hx.1 hy.1, T.mem_of_dependent x y z h hdep hx.2 hy.2⟩ } }

def of_submodule (H : submodule K V) : subspace K V :=
{ carrier := { x | x.submodule ≤ H },
  mem_of_add' :=
  begin
    intros v w hv hw hvw h1 h2,
    simp only [set.mem_set_of_eq, submodule_mk, submodule.span_singleton_le_iff_mem] at h1 h2 ⊢,
    exact H.add_mem h1 h2,
  end }

open_locale big_operators classical
def equiv : subspace K V ≃o submodule K V :=
{ to_fun := λ S, ⨆ (x : ℙ K V) (hx : x ∈ S), x.submodule,
  inv_fun := of_submodule,
  left_inv :=
  begin
    intros W,
    dsimp,
    ext,
    unfold of_submodule,
    split,

    { rw ← mk_rep x,
      intros h,
      dsimp at h,
      simp at h,
      rw submodule.mem_bsupr_iff_exists_dfinsupp at h,
      obtain ⟨f, hf ⟩ := h,
      dsimp at hf,
      erw dfinsupp.sum_add_hom_apply at hf,
      dsimp [dfinsupp.sum] at hf,
      rw finset.sum_subtype at hf,
      rotate,
      exact f.support,
      rw ← hf,



      /-
      have heq : (⨆ (x : ℙ K V) (hx : x ∈ W), x.submodule) = (⨆ (x : ℙ K V) (hx : x ∈ W),
      submodule.span K {x.rep}), by {congr, ext, rw [← submodule_mk x_1.rep (rep_nonzero x_1), mk_rep],},
      rw heq at hx,
      have hxr : _, by { exact (hx (submodule.mem_span_singleton_self x.rep))},
      suffices hmemw : x.rep = 0 ∨ (∃ hx : x.rep ≠ 0, (projectivization.mk K x.rep hx) ∈ W.carrier), by {sorry},
      apply @submodule.supr_induction K V _ _ _ _ _ (λ y, y = 0 ∨ (∃ hy : y ≠ 0, (projectivization.mk K y hy) ∈ W.carrier)) x.rep hxr,

      { intros y v hv,
        simp at hv,
        have hvy: v ∈ submodule.span K {y.rep}, by { sorry },
        rw submodule.mem_span_singleton at hvy,
        by_cases hvz : v = 0,
        { exact or.inl hvz,},
        { right,
          use hvz,
          rw ← projectivization.mk_eq_mk_iff' K v y.rep hvz (rep_nonzero y) at hvy,
          rw hvy,
          sorry },},
      { simp,},
      { intros v u hv hu,
        cases hv,
        { cases hu,
          { rw [hv, hu, add_zero], exact or.inl (rfl),},
          { simp_rw [hv, zero_add], exact or.inr hu},},
        { cases hu,
          { simp_rw [hu, add_zero], exact or.inr hv},
          { cases hv with hv hvw,
            cases hu with hu huw,
            sorry},},},

            -/
            },
    { intro hx,
      rw set.mem_set_of_eq,
      refine le_Sup _,
      rw set.mem_range,
      exact ⟨x, supr_pos hx⟩ },
  end,
  right_inv :=
  begin
    intros W, dsimp, ext, split,
    { intro hx,
      have hxw : (⨆ (x : ℙ K V) (hx : x ∈ of_submodule W), x.submodule) ≤ W, by
      { refine supr_le _, simp only [supr_le_iff], intros i hi, exact hi },
      exact hxw hx },
    { intro hx,
      by_cases hxt : x = 0,
      { rw hxt, exact submodule.zero_mem _ },
      { have hxw : (projectivization.mk K x hxt) ∈ (of_submodule W), by
        { exact (submodule.span_singleton_le_iff_mem x W).mpr hx },
        have : (projectivization.mk K x hxt).submodule ≤
        ⨆ (x : ℙ K V) (hx : x ∈ of_submodule W), x.submodule, by
        { refine le_Sup _, rw [submodule_mk, set.mem_range],
          exact ⟨(projectivization.mk K x hxt), supr_pos hxw⟩ },
        exact this (by { rw submodule_mk, exact submodule.mem_span_singleton_self x }) } },
  end,
  map_rel_iff' :=
  begin
    intros W S,
    rw [equiv.coe_fn_mk, supr₂_le_iff],
    split,
    {
      intros hw v hv,
      specialize hw v hv,
      rw [← mk_rep v, submodule_mk, submodule.span_singleton_le_iff_mem,
      submodule.supr_eq_span] at hw,
      rcases (submodule.mem_span_finite_of_mem_span hw) with ⟨s, ⟨hs, hvs⟩⟩,
      rw mem_span_finset at hvs,
      cases hvs with f hf,
      sorry},

    { intros hws w hw u hu,
      specialize hws hw,
      have : w.submodule ≤ ⨆ (x : ℙ K V) (hx : x ∈ S), x.submodule,
      by { refine le_Sup _, rw set.mem_range, exact ⟨w, supr_pos hws⟩},
      exact this hu},
  end, }



/- A point in projective space determines a subspace consisting of the point. -/
instance : has_singleton (ℙ K V) (subspace K V):=
{ singleton := λ a,
{ carrier := {a},
  mem_of_dependent' :=
  by {intros x y z h hdep hx hy, simp at *, rw [hx, hy] at h, contradiction} }}

/- A point belongs to a singleton subspace iff the point is equal to the singleton determining
  the subspace-/
lemma mem_singleton_iff (a b : ℙ K V) : b ∈ ({a} : subspace K V) ↔ b = a :=
begin
  exact ⟨by { intro hb, induction hb, refl }, by { intro h, rw h, split }⟩,
end

/- The submodule corresponding to the intersection of two subspaces is the intersection of the
  two submodules corresponding to the respective subspaces. -/
lemma inter_equiv_eq_equiv_inter (W S : subspace K V) :
  subspace.equiv (W ∩ S) = (subspace.equiv W) ∩ (subspace.equiv S) :=
begin
  sorry
end

/- The line determined by two points in projective space is their span. -/
def line (a b : ℙ K V) : subspace K V := span {a, b}

/- A point in projective space is a member of a subspace iff the subspace determined by that
  point is in the subspace. -/
lemma singleton_mem_iff_leq (a : ℙ K V) (W : subspace K V) : a ∈ W ↔ {a} ≤ W :=
  by { change a ∈ W ↔ ({a} : set (ℙ K V)) ⊆ W, rw [set.singleton_subset_iff, set_like.mem_coe] }

/- The submodule corresponding to a one point subspace in projective space is the same as the
  submodule determined by the point. -/
lemma of_submodule_singleton (a : ℙ K V) : subspace.equiv {a} = a.submodule :=
begin
  unfold equiv,
  simp_rw [rel_iso.coe_fn_mk, equiv.coe_fn_mk, mem_singleton_iff, supr_supr_eq_left],
end

/- A point in projective space is a member of a subspace iff the representative of the point is
  a member of the corresponding submodule. -/
lemma mem_of_subspace_iff (a : ℙ K V) (W : subspace K V) : a ∈ W ↔ a.rep ∈ subspace.equiv W :=
begin
  rw [← submodule.span_singleton_le_iff_mem, singleton_mem_iff_leq a W,
   ← subspace.equiv.map_rel_iff'],
  change (subspace.equiv) {a} ≤ (subspace.equiv) W ↔ submodule.span K {a.rep} ≤ equiv W,
  rw [of_submodule_singleton, ← submodule_mk a.rep (rep_nonzero a), mk_rep],
end

/- If a point is contained in the span of a set of points, then the point's representative is
  contained in the span of the set's representatives. -/
lemma in_span_in_rep_span (a : ℙ K V) (S : set (ℙ K V)) (h : a ∈ span S) :
  a.rep ∈ submodule.span K {v : V | ∃ s : ℙ K V, s ∈ S ∧  v = s.rep} :=
begin
  change a ∈ span_carrier S at h,
  induction h with a b c d e f g h i j k,
  { exact submodule.subset_span ⟨a, by { simpa }⟩ },
  { rcases  (dependent_triple_and_neq_pair f g) with ⟨p, q, hpq, hz ⟩,
    rw hz,
    exact submodule.add_mem _ (submodule.smul_mem _ p j) (submodule.smul_mem _ q k) },
end

/- The supremum of the submodules determined by the points in the span of set S is a submodule of
  the span of the representatives of the points in S. -/
lemma supr_span_submodule_leq_span (S : set (ℙ K V)) :
  (⨆ (x : ℙ K V) (hx : x ∈ span S), x.submodule) ≤
  submodule.span K {v : V | ∃ s : ℙ K V, s ∈ S ∧ v = s.rep} :=
begin
  intros x hx,
  apply submodule.supr_induction _ hx,
  { intros v y hy,
    dsimp at hy,
    sorry},
  { exact submodule.zero_mem _ },
  { intros y z hy hz, exact submodule.add_mem _ hy hz },
end

/- The submodule corresponding to the span of a set of points in projective space is
  the submodule spanned by the representatives of the points. -/
lemma of_submodule_eq_span_mem_reps (S : set (ℙ K V)) :
submodule.span K {v : V | ∃ s : ℙ K V, s ∈ S ∧  v = s.rep} = subspace.equiv (span S) :=
begin
  unfold equiv,
  rw [rel_iso.coe_fn_mk, equiv.coe_fn_mk],
  ext,
  split,
  { intro hx,
    apply submodule.span_induction hx,
    { intros y hy,
      refine submodule.mem_supr_of_mem (projectivization.mk K y _) _,
      rcases hy with ⟨s, ⟨hs, hsy⟩⟩,
      { rw hsy, exact rep_nonzero s },
      { rcases hy with ⟨z, ⟨hs, hy⟩⟩,
        simp_rw [submodule_mk, hy, mk_rep z],
        apply submodule.mem_supr_of_mem,
        exact (subset_span S hs),
        exact submodule.mem_span_singleton_self (z.rep) } },
    { simp },
    { intros y z hy hz, exact submodule.add_mem _ hy hz },
    { intros a y hy, exact submodule.smul_mem _ a hy } },
  { intro hxx, exact ((supr_span_submodule_leq_span S) hxx) },
end

/- The submodule corresponding to a line is the span of the
  representatives of the two points which determine the line. -/
lemma equiv_line_eq_span_reps (a b : ℙ K V) : submodule.span K {a.rep, b.rep} =
  subspace.equiv (line a b) :=
begin
  convert of_submodule_eq_span_mem_reps _,
  ext,
  simp only [set.mem_insert_iff, set.mem_singleton_iff, set.mem_set_of_eq],
  split,
  { rintro ⟨ha, hb⟩,
    { use a, simpa },
    { use b, simpa } },
  { rintro ⟨y, hy⟩,
    rcases hy with ⟨⟨hab, hab⟩, hr⟩, exact or.inl hr, rw hy_left at hr, exact or.inr hr }
end

/- The line determined by a single point is the one-point subspace containing that point. -/
lemma P1 (a : ℙ K V) : (line a a) = {a} :=
by { unfold line, rw set.pair_eq_singleton, exact span_subspace_self {a} }

/- A point in projective space is a member of any line it determines. -/

lemma P2 (a b : ℙ K V) : a ∈ line b a :=
begin
  refine subset_span {b, a} _,
  simp only [set.mem_insert_iff, set.mem_singleton, or_true],
end

lemma P2_ref (a b : ℙ K V) : a ∈ line a b :=
begin
  refine subset_span {a, b} _,
  simp only [set.mem_insert_iff, eq_self_iff_true, true_or],
end

/- If -/
lemma P3 (a b p c d : ℙ K V) (h1: a ≠ c) (h2: a ∈ line b p) (h3: p ∈ line c d) :
(∃ q : ℙ K V, q ∈ line a c ∩ line b d) :=
begin
  by_cases hbp : b = p,
  { refine ⟨b, _, P2_ref b d ⟩,
    rw [hbp, P1, mem_singleton_iff] at h2, rw [hbp, h2], exact P2_ref p c },
  { by_cases hcd : c = d,
    { use d,
      rw hcd, exact ⟨P2 d a, P2 d b⟩ },
    { simp_rw [mem_of_subspace_iff, ← equiv_line_eq_span_reps] at *,
      change b ≠ p at hbp,
      change c ≠ d at hcd,
      rw [← pair_independent_iff_neq, independent_iff, fin_comp_commutes₂] at hbp hcd,
      sorry } },
end

end subspace

end projectivization
