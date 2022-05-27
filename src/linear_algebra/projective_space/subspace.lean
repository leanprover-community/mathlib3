import linear_algebra.projective_space.dependent
import linear_algebra
import linear_algebra.finsupp
import linear_algebra.finite_dimensional
import algebra.module.submodule.basic
import order.copy
import tactic

variables (K V : Type*) [field K] [add_comm_group V] [module K V]

namespace projectivization

open_locale classical

/- A subspace of projective space is a set of points such that if two nonzero vectors determine
  points in the set, and their sum is nonzero, then the point their sum determines is also
  in the set. -/
@[ext] structure subspace :=
(carrier : set (ℙ K V))
(mem_add' (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v + w ≠ 0) :
  mk K v hv ∈ carrier → mk K w hw ∈ carrier → mk K (v + w) (hvw) ∈ carrier)

namespace subspace

variables {K V}

instance : set_like (subspace K V) (ℙ K V) :=
{ coe := carrier,
  coe_injective' := λ A B, by { cases A, cases B, simp } }

@[simp]
lemma mem_carrier_iff (A : subspace K V) (x : ℙ K V) : x ∈ A.carrier ↔ x ∈ A := iff.refl _

lemma mem_add (T : subspace K V) (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v + w ≠ 0) :
  projectivization.mk K v hv ∈ T → projectivization.mk K w hw ∈ T →
  projectivization.mk K (v + w) (hvw) ∈ T :=
  T.mem_add' v w hv hw hvw

open_locale big_operators

/- The span of a set of points in projective space is a set of points which contains the original
set, and contains all points that represent the (nonzero) sum of two nonzero vectors which determine
points in the span. -/
inductive span_carrier (S : set (ℙ K V)) : set (ℙ K V)
| of (x : ℙ K V) (hx : x ∈ S) : span_carrier x
| mem_add (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v + w ≠ 0) :
    span_carrier (projectivization.mk K v hv) → span_carrier (projectivization.mk K w hw) →
    span_carrier (projectivization.mk K (v + w) (hvw))

/- The span of a set of points in projective space is a subspace. -/
def span (S : set (ℙ K V)) : subspace K V :=
{ carrier := span_carrier S,
  mem_add' := λ v w hv hw hvw,
    span_carrier.mem_add v w hv hw hvw }

/- The span of a set of points contains the set. -/
lemma subset_span (S : set (ℙ K V)) : S ⊆ span S :=
λ x hx, span_carrier.of _ hx

/- The span of a subspace is itself. -/
@[simp] lemma span_coe (W : subspace K V) : span ↑W = W :=
begin
  ext, split; intro hx,
  { induction hx with a ha u w hu hw huw _ _ hum hwm,
    exact ha,
    exact mem_add W u w hu hw huw hum hwm },
  { exact subset_span W hx },
end

def gi : galois_insertion (span : set (ℙ K V) → subspace K V) coe :=
{ choice := λ S hS, span S,
  gc := λ A B, ⟨λ h, le_trans (subset_span _) h, begin
    intros h x hx,
    induction hx,
    { apply h, assumption },
    { apply B.mem_add, assumption' }
  end⟩,
  le_l_u := λ S, subset_span _,
  choice_eq := λ _ _, rfl }

instance has_top : has_top (subspace K V) :=
⟨⟨⊤, λ _ _ _ _ _ _ _, trivial⟩⟩

instance has_bot : has_bot (subspace K V) :=
⟨⟨⊥, λ v w hv hw hvw h, h.elim⟩⟩

instance has_inf : has_inf (subspace K V) :=
⟨λ A B, ⟨A ⊓ B, λ v w hv hw hvw h1 h2,
  ⟨A.mem_add _ _ hv hw _ h1.1 h2.1, B.mem_add _ _ hv hw _ h1.2 h2.2⟩⟩⟩

instance has_Inf : has_Inf (subspace K V) :=
⟨λ A, ⟨Inf (coe '' A), λ v w hv hw hvw h1 h2 t, begin
  rintro ⟨s,hs,rfl⟩,
  exact s.mem_add v w hv hw _ (h1 s ⟨s,hs,rfl⟩) (h2 s ⟨s,hs,rfl⟩),
end⟩⟩

/- The Galois insertion determines a complete lattice structure on the subspaces of a
  projective space. -/
instance : complete_lattice (subspace K V) :=
{ sup := λ A B, Inf { E | A ≤ E ∧ B ≤ E },
  le_sup_left := begin
    rintros A B x hx E ⟨E,hE,rfl⟩,
    exact hE.1 hx,
  end,
  le_sup_right := begin
    rintros A B x hx E ⟨E,hE,rfl⟩,
    exact hE.2 hx,
  end,
  sup_le := λ A B C h1 h2 x hx, hx C ⟨C,⟨h1,h2⟩, rfl⟩,
  inf_le_left := λ A B x hx, by exact hx.1,
  inf_le_right := λ A B x hx, by exact hx.2,
  le_inf := λ A B C h1 h2 x hx, ⟨h1 hx, h2 hx⟩,
  Sup := λ A, Inf { E | ∀ U ∈ A, U ≤ E },
  le_Sup := begin
    rintros S A hA x hx E ⟨E,hE,rfl⟩,
    exact hE _ hA hx,
  end,
  Sup_le := λ S A hA x hx, hx A ⟨A, hA, rfl⟩,
  Inf_le := λ S A hA x hx, by exact hx _ ⟨A, hA, rfl⟩,
  le_Inf := begin
    rintros S A hA x hx E ⟨E,hE,rfl⟩,
    exact hA _ hE hx,
  end,
  le_top := λ E x hx, trivial,
  bot_le := λ E x hx, hx.elim,
  ..(infer_instance : has_Inf _),
  ..(infer_instance : has_inf _),
  ..(infer_instance : has_top _),
  ..(infer_instance : has_bot _),
  ..set_like.partial_order }

/- The subspace associated to a submodule is the set of points whose representative's are
  are contained in the submodule. -/
def of_submodule (H : submodule K V) : subspace K V :=
{ carrier := { x | x.submodule ≤ H },
  mem_add' :=
  begin
    intros v w hv hw hvw h1 h2,
    simp only [set.mem_set_of_eq, submodule_mk, submodule.span_singleton_le_iff_mem] at h1 h2 ⊢,
    exact H.add_mem h1 h2,
  end }

/- The supremum of the submodules determined by the points in the span of a set S is a submodule of
  the span of the representatives of the points in S. -/
lemma bsupr_submodule_eq_span_image_rep (S : set (ℙ K V)) :
  (⨆ (x : ℙ K V) (hx : x ∈ span S), x.submodule) = submodule.span K (projectivization.rep '' S) :=
begin
  ext,
  split; intro hx,
  { apply submodule.supr_induction _ hx,
    { intros v y hy,
      apply ((submodule.mem_supr _).1) hy (submodule.span K (projectivization.rep '' S)),
      clear hy,
      intro hv,
      induction hv with s hs _ _ _ _ _ _ _ hus hws,
      { rw [← mk_rep s, submodule_mk, submodule.span_singleton_le_iff_mem],
        exact submodule.subset_span ⟨s, ⟨hs, rfl⟩⟩ },
      { rw [submodule_mk, submodule.span_singleton_le_iff_mem] at *,
        exact submodule.add_mem _ hus hws } },
    { exact submodule.zero_mem _ },
    { intros y z hy hz, exact submodule.add_mem _ hy hz } },
  { refine (submodule.span_le.2) _ hx,
    rintros y ⟨v, ⟨hs, hv⟩⟩,
    refine submodule.mem_supr_of_mem v (submodule.mem_supr_of_mem (subspace.subset_span S hs) _),
    rw [← hv, ← mk_rep v, submodule_mk, mk_rep],
    exact submodule.mem_span_singleton_self (v.rep) },
end

/- If the representative of a point is contained in the span of the set of representatives of a
  subspace, then that point is contained in the subspace. -/
lemma rep_mem_reps_span (v : ℙ K V) (S : subspace K V)
  (hv : v.rep ∈ submodule.span K (projectivization.rep '' (S : set (ℙ K V)))) : v ∈ S :=
begin
  suffices h : ∀ (v : V), v ∈ (submodule.span K (projectivization.rep '' (S : set (ℙ K V)))) →
    v ≠ 0 → (∃ (hv : v ≠ 0), projectivization.mk K v hv ∈ S), by
    { specialize h v.rep hv (rep_nonzero v), simp_rw mk_rep at h, cases h with _ hs, exact hs },
  clear hv,
  intros v hv,
  apply submodule.span_induction hv,
  { intros w hw _,
    rcases hw with ⟨s, ⟨hs, hw⟩⟩,
    simp_rw ← hw,
    exact ⟨rep_nonzero s, by { rwa mk_rep s }⟩ },
  { intro h, exfalso, exact h (eq.refl 0) },
  { intros u w hu hw huw,
    by_cases h1 : w = 0; by_cases h2 : u = 0,
    { rw [h1, h2, zero_add] at huw, exfalso, exact huw (eq.refl 0) },
    { rw [h1, add_zero], specialize hu h2, cases hu with _ hu, exact ⟨hu_w, hu⟩ },
    { rw [h2, zero_add], specialize hw h1, cases hw with _ hw, exact ⟨hw_w, hw⟩ },
    { use huw, specialize hu h2, specialize hw h1, cases hu with _ _, cases hw with _ _,
      exact mem_add S u w hu_w hw_w huw hu_h hw_h } },
  { intros a u hus hau,
    have hu : u ≠ 0, by { intro h, rw [h, smul_zero] at hau, exact hau (eq.refl 0) },
    cases (hus hu) with hu hus,
    use hau,
    convert hus using 1,
    rw mk_eq_mk_iff', exact ⟨a, refl _⟩ }
end

open_locale big_operators classical
/- There is an order preserving bijection between subspaces of ℙ K V and submodules of V. -/
def equiv : subspace K V ≃o submodule K V :=
{ to_fun := λ S, ⨆ (x : ℙ K V) (hx : x ∈ S), x.submodule,
  inv_fun := of_submodule,
  left_inv :=
  begin
    intros W,
    ext,
    unfold of_submodule,
    rw [← span_coe W, bsupr_submodule_eq_span_image_rep, span_coe W, set.mem_set_of_eq,
      ← mk_rep x, submodule_mk, mk_rep x, submodule.span_singleton_le_iff_mem],
    split; intro hx,
    { exact rep_mem_reps_span x W hx },
    { exact submodule.subset_span ⟨x, ⟨hx, eq.refl x.rep⟩⟩ },
  end,
  right_inv :=
  begin
    intros W, dsimp, unfold of_submodule,
    change (⨆ (x : ℙ K V) (x_1 : x.submodule ≤ W), x.submodule) = W,
    apply le_antisymm,
    { refine (supr_le _), simp },
    { intros x hx,
      by_cases hxt : x = 0,
      { rw hxt, exact submodule.zero_mem _ },
      { rw ← submodule.span_singleton_le_iff_mem x,
        refine le_Sup ⟨projectivization.mk K x hxt, _ ⟩,
        simp only [submodule_mk, submodule.span_singleton_le_iff_mem, supr_pos hx] } },
  end,
  map_rel_iff' :=
  begin
    intros W S,
    rw [equiv.coe_fn_mk, ← span_coe W, ← span_coe S, bsupr_submodule_eq_span_image_rep ↑S,
      bsupr_submodule_eq_span_image_rep ↑W, span_coe S, span_coe W],
    split,
    { intros hw v hv, exact rep_mem_reps_span v S (hw (submodule.subset_span ⟨v, ⟨hv, rfl⟩⟩)) },
    { intro h, apply submodule.span_mono, exact set.image_subset projectivization.rep h },
  end, }

/-  If two nonzero vectors go to the same point in projective space, and their sum is nonzero,
  then their sum also goes to that same point.-/
lemma eq_mk_sum_mk {v u : V} {w : (ℙ K V)} {hv : v ≠ 0} {hu : u ≠ 0} (hvu : v + u ≠ 0)
  (hva : projectivization.mk K v hv = w) (hua : projectivization.mk K u hu = w) :
  projectivization.mk K (v + u) hvu = w :=
begin
  cases exists_smul_mk_rep_eq K v hv with a ha,
  cases exists_smul_mk_rep_eq K u hu with b hb,
  simp_rw [hva, hua] at *,
  rw [← mk_rep w, mk_eq_mk_iff'],
  exact ⟨a + b, by { rw [hb, ha, add_smul], refl }⟩,
end

/- A set containing a single point is a subspace. -/
instance : has_singleton (ℙ K V) (subspace K V):=
{ singleton := λ a,
{ carrier := {a},
  mem_add' :=
  by { intros v w hv hw hvw h1 h2, rw set.mem_singleton_iff at *, exact eq_mk_sum_mk hvw h1 h2 } } }

/- A point belongs to a singleton subspace iff the point is equal to the singleton determining
  the subspace. -/
lemma mem_singleton_iff (a b : ℙ K V) : b ∈ ({a} : subspace K V) ↔ b = a :=
  by { exact ⟨by { intro hb, induction hb, refl }, by { intro h, rw h, split }⟩ }

example (A B : submodule K V) :
  ((A ⊔ B : submodule K V)) = Inf { E | A ≤ E ∧ B ≤ E } :=
begin
  refl,
end

/- The line determined by two points in projective space is the subspace give by their span. -/
def line (a b : ℙ K V) : subspace K V := span {a, b}

/- A point in projective space is a member of a subspace iff the singleton subspace determined by
  that point is in the subspace. -/
lemma singleton_mem_iff_leq (a : ℙ K V) (W : subspace K V) : a ∈ W ↔ {a} ≤ W :=
  by { change a ∈ W ↔ ({a} : set (ℙ K V)) ⊆ W, rw [set.singleton_subset_iff, set_like.mem_coe] }

/- The submodule corresponding to a one point subspace in projective space is the same as the
  submodule determined by the point, i.e it is the submodule give by the span of the representative
  of the point. -/
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

/- A nonzero vector belongs to a submodule iff the representative of the point it goes to in
  projective space beongs to that submodule. -/
lemma rep_mem_submodule_iff (T : submodule K V) (v : V) (hv : v ≠ 0) :
  (projectivization.mk K v hv).rep ∈ T ↔ v ∈ T :=
begin
  cases exists_smul_eq_mk_rep K v hv with a ha,
  convert submodule.smul_mem_iff T (units.ne_zero a),
  exact ha.symm
end

/- If a point is contained in the span of a set of points, then the point's representative is
  contained in the span of the set's representatives. -/
lemma in_span_in_rep_span (v : ℙ K V) (S : set (ℙ K V)) (h : v ∈ span S) :
  v.rep ∈ submodule.span K (projectivization.rep '' S) :=
begin
  induction h with u v w s hw hs hws h1 h2 hwr hsr,
  { exact submodule.subset_span ⟨u, by { simpa }⟩ },
  { rw rep_mem_submodule_iff at *, exact submodule.add_mem _ hwr hsr },
end

/- The submodule corresponding to the span of a set of points in projective space is
  the submodule spanned by the representatives of the points. -/
lemma of_submodule_eq_span_mem_reps (S : set (ℙ K V)) :
submodule.span K (projectivization.rep '' S) = subspace.equiv (span S) :=
  by { exact (bsupr_submodule_eq_span_image_rep S).symm }

/- The submodule corresponding to a line in projective space is the span of the
  representatives of the two points which determine the line. -/
lemma equiv_line_eq_span_reps (a b : ℙ K V) : submodule.span K {a.rep, b.rep} =
  subspace.equiv (line a b) :=
  by { convert of_submodule_eq_span_mem_reps _, rw set.image_pair }

/- The line determined by two points in projective space does not depend on their order. -/
lemma line_symm (u v : ℙ K V) : line u v = line v u :=
  by { unfold line, rw set.pair_comm u v }

/- Elements are contained in the intersection of two submodules/subspaces iff they are contained
  in both of the modules/subspaces. -/

lemma submodule_mem_inter_iff (W S : submodule K V) (v : V) : v ∈ W ⊓ S ↔ v ∈ W ∧ v ∈ S :=
  by { refl }

lemma mem_inter_iff (W S : subspace K V) (v : ℙ K V) : v ∈ W ⊓ S ↔ v ∈ W ∧ v ∈ S :=
  by { refl }

/- The submodule corresponding to the intersection of two subspaces is the intersection of the
  two submodules corresponding to the respective subspaces. -/
lemma inter_equiv_eq_equiv_inter (W S : subspace K V) :
  subspace.equiv (W ⊓ S) = (subspace.equiv W) ⊓ (subspace.equiv S) :=
begin
  ext,
  by_cases hx : x = 0,
  { rw hx, simp },
  { simp_rw [submodule_mem_inter_iff, ← rep_mem_submodule_iff _ x hx,
      ← mem_of_subspace_iff, mem_inter_iff] }
end

/- The line determined by a single point is the one-point subspace containing that point. -/
lemma P1 (a : ℙ K V) : (line a a) = {a} :=
by { unfold line, rw set.pair_eq_singleton, exact span_coe {a} }

/- A point in projective space is a member of any line it determines. -/

lemma P2 (a b : ℙ K V) : a ∈ line a b :=
begin
  refine subset_span {a, b} _,
  simp only [set.mem_insert_iff, eq_self_iff_true, true_or],
end

lemma P2_ref (a b : ℙ K V) : a ∈ line b a :=
begin
  refine subset_span {b, a} _,
  simp only [set.mem_insert_iff, set.mem_singleton, or_true],
end

/- If two points determine a line, and another point is contained in that line, then the line
  determined by the new point and one of the original points is contained in the original line. -/

lemma mem_line_le_line₁ (u v w : ℙ K V) (hu : u ∈ line v w) : line u w ≤ line v w :=
begin
  simp_rw mem_of_subspace_iff at hu,
  rw ← equiv.map_rel_iff',
  change equiv (line u w) ≤ equiv (line v w),
  simp_rw [← equiv_line_eq_span_reps, submodule.span_le] at *,
  intros x hx,
  rcases hx,
  { rwa hx },
  { rw [set.mem_singleton_iff] at hx, rw hx, refine submodule.subset_span _, simp },
end

lemma mem_line_le_line₂ (u v w : ℙ K V) (hu : u ∈ line v w) : line v u ≤ line v w :=
  by {  rw [line_symm v w, line_symm v u] at *, exact mem_line_le_line₁ u w v hu }

/- If a point is contained in the line deterimined by two other points, and the point is not equal
  to one of the points which determines the line, then the other point which determines the
  original line is contained in the line determined by the two nonequal points. -/
lemma line_exchange (u v w : ℙ K V) (huv : v ≠ u) (h : u ∈ line v w) : w ∈ line u v :=
begin
  simp_rw [mem_of_subspace_iff, ← equiv_line_eq_span_reps, set.pair_comm v.rep w.rep] at *,
  refine mem_span_insert_exchange h _,
  intro ha,
  rw [submodule.mem_span_singleton] at ha,
  rw [← mk_rep v, ← mk_rep u] at huv,
  exact huv.symm ((mk_eq_mk_iff' K u.rep v.rep (rep_nonzero u) (rep_nonzero v)).2 ha)
end


/- If -/
lemma P3 (a b p c d : ℙ K V) (h1: a ≠ c) (h2: a ∈ line b p) (h3: p ∈ line c d) :
(∃ q : ℙ K V, q ∈ line a c ⊓ line b d) :=
begin
  by_cases hbp : b = p,
  { refine ⟨b, _, P2 b d ⟩,
    rw [hbp, P1, mem_singleton_iff] at h2, rw [hbp, h2], exact P2 p c },
  { by_cases hcd : c = d,
    { use d,
      rw hcd, exact ⟨P2_ref d a, P2_ref d b⟩ },
    { by_cases hab : a = b,
      { rw hab, use b, exact ⟨P2 b c,P2 b d⟩ },
      { by_cases hbd : b = d,
        { rw ← hbd at *,
          have := mem_line_le_line₂ p b c,
          rw line_symm c b at h3,
          specialize this h3 h2,
          refine ⟨b, _, P2 b b⟩,
          rw line_symm b c at this,
          exact line_exchange a c b (ne.symm h1) this },
        { simp_rw [mem_of_subspace_iff, ← equiv_line_eq_span_reps, ← ne.def,
            ← pair_independent_iff_neq, independent_iff, fin_comp_commutes₂,
            inter_equiv_eq_equiv_inter, ← equiv_line_eq_span_reps] at *,
          suffices h : ∃ (v : V) (hv : v ≠ 0),
            v ∈ submodule.span K {a.rep, c.rep} ⊓ submodule.span K {b.rep, d.rep}, by
            { rcases h with ⟨v, ⟨ hv, hvm⟩⟩, refine ⟨projectivization.mk K v hv, _⟩,
              rwa rep_mem_submodule_iff },
          by_contra,
          simp only [ne.def, exists_prop, not_exists, not_and] at h,
          sorry } } } },
end

end subspace

end projectivization
