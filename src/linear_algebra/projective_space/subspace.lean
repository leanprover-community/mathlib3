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
lemma subset_span (S : set (ℙ K V)) : S ⊆ span S := λ x hx, span_carrier.of _ hx

/- The span of a subspace is the subspace. -/
@[simp] lemma span_coe (W : subspace K V) : span ↑W = W :=
begin
  ext, split; intro hx,
  { induction hx with a ha u w hu hw huw _ _ hum hwm,
      { exact ha },
      { exact mem_add W u w hu hw huw hum hwm } },
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

/- The projective space is the top of the lattice of subspaces. -/
instance has_top : has_top (subspace K V) :=
⟨⟨⊤, λ _ _ _ _ _ _ _, trivial⟩⟩

/- The empty set is the bottom of the lattice of subspaces. -/
instance has_bot : has_bot (subspace K V) :=
⟨⟨⊥, λ v w hv hw hvw h, h.elim⟩⟩

/- The infimum of two subspaces exists. -/
instance has_inf : has_inf (subspace K V) :=
⟨λ A B, ⟨A ⊓ B, λ v w hv hw hvw h1 h2,
  ⟨A.mem_add _ _ hv hw _ h1.1 h2.1, B.mem_add _ _ hv hw _ h1.2 h2.2⟩⟩⟩

/- A point is a member of the infimum of two subspaces iff it is a member of each subspace. -/
@[simp]
lemma mem_inf {v : ℙ K V} {W S : subspace K V} : v ∈ W ⊓ S ↔ v ∈ W ∧ v ∈ S := iff.rfl

/- Infimums of arbitrary collections of subspaces exist. -/
instance has_Inf : has_Inf (subspace K V) :=
⟨λ A, ⟨Inf (coe '' A), λ v w hv hw hvw h1 h2 t, begin
  rintro ⟨s,hs,rfl⟩,
  exact s.mem_add v w hv hw _ (h1 s ⟨s,hs,rfl⟩) (h2 s ⟨s,hs,rfl⟩),
end⟩⟩

/- Projective subspaces form a complete lattice. -/
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

/- If a set of points is a subset of another set of points, its span will
  be contained in the span of that set-/
lemma span_mono {S T : set (ℙ K V)} (h : S ⊆ T) : span S ≤ span T :=
begin
  rintros s hs, induction hs with u hu v w hv hw hvw _ _ hvt hwt,
  { exact subset_span T (h hu) },
  { exact mem_add (span T) v w hv hw hvw hvt hwt },
end

/- The span of a set of points is contained in a subspace iff the set of points is contained in the
  subspace. -/
lemma span_le_subspace_iff {S : set (ℙ K V)} {W : subspace K V} : span S ≤ W ↔ S ⊆ W :=
begin
  split; intro h,
  { change S ≤ W, exact le_trans (subset_span S) h },
  { rw ← span_coe W, exact (span_mono h) },
end

/- The span of a set of points in projective space is the infimum of the subspaces
  containig the set. -/
lemma span_eq_inf_ge (S : set (ℙ K V)) : span S = Inf {T : subspace K V | S ≤ T} :=
begin
  apply le_antisymm,
  { refine le_Inf _,
    rintros T hT,
    rwa [set.le_eq_subset, set.mem_set_of_eq, ← span_le_subspace_iff] at hT },
  { exact Inf_le (subset_span S) },
end

/- The supremum of two subspaces is the span of their union. -/
lemma sup_eq_span_union {W S : subspace K V} : W ⊔ S = span (W ∪ S) :=
begin
  apply le_antisymm,
  { refine sup_le _ _,
    { rw ← span_coe W, apply span_mono, rw span_coe, simp },
    { rw ← span_coe S, apply span_mono, rw span_coe, simp } },
  { rw span_le_subspace_iff, simp },
end

/- The supremum of a set of subspaces is the span of the union of the subspaces. -/
lemma Sup_eq_span_union (S : set (subspace K V)) :
  Sup S = span ⋃ (W : subspace K V) (hW : W ∈ S), ↑W :=
begin
  apply le_antisymm,
  { refine Sup_le _,
    intros W hW, rw ← span_coe W, apply span_mono, exact set.subset_bUnion_of_mem hW },
  { simp_rw [span_le_subspace_iff, set.Union₂_subset_iff], intros s hs, exact le_Sup hs },
end

/- The subspace associated to a submodule consists of the points whose representatives
  are contained in the submodule. -/
def of_submodule (H : submodule K V) : subspace K V :=
{ carrier := { x | x.submodule ≤ H },
  mem_add' :=
  begin
    intros v w hv hw hvw h1 h2,
    simp only [set.mem_set_of_eq, submodule_mk, submodule.span_singleton_le_iff_mem] at h1 h2 ⊢,
    exact H.add_mem h1 h2,
  end }

/- The supremum of the collection of submodules determined by the points in the span of a set S
  is a submodule of the span of the representatives of the points in S. -/
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
  { rintros w ⟨s, ⟨hs, rfl⟩⟩ _, exact ⟨rep_nonzero s, by { rwa mk_rep s }⟩ },
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


/- There is an order preserving bijection between subspaces of ℙ K V and submodules of V. -/
def equiv : subspace K V ≃o submodule K V :=
{ to_fun := λ S, ⨆ (x : ℙ K V) (hx : x ∈ S), x.submodule,
  inv_fun := of_submodule,
  left_inv :=
  begin
    intros W, ext, unfold of_submodule,
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
        refine le_Sup ⟨projectivization.mk K x hxt, _⟩,
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


/- If two nonzero vectors go to the same point in projective space, and their sum is nonzero,
  then the sum of the two vectors also goes to that same point.-/
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
      by { intros _ _ _ _ _ h1 h2, rw set.mem_singleton_iff at *, exact eq_mk_sum_mk _ h1 h2 } } }

/- A point belongs to a singleton subspace iff the point is equal to the singleton determining
  the subspace. -/
lemma mem_singleton_iff (a b : ℙ K V) : b ∈ ({a} : subspace K V) ↔ b = a :=
  by { exact ⟨by { intro hb, induction hb, refl }, by { intro h, rw h, split }⟩ }

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
lemma mem_subspace_iff (a : ℙ K V) (W : subspace K V) : a ∈ W ↔ a.rep ∈ subspace.equiv W :=
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

/- The submodule corresponding to the intersection of two subspaces is the intersection of the
  two submodules corresponding to the respective subspaces. -/
lemma equiv_inf_eq_inf_equiv (W S : subspace K V) :
  subspace.equiv (W ⊓ S) = (subspace.equiv W) ⊓ (subspace.equiv S) :=
  by { exact order_iso.map_inf equiv W S }

lemma equiv_sup_eq_sup_equiv (W S : subspace K V) :
  subspace.equiv (W ⊔ S) = (subspace.equiv W) ⊔ (subspace.equiv S) :=
  by { exact order_iso.map_sup equiv W S }


/- Due to the order preserving bijection between subspaces of ℙ K V and submodules of V
  the subspaces of ℙ K V form a modular lattice. -/
instance : is_modular_lattice (subspace K V) :=
{ sup_inf_le_assoc_of_le :=
  begin
    intros x y z hxz,
    rw ← subspace.equiv.map_rel_iff' at hxz ⊢,
    change (equiv) ((x ⊔ y) ⊓ z) ≤ (equiv) (x ⊔ y ⊓ z),
    change (equiv) x ≤ (equiv) z at hxz,
    simp_rw [equiv_sup_eq_sup_equiv, equiv_inf_eq_inf_equiv] at hxz ⊢,
    rw equiv_sup_eq_sup_equiv,
    exact is_modular_lattice.sup_inf_le_assoc_of_le (equiv y) hxz,
  end }

/- The lattice of subspaces of a projective space is complemented. -/
instance : is_complemented (subspace K V) :=
  by { rw (order_iso.is_complemented_iff (@equiv K V _ _ _)), apply_instance }

/- A subspace is the supremum of the singleton subspaces formed by its elements. -/
lemma subspace_eq_sup_singletons (W : subspace K V) :
  W = Sup {S | ∃ (v : ℙ K V) (hv : v ∈ W), S = {v}} :=
begin
  apply le_antisymm,
  { intros w hW, rw singleton_mem_iff_leq, exact le_Sup ⟨w, ⟨hW, rfl⟩⟩ },
  { refine Sup_le _, rintros S ⟨v, ⟨hW, rfl⟩⟩, rwa ← singleton_mem_iff_leq, },
end

/- Singleton subspaces are compact elements of the lattice of subspaces. -/
lemma singletons_compact (v : ℙ K V) :
  complete_lattice.is_compact_element ({v} : subspace K V) :=
begin
  simp_rw [complete_lattice.is_compact_element_iff_le_of_directed_Sup_le, ← singleton_mem_iff_leq,
    Sup_eq_span_union],
  intros S hS hSd hv,
  induction hv with u hu w s hw hs hws _ _ hwS hsS,
  { rw set.mem_Union₂ at hu, rcases hu with ⟨T, ⟨hTS, hTu⟩⟩, exact ⟨T, ⟨hTS, hTu⟩⟩ },
  { rcases hwS with ⟨T,⟨hT, hwT⟩⟩,
    rcases hsS with ⟨U,⟨hU, hsU⟩⟩,
    rcases (hSd T hT U hU) with ⟨E, ⟨hES, hE⟩⟩,
    exact ⟨E, ⟨hES, mem_add E w s hw hs hws (hE.1 hwT) (hE.2 hsU)⟩⟩ }
end

/- The lattice of subspaces of a projective space is compactly generated. -/
instance : is_compactly_generated (subspace K V) :=
  { exists_Sup_eq :=
    begin
      intro W,
      use {S | ∃ (v : ℙ K V) (hv : v ∈ W), S = {v}},
      split,
      { rintros T ⟨v, ⟨hv, rfl⟩⟩, exact singletons_compact v },
      { exact (subspace_eq_sup_singletons W).symm },
    end }

/- Since the the lattice of subspaces ℙ K V is compactly generated
  and there is an order preserving bijection between subspaces of ℙ K V and submodules
  of V, the lattice of subspaces of ℙ K V is atomistic. -/
instance : is_atomistic (subspace K V) :=
  by { rw ← is_complemented_iff_is_atomistic, apply_instance }


/- The line determined by two points in projective space is the subspace give by their span. -/
def line (a b : ℙ K V) : subspace K V := span {a, b}

infix ` ⋆ `: 100 := line

/- The submodule corresponding to a line in projective space is the span of the
  representatives of the two points which determine the line. -/
lemma equiv_line_eq_span_reps (a b : ℙ K V) : submodule.span K {a.rep, b.rep} =
  subspace.equiv (a ⋆ b) :=
  by { convert of_submodule_eq_span_mem_reps _, rw set.image_pair }

/- The line determined by two points in projective space does not depend on their order. -/
lemma line_symm (u v : ℙ K V) : u ⋆ v = v ⋆ u :=
  by { unfold line, rw set.pair_comm u v }

/- A subspace contatins all of the lines through its points. -/
lemma subspace_contains_lines {u v w: ℙ K V} {W : subspace K V} (hu : u ∈ W) (hv : v ∈ W) :
  u ⋆ v ≤ W :=
  by { unfold line, rw span_le_subspace_iff, intros x hx, cases hx, rwa hx,
    simp only [set.mem_singleton_iff] at hx, rwa hx }

/- The line determined by a single point is the singleton subspace containing that point. -/
lemma P1 (a : ℙ K V) : a ⋆ a = {a} :=
  by { unfold line, rw set.pair_eq_singleton, exact span_coe {a} }

/- A point in projective space is a member of any line it determines. -/
lemma P2 (a b : ℙ K V) : a ∈ a ⋆ b :=
  by { refine subset_span {a, b} _, simp }

lemma P2_ref (a b : ℙ K V) : a ∈ b ⋆ a :=
  by { rw line_symm b a, exact P2 a b }


/- If two points determine a line, and another point is contained in that line, then the line
  determined by the new point and one of the original points is contained in the original line. -/

lemma mem_line_le_line₁ {u v w : ℙ K V} (hu : u ∈ v ⋆ w) : u ⋆ w ≤ v ⋆ w :=
begin
  simp_rw mem_subspace_iff at hu,
  rw ← equiv.map_rel_iff',
  change equiv (u ⋆ w) ≤ equiv (v ⋆ w),
  simp_rw [← equiv_line_eq_span_reps, submodule.span_le] at hu ⊢,
  intros x hx,
  rcases hx,
  { rwa hx },
  { rw [set.mem_singleton_iff] at hx, rw hx, refine submodule.subset_span _, simp },
end

lemma mem_line_le_line₂ {u v w : ℙ K V} (hu : u ∈ v ⋆ w) : v ⋆ u ≤ v ⋆ w :=
  by { rw [line_symm v w, line_symm v u] at *, exact mem_line_le_line₁ hu }


/- If a point is contained in the line deterimined by two other points, and the point is not equal
  to one of the points which determines the line, then the other point which determines the
  original line is contained in the line determined by the two nonequal points. -/
lemma line_exchange {u v w : ℙ K V} (huv : u ≠ v) (h : u ∈ v ⋆ w) : w ∈ u ⋆ v :=
begin
  simp_rw [mem_subspace_iff, ← equiv_line_eq_span_reps, set.pair_comm v.rep w.rep] at *,
  refine mem_span_insert_exchange h _,
  intro ha,
  rw [submodule.mem_span_singleton] at ha,
  rw [← mk_rep v, ← mk_rep u] at huv,
  exact huv ((mk_eq_mk_iff' K u.rep v.rep (rep_nonzero u) (rep_nonzero v)).2 ha)
end

/- A vector is in the span of two other vectors iff it is a linear combination of them. -/
lemma mem_span_pair {u v w : V} :
  (u ∈ (@submodule.span K V _ _ _ {v, w})) ↔ (∃ (a b : K), u = a • v + b • w) :=
  by { simp_rw [submodule.mem_span_insert, submodule.mem_span_singleton], simp }

lemma mem_span_mem_of_span_insert {u v w s : V} (hv : v ∈ @submodule.span K V _ _ _ {w, s}) :
  (submodule.span K {u, v}) ≤ (@submodule.span K V _ _ _ {u, w, s}) :=
begin
  rw @submodule.span_le K V _ _ _,
  intros x hx,
  rw [set.mem_insert_iff, set.mem_singleton_iff] at hx,
  cases hx with hx hx; rw hx,
  { refine submodule.subset_span _, simp },
  { refine submodule.span_mono _ hv, simp },
end

/- If -/
lemma P3 {a b p c d : ℙ K V} (h1: a ≠ c) (h2: a ∈ b ⋆ p) (h3: p ∈ c ⋆ d) :
  (∃ q : ℙ K V, q ∈ a ⋆ c ⊓ b ⋆ d) :=
begin
  simp_rw [mem_subspace_iff, equiv_inf_eq_inf_equiv, ← equiv_line_eq_span_reps] at *,
  suffices : ∃ (v : V) (hv : v ≠ 0),
    v ∈ submodule.span K {a.rep, c.rep} ⊓ submodule.span K {b.rep, d.rep}, by
    { rcases this with ⟨v, ⟨hv, hvm⟩⟩, use projectivization.mk K v hv, rwa rep_mem_submodule_iff },
  let ha := (mem_span_mem_of_span_insert h3) h2,
  simp_rw [submodule.mem_span_insert, submodule.mem_span_singleton] at ha,
  rcases ha with ⟨y, v, ⟨x, u, ⟨⟨z, rfl⟩, rfl⟩⟩, ha⟩,
  use a.rep + - (x • c.rep),
  apply_fun (λ (i : V), - (x • c.rep) + i) at ha,
  abel at ha,
  simp_rw [neg_one_smul, ← neg_smul] at *,
  split,
    { intro h,
      rw [← one_smul K a.rep] at h,
      rw [← pair_independent_iff_neq, independent_iff_not_dependent] at h1,
      exact h1 ((dependent_iff_reps_dependent₂ a c).2 ⟨1, -x, ⟨by { simp }, h⟩⟩) },
    { split,
      { rw [set_like.mem_coe, mem_span_pair], use [1, -x], simp },
      { rw [ha, set_like.mem_coe, mem_span_pair], use [y, z] } }
end

lemma P7 {a b c : ℙ K V} (hab : a ≠ b) (ha : a ∈ b ⋆ c) : a ⋆ b = b ⋆ c :=
begin
  apply le_antisymm,
  { convert mem_line_le_line₂ ha using 1, exact line_symm a b },
  { convert mem_line_le_line₁ (line_exchange hab ha) using 1, exact line_symm b c },
end

/- If two distinct points are contianed in a line, the line the points determine is equal to the
  line they are contained in. -/
lemma P8 {a b c d : ℙ K V} (hab : a ≠ b) (ha : a ∈ c ⋆ d) (hb : b ∈ c ⋆ d) :
  a ⋆ b = c ⋆ d :=
begin
  by_cases hbc : b = c,
  { simp_rw hbc at *, exact P7 hab ha },
  { rw [← P7 hbc hb, P7 hab ha] at * },
end

lemma P9 {a b c d p : ℙ K V} (habp : a ∈ b ⋆ p) (hpcd : p ∈ c ⋆ d) :
  ∃ (q : ℙ K V), q ∈ b ⋆ d ∧ a ∈ c ⋆ q :=
begin
  by_cases hcbd : c ∈ b ⋆ d,
  { exact ⟨a, ⟨(mem_line_le_line₂ ((mem_line_le_line₁ hcbd) hpcd)) habp, P2_ref a c⟩⟩ },
  { by_cases hac: a = c,
    { refine ⟨b, ⟨ P2 b d, _ ⟩⟩, rw hac, exact P2 c b },
    { cases (P3 hac habp hpcd) with q hq,
      refine ⟨q, ⟨hq.2, _ ⟩⟩,
      simp_rw [line_symm a c, line_symm c q] at hq ⊢,
      refine line_exchange _ hq.1,
      rintro ⟨rfl⟩, exact hcbd hq.2 } },
end

/- Three points of a projective space, at least two of which are not equal, are dependent iff
  the third point is a member of the line determined by the two nonequal points. -/
lemma dependent_iff_mem_line {u v w : ℙ K V} (huv : u ≠ v) : dependent ![u, v, w] ↔ w ∈ u ⋆ v :=
begin
  rw [mem_subspace_iff, ← equiv_line_eq_span_reps, mem_span_pair],
  split; intro h,
  { rcases (dependent_triple_and_neq_pair huv h) with ⟨a, b, ⟨_, hs⟩⟩, exact ⟨a, b, hs⟩ },
  { rw [dependent_iff_reps_dependent₃],
    rcases h with ⟨a, b, hs⟩,
    refine ⟨a, b, -1, ⟨by { simp }, _⟩⟩,
    apply_fun (λ (x : V), x + (-1 : K) • w.rep) at hs,
    simp_rw [neg_smul, one_smul, ne.def, add_right_neg] at *,
    exact hs.symm }
end

/- Three points of a projective space, at least two of which are not equal, are independent iff
  the third point is not a member of the line determined by the two nonequal points. -/
lemma independent_iff_not_mem_line {u v w : ℙ K V} (huv : u ≠ v) :
  independent ![u, v, w] ↔ w ∉ u ⋆ v :=
  by {rw [independent_iff_not_dependent, not_congr], exact dependent_iff_mem_line huv }


/- The dependence relation on a triple of points in projective space satisfies the
  axioms of a projective geometry. -/

/- A point is dependent with any other point. -/
lemma L1 (a b : ℙ K V) : dependent ![a, b, a] :=
  by { rw dependent_iff_reps_dependent₃, use [1, 0, -1], simp }

/- If two points are both dependent with a pair of distinct points, then the two points together are
  dependent with either point from that pair. -/
lemma L2 {a b p q : ℙ K V} (hpq : p ≠ q) (hapq : dependent ![a, p, q])
  (hbpq : dependent ![b, p, q]) : dependent ![a, b, p] :=
begin
  rw ← dependent_cycle₃ at hapq hbpq,
  by_cases hab : a = b,
  { rw [hab, ← dependent_cycle₃], exact L1 b p },
  { rw dependent_iff_mem_line hpq at hbpq hapq, rw dependent_iff_mem_line hab,
    convert P2 p q using 1,
    exact P8 hab hapq hbpq },
end

lemma L2' {a b p q : ℙ K V} (hpq : p ≠ q) (hapq : dependent ![a, p, q])
  (hbpq : dependent ![b, p, q]) : dependent ![a, b, q] :=
  by { rw [dependent_12_trans, ← dependent_cycle₃] at hapq hbpq, exact L2 (hpq.symm) hapq hbpq }


/- -/
lemma L3 {a b c d p : ℙ K V} (hpab : dependent ![p, a, b]) (hpcd : dependent ![p, c, d]) :
  ∃ (q : ℙ K V), dependent ![q, a, c] ∧ dependent ![q, b, d] :=
begin
  by_cases hbp : b = p,
  { simp_rw hbp at *, exact ⟨c, ⟨L1 c a, dependent_12_trans.1 hpcd⟩⟩ },
  { by_cases hcd : c = d,
    { simp_rw ← hcd at *, exact ⟨c, ⟨L1 c a, L1 c b⟩⟩ },
    { by_cases hac: a = c,
      { simp_rw hac at *, refine ⟨d, ⟨_, L1 d b⟩⟩, rw dependent_cycle₃, exact L1 c d },
      { by_cases hbd : b = d,
        { simp_rw hbd at *, refine ⟨c, ⟨L1 c a, _⟩⟩, rw dependent_cycle₃, exact L1 d c },
        { rw [dependent_cycle₃, dependent_iff_mem_line hbp] at hpab,
          rw [← dependent_cycle₃, dependent_iff_mem_line hcd] at hpcd,
          simp_rw [← dependent_cycle₃, dependent_iff_mem_line hac, dependent_iff_mem_line hbd],
          exact P3 hac hpab hpcd } } } },
end


variables {W L : Type*} [add_comm_group W] [field L] [module L W]
variables  {σ : K →+* L} {T : V →ₛₗ[σ] W} {hT : function.injective T}

variables (K V L W)

/- A morphism of projective geometries is a map such that the image of the line through two points
  is contained in the line through the image of the two points. -/
@[ext] structure projective_morphism :=
(of_fun : ℙ K V → ℙ L W)
(line_into {u v w: ℙ K V} (hw : w ∈ u ⋆ v) : of_fun w ∈ (of_fun u) ⋆ (of_fun v))

variables {K V L W}

/- A morhpism of projective geometries has a coercion to a function between them. -/
instance : has_coe_to_fun (projective_morphism K V W L) (λ x, ℙ K V → ℙ L W) :=
  { coe := λ x, x.of_fun }

/- A morhpism of projective geometries preserves the independence of points. -/
lemma morphism_preserves_dependence {u v w : ℙ K V} (φ : projective_morphism K V W L)
  (h : dependent ![u, v, w]) : dependent ![φ u, φ v, φ w] :=
begin
  by_cases huv : u = v,
  { rw [huv, ← dependent_cycle₃], exact L1 _ _ },
  { by_cases hm : φ u = φ v,
    { rw [hm, ← dependent_cycle₃], exact L1 _ _,},
    { rw dependent_iff_mem_line hm, rw dependent_iff_mem_line huv at h, exact φ.line_into h } },
end

/- For a semilinear map which is injective, the image under the
  induced map of the span of a set of points is contained in the span of the image of the set. -/
lemma of_sl_span_le_span_sl (S : set (ℙ K V)) : (map T hT) '' (span S) ≤ span (map T hT '' S) :=
begin
  rintro x ⟨v, ⟨hv, rfl⟩⟩,
  induction hv with w hw u v _ _ _ _ _ hu hw,
  { apply subset_span, exact ⟨w, ⟨hw, rfl⟩⟩ },
  { rw sl_map_mk_eq_mk at hu hw ⊢,
    simp only [map_add, set_like.mem_coe],
    exact mem_add (span (map T hT '' S)) (T u) (T v) (_) (_) (_) hu hw }
end

/- A map on projective spaces induced by an injective semilinear map sends the line through two
  points into the line through the images of the two points. This implies that the
  map between projective geometries induced by a semilinear map is a morphism of projective
  geometries. -/
lemma of_sl_line_le_line_sl_reps (u v : ℙ K V) : (map T hT) '' (u ⋆ v) ≤
  (map T hT u) ⋆ (map T hT v) :=
  by { unfold line, convert (of_sl_span_le_span_sl {u, v}), rw set.image_pair }

end subspace

end projectivization
