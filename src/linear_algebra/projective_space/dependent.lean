import linear_algebra.projective_space.basic
import tactic
variables {K V : Type*} [field K] [add_comm_group V] [module K V]

namespace projectivization

/- Composition of a function and a finite indexing of size two or three commute -/
lemma fin_comp_commutes₂ {α β : Type*} {a b : α} {f: α → β} : (f ∘ (![a, b])) = (![f a, f b]) :=
by { ext, fin_cases x; refl }

lemma fin_comp_commutes₃ {α β : Type*} {a b c : α} {f: α → β} :
  (f ∘ (![a, b, c])) = (![f a, f b, f c]) :=
by { ext, fin_cases x; refl }

/- A finite indexing of size two or three is nonzero iff all but one element being
mapped to 0 implies the other element is not mapped to zero. -/

lemma fin_nonzero_iff₂ {a b : K} : ![a, b] ≠ 0 ↔ (a = 0 → b ≠ 0) :=
by { simp }

lemma fin_nonzero_iff₃ {a b c : K} : ![a, b, c] ≠ 0 ↔ (a = 0 → b = 0 → c ≠ 0) :=
by { simp }

/- The order of the values taken by a nonzero indexing of size three does not alter the fact that
  it is nonzero. -/
lemma index_cylce₃ {a b c : K} : ![a, b, c] ≠ 0 ↔ ![c, a, b] ≠ 0 :=
begin
  simp_rw fin_nonzero_iff₃,
  split; intro h,
  { intros hc ha hb, specialize h ha hb, exact h hc },
  { intros ha hb hc, exact h hc ha hb },
end

lemma index_12_trans₃ {a b c : K} : ![a, b, c] ≠ 0 ↔ ![b, a, c] ≠ 0 :=
begin
  simp_rw fin_nonzero_iff₃,
  split; intro h,
  { intros hb ha hc, exact h ha hb hc },
  { intros ha hb hc, exact h hb ha hc },
end

/- If an indexing of size 3 is nonzero and the first term is zero, then
  the indexing obtained from the last two elements is nonzero. -/
@[simp] lemma nontrivial_and_zero₁ {a b c : K} (ht : ![a, b, c] ≠ 0)
  (ha : a = 0) : ![b, c] ≠ 0 :=
  by { simp_rw [fin_nonzero_iff₂, fin_nonzero_iff₃] at *, exact ht ha }

/- If an indexing of size 3 is nonzero and the second term is zero, then
  the indexing obtained from the first and last elements is nonzero. -/
@[simp] lemma nontrivial_and_zero₂ {a b c : K} (ht : ![a, b, c] ≠ 0)
  (hb : b = 0) : ![a, c] ≠ 0 :=
  by { simp_rw [fin_nonzero_iff₂, fin_nonzero_iff₃] at *, intro ha, exact ht ha hb  }

/- If an indexing of size 3 is nonzero and the third term is zero, then
  the indexing obtained from the first and second elements is nonzero. -/
@[simp] lemma nontrivial_and_zero₃ {a b c : K} (ht : ![a, b, c] ≠ 0)
  (hc : c = 0) : ![a, b] ≠ 0 :=
  by { simp_rw [fin_nonzero_iff₂, fin_nonzero_iff₃] at *, intros ha hb, exact ht ha hb hc }

variable (K)

/-Two nonzero vectors go to the same point in projective space iff one is in
the span of the other. -/
lemma mk_eq_mk_iff' (v w: V) (hv : v ≠ 0) (hw : w ≠ 0) : mk K v hv = mk K w hw ↔
  ∃ a : K, a • w = v :=
begin
  rw mk_eq_mk_iff K v w hv hw,
  split,
  { rintro ⟨a, ha⟩, exact ⟨a, ha⟩ },
  { rintro ⟨a, ha⟩, refine ⟨units.mk0 a (λ c, hv.symm _), ha⟩, rwa [c, zero_smul] at ha }
end

/- A nonzero vector is a scalar multiple of the representative of its equivalence class in
projective space. -/
lemma exists_smul_mk_rep_eq (v : V) (hv : v ≠ 0) : ∃ (a : Kˣ), v = a • ((mk K v hv).rep) :=
begin
  cases (exists_smul_eq_mk_rep K v hv) with a ha,
  refine ⟨a⁻¹, _⟩,
  apply_fun (λ x, (a)⁻¹ • x) at ha,
  rwa [inv_smul_smul] at ha,
end

variable {K}

/- A linearly independent familty of nonzero vectors gives an independent family of points
in the projective space. -/
inductive independent {ι : Type*} : (ι → ℙ K V) → Prop
| mk (f : ι → V) (hf : ∀ i : ι, f i ≠ 0) (hl : linear_independent K f) :
    independent (λ i, mk K (f i) (hf i))

/- A family of points in a projective space are independent iff their
representatives are linearly independent. -/
lemma independent_iff (ι : Type*) (f : ι → (ℙ K V)) : independent f ↔
  linear_independent K (projectivization.rep ∘ f) :=
begin
  split,
  { rintro h, induction h with ff hff hh,
    choose a ha using λ (i : ι), exists_smul_eq_mk_rep K (ff i) (hff i),
    convert hh.units_smul a,
    ext i, exact (ha i).symm },
  { intro h,
    convert independent.mk _ _ h,
    { ext, simp only [mk_rep] },
    { intro i, apply rep_nonzero } }
end

/- A linearly dependent family of nonzero vectors gives a dependent family of points
in the projective space. -/
inductive dependent {ι : Type*} : (ι → ℙ K V) → Prop
| mk (f : ι → V) (hf : ∀ i : ι, f i ≠ 0) (h : ¬linear_independent K f) :
    dependent (λ i, mk K (f i) (hf i))

/- A family of points in a projective space is dependent iff their
representatives are linearly dependent. -/
lemma dependent_iff (ι : Type*) (f : ι → (ℙ K V)) : dependent f ↔
  ¬ linear_independent K (projectivization.rep ∘ f) :=
begin
  split,
  { rw ← independent_iff,
    intros h1, induction h1 with ff hff hh1,
    contrapose! hh1, rw independent_iff at hh1,
    choose a ha using λ (i : ι), exists_smul_eq_mk_rep K (ff i) (hff i),
    convert hh1.units_smul a⁻¹,
    ext i, simp only [← ha, inv_smul_smul, pi.smul_apply', pi.inv_apply, function.comp_app] },
  { intro h,
    convert dependent.mk _ _ h,
    { ext, simp only [mk_rep] },
    { intro i, apply rep_nonzero } }
end

/- Dependence is the negation of independence. -/
lemma dependent_iff_not_independent {ι : Type*} (f : ι → ℙ K V) :
  dependent f ↔ ¬ independent f :=
by { rw [dependent_iff, independent_iff] }

/- Independence is the negation of dependence. -/
lemma independent_iff_not_dependent {ι : Type*} (f : ι → ℙ K V) :
  independent f ↔ ¬ dependent f :=
by { rw [dependent_iff, independent_iff, not_not] }


/- Two points in a projective space are dependent iff they are equal. -/
@[simp] lemma pair_dependent_iff_eq (u v : ℙ K V) : dependent ![u, v] ↔ u = v :=
begin
  simp_rw [dependent_iff_not_independent, independent_iff, linear_independent_fin2,
    function.comp_app, matrix.cons_val_one, matrix.head_cons,
    ne.def, matrix.cons_val_zero, not_and, not_forall, not_not,
    ← mk_eq_mk_iff' K _ _ (rep_nonzero u) (rep_nonzero v), mk_rep,
    imp_iff_right_iff],
  exact or.inl (rep_nonzero v),
end

/- Two points in a projective space are independent iff the points are not equal. -/
@[simp] lemma pair_independent_iff_neq (u v : ℙ K V) : (independent ![u, v]) ↔ u ≠ v :=
by { rw [independent_iff_not_dependent, pair_dependent_iff_eq u v] }

open_locale big_operators
/- Two vectors are linearly dependent iff 0 is a nontrivial linear combination of them. -/
lemma linear_dependent_iff₂ (u v : V) : ¬ linear_independent K ![u, v] ↔
  (∃ (a b : K) (hnt : ![a, b] ≠ 0), a • u + b • v = 0) :=
begin
  rw fintype.linear_independent_iff,
  simp only [not_forall, exists_prop, fin.sum_univ_succ, function.comp_app, matrix.cons_val_zero,
  matrix.cons_val_succ, fin.succ_zero_eq_one, fintype.univ_of_subsingleton, fin.mk_eq_subtype_mk,
  fin.mk_zero, finset.sum_singleton, function.ne_iff],
  split,
  { rintros ⟨g, h, ⟨i, hi⟩⟩,
    exact ⟨g 0, g 1, ⟨⟨i, by { fin_cases i; exact hi}⟩, h⟩⟩ },
  { rintros ⟨a, b, ⟨h, hs⟩⟩,
    exact ⟨![a, b], ⟨hs, h⟩⟩ }
end

/- Three vectors are linearly dependent iff 0 is a nontrivial linear combination of them. -/
lemma linear_dependent_iff₃ (u v w : V) : ¬ linear_independent K ![u, v, w] ↔
  (∃ (a b c: K) (hnt : ![a, b, c] ≠ 0), a • u + b • v + c • w = 0) :=
begin
  rw fintype.linear_independent_iff,
  simp only [not_forall, exists_prop, fin.sum_univ_succ, function.comp_app, matrix.cons_val_zero,
  matrix.cons_val_succ, fin.succ_zero_eq_one, fintype.univ_of_subsingleton, fin.mk_eq_subtype_mk,
  fin.mk_zero, finset.sum_singleton, add_assoc, function.ne_iff],
  split,
  { rintros ⟨g, h, ⟨i, hi⟩⟩,
    exact ⟨g 0, g 1, g 2, ⟨⟨i, by {fin_cases i; exact hi}⟩, h⟩⟩ },
  { rintros ⟨a, b, c, ⟨h, hs⟩⟩,
    exact ⟨![a, b, c], ⟨hs, h⟩⟩ }
end

/- Two points are dependent iff 0 is a nontrivial linear combination of their representatives. -/
lemma dependent_iff_reps_dependent₂ (u v : ℙ K V) : dependent ![u, v] ↔
  ∃ (a b : K) (hnt : ![a, b] ≠ 0), a • u.rep + b • v.rep = 0 :=
  by { rw [dependent_iff, fin_comp_commutes₂], exact linear_dependent_iff₂ u.rep v.rep }


/- Three points are dependent iff 0 is a nontrivial linear combination of their representatives. -/
lemma dependent_iff_reps_dependent₃ (u v w : ℙ K V) : dependent ![u, v, w] ↔
  ∃ (a b c : K) (hnt : ![a, b, c] ≠ 0), a • u.rep + b • v.rep + c • w.rep = 0 :=
  by { rw [dependent_iff, fin_comp_commutes₃], exact linear_dependent_iff₃ u.rep v.rep w.rep }


/- An indexed family of nonzero vectors is linearly independent iff
  the family of representatives of the points they determine in projective space
  is linearly independent. -/
lemma linear_independent_iff_mk_rep {ι : Type*} (f : ι → V) (hf : ∀ i : ι, f i ≠ 0) :
  linear_independent K f ↔ linear_independent K (λ i, (mk K (f i) (hf i)).rep) :=
begin
  choose a ha using λ (i : ι), exists_smul_eq_mk_rep K (f i) (hf i),
  split; intro hf,
  { convert linear_independent.units_smul hf a,
    ext,
    rwa [pi.smul_apply', ha x] },
  { convert linear_independent.units_smul hf (λ i, (a i)⁻¹),
    ext,
    specialize ha x,
    apply_fun (λ (v : V), (a x)⁻¹ • v) at ha,
    rwa [inv_smul_smul] at ha },
end

/- The points two nonzero vectors represent in projective space are dependent iff
  zero is a nontrivial linear combination of the vectors. -/
lemma mk_dependent_iff_dependent₂ (u v : V) (hu : u ≠ 0) (hv : v ≠ 0) :
  dependent ![mk K u hu, mk K v hv] ↔ ∃ (a b: K) (hnt : ![a, b] ≠ 0), a • u + b • v = 0 :=
begin
  rw [← linear_dependent_iff₂, dependent_iff, not_iff_not, iff.comm],
  convert linear_independent_iff_mk_rep ![u, v] (by { intro i, fin_cases i; assumption }),
  ext, fin_cases x; simp
end

/- The points three nonzero vectors represent in projective space are dependent iff
  zero is a nontrivial linear combination of the vectors. -/
lemma mk_dependent_iff_dependent₃ (u v w : V) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) :
  dependent ![mk K u hu, mk K v hv, mk K w hw] ↔
  ∃ (a b c : K) (hnt : ![a, b, c] ≠ 0), a • u + b • v + c • w = 0 :=
begin
  rw [← linear_dependent_iff₃, dependent_iff, not_iff_not, iff.comm],
  convert linear_independent_iff_mk_rep ![u, v, w] (by { intro i, fin_cases i; assumption }),
  ext, fin_cases x; simp
end

/- The order of two points does not change whether or not they are independent. -/
lemma dependent_cycle₂ {u v : ℙ K V} : dependent ![u, v] ↔ dependent ![v, u] :=
  by { simp_rw pair_dependent_iff_eq, exact comm}

/- Three points are dependent in projective space iff they are dependent when their order
  is cycled. -/
lemma dependent_cycle₃ {u v w : ℙ K V} : dependent ![u, v, w] ↔ dependent ![w, u , v] :=
begin
  simp_rw dependent_iff_reps_dependent₃, split,
  { rintros ⟨a, b, c, ⟨hnt, hs⟩⟩,
    refine ⟨c, a, b, ⟨by { rwa index_cylce₃ at hnt }, by { abel at hs ⊢, exact hs }⟩⟩ },
  { rintros ⟨a, b, c, ⟨hnt, hs⟩⟩,
    refine ⟨b, c, a, ⟨by { rwa ← index_cylce₃ at hnt }, by { abel at hs ⊢, exact hs }⟩⟩ },
end

/- Three points are dependent in projective space iff they are dependent when the first two
  points are transposed. -/
lemma dependent_12_trans {u v w : ℙ K V} : dependent ![u, v, w] ↔ dependent ![v, u, w] :=
begin
  simp_rw dependent_iff_reps_dependent₃, split,
  { rintros ⟨a, b, c, ⟨hnt, hs⟩⟩,
    refine ⟨b, a, c, ⟨by { rwa index_12_trans₃ at hnt } , by { abel at hs ⊢, exact hs }⟩⟩ },
  { rintros ⟨a, b, c, ⟨hnt, hs⟩⟩,
    refine ⟨b, a, c, ⟨by { rwa index_12_trans₃ at hnt } , by { abel at hs ⊢, exact hs }⟩⟩ },
end

/-If three points in a projective geometry are such that zero is a linear combination of their
representatives, and the scalar associated to one of the representative of the is zero,
then the other two points are dependent. -/

lemma dependent_and_zero_gives_dependent_pair₁ {u v w : ℙ K V} {a b c : K} (hnz : ![a, b, c] ≠ 0)
  (ha : a = 0) (hsz : a • u.rep + b • v.rep + c • w.rep = 0) : dependent ![v, w] :=
begin
  simp_rw [ha, zero_smul, zero_add, dependent_iff_reps_dependent₂] at ⊢ hsz,
  exact ⟨b, c, ⟨nontrivial_and_zero₁ hnz ha, hsz⟩⟩,
end

lemma dependent_and_zero_gives_dependent_pair₂ {u v w : ℙ K V} {a b c : K} (hnz : ![a, b, c] ≠ 0)
  (hb : b = 0) (hsz : a • u.rep + b • v.rep + c • w.rep = 0) : dependent ![u, w] :=
begin
  simp_rw [hb, zero_smul, add_zero, dependent_iff_reps_dependent₂] at ⊢ hsz,
  exact ⟨a, c, ⟨nontrivial_and_zero₂ hnz hb, hsz⟩⟩,
end

lemma dependent_and_zero_gives_dependent_pair₃ {u v w : ℙ K V} {a b c : K} (hnz : ![a, b, c] ≠ 0)
  (hc : c = 0) (hsz : a • u.rep + b • v.rep + c • w.rep = 0) : dependent ![u, v] :=
begin
  simp_rw [hc, zero_smul, add_zero, dependent_iff_reps_dependent₂] at ⊢ hsz,
  exact ⟨a, b, ⟨nontrivial_and_zero₃ hnz hc, hsz⟩⟩,
end

/-If three points in a projective geometry are such that 0 is a nontrivial linear combination of
their representatives, and two of the points are distinct, the scalar corresponding to
the remaining point is not zero. -/
lemma neq_scalar_neq_zero₁ {u v w : ℙ K V} {a b c : K} (hneq : v ≠ w)
  (hnt : ![a, b, c] ≠ 0) (hsz : a • u.rep + b • v.rep + c • w.rep = 0) : a ≠ 0 :=
begin
  intro h,
  rw fin_nonzero_iff₃ at hnt,
  refine hneq _,
  rw [← pair_dependent_iff_eq, dependent_iff_reps_dependent₂],
  exact ⟨b, c, by { rw fin_nonzero_iff₂, exact hnt h}, by { rwa [h, zero_smul, zero_add] at hsz }⟩,
end

/-If three points of a projective space are dependent, and two of them are not equal, the
representative of the remaining point is in the span of the other two representatives. -/
lemma dependent_triple_and_neq_pair {u v w : ℙ K V} (huv : u ≠ v)
  (huvw : dependent ![u, v, w]) : ∃ (a b : K) (hxy : ![a, b] ≠ 0), w.rep = a • u.rep + b • v.rep :=
begin
  by_cases hvw : v = w,
  { exact ⟨0, 1, by { simp }, by { rw [zero_smul, zero_add, one_smul, hvw] }⟩ },
  { rw dependent_iff_reps_dependent₃ at huvw,
    rcases huvw with ⟨a, b, c, ⟨hnt, hsz⟩⟩,
    have hc : c ≠ 0, by
      { intro h, rw [← pair_independent_iff_neq, independent_iff_not_dependent] at huv,
        exact huv (dependent_and_zero_gives_dependent_pair₃ hnt h hsz) },
    refine ⟨-c⁻¹*a, -c⁻¹*b, _, _⟩,
      { intro h,
        simp only [matrix.cons_eq_zero_iff, neg_eq_zero, mul_eq_zero, inv_eq_zero,
          eq_iff_true_of_subsingleton, and_true] at h,
        cases h with ha hb,
        exact (neq_scalar_neq_zero₁ hvw hnt hsz) (or.resolve_left ha hc) },
      { apply_fun (λ x, c⁻¹ • x) at hsz,
        simp_rw [smul_zero, smul_add, add_eq_zero_iff_neg_eq, ← mul_smul, inv_mul_cancel hc,
          one_smul, neg_add, ← neg_smul, ← neg_mul] at hsz,
        exact hsz.symm } }
end

variables {W L : Type*} [add_comm_group W] [field L] [module L W]
variables  {σ : K →+* L} {T : V →ₛₗ[σ] W} {hT : function.injective T}

/- Projection to the quotient and the map induced by an injective semilinear map commute. -/
lemma sl_map_mk_eq_mk (v : V) (hv : v ≠ 0) : map T hT (mk K v hv) =
  mk _ (T v) ((map_ne_zero_iff T hT).mpr hv) := rfl


end projectivization
