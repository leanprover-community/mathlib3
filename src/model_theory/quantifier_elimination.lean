import model_theory.satisfiability

universes u v w
open_locale first_order

namespace first_order
namespace language
open category_theory bounded_formula

variables (L : language.{u v}) {α β : Type*} {m n : ℕ}

namespace bounded_formula

variables {L}

lemma is_atomic.to_formula {φ : L.bounded_formula α n} (h : φ.is_atomic) :
  φ.to_formula.is_atomic :=
begin
  induction h,
  { exact is_atomic.equal _ _ },
  { exact is_atomic.rel _ _ }
end

lemma is_qf.to_formula {φ : L.bounded_formula α n} (h : φ.is_qf) :
  φ.to_formula.is_qf :=
begin
  induction h with _ h _ _ _ _ ih1 ih2,
  { exact is_qf.falsum },
  { exact h.to_formula.is_qf },
  { exact ih1.imp ih2 }
end

lemma is_qf.realize_embed {A B : Type*} [L.Structure A] [L.Structure B]
  {φ : L.bounded_formula α n} (h : is_qf φ) {v : α → A} {xs : fin n → A}
  {AB : A ↪[L] B} :
  φ.realize (AB ∘ v) (AB ∘ xs) ↔ φ.realize v xs :=
begin
  induction h with _ h _ _ _ _ ih1 ih2,
  { refl },
  { induction h,
    { simp only [realize_bd_equal, ← sum.comp_elim, embedding.realize_term,
        embedding_like.apply_eq_iff_eq] },
    { simp only [realize_rel, ← sum.comp_elim, embedding.realize_term, embedding.map_rel], } },
  { simp only [realize_imp, ih1, ih2] }
end

/-- Substitutes the variables in a given formula with terms. -/
def subst' {n : ℕ} (φ : L.bounded_formula α n)
  (f : α ⊕ fin n → L.term (β ⊕ fin m)) :
  L.bounded_formula β m :=
(φ.to_formula.subst f).relabel id

@[simp] lemma subst'_relation {k : ℕ} (R : L.relations n)
  (ts₁ : fin n → L.term (α ⊕ fin m))
  (ts₂ : (α ⊕ fin m) → L.term (α ⊕ fin k)) :
  (R.bounded_formula ts₁).subst' ts₂ = R.bounded_formula (λ i, (ts₁ i).subst ts₂) :=
begin
  simp only [subst', subst, relations.bounded_formula, to_formula, relations.formula, id.def,
    relabel, map_term_rel, heq_iff_eq, eq_self_iff_true, true_and],
  ext i,
  induction (ts₁ i) with a _ _ _ ih,
  { simp only [term.relabel, term.subst, sum.elim_inl, relabel_relabel],
    induction (ts₂ a) with b _ _ _ ih',
    { cases b;
      simp [relabel_aux] },
    { simp [ih'], } },
  { simp [ih] }
end

@[simp] lemma subst_on_term
  {L' : language} {Lh : L →ᴸ L'} {t : L.term α}
  {f : α → L.term β} :
  Lh.on_term (t.subst f) = (Lh.on_term t).subst (Lh.on_term ∘ f) :=
begin
  induction t with _ _ _ _ ih,
  { refl },
  { simp [ih] }
end

@[simp] lemma subst_on_bounded_formula
  {L' : language} {Lh : L →ᴸ L'} {φ : L.bounded_formula α n}
  {f : α → L.term β} :
  Lh.on_bounded_formula (φ.subst f) = (Lh.on_bounded_formula φ).subst (Lh.on_term ∘ f) :=
begin
  induction φ,
  { refl },
  { simp only [Lhom.on_bounded_formula, subst, map_term_rel, term.bd_equal, subst_on_term, sum.comp_elim],
    refine ⟨congr rfl (congr (congr rfl _) _), congr rfl (congr (congr rfl _) _)⟩,
    { ext a,
      sorry,

    },


  }
end

end bounded_formula

def morleyization : language.{u (max u v)} :=
L.sum ⟨λ n, empty, λ n, L.bounded_formula empty n⟩

variable {L}

@[simp] def term_demorley : L.morleyization.term α → L.term α
| (var i) := var i
| (func (sum.inl f) ts) := func f (λ i, term_demorley (ts i))

@[simp] def formula_demorley :
  ∀ {n}, L.morleyization.bounded_formula empty n → L.bounded_formula empty n
| n bounded_formula.falsum := ⊥
| n (bounded_formula.equal t₁ t₂) := bounded_formula.equal (term_demorley t₁) (term_demorley t₂)
| n (bounded_formula.rel (sum.inl R) ts) := bounded_formula.rel R (λ i, term_demorley (ts i))
| n (bounded_formula.rel (sum.inr R) ts) :=
    R.subst' (sum.elim empty.elim (λ i, term_demorley (ts i)))
| n (bounded_formula.imp φ₁ φ₂) := (formula_demorley φ₁).imp (formula_demorley φ₂)
| n (bounded_formula.all φ) := (formula_demorley φ).all

@[simp] lemma on_term_demorley (t : L.morleyization.term α) :
  Lhom.sum_inl.on_term (term_demorley t) = t :=
begin
  induction t with t n f ts ih,
  { refl },
  { cases f,
    { simp [ih] },
    { exact f.elim } }
end

@[simp] lemma on_term_comp_demorley (ts : β → L.morleyization.term α) :
  Lhom.sum_inl.on_term ∘ (λ i, term_demorley (ts i)) = ts :=
begin
  ext i,
  simp,
end

namespace Theory
namespace semantically_equivalent
variables {L} {T T' : L.Theory}

lemma mono
  {φ ψ : L.bounded_formula α n}
  (h : T.semantically_equivalent φ ψ) (TT' : T ⊆ T') :
  T'.semantically_equivalent φ ψ :=
begin
  intros M v xs,
  rw [ bounded_formula.realize_iff, h.realize_bd_iff],
  { apply_instance, },
  { exact Theory.model.mono infer_instance TT' }
end

lemma to_formula
  {φ ψ : L.bounded_formula α n}
  (h : T.semantically_equivalent φ ψ) :
  T.semantically_equivalent φ.to_formula ψ.to_formula :=
begin
  intros M v xs,
  simp only [bounded_formula.realize_iff, unique.eq_default xs],
  rw [← formula.realize, bounded_formula.realize_to_formula,
    ← formula.realize, bounded_formula.realize_to_formula],
  exact h.realize_bd_iff,
end

lemma relabel
  {φ ψ : L.bounded_formula α n}
  (h : T.semantically_equivalent φ ψ)
  (f : α → β ⊕ fin m) :
  T.semantically_equivalent (φ.relabel f) (ψ.relabel f) :=
begin
  intros M v xs,
  simp only [bounded_formula.realize_iff, bounded_formula.realize_relabel],
  exact h.realize_bd_iff,
end

lemma subst
  {φ ψ : L.bounded_formula α n}
  (h : T.semantically_equivalent φ ψ)
  (f : α → L.term β) :
  T.semantically_equivalent (φ.subst f) (ψ.subst f) :=
begin
  intros M v xs,
  simp only [bounded_formula.realize_iff, bounded_formula.realize_subst],
  exact h.realize_bd_iff,
end

lemma subst'
  {φ ψ : L.bounded_formula α n} (h : T.semantically_equivalent φ ψ)
  (f : α ⊕ fin n → L.term (β ⊕ fin m)) :
  T.semantically_equivalent (φ.subst' f) (ψ.subst' f) :=
(h.to_formula.subst f).relabel id

lemma iff_model_alls_iff {φ ψ : L.bounded_formula empty n} :
  T.semantically_equivalent φ ψ ↔ T ⊨ (φ ⇔ ψ).alls :=
begin
  simp only [models_sentence_iff, sentence.realize, realize_alls, bounded_formula.realize_iff],
  simp only [semantically_equivalent, models_bounded_formula, bounded_formula.realize_iff],
  exact forall_congr (λ M, unique.forall_iff),
end

end semantically_equivalent

variables {L} (T : L.Theory)
include T

def morleyization : L.morleyization.Theory :=
Lhom.sum_inl.on_Theory T ∪ (⋃ (n : ℕ), set.range (λ φ : L.bounded_formula empty n,
  (Lhom.sum_inl.on_bounded_formula φ ⇔
  (Lhom.sum_inr.on_relation φ : L.morleyization.relations n).bounded_formula (λ i, &i)).alls))

def has_qe : Prop :=
∀ {n : ℕ} (φ : L.bounded_formula empty n), ∃ (ψ : L.bounded_formula empty n),
  ψ.is_qf ∧ T.semantically_equivalent φ ψ

@[simp] lemma realize_term_demorley {α : Type*} (t : L.morleyization.term α)
  {M : T.morleyization.Model} {xs : α → M} :
  realize xs (term_demorley t) = realize xs t :=
begin
  induction t with _ _ f _ ih,
  { refl, },
  { cases f,
    { simp [ih], },
    { exact f.elim } }
end

lemma equiv_morley (φ : L.bounded_formula empty n) :
  T.morleyization.semantically_equivalent
    (Lhom.sum_inl.on_bounded_formula φ) (relations.bounded_formula (sum.inr φ) (λ i, &i)) :=
begin
  rw semantically_equivalent.iff_model_alls_iff,
  exact Theory.models_sentence_of_mem (set.mem_union_right _
        (set.mem_Union.2 ⟨_, (set.mem_range.2 ⟨_, rfl⟩)⟩)),
end

lemma equiv_demorley (φ : L.morleyization.bounded_formula empty n) :
  T.morleyization.semantically_equivalent φ
  (Lhom.sum_inl.on_bounded_formula (formula_demorley φ)) :=
begin
  induction φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih,
  { refl },
  { simp only [Lhom.on_bounded_formula, formula_demorley, on_term_demorley],
    refl },
  { cases φ_R,
    { simp only [Lhom.on_bounded_formula, formula_demorley, Lhom.sum_inl_on_relation,
        on_term_comp_demorley],
      refl },
    { rw formula_demorley,
      have h := (T.equiv_morley φ_R).symm.subst' (φ_ts ∘ (sum.elim empty.elim id)),
      simp_rw [bounded_formula.subst'_relation, relations.bounded_formula, term.subst,
        function.comp_apply, sum.elim_inr] at h,
      refine h.trans _,
      simp only [sum.comp_elim, function.comp.right_id, subsingleton.elim (φ_ts ∘ _) empty.elim],



      --simp only [bounded_formula.subst', function.comp_app] at h,
      intros M v xs,
      rw [bounded_formula.realize_iff, Lhom.realize_on_bounded_formula],
      have h' := @Theory.realize_sentence_of_mem _ M _ T.morleyization _ _ (set.mem_union_right _
        (set.mem_Union.2 ⟨_, (set.mem_range.2 ⟨φ_R, rfl⟩)⟩)),
      rw [sentence.realize, bounded_formula.realize_alls] at h',
      have h'' := h' (λ i, (φ_ts i).realize (sum.elim v xs)),
      simp only [bounded_formula.realize_iff, term.realize, Lhom.sum_inr_on_relation,
        Lhom.realize_on_bounded_formula, bounded_formula.realize_rel, sum.elim_inr] at h'',
      rw [← relations.bounded_formula, bounded_formula.realize_rel, ← h''],
      simp only [relations.bounded_formula],
      rw [bounded_formula.realize_relabel, bounded_formula.realize_subst,
        unique.eq_default (xs ∘ (fin.nat_add φ_n : fin 0 → fin φ_n)), ← formula.realize,
        bounded_formula.realize_to_formula, iff_eq_eq],
      refine congr (congr rfl (unique.eq_default _).symm) _,
      ext i,
      simp } },
  { exact ih1.imp ih2 },
  { exact ih.all }
end

theorem morleyization.has_qe : T.morleyization.has_qe :=
λ n φ, begin
  refine ⟨(Lhom.sum_inr.on_relation (formula_demorley φ) :
    L.morleyization.relations n).bounded_formula (λ i, &i),
    (bounded_formula.is_atomic.rel _ _).is_qf,
    (equiv_demorley T φ).trans _⟩,
  intros M v xs,
  have h := @Theory.realize_sentence_of_mem _ M _ T.morleyization _ _ (set.mem_union_right _
        (set.mem_Union.2 ⟨_, (set.mem_range.2 ⟨formula_demorley φ, rfl⟩)⟩)),
  -- connect semantically equivalent to alls?
  rw [sentence.realize, bounded_formula.realize_alls, ← unique.eq_default v] at h,
  exact h xs,
end

theorem has_qe_iff :
  T.has_qe ↔ ∀ {n} (φ : L.bounded_formula empty (n + 1)) (h : φ.is_qf),
    ∃ (ψ : L.bounded_formula empty n), ψ.is_qf ∧ T.semantically_equivalent φ.ex ψ :=
begin
  refine ⟨λ h _ φ _, h φ.ex, λ h _ φ, φ.induction_on_exists_not (λ m ψ hψ, ⟨ψ, hψ, refl _⟩) _ _ _⟩,
  { rintros m φ ⟨ψ, hψ, φψ⟩,
    exact ⟨ψ.not, hψ.not, φψ.not⟩ },
  { rintros m φ ⟨ψ, hψ, φψ⟩,
    obtain ⟨θ, hθ, ψθ⟩ := h ψ hψ,
    exact ⟨θ, hθ, φψ.ex.trans ψθ⟩ },
  { rintros m φ ψ φψ,
    split,
    { rintro ⟨θ, hθ, φθ⟩,
      exact ⟨θ, hθ, (φψ.mono T.empty_subset).symm.trans φθ⟩ },
    { rintro ⟨θ, hθ, ψθ⟩,
      exact ⟨θ, hθ, (φψ.mono T.empty_subset).trans ψθ⟩ } }
end


theorem has_qe.exists_qf_equiv (h : T.has_qe) (φ : L.bounded_formula α n) :
  ∃ (ψ : L.bounded_formula α n), ψ.is_qf ∧ T.semantically_equivalent φ ψ :=
begin
  classical,
  obtain ⟨ψ, hψ, φψ⟩ := h ((φ.restrict_free_var id).relabel (sum.inr ∘ (fintype.equiv_fin _))),
  refine ⟨bounded_formula.relabel
    ((sum.map (coe ∘ (fintype.equiv_fin _).symm) id) ∘ (sum.elim empty.elim fin_sum_fin_equiv.symm))
    ψ.to_formula, hψ.to_formula.relabel _, λ M v xs, _⟩,
  have φψ' := φψ M default (sum.elim v xs ∘ ((sum.map (coe ∘ (fintype.equiv_fin _).symm) id) ∘
    fin_sum_fin_equiv.symm)),
  simp only [bounded_formula.realize_iff, bounded_formula.realize_relabel, iff_eq_eq] at *,
  rw [← realize_restrict_free_var (set.subset.refl _), set.inclusion_eq_id],
  rw [unique.eq_default (xs ∘ (fin.nat_add n : fin 0 → fin n)),
      ← formula.realize, realize_to_formula],
  refine (congr (congr rfl _) _).trans
    (φψ'.trans (congr (congr rfl (unique.eq_default _).symm) _)),
  { ext i,
      simp only [free_var_finset, function.comp_app, sum.elim_inr,
        fin_sum_fin_equiv_symm_apply_cast_add, sum.map_inl,
        _root_.equiv.symm_apply_apply, sum.elim_inl, eq_self_iff_true], },
  { ext i,
    simp only [function.comp_app, fin_sum_fin_equiv_symm_apply_nat_add, sum.map_inr,
      id.def, sum.elim_inr], },
  { ext i,
    simp only [function.comp_app, fin.cast_add_zero, fin.cast_refl, order_iso.coe_refl,
      function.comp.right_id, sum.elim_inr], }
end

variables {T}

theorem has_qe_iff' :
  T.has_qe ↔ ∀ (M : Theory.Model.{u v (max u v)} T) (a : finset M),
    T ∪ {φ ∈ L.elementary_diagram a} :=
begin
  refine ⟨λ h A M N AM AN n a φ, _, λ h n φ, _⟩,
  { obtain ⟨ψ, hψ, φψ⟩ := h φ,
    rw [φψ.realize_bd_iff, ← unique.eq_default (AM ∘ default), hψ.realize_embed,
      φψ.realize_bd_iff, ← unique.eq_default (AN ∘ default), hψ.realize_embed];
    apply_instance },
  { 
    

  }
end

theorem has_qe_iff'' :
  T.has_qe ↔ ∀ (A : bundled L.Structure) (M N : Theory.Model.{u v (max u v)} T) (AM : A ↪[L] M) (AN : A ↪[L] N)
    {n : ℕ} (a : fin n → A) (φ : L.bounded_formula empty n),
  φ.realize default (AM ∘ a) ↔ φ.realize default (AN ∘ a) :=
begin
  refine ⟨λ h A M N AM AN n a φ, _, λ h n φ, _⟩,
  { obtain ⟨ψ, hψ, φψ⟩ := h φ,
    rw [φψ.realize_bd_iff, ← unique.eq_default (AM ∘ default), hψ.realize_embed,
      φψ.realize_bd_iff, ← unique.eq_default (AN ∘ default), hψ.realize_embed];
    apply_instance },
  { 


  }
end



end Theory
end language
end first_order
