import ring_theory.adjoin.basic
import linear_algebra.linear_independent
import ring_theory.mv_polynomial.basic

noncomputable theory

open function set subalgebra mv_polynomial algebra
open_locale classical big_operators

universes u

variables {ι : Type*} {ι' : Type*} (R : Type*) {K : Type*}
variables {A : Type*} {A' A'' : Type*} {V : Type u} {V' : Type*}

section

variables (v : ι → A)
variables [comm_ring R] [comm_ring A] [comm_ring A'] [comm_ring A'']
variables [algebra R A] [algebra R A'] [algebra R A'']
variables {a b : R} {x y : A}

/-- `linear_independent R v` states the family of vectors `v` is linearly independent over `R`. -/
def algebraic_independent : Prop :=
injective (mv_polynomial.aeval v : mv_polynomial ι R →ₐ[R] A)

variables {R} {v}

theorem algebraic_independent_iff_ker_eq_bot : algebraic_independent R v ↔
  (mv_polynomial.aeval v : mv_polynomial ι R →ₐ[R] A).to_ring_hom.ker = ⊥ :=
ring_hom.injective_iff_ker_eq_bot _

theorem algebraic_independent_iff : algebraic_independent R v ↔
  ∀p : mv_polynomial ι R, mv_polynomial.aeval (v : ι → A) p = 0 → p = 0 :=
ring_hom.injective_iff _

theorem algebraic_independent_iff_injective_aeval :
  algebraic_independent R v ↔ injective (mv_polynomial.aeval v : mv_polynomial ι R →ₐ[R] A) :=
iff.rfl
#print mv_polynomial_equiv_mv_polynomial
@[simp] lemma algebraic_independent_empty_type [is_empty ι] :
  algebraic_independent R v ↔ injective (algebra_map R A) :=
begin
  split,
  {  }

end

namespace algebraic_independent

variables (hv : algebraic_independent R v)

include hv

lemma algebra_map_injective : injective (algebra_map R A) :=
by simpa [← mv_polynomial.algebra_map_eq, function.comp] using
    (injective.of_comp_iff
      (algebraic_independent_iff_injective_aeval.1 hv) (mv_polynomial.C)).2
    (mv_polynomial.C_injective _ _)

lemma linear_independent : linear_independent R v :=
begin
  rw [linear_independent_iff_injective_total],
  have : finsupp.total ι A R v =
    (mv_polynomial.aeval v).to_linear_map.comp (finsupp.total ι _ R X),
  { ext, simp },
  rw this,
  refine hv.comp _,
  rw [← linear_independent_iff_injective_total],
  exact linear_independent_X _ _
end

lemma ne_zero [nontrivial R] (i : ι) : v i ≠ 0 :=
hv.linear_independent.ne_zero i

lemma comp (f : ι' → ι) (hf : function.injective f) : algebraic_independent R (v ∘ f) :=
λ p q, by simpa [aeval_rename, (rename_injective f hf).eq_iff] using @hv (rename f p) (rename f q)

lemma coe_range : algebraic_independent R (coe : range v → A) :=
by simpa using hv.comp _ (range_splitting_injective v)

lemma map {f : A →ₐ[R] A'} (hf_inj : set.inj_on f (adjoin R (range v))) :
  algebraic_independent R (f ∘ v) :=
have aeval (f ∘ v) = f.comp (aeval v), by ext; simp,
have h : ∀ x : mv_polynomial ι R, aeval v x ∈ (@aeval R _ _ _ _ (coe : range v → A) _).range,
  { intro x,
    rw [alg_hom.mem_range],
    refine ⟨mv_polynomial.rename (cod_restrict v (range v) (mem_range_self)) x, _⟩,
    simp [function.comp, aeval_rename] },
begin
  intros x y hxy,
  rw [this] at hxy,
  rw [adjoin_eq_range] at hf_inj,
  exact hv (hf_inj (h x) (h y) hxy)
end

lemma map' {f : A →ₐ[R] A'} (hf_inj : injective f) : algebraic_independent R (f ∘ v) :=
hv.map (inj_on_of_injective hf_inj _)

omit hv

lemma of_comp (f : A →ₐ[R] A') (hfv : algebraic_independent R (f ∘ v)) :
  algebraic_independent R v :=
have aeval (f ∘ v) = f.comp (aeval v), by ext; simp,
by rw [algebraic_independent, this] at hfv; exact hfv.of_comp

end algebraic_independent

open algebraic_independent

lemma alg_hom.algebraic_independent_iff (f : A →ₐ[R] A') (hf : injective f) :
  algebraic_independent R (f ∘ v) ↔ algebraic_independent R v :=
⟨λ h, h.of_comp f, λ h, h.map (inj_on_of_injective hf _)⟩


end
