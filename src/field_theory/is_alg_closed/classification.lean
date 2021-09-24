import data.W.cardinal
import ring_theory.algebraic_independent
import field_theory.is_alg_closed.basic
import field_theory.intermediate_field

open cardinal
open_locale cardinal

universes u v

section mv_polynomial

def mv_polynomial_fun (R σ : Type u) : Type u :=
R ⊕ σ ⊕ ulift.{u} bool

variables {R σ : Type u}

namespace mv_polynomial_fun

@[simp] def arity : mv_polynomial_fun R σ → Type u
| (sum.inl _)              := pempty
| (sum.inr (sum.inl _))    := pempty
| (sum.inr (sum.inr ⟨ff⟩)) := ulift bool
| (sum.inr (sum.inr ⟨tt⟩)) := ulift bool

instance arity_fintype (x : mv_polynomial_fun R σ) : fintype x.arity :=
by rcases x with x | x | ⟨_ | _⟩; dsimp; apply_instance

variables [comm_semiring R]

@[simp] noncomputable def to_mv_polynomial :
  W_type (@mv_polynomial_fun.arity R σ) → mv_polynomial σ R
| ⟨sum.inl r, _⟩              := mv_polynomial.C r
| ⟨sum.inr (sum.inl i), _⟩    := mv_polynomial.X i
| ⟨sum.inr (sum.inr ⟨ff⟩), f⟩ :=
  to_mv_polynomial (f (ulift.up tt)) * to_mv_polynomial (f (ulift.up ff))
| ⟨sum.inr (sum.inr ⟨tt⟩), f⟩ :=
  to_mv_polynomial (f (ulift.up tt)) + to_mv_polynomial (f (ulift.up ff))

lemma to_mv_polynomial_surjective : function.surjective (@to_mv_polynomial R σ _) :=
begin
  intro p,
  induction p using mv_polynomial.induction_on with x p₁ p₂ ih₁ ih₂ p i ih,
  { exact ⟨W_type.mk (sum.inl x) pempty.elim, rfl⟩ },
  { rcases ih₁ with ⟨w₁, rfl⟩,
    rcases ih₂ with ⟨w₂, rfl⟩,
    exact ⟨W_type.mk (sum.inr (sum.inr ⟨tt⟩)) (λ x, cond x.down w₁ w₂), by simp⟩ },
  { rcases ih with ⟨w, rfl⟩,
    exact ⟨W_type.mk (sum.inr (sum.inr ⟨ff⟩)) (λ x, cond x.down w (W_type.mk
      (sum.inr (sum.inl i)) pempty.elim)), by simp⟩ }
end

lemma cardinal_mv_polynomial_fun_le : #(mv_polynomial_fun R σ) ≤ max (max (#R) (#σ)) ω :=
calc #(mv_polynomial_fun R σ) = #R + #σ + #(ulift bool) :
  by delta mv_polynomial_fun; simp only [← add_def, add_assoc]
... ≤ max (max (#R + #σ) (#(ulift bool))) ω : add_le_max _ _
... ≤ max (max (max (max (#R) (#σ)) ω) (#(ulift bool))) ω :
  max_le_max (max_le_max (add_le_max _ _) (le_refl _)) (le_refl _)
... ≤ _ : begin
  have : #(ulift.{u} bool) ≤ ω,
    from le_of_lt (lt_omega_iff_fintype.2 ⟨infer_instance⟩),
  simp only [max_comm omega.{u}, max_assoc, max_left_comm omega.{u}, max_self, max_eq_left this],
end

end mv_polynomial_fun

open mv_polynomial_fun

namespace mv_polynomial

lemma cardinal_mk_le_max {R σ : Type u} [comm_semiring R] :
  #(mv_polynomial σ R) ≤ max (max (#R) (#σ)) ω :=
calc #(mv_polynomial σ R) ≤ #(W_type (@mv_polynomial_fun.arity R σ)) :
  cardinal.mk_le_of_surjective to_mv_polynomial_surjective
... ≤ max (#(mv_polynomial_fun R σ)) ω : W_type.cardinal_mk_le_max_omega_of_fintype
... ≤ _ : max_le_max cardinal_mv_polynomial_fun_le (le_refl _)
... ≤ _ : by simp only [max_assoc, max_self]

end mv_polynomial

end mv_polynomial

namespace polynomial

lemma cardinal_mk_le_max {R : Type u} [comm_semiring R] : #(polynomial R) ≤ max (#R) ω :=
calc #(polynomial R) = #(mv_polynomial punit.{u + 1} R) :
  cardinal.eq.2 ⟨(mv_polynomial.punit_alg_equiv.{u u} R).to_equiv.symm⟩
... ≤ _ : mv_polynomial.cardinal_mk_le_max
... ≤ _ : begin
  have : #(punit.{u + 1}) ≤ ω, from le_of_lt (lt_omega_iff_fintype.2 ⟨infer_instance⟩),
  rw [max_assoc, max_eq_right this]
end

end polynomial

section field_of_fractions

variables {R K : Type u} [integral_domain R] [field K] [algebra R K] [is_fraction_ring R K]

namespace is_fraction_ring

lemma cardinal_mk_le_max : #K ≤ max (#R) ω :=
calc #K ≤ #R * #R :
  begin
    rw [mul_def],
    refine @mk_le_of_surjective _ _ (λ r : R × R, algebra_map R K r.1 / algebra_map R K r.2) _,
    intros x,
    rcases @div_surjective R _ _ _ _ _ x with ⟨a, b, _, rfl⟩,
    exact ⟨(a, b), rfl⟩,
  end
... ≤ _ : mul_le_max _ _
... ≤ _ : by simp [le_total]

end is_fraction_ring

end field_of_fractions

section algebraic_closure

namespace is_alg_closure

variables (K L : Type u) [field K] [field L] [algebra K L] [is_alg_closure K L]

lemma cardinal_mk_le_max : #L ≤ max (#K) ω :=
calc #L ≤ #(Σ p : polynomial K, { x : L // x ∈ (p.map (algebra_map K L)).roots }) :
  @mk_le_of_injective L (Σ p : polynomial K, { x : L | x ∈ (p.map (algebra_map K L)).roots })
    (λ x : L, ⟨minpoly K x, x,
       begin
         rw [set.mem_set_of_eq, polynomial.mem_roots, polynomial.is_root.def, polynomial.eval_map,
           ← polynomial.aeval_def, minpoly.aeval],
         refine polynomial.map_ne_zero _,
         refine minpoly.ne_zero _,
         rw [← is_algebraic_iff_is_integral],
         exact is_alg_closure.algebraic x
       end⟩) (λ x y, begin
      intro h,
      simp only at h,
      refine (subtype.heq_iff_coe_eq _).1 h.2,
      simp only [h.1, iff_self, forall_true_iff]
    end)
... = cardinal.sum (λ p : polynomial K, #{ x : L | x ∈ (p.map (algebra_map K L)).roots }) :
  (sum_mk _).symm
... ≤ cardinal.sum.{u u} (λ p : polynomial K, ω) : sum_le_sum _ _
  (λ p, le_of_lt begin
    rw [lt_omega_iff_finite],
    classical,
    simp only [← @multiset.mem_to_finset _ _ _ (p.map (algebra_map K L)).roots],
    exact set.finite_mem_finset _,
  end)
... = #(polynomial K) * ω : sum_const _ _
... ≤ max (max (#(polynomial K)) ω) ω : mul_le_max _ _
... ≤ max (max (max (#K) ω) ω) ω :
  max_le_max (max_le_max polynomial.cardinal_mk_le_max (le_refl _)) (le_refl _)
... = max (#K) ω : by simp only [max_assoc, max_comm omega.{u}, max_left_comm omega.{u}, max_self]

end is_alg_closure

end algebraic_closure

section classification

noncomputable theory

variables {K L R : Type*} [integral_domain R]
variables [field K] [algebra R K]
variables [field L] [algebra R L]
variables {ι : Type*} (v : ι → K)
variables {κ : Type*} (w : κ → L)

variables (hv : algebraic_independent R v)

@[derive field, derive algebra (mv_polynomial ι R),
  derive is_fraction_ring (mv_polynomial ι R)]
def rat_fun (v : ι → K) (hv : algebraic_independent R v) : Type* :=
fraction_ring (mv_polynomial ι R)

instance fr_alg (hv : algebraic_independent R v) : algebra (rat_fun v hv) K :=
ring_hom.to_algebra (is_fraction_ring.lift hv)

instance adjoin_alg : algebra (algebra.adjoin R (set.range v)) (rat_fun v hv) :=
ring_hom.to_algebra (ring_hom.comp (algebra_map _ _) hv.repr.to_ring_hom)

instance fr_alg' : is_fraction_ring (algebra.adjoin R (set.range v)) (rat_fun v hv) := sorry

instance fr_sc : is_scalar_tower (algebra.adjoin R (set.range v)) (rat_fun v hv) K :=
is_scalar_tower.of_algebra_map_eq
  (λ x, begin
    show ↑x = is_fraction_ring.lift hv (algebra_map _ _ (hv.repr x)),
    rw [is_fraction_ring.lift_algebra_map hv, mv_polynomial.coe_eval₂_hom,
      ← mv_polynomial.aeval_def, algebraic_independent.aeval_repr]
  end)

lemma is_alg_closure_of_transcendence_basis [is_alg_closed K]
  (hv : is_transcendence_basis R v) : is_alg_closure (rat_fun v hv.1) K :=
{ alg_closed := by apply_instance,
  algebraic := λ x, (is_fraction_ring.is_algebraic_iff (algebra.adjoin R (set.range v)) _).1
    (hv.is_algebraic x) }

variables (hw : algebraic_independent R w)

def rat_fun_equiv (e : ι ≃ κ) : rat_fun v hv ≃+* rat_fun w hw := sorry
-- ring_equiv.of_hom_inv
--   (is_fraction_ring.lift
--     (show function.injective
--         ((algebra_map (mv_polynomial κ R) (rat_fun w hw)).comp
--           (mv_polynomial.rename e).to_ring_hom),
--       from function.injective.comp
--         (is_fraction_ring.injective _ _)
--         (mv_polynomial.rename_injective e e.injective)))
--   (is_fraction_ring.lift
--     (show function.injective
--         ((algebra_map (mv_polynomial ι R) (rat_fun v hv)).comp
--           (mv_polynomial.rename e.symm).to_ring_hom),
--       from function.injective.comp
--         (is_fraction_ring.injective _ _)
--         (mv_polynomial.rename_injective e.symm e.symm.injective)))
--   begin
--     refine is_localization.ring_hom_ext (non_zero_divisors (mv_polynomial ι R)) _,
--     ext;
--     simp
--   end
--   begin
--     refine is_localization.ring_hom_ext (non_zero_divisors (mv_polynomial κ R)) _,
--     ext;
--     simp
--   end

def equiv_of_transcendence_basis
  [is_alg_closed K]
  [is_alg_closed L]
  (e : ι ≃ κ)
  (hv : is_transcendence_basis R v)
  (hw : is_transcendence_basis R w) :
  K ≃+* L :=
by letI := is_alg_closure_of_transcendence_basis v hv;
   letI := is_alg_closure_of_transcendence_basis w hw;
exact is_alg_closure.equiv_of_equiv
  (rat_fun v hv.1) (rat_fun w hw.1) K L (rat_fun_equiv v w hv.1 hw.1 e)

end classification

section cardinal

variables {K L R : Type u} [integral_domain R]
variables [field K] [algebra R K] [is_alg_closed K]
variables {ι : Type u} (v : ι → K)
variable (hv : is_transcendence_basis R v)

lemma cardinal_rat_fun (hv : algebraic_independent R v) :
  #(rat_fun v hv) ≤ max (max (#R) (#ι)) ω :=
calc #(rat_fun v hv) ≤ max (#(mv_polynomial ι R)) ω :is_fraction_ring.cardinal_mk_le_max
... ≤ max (max (max (#R) (#ι)) ω) ω :
  max_le_max mv_polynomial.cardinal_mk_le_max (le_refl _)
... = _ : by simp [max_assoc]

lemma cardinal_le (hv : is_transcendence_basis R v) : #(K) ≤ max (max (#R) (#ι)) ω :=
calc #(K) ≤ max (#(rat_fun v hv.1)) ω :
  by letI := is_alg_closure_of_transcendence_basis v hv;
    exact is_alg_closure.cardinal_mk_le_max _ _
... ≤ max (max (max (#R) (#ι)) ω) ω : max_le_max (cardinal_rat_fun v hv.1) (le_refl _)
... = _ : by simp [max_assoc]

end cardinal

def ring_equiv_of_cardinal_eq
  {K L : Type u}
  [field K] [field L]
  [is_alg_closed K] [is_alg_closed L]
  (hchar : ring_char K = ring_char L)
  (hK : ω < #K) (hKL : #K = #L) :
  K ≃+* L :=
begin


end
