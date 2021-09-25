import data.W.cardinal
import ring_theory.algebraic_independent
import field_theory.is_alg_closed.basic
import field_theory.intermediate_field
import data.polynomial.cardinal
import data.mv_polynomial.cardinal

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

/-- the field of rational functions over `ι`. `v` is an explicit unused argument
here in order to be able to define an `algebra _ K` instance. -/
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

def rat_fun_equiv (e : ι ≃ κ) : rat_fun v hv ≃+* rat_fun w hw :=
ring_equiv.of_hom_inv
  (is_fraction_ring.lift
    (show function.injective
        ((algebra_map (mv_polynomial κ R) (rat_fun w hw)).comp
          (mv_polynomial.rename e).to_ring_hom),
      from function.injective.comp
        (is_fraction_ring.injective _ _)
        (mv_polynomial.rename_injective e e.injective)))
  (is_fraction_ring.lift
    (show function.injective
        ((algebra_map (mv_polynomial ι R) (rat_fun v hv)).comp
          (mv_polynomial.rename e.symm).to_ring_hom),
      from function.injective.comp
        (is_fraction_ring.injective _ _)
        (mv_polynomial.rename_injective e.symm e.symm.injective)))
  begin
    refine is_localization.ring_hom_ext (non_zero_divisors (mv_polynomial ι R)) _,
    ext;
    simp
  end
  begin
    refine is_localization.ring_hom_ext (non_zero_divisors (mv_polynomial κ R)) _,
    ext;
    simp
  end

/-- setting `R` to be `zmod (ring_char K)` this result shows that if two algebraically
closed fields have the same size transcendence basis and the same characteristic then they are
isomorphic. -/
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

/-- If `K` is an uncountable algebraically closed field, then its
cardinality is the same as that of a transcendence basis. -/
lemma cardinal_eq_cardinal_transcendence_basis_of_omega_lt
  (hv : is_transcendence_basis R v)
  (hR : #R ≤ ω)
  (hK : ω < #K) :
  #K = #ι :=
have ω ≤ #ι,
  from le_of_not_lt (λ h,
    not_le_of_gt hK $ calc
      #K ≤ max (max (#R) (#ι)) ω : cardinal_le v hv
     ... ≤ _ : max_le (max_le hR (le_of_lt h)) (le_refl _)),
le_antisymm
  (calc #K ≤ max (max (#R) (#ι)) ω : cardinal_le v hv
       ... = #ι : begin
         rw [max_eq_left, max_eq_right],
         { exact le_trans hR this },
         { exact le_max_of_le_right this }
       end)
  (mk_le_of_injective (show function.injective v, from hv.1.injective))


end cardinal

--TODO: prove for algebraically closed fields of characteristic `p`
/-- Two uncountable algebraically closed fields of characteristic zero are isomorphic
if they have the same cardinality. -/
def ring_equiv_of_cardinal_eq
  {K L : Type}
  [field K] [field L]
  [is_alg_closed K] [is_alg_closed L]
  [char_zero K] [char_zero L]
  (hK : ω < #K) (hKL : #K = #L) :
  K ≃+* L :=
begin
  apply classical.choice,
  cases exists_is_transcendence_basis ℤ
    (show function.injective (algebra_map ℤ K),
      from int.cast_injective) with s hs,
  cases exists_is_transcendence_basis ℤ
    (show function.injective (algebra_map ℤ L),
      from int.cast_injective) with t ht,
  have : #s = #t,
  { rw [← cardinal_eq_cardinal_transcendence_basis_of_omega_lt _ hs (le_of_eq mk_int) hK,
        ← cardinal_eq_cardinal_transcendence_basis_of_omega_lt _ ht (le_of_eq mk_int), hKL],
    rwa ← hKL },
  cases cardinal.eq.1 this with e,
  exact ⟨equiv_of_transcendence_basis _ _ e hs ht⟩,
end
