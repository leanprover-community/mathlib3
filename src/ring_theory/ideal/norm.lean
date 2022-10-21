/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best
-/

import data.matrix.notation
import data.zmod.quotient
import linear_algebra.free_module.finite.basic
import linear_algebra.free_module.pid
import linear_algebra.isomorphisms
import ring_theory.dedekind_domain.ideal
import ring_theory.norm

/-!

# Ideal norms

This file defines the absolute ideal norm `ideal.abs_norm (I : ideal R) : ℕ` as the cardinality of
the quotient `R ⧸ I` (setting it to 0 if the cardinality is infinite).

## Main definitions

 * `submodule.card_quot (S : submodule R M)`: the cardinality of the quotient `M ⧸ S`, in `ℕ`.
   This maps `⊥` to `0` and `⊤` to `1`.
 * `ideal.abs_norm (I : ideal R)`: the absolute ideal norm, defined as
   the cardinality of the quotient `R ⧸ I`, as a bundled monoid-with-zero homomorphism.

## TODO

Define the relative norm.
-/

open_locale big_operators

section move_me

section
open_locale classical

-- really we only need one infinite and the others inhabited
instance {ι : Type*} {π : ι → Sort*} [∀ i, infinite $ π i] [nonempty ι] : infinite (Π i : ι, π i) :=
infinite.of_injective (λ (i : π (classical.arbitrary ι)) t,
  if h : t = classical.arbitrary ι then
    cast (congr_arg π h.symm) i
  else
    classical.arbitrary _)
  (λ x y h, by simpa using congr_fun h (classical.arbitrary ι))

-- really we only need one infinite and the others inhabited
instance {ι π : Sort*} [infinite π] [has_zero π] [nonempty ι] : infinite (ι →₀ π) :=
infinite.of_injective (λ i, finsupp.single (classical.arbitrary ι) i)
  (finsupp.single_injective (classical.arbitrary ι))

-- TODO also dfinsupp?

end

lemma basis.repr_sum_self {ι R M : Type*} [fintype ι] [comm_semiring R]
  [add_comm_monoid M] [module R M] (b : basis ι R M) (c : ι → R) :
  ⇑(b.repr (∑ i, c i • b i)) = c :=
begin
  ext j,
  simp only [linear_equiv.map_sum, linear_equiv.map_smul, basis.repr_self, finsupp.smul_single,
             smul_eq_mul, mul_one, finset.sum_apply'],
  rw [finset.sum_eq_single j, finsupp.single_eq_same],
  { rintros i - hi, exact finsupp.single_eq_of_ne hi },
  { intros, have := finset.mem_univ j, contradiction }
end

lemma basis.mem_submodule_iff {ι R M : Type*} [comm_ring R] [add_comm_group M] [module R M]
  {P : submodule R M} (b : basis ι R P) {x : M} :
  x ∈ P ↔ ∃ (c : ι →₀ R), x = finsupp.sum c (λ i x, x • b i) :=
begin
  split,
  { intro hx, use b.repr ⟨x, hx⟩,
    calc P.subtype ⟨x, hx⟩
        = P.subtype (b.repr.symm (b.repr ⟨x, hx⟩)) : by rw [linear_equiv.symm_apply_apply]
    ... = (b.repr ⟨x, hx⟩).sum (λ i x, x • P.subtype (b i)) : _,
    rw [basis.repr_symm_apply, P.subtype.map_finsupp_total, finsupp.total_apply] },
  { rintros ⟨c, rfl⟩,
    exact P.sum_mem (λ i _, P.smul_mem _ (b i).2) },
end

lemma basis.mem_submodule_iff' {ι R M : Type*} [fintype ι] [comm_ring R] [add_comm_group M]
  [module R M] {P : submodule R M} (b : basis ι R P) {x : M} :
  x ∈ P ↔ ∃ (c : ι → R), x = ∑ i, c i • b i :=
b.mem_submodule_iff.trans $ finsupp.equiv_fun_on_fintype.exists_congr_left.trans $ exists_congr $
λ c, by simp [finsupp.sum_fintype]

lemma basis.mem_ideal_iff {ι R S : Type*} [comm_ring R] [comm_ring S] [algebra R S]
  {I : ideal S} (b : basis ι R I) {x : S} :
  x ∈ I ↔ ∃ (c : ι →₀ R), x = finsupp.sum c (λ i x, x • b i) :=
(b.map ((I.restrict_scalars_equiv R _ _).restrict_scalars R).symm).mem_submodule_iff

lemma basis.mem_ideal_iff' {ι R S : Type*} [fintype ι] [comm_ring R] [comm_ring S] [algebra R S]
  {I : ideal S} (b : basis ι R I) {x : S} :
  x ∈ I ↔ ∃ (c : ι → R), x = ∑ i, c i • b i :=
(b.map ((I.restrict_scalars_equiv R _ _).restrict_scalars R).symm).mem_submodule_iff'

lemma le_comap_single_pi {ι R : Type*} [decidable_eq ι] [comm_ring R]
  {M : ι → Type*} [∀ i, add_comm_group (M i)] [∀ i, module R (M i)]
  (p : ∀ i, submodule R (M i)) {i} :
  p i ≤ submodule.comap (linear_map.single i : M i →ₗ[R] _) (submodule.pi set.univ p) :=
begin
  intros x hx,
  rw [submodule.mem_comap, submodule.mem_pi],
  rintros j -,
  by_cases h : j = i,
  { rwa [h, linear_map.coe_single, pi.single_eq_same] },
  { rw [linear_map.coe_single, pi.single_eq_of_ne h], exact (p j).zero_mem }
end

/-- If `P` is a submodule of `M` and `Q` a submodule of `N`,
and `f : M ≃ₗ N` maps `P` to `Q`, then `M ⧸ P` is equivalent to `N ⧸ Q`. -/
@[simps] def submodule.quotient.equiv {R M N : Type*} [comm_ring R]
  [add_comm_group M] [module R M] [add_comm_group N] [module R N]
  (P : submodule R M) (Q : submodule R N)
  (f : M ≃ₗ[R] N) (hf : P.map (f : M →ₗ[R] N) = Q) : (M ⧸ P) ≃ₗ[R] N ⧸ Q :=
{ to_fun := P.mapq Q (f : M →ₗ[R] N) (λ x hx, hf ▸ submodule.mem_map_of_mem hx),
  inv_fun := Q.mapq P (f.symm : N →ₗ[R] M) (λ x hx, begin
    rw [← hf, submodule.mem_map] at hx,
    obtain ⟨y, hy, rfl⟩ := hx,
    simpa
  end),
  left_inv := λ x, quotient.induction_on' x (by simp),
  right_inv := λ x, quotient.induction_on' x (by simp),
  .. P.mapq Q (f : M →ₗ[R] N) (λ x hx, hf ▸ submodule.mem_map_of_mem hx) }

/-- Lift a family of maps to the direct sum of quotients. -/
def submodule.pi_quotient_lift {ι R : Type*} [fintype ι] [decidable_eq ι] [comm_ring R]
  {M : ι → Type*} [∀ i, add_comm_group (M i)] [∀ i, module R (M i)]
  {N : Type*} [add_comm_group N] [module R N]
  (p : ∀ i, submodule R (M i)) (q : submodule R N)
  (f : Π i, M i →ₗ[R] N) (hf : ∀ i, p i ≤ q.comap (f i)) :
  (Π i, (M i ⧸ p i)) →ₗ[R] (N ⧸ q) :=
linear_map.lsum R (λ i, (M i ⧸ (p i))) R (λ i, (p i).mapq q (f i) (hf i))

@[simp] lemma submodule.pi_quotient_lift_mk {ι R : Type*} [fintype ι] [decidable_eq ι] [comm_ring R]
  {M : ι → Type*} [∀ i, add_comm_group (M i)] [∀ i, module R (M i)]
  {N : Type*} [add_comm_group N] [module R N]
  (p : ∀ i, submodule R (M i)) (q : submodule R N)
  (f : Π i, M i →ₗ[R] N) (hf : ∀ i, p i ≤ q.comap (f i)) (x : Π i, M i) :
  submodule.pi_quotient_lift p q f hf (λ i, submodule.quotient.mk (x i)) =
    submodule.quotient.mk (linear_map.lsum _ _ R f x) :=
by rw [submodule.pi_quotient_lift, linear_map.lsum_apply, linear_map.sum_apply,
       ← submodule.mkq_apply, linear_map.lsum_apply, linear_map.sum_apply, linear_map.map_sum];
   simp only [linear_map.coe_proj, submodule.mapq_apply, submodule.mkq_apply, linear_map.comp_apply]

@[simp] lemma submodule.pi_quotient_lift_single {ι R : Type*} [fintype ι] [decidable_eq ι]
  [comm_ring R] {M : ι → Type*} [∀ i, add_comm_group (M i)] [∀ i, module R (M i)]
  {N : Type*} [add_comm_group N] [module R N]
  (p : ∀ i, submodule R (M i)) (q : submodule R N)
  (f : Π i, M i →ₗ[R] N) (hf : ∀ i, p i ≤ q.comap (f i)) (i) (x : M i ⧸ p i) :
  submodule.pi_quotient_lift p q f hf (pi.single i x) =
    submodule.mapq _ _ (f i) (hf i) x :=
begin
  simp_rw [submodule.pi_quotient_lift, linear_map.lsum_apply, linear_map.sum_apply,
           linear_map.comp_apply, linear_map.proj_apply],
  rw finset.sum_eq_single i,
  { rw pi.single_eq_same },
  { rintros j - hj, rw [pi.single_eq_of_ne hj, linear_map.map_zero] },
  { intros, have := finset.mem_univ i, contradiction },
end

/-- Lift a family of maps to a quotient of direct sums. -/
def submodule.quotient_pi_lift {ι R : Type*} [comm_ring R]
  {M : ι → Type*} [∀ i, add_comm_group (M i)] [∀ i, module R (M i)]
  {N : ι → Type*} [∀ i, add_comm_group (N i)] [∀ i, module R (N i)]
  (p : ∀ i, submodule R (M i))
  (f : Π i, M i →ₗ[R] N i) (hf : ∀ i, p i ≤ linear_map.ker (f i)) :
  ((Π i, M i) ⧸ submodule.pi set.univ p) →ₗ[R] Π i, N i :=
(submodule.pi set.univ p).liftq (linear_map.pi (λ i, (f i).comp (linear_map.proj i))) $
λ x hx, linear_map.mem_ker.mpr $
by { ext i, simpa using hf i (submodule.mem_pi.mp hx i (set.mem_univ i)) }

@[simp] lemma submodule.quotient_pi_lift_mk {ι R : Type*} [comm_ring R]
  {M : ι → Type*} [∀ i, add_comm_group (M i)] [∀ i, module R (M i)]
  {N : ι → Type*} [∀ i, add_comm_group (N i)] [∀ i, module R (N i)]
  (p : ∀ i, submodule R (M i))
  (f : Π i, M i →ₗ[R] N i) (hf : ∀ i, p i ≤ linear_map.ker (f i)) (x : Π i, M i) :
  submodule.quotient_pi_lift p f hf (submodule.quotient.mk x) = λ i, f i (x i) :=
rfl

@[simp] lemma sum_pi_single {ι : Type*} [fintype ι] [decidable_eq ι]
  {M : ι → Type*} [∀ i, add_comm_monoid (M i)] (x : Π i, M i) :
  ∑ i, pi.single i (x i) = x :=
funext (λ j, begin
  rw [finset.sum_apply, finset.sum_eq_single j],
  { simp },
  { rintros i - hi, exact pi.single_eq_of_ne hi.symm _ },
  { simp }
end)

@[simp] lemma linear_map.lsum_single {ι R : Type*} [fintype ι] [decidable_eq ι] [comm_ring R]
  {M : ι → Type*} [∀ i, add_comm_group (M i)] [∀ i, module R (M i)] :
  linear_map.lsum R M R linear_map.single = linear_map.id :=
linear_map.ext (λ x, by simp)

/-- The quotient of a direct sum is the direct sum of quotients -/
@[simps] def submodule.quotient_pi {ι R : Type*} [fintype ι] [decidable_eq ι] [comm_ring R]
  {M : ι → Type*} [∀ i, add_comm_group (M i)] [∀ i, module R (M i)]
  (p : ∀ i, submodule R (M i)) :
  ((Π i, M i) ⧸ submodule.pi set.univ p) ≃ₗ[R] Π i, M i ⧸ p i :=
{ to_fun := submodule.quotient_pi_lift p (λ i, (p i).mkq) (λ i, by simp),
  inv_fun := submodule.pi_quotient_lift p (submodule.pi set.univ p)
    linear_map.single (λ i, le_comap_single_pi p),
  left_inv := λ x, quotient.induction_on' x (λ x',
    by simp_rw [submodule.quotient.mk'_eq_mk, submodule.quotient_pi_lift_mk, submodule.mkq_apply,
                submodule.pi_quotient_lift_mk, linear_map.lsum_single, linear_map.id_apply]),
  right_inv := begin
    rw [function.right_inverse_iff_comp, ← linear_map.coe_comp, ← @linear_map.id_coe R],
    refine congr_arg _ (linear_map.pi_ext (λ i x, quotient.induction_on' x (λ x', funext $ λ j, _))),
    rw [linear_map.comp_apply, submodule.pi_quotient_lift_single, submodule.quotient.mk'_eq_mk,
        submodule.mapq_apply, submodule.quotient_pi_lift_mk, linear_map.id_apply],
    by_cases hij : i = j; simp only [submodule.mkq_apply, linear_map.coe_single],
    { subst hij, simp only [pi.single_eq_same] },
    { simp only [pi.single_eq_of_ne (ne.symm hij), submodule.quotient.mk_zero] },
  end,
  .. submodule.quotient_pi_lift p (λ i, (p i).mkq) (λ i, by simp) }

instance {R M : Type*} [ring R] [add_comm_group M] [module R M] [infinite M] :
  infinite (M ⧸ (⊥ : submodule R M)) :=
infinite.of_injective submodule.quotient.mk $ λ x y h, sub_eq_zero.mp $
  (submodule.quotient.eq ⊥).mp h

instance submodule.quotient_top.unique {R M : Type*} [ring R] [add_comm_group M] [module R M] :
  unique (M ⧸ (⊤ : submodule R M)) :=
{ default := 0,
  uniq := λ x, quotient.induction_on' x $ λ x, (submodule.quotient.eq ⊤).mpr submodule.mem_top }

lemma submodule.unique_quotient_iff_eq_top {R M : Type*} [ring R] [add_comm_group M] [module R M]
  {P : submodule R M} :
  nonempty (unique (M ⧸ P)) ↔ P = ⊤ :=
begin
  split,
  { rintro ⟨h⟩,
    refine eq_top_iff.mpr (λ x _, _),
    have this : x - 0 ∈ P := (submodule.quotient.eq P).mp (by exactI subsingleton.elim _ _),
    rwa [sub_zero] at this },
  { rintro rfl,
    exact ⟨submodule.quotient_top.unique⟩ }
end

/-- Any two modules that are subsingletons are isomorphic. -/
@[simps] def linear_equiv.of_subsingleton (R : Type*) {M N : Type*} [semiring R]
  [add_comm_monoid M] [add_comm_monoid N] [module R M] [module R N]
  [subsingleton M] [subsingleton N] : M ≃ₗ[R] N :=
{ to_fun := λ _, 0,
  inv_fun := λ _, 0,
  left_inv := λ x, subsingleton.elim _ _,
  right_inv := λ x, subsingleton.elim _ _,
  .. (0 : M →ₗ[R] N)}

noncomputable instance {R M : Type*} [ring R] [add_comm_group M] [module R M]
  [fintype M] (S : submodule R M) :
  fintype (M ⧸ S) :=
@@quotient.fintype _ _ (λ _ _, classical.dec _)

lemma ideal.span_singleton_le_iff_mem {a : S} {I : ideal S} :
  ideal.span {a} ≤ I ↔ a ∈ I :=
submodule.span_singleton_le_iff_mem _ _

end move_me

namespace submodule

variables {R M : Type*} [ring R] [add_comm_group M] [module R M]

section

/-- The cardinality of `(M ⧸ S)`, if `(M ⧸ S)` is finite, and `0` otherwise.
This is used to define the absolute ideal norm `ideal.abs_norm`.
-/
noncomputable def card_quot (S : submodule R M) : ℕ :=
add_subgroup.index S.to_add_subgroup

@[simp] lemma card_quot_apply (S : submodule R M) [fintype (M ⧸ S)] :
  card_quot S = fintype.card (M ⧸ S) :=
add_subgroup.index_eq_card _

variables (R M)

@[simp] lemma card_quot_bot [infinite M] : card_quot (⊥ : submodule R M) = 0 :=
add_subgroup.index_bot.trans nat.card_eq_zero_of_infinite

@[simp] lemma card_quot_top : card_quot (⊤ : submodule R M) = 1 :=
add_subgroup.index_top

variables {R M}

@[simp] lemma card_quot_eq_one_iff {P : submodule R M} : card_quot P = 1 ↔ P = ⊤ :=
add_subgroup.index_eq_one.trans (by simp [set_like.ext_iff])

/-- A (non-canonical) bijection between a module `M` and the product `(M / S) × S` -/
noncomputable def module_equiv_quotient_times_submodule (S : submodule R M) :
  M ≃ (M ⧸ S) × S :=
calc M ≃ Σ L : M ⧸ S, {x : M // quotient.mk x = L} :
  (equiv.sigma_preimage_equiv S.mkq).symm
    ... ≃ Σ L : M ⧸ S, {x : M // x - quotient.out' L ∈ S} :
  equiv.sigma_congr_right (λ L, (equiv.refl M).subtype_equiv (λ x,
    by { conv_lhs { rw ← quotient.out_eq' L },
      rw [submodule.quotient.mk'_eq_mk, submodule.quotient.eq, equiv.refl_apply] }))
    ... ≃ Σ L : M ⧸ S, S :
  equiv.sigma_congr_right (λ L,
    ⟨λ x, ⟨x.1 - quotient.out' L, x.2⟩,
     λ x, ⟨x.1 + quotient.out' L, by simp⟩,
     λ ⟨x, hx⟩, subtype.eq $ by simp,
     λ ⟨g, hg⟩, subtype.eq $ by simp⟩)
    ... ≃ (M ⧸ S) × S :
  equiv.sigma_equiv_prod _ _

lemma card_eq_card_quotient_mul_card [fintype M] (S : submodule R M) [decidable_pred (∈ S)]  :
  fintype.card M = fintype.card S * fintype.card (M ⧸ S) :=
by { rw [mul_comm, ← fintype.card_prod],
     exact fintype.card_congr (module_equiv_quotient_times_submodule S) }

/-- `[S : T] [M : S] = [M : T]` -/
lemma card_quotient_mul_card_quotient (S T : submodule R M) (hST : T ≤ S)
  [fintype (M ⧸ S)] [fintype (M ⧸ T)] :
  fintype.card (S.map T.mkq) * fintype.card (M ⧸ S) = fintype.card (M ⧸ T) :=
by rw [submodule.card_eq_card_quotient_mul_card (map T.mkq S),
       fintype.card_eq.mpr ⟨(quotient_quotient_equiv_quotient T S hST).to_equiv⟩]

end

end submodule

section fintype_quotient

variables {ι R S : Type*} [comm_ring R] [comm_ring S] [algebra R S]
variables [is_domain R] [is_principal_ideal_ring R] [is_domain S] [fintype ι]

/-- If `S` a finite-dimensional ring extension of a PID `R` which is free as an `R`-module,
then any nonzero `S`-ideal `I` is free as an `R`-submodule of `S`, and we can
find a basis for `S` and `I` such that the inclusion map is a square diagonal
matrix; this is the basis for `S`.

See `ideal.self_basis` for the basis on `I`,
see `ideal.smith_coeffs` for the entries of the diagonal matrix
and `ideal.self_basis_def` for the proof that the inclusion map forms a square diagonal matrix.
-/
noncomputable def ideal.ring_basis (b : basis ι R S) (I : ideal S) (hI : I ≠ ⊥) :
  basis ι R S := (ideal.exists_smith_normal_form b I hI).some

/-- If `S` a finite-dimensional ring extension of a PID `R` which is free as an `R`-module,
then any nonzero `S`-ideal `I` is free as an `R`-submodule of `S`, and we can
find a basis for `S` and `I` such that the inclusion map is a square diagonal
matrix; this is the basis for `I`.

See `ideal.ring_basis` for the basis on `S`,
see `ideal.smith_coeffs` for the entries of the diagonal matrix
and `ideal.self_basis_def` for the proof that the inclusion map forms a square diagonal matrix.
-/
noncomputable def ideal.self_basis (b : basis ι R S) (I : ideal S) (hI : I ≠ ⊥) :
  basis ι R I := (ideal.exists_smith_normal_form b I hI).some_spec.some_spec.some

/-- If `S` a finite-dimensional ring extension of a PID `R` which is free as an `R`-module,
then any nonzero `S`-ideal `I` is free as an `R`-submodule of `S`, and we can
find a basis for `S` and `I` such that the inclusion map is a square diagonal
matrix; these are the entries of the diagonal matrix.

See `ideal.ring_basis` for the basis on `S`,
see `ideal.self_basis` for the basis on `I`,
and `ideal.self_basis_def` for the proof that the inclusion map forms a square diagonal matrix.
-/
noncomputable def ideal.smith_coeffs (b : basis ι R S) (I : ideal S) (hI : I ≠ ⊥) :
  ι → R := (ideal.exists_smith_normal_form b I hI).some_spec.some

/-- If `S` a finite-dimensional ring extension of a PID `R` which is free as an `R`-module,
then any nonzero `S`-ideal `I` is free as an `R`-submodule of `S`, and we can
find a basis for `S` and `I` such that the inclusion map is a square diagonal
matrix.
-/
@[simp]
lemma ideal.self_basis_def (b : basis ι R S) (I : ideal S) (hI : I ≠ ⊥) :
  ∀ i, (ideal.self_basis b I hI i : S) = ideal.smith_coeffs b I hI i • ideal.ring_basis b I hI i :=
(ideal.exists_smith_normal_form b I hI).some_spec.some_spec.some_spec

@[simp]
lemma ideal.smith_coeffs_ne_zero (b : basis ι R S) (I : ideal S) (hI : I ≠ ⊥) (i) :
  ideal.smith_coeffs b I hI i ≠ 0 :=
begin
  intro hi,
  apply basis.ne_zero (ideal.self_basis b I hI) i,
  refine subtype.coe_injective _,
  simp [hi]
end

/-- We can write the quotient of an ideal over a PID as a product of quotients by principal ideals. -/
noncomputable def ideal.quotient_equiv_pi_span
  (I : ideal S) (b : basis ι R S) (hI : I ≠ ⊥) :
  (S ⧸ I) ≃ₗ[R] Π i, (R ⧸ ideal.span ({I.smith_coeffs b hI i} : set R)) :=
begin
  -- Choose `e : S ≃ₗ I` and a basis `b'` for `S` that turns the map
  -- `f := ((submodule.subtype I).restrict_scalars R).comp e` into a diagonal matrix:
  -- there is an `a : ι → ℤ` such that `f (b' i) = a i • b' i`.
  let a := I.smith_coeffs b hI,
  let b' := I.ring_basis b hI,
  let ab := I.self_basis b hI,
  have ab_eq := I.self_basis_def b hI,
  let e : S ≃ₗ[R] I := b'.equiv ab (equiv.refl _),
  let f : S →ₗ[R] S := (I.subtype.restrict_scalars R).comp (e : S →ₗ[R] I),
  let f_apply : ∀ x, f x = b'.equiv ab (equiv.refl _) x := λ x, rfl,
  have ha : ∀ i, f (b' i) = a i • b' i,
  { intro i, rw [f_apply, b'.equiv_apply, equiv.refl_apply, ab_eq] },
  have mem_I_iff : ∀ x, x ∈ I ↔ ∀ i, a i ∣ b'.repr x i,
  { intro x, simp_rw [ab.mem_ideal_iff', ab_eq],
    have : ∀ (c : ι → R) i, b'.repr (∑ (j : ι), c j • a j • b' j) i = a i * c i,
    { intros c i,
      simp only [← mul_action.mul_smul, b'.repr_sum_self, mul_comm] },
    split,
    { rintro ⟨c, rfl⟩ i, exact ⟨c i, this c i⟩ },
    { rintros ha,
      choose c hc using ha, exact ⟨c, b'.ext_elem (λ i, trans (hc i) (this c i).symm)⟩ } },

  -- Now we map everything through the linear equiv `S ≃ₗ (ι → R)`,
  -- which maps `I` to `I' := Π i, a i ℤ`.
  let I' : submodule R (ι → R) := submodule.pi set.univ (λ i, ideal.span ({a i} : set R)),
  have : submodule.map (b'.equiv_fun : S →ₗ[R] (ι → R)) (I.restrict_scalars R) = I',
  { ext x,
    simp only [submodule.mem_map, submodule.mem_pi, ideal.mem_span_singleton, set.mem_univ,
               submodule.restrict_scalars_mem, mem_I_iff, smul_eq_mul, forall_true_left,
               linear_equiv.coe_coe, basis.equiv_fun_apply],
    split,
    { rintros ⟨y, hy, rfl⟩ i, exact hy i },
    { rintros hdvd,
      refine ⟨∑ i, x i • b' i, λ i, _, _⟩; rwa b'.repr_sum_self,
      { exact hdvd i } } },
  refine ((submodule.quotient.restrict_scalars_equiv R I).restrict_scalars R).symm.trans _,
  any_goals { apply ring_hom.id }, any_goals { apply_instance },
  refine (submodule.quotient.equiv (I.restrict_scalars R) I' b'.equiv_fun this).trans _,
  any_goals { apply ring_hom.id }, any_goals { apply_instance },
  classical,
  let := submodule.quotient_pi (show Π i, submodule R R, from λ i, ideal.span ({a i} : set R)),
  exact this
end

-- TODO: do we want to strengthen the equiv (e.g. ring equiv?)
/-- Ideal quotients over a free finite extension of `ℤ` are isomorphic to a direct product of `zmod`. -/
noncomputable def ideal.quotient_equiv_pi_zmod
  (I : ideal S) (b : basis ι ℤ S) (hI : I ≠ ⊥) :
  (S ⧸ I) ≃ Π i, (zmod (I.smith_coeffs b hI i).nat_abs) :=
begin
  let a := I.smith_coeffs b hI,
  let e := I.quotient_equiv_pi_span b hI,
  recover,
  let e' : (Π (i : ι), (ℤ ⧸ ideal.span ({a i} : set ℤ))) ≃ Π (i : ι), zmod (a i).nat_abs :=
    equiv.Pi_congr (equiv.refl _) (λ i, (int.quotient_span_equiv_zmod (a i)).to_equiv),
  refine (_ : (S ⧸ I) ≃ₗ[ℤ] _).to_equiv.trans e',
  -- TODO: probably from the `module _ (S ⧸ I)` instance assuming `is_scalar_tower`
  haveI : unique (module ℤ (S ⧸ I)) := add_comm_group.int_module.unique,
  convert e
end

/-- A nonzero ideal over a free finite extension of `ℤ` has a finite quotient. -/
noncomputable def ideal.fintype_quotient_of_free_of_ne_bot [decidable_eq ι]
  (I : ideal S) (b : basis ι ℤ S) (hI : I ≠ ⊥) :
  fintype (S ⧸ I) :=
begin
  let a := I.smith_coeffs b hI,
  let e := I.quotient_equiv_pi_zmod b hI,
  haveI : ∀ i, ne_zero (a i).nat_abs := λ i,
    ⟨int.nat_abs_ne_zero_of_ne_zero (ideal.smith_coeffs_ne_zero b I hI i)⟩,
  exact fintype.of_equiv (Π i, zmod (a i).nat_abs) e.symm,
end

end fintype_quotient

/-- The product over `fin 2` of some rings is just the cartesian product of these rings. -/
@[simps]
def ring_equiv.fin_two (α : fin 2 → Type*) [Π i, semiring (α i)] :
  (Π (i : fin 2), α i) ≃+* α 0 × α 1 :=
{ to_fun := pi_fin_two_equiv α,
  map_add' := λ a b, rfl,
  map_mul' := λ a b, rfl,
  .. pi_fin_two_equiv α }

section dedekind_domain_inf

open ideal

variables {S : Type*} [comm_ring S] [is_domain S]

open_locale classical

@[simp] lemma sup_mul_inf {D : Type*} [comm_ring D] [is_domain D] [is_dedekind_domain D]
  (I J : ideal D) : (I ⊔ J) * (I ⊓ J) = I * J :=
begin
  letI := unique_factorization_monoid.to_normalized_gcd_monoid (ideal D),
  have hgcd : gcd I J = I ⊔ J,
  { rw [gcd_eq_normalize _ _, normalize_eq],
    { rw [ideal.dvd_iff_le, sup_le_iff, ← ideal.dvd_iff_le, ← ideal.dvd_iff_le],
      exact ⟨gcd_dvd_left _ _, gcd_dvd_right _ _⟩ },
    { rw [dvd_gcd_iff, ideal.dvd_iff_le, ideal.dvd_iff_le],
      simp } },
  have hlcm : lcm I J = I ⊓ J,
  { rw [lcm_eq_normalize _ _, normalize_eq],
    { rw [lcm_dvd_iff, ideal.dvd_iff_le, ideal.dvd_iff_le],
      simp, },
    { rw [ideal.dvd_iff_le, le_inf_iff, ← ideal.dvd_iff_le, ← ideal.dvd_iff_le],
      exact ⟨dvd_lcm_left _ _, dvd_lcm_right _ _⟩ } },
  rw [← hgcd, ← hlcm, associated_iff_eq.mp (gcd_mul_lcm _ _)],
  apply_instance
end

/-- Ideals in a Dedekind domain have gcd and lcm operators that (trivially) are compatible with
the normalization operator. -/
instance {D : Type*} [comm_ring D] [is_domain D] [is_dedekind_domain D] :
  normalized_gcd_monoid (ideal D) :=
{ gcd := (⊔),
  gcd_dvd_left := λ _ _, by simpa only [ideal.dvd_iff_le] using le_sup_left,
  gcd_dvd_right := λ _ _, by simpa only [ideal.dvd_iff_le] using le_sup_right,
  dvd_gcd := λ _ _ _, by simpa only [ideal.dvd_iff_le] using sup_le,
  lcm := (⊓),
  lcm_zero_left := λ _, by simp only [ideal.zero_eq_bot, bot_inf_eq],
  lcm_zero_right := λ _, by simp only [ideal.zero_eq_bot, inf_bot_eq],
  gcd_mul_lcm := λ _ _, by rw [associated_iff_eq, sup_mul_inf],
  normalize_gcd := λ _ _, normalize_eq _,
  normalize_lcm := λ _ _, normalize_eq _,
  .. ideal.normalization_monoid }

@[simp]
lemma gcd_eq_sup {R : Type*} [comm_ring R] [is_domain R] [is_dedekind_domain R] (I J : ideal R) :
  gcd I J = I ⊔ J :=
rfl

@[simp]
lemma lcm_eq_inf {R : Type*} [comm_ring R] [is_domain R] [is_dedekind_domain R] (I J : ideal R) :
  lcm I J = I ⊓ J :=
rfl

lemma inf_eq_mul_of_coprime [is_dedekind_domain S] {I J : ideal S} (coprime : I ⊔ J = ⊤) :
  I ⊓ J = I * J :=
by rw [← associated_iff_eq.mp (gcd_mul_lcm I J), lcm_eq_inf I J, gcd_eq_sup, coprime, ideal.top_mul]

end dedekind_domain_inf

lemma set.range_fin_two {α : Type*} (f : fin 2 → α) :
  set.range f = {f 0, f 1} :=
begin
  ext fi,
  rw set.mem_range,
  split,
  { rintro ⟨i, rfl⟩,
    fin_cases i; simp },
  { rintro (hi | hi); exact ⟨_, hi.symm⟩ },
end

@[simp]
lemma infi_fin_two {α : Type*} (f : fin 2 → α) [complete_lattice α] :
  (⨅ (i : fin 2), f i) = f 0 ⊓ f 1 :=
by rw [infi, set.range_fin_two, Inf_insert, Inf_singleton]

variables {ι S : Type*} [comm_ring S] [is_domain S]

/-- Chinese remainder theorem, specialized to two ideals. -/
noncomputable def ideal.quotient_mul_equiv_quotient_prod [is_dedekind_domain S] (I J : ideal S)
  (coprime : I ⊔ J = ⊤) :
  (S ⧸ (I * J)) ≃+* (S ⧸ I) × S ⧸ J :=
let f : fin 2 → ideal S := ![I, J] in
have hf : ∀ (i j : fin 2), i ≠ j → f i ⊔ f j = ⊤,
{ intros i j h,
  fin_cases i; fin_cases j; try { contradiction }; simpa [f, sup_comm] using coprime },
ring_equiv.trans (ideal.quotient_equiv _ _ (ring_equiv.refl S)
  (trans (infi_fin_two f) $ (inf_eq_mul_of_coprime coprime).trans $ (ideal.map_id _).symm)) $
ring_equiv.trans (ideal.quotient_inf_ring_equiv_pi_quotient f hf)
  (ring_equiv.fin_two (λ i, S ⧸ f i))

open submodule

/-- Multiplicity of the ideal norm, for coprime ideals.
This is essentially just a repackaging of the Chinese Remainder Theorem.
-/
lemma card_quot_mul_of_coprime [is_dedekind_domain S] [module.free ℤ S] [module.finite ℤ S]
  (I J : ideal S) (coprime : I ⊔ J = ⊤) : card_quot (I * J) = card_quot I * card_quot J :=
begin
  let b := module.free.choose_basis ℤ S,
  casesI is_empty_or_nonempty (module.free.choose_basis_index ℤ S),
  { haveI : subsingleton S := function.surjective.subsingleton b.repr.to_equiv.symm.surjective,
    nontriviality S,
    exfalso,
    exact not_nontrivial_iff_subsingleton.mpr ‹subsingleton S› ‹nontrivial S› },
  haveI : infinite S := infinite.of_surjective _ b.repr.to_equiv.surjective,
  by_cases hI : I = ⊥,
  { rw [hI, submodule.bot_mul, card_quot_bot, zero_mul] },
  by_cases hJ : J = ⊥,
  { rw [hJ, submodule.mul_bot, card_quot_bot, mul_zero] },
  have hIJ : I * J ≠ ⊥ := mt ideal.mul_eq_bot.mp (not_or hI hJ),

  letI := classical.dec_eq (module.free.choose_basis_index ℤ S),
  letI := I.fintype_quotient_of_free_of_ne_bot b hI,
  letI := J.fintype_quotient_of_free_of_ne_bot b hJ,
  letI := (I * J).fintype_quotient_of_free_of_ne_bot b hIJ,

  rw [card_quot_apply, card_quot_apply, card_quot_apply,
      fintype.card_eq.mpr ⟨(ideal.quotient_mul_equiv_quotient_prod I J coprime).to_equiv⟩,
      fintype.card_prod]
end

lemma unique_factorization_monoid.pow_eq_pow_iff {M : Type*}
  [cancel_comm_monoid_with_zero M] [unique_factorization_monoid M]
  {a : M} (ha0 : a ≠ 0) (ha1 : ¬ is_unit a) {i j : ℕ} : a ^ i = a ^ j ↔ i = j :=
begin
  letI := classical.dec_eq M,
  split,
  { intros hij,
    letI : nontrivial M := ⟨⟨a, 0, ha0⟩⟩,
    letI : normalization_monoid M := unique_factorization_monoid.normalization_monoid,
    obtain ⟨p', hp', dvd'⟩ := wf_dvd_monoid.exists_irreducible_factor ha1 ha0,
    obtain ⟨p, mem, _⟩ := unique_factorization_monoid.exists_mem_normalized_factors_of_dvd ha0 hp' dvd',
    have := congr_arg (λ x, multiset.count p (unique_factorization_monoid.normalized_factors x)) hij,
    simp only [unique_factorization_monoid.normalized_factors_pow, multiset.count_nsmul] at this,
    exact mul_right_cancel₀ (multiset.count_ne_zero.mpr mem) this },
  { rintros rfl, refl }
end

lemma ideal.pow_succ_lt_pow [is_dedekind_domain S] {P : ideal S} [P_prime : P.is_prime]
  (hP : P ≠ ⊥) (i : ℕ) :
  P ^ (i + 1) < P ^ i :=
lt_of_le_of_ne (ideal.pow_le_pow (nat.le_succ _))
  (mt (unique_factorization_monoid.pow_eq_pow_iff hP
    (mt ideal.is_unit_iff.mp P_prime.ne_top)).mp
    i.succ_ne_self)

lemma ideal.mem_span_singleton_sup {S : Type*} [comm_semiring S] {x y : S} {I : ideal S} :
  x ∈ ideal.span {y} ⊔ I ↔ ∃ (a : S) (b ∈ I), y * a + b = x :=
begin
  rw mem_sup,
  split,
  { rintro ⟨ya, hya, b, hb, rfl⟩,
    obtain ⟨a, ha, rfl⟩ := ideal.mem_span_singleton.mp hya,
    exact ⟨a, b, hb, rfl⟩ },
  { rintro ⟨a, b, hb, rfl⟩,
    exact ⟨y * a, ideal.mem_span_singleton.mpr (dvd_mul_right _ _), b, hb, rfl⟩ }
end

open unique_factorization_monoid

lemma multiset.lt_repeat_succ {α : Type*} {m : multiset α} {x : α} {n : ℕ} :
  m < multiset.repeat x (n + 1) ↔ m ≤ multiset.repeat x n :=
begin
  rw multiset.lt_iff_cons_le,
  split,
  { rintros ⟨x', hx'⟩,
    have := multiset.eq_of_mem_repeat (multiset.mem_of_le hx' (multiset.mem_cons_self _ _)),
    rwa [this, multiset.repeat_succ, multiset.cons_le_cons_iff] at hx' },
  { intro h,
    rw multiset.repeat_succ,
    exact ⟨x, multiset.cons_le_cons _ h⟩ }
end

open unique_factorization_monoid

lemma exists_mem_factors {α : Type*} [decidable_eq α]
  [cancel_comm_monoid_with_zero α] [unique_factorization_monoid α]
  {x : α} (hx : x ≠ 0) (h : ¬ is_unit x) : ∃ p, p ∈ factors x :=
begin
  obtain ⟨p', hp', hp'x⟩ := wf_dvd_monoid.exists_irreducible_factor h hx,
  obtain ⟨p, hp, hpx⟩ := exists_mem_factors_of_dvd hx hp' hp'x,
  exact ⟨p, hp⟩
end

lemma exists_mem_normalized_factors {α : Type*} [decidable_eq α]
  [cancel_comm_monoid_with_zero α] [unique_factorization_monoid α] [normalization_monoid α]
  {x : α} (hx : x ≠ 0) (h : ¬ is_unit x) : ∃ p, p ∈ normalized_factors x :=
begin
  obtain ⟨p', hp', hp'x⟩ := wf_dvd_monoid.exists_irreducible_factor h hx,
  obtain ⟨p, hp, hpx⟩ := exists_mem_normalized_factors_of_dvd hx hp' hp'x,
  exact ⟨p, hp⟩
end

@[simp] lemma factors_pos {α : Type*} [decidable_eq α]
  [cancel_comm_monoid_with_zero α] [unique_factorization_monoid α]
  (x : α) (hx : x ≠ 0) : 0 < factors x ↔ ¬ is_unit x :=
begin
  split,
  { intros h hx,
    obtain ⟨p, hp⟩ := multiset.exists_mem_of_ne_zero h.ne',
    exact (prime_of_factor _ hp).not_unit (is_unit_of_dvd_unit (dvd_of_mem_factors hp) hx) },
  { intros h,
    obtain ⟨p, hp⟩ := exists_mem_factors hx h,
    exact bot_lt_iff_ne_bot.mpr (mt multiset.eq_zero_iff_forall_not_mem.mp
      (not_forall.mpr ⟨p, not_not.mpr hp⟩)) },
end

@[simp] lemma normalized_factors_pos {α : Type*} [decidable_eq α]
  [cancel_comm_monoid_with_zero α] [unique_factorization_monoid α] [normalization_monoid α]
  (x : α) (hx : x ≠ 0) : 0 < normalized_factors x ↔ ¬ is_unit x :=
begin
  split,
  { intros h hx,
    obtain ⟨p, hp⟩ := multiset.exists_mem_of_ne_zero h.ne',
    exact (prime_of_normalized_factor _ hp).not_unit (is_unit_of_dvd_unit (dvd_of_mem_normalized_factors hp) hx) },
  { intros h,
    obtain ⟨p, hp⟩ := exists_mem_normalized_factors hx h,
    exact bot_lt_iff_ne_bot.mpr (mt multiset.eq_zero_iff_forall_not_mem.mp
      (not_forall.mpr ⟨p, not_not.mpr hp⟩)) },
end

lemma dvd_not_unit_iff_factors_lt_factors {α : Type*} [decidable_eq α]
  [cancel_comm_monoid_with_zero α] [unique_factorization_monoid α] [normalization_monoid α]
  {x y : α} (hx : x ≠ 0) (hy : y ≠ 0) :
  dvd_not_unit x y ↔ normalized_factors x < normalized_factors y :=
begin
  split,
  { rintro ⟨_, c, hc, rfl⟩,
    simp only [hx, right_ne_zero_of_mul hy, normalized_factors_mul, ne.def, not_false_iff,
      lt_add_iff_pos_right, normalized_factors_pos, hc] },
  { intro h,
    exact dvd_not_unit_of_dvd_of_not_dvd
      ((dvd_iff_normalized_factors_le_normalized_factors hx hy).mpr h.le)
      (mt (dvd_iff_normalized_factors_le_normalized_factors hy hx).mp h.not_le) }
end


lemma ideal.eq_prime_pow_of_succ_lt_of_le [is_dedekind_domain S]
  {P I : ideal S} [P_prime : P.is_prime] (hP : P ≠ ⊥) {i : ℕ}
  (hlt : P ^ (i + 1) < I) (hle : I ≤ P ^ i) : I = P ^ i :=
begin
  refine le_antisymm hle _,
  letI := classical.dec_eq (ideal S),
  have P_prime' := ideal.prime_of_is_prime hP P_prime,
  have : I ≠ ⊥ := (lt_of_le_of_lt bot_le hlt).ne',
  have := pow_ne_zero i hP,
  have := pow_ne_zero (i + 1) hP,
  rw [← ideal.dvd_not_unit_iff_lt, dvd_not_unit_iff_factors_lt_factors, normalized_factors_pow,
      normalized_factors_irreducible P_prime'.irreducible, multiset.nsmul_singleton,
      multiset.lt_repeat_succ]
    at hlt,
  rw [← ideal.dvd_iff_le, dvd_iff_normalized_factors_le_normalized_factors, normalized_factors_pow,
      normalized_factors_irreducible P_prime'.irreducible, multiset.nsmul_singleton],
  all_goals { assumption }
end

/-- If `a ∈ P^i \ P^(i+1) c ∈ P^i`, then `a * d + e = c` for `e ∈ P^(i+1)`.
`ideal.mul_add_mem_pow_succ_unique` shows the choice of `d` is unique, up to `P`.
Inspired by [Neukirch], proposition 6.1 -/
lemma ideal.exists_mul_add_mem_pow_succ [is_dedekind_domain S]
  (P : ideal S) [P_prime : P.is_prime] (hP : P ≠ ⊥) {i : ℕ}
  (a c : S) (a_mem : a ∈ P ^ i) (a_not_mem : a ∉ P ^ (i + 1)) (c_mem : c ∈ P ^ i) :
  ∃ (d : S) (e ∈ P ^ (i + 1)), a * d + e = c :=
begin
  suffices eq_b : P ^ i = ideal.span {a} ⊔ P ^ (i + 1),
  { exact ideal.mem_span_singleton_sup.mp (eq_b ▸ c_mem) },
  refine (ideal.eq_prime_pow_of_succ_lt_of_le hP
    (lt_of_le_of_ne le_sup_right _)
    (sup_le (ideal.span_le.mpr (set.singleton_subset_iff.mpr a_mem))
      (ideal.pow_succ_lt_pow hP i).le)).symm,
  contrapose! a_not_mem with this,
  rw this,
  exact mem_sup.mpr ⟨a, mem_span_singleton_self a, 0, by simp, by simp⟩
end

lemma prime_pow_succ_dvd_mul {α : Type*} [cancel_comm_monoid_with_zero α]
  {p x y : α} (h : prime p) {i : ℕ} (hxy : p ^ (i + 1) ∣ x * y) :
  p ^ (i + 1) ∣ x ∨ p ∣ y :=
begin
  rw or_iff_not_imp_right,
  intro hy,
  induction i with i ih generalizing x,
  { simp only [zero_add, pow_one] at *,
    exact (h.dvd_or_dvd hxy).resolve_right hy },
  rw pow_succ at hxy ⊢,
  obtain ⟨x', rfl⟩ := (h.dvd_or_dvd (dvd_of_mul_right_dvd hxy)).resolve_right hy,
  rw mul_assoc at hxy,
  exact mul_dvd_mul_left p (ih ((mul_dvd_mul_iff_left h.ne_zero).mp hxy)),
end

lemma ideal.mem_prime_of_mul_mem_pow [is_dedekind_domain S]
  {P : ideal S} [P_prime : P.is_prime] (hP : P ≠ ⊥) {i : ℕ}
  {a b : S} (a_not_mem : a ∉ P ^ (i + 1))
  (ab_mem : a * b ∈ P ^ (i + 1)) : b ∈ P :=
begin
  simp only [← ideal.span_singleton_le_iff_mem, ← ideal.dvd_iff_le, pow_succ,
       ← ideal.span_singleton_mul_span_singleton] at a_not_mem ab_mem ⊢,
  exact (prime_pow_succ_dvd_mul (ideal.prime_of_is_prime hP P_prime) ab_mem).resolve_left a_not_mem
end

/-- The choice of `d` in `ideal.exists_mul_add_mem_pow_succ` is unique, up to `P`.
Inspired by [Neukirch], proposition 6.1 -/
lemma ideal.mul_add_mem_pow_succ_unique [is_dedekind_domain S]
  (P : ideal S) [P_prime : P.is_prime] (hP : P ≠ ⊥) {i : ℕ}
  (a d d' e e' : S) (a_not_mem : a ∉ P ^ (i + 1))
  (e_mem : e ∈ P ^ (i + 1)) (e'_mem : e' ∈ P ^ (i + 1))
  (h : (a * d + e) - (a * d' + e') ∈ P ^ (i + 1)) : d - d' ∈ P :=
begin
  have : e' - e ∈ P ^ (i + 1) := ideal.sub_mem _ e'_mem e_mem,
  have h' : a * (d - d') ∈ P ^ (i + 1),
  { convert ideal.add_mem _ h (ideal.sub_mem _ e'_mem e_mem),
    ring },
  exact ideal.mem_prime_of_mul_mem_pow hP a_not_mem h'
end

/-- If the `d` from `ideal.exists_mul_add_mem_pow_succ` is unique, up to `P`,
then so are the `c`s, up to `P ^ (i + 1)`.
Inspired by [Neukirch], proposition 6.1 -/
lemma ideal.mul_add_mem_pow_succ_inj
  (P : ideal S) {i : ℕ} (a d d' e e' : S) (a_mem : a ∈ P ^ i)
  (e_mem : e ∈ P ^ (i + 1)) (e'_mem : e' ∈ P ^ (i + 1))
  (h : d - d' ∈ P) : (a * d + e) - (a * d' + e') ∈ P ^ (i + 1) :=
begin
  have : a * d - a * d' ∈ P ^ (i + 1),
  { convert ideal.mul_mem_mul a_mem h; simp [mul_sub, pow_succ, mul_comm] },
  convert ideal.add_mem _ this (ideal.sub_mem _ e_mem e'_mem),
  ring,
end

set_option pp.proofs true

/-- Multiplicity of the ideal norm, for powers of prime ideals. -/
lemma card_quot_pow_of_prime [is_dedekind_domain S] [module.finite ℤ S] [module.free ℤ S]
  (P : ideal S) [P_prime : P.is_prime] (hP : P ≠ ⊥) {i : ℕ} :
  card_quot (P ^ i) = card_quot P ^ i :=
begin
  let b := module.free.choose_basis ℤ S,
  letI := classical.dec_eq (module.free.choose_basis_index ℤ S),
  induction i with i ih,
  { simp },
  letI := ideal.fintype_quotient_of_free_of_ne_bot (P ^ i.succ) b (pow_ne_zero _ hP),
  letI := ideal.fintype_quotient_of_free_of_ne_bot (P ^ i) b (pow_ne_zero _ hP),
  letI := ideal.fintype_quotient_of_free_of_ne_bot P b hP,
  have : P ^ (i + 1) < P ^ i := ideal.pow_succ_lt_pow hP i,
  suffices hquot : map (P ^ i.succ).mkq (P ^ i) ≃ S ⧸ P,
  { rw [pow_succ (card_quot P), ← ih, card_quot_apply (P ^ i.succ),
      ← card_quotient_mul_card_quotient (P ^ i) (P ^ i.succ) this.le,
      card_quot_apply (P ^ i), card_quot_apply P],
    congr' 1,
    rw fintype.card_eq,
    exact ⟨hquot⟩ },
  choose a a_mem a_not_mem using set_like.exists_of_lt this,
  -- TODO: can we do this with less repetition?
  refine equiv.of_bijective (λ c', quotient.mk' _) ⟨_, _⟩,
  { cases c' with c' hc',
    choose c hc eq_c' using submodule.mem_map.mp hc',
    exact (ideal.exists_mul_add_mem_pow_succ P hP a c a_mem a_not_mem hc).some },
  { intros c₁' c₂' h,
    cases c₁' with c₁' hc₁',
    cases c₂' with c₂' hc₂',
    rw subtype.mk_eq_mk,
    replace h := (submodule.quotient.eq _).mp h,
    simp only [mkq_apply, ideal.quotient.mk_eq_mk, mem_map] at h,
    obtain ⟨hc₁, eq_c₁'⟩ := classical.some_spec (submodule.mem_map.mp hc₁'),
    obtain ⟨hc₂, eq_c₂'⟩ := classical.some_spec (submodule.mem_map.mp hc₂'),
    intro h,
    rw [← eq_c₁', ← eq_c₂', mkq_apply, mkq_apply, submodule.quotient.eq],
    obtain ⟨he₁, hd₁⟩ := (ideal.exists_mul_add_mem_pow_succ P hP a _ a_mem a_not_mem hc₁).some_spec.some_spec,
    obtain ⟨he₂, hd₂⟩ := (ideal.exists_mul_add_mem_pow_succ P hP a _ a_mem a_not_mem hc₂).some_spec.some_spec,
    rw [← hd₁, ← hd₂],
    exact ideal.mul_add_mem_pow_succ_inj P a _ _ _ _ a_mem he₁ he₂ h },
  { intros d',
    refine quotient.induction_on' d' (λ d, _),
    have hc' := ideal.mul_mem_right d _ a_mem,
    have hd' := mem_map.mpr ⟨a * d, hc', rfl⟩,
    refine ⟨⟨_, hd'⟩, _⟩,
    simp only [submodule.quotient.mk'_eq_mk, ideal.quotient.mk_eq_mk, ideal.quotient.eq],
    obtain ⟨he, hd''⟩ := (ideal.exists_mul_add_mem_pow_succ P hP a _ a_mem a_not_mem hc').some_spec.some_spec,
    refine ideal.mul_add_mem_pow_succ_unique P hP a _ _ 0 _ a_not_mem _ he _,
    { exact (P ^ (i + 1)).zero_mem },
    convert submodule.neg_mem _ (ideal.add_mem _ he he), -- Come on, Lean!
    rw add_zero,
    conv_lhs { congr, skip, congr, rw ← hd'' },
    rw [eq_neg_iff_add_eq_zero, add_assoc, ← sub_sub, sub_add_cancel],
    convert sub_self _, -- At some point we used `a * d` as a witness for an existential, so now we need to show the choice of witness doesn't matter.
    have sub_mem := (submodule.quotient.eq _).mp (classical.some_spec (mem_map.mp hd')).2,
    ext x,
    split; rintro ⟨e, he, eq⟩,
    { refine ⟨_, submodule.add_mem _ he sub_mem, _⟩,
      rw [← add_assoc, eq], ring },
    { refine ⟨_, submodule.sub_mem _ he sub_mem, _⟩,
      rw [← add_sub_assoc, eq], ring } }
end

/-- If `P` holds units and powers of primes,
and `P x ∧ P y` for coprime `x, y` implies `P (x * y)`,
then `P` holds on a product of prime powers. -/
@[elab_as_eliminator]
theorem unique_factorization_monoid.induction_on_prime_power {α : Type*}
  [cancel_comm_monoid_with_zero α] [unique_factorization_monoid α]
  {P : α → Prop} (s : finset α) (i : α → ℕ)
  (is_prime : ∀ p ∈ s, prime p) (is_coprime : ∀ p q ∈ s, p ∣ q → p = q)
  (h1 : ∀ {x}, is_unit x → P x) (hpr : ∀ {p} (i : ℕ), prime p → P (p ^ i))
  (hcp : ∀ {x y}, (∀ p, p ∣ x → p ∣ y → is_unit p) → P x → P y → P (x * y)) :
  P (∏ p in s, p ^ (i p)) :=
begin
  letI := classical.dec_eq α,
  induction s using finset.induction_on with p f' hpf' ih,
  { simpa using h1 is_unit_one },
  rw finset.prod_insert hpf',
  have hp := is_prime _ (finset.mem_insert_self _ _),
  refine hcp _ (hpr (i p) hp) (ih (λ q hq, is_prime _ (finset.mem_insert_of_mem hq))
    (λ q hq q' hq', is_coprime _ (finset.mem_insert_of_mem hq) _ (finset.mem_insert_of_mem hq'))),
  refine λ _, no_factors_of_no_prime_factors (pow_ne_zero _ hp.ne_zero) _,
  intros d hdp hdprod hd,
  apply hpf',
  replace hdp := hd.dvd_of_dvd_pow hdp,
  obtain ⟨q, q_mem', hdq⟩ := hd.exists_mem_multiset_dvd hdprod,
  obtain ⟨q, q_mem, rfl⟩ := multiset.mem_map.mp q_mem',
  replace hdq := hd.dvd_of_dvd_pow hdq,
  have : p ∣ q := dvd_trans
    (hd.irreducible.dvd_symm hp.irreducible hdp)
    hdq,
  convert q_mem,
  exact is_coprime _  (finset.mem_insert_self p f') _ (finset.mem_insert_of_mem q_mem) this,
end

/-- If `P` holds for `0`, units and powers of primes,
and `P x ∧ P y` for coprime `x, y` implies `P (x * y)`,
then `P` holds on all `a : α`. -/
@[elab_as_eliminator]
theorem unique_factorization_monoid.induction_on_coprime {α : Type*}
  [cancel_comm_monoid_with_zero α] [unique_factorization_monoid α]
  {P : α → Prop} (a : α) (h0 : P 0) (h1 : ∀ {x}, is_unit x → P x)
  (hpr : ∀ {p} (i : ℕ), prime p → P (p ^ i))
  (hcp : ∀ {x y}, (∀ p, p ∣ x → p ∣ y → is_unit p) → P x → P y → P (x * y)) :
  P a :=
begin
  letI := classical.dec_eq α,
  have P_of_associated : ∀ {x y}, associated x y → P x → P y,
  { rintros x y ⟨u, rfl⟩ hx,
    exact hcp (λ p _ hpx, is_unit_of_dvd_unit hpx u.is_unit) hx (h1 u.is_unit) },
  by_cases ha0 : a = 0, { rwa ha0 },
  haveI : nontrivial α := ⟨⟨_, _, ha0⟩⟩,
  letI : normalization_monoid α := unique_factorization_monoid.normalization_monoid,
  refine P_of_associated (normalized_factors_prod ha0) _,
  rw [← (normalized_factors a).map_id, finset.prod_multiset_map_count],
  refine unique_factorization_monoid.induction_on_prime_power _ _ _ _ @h1 @hpr @hcp;
    simp only [multiset.mem_to_finset],
  { apply prime_of_normalized_factor },
  rintro p hp q hq hdvd,
  convert normalize_eq_normalize hdvd
    (((prime_of_normalized_factor _ hp).irreducible).dvd_symm
      ((prime_of_normalized_factor _ hq).irreducible) hdvd);
    apply (normalize_normalized_factor _ _).symm; assumption
end

/-- If `f` maps `p ^ i` to `(f p) ^ i` for primes `p`, and `f`
is multiplicative on coprime elements, then `f` is multiplicative on all products of primes. -/
@[elab_as_eliminator]
theorem unique_factorization_monoid.multiplicative_prime_power {α β : Type*}
  [cancel_comm_monoid_with_zero α] [unique_factorization_monoid α] [cancel_comm_monoid_with_zero β]
  {f : α → β} (s : finset α) (i j : α → ℕ)
  (is_prime : ∀ p ∈ s, prime p) (is_coprime : ∀ p q ∈ s, p ∣ q → p = q)
  (h1 : ∀ {x y}, is_unit y → f (x * y) = f x * f y)
  (hpr : ∀ {p} (i : ℕ), prime p → f (p ^ i) = (f p) ^ i)
  (hcp : ∀ {x y}, (∀ p, p ∣ x → p ∣ y → is_unit p) → f (x * y) = f x * f y) :
  f (∏ p in s, p ^ (i p + j p)) = f (∏ p in s, p ^ i p) * f (∏ p in s, p ^ j p) :=
begin
  letI := classical.dec_eq α,
  induction s using finset.induction_on with p f' hpf' ih,
  { simpa using h1 is_unit_one },
  simp only [finset.prod_insert hpf'],
  have hp := is_prime _ (finset.mem_insert_self _ _),
  suffices red : ∀ (i' : α → ℕ) (q : α), q ∣ p ^ i' p → q ∣ ∏ q' in f', q' ^ i' q' → is_unit q,
  { rw [hcp (red _), hpr (i p + j p) hp, hcp (red _), hpr (i p) hp, hcp (red _), hpr (j p) hp,
        ih (λ q hq, is_prime _ (finset.mem_insert_of_mem hq))
          (λ q hq q' hq', is_coprime _ (finset.mem_insert_of_mem hq) _ (finset.mem_insert_of_mem hq')),
        pow_add, mul_assoc, mul_left_comm (f p ^ j p), mul_assoc] },
  -- TODO: unify this and the analogous argument for `induction_on_coprime`
  refine λ i' _, no_factors_of_no_prime_factors (pow_ne_zero _ hp.ne_zero) _,
  intros d hdp hdprod hd,
  apply hpf',
  replace hdp := hd.dvd_of_dvd_pow hdp,
  obtain ⟨q, q_mem', hdq⟩ := hd.exists_mem_multiset_dvd hdprod,
  obtain ⟨q, q_mem, rfl⟩ := multiset.mem_map.mp q_mem',
  replace hdq := hd.dvd_of_dvd_pow hdq,
  have : p ∣ q := (hd.irreducible.dvd_symm hp.irreducible hdp).trans hdq,
  convert q_mem,
  exact is_coprime _ (finset.mem_insert_self p f') _ (finset.mem_insert_of_mem q_mem) this,
end

/-- If `f` maps `p ^ i` to `(f p) ^ i` for primes `p`, and `f`
is multiplicative on coprime elements, then `f` is multiplicative everywhere. -/
theorem unique_factorization_monoid.multiplicative_of_coprime {α β : Type*}
  [cancel_comm_monoid_with_zero α] [unique_factorization_monoid α] [cancel_comm_monoid_with_zero β]
  (f : α → β) (a b : α) (h0 : f 0 = 0) (h1 : ∀ {x y}, is_unit y → f (x * y) = f x * f y)
  (hpr : ∀ {p} (i : ℕ), prime p → f (p ^ i) = (f p) ^ i)
  (hcp : ∀ {x y}, (∀ p, p ∣ x → p ∣ y → is_unit p) → f (x * y) = f x * f y) :
  f (a * b) = f a * f b :=
begin
  by_cases ha0 : a = 0, { rw [ha0, zero_mul, h0, zero_mul] },
  by_cases hb0 : b = 0, { rw [hb0, mul_zero, h0, mul_zero] },
  by_cases hf1 : f 1 = 0,
  { calc f (a * b) = f ((a * b) * 1) : by rw mul_one
               ... = 0 : by simp only [h1 is_unit_one, hf1, mul_zero]
               ... = f a * f (b * 1) : by simp only [h1 is_unit_one, hf1, mul_zero]
               ... = f a * f b : by rw mul_one },
  have h1' : f 1 = 1 := (mul_left_inj' hf1).mp (by rw [← h1 is_unit_one, one_mul, one_mul]),
  letI := classical.dec_eq α,
  haveI : nontrivial α := ⟨⟨_, _, ha0⟩⟩,
  letI : normalization_monoid α := unique_factorization_monoid.normalization_monoid,
  obtain ⟨ua, a_eq⟩ := normalized_factors_prod ha0,
  obtain ⟨ub, b_eq⟩ := normalized_factors_prod hb0,
  rw [← a_eq, ← b_eq, mul_right_comm _ ↑ua, h1 ua.is_unit, h1 ub.is_unit, h1 ua.is_unit,
      ← mul_assoc, h1 ub.is_unit, mul_right_comm _ (f ua), ← mul_assoc],
  congr,
  rw [← (normalized_factors a).map_id, ← (normalized_factors b).map_id,
      finset.prod_multiset_map_count, finset.prod_multiset_map_count,
      finset.prod_subset (finset.subset_union_left _ (normalized_factors b).to_finset),
      finset.prod_subset (finset.subset_union_right (normalized_factors a).to_finset (normalized_factors b).to_finset),
      ← finset.prod_mul_distrib],
  simp_rw [id.def, ← pow_add],
  refine unique_factorization_monoid.multiplicative_prime_power _ _ _ _ _ @h1 @hpr @hcp,
  all_goals { simp only [multiset.mem_to_finset, finset.mem_union] },
  { rintros p (hpa | hpb); apply prime_of_normalized_factor; assumption },
  { rintro p (hp | hp) q (hq | hq) hdvd;
      rw [← normalize_normalized_factor _ hp, ← normalize_normalized_factor _ hq];
      exact normalize_eq_normalize hdvd
        ((prime_of_normalized_factor _ hp).irreducible.dvd_symm
          (prime_of_normalized_factor _ hq).irreducible
          hdvd) },
  { intros p hpab hpb,
    simp [hpb] },
  { intros p hpab hpa,
    simp [hpa] }
end

/-- Multiplicativity of the ideal norm in number rings. -/
theorem card_quot_mul [is_dedekind_domain S] [module.free ℤ S] [module.finite ℤ S] (I J : ideal S) :
  card_quot (I * J) = card_quot I * card_quot J :=
begin
  let b := module.free.choose_basis ℤ S,
  casesI is_empty_or_nonempty (module.free.choose_basis_index ℤ S),
  { haveI : subsingleton S := function.surjective.subsingleton b.repr.to_equiv.symm.surjective,
    nontriviality S,
    exfalso,
    exact not_nontrivial_iff_subsingleton.mpr ‹subsingleton S› ‹nontrivial S›, },
  haveI : infinite S := infinite.of_surjective _ b.repr.to_equiv.surjective,
  exact unique_factorization_monoid.multiplicative_of_coprime card_quot I J
    card_quot_bot
    (λ I J hI, by simp [ideal.is_unit_iff.mp hI, ideal.mul_top])
    (λ I i hI, have ideal.is_prime I := ideal.is_prime_of_prime hI,
              by exactI card_quot_pow_of_prime _ hI.ne_zero)
    (λ I J hIJ, card_quot_mul_of_coprime I J (ideal.is_unit_iff.mp (hIJ _
      (ideal.dvd_iff_le.mpr le_sup_left)
      (ideal.dvd_iff_le.mpr le_sup_right))))
end

/-- The absolute norm of the ideal `I : ideal R` is the cardinality of the quotient `R ⧸ I`. -/
noncomputable def ideal.abs_norm [infinite S] [is_dedekind_domain S]
  [module.free ℤ S] [module.finite ℤ S] :
  ideal S →*₀ ℕ :=
{ to_fun := submodule.card_quot,
  map_mul' := λ I J, by rw card_quot_mul,
  map_one' := by rw [ideal.one_eq_top, card_quot_top],
  map_zero' := by rw [ideal.zero_eq_bot, card_quot_bot] }
end
