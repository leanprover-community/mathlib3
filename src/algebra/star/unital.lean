import algebra.star.non_unital_subalgebra
import algebra.star.subalgebra
import algebra.algebra.unitization

.

/-!
# Relating unital and non-unital substructures

This file takes unital and non-unital structures and relates them.

## Main declarations

* `non_unital_subalgebra.unitization s : unitization R s →ₐ[R] algebra.adjoin R (s : set A)`:
  where `s` is a non-unital subalgebra of a unital `R`-algebra `A`, this is the natural algebra
  homomorphism sending `(r, a)` to `r • 1 + a`. This is always surjective.#check
* `non_unital_subalgebra.unitization_equiv s : unitization R s ≃ₐ[R] algebra.adjoin R (s : set A)`:
  when `R` is a field and `1 ∉ s`, the above homomorphism is injective is upgraded to
  an `alg_equiv`.
* `subsemiring.closure_equiv_adjoin_nat : subsemiring.closure s ≃ₐ[ℕ] algebra.adjoin ℕ s`: the
  identity map between these subsemirings, viewed as `ℕ`-algebras.
* `subring.closure_equiv_adjoin_int : subring.closure s ≃ₐ[ℤ] algebra.adjoin ℤ s`: the
  identity map between these subsemirings, viewed as `ℤ`-algebras.
* `non_unital_subsemiring.unitization : unitization ℕ S →ₐ[ℕ] subsemiring.closure (S : set R)`:
  the natural `ℕ`-algebra homomorphism between the unitization of a non-unital subsemiring `S` and
  its `subsemiring.closure`. This is just `non_unital_subalgebra.unitization S` where we replace the
  codomain using `subsemiring.closure_equiv_adjoint_nat`
* `non_unital_subring.unitization : unitization ℤ S →ₐ[ℤ] subring.closure (S : set R)`:
  the natural `ℤ`-algebra homomorphism between the unitization of a non-unital subring `S` and
  its `subring.closure`. This is just `non_unital_subalgebra.unitization S` where we replace the
  codomain using `subring.closure_equiv_adjoint_int`

-/

section generic

variables {R S A : Type*} [comm_semiring R] [semiring A] [algebra R A] [set_like S A]
  [hSA : non_unital_subsemiring_class S A] [hSRA : smul_mem_class S R A] (s : S)
include hSA hSRA

instance non_unital_subalgebra_class.is_scalar_tower : is_scalar_tower R s s :=
{ smul_assoc := λ r x y, subtype.ext $ smul_assoc r (x : A) (y : A) }

instance non_unital_subalgebra_class.smul_comm_class : smul_comm_class R s s :=
{ smul_comm := λ r x y, subtype.ext $ smul_comm r (x : A) (y : A) }

/-- The natural `R`-algebra homomorphism from the unitization of a non-unital subalgebra to
its `algebra.adjoin`. -/
def non_unital_subalgebra.unitization : unitization R s →ₐ[R] algebra.adjoin R (s : set A) :=
unitization.lift
{ to_fun := λ x : s, (⟨x, algebra.subset_adjoin x.prop⟩ : algebra.adjoin R (s : set A)),
  map_smul' := λ (_ : R) _, rfl,
  map_zero' := rfl,
  map_add' := λ _ _, rfl,
  map_mul' := λ _ _, rfl }

@[simp]
lemma non_unital_subalgebra.unitization_apply_coe (x : unitization R s) :
  (non_unital_subalgebra.unitization s x : A) =
    algebra_map R (algebra.adjoin R (s : set A)) x.fst + x.snd :=
rfl

lemma non_unital_subalgebra.unitization_surjective :
  function.surjective (non_unital_subalgebra.unitization s) :=
begin
  refine algebra.adjoin_induction' _ _ _ _,
  { refine λ x hx, ⟨(0, ⟨x, hx⟩), subtype.ext _⟩,
    simp only [non_unital_subalgebra.unitization_apply_coe, subtype.coe_mk],
    change (algebra_map R {x // x ∈ algebra.adjoin R (s : set A)} 0 : A) + x = x,
    rw [map_zero, subsemiring.coe_zero, zero_add], },
  { exact λ r, ⟨algebra_map R (unitization R s) r, alg_hom.commutes _ r⟩, },
  { rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩,
    exact ⟨x + y, map_add _ _ _⟩, },
  { rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩,
    exact ⟨x * y, map_mul _ _ _⟩, },
end

lemma non_unital_subalgebra.unitization_injective {R S A : Type*} [field R] [ring A]
  [algebra R A] [set_like S A] [hSA : non_unital_subring_class S A]
  [hSRA : smul_mem_class S R A] (s : S) (h1 : (1 : A) ∉ s) :
  function.injective (non_unital_subalgebra.unitization s) :=
begin
  rw [ring_hom.injective_iff_ker_eq_bot, ring_hom.ker_eq_bot_iff_eq_zero],
  refine λ x hx, _,
  induction x using unitization.ind with r a,
  rw [map_add] at hx,
  have hx' := congr_arg (coe : _ → A) hx,
  simp only [non_unital_subalgebra.unitization_apply_coe, unitization.fst_inl,
    subalgebra.coe_algebra_map, unitization.snd_inl, zero_mem_class.coe_zero, add_zero, map_neg,
    add_subgroup_class.coe_neg, unitization.fst_coe, map_zero, unitization.snd_coe,
    subalgebra.coe_add, zero_add] at hx',
  by_cases hr : r = 0,
  { simp only [hr, map_zero, unitization.inl_zero, zero_add] at hx' ⊢,
    rw [←zero_mem_class.coe_zero s] at hx',
    exact congr_arg _ (subtype.coe_injective hx') },
  { refine false.elim (h1 _),
    rw [←eq_sub_iff_add_eq, zero_sub] at hx',
    replace hx' := congr_arg (λ y, r⁻¹ • y) hx',
    simp only [algebra.algebra_map_eq_smul_one, ←smul_assoc, smul_eq_mul, inv_mul_cancel hr,
      one_smul] at hx',
    exact hx'.symm ▸ smul_mem_class.smul_mem r⁻¹ (neg_mem a.prop) }
end

/-- If a `non_unital_subalgebra` over a field does not contain `1`, then its unitization is
isomorphic to its `algebra.adjoin`. -/
noncomputable def non_unital_subalgebra.unitization_alg_equiv {R S A : Type*} [field R] [ring A]
  [algebra R A] [set_like S A] [hSA : non_unital_subring_class S A]
  [hSRA : smul_mem_class S R A] (s : S) (h1 : (1 : A) ∉ s) :
  unitization R s ≃ₐ[R] algebra.adjoin R (s : set A) :=
alg_equiv.of_bijective (non_unital_subalgebra.unitization s)
  ⟨non_unital_subalgebra.unitization_injective s h1, non_unital_subalgebra.unitization_surjective s⟩

end generic

section subsemiring

variables {R : Type*} [non_assoc_semiring R]

/-! ## Subsemirings -/

/-- Turn a `subsemiring` into a `non_unital_subsemiring` by forgetting that it contains `1`. -/
def subsemiring.to_non_unital_subsemiring (S : subsemiring R) :
  non_unital_subsemiring R :=
{ carrier := S.carrier,
  .. S }

lemma subsemiring.one_mem_to_non_unital_subsemiring (S : subsemiring R) :
  (1 : R) ∈ S.to_non_unital_subsemiring :=
S.one_mem

/-- Turn a non-unital subsemiring containing `1` into a subsemiring. -/
def non_unital_subsemiring.to_subsemiring (S : non_unital_subsemiring R)
  (h1 : (1 : R) ∈ S) :
  subsemiring R :=
{ carrier := S.carrier,
  one_mem' := h1,
  .. S }

lemma subsemiring.to_non_unital_subsemiring_to_subsemiring (S : subsemiring R) :
  S.to_non_unital_subsemiring.to_subsemiring S.one_mem = S :=
subsemiring.cases_on S (λ _ _ _ _ _, rfl)

lemma non_unital_subsemiring.to_subsemiring_to_non_unital_subsemiring
  (S : non_unital_subsemiring R) (h1 : (1 : R) ∈ S) :
  (non_unital_subsemiring.to_subsemiring S h1).to_non_unital_subsemiring = S :=
by {cases S, refl}

/-- The `ℕ`-algebra equivalence between `subsemiring.closure s` and `algebra.adjoin ℕ s` given
by the identity map. -/
def subsemiring.closure_equiv_adjoin_nat {R : Type*} [semiring R] (s : set R) :
  subsemiring.closure s ≃ₐ[ℕ] algebra.adjoin ℕ s :=
{ to_fun := subtype.map id $ λ r hr, subsemiring.closure_induction hr algebra.subset_adjoin
    (zero_mem _) (one_mem _) (λ _ _, add_mem) (λ _ _, mul_mem),
  inv_fun := subtype.map id $ λ r hr, algebra.adjoin_induction hr subsemiring.subset_closure
    (nat_cast_mem _) (λ _ _, add_mem) (λ _ _, mul_mem),
  left_inv := λ _, subtype.ext rfl,
  right_inv := λ _, subtype.ext rfl,
  map_mul' := λ _ _, subtype.ext rfl,
  map_add' := λ _ _, subtype.ext rfl,
  commutes' := λ _, subtype.ext rfl }

/-- The natural `ℕ`-algebra homomorphism from the unitization of a non-unital subsemiring to
its `subsemiring.closure`. -/
def non_unital_subsemiring.unitization {R : Type*} [semiring R] (S : non_unital_subsemiring R) :
  unitization ℕ S →ₐ[ℕ] subsemiring.closure (S : set R) :=
alg_equiv.refl.arrow_congr (subsemiring.closure_equiv_adjoin_nat (S : set R)).symm
  $ non_unital_subalgebra.unitization S

@[simp]
lemma non_unital_subsemiring.unitization_apply_coe {R : Type*} [semiring R]
  (S : non_unital_subsemiring R) (x : unitization ℕ S) :
  (S.unitization x : R) = algebra_map ℕ (subsemiring.closure (S : set R)) x.fst + x.snd :=
rfl

lemma non_unital_subsemiring.unitization_surjective {R : Type*} [semiring R]
  (S : non_unital_subsemiring R) : function.surjective S.unitization :=
begin
  intro x,
  refine subsemiring.closure_induction' x _ ⟨0, map_zero _⟩ ⟨1, map_one _⟩ _ _,
  { refine λ x hx, ⟨(0, ⟨x, hx⟩), subtype.ext _⟩,
    simp only [non_unital_subsemiring.unitization_apply_coe, subtype.coe_mk,
      unitization.fst, unitization.snd, map_zero, subsemiring.coe_zero, zero_add] },
  { rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩,
    exact ⟨x + y, map_add _ _ _⟩, },
  { rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩,
    exact ⟨x * y, map_mul _ _ _⟩, },
end

end subsemiring

section subring

variables {R : Type*} [ring R]

/-! ## Subrings -/

/-- Turn a `subring` into a `non_unital_subring` by forgetting that it contains `1`. -/
def subring.to_non_unital_subring (S : subring R) :
  non_unital_subring R :=
{ carrier := S.carrier,
  .. S }

lemma subring.one_mem_to_non_unital_subring (S : subring R) :
  (1 : R) ∈ S.to_non_unital_subring :=
S.one_mem

/-- Turn a non-unital subring containing `1` into a subring. -/
def non_unital_subring.to_subring (S : non_unital_subring R)
  (h1 : (1 : R) ∈ S) :
  subring R :=
{ carrier := S.carrier,
  one_mem' := h1,
  .. S }

lemma subring.to_non_unital_subring_to_subring (S : subring R) :
  S.to_non_unital_subring.to_subring S.one_mem = S :=
subring.cases_on S (λ _ _ _ _ _ _, rfl)

lemma non_unital_subring.to_subring_to_non_unital_subring
  (S : non_unital_subring R) (h1 : (1 : R) ∈ S) :
  (non_unital_subring.to_subring S h1).to_non_unital_subring = S :=
by {cases S, refl}

-- why don't we have this theorem?
theorem int_cast_mem {S : Type*} {R : Type*} [add_group_with_one R] [set_like S R] (s : S)
  [add_submonoid_with_one_class S R] [neg_mem_class S R] (n : ℤ) : (n : R) ∈ s :=
begin
  cases n,
  simpa only [int.cast_coe_nat, int.of_nat_eq_coe] using nat_cast_mem s n,
  simpa only [int.cast_neg_succ_of_nat] using neg_mem (nat_cast_mem s (n + 1)),
end

/-- The `ℤ`-algebra equivalence between `subring.closure s` and `algebra.adjoin ℤ s` given by
the identity map. -/
def subring.closure_equiv_adjoin_int (s : set R) :
  subring.closure s ≃ₐ[ℤ] algebra.adjoin ℤ s :=
{ to_fun := subtype.map id $ λ r hr, subring.closure_induction hr algebra.subset_adjoin
    (zero_mem _) (one_mem _) (λ _ _, add_mem) (λ _, neg_mem) (λ _ _, mul_mem),
  inv_fun := subtype.map id $ λ r hr, algebra.adjoin_induction hr subring.subset_closure
    (int_cast_mem _) (λ _ _, add_mem) (λ _ _, mul_mem),
  left_inv := λ _, subtype.ext rfl,
  right_inv := λ _, subtype.ext rfl,
  map_mul' := λ _ _, subtype.ext rfl,
  map_add' := λ _ _, subtype.ext rfl,
  commutes' := λ _, subtype.ext rfl }

/-- The natural `ℤ`-algebra homomorphism from the unitization of a non-unital subring to
its `subring.closure`. -/
def non_unital_subring.unitization
  (S : non_unital_subring R) : -- (h : ∀ n : ℕ, (n : R) ∉ S) :
  unitization ℤ S →ₐ[ℤ] subring.closure (S : set R) :=
alg_equiv.refl.arrow_congr (subring.closure_equiv_adjoin_int (S : set R)).symm
  $ non_unital_subalgebra.unitization S

@[simp]
lemma non_unital_subring.unitization_apply_coe
  (S : non_unital_subring R) (x : unitization ℤ S) :
  (S.unitization x : R) = algebra_map ℤ (subring.closure (S : set R)) x.fst + x.snd :=
rfl

lemma non_unital_subring.unitization_surjective
  (S : non_unital_subring R) : function.surjective S.unitization :=
begin
  intro x,
  refine subring.closure_induction' x _ ⟨0, map_zero _⟩ ⟨1, map_one _⟩ _ _ _,
  { refine λ x hx, ⟨(0, ⟨x, hx⟩), subtype.ext _⟩,
    simp only [non_unital_subring.unitization_apply_coe, subtype.coe_mk,
      unitization.fst, unitization.snd, map_zero, subring.coe_zero, zero_add], },
  { rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩,
    exact ⟨x + y, map_add _ _ _⟩, },
  { rintro _ ⟨x, rfl⟩,
    exact ⟨-x, map_neg _ _⟩, },
  { rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩,
    exact ⟨x * y, map_mul _ _ _⟩, },
end

end subring

section subalgebra

variables {R A : Type*} [comm_semiring R] [semiring A] [algebra R A]

/-! ## Subalgebras -/

/-- Turn a `subalgebra` into a `non_unital_subalgebra` by forgetting that it contains `1`. -/
def subalgebra.to_non_unital_subalgebra (S : subalgebra R A) :
  non_unital_subalgebra R A :=
{ carrier := S.carrier,
  smul_mem' := λ r x hx, S.smul_mem hx r,
  .. S }

lemma subalgebra.one_mem_to_non_unital_subalgebra (S : subalgebra R A) :
  (1 : A) ∈ S.to_non_unital_subalgebra :=
S.one_mem

/-- Turn a non-unital subalgebra containing `1` into a subalgebra. -/
def non_unital_subalgebra.to_subalgebra (S : non_unital_subalgebra R A)
  (h1 : (1 : A) ∈ S) :
  subalgebra R A :=
{ carrier := S.carrier,
  one_mem' := h1,
  algebra_map_mem' := λ r, (@algebra.algebra_map_eq_smul_one R A _ _ _ r).symm ▸ S.smul_mem h1 r,
  .. S }

lemma subalgebra.to_non_unital_subalgebra_to_subalgebra (S : subalgebra R A) :
  S.to_non_unital_subalgebra.to_subalgebra S.one_mem = S :=
subalgebra.cases_on S (λ _ _ _ _ _ _, rfl)

lemma non_unital_subalgebra.to_subalgebra_to_non_unital_subalgebra
  (S : non_unital_subalgebra R A) (h1 : (1 : A) ∈ S) :
  (non_unital_subalgebra.to_subalgebra S h1).to_non_unital_subalgebra = S :=
by {cases S, refl}

end subalgebra

section star_subalgebra

variables {R A : Type*} [comm_semiring R] [star_ring R] [semiring A] [star_ring A]
variables [algebra R A] [star_module R A]

/-! ## star_subalgebras -/

/-- Turn a `star_subalgebra` into a `non_unital_star_subalgebra` by forgetting that it contains `1`. -/
def star_subalgebra.to_non_unital_star_subalgebra (S : star_subalgebra R A) :
  non_unital_star_subalgebra R A :=
{ carrier := S.carrier,
  smul_mem' := λ r x hx, S.smul_mem hx r,
  .. S }

lemma star_subalgebra.one_mem_to_non_unital_star_subalgebra (S : star_subalgebra R A) :
  (1 : A) ∈ S.to_non_unital_star_subalgebra :=
S.one_mem'

/-- Turn a non-unital star_subalgebra containing `1` into a star_subalgebra. -/
def non_unital_star_subalgebra.to_star_subalgebra (S : non_unital_star_subalgebra R A)
  (h1 : (1 : A) ∈ S) :
  star_subalgebra R A :=
{ carrier := S.carrier,
  one_mem' := h1,
  algebra_map_mem' := λ r, (@algebra.algebra_map_eq_smul_one R A _ _ _ r).symm ▸ S.smul_mem h1 r,
  .. S }

lemma star_subalgebra.to_non_unital_star_subalgebra_to_star_subalgebra (S : star_subalgebra R A) :
  S.to_non_unital_star_subalgebra.to_star_subalgebra S.one_mem' = S :=
star_subalgebra.cases_on S (λ _ _ _ _ _ _ _, rfl)

lemma non_unital_star_subalgebra.to_star_subalgebra_to_non_unital_star_subalgebra
  (S : non_unital_star_subalgebra R A) (h1 : (1 : A) ∈ S) :
  (non_unital_star_subalgebra.to_star_subalgebra S h1).to_non_unital_star_subalgebra = S :=
by {cases S, refl}

/-- The natural `R`-algebra homomorphism from the unitization of a non-unital star_subalgebra to
its `algebra.adjoin`. -/
def non_unital_star_subalgebra.unitization (S : non_unital_star_subalgebra R A) :
  unitization R S →⋆ₐ[R] star_subalgebra.adjoin R (S : set A) :=
unitization.star_lift
{ to_fun := λ x : S, (⟨x, star_subalgebra.subset_adjoin R _ x.prop⟩ : star_subalgebra.adjoin R (S : set A)),
  map_smul' := λ (_ : R) _, rfl,
  map_zero' := rfl,
  map_add' := λ _ _, rfl,
  map_mul' := λ _ _, rfl,
  map_star' := λ _, rfl }

@[simp]
lemma non_unital_star_subalgebra.unitization_apply_coe (S : non_unital_star_subalgebra R A)
  (x : unitization R S) :
  (S.unitization x : A) = algebra_map R (star_subalgebra.adjoin R (S : set A)) x.fst + x.snd :=
rfl

lemma non_unital_star_subalgebra.unitization_surjective (S : non_unital_star_subalgebra R A) :
  function.surjective S.unitization :=
begin
  refine λ x, star_subalgebra.adjoin_induction' x _ _ _ _ _,
  { refine λ x hx, ⟨(0, ⟨x, hx⟩), subtype.ext _⟩,
    simp only [non_unital_subalgebra.unitization_apply_coe, subtype.coe_mk],
    change (algebra_map R {x // x ∈ algebra.adjoin R (S : set A)} 0 : A) + x = x,
    rw [map_zero, subsemiring.coe_zero, zero_add], },
  { exact λ r, ⟨algebra_map R (unitization R S) r, alg_hom.commutes _ r⟩, },
  { rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩,
    exact ⟨x + y, map_add _ _ _⟩, },
  { rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩,
    exact ⟨x * y, map_mul _ _ _⟩, },
  { rintro _ ⟨x, rfl⟩,
    exact ⟨star x, map_star _ _⟩, },
end

-- it would be nice to get the surjectivity and other results for free from the non-starred version

end star_subalgebra
