import algebra.star.non_unital_subalgebra
import algebra.star.subalgebra
import algebra.algebra.unitization

.

/-! # Relating unital and non-unital substructures

This file takes unital and non-unital structures and relates them.

-/

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

/-- The natural `ℕ`-algebra homomorphism from the unitization of a non-unital subsemiring to
its `subsemiring.closure`. -/
def non_unital_subsemiring.unitization {R : Type*} [semiring R]
  (S : non_unital_subsemiring R) : -- (h : ∀ n : ℕ, (n : R) ∉ S) :
  unitization ℕ S →ₐ[ℕ] subsemiring.closure (S : set R) :=
unitization.lift
{ to_fun := λ x : S, (⟨x, subsemiring.subset_closure x.prop⟩ : subsemiring.closure (S : set R)),
  map_smul' := λ (_ : ℕ) _, rfl,
  map_zero' := rfl,
  map_add' := λ _ _, rfl,
  map_mul' := λ _ _, rfl }

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

/-- The natural `ℤ`-algebra homomorphism from the unitization of a non-unital subring to
its `subring.closure`. -/
def non_unital_subring.unitization {R : Type*} [ring R]
  (S : non_unital_subring R) : -- (h : ∀ n : ℕ, (n : R) ∉ S) :
  unitization ℤ S →ₐ[ℤ] subring.closure (S : set R) :=
unitization.lift
{ to_fun := λ x : S, (⟨x, subring.subset_closure x.prop⟩ : subring.closure (S : set R)),
  map_smul' := λ (_ : ℤ) _, rfl,
  map_zero' := rfl,
  map_add' := λ _ _, rfl,
  map_mul' := λ _ _, rfl }

@[simp]
lemma non_unital_subring.unitization_apply_coe {R : Type*} [ring R]
  (S : non_unital_subring R) (x : unitization ℤ S) :
  (S.unitization x : R) = algebra_map ℤ (subring.closure (S : set R)) x.fst + x.snd :=
rfl

/- borked because of a type class inference loop?
lemma non_unital_subring.unitization_surjective {R : Type*} [ring R]
  (S : non_unital_subring R) : function.surjective S.unitization :=
begin
  intro x,
  refine subring.closure_induction' x _ _ _ _ _ _, --⟨0, map_zero _⟩ ⟨1, map_one _⟩ _ _ _,
  { refine λ x hx, ⟨(0, ⟨x, hx⟩), subtype.ext _⟩,
    simp only [non_unital_subring.unitization_apply_coe, subtype.coe_mk,
      unitization.fst, unitization.snd, map_zero, subsemiring.coe_zero, zero_add],
    rw map_zero, },
  { rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩,
    exact ⟨x + y, map_add _ _ _⟩, },
  { rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩,
    exact ⟨x * y, map_mul _ _ _⟩, },
end
-/

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

/-- The natural `R`-algebra homomorphism from the unitization of a non-unital subalgebra to
its `algebra.adjoin`. -/
def non_unital_subalgebra.unitization (S : non_unital_subalgebra R A) :
  unitization R S →ₐ[R] algebra.adjoin R (S : set A) :=
unitization.lift
{ to_fun := λ x : S, (⟨x, algebra.subset_adjoin x.prop⟩ : algebra.adjoin R (S : set A)),
  map_smul' := λ (_ : R) _, rfl,
  map_zero' := rfl,
  map_add' := λ _ _, rfl,
  map_mul' := λ _ _, rfl }

@[simp]
lemma non_unital_subalgebra.unitization_apply_coe (S : non_unital_subalgebra R A)
  (x : unitization R S) :
  (S.unitization x : A) = algebra_map R (algebra.adjoin R (S : set A)) x.fst + x.snd :=
rfl

lemma non_unital_subalgebra.unitization_surjective (S : non_unital_subalgebra R A) :
  function.surjective S.unitization :=
begin
  refine algebra.adjoin_induction' _ _ _ _,
  { refine λ x hx, ⟨(0, ⟨x, hx⟩), subtype.ext _⟩,
    simp only [non_unital_subalgebra.unitization_apply_coe, subtype.coe_mk],
    change (algebra_map R {x // x ∈ algebra.adjoin R (S : set A)} 0 : A) + x = x,
    rw [map_zero, subsemiring.coe_zero, zero_add], },
  { exact λ r, ⟨algebra_map R (unitization R S) r, alg_hom.commutes _ r⟩, },
  { rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩,
    exact ⟨x + y, map_add _ _ _⟩, },
  { rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩,
    exact ⟨x * y, map_mul _ _ _⟩, },
end

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

end star_subalgebra
