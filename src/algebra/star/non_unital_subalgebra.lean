/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import algebra.algebra.non_unital_subalgebra.basic
import algebra.star.star_alg_hom
import algebra.star.pointwise

/-!
# Non-unital Subalgebras over Commutative Semirings

In this file we define `non_unital_star_subalgebra`s and the usual operations on them (`map`, `comap`).

## TODO

* once we have scalar actions by semigroups (as opposed to monoids), implement the action of a
  non-unital subalgebra on the larger algebra.
-/

universes u u' v v' w w' w''

open_locale big_operators

set_option old_structure_cmd true

variables {F : Type v'} {R' : Type u'} {R : Type u}
variables {A : Type v} {B : Type w} {C : Type w'}

namespace non_unital_star_subalgebra_class

variables [comm_semiring R] [non_unital_semiring A]
variables [has_star A] [module R A]
variables {S : Type w''} [set_like S A] [non_unital_subsemiring_class S A]
variables [hSR : smul_mem_class S R A] [star_mem_class S A] (s : S)
include hSR

/-- Embedding of a non-unital subalgebra into the non-unital algebra. -/
def subtype (s : S) : s →⋆ₙₐ[R] A :=
{ to_fun := coe,
  map_star' := λ _, rfl,
 .. non_unital_subalgebra_class.subtype s }

@[simp] theorem coe_subtype : (subtype s : s → A) = coe := rfl

end non_unital_star_subalgebra_class

/-- A non-unital star subalgebra is a non-unital subalgebra which is closed under the `star`
operation. -/
structure non_unital_star_subalgebra (R : Type u) (A : Type v)
  [comm_semiring R] [non_unital_semiring A] [module R A] [has_star A] extends
  non_unital_subalgebra R A : Type v :=
(star_mem' : ∀ {a : A} (ha : a ∈ carrier), star a ∈ carrier)

/-- Reinterpret a `non_unital_star_subalgebra` as a `non_unital_star_subalgebra`. -/
add_decl_doc non_unital_star_subalgebra.to_non_unital_subalgebra

namespace non_unital_star_subalgebra

variables [comm_semiring R]
variables [non_unital_semiring A] [module R A] [has_star A]
variables [non_unital_semiring B] [module R B] [has_star B]
variables [non_unital_semiring C] [module R C] [has_star C]
variables [non_unital_star_alg_hom_class F R A B]
include R

instance : set_like (non_unital_star_subalgebra R A) A :=
{ coe := non_unital_star_subalgebra.carrier,
  coe_injective' := λ p q h, by cases p; cases q; congr' }

instance : non_unital_subsemiring_class (non_unital_star_subalgebra R A) A :=
{ add_mem := add_mem',
  mul_mem := mul_mem',
  zero_mem := zero_mem' }

instance : smul_mem_class (non_unital_star_subalgebra R A) R A :=
{ smul_mem := smul_mem' }

instance : star_mem_class (non_unital_star_subalgebra R A) A :=
{ star_mem := star_mem' }

@[simp]
lemma mem_carrier {s : non_unital_star_subalgebra R A} {x : A} : x ∈ s.carrier ↔ x ∈ s := iff.rfl

@[ext] theorem ext {S T : non_unital_star_subalgebra R A} (h : ∀ x : A, x ∈ S ↔ x ∈ T) : S = T :=
set_like.ext h

@[simp] lemma mem_to_non_unital_subalgebra {S : non_unital_star_subalgebra R A} {x} :
  x ∈ S.to_non_unital_subalgebra ↔ x ∈ S := iff.rfl

@[simp] lemma coe_to_non_unital_subalgebra (S : non_unital_star_subalgebra R A) :
  (↑S.to_non_unital_subalgebra : set A) = S := rfl

theorem to_non_unital_subalgebra_injective : function.injective
  (to_non_unital_subalgebra : non_unital_star_subalgebra R A → non_unital_subalgebra R A) :=
λ S T h, ext $ λ x, by rw [← mem_to_non_unital_subalgebra, ← mem_to_non_unital_subalgebra, h]

theorem to_non_unital_subalgebra_inj {S U : non_unital_star_subalgebra R A} :
  S.to_non_unital_subalgebra = U.to_non_unital_subalgebra ↔ S = U :=
to_non_unital_subalgebra_injective.eq_iff

lemma to_non_unital_subalgebra_le_iff {S₁ S₂ : non_unital_star_subalgebra R A} :
  S₁.to_non_unital_subalgebra ≤ S₂.to_non_unital_subalgebra ↔ S₁ ≤ S₂ := iff.rfl

/-- Copy of a non-unital star subalgebra with a new `carrier` equal to the old one.
Useful to fix definitional equalities. -/
protected def copy (S : non_unital_star_subalgebra R A) (s : set A) (hs : s = ↑S) :
  non_unital_star_subalgebra R A :=
{ carrier := s,
  add_mem' := λ _ _, hs.symm ▸ S.add_mem',
  mul_mem' := λ _ _, hs.symm ▸ S.mul_mem',
  zero_mem' := hs.symm ▸ S.zero_mem',
  smul_mem' := hs.symm ▸ S.smul_mem',
  star_mem' := λ _, hs.symm ▸ S.star_mem' }

@[simp] lemma coe_copy (S : non_unital_star_subalgebra R A) (s : set A) (hs : s = ↑S) :
  (S.copy s hs : set A) = s := rfl

lemma copy_eq (S : non_unital_star_subalgebra R A) (s : set A) (hs : s = ↑S) : S.copy s hs = S :=
set_like.coe_injective hs

variables (S : non_unital_star_subalgebra R A)

protected theorem smul_mem {x : A} (hx : x ∈ S) (r : R) : r • x ∈ S := S.smul_mem' r hx
protected theorem mul_mem {x y : A} (hx : x ∈ S) (hy : y ∈ S) : x * y ∈ S := mul_mem hx hy
protected theorem zero_mem : (0 : A) ∈ S := zero_mem S
protected theorem add_mem {x y : A} (hx : x ∈ S) (hy : y ∈ S) : x + y ∈ S := add_mem hx hy
protected theorem nsmul_mem {x : A} (hx : x ∈ S) (n : ℕ) : n • x ∈ S := nsmul_mem hx n
protected theorem list_sum_mem {L : list A} (h : ∀ x ∈ L, x ∈ S) : L.sum ∈ S := list_sum_mem h
protected theorem multiset_sum_mem {m : multiset A} (h : ∀ x ∈ m, x ∈ S) : m.sum ∈ S :=
multiset_sum_mem m h
protected theorem sum_mem {ι : Type w} {t : finset ι} {f : ι → A} (h : ∀ x ∈ t, f x ∈ S) :
  ∑ x in t, f x ∈ S :=
sum_mem h
protected theorem star_mem {x : A} (hx : x ∈ S) : star x ∈ S :=
star_mem hx

protected theorem neg_mem {R : Type u} {A : Type v} [comm_ring R] [non_unital_ring A]
  [module R A] [has_star A] (S : non_unital_star_subalgebra R A) {x : A} (hx : x ∈ S) : -x ∈ S :=
neg_mem hx
protected theorem sub_mem {R : Type u} {A : Type v} [comm_ring R] [non_unital_ring A]
  [module R A] [has_star A] (S : non_unital_star_subalgebra R A) {x y : A} (hx : x ∈ S)
  (hy : y ∈ S) : x - y ∈ S :=
sub_mem hx hy

protected theorem zsmul_mem {R : Type u} {A : Type v} [comm_ring R] [non_unital_ring A]
  [module R A] [has_star A] (S : non_unital_star_subalgebra R A) {x : A} (hx : x ∈ S) (n : ℤ) :
  n • x ∈ S :=
zsmul_mem hx n

-- do we need to duplicate the `non_unital_subring` stuff given that we have the
-- `non_unital_subring_class` already?

/-- A non-unital subalgebra over a ring is also a `subring`. -/
def to_non_unital_subring {R : Type u} {A : Type v} [comm_ring R] [non_unital_ring A] [module R A]
  [has_star A] (S : non_unital_star_subalgebra R A) : non_unital_subring A :=
{ neg_mem' := λ _, S.neg_mem,
  .. S.to_non_unital_subalgebra }

@[simp] lemma mem_to_non_unital_subring {R : Type u} {A : Type v} [comm_ring R]
  [non_unital_ring A] [module R A] [has_star A] {S : non_unital_star_subalgebra R A} {x} :
  x ∈ S.to_non_unital_subring ↔ x ∈ S := iff.rfl

@[simp] lemma coe_to_non_unital_subring {R : Type u} {A : Type v} [comm_ring R]
  [non_unital_ring A] [module R A] [has_star A] (S : non_unital_star_subalgebra R A) :
  (↑S.to_non_unital_subring : set A) = S := rfl

theorem to_non_unital_subring_injective {R : Type u} {A : Type v} [comm_ring R]
  [non_unital_ring A] [module R A] [has_star A] : function.injective
    (to_non_unital_subring : non_unital_star_subalgebra R A → non_unital_subring A) :=
λ S T h, ext $ λ x, by rw [← mem_to_non_unital_subring, ← mem_to_non_unital_subring, h]

theorem to_non_unital_subring_inj {R : Type u} {A : Type v} [comm_ring R]
  [non_unital_ring A] [module R A] [has_star A]
  {S U : non_unital_star_subalgebra R A} : S.to_non_unital_subring = U.to_non_unital_subring ↔ S = U :=
to_non_unital_subring_injective.eq_iff

instance : inhabited S := ⟨(0 : S.to_non_unital_subalgebra)⟩

section

/-! `non_unital_star_subalgebra`s inherit structure from their `non_unital_subalgebra` / `semiring` coercions. -/

instance to_non_unital_semiring {R A} [comm_semiring R] [non_unital_semiring A] [module R A]
  [has_star A] (S : non_unital_star_subalgebra R A) : non_unital_semiring S :=
infer_instance
instance to_non_unital_comm_semiring {R A} [comm_semiring R] [non_unital_comm_semiring A]
  [module R A] [has_star A] (S : non_unital_star_subalgebra R A) : non_unital_comm_semiring S :=
infer_instance
instance to_non_unital_ring {R A} [comm_ring R] [non_unital_ring A] [module R A] [has_star A]
  (S : non_unital_star_subalgebra R A) : non_unital_ring S :=
infer_instance
instance to_non_unital_comm_ring {R A} [comm_ring R] [non_unital_comm_ring A] [module R A]
  [has_star A] (S : non_unital_star_subalgebra R A) : non_unital_comm_ring S :=
infer_instance

end

/-- The forgetful map from `non_unital_star_subalgebra` to `non_unital_subalgebra` as an
`order_embedding` -/
def to_non_unital_subalgebra' : non_unital_star_subalgebra R A ↪o non_unital_subalgebra R A :=
{ to_embedding :=
  { to_fun := λ S, S.to_non_unital_subalgebra,
    inj' := λ S T h, ext $ by apply set_like.ext_iff.1 h },
  map_rel_iff' := λ S T, set_like.coe_subset_coe.symm.trans set_like.coe_subset_coe }

section

-- TODO: generalize to `smul_mem_class`

/-! `non_unital_star_subalgebra`s inherit structure from their `submodule` coercions. -/
instance module' [semiring R'] [has_smul R' R] [module R' A] [is_scalar_tower R' R A] :
  module R' S :=
S.to_non_unital_subalgebra.module'

instance : module R S := S.module'

instance is_scalar_tower' [semiring R'] [has_smul R' R] [module R' A] [is_scalar_tower R' R A] :
  is_scalar_tower R' R S :=
S.to_non_unital_subalgebra.is_scalar_tower'

instance [is_scalar_tower R A A] :
  is_scalar_tower R S S :=
{ smul_assoc := λ r x y, subtype.ext $ smul_assoc r (x : A) (y : A) }

instance smul_comm_class' [semiring R'] [has_smul R' R] [module R' A] [is_scalar_tower R' R A]
  [smul_comm_class R' R A] :
  smul_comm_class R' R S :=
{ smul_comm := λ r' r s, subtype.ext $ smul_comm r' r s }

instance [smul_comm_class R A A] : smul_comm_class R S S :=
{ smul_comm := λ r x y, subtype.ext $ smul_comm r (x : A) (y : A) }


end

instance no_zero_smul_divisors_bot [no_zero_smul_divisors R A] : no_zero_smul_divisors R S :=
⟨λ c x h,
  have c = 0 ∨ (x : A) = 0,
  from eq_zero_or_eq_zero_of_smul_eq_zero (congr_arg coe h),
  this.imp_right (@subtype.ext_iff _ _ x 0).mpr⟩

protected lemma coe_add (x y : S) : (↑(x + y) : A) = ↑x + ↑y := rfl
protected lemma coe_mul (x y : S) : (↑(x * y) : A) = ↑x * ↑y := rfl
protected lemma coe_zero : ((0 : S) : A) = 0 := rfl
protected lemma coe_neg {R : Type u} {A : Type v} [comm_ring R] [non_unital_ring A] [module R A]
  [has_star A] {S : non_unital_star_subalgebra R A} (x : S) : (↑(-x) : A) = -↑x := rfl
protected lemma coe_sub {R : Type u} {A : Type v} [comm_ring R] [non_unital_ring A]
  [module R A] [has_star A] {S : non_unital_star_subalgebra R A} (x y : S) :
  (↑(x - y) : A) = ↑x - ↑y := rfl
@[simp, norm_cast] lemma coe_smul [semiring R'] [has_smul R' R] [module R' A]
  [is_scalar_tower R' R A] (r : R') (x : S) : (↑(r • x) : A) = r • ↑x := rfl

protected lemma coe_eq_zero {x : S} : (x : A) = 0 ↔ x = 0 := zero_mem_class.coe_eq_zero

-- todo: standardize on the names these morphisms
-- compare with submodule.subtype

@[simp] lemma to_non_unital_subalgebra_subtype :
  non_unital_subalgebra_class.subtype S = non_unital_star_subalgebra_class.subtype S :=
rfl

@[simp] lemma to_subring_subtype {R A : Type*} [comm_ring R] [non_unital_ring A]
  [module R A] [has_star A] (S : non_unital_star_subalgebra R A) :
  non_unital_subring_class.subtype S = non_unital_star_subalgebra_class.subtype S :=
rfl

/- need to refactor `alg_equiv` in order for this to work.
/-- Linear equivalence between `S : submodule R A` and `S`. Though these types are equal,
we define it as a `linear_equiv` to avoid type equalities. -/
def to_non_unital_subalgebra_equiv (S : non_unital_star_subalgebra R A) :
  S.to_non_unital_subalgebra ≃ₐ[R] S :=
linear_equiv.of_eq _ _ rfl
-/

/-- Transport a non_unital_star_subalgebra via an algebra homomorphism. -/
def map (f : F) (S : non_unital_star_subalgebra R A) :
  non_unital_star_subalgebra R B :=
{ star_mem' := by { rintro _ ⟨a, ha, rfl⟩, exact ⟨star a, S.star_mem ha, map_star f a⟩ },
  .. S.to_non_unital_subalgebra.map (f : A →ₙₐ[R] B) }

lemma map_mono {S₁ S₂ : non_unital_star_subalgebra R A} {f : F} :
  S₁ ≤ S₂ → (map f S₁ : non_unital_star_subalgebra R B) ≤ map f S₂ :=
set.image_subset f

lemma map_injective {f : F} (hf : function.injective f) :
  function.injective (map f : non_unital_star_subalgebra R A → non_unital_star_subalgebra R B) :=
λ S₁ S₂ ih, ext $ set.ext_iff.1 $ set.image_injective.2 hf $ set.ext $ set_like.ext_iff.mp ih

@[simp] lemma map_id (S : non_unital_star_subalgebra R A) :
  map (non_unital_star_alg_hom.id R A) S = S :=
set_like.coe_injective $ set.image_id _

lemma map_map (S : non_unital_star_subalgebra R A) (g : B →⋆ₙₐ[R] C) (f : A →⋆ₙₐ[R] B) :
  (S.map f).map g = S.map (g.comp f) :=
set_like.coe_injective $ set.image_image _ _ _

lemma mem_map {S : non_unital_star_subalgebra R A} {f : F} {y : B} :
  y ∈ map f S ↔ ∃ x ∈ S, f x = y :=
non_unital_subalgebra.mem_map

lemma map_to_non_unital_subalgebra {S : non_unital_star_subalgebra R A} {f : F} :
  (map f S : non_unital_star_subalgebra R B).to_non_unital_subalgebra =
    non_unital_subalgebra.map f S.to_non_unital_subalgebra :=
set_like.coe_injective rfl

@[simp] lemma coe_map (S : non_unital_star_subalgebra R A) (f : F) :
  (map f S : set B) = f '' S :=
rfl

/-- Preimage of a non_unital_star_subalgebra under an algebra homomorphism. -/
def comap (f : F) (S : non_unital_star_subalgebra R B) : non_unital_star_subalgebra R A :=
{ star_mem' := λ a (ha : f a ∈ S), show f (star a) ∈ S, from (map_star f a).symm ▸ S.star_mem ha,
  .. S.to_non_unital_subalgebra.comap f }

theorem map_le {S : non_unital_star_subalgebra R A} {f : F} {U : non_unital_star_subalgebra R B} :
  map f S ≤ U ↔ S ≤ comap f U :=
set.image_subset_iff

lemma gc_map_comap (f : F) :
  galois_connection (map f : non_unital_star_subalgebra R A → non_unital_star_subalgebra R B) (comap f) :=
λ S U, map_le

@[simp] lemma mem_comap (S : non_unital_star_subalgebra R B) (f : F) (x : A) :
  x ∈ comap f S ↔ f x ∈ S :=
iff.rfl

@[simp, norm_cast] lemma coe_comap (S : non_unital_star_subalgebra R B) (f : F) :
  (comap f S : set A) = f ⁻¹' (S : set B) :=
rfl

instance no_zero_divisors {R A : Type*} [comm_semiring R] [non_unital_semiring A]
  [no_zero_divisors A] [module R A] [has_star A] (S : non_unital_star_subalgebra R A) :
  no_zero_divisors S :=
non_unital_subsemiring_class.no_zero_divisors S

end non_unital_star_subalgebra

namespace non_unital_subalgebra

variables [comm_semiring R] [non_unital_semiring A] [module R A] [has_star A]
variables (s : non_unital_subalgebra R A)

/-- A non-unital star subalgebra closed under multiplication is a non-unital subalgebra. -/
def to_non_unital_star_subalgebra (h_star : ∀ x, x ∈ s → star x ∈ s) :
  non_unital_star_subalgebra R A :=
{ star_mem' := h_star,
  .. s }

@[simp] lemma mem_to_non_unital_star_subalgebra {s : non_unital_subalgebra R A} {h_star} {x} :
  x ∈ s.to_non_unital_star_subalgebra h_star ↔ x ∈ s := iff.rfl

@[simp] lemma coe_to_non_unital_star_subalgebra (s : non_unital_subalgebra R A) (h_star) :
  (s.to_non_unital_star_subalgebra h_star : set A) = s := rfl

@[simp] lemma to_non_unital_star_subalgebra_mk (s : set A) (h0 hadd hsmul hmul hstar) :
  (⟨s, hadd, h0, hmul, hsmul⟩ : non_unital_subalgebra R A).to_non_unital_star_subalgebra hstar =
    non_unital_star_subalgebra.mk s @hadd h0 @hmul hsmul hstar :=
rfl

@[simp] lemma to_non_unital_star_subalgebra_to_non_unital_subalgebra (s : non_unital_subalgebra R A)
  (h_star) : (s.to_non_unital_star_subalgebra h_star).to_non_unital_subalgebra = s :=
set_like.coe_injective rfl

@[simp] lemma _root_.non_unital_star_subalgebra.to_non_unital_subalgebra_to_non_unital_star_subalgebra
  (S : non_unital_star_subalgebra R A) :
  S.to_non_unital_subalgebra.to_non_unital_star_subalgebra (λ _, S.star_mem) = S :=
set_like.coe_injective rfl

end non_unital_subalgebra

---- INSERT MORE SUBALGEBRA STUFF HERE (E.G. `star_closure`)

namespace non_unital_star_alg_hom

variables [comm_semiring R]
variables [non_unital_semiring A] [module R A] [has_star A]
variables [non_unital_semiring B] [module R B] [has_star B]
variables [non_unital_semiring C] [module R C] [has_star C]
variables [non_unital_star_alg_hom_class F R A B]

/-- Range of an `non_unital_alg_hom` as a non_unital_star_subalgebra. -/
protected def range (φ : F) : non_unital_star_subalgebra R B :=
{ star_mem' := by { rintro _ ⟨a, rfl⟩,  exact ⟨star a, map_star φ a⟩ },
  .. (φ : A →ₙₐ[R] B).range }

@[simp] lemma mem_range (φ : F) {y : B} :
  y ∈ (non_unital_star_alg_hom.range φ : non_unital_star_subalgebra R B) ↔ ∃ (x : A), φ x = y :=
non_unital_ring_hom.mem_srange

theorem mem_range_self (φ : F) (x : A) :
  φ x ∈ (non_unital_star_alg_hom.range φ : non_unital_star_subalgebra R B) :=
(non_unital_alg_hom.mem_range φ).2 ⟨x, rfl⟩

@[simp] lemma coe_range (φ : F) :
  ((non_unital_star_alg_hom.range φ : non_unital_star_subalgebra R B) : set B) = set.range (φ : A → B) :=
by { ext, rw [set_like.mem_coe, mem_range], refl }

theorem range_comp (f : A →⋆ₙₐ[R] B) (g : B →⋆ₙₐ[R] C) : (g.comp f).range = f.range.map g :=
set_like.coe_injective (set.range_comp g f)

theorem range_comp_le_range (f : A →⋆ₙₐ[R] B) (g : B →⋆ₙₐ[R] C) : (g.comp f).range ≤ g.range :=
set_like.coe_mono (set.range_comp_subset_range f g)

/-- Restrict the codomain of an algebra homomorphism. -/
def cod_restrict (f : F) (S : non_unital_star_subalgebra R B) (hf : ∀ x, f x ∈ S) : A →⋆ₙₐ[R] S :=
{ map_star' := λ a, subtype.ext $ map_star f a,
  .. non_unital_alg_hom.cod_restrict f S.to_non_unital_subalgebra hf }

@[simp] lemma subtype_comp_cod_restrict (f : F) (S : non_unital_star_subalgebra R B)
  (hf : ∀ (x : A), f x ∈ S) :
  (non_unital_star_subalgebra_class.subtype S).comp (non_unital_star_alg_hom.cod_restrict f S hf) = f :=
non_unital_star_alg_hom.ext $ λ _, rfl

@[simp] lemma coe_cod_restrict (f : F) (S : non_unital_star_subalgebra R B) (hf : ∀ x, f x ∈ S) (x : A) :
  ↑(non_unital_star_alg_hom.cod_restrict f S hf x) = f x := rfl

theorem injective_cod_restrict (f : F) (S : non_unital_star_subalgebra R B) (hf : ∀ x : A, f x ∈ S) :
  function.injective (non_unital_star_alg_hom.cod_restrict f S hf) ↔ function.injective f :=
⟨λ H x y hxy, H $ subtype.eq hxy, λ H x y hxy, H (congr_arg subtype.val hxy : _)⟩

/-- Restrict the codomain of a alg_hom `f` to `f.range`.

This is the bundled version of `set.range_factorization`. -/
@[reducible] def range_restrict (f : F) :
  A →⋆ₙₐ[R] (non_unital_star_alg_hom.range f : non_unital_star_subalgebra R B) :=
non_unital_star_alg_hom.cod_restrict f (non_unital_star_alg_hom.range f) (non_unital_star_alg_hom.mem_range_self f)

/-- The equalizer of two R-algebra homomorphisms -/
def equalizer (ϕ ψ : F) : non_unital_star_subalgebra R A :=
{ carrier := {a | (ϕ a : B) = ψ a},
  star_mem' := λ x (hx : ϕ x = ψ x),
    by rw [set.mem_set_of_eq, map_star, map_star, hx],
  .. non_unital_alg_hom.equalizer ϕ ψ }

@[simp] lemma mem_equalizer (φ ψ : F) (x : A) :
  x ∈ (@non_unital_star_alg_hom.equalizer F R A B _ _ _ _ _ _ _ _ φ ψ) ↔ φ x = ψ x :=
iff.rfl

/-- The range of a morphism of algebras is a fintype, if the domain is a fintype.

Note that this instance can cause a diamond with `subtype.fintype` if `B` is also a fintype. -/
instance fintype_range [fintype A] [decidable_eq B] (φ : F) :
  fintype (@non_unital_alg_hom.range F R A B _ _ _ _ _ _ φ) :=
set.fintype_range φ

end non_unital_star_alg_hom

namespace star_alg_equiv

variables [comm_semiring R]
variables [non_unital_semiring A] [module R A] [has_star A]
variables [non_unital_semiring B] [module R B] [has_star B]
variables [non_unital_semiring C] [module R C] [has_star C]
variables [hF : non_unital_star_alg_hom_class F R A B]
include hF

/-- Restrict an algebra homomorphism with a left inverse to an algebra isomorphism to its range.

This is a computable alternative to `star_alg_equiv.of_injective`. -/
def of_left_inverse
  {g : B → A} {f : F} (h : function.left_inverse g f) :
  A ≃⋆ₐ[R] (non_unital_star_alg_hom.range f) :=
{ to_fun := (non_unital_star_alg_hom.range_restrict f),
  inv_fun := g ∘ (non_unital_star_subalgebra_class.subtype $ non_unital_star_alg_hom.range f),
  left_inv := h,
  right_inv := λ x, subtype.ext $
    let ⟨x', hx'⟩ := (non_unital_star_alg_hom.mem_range f).mp x.prop in
    show f (g x) = x, by rw [←hx', h x'],
  .. non_unital_star_alg_hom.range_restrict f }

@[simp] lemma of_left_inverse_apply
  {g : B → A} {f : F} (h : function.left_inverse g f) (x : A) :
  ↑(of_left_inverse h x) = f x := rfl

@[simp] lemma of_left_inverse_symm_apply
  {g : B → A} {f : F} (h : function.left_inverse g f) (x : non_unital_star_alg_hom.range f) :
  (of_left_inverse h).symm x = g x := rfl

/-- Restrict an injective algebra homomorphism to an algebra isomorphism -/
noncomputable def of_injective (f : F) (hf : function.injective f) :
  A ≃⋆ₐ[R] (non_unital_star_alg_hom.range f) :=
of_left_inverse (classical.some_spec hf.has_left_inverse)

@[simp] lemma of_injective_apply (f : F) (hf : function.injective f) (x : A) :
  ↑(of_injective f hf x) = f x := rfl

/-
/-- Given an equivalence `e : A ≃ₐ[R] B` of `R`-algebras and a non_unital_star_subalgebra `S` of `A`,
`non_unital_star_subalgebra_map` is the induced equivalence between `S` and `S.map e` -/
@[simps] def non_unital_star_subalgebra_map (e : A ≃ₐ[R] B) (S : non_unital_star_subalgebra R A) :
  S ≃ₐ[R] (S.map e.to_alg_hom) :=
{ commutes' := λ r, by { ext, simp },
  ..e.to_ring_equiv.non_unital_subalgebra_map S.to_non_unital_subalgebra }
  -/

end star_alg_equiv

/-! ### The star closure of a subalgebra -/

namespace non_unital_subalgebra

open_locale pointwise

variables [comm_semiring R] [star_ring R]
variables [non_unital_semiring A] [star_ring A] [module R A]
variables [is_scalar_tower R A A] [smul_comm_class R A A] [star_module R A]
variables [non_unital_semiring B] [star_ring B] [module R B]
variables [is_scalar_tower R B B] [smul_comm_class R B B] [star_module R B]

/-- The pointwise `star` of a non-unital subalgebra is a non-unital subalgebra. -/
instance : has_involutive_star (non_unital_subalgebra R A) :=
{ star := λ S,
  { carrier := star S.carrier,
    mul_mem' := λ x y hx hy,
    begin
      simp only [set.mem_star, non_unital_subalgebra.mem_carrier] at *,
      exact (star_mul x y).symm ▸ mul_mem hy hx,
    end,
    add_mem' := λ x y hx hy,
    begin
      simp only [set.mem_star, non_unital_subalgebra.mem_carrier] at *,
      exact (star_add x y).symm ▸ add_mem hx hy,
    end,
    zero_mem' := set.mem_star.mp ((star_zero A).symm ▸ zero_mem S : star (0 : A) ∈ S),
    smul_mem' := λ r x hx,
    begin
      simp only [set.mem_star, non_unital_subalgebra.mem_carrier] at *,
      exact (star_smul r x).symm ▸ smul_mem_class.smul_mem (star r) hx,
    end },
  star_involutive := λ S, non_unital_subalgebra.ext $ λ x, ⟨λ hx, (star_star x ▸ hx), λ hx,
    ((star_star x).symm ▸ hx : star (star x) ∈ S)⟩ }

@[simp] lemma mem_star_iff (S : non_unital_subalgebra R A) (x : A) :
  x ∈ star S ↔ star x ∈ S := iff.rfl

@[simp] lemma star_mem_star_iff (S : non_unital_subalgebra R A) (x : A) :
  star x ∈ star S ↔ x ∈ S :=
by simpa only [star_star] using mem_star_iff S (star x)

@[simp] lemma coe_star (S : non_unital_subalgebra R A) :
  ((star S : non_unital_subalgebra R A) : set A) = star S := rfl

lemma star_mono : monotone (star : non_unital_subalgebra R A → non_unital_subalgebra R A) :=
λ _ _ h _ hx, h hx

variables (R)

/-- The star operation on `subalgebra` commutes with `algebra.adjoin`. -/
lemma star_adjoin_comm (s : set A) :
  star (non_unital_algebra.adjoin R s) = non_unital_algebra.adjoin R (star s) :=
have
  this : ∀ t : set A, non_unital_algebra.adjoin R (star t) ≤ star (non_unital_algebra.adjoin R t),
  from λ t, non_unital_algebra.adjoin_le (λ x hx, non_unital_algebra.subset_adjoin R hx),
le_antisymm (by simpa only [star_star] using non_unital_subalgebra.star_mono (this (star s)))
  (this s)

variables {R}

/-- The `non_unital_star_subalgebra` obtained from `S : non_unital_subalgebra R A` by taking the
smallest subalgebra containing both `S` and `star S`. -/
@[simps] def star_closure (S : non_unital_subalgebra R A) : non_unital_star_subalgebra R A :=
{ star_mem' := λ a ha,
  begin
    simp only [non_unital_subalgebra.mem_carrier,
      ←(@non_unital_algebra.gi R A _ _ _ _ _ ).l_sup_u _ _] at *,
    rw [←mem_star_iff _ a, star_adjoin_comm],
    convert ha,
    simp [set.union_comm],
  end,
  .. S ⊔ star S }

lemma star_closure_le {S₁ : non_unital_subalgebra R A} {S₂ : non_unital_star_subalgebra R A}
  (h : S₁ ≤ S₂.to_non_unital_subalgebra) : S₁.star_closure ≤ S₂ :=
non_unital_star_subalgebra.to_non_unital_subalgebra_le_iff.1 $ sup_le h $
  λ x hx, (star_star x ▸ star_mem (show star x ∈ S₂, from h $ (S₁.mem_star_iff _).1 hx) : x ∈ S₂)

lemma star_closure_le_iff {S₁ : non_unital_subalgebra R A} {S₂ : non_unital_star_subalgebra R A} :
  S₁.star_closure ≤ S₂ ↔ S₁ ≤ S₂.to_non_unital_subalgebra :=
⟨λ h, le_sup_left.trans h, star_closure_le⟩

end non_unital_subalgebra

namespace non_unital_star_algebra

variables [comm_semiring R] [star_ring R]
variables [non_unital_semiring A] [star_ring A]
variables [module R A] [is_scalar_tower R A A] [smul_comm_class R A A] [star_module R A]
variables [non_unital_semiring B] [star_ring B]
variables [module R B] [is_scalar_tower R B B] [smul_comm_class R B B] [star_module R B]
variables [hF : non_unital_star_alg_hom_class F R A B]

open_locale pointwise
open non_unital_star_subalgebra

variable (R)

/-- The minimal non-unital subalgebra that includes `s`. -/
def adjoin (s : set A) :
  non_unital_star_subalgebra R A :=
{ star_mem' := λ x hx,
    by rwa [non_unital_subalgebra.mem_carrier, ←non_unital_subalgebra.mem_star_iff,
      non_unital_subalgebra.star_adjoin_comm, set.union_star, star_star, set.union_comm],
  .. (non_unital_algebra.adjoin R (s ∪ star s)) }

lemma adjoin_eq_star_closure_adjoin (s : set A) :
  adjoin R s = (non_unital_algebra.adjoin R s).star_closure :=
to_non_unital_subalgebra_injective $
  show non_unital_algebra.adjoin R (s ∪ star s) =
    non_unital_algebra.adjoin R s ⊔ star (non_unital_algebra.adjoin R s),
  from (non_unital_subalgebra.star_adjoin_comm R s).symm ▸
    non_unital_algebra.adjoin_union s (star s)

lemma adjoin_to_non_unital_subalgebra (s : set A) :
  (adjoin R s).to_non_unital_subalgebra = (non_unital_algebra.adjoin R (s ∪ star s)) := rfl

lemma subset_adjoin (s : set A) : s ⊆ adjoin R s :=
  (set.subset_union_left s (star s)).trans $ non_unital_algebra.subset_adjoin R

lemma star_subset_adjoin (s : set A) : star s ⊆ adjoin R s :=
  (set.subset_union_right s (star s)).trans $ non_unital_algebra.subset_adjoin R

lemma self_mem_adjoin_singleton (x : A) : x ∈ adjoin R ({x} : set A) :=
non_unital_algebra.subset_adjoin R $ set.mem_union_left _ (set.mem_singleton x)

lemma star_self_mem_adjoin_singleton (x : A) : star x ∈ adjoin R ({x} : set A) :=
star_mem $ self_mem_adjoin_singleton R x

variables {R}

protected lemma gc : galois_connection (adjoin R : set A → non_unital_star_subalgebra R A) coe :=
begin
  intros s S,
  rw [←to_non_unital_subalgebra_le_iff, adjoin_to_non_unital_subalgebra,
    non_unital_algebra.adjoin_le_iff, coe_to_non_unital_subalgebra],
  exact ⟨λ h, (set.subset_union_left s _).trans h,
    λ h, set.union_subset h $ λ x hx, star_star x ▸ star_mem (show star x ∈ S, from h hx)⟩,
end

/-- Galois insertion between `adjoin` and `coe`. -/
protected def gi : galois_insertion (adjoin R : set A → non_unital_star_subalgebra R A) coe :=
{ choice := λ s hs, (adjoin R s).copy s $ le_antisymm (non_unital_star_algebra.gc.le_u_l s) hs,
  gc := non_unital_star_algebra.gc,
  le_l_u := λ S, (non_unital_star_algebra.gc (S : set A) (adjoin R S)).1 $ le_rfl,
  choice_eq := λ _ _, non_unital_star_subalgebra.copy_eq _ _ _ }

lemma adjoin_le {S : non_unital_star_subalgebra R A} {s : set A} (hs : s ⊆ S) : adjoin R s ≤ S :=
non_unital_star_algebra.gc.l_le hs

lemma adjoin_le_iff {S : non_unital_star_subalgebra R A} {s : set A} : adjoin R s ≤ S ↔ s ⊆ S :=
non_unital_star_algebra.gc _ _

lemma _root_.subalgebra.star_closure_eq_adjoin (S : non_unital_subalgebra R A) :
  S.star_closure = adjoin R (S : set A) :=
le_antisymm (non_unital_subalgebra.star_closure_le_iff.2 $ subset_adjoin R (S : set A))
  (adjoin_le (le_sup_left : S ≤ S ⊔ star S))

instance : complete_lattice (non_unital_star_subalgebra R A) :=
galois_insertion.lift_complete_lattice non_unital_star_algebra.gi

@[simp]
lemma coe_top : (↑(⊤ : non_unital_star_subalgebra R A) : set A) = set.univ := rfl

@[simp] lemma mem_top {x : A} : x ∈ (⊤ : non_unital_star_subalgebra R A) :=
set.mem_univ x

@[simp] lemma top_to_non_unital_subalgebra :
  (⊤ : non_unital_star_subalgebra R A).to_non_unital_subalgebra = ⊤ := rfl

@[simp] lemma to_non_unital_subalgebra_eq_top {S : non_unital_star_subalgebra R A} :
  S.to_non_unital_subalgebra = ⊤ ↔ S = ⊤ :=
non_unital_star_subalgebra.to_non_unital_subalgebra_injective.eq_iff' top_to_non_unital_subalgebra

lemma mem_sup_left {S T : non_unital_star_subalgebra R A} : ∀ {x : A}, x ∈ S → x ∈ S ⊔ T :=
show S ≤ S ⊔ T, from le_sup_left

lemma mem_sup_right {S T : non_unital_star_subalgebra R A} : ∀ {x : A}, x ∈ T → x ∈ S ⊔ T :=
show T ≤ S ⊔ T, from le_sup_right

lemma mul_mem_sup {S T : non_unital_star_subalgebra R A} {x y : A} (hx : x ∈ S) (hy : y ∈ T) :
  x * y ∈ S ⊔ T :=
(S ⊔ T).mul_mem (mem_sup_left hx) (mem_sup_right hy)

include hF

lemma map_sup (f : F) (S T : non_unital_star_subalgebra R A) :
  ((S ⊔ T).map f : non_unital_star_subalgebra R B) = S.map f ⊔ T.map f :=
(@non_unital_star_subalgebra.gc_map_comap F R A B _ _ _ _ _ _ _ _ f).l_sup

omit hF

@[simp, norm_cast]
lemma coe_inf (S T : non_unital_star_subalgebra R A) : (↑(S ⊓ T) : set A) = S ∩ T := rfl

@[simp]
lemma mem_inf {S T : non_unital_star_subalgebra R A} {x : A} : x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T := iff.rfl

@[simp] lemma inf_to_non_unital_subalgebra (S T : non_unital_star_subalgebra R A) :
  (S ⊓ T).to_non_unital_subalgebra = S.to_non_unital_subalgebra ⊓ T.to_non_unital_subalgebra := rfl

@[simp, norm_cast]
lemma coe_Inf (S : set (non_unital_star_subalgebra R A)) : (↑(Inf S) : set A) = ⋂ s ∈ S, ↑s :=
Inf_image

lemma mem_Inf {S : set (non_unital_star_subalgebra R A)} {x : A} : x ∈ Inf S ↔ ∀ p ∈ S, x ∈ p :=
by simp only [← set_like.mem_coe, coe_Inf, set.mem_Inter₂]

@[simp] lemma Inf_to_non_unital_subalgebra (S : set (non_unital_star_subalgebra R A)) :
  (Inf S).to_non_unital_subalgebra =
    Inf (non_unital_star_subalgebra.to_non_unital_subalgebra '' S) :=
set_like.coe_injective $ by simp

@[simp, norm_cast]
lemma coe_infi {ι : Sort*} {S : ι → non_unital_star_subalgebra R A} : (↑(⨅ i, S i) : set A) = ⋂ i, S i :=
by simp [infi]

lemma mem_infi {ι : Sort*} {S : ι → non_unital_star_subalgebra R A} {x : A} : (x ∈ ⨅ i, S i) ↔ ∀ i, x ∈ S i :=
by simp only [infi, mem_Inf, set.forall_range_iff]

@[simp] lemma infi_to_non_unital_subalgebra {ι : Sort*} (S : ι → non_unital_star_subalgebra R A) :
  (⨅ i, S i).to_non_unital_subalgebra = ⨅ i, (S i).to_non_unital_subalgebra :=
set_like.coe_injective $ by simp

instance : inhabited (non_unital_star_subalgebra R A) := ⟨⊥⟩

theorem mem_bot {x : A} : x ∈ (⊥ : non_unital_star_subalgebra R A) ↔ x = 0 :=
show x ∈ non_unital_algebra.adjoin R (∅ ∪ star ∅ : set A) ↔ x = 0, by
  rw [set.star_empty, set.union_empty, non_unital_algebra.adjoin_empty, non_unital_algebra.mem_bot]

theorem to_non_unital_subalgebra_bot :
  (⊥ : non_unital_star_subalgebra R A).to_non_unital_subalgebra = ⊥ :=
by { ext x, simp only [mem_bot, non_unital_star_subalgebra.mem_to_non_unital_subalgebra,
  non_unital_algebra.mem_bot] }

@[simp] theorem coe_bot : ((⊥ : non_unital_star_subalgebra R A) : set A) = {0} :=
by simp only [set.ext_iff, non_unital_star_algebra.mem_bot, set_like.mem_coe, set.mem_singleton_iff,
  iff_self, forall_const]

theorem eq_top_iff {S : non_unital_star_subalgebra R A} :
  S = ⊤ ↔ ∀ x : A, x ∈ S :=
⟨λ h x, by rw h; exact mem_top, λ h, by ext x; exact ⟨λ _, mem_top, λ _, h x⟩⟩

include hF
lemma range_top_iff_surjective (f : F) :
  non_unital_star_alg_hom.range f = (⊤ : non_unital_star_subalgebra R B) ↔ function.surjective f :=
non_unital_star_algebra.eq_top_iff

omit hF

@[simp] theorem range_id : (non_unital_star_alg_hom.id R A).range = ⊤ :=
set_like.coe_injective set.range_id

include hF
@[simp] theorem map_top (f : F) :
  (⊤ : non_unital_star_subalgebra R A).map f = non_unital_star_alg_hom.range f :=
set_like.coe_injective set.image_univ

@[simp] theorem map_bot (f : F) : (⊥ : non_unital_star_subalgebra R A).map f = ⊥ :=
set_like.coe_injective $
by simp [non_unital_algebra.coe_bot, non_unital_star_subalgebra.coe_map]

@[simp] theorem comap_top (f : F) : (⊤ : non_unital_star_subalgebra R B).comap f = ⊤ :=
eq_top_iff.2 $ λ x, mem_top

omit hF

/-- `non_unital_alg_hom` to `⊤ : non_unital_star_subalgebra R A`. -/
def to_top : A →⋆ₙₐ[R] (⊤ : non_unital_star_subalgebra R A) :=
(non_unital_star_alg_hom.id R A).cod_restrict ⊤ (λ _, mem_top)

end non_unital_star_algebra

namespace non_unital_star_subalgebra
open non_unital_star_algebra

variables [comm_semiring R] [star_ring R]
variables [non_unital_semiring A] [star_ring A]
variables [module R A] [is_scalar_tower R A A] [smul_comm_class R A A] [star_module R A]
variables [non_unital_semiring B] [star_ring B]
variables [module R B] [is_scalar_tower R B B] [smul_comm_class R B B] [star_module R B]
variables [hF : non_unital_star_alg_hom_class F R A B] (S : non_unital_star_subalgebra R A)

/- can't have this until we refactor `alg_equiv`.
/-- The top non_unital_star_subalgebra is isomorphic to the algebra.

This is the algebra version of `submodule.top_equiv`. -/
@[simps] def top_equiv : (⊤ : non_unital_star_subalgebra R A) ≃ₐ[R] A :=
alg_equiv.of_alg_hom (non_unital_star_subalgebra_class.subtype ⊤) to_top rfl $
  non_unital_alg_hom.ext $ λ _, subtype.ext rfl
  -/
#where

instance subsingleton_of_subsingleton [subsingleton A] :
  subsingleton (non_unital_star_subalgebra R A) :=
⟨λ B C, ext (λ x, by { simp only [subsingleton.elim x 0, zero_mem B, zero_mem C] })⟩

instance _root_.non_unital_star_alg_hom.subsingleton
  [subsingleton (non_unital_star_subalgebra R A)] : subsingleton (A →⋆ₙₐ[R] B) :=
⟨λ f g, non_unital_star_alg_hom.ext $ λ a, have a ∈ (⊥ : non_unital_star_subalgebra R A),
  from subsingleton.elim (⊤ : non_unital_star_subalgebra R A) ⊥ ▸ mem_top,
  (mem_bot.mp this).symm ▸ (map_zero f).trans (map_zero g).symm⟩

/- need to refactor `alg_equiv` first
instance _root_.non_unital_alg_equiv.subsingleton_left [subsingleton (non_unital_star_subalgebra R A)] :
  subsingleton (A ≃ₐ[R] B) :=
⟨λ f g, alg_equiv.ext (λ x, alg_hom.ext_iff.mp (subsingleton.elim f.to_alg_hom g.to_alg_hom) x)⟩

instance _root_.alg_equiv.subsingleton_right [subsingleton (non_unital_star_subalgebra R B)] :
  subsingleton (A ≃ₐ[R] B) :=
⟨λ f g, by rw [← f.symm_symm, subsingleton.elim f.symm g.symm, g.symm_symm]⟩
-/

lemma range_val : (non_unital_star_subalgebra_class.subtype S).range = S :=
ext $ set.ext_iff.1 $ (non_unital_star_subalgebra_class.subtype S).coe_range.trans subtype.range_val

/-- The map `S → T` when `S` is a non_unital_star_subalgebra contained in the non_unital_star_subalgebra `T`.

This is the non_unital_star_subalgebra version of `submodule.of_le`, or `subring.inclusion`  -/
def inclusion {S T : non_unital_star_subalgebra R A} (h : S ≤ T) : S →ₙₐ[R] T :=
{ to_fun := set.inclusion h,
  map_add' := λ _ _, rfl,
  map_mul' := λ _ _, rfl,
  map_zero' := rfl,
  map_smul' := λ _ _, rfl }

lemma inclusion_injective {S T : non_unital_star_subalgebra R A} (h : S ≤ T) :
  function.injective (inclusion h) :=
λ _ _, subtype.ext ∘ subtype.mk.inj

@[simp] lemma inclusion_self {S : non_unital_star_subalgebra R A}:
  inclusion (le_refl S) = non_unital_alg_hom.id R S :=
non_unital_alg_hom.ext $ λ x, subtype.ext rfl

@[simp] lemma inclusion_mk {S T : non_unital_star_subalgebra R A} (h : S ≤ T) (x : A) (hx : x ∈ S) :
  inclusion h ⟨x, hx⟩ = ⟨x, h hx⟩ := rfl

lemma inclusion_right {S T : non_unital_star_subalgebra R A} (h : S ≤ T) (x : T)
  (m : (x : A) ∈ S) : inclusion h ⟨x, m⟩ = x := subtype.ext rfl

@[simp] lemma inclusion_inclusion {S T U : non_unital_star_subalgebra R A} (hst : S ≤ T) (htu : T ≤ U)
  (x : S) : inclusion htu (inclusion hst x) = inclusion (le_trans hst htu) x :=
subtype.ext rfl

@[simp] lemma coe_inclusion {S T : non_unital_star_subalgebra R A} (h : S ≤ T) (s : S) :
  (inclusion h s : A) = s := rfl

/- need to refactor `alg_equiv`
/-- Two non_unital_star_subalgebras that are equal are also equivalent as algebras.

This is the `non_unital_star_subalgebra` version of `linear_equiv.of_eq` and `equiv.set.of_eq`. -/
@[simps apply]
def equiv_of_eq (S T : non_unital_star_subalgebra R A) (h : S = T) : S ≃ₐ[R] T :=
{ to_fun := λ x, ⟨x, h ▸ x.2⟩,
  inv_fun := λ x, ⟨x, h.symm ▸ x.2⟩,
  map_mul' := λ _ _, rfl,
  commutes' := λ _, rfl,
  .. linear_equiv.of_eq _ _ (congr_arg to_submodule h) }

@[simp] lemma equiv_of_eq_symm (S T : non_unital_star_subalgebra R A) (h : S = T) :
  (equiv_of_eq S T h).symm = equiv_of_eq T S h.symm :=
rfl

@[simp] lemma equiv_of_eq_rfl (S : non_unital_star_subalgebra R A) :
  equiv_of_eq S S rfl = alg_equiv.refl :=
by { ext, refl }

@[simp] lemma equiv_of_eq_trans (S T U : non_unital_star_subalgebra R A) (hST : S = T) (hTU : T = U) :
  (equiv_of_eq S T hST).trans (equiv_of_eq T U hTU) = equiv_of_eq S U (trans hST hTU) :=
rfl
  -/

section prod

variables (S₁ : non_unital_star_subalgebra R B)

/-- The product of two non_unital_star_subalgebras is a non_unital_star_subalgebra. -/
def prod : non_unital_star_subalgebra R (A × B) :=
{ carrier := S ×ˢ S₁,
  star_mem' := λ x hx, ⟨S.star_mem hx.1, S₁.star_mem hx.2⟩,
  .. S.to_non_unital_subalgebra.prod S₁.to_non_unital_subalgebra }

@[simp] lemma coe_prod : (prod S S₁ : set (A × B)) = S ×ˢ S₁ := rfl

lemma prod_to_non_unital_subalgebra :
  (S.prod S₁).to_non_unital_subalgebra =
    S.to_non_unital_subalgebra.prod S₁.to_non_unital_subalgebra :=
rfl

@[simp] lemma mem_prod {S : non_unital_star_subalgebra R A} {S₁ : non_unital_star_subalgebra R B}
  {x : A × B} : x ∈ prod S S₁ ↔ x.1 ∈ S ∧ x.2 ∈ S₁ := set.mem_prod

@[simp] lemma prod_top : (prod ⊤ ⊤ : non_unital_star_subalgebra R (A × B)) = ⊤ :=
by ext; simp

lemma prod_mono {S T : non_unital_star_subalgebra R A} {S₁ T₁ : non_unital_star_subalgebra R B} :
  S ≤ T → S₁ ≤ T₁ → prod S S₁ ≤ prod T T₁ := set.prod_mono

@[simp] lemma prod_inf_prod {S T : non_unital_star_subalgebra R A} {S₁ T₁ : non_unital_star_subalgebra R B} :
  S.prod S₁ ⊓ T.prod T₁ = (S ⊓ T).prod (S₁ ⊓ T₁) :=
set_like.coe_injective set.prod_inter_prod

end prod

section supr_lift
variables {ι : Type*}

lemma coe_supr_of_directed [nonempty ι] {S : ι → non_unital_star_subalgebra R A}
  (dir : directed (≤) S) : ↑(supr S) = ⋃ i, (S i : set A) :=
let K : non_unital_star_subalgebra R A :=
  { carrier := ⋃ i, (S i),
    zero_mem' := let i := @nonempty.some ι infer_instance in set.mem_Union.2 ⟨i, zero_mem (S i)⟩,
    mul_mem' := λ x y hx hy,
      let ⟨i, hi⟩ := set.mem_Union.1 hx in
      let ⟨j, hj⟩ := set.mem_Union.1 hy in
      let ⟨k, hik, hjk⟩ := dir i j in
      set.mem_Union.2 ⟨k, non_unital_star_subalgebra.mul_mem (S k) (hik hi) (hjk hj)⟩ ,
    add_mem' := λ x y hx hy,
      let ⟨i, hi⟩ := set.mem_Union.1 hx in
      let ⟨j, hj⟩ := set.mem_Union.1 hy in
      let ⟨k, hik, hjk⟩ := dir i j in
      set.mem_Union.2 ⟨k, non_unital_star_subalgebra.add_mem (S k) (hik hi) (hjk hj)⟩,
    smul_mem' := λ r x hx, let ⟨i, hi⟩ := set.mem_Union.1 hx in
      set.mem_Union.2 ⟨i, (S i).smul_mem hi r⟩,
    star_mem' := λ x hx,
      let ⟨i, hi⟩ := set.mem_Union.1 hx in
      set.mem_Union.2 ⟨i, (S i).star_mem hi⟩ } in
have supr S = K,
  from le_antisymm (supr_le (λ i, set.subset_Union (λ i, ↑(S i)) i))
    (set_like.coe_subset_coe.1
      (set.Union_subset (λ i, set_like.coe_subset_coe.2 (le_supr _ _)))),
this.symm ▸ rfl

/-- Define an algebra homomorphism on a directed supremum of non-unital subalgebras by defining
it on each non-unital subalgebra, and proving that it agrees on the intersection of
non-unital subalgebras. -/
noncomputable def supr_lift [nonempty ι]
  (K : ι → non_unital_star_subalgebra R A)
  (dir : directed (≤) K)
  (f : Π i, K i →ₙₐ[R] B)
  (hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h))
  (T : non_unital_star_subalgebra R A) (hT : T = supr K) :
  ↥T →ₙₐ[R] B :=
by subst hT; exact
{ to_fun := set.Union_lift (λ i, ↑(K i)) (λ i x, f i x)
    (λ i j x hxi hxj,
      let ⟨k, hik, hjk⟩ := dir i j in
      begin
        rw [hf i k hik, hf j k hjk],
        refl
      end) ↑(supr K)
    (by rw coe_supr_of_directed dir; refl),
  map_zero' := set.Union_lift_const _ (λ _, 0) (λ _, rfl) _ (by simp),
  map_mul' := set.Union_lift_binary (coe_supr_of_directed dir) dir _
    (λ _, (*)) (λ _ _ _, rfl) _ (by simp),
  map_add' := set.Union_lift_binary (coe_supr_of_directed dir) dir _
    (λ _, (+)) (λ _ _ _, rfl) _ (by simp),
  map_smul' := λ r, set.Union_lift_unary (coe_supr_of_directed dir) _ (λ _ x, r • x) (λ _ _, rfl) _
    (by simp) }

variables [nonempty ι] {K : ι → non_unital_star_subalgebra R A} {dir : directed (≤) K}
  {f : Π i, K i →ₙₐ[R] B}
  {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h)}
  {T : non_unital_star_subalgebra R A} {hT : T = supr K}

@[simp] lemma supr_lift_inclusion {i : ι} (x : K i) (h : K i ≤ T) :
  supr_lift K dir f hf T hT (inclusion h x) = f i x :=
by subst T; exact set.Union_lift_inclusion _ _

@[simp] lemma supr_lift_comp_inclusion {i : ι} (h : K i ≤ T) :
  (supr_lift K dir f hf T hT).comp (inclusion h) = f i :=
by ext; simp

@[simp] lemma supr_lift_mk {i : ι} (x : K i) (hx : (x : A) ∈ T) :
  supr_lift K dir f hf T hT ⟨x, hx⟩ = f i x :=
by subst hT; exact set.Union_lift_mk x hx

lemma supr_lift_of_mem {i : ι} (x : T) (hx : (x : A) ∈ K i) :
  supr_lift K dir f hf T hT x = f i ⟨x, hx⟩ :=
by subst hT; exact set.Union_lift_of_mem x hx

end supr_lift

section center

lemma _root_.set.star_mem_center {A : Type*} [semigroup A] [star_semigroup A] {a : A}
  (ha : a ∈ set.center A) : star a ∈ set.center A :=
by simpa only [star_mul, star_star] using
  λ g, congr_arg star ((set.mem_center_iff A).mp ha $ star g).symm

variables (R A)

/-- The center of an algebra is the set of elements which commute with every element. They form a
non-unital subalgebra. -/
def center : non_unital_star_subalgebra R A :=
{ star_mem' := λ a, set.star_mem_center,
  .. non_unital_subalgebra.center R A }

lemma coe_center : (center R A : set A) = set.center A := rfl

@[simp] lemma center_to_non_unital_subalgebra :
  (center R A).to_non_unital_subalgebra = non_unital_subalgebra.center R A :=
rfl

@[simp] lemma center_eq_top (A : Type*) [non_unital_comm_semiring A] [star_ring A] [module R A]
  [is_scalar_tower R A A] [smul_comm_class R A A] [star_module R A] : center R A = ⊤ :=
set_like.coe_injective (set.center_eq_univ A)

variables {R A}

/-
instance : comm_semiring (center R A) := non_unital_subalgebra.center.comm_semiring

instance {A : Type*} [non_unital_ring A] [star_ring A] [module R A] [is_scalar_tower R A A]
  [smul_comm_class R A A] [star_module R A] : comm_ring (center R A) :=
non_unital_subring.center.comm_ring
-/

lemma mem_center_iff {a : A} : a ∈ center R A ↔ ∀ (b : A), b * a = a * b := iff.rfl

end center

section centralizer

lemma _root_.set.star_mem_centralizer {A : Type*} [non_unital_semiring A] [star_ring A]
  {a : A} {s : set A} (h : ∀ (a : A), a ∈ s → star a ∈ s) (ha : a ∈ set.centralizer s) :
  star a ∈ set.centralizer s :=
λ y hy, by simpa using congr_arg star (ha _ (h _ hy)).symm

lemma _root_.set.star_mem_centralizer' {A : Type*} [non_unital_semiring A] [star_ring A]
  {a : A} {s : set A} (ha : a ∈ set.centralizer (s ∪ star s)) :
  star a ∈ set.centralizer (s ∪ star s) :=
set.star_mem_centralizer (λ x hx, hx.elim (λ hx, or.inr $ set.star_mem_star.mpr hx) or.inl) ha

variables (R)


/-- The centralizer of the star-closure of a set as a non-unital star subalgebra. -/
def centralizer (s : set A) : non_unital_star_subalgebra R A :=
{ star_mem' := λ a, set.star_mem_centralizer',
  .. non_unital_subalgebra.centralizer R (s ∪ star s), }

@[simp, norm_cast]
lemma coe_centralizer (s : set A) :
  (centralizer R s : set A) = (s ∪ star s).centralizer :=
rfl

lemma mem_centralizer_iff {s : set A} {z : A} :
  z ∈ centralizer R s ↔ ∀ g ∈ s, g * z = z * g ∧ (star g) * z = z * (star g) :=
begin
  show (∀ g ∈ s ∪ star s, g * z = z * g) ↔ ∀ g ∈ s, g * z = z * g ∧ (star g) * z = z * (star g),
  simp only [set.mem_union, or_imp_distrib, forall_and_distrib, and.congr_right_iff],
  exact λ h, ⟨λ hz a ha, hz _ (set.star_mem_star.mpr ha), λ hz a ha, star_star a ▸ hz _ ha⟩,
end

lemma centralizer_le (s t : set A) (h : s ⊆ t) :
  centralizer R t ≤ centralizer R s :=
set.centralizer_subset (set.union_subset_union h $ set.preimage_mono h)

@[simp]
lemma centralizer_univ : centralizer R set.univ = center R A :=
set_like.ext' $ by rw [coe_centralizer, set.univ_union, coe_center, set.centralizer_univ]

end centralizer

end non_unital_star_subalgebra
