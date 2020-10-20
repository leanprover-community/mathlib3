/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import algebra.algebra.basic

/-!
# Subalgebras over Commutative Semiring

In this file we define `subalgebra`s and the usual operations on them (`map`, `comap`).

More lemmas about `adjoin` can be found in `ring_theory.adjoin`.
-/
universes u v w

open_locale tensor_product big_operators

set_option old_structure_cmd true

/-- A subalgebra is a sub(semi)ring that includes the range of `algebra_map`. -/
structure subalgebra (R : Type u) (A : Type v)
  [comm_semiring R] [semiring A] [algebra R A] extends subsemiring A : Type v :=
(algebra_map_mem' : ∀ r, algebra_map R A r ∈ carrier)

/-- Reinterpret a `subalgebra` as a `subsemiring`. -/
add_decl_doc subalgebra.to_subsemiring

namespace subalgebra

variables {R : Type u} {A : Type v} {B : Type w}
variables [comm_semiring R] [semiring A] [algebra R A] [semiring B] [algebra R B]
include R

instance : has_coe (subalgebra R A) (subsemiring A) :=
⟨λ S, { ..S }⟩

instance : has_mem A (subalgebra R A) :=
⟨λ x S, x ∈ (S : set A)⟩

variables {A}
theorem mem_coe {x : A} {s : subalgebra R A} : x ∈ (s : set A) ↔ x ∈ s :=
iff.rfl

@[ext] theorem ext {S T : subalgebra R A}
  (h : ∀ x : A, x ∈ S ↔ x ∈ T) : S = T :=
by cases S; cases T; congr; ext x; exact h x

theorem ext_iff {S T : subalgebra R A} : S = T ↔ ∀ x : A, x ∈ S ↔ x ∈ T :=
⟨λ h x, by rw h, ext⟩

variables (S : subalgebra R A)

theorem algebra_map_mem (r : R) : algebra_map R A r ∈ S :=
S.algebra_map_mem' r

theorem srange_le : (algebra_map R A).srange ≤ S :=
λ x ⟨r, _, hr⟩, hr ▸ S.algebra_map_mem r

theorem range_subset : set.range (algebra_map R A) ⊆ S :=
λ x ⟨r, hr⟩, hr ▸ S.algebra_map_mem r

theorem range_le : set.range (algebra_map R A) ≤ S :=
S.range_subset

theorem one_mem : (1 : A) ∈ S :=
subsemiring.one_mem S

theorem mul_mem {x y : A} (hx : x ∈ S) (hy : y ∈ S) : x * y ∈ S :=
subsemiring.mul_mem S hx hy

theorem smul_mem {x : A} (hx : x ∈ S) (r : R) : r • x ∈ S :=
(algebra.smul_def r x).symm ▸ S.mul_mem (S.algebra_map_mem r) hx

theorem pow_mem {x : A} (hx : x ∈ S) (n : ℕ) : x ^ n ∈ S :=
subsemiring.pow_mem S hx n

theorem zero_mem : (0 : A) ∈ S :=
subsemiring.zero_mem S

theorem add_mem {x y : A} (hx : x ∈ S) (hy : y ∈ S) : x + y ∈ S :=
subsemiring.add_mem S hx hy

theorem neg_mem {R : Type u} {A : Type v} [comm_ring R] [ring A]
  [algebra R A] (S : subalgebra R A) {x : A} (hx : x ∈ S) : -x ∈ S :=
neg_one_smul R x ▸ S.smul_mem hx _

theorem sub_mem {R : Type u} {A : Type v} [comm_ring R] [ring A]
  [algebra R A] (S : subalgebra R A) {x y : A} (hx : x ∈ S) (hy : y ∈ S) : x - y ∈ S :=
S.add_mem hx $ S.neg_mem hy

theorem nsmul_mem {x : A} (hx : x ∈ S) (n : ℕ) : n •ℕ x ∈ S :=
subsemiring.nsmul_mem S hx n

theorem gsmul_mem {R : Type u} {A : Type v} [comm_ring R] [ring A]
  [algebra R A] (S : subalgebra R A) {x : A} (hx : x ∈ S) (n : ℤ) : n •ℤ x ∈ S :=
int.cases_on n (λ i, S.nsmul_mem hx i) (λ i, S.neg_mem $ S.nsmul_mem hx _)

theorem coe_nat_mem (n : ℕ) : (n : A) ∈ S :=
subsemiring.coe_nat_mem S n

theorem coe_int_mem {R : Type u} {A : Type v} [comm_ring R] [ring A]
  [algebra R A] (S : subalgebra R A) (n : ℤ) : (n : A) ∈ S :=
int.cases_on n (λ i, S.coe_nat_mem i) (λ i, S.neg_mem $ S.coe_nat_mem $ i + 1)

theorem list_prod_mem {L : list A} (h : ∀ x ∈ L, x ∈ S) : L.prod ∈ S :=
subsemiring.list_prod_mem S h

theorem list_sum_mem {L : list A} (h : ∀ x ∈ L, x ∈ S) : L.sum ∈ S :=
subsemiring.list_sum_mem S h

theorem multiset_prod_mem {R : Type u} {A : Type v} [comm_semiring R] [comm_semiring A]
  [algebra R A] (S : subalgebra R A) {m : multiset A} (h : ∀ x ∈ m, x ∈ S) : m.prod ∈ S :=
subsemiring.multiset_prod_mem S m h

theorem multiset_sum_mem {m : multiset A} (h : ∀ x ∈ m, x ∈ S) : m.sum ∈ S :=
subsemiring.multiset_sum_mem S m h

theorem prod_mem {R : Type u} {A : Type v} [comm_semiring R] [comm_semiring A]
  [algebra R A] (S : subalgebra R A) {ι : Type w} {t : finset ι} {f : ι → A}
  (h : ∀ x ∈ t, f x ∈ S) : ∏ x in t, f x ∈ S :=
subsemiring.prod_mem S h

theorem sum_mem {ι : Type w} {t : finset ι} {f : ι → A}
  (h : ∀ x ∈ t, f x ∈ S) : ∑ x in t, f x ∈ S :=
subsemiring.sum_mem S h

instance {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
  (S : subalgebra R A) : is_add_submonoid (S : set A) :=
{ zero_mem := S.zero_mem,
  add_mem := λ _ _, S.add_mem }

instance {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
  (S : subalgebra R A) : is_submonoid (S : set A) :=
{ one_mem := S.one_mem,
  mul_mem := λ _ _, S.mul_mem }

/-- A subalgebra over a ring is also a `subring`. -/
def to_subring {R : Type u} {A : Type v} [comm_ring R] [ring A] [algebra R A] (S : subalgebra R A) :
  subring A :=
{ neg_mem' := λ _, S.neg_mem,
  .. S.to_subsemiring }

instance {R : Type u} {A : Type v} [comm_ring R] [ring A] [algebra R A] (S : subalgebra R A) :
  is_subring (S : set A) :=
{ neg_mem := λ _, S.neg_mem }

instance : inhabited S := ⟨0⟩
instance (R : Type u) (A : Type v) [comm_semiring R] [semiring A]
  [algebra R A] (S : subalgebra R A) : semiring S := subsemiring.to_semiring S
instance (R : Type u) (A : Type v) [comm_semiring R] [comm_semiring A]
  [algebra R A] (S : subalgebra R A) : comm_semiring S := subsemiring.to_comm_semiring S
instance (R : Type u) (A : Type v) [comm_ring R] [ring A]
  [algebra R A] (S : subalgebra R A) : ring S := @@subtype.ring _ S.is_subring
instance (R : Type u) (A : Type v) [comm_ring R] [comm_ring A]
  [algebra R A] (S : subalgebra R A) : comm_ring S := @@subtype.comm_ring _ S.is_subring

instance algebra : algebra R S :=
{ smul := λ (c:R) x, ⟨c • x.1, S.smul_mem x.2 c⟩,
  commutes' := λ c x, subtype.eq $ algebra.commutes _ _,
  smul_def' := λ c x, subtype.eq $ algebra.smul_def _ _,
  .. (algebra_map R A).cod_srestrict S $ λ x, S.range_le ⟨x, rfl⟩ }

instance to_algebra {R A B : Type*} [comm_semiring R] [comm_semiring A] [semiring B]
  [algebra R A] [algebra A B] (A₀ : subalgebra R A) : algebra A₀ B :=
algebra.of_subsemiring A₀

instance nontrivial [nontrivial A] : nontrivial S :=
subsemiring.nontrivial S

-- todo: standardize on the names these morphisms
-- compare with submodule.subtype

/-- Embedding of a subalgebra into the algebra. -/
def val : S →ₐ[R] A :=
by refine_struct { to_fun := (coe : S → A) }; intros; refl

@[simp] lemma coe_val : (S.val : S → A) = coe := rfl

lemma val_apply (x : S) : S.val x = (x : A) := rfl

/-- Convert a `subalgebra` to `submodule` -/
def to_submodule : submodule R A :=
{ carrier := S,
  zero_mem' := (0:S).2,
  add_mem' := λ x y hx hy, (⟨x, hx⟩ + ⟨y, hy⟩ : S).2,
  smul_mem' := λ c x hx, (algebra.smul_def c x).symm ▸
    (⟨algebra_map R A c, S.range_le ⟨c, rfl⟩⟩ * ⟨x, hx⟩:S).2 }

instance coe_to_submodule : has_coe (subalgebra R A) (submodule R A) :=
⟨to_submodule⟩

instance to_submodule.is_subring {R : Type u} {A : Type v} [comm_ring R] [ring A] [algebra R A]
  (S : subalgebra R A) : is_subring ((S : submodule R A) : set A) := S.is_subring

@[simp] lemma mem_to_submodule {x} : x ∈ (S : submodule R A) ↔ x ∈ S := iff.rfl

theorem to_submodule_injective {S U : subalgebra R A} (h : (S : submodule R A) = U) : S = U :=
ext $ λ x, by rw [← mem_to_submodule, ← mem_to_submodule, h]

theorem to_submodule_inj {S U : subalgebra R A} : (S : submodule R A) = U ↔ S = U :=
⟨to_submodule_injective, congr_arg _⟩

/-- Linear equivalence between `S : submodule R A` and `S`. Though these types are equal,
we define it as a `linear_equiv` to avoid type equalities. -/
def to_submodule_equiv (S : subalgebra R A) : (S : submodule R A) ≃ₗ[R] S :=
linear_equiv.of_eq _ _ rfl

instance : partial_order (subalgebra R A) :=
{ le := λ S T, (S : set A) ⊆ (T : set A),
  le_refl := λ S, set.subset.refl S,
  le_trans := λ _ _ _, set.subset.trans,
  le_antisymm := λ S T hst hts, ext $ λ x, ⟨@hst x, @hts x⟩ }

/-- Reinterpret an `S`-subalgebra as an `R`-subalgebra in `comap R S A`. -/
def comap {R : Type u} {S : Type v} {A : Type w}
  [comm_semiring R] [comm_semiring S] [semiring A] [algebra R S] [algebra S A]
  (iSB : subalgebra S A) : subalgebra R (algebra.comap R S A) :=
{ algebra_map_mem' := λ r, iSB.algebra_map_mem (algebra_map R S r),
  .. iSB }

/-- If `S` is an `R`-subalgebra of `A` and `T` is an `S`-subalgebra of `A`,
then `T` is an `R`-subalgebra of `A`. -/
def under {R : Type u} {A : Type v} [comm_semiring R] [comm_semiring A]
  {i : algebra R A} (S : subalgebra R A)
  (T : subalgebra S A) : subalgebra R A :=
{ algebra_map_mem' := λ r, T.algebra_map_mem ⟨algebra_map R A r, S.algebra_map_mem r⟩,
  .. T }

/-- Transport a subalgebra via an algebra homomorphism. -/
def map (S : subalgebra R A) (f : A →ₐ[R] B) : subalgebra R B :=
{ algebra_map_mem' := λ r, f.commutes r ▸ set.mem_image_of_mem _ (S.algebra_map_mem r),
  .. subsemiring.map (f : A →+* B) S,}

/-- Preimage of a subalgebra under an algebra homomorphism. -/
def comap' (S : subalgebra R B) (f : A →ₐ[R] B) : subalgebra R A :=
{ algebra_map_mem' := λ r, show f (algebra_map R A r) ∈ S,
    from (f.commutes r).symm ▸ S.algebra_map_mem r,
  .. subsemiring.comap (f : A →+* B) S,}

lemma map_mono {S₁ S₂ : subalgebra R A} {f : A →ₐ[R] B} :
  S₁ ≤ S₂ → S₁.map f ≤ S₂.map f :=
set.image_subset f

theorem map_le {S : subalgebra R A} {f : A →ₐ[R] B} {U : subalgebra R B} :
  map S f ≤ U ↔ S ≤ comap' U f :=
set.image_subset_iff

lemma map_injective {S₁ S₂ : subalgebra R A} (f : A →ₐ[R] B)
  (hf : function.injective f) (ih : S₁.map f = S₂.map f) : S₁ = S₂ :=
ext $ set.ext_iff.1 $ set.image_injective.2 hf $ set.ext $ ext_iff.1 ih

lemma mem_map {S : subalgebra R A} {f : A →ₐ[R] B} {y : B} :
  y ∈ map S f ↔ ∃ x ∈ S, f x = y :=
subsemiring.mem_map

instance integral_domain {R A : Type*} [comm_ring R] [integral_domain A] [algebra R A]
  (S : subalgebra R A) : integral_domain S :=
@subring.domain A _ S _

end subalgebra

namespace alg_hom

variables {R : Type u} {A : Type v} {B : Type w}
variables [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B]
variables (φ : A →ₐ[R] B)

/-- Range of an `alg_hom` as a subalgebra. -/
protected def range (φ : A →ₐ[R] B) : subalgebra R B :=
{ algebra_map_mem' := λ r, ⟨algebra_map R A r, set.mem_univ _, φ.commutes r⟩,
  .. φ.to_ring_hom.srange }

@[simp] lemma mem_range (φ : A →ₐ[R] B) {y : B} :
  y ∈ φ.range ↔ ∃ x, φ x = y := ring_hom.mem_srange

@[simp] lemma coe_range (φ : A →ₐ[R] B) : (φ.range : set B) = set.range φ :=
by { ext, rw [subalgebra.mem_coe, mem_range], refl }

/-- Restrict the codomain of an algebra homomorphism. -/
def cod_restrict (f : A →ₐ[R] B) (S : subalgebra R B) (hf : ∀ x, f x ∈ S) : A →ₐ[R] S :=
{ commutes' := λ r, subtype.eq $ f.commutes r,
  .. ring_hom.cod_srestrict (f : A →+* B) S hf }

theorem injective_cod_restrict (f : A →ₐ[R] B) (S : subalgebra R B) (hf : ∀ x, f x ∈ S) :
  function.injective (f.cod_restrict S hf) ↔ function.injective f :=
⟨λ H x y hxy, H $ subtype.eq hxy, λ H x y hxy, H (congr_arg subtype.val hxy : _)⟩

end alg_hom

namespace algebra

variables (R : Type u) {A : Type v} {B : Type w}
variables [comm_semiring R] [semiring A] [algebra R A] [semiring B] [algebra R B]

/-- The minimal subalgebra that includes `s`. -/
def adjoin (s : set A) : subalgebra R A :=
{ algebra_map_mem' := λ r, subsemiring.subset_closure $ or.inl ⟨r, rfl⟩,
  .. subsemiring.closure (set.range (algebra_map R A) ∪ s) }
variables {R}

protected lemma gc : galois_connection (adjoin R : set A → subalgebra R A) coe :=
λ s S, ⟨λ H, le_trans (le_trans (set.subset_union_right _ _) subsemiring.subset_closure) H,
λ H, subsemiring.closure_le.2 $ set.union_subset S.range_subset H⟩

/-- Galois insertion between `adjoin` and `coe`. -/
protected def gi : galois_insertion (adjoin R : set A → subalgebra R A) coe :=
{ choice := λ s hs, adjoin R s,
  gc := algebra.gc,
  le_l_u := λ S, (algebra.gc (S : set A) (adjoin R S)).1 $ le_refl _,
  choice_eq := λ _ _, rfl }

instance : complete_lattice (subalgebra R A) :=
galois_insertion.lift_complete_lattice algebra.gi

instance : inhabited (subalgebra R A) := ⟨⊥⟩

theorem mem_bot {x : A} : x ∈ (⊥ : subalgebra R A) ↔ x ∈ set.range (algebra_map R A) :=
suffices (of_id R A).range = (⊥ : subalgebra R A),
by { rw [← this, ← subalgebra.mem_coe, alg_hom.coe_range], refl },
le_bot_iff.mp (λ x hx, subalgebra.range_le _ ((of_id R A).coe_range ▸ hx))

theorem to_submodule_bot : ((⊥ : subalgebra R A) : submodule R A) = submodule.span R {1} :=
by { ext x, simp [mem_bot, -set.singleton_one, submodule.mem_span_singleton, algebra.smul_def] }

@[simp] theorem mem_top {x : A} : x ∈ (⊤ : subalgebra R A) :=
subsemiring.subset_closure $ or.inr trivial

@[simp] theorem coe_top : ((⊤ : subalgebra R A) : submodule R A) = ⊤ :=
submodule.ext $ λ x, iff_of_true mem_top trivial

@[simp] theorem coe_bot : ((⊥ : subalgebra R A) : set A) = set.range (algebra_map R A) :=
by simp [set.ext_iff, algebra.mem_bot]

theorem eq_top_iff {S : subalgebra R A} :
  S = ⊤ ↔ ∀ x : A, x ∈ S :=
⟨λ h x, by rw h; exact mem_top, λ h, by ext x; exact ⟨λ _, mem_top, λ _, h x⟩⟩

@[simp] theorem map_top (f : A →ₐ[R] B) : subalgebra.map (⊤ : subalgebra R A) f = f.range :=
subalgebra.ext $ λ x,
  ⟨λ ⟨y, _, hy⟩, ⟨y, set.mem_univ _, hy⟩, λ ⟨y, mem, hy⟩, ⟨y, algebra.mem_top, hy⟩⟩

@[simp] theorem map_bot (f : A →ₐ[R] B) : subalgebra.map (⊥ : subalgebra R A) f = ⊥ :=
eq_bot_iff.2 $ λ x ⟨y, hy, hfy⟩, let ⟨r, hr⟩ := mem_bot.1 hy in subalgebra.range_le _
⟨r, by rwa [← f.commutes, hr]⟩

@[simp] theorem comap_top (f : A →ₐ[R] B) : subalgebra.comap' (⊤ : subalgebra R B) f = ⊤ :=
eq_top_iff.2 $ λ x, mem_top

/-- `alg_hom` to `⊤ : subalgebra R A`. -/
def to_top : A →ₐ[R] (⊤ : subalgebra R A) :=
by refine_struct { to_fun := λ x, (⟨x, mem_top⟩ : (⊤ : subalgebra R A)) }; intros; refl

theorem surjective_algebra_map_iff :
  function.surjective (algebra_map R A) ↔ (⊤ : subalgebra R A) = ⊥ :=
⟨λ h, eq_bot_iff.2 $ λ y _, let ⟨x, hx⟩ := h y in hx ▸ subalgebra.algebra_map_mem _ _,
λ h y, algebra.mem_bot.1 $ eq_bot_iff.1 h (algebra.mem_top : y ∈ _)⟩

theorem bijective_algebra_map_iff {R A : Type*} [field R] [semiring A] [nontrivial A] [algebra R A] :
  function.bijective (algebra_map R A) ↔ (⊤ : subalgebra R A) = ⊥ :=
⟨λ h, surjective_algebra_map_iff.1 h.2,
λ h, ⟨(algebra_map R A).injective, surjective_algebra_map_iff.2 h⟩⟩

/-- The bottom subalgebra is isomorphic to the base ring. -/
noncomputable def bot_equiv_of_injective (h : function.injective (algebra_map R A)) :
  (⊥ : subalgebra R A) ≃ₐ[R] R :=
alg_equiv.symm $ alg_equiv.of_bijective (algebra.of_id R _)
⟨λ x y hxy, h (congr_arg subtype.val hxy : _),
 λ ⟨y, hy⟩, let ⟨x, hx⟩ := algebra.mem_bot.1 hy in ⟨x, subtype.eq hx⟩⟩

/-- The bottom subalgebra is isomorphic to the field. -/
noncomputable def bot_equiv (F R : Type*) [field F] [semiring R] [nontrivial R] [algebra F R] :
  (⊥ : subalgebra F R) ≃ₐ[F] F :=
bot_equiv_of_injective (ring_hom.injective _)

end algebra

namespace subalgebra
open algebra

variables {R : Type u} {A : Type v}
variables [comm_semiring R] [semiring A] [algebra R A]
variables (S : subalgebra R A)

lemma range_val : S.val.range = S :=
ext $ set.ext_iff.1 $ S.val.coe_range.trans subtype.range_val

instance : unique (subalgebra R R) :=
{ uniq :=
  begin
    intro S,
    refine le_antisymm (λ r hr, _) bot_le,
    simp only [set.mem_range, coe_bot, id.map_eq_self, exists_apply_eq_apply, default],
  end
  .. algebra.inhabited }

end subalgebra

section nat

variables {R : Type*} [semiring R]

/-- A subsemiring is a `ℕ`-subalgebra. -/
def subalgebra_of_subsemiring (S : subsemiring R) : subalgebra ℕ R :=
{ algebra_map_mem' := λ i, S.coe_nat_mem i,
  .. S }

@[simp] lemma mem_subalgebra_of_subsemiring {x : R} {S : subsemiring R} :
  x ∈ subalgebra_of_subsemiring S ↔ x ∈ S :=
iff.rfl

end nat

section int

variables {R : Type*} [ring R]

/-- A subring is a `ℤ`-subalgebra. -/
def subalgebra_of_subring (S : subring R) : subalgebra ℤ R :=
{ algebra_map_mem' := λ i, int.induction_on i S.zero_mem
  (λ i ih, S.add_mem ih S.one_mem)
  (λ i ih, show ((-i - 1 : ℤ) : R) ∈ S, by { rw [int.cast_sub, int.cast_one],
    exact S.sub_mem ih S.one_mem }),
  .. S }

/-- A subset closed under the ring operations is a `ℤ`-subalgebra. -/
def subalgebra_of_is_subring (S : set R) [is_subring S] : subalgebra ℤ R :=
subalgebra_of_subring S.to_subring

variables {S : Type*} [semiring S]

@[simp] lemma mem_subalgebra_of_subring {x : R} {S : subring R} :
  x ∈ subalgebra_of_subring S ↔ x ∈ S :=
iff.rfl

@[simp] lemma mem_subalgebra_of_is_subring {x : R} {S : set R} [is_subring S] :
  x ∈ subalgebra_of_is_subring S ↔ x ∈ S :=
iff.rfl

end int
