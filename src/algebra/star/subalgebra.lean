/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.star.star_alg_hom
import algebra.algebra.subalgebra.basic

/-!
# Star subalgebras

A *-subalgebra is a subalgebra of a *-algebra which is closed under *.

The centralizer of a *-closed set is a *-subalgebra.
-/

universes u v

set_option old_structure_cmd true

/-- A *-subalgebra is a subalgebra of a *-algebra which is closed under *. -/
structure star_subalgebra (R : Type u) (A : Type v) [comm_semiring R] [star_ring R]
  [semiring A] [star_ring A] [algebra R A] [star_module R A] extends subalgebra R A : Type v :=
(star_mem' {a} : a ∈ carrier → star a ∈ carrier)

namespace star_subalgebra

/--
Forgetting that a *-subalgebra is closed under *.
-/
add_decl_doc star_subalgebra.to_subalgebra

variables {R A B C : Type*} [comm_semiring R] [star_ring R]
variables [semiring A] [star_ring A] [algebra R A] [star_module R A]
variables [semiring B] [star_ring B] [algebra R B] [star_module R B]
variables [semiring C] [star_ring C] [algebra R C] [star_module R C]

instance : set_like (star_subalgebra R A) A :=
⟨star_subalgebra.carrier, λ p q h, by cases p; cases q; congr'⟩

instance : has_top (star_subalgebra R A) :=
⟨{ star_mem' := by tidy, ..(⊤ : subalgebra R A) }⟩

instance : inhabited (star_subalgebra R A) := ⟨⊤⟩

instance : star_mem_class (star_subalgebra R A) A :=
{ star_mem := λ s a, s.star_mem' }

instance : subsemiring_class (star_subalgebra R A) A :=
{ add_mem := add_mem',
  mul_mem := mul_mem',
  one_mem := one_mem',
  zero_mem := zero_mem' }

-- this uses the `has_star` instance `s` inherits from `star_mem_class (star_subalgebra R A) A`
instance (s : star_subalgebra R A) : star_ring s :=
{ star := star,
  star_involutive := λ r, subtype.ext (star_star r),
  star_mul := λ r₁ r₂, subtype.ext (star_mul r₁ r₂),
  star_add := λ r₁ r₂, subtype.ext (star_add r₁ r₂) }

instance (s : star_subalgebra R A) : algebra R s := s.to_subalgebra.algebra'

instance (s : star_subalgebra R A) : star_module R s :=
{ star_smul := λ r a, subtype.ext (star_smul r a) }

@[simp]
lemma mem_carrier {s : star_subalgebra R A} {x : A} : x ∈ s.carrier ↔ x ∈ s := iff.rfl

@[ext] theorem ext {S T : star_subalgebra R A} (h : ∀ x : A, x ∈ S ↔ x ∈ T) : S = T :=
set_like.ext h

@[simp] lemma mem_to_subalgebra {S : star_subalgebra R A} {x} : x ∈ S.to_subalgebra ↔ x ∈ S :=
iff.rfl

@[simp] lemma coe_to_subalgebra (S : star_subalgebra R A) : (S.to_subalgebra : set A) = S := rfl

theorem to_subalgebra_injective :
  function.injective (to_subalgebra : star_subalgebra R A → subalgebra R A) :=
λ S T h, ext $ λ x, by rw [← mem_to_subalgebra, ← mem_to_subalgebra, h]

theorem to_subalgebra_inj {S U : star_subalgebra R A} : S.to_subalgebra = U.to_subalgebra ↔ S = U :=
to_subalgebra_injective.eq_iff

/-- Copy of a star subalgebra with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (S : star_subalgebra R A) (s : set A) (hs : s = ↑S) : star_subalgebra R A :=
{ carrier := s,
  add_mem' := λ _ _, hs.symm ▸ S.add_mem',
  mul_mem' := λ _ _, hs.symm ▸ S.mul_mem',
  algebra_map_mem' := hs.symm ▸ S.algebra_map_mem',
  star_mem' := λ _, hs.symm ▸ S.star_mem' }

@[simp] lemma coe_copy (S : star_subalgebra R A) (s : set A) (hs : s = ↑S) :
  (S.copy s hs : set A) = s := rfl

lemma copy_eq (S : star_subalgebra R A) (s : set A) (hs : s = ↑S) : S.copy s hs = S :=
set_like.coe_injective hs

variables (S : star_subalgebra R A)

theorem algebra_map_mem (r : R) : algebra_map R A r ∈ S :=
S.algebra_map_mem' r

theorem srange_le : (algebra_map R A).srange ≤ S.to_subalgebra.to_subsemiring :=
λ x ⟨r, hr⟩, hr ▸ S.algebra_map_mem r

theorem range_subset : set.range (algebra_map R A) ⊆ S :=
λ x ⟨r, hr⟩, hr ▸ S.algebra_map_mem r

theorem range_le : set.range (algebra_map R A) ≤ S :=
S.range_subset

protected theorem smul_mem {x : A} (hx : x ∈ S) (r : R) : r • x ∈ S :=
(algebra.smul_def r x).symm ▸ mul_mem (S.algebra_map_mem r) hx

/-- Embedding of a subalgebra into the algebra. -/
def subtype : S →⋆ₐ[R] A :=
by refine_struct { to_fun := (coe : S → A) }; intros; refl

@[simp] lemma coe_subtype : (S.subtype : S → A) = coe := rfl

lemma subtype_apply (x : S) : S.subtype x = (x : A) := rfl

@[simp] lemma to_subalgebra_subtype : S.to_subalgebra.val = S.subtype.to_alg_hom :=
rfl

section map

/-- Transport a star subalgebra via a star algebra homomorphism. -/
def map (f : A →⋆ₐ[R] B) (S : star_subalgebra R A) : star_subalgebra R B :=
{ star_mem' :=
  begin
    rintro _ ⟨a, ha, rfl⟩,
    exact map_star f a ▸ set.mem_image_of_mem _ (S.star_mem' ha),
  end,
  .. S.to_subalgebra.map f.to_alg_hom }

lemma map_mono {S₁ S₂ : star_subalgebra R A} {f : A →⋆ₐ[R] B} :
  S₁ ≤ S₂ → S₁.map f ≤ S₂.map f :=
set.image_subset f

lemma map_injective {f : A →⋆ₐ[R] B} (hf : function.injective f) :
  function.injective (map f) :=
λ S₁ S₂ ih, ext $ set.ext_iff.1 $ set.image_injective.2 hf $ set.ext $ set_like.ext_iff.mp ih

@[simp] lemma map_id (S : star_subalgebra R A) : S.map (star_alg_hom.id R A) = S :=
set_like.coe_injective $ set.image_id _

lemma map_map (S : star_subalgebra R A) (g : B →⋆ₐ[R] C) (f : A →⋆ₐ[R] B) :
  (S.map f).map g = S.map (g.comp f) :=
set_like.coe_injective $ set.image_image _ _ _

lemma mem_map {S : star_subalgebra R A} {f : A →⋆ₐ[R] B} {y : B} :
  y ∈ map f S ↔ ∃ x ∈ S, f x = y :=
subsemiring.mem_map

lemma map_to_subalgebra {S : star_subalgebra R A} {f : A →⋆ₐ[R] B} :
  (S.map f).to_subalgebra = S.to_subalgebra.map f.to_alg_hom :=
set_like.coe_injective rfl

@[simp] lemma coe_map (S : star_subalgebra R A) (f : A →⋆ₐ[R] B) :
  (S.map f : set B) = f '' S :=
rfl

/-- Preimage of a star subalgebra under an star algebra homomorphism. -/
def comap (f : A →⋆ₐ[R] B) (S : star_subalgebra R B) : star_subalgebra R A :=
{ star_mem' := λ a ha, show f (star a) ∈ S, from (map_star f a).symm ▸ star_mem ha,
  .. S.to_subalgebra.comap f.to_alg_hom }

theorem map_le_iff_le_comap {S : star_subalgebra R A} {f : A →⋆ₐ[R] B} {U : star_subalgebra R B} :
  map f S ≤ U ↔ S ≤ comap f U :=
set.image_subset_iff

lemma gc_map_comap (f : A →⋆ₐ[R] B) : galois_connection (map f) (comap f) :=
λ S U, map_le_iff_le_comap

lemma comap_mono {S₁ S₂ : star_subalgebra R B} {f : A →⋆ₐ[R] B} :
  S₁ ≤ S₂ → S₁.comap f ≤ S₂.comap f :=
set.preimage_mono

lemma comap_injective {f : A →⋆ₐ[R] B} (hf : function.surjective f) :
  function.injective (comap f) :=
λ S₁ S₂ h, ext $ λ b, let ⟨x, hx⟩ := hf b in let this := set_like.ext_iff.1 h x in hx ▸ this

@[simp] lemma comap_id (S : star_subalgebra R A) : S.comap (star_alg_hom.id R A) = S :=
set_like.coe_injective $ set.preimage_id

lemma comap_comap (S : star_subalgebra R C) (g : B →⋆ₐ[R] C) (f : A →⋆ₐ[R] B) :
  (S.comap g).comap f = S.comap (g.comp f) :=
set_like.coe_injective $ set.preimage_preimage

@[simp] lemma mem_comap (S : star_subalgebra R B) (f : A →⋆ₐ[R] B) (x : A) :
  x ∈ S.comap f ↔ f x ∈ S :=
iff.rfl

@[simp, norm_cast] lemma coe_comap (S : star_subalgebra R B) (f : A →⋆ₐ[R] B) :
  (S.comap f : set A) = f ⁻¹' (S : set B) :=
rfl

end map

section centralizer
variables (R) {A}

/-- The centralizer, or commutant, of a *-closed set as star subalgebra. -/
def centralizer
  (s : set A) (w : ∀ (a : A), a ∈ s → star a ∈ s) : star_subalgebra R A :=
{ star_mem' := λ x xm y hy, by simpa using congr_arg star (xm _ (w _ hy)).symm,
  ..subalgebra.centralizer R s, }

@[simp]
lemma coe_centralizer (s : set A) (w : ∀ (a : A), a ∈ s → star a ∈ s) :
  (centralizer R s w : set A) = s.centralizer := rfl

lemma mem_centralizer_iff {s : set A} {w} {z : A} :
  z ∈ centralizer R s w ↔ ∀ g ∈ s, g * z = z * g :=
iff.rfl

lemma centralizer_le (s t : set A)
  (ws : ∀ (a : A), a ∈ s → star a ∈ s) (wt : ∀ (a : A), a ∈ t → star a ∈ t) (h : s ⊆ t) :
  centralizer R t wt ≤ centralizer R s ws :=
set.centralizer_subset h

end centralizer

end star_subalgebra
