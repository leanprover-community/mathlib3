/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Jireh Loreaux
-/
import algebra.star.star_alg_hom
import algebra.algebra.subalgebra.basic
import algebra.star.pointwise
import algebra.star.module
import ring_theory.adjoin.basic

/-!
# Star subalgebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

variables {F R A B C : Type*} [comm_semiring R] [star_ring R]
variables [semiring A] [star_ring A] [algebra R A] [star_module R A]
variables [semiring B] [star_ring B] [algebra R B] [star_module R B]
variables [semiring C] [star_ring C] [algebra R C] [star_module R C]

instance : set_like (star_subalgebra R A) A :=
⟨star_subalgebra.carrier, λ p q h, by cases p; cases q; congr'⟩

instance : star_mem_class (star_subalgebra R A) A :=
{ star_mem := λ s a, s.star_mem' }

instance : subsemiring_class (star_subalgebra R A) A :=
{ add_mem := add_mem',
  mul_mem := mul_mem',
  one_mem := one_mem',
  zero_mem := zero_mem' }

instance {R A} [comm_ring R] [star_ring R] [ring A] [star_ring A] [algebra R A] [star_module R A] :
  subring_class (star_subalgebra R A) A :=
{ neg_mem := λ s a ha, show -a ∈ s.to_subalgebra, from neg_mem ha }

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

lemma to_subalgebra_le_iff {S₁ S₂ : star_subalgebra R A} :
  S₁.to_subalgebra ≤ S₂.to_subalgebra ↔ S₁ ≤ S₂ := iff.rfl

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

/-- The inclusion map between `star_subalgebra`s given by `subtype.map id` as a `star_alg_hom`. -/
@[simps] def inclusion {S₁ S₂ : star_subalgebra R A} (h : S₁ ≤ S₂) : S₁ →⋆ₐ[R] S₂ :=
{ to_fun := subtype.map id h,
  map_one' := rfl,
  map_mul' := λ x y, rfl,
  map_zero' := rfl,
  map_add' := λ x y, rfl,
  commutes' := λ z, rfl,
  map_star' := λ x, rfl }

lemma inclusion_injective {S₁ S₂ : star_subalgebra R A} (h : S₁ ≤ S₂) :
  function.injective $ inclusion h :=
set.inclusion_injective h

@[simp] lemma subtype_comp_inclusion {S₁ S₂ : star_subalgebra R A} (h : S₁ ≤ S₂) :
  S₂.subtype.comp (inclusion h) = S₁.subtype :=
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

lemma _root_.set.star_mem_centralizer {a : A} {s : set A}
  (h : ∀ (a : A), a ∈ s → star a ∈ s) (ha : a ∈ set.centralizer s) :
  star a ∈ set.centralizer s :=
λ y hy, by simpa using congr_arg star (ha _ (h _ hy)).symm

/-- The centralizer, or commutant, of a *-closed set as star subalgebra. -/
def centralizer
  (s : set A) (w : ∀ (a : A), a ∈ s → star a ∈ s) : star_subalgebra R A :=
{ star_mem' := λ x, set.star_mem_centralizer w,
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

/-! ### The star closure of a subalgebra -/

namespace subalgebra

open_locale pointwise

variables {F R A B : Type*} [comm_semiring R] [star_ring R]
variables [semiring A] [algebra R A] [star_ring A] [star_module R A]
variables [semiring B] [algebra R B] [star_ring B] [star_module R B]

/-- The pointwise `star` of a subalgebra is a subalgebra. -/
instance : has_involutive_star (subalgebra R A) :=
{ star := λ S,
  { carrier := star S.carrier,
    mul_mem' := λ x y hx hy,
    begin
      simp only [set.mem_star, subalgebra.mem_carrier] at *,
      exact (star_mul x y).symm ▸ mul_mem hy hx,
    end,
    one_mem' := set.mem_star.mp ((star_one A).symm ▸ one_mem S : star (1 : A) ∈ S),
    add_mem' := λ x y hx hy,
    begin
      simp only [set.mem_star, subalgebra.mem_carrier] at *,
      exact (star_add x y).symm ▸ add_mem hx hy,
    end,
    zero_mem' := set.mem_star.mp ((star_zero A).symm ▸ zero_mem S : star (0 : A) ∈ S),
    algebra_map_mem' := λ r, by simpa only [set.mem_star, subalgebra.mem_carrier,
      ←algebra_map_star_comm] using S.algebra_map_mem (star r) },
  star_involutive := λ S, subalgebra.ext $ λ x, ⟨λ hx, (star_star x ▸ hx), λ hx,
    ((star_star x).symm ▸ hx : star (star x) ∈ S)⟩ }

@[simp] lemma mem_star_iff (S : subalgebra R A) (x : A) : x ∈ star S ↔ star x ∈ S := iff.rfl
@[simp] lemma star_mem_star_iff (S : subalgebra R A) (x : A) : star x ∈ star S ↔ x ∈ S :=
by simpa only [star_star] using mem_star_iff S (star x)
@[simp] lemma coe_star (S : subalgebra R A) : ((star S : subalgebra R A) : set A) = star S := rfl

lemma star_mono : monotone (star : subalgebra R A → subalgebra R A) := λ _ _ h _ hx, h hx

variables (R)

/-- The star operation on `subalgebra` commutes with `algebra.adjoin`. -/
lemma star_adjoin_comm (s : set A) : star (algebra.adjoin R s) = algebra.adjoin R (star s) :=
have this : ∀ t : set A, algebra.adjoin R (star t) ≤ star (algebra.adjoin R t),
  from λ t, algebra.adjoin_le (λ x hx, algebra.subset_adjoin hx),
le_antisymm (by simpa only [star_star] using subalgebra.star_mono (this (star s))) (this s)

variables {R}

/-- The `star_subalgebra` obtained from `S : subalgebra R A` by taking the smallest subalgebra
containing both `S` and `star S`. -/
@[simps] def star_closure (S : subalgebra R A) : star_subalgebra R A :=
{ star_mem' := λ a ha,
  begin
    simp only [subalgebra.mem_carrier, ←(@algebra.gi R A _ _ _).l_sup_u _ _] at *,
    rw [←mem_star_iff _ a, star_adjoin_comm],
    convert ha,
    simp [set.union_comm],
  end,
  .. S ⊔ star S }

lemma star_closure_le {S₁ : subalgebra R A} {S₂ : star_subalgebra R A} (h : S₁ ≤ S₂.to_subalgebra) :
  S₁.star_closure ≤ S₂ :=
star_subalgebra.to_subalgebra_le_iff.1 $ sup_le h $
  λ x hx, (star_star x ▸ star_mem (show star x ∈ S₂, from h $ (S₁.mem_star_iff _).1 hx) : x ∈ S₂)

lemma star_closure_le_iff {S₁ : subalgebra R A} {S₂ : star_subalgebra R A} :
  S₁.star_closure ≤ S₂ ↔ S₁ ≤ S₂.to_subalgebra :=
⟨λ h, le_sup_left.trans h, star_closure_le⟩

end subalgebra

/-! ### The star subalgebra generated by a set -/

namespace star_subalgebra

variables {F R A B : Type*} [comm_semiring R] [star_ring R]
variables [semiring A] [algebra R A] [star_ring A] [star_module R A]
variables [semiring B] [algebra R B] [star_ring B] [star_module R B]

variables (R)

/-- The minimal star subalgebra that contains `s`. -/
@[simps] def adjoin (s : set A) : star_subalgebra R A :=
{ star_mem' := λ x hx, by rwa [subalgebra.mem_carrier, ←subalgebra.mem_star_iff,
    subalgebra.star_adjoin_comm, set.union_star, star_star, set.union_comm],
  .. (algebra.adjoin R (s ∪ star s)) }

lemma adjoin_eq_star_closure_adjoin (s : set A) : adjoin R s = (algebra.adjoin R s).star_closure :=
to_subalgebra_injective $
  show algebra.adjoin R (s ∪ star s) = algebra.adjoin R s ⊔ star (algebra.adjoin R s),
  from (subalgebra.star_adjoin_comm R s).symm ▸ algebra.adjoin_union s (star s)

lemma adjoin_to_subalgebra (s : set A) :
  (adjoin R s).to_subalgebra = (algebra.adjoin R (s ∪ star s)) := rfl

lemma subset_adjoin (s : set A) : s ⊆ adjoin R s :=
  (set.subset_union_left s (star s)).trans algebra.subset_adjoin

lemma star_subset_adjoin (s : set A) : star s ⊆ adjoin R s :=
  (set.subset_union_right s (star s)).trans algebra.subset_adjoin

lemma self_mem_adjoin_singleton (x : A) : x ∈ adjoin R ({x} : set A) :=
algebra.subset_adjoin $ set.mem_union_left _ (set.mem_singleton x)

lemma star_self_mem_adjoin_singleton (x : A) : star x ∈ adjoin R ({x} : set A) :=
star_mem $ self_mem_adjoin_singleton R x

variables {R}

protected lemma gc : galois_connection (adjoin R : set A → star_subalgebra R A) coe :=
begin
  intros s S,
  rw [←to_subalgebra_le_iff, adjoin_to_subalgebra, algebra.adjoin_le_iff, coe_to_subalgebra],
  exact ⟨λ h, (set.subset_union_left s _).trans h,
    λ h, set.union_subset h $ λ x hx, star_star x ▸ star_mem (show star x ∈ S, from h hx)⟩,
end

/-- Galois insertion between `adjoin` and `coe`. -/
protected def gi : galois_insertion (adjoin R : set A → star_subalgebra R A) coe :=
{ choice := λ s hs, (adjoin R s).copy s $ le_antisymm (star_subalgebra.gc.le_u_l s) hs,
  gc := star_subalgebra.gc,
  le_l_u := λ S, (star_subalgebra.gc (S : set A) (adjoin R S)).1 $ le_rfl,
  choice_eq := λ _ _, star_subalgebra.copy_eq _ _ _ }

lemma adjoin_le {S : star_subalgebra R A} {s : set A} (hs : s ⊆ S) : adjoin R s ≤ S :=
star_subalgebra.gc.l_le hs

lemma adjoin_le_iff {S : star_subalgebra R A} {s : set A} : adjoin R s ≤ S ↔ s ⊆ S :=
star_subalgebra.gc _ _

lemma _root_.subalgebra.star_closure_eq_adjoin (S : subalgebra R A) :
  S.star_closure = adjoin R (S : set A) :=
le_antisymm (subalgebra.star_closure_le_iff.2 $ subset_adjoin R (S : set A))
  (adjoin_le (le_sup_left : S ≤ S ⊔ star S))

/-- If some predicate holds for all `x ∈ (s : set A)` and this predicate is closed under the
`algebra_map`, addition, multiplication and star operations, then it holds for `a ∈ adjoin R s`. -/
lemma adjoin_induction {s : set A} {p : A → Prop} {a : A} (h : a ∈ adjoin R s)
  (Hs : ∀ (x : A), x ∈ s → p x) (Halg : ∀ (r : R), p (algebra_map R A r))
  (Hadd : ∀ (x y : A), p x → p y → p (x + y)) (Hmul : ∀ (x y : A), p x → p y → p (x * y))
  (Hstar : ∀ (x : A), p x → p (star x)) : p a :=
algebra.adjoin_induction h (λ x hx, hx.elim (λ hx, Hs x hx) (λ hx, star_star x ▸ Hstar _ (Hs _ hx)))
  Halg Hadd Hmul

lemma adjoin_induction₂ {s : set A} {p : A → A → Prop} {a b : A} (ha : a ∈ adjoin R s)
  (hb : b ∈ adjoin R s) (Hs : ∀ (x : A), x ∈ s → ∀ (y : A), y ∈ s → p x y)
  (Halg : ∀ (r₁ r₂ : R), p (algebra_map R A r₁) (algebra_map R A r₂))
  (Halg_left : ∀ (r : R) (x : A), x ∈ s → p (algebra_map R A r) x)
  (Halg_right : ∀ (r : R) (x : A), x ∈ s → p x (algebra_map R A r))
  (Hadd_left : ∀ (x₁ x₂ y : A), p x₁ y → p x₂ y → p (x₁ + x₂) y)
  (Hadd_right : ∀ (x y₁ y₂ : A), p x y₁ → p x y₂ → p x (y₁ + y₂))
  (Hmul_left : ∀ (x₁ x₂ y : A), p x₁ y → p x₂ y → p (x₁ * x₂) y)
  (Hmul_right : ∀ (x y₁ y₂ : A), p x y₁ → p x y₂ → p x (y₁ * y₂))
  (Hstar : ∀ (x y : A), p x y → p (star x) (star y))
  (Hstar_left : ∀ (x y : A), p x y → p (star x) y)
  (Hstar_right : ∀ (x y : A), p x y → p x (star y)) : p a b :=
begin
  refine algebra.adjoin_induction₂ ha hb (λ x hx y hy, _) Halg (λ r x hx, _) (λ r x hx, _)
    Hadd_left Hadd_right Hmul_left Hmul_right,
  { cases hx; cases hy,
    exacts [Hs x hx y hy, star_star y ▸ Hstar_right _ _ (Hs _ hx _ hy),
      star_star x ▸ Hstar_left _ _ (Hs _ hx _ hy),
      star_star x ▸ star_star y ▸ Hstar _ _ (Hs _ hx _ hy)] },
  { cases hx, exacts [Halg_left _ _ hx, star_star x ▸ Hstar_right _ _ (Halg_left r _ hx)] },
  { cases hx, exacts [Halg_right _ _ hx, star_star x ▸ Hstar_left _ _ (Halg_right r _ hx)] },
end

/-- The difference with `star_subalgebra.adjoin_induction` is that this acts on the subtype. -/
lemma adjoin_induction' {s : set A} {p : adjoin R s → Prop} (a : adjoin R s)
  (Hs : ∀ x (h : x ∈ s), p ⟨x, subset_adjoin R s h⟩)
  (Halg : ∀ r, p (algebra_map R _ r)) (Hadd : ∀ x y, p x → p y → p (x + y))
  (Hmul : ∀ x y, p x → p y → p (x * y)) (Hstar : ∀ x, p x → p (star x)) : p a :=
subtype.rec_on a $ λ b hb,
begin
  refine exists.elim _ (λ (hb : b ∈ adjoin R s) (hc : p ⟨b, hb⟩), hc),
  apply adjoin_induction hb,
  exacts [λ x hx, ⟨subset_adjoin R s hx, Hs x hx⟩,
    λ r, ⟨star_subalgebra.algebra_map_mem _ r, Halg r⟩,
    (λ x y hx hy, exists.elim hx $ λ hx' hx,
      exists.elim hy $ λ hy' hy, ⟨add_mem hx' hy', Hadd _ _ hx hy⟩),
    (λ x y hx hy, exists.elim hx $ λ hx' hx,
      exists.elim hy $ λ hy' hy, ⟨mul_mem hx' hy', Hmul _ _ hx hy⟩),
    λ x hx, exists.elim hx (λ hx' hx, ⟨star_mem hx', Hstar _ hx⟩)]
end

variables (R)

/-- If all elements of `s : set A` commute pairwise and also commute pairwise with elements of
`star s`, then `star_subalgebra.adjoin R s` is commutative. See note [reducible non-instances]. -/
@[reducible]
def adjoin_comm_semiring_of_comm {s : set A}
  (hcomm : ∀ (a : A), a ∈ s → ∀ (b : A), b ∈ s → a * b = b * a)
  (hcomm_star : ∀ (a : A), a ∈ s → ∀ (b : A), b ∈ s → a * star b = star b * a) :
  comm_semiring (adjoin R s) :=
{ mul_comm :=
  begin
    rintro ⟨x, hx⟩ ⟨y, hy⟩,
    ext,
    simp only [set_like.coe_mk, mul_mem_class.mk_mul_mk],
    rw [←mem_to_subalgebra, adjoin_to_subalgebra] at hx hy,
    letI : comm_semiring (algebra.adjoin R (s ∪ star s)) := algebra.adjoin_comm_semiring_of_comm R
    begin
      intros a ha b hb,
      cases ha; cases hb,
      exacts [hcomm _ ha _ hb, star_star b ▸ hcomm_star _ ha _ hb,
        star_star a ▸ (hcomm_star _ hb _ ha).symm,
        by simpa only [star_mul, star_star] using congr_arg star (hcomm _ hb _ ha)],
    end,
    exact congr_arg coe (mul_comm (⟨x, hx⟩ : algebra.adjoin R (s ∪ star s)) ⟨y, hy⟩),
  end,
  ..(adjoin R s).to_subalgebra.to_semiring }

/-- If all elements of `s : set A` commute pairwise and also commute pairwise with elements of
`star s`, then `star_subalgebra.adjoin R s` is commutative. See note [reducible non-instances]. -/
@[reducible]
def adjoin_comm_ring_of_comm (R : Type u) {A : Type v} [comm_ring R] [star_ring R]
  [ring A] [algebra R A] [star_ring A] [star_module R A] {s : set A}
  (hcomm : ∀ (a : A), a ∈ s → ∀ (b : A), b ∈ s → a * b = b * a)
  (hcomm_star : ∀ (a : A), a ∈ s → ∀ (b : A), b ∈ s → a * star b = star b * a) :
  comm_ring (adjoin R s) :=
{ ..star_subalgebra.adjoin_comm_semiring_of_comm R hcomm hcomm_star,
  ..(adjoin R s).to_subalgebra.to_ring }

/-- The star subalgebra `star_subalgebra.adjoin R {x}` generated by a single `x : A` is commutative
if `x` is normal. -/
instance adjoin_comm_semiring_of_is_star_normal (x : A) [is_star_normal x] :
  comm_semiring (adjoin R ({x} : set A)) :=
adjoin_comm_semiring_of_comm R
  (λ a ha b hb, by { rw [set.mem_singleton_iff] at ha hb, rw [ha, hb] })
  (λ a ha b hb,
    by { rw [set.mem_singleton_iff] at ha hb, simpa only [ha, hb] using (star_comm_self' x).symm })

/-- The star subalgebra `star_subalgebra.adjoin R {x}` generated by a single `x : A` is commutative
if `x` is normal. -/
instance adjoin_comm_ring_of_is_star_normal (R : Type u) {A : Type v} [comm_ring R] [star_ring R]
  [ring A] [algebra R A] [star_ring A] [star_module R A]  (x : A) [is_star_normal x] :
  comm_ring (adjoin R ({x} : set A)) :=
{ mul_comm := mul_comm, ..(adjoin R ({x} : set A)).to_subalgebra.to_ring }

/-! ### Complete lattice structure -/

variables {F R A B}

instance : complete_lattice (star_subalgebra R A) :=
galois_insertion.lift_complete_lattice star_subalgebra.gi

instance : inhabited (star_subalgebra R A) := ⟨⊤⟩

@[simp]
lemma coe_top : (↑(⊤ : star_subalgebra R A) : set A) = set.univ := rfl

@[simp] lemma mem_top {x : A} : x ∈ (⊤ : star_subalgebra R A) :=
set.mem_univ x

@[simp] lemma top_to_subalgebra : (⊤ : star_subalgebra R A).to_subalgebra = ⊤ := rfl

@[simp] lemma to_subalgebra_eq_top {S : star_subalgebra R A} : S.to_subalgebra = ⊤ ↔ S = ⊤ :=
star_subalgebra.to_subalgebra_injective.eq_iff' top_to_subalgebra

lemma mem_sup_left {S T : star_subalgebra R A} : ∀ {x : A}, x ∈ S → x ∈ S ⊔ T :=
show S ≤ S ⊔ T, from le_sup_left

lemma mem_sup_right {S T : star_subalgebra R A} : ∀ {x : A}, x ∈ T → x ∈ S ⊔ T :=
show T ≤ S ⊔ T, from le_sup_right

lemma mul_mem_sup {S T : star_subalgebra R A} {x y : A} (hx : x ∈ S) (hy : y ∈ T) :
  x * y ∈ S ⊔ T :=
mul_mem (mem_sup_left hx) (mem_sup_right hy)

lemma map_sup (f : A →⋆ₐ[R] B) (S T : star_subalgebra R A) : map f (S ⊔ T) = map f S ⊔ map f T :=
(star_subalgebra.gc_map_comap f).l_sup

@[simp, norm_cast]
lemma coe_inf (S T : star_subalgebra R A) : (↑(S ⊓ T) : set A) = S ∩ T := rfl

@[simp]
lemma mem_inf {S T : star_subalgebra R A} {x : A} : x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T := iff.rfl

@[simp] lemma inf_to_subalgebra (S T : star_subalgebra R A) :
  (S ⊓ T).to_subalgebra = S.to_subalgebra ⊓ T.to_subalgebra := rfl

@[simp, norm_cast]
lemma coe_Inf (S : set (star_subalgebra R A)) : (↑(Inf S) : set A) = ⋂ s ∈ S, ↑s := Inf_image

lemma mem_Inf {S : set (star_subalgebra R A)} {x : A} : x ∈ Inf S ↔ ∀ p ∈ S, x ∈ p :=
by simp only [← set_like.mem_coe, coe_Inf, set.mem_Inter₂]

@[simp] lemma Inf_to_subalgebra (S : set (star_subalgebra R A)) :
  (Inf S).to_subalgebra = Inf (star_subalgebra.to_subalgebra '' S) :=
set_like.coe_injective $ by simp

@[simp, norm_cast]
lemma coe_infi {ι : Sort*} {S : ι → star_subalgebra R A} : (↑(⨅ i, S i) : set A) = ⋂ i, S i :=
by simp [infi]

lemma mem_infi {ι : Sort*} {S : ι → star_subalgebra R A} {x : A} : (x ∈ ⨅ i, S i) ↔ ∀ i, x ∈ S i :=
by simp only [infi, mem_Inf, set.forall_range_iff]

@[simp] lemma infi_to_subalgebra {ι : Sort*} (S : ι → star_subalgebra R A) :
  (⨅ i, S i).to_subalgebra = ⨅ i, (S i).to_subalgebra :=
set_like.coe_injective $ by simp

lemma bot_to_subalgebra : (⊥ : star_subalgebra R A).to_subalgebra = ⊥ :=
by { change algebra.adjoin R (∅ ∪ star ∅) = algebra.adjoin R ∅, simp }

theorem mem_bot {x : A} : x ∈ (⊥ : star_subalgebra R A) ↔ x ∈ set.range (algebra_map R A) :=
by rw [←mem_to_subalgebra, bot_to_subalgebra, algebra.mem_bot]

@[simp] theorem coe_bot : ((⊥ : star_subalgebra R A) : set A) = set.range (algebra_map R A) :=
by simp [set.ext_iff, mem_bot]

theorem eq_top_iff {S : star_subalgebra R A} :
  S = ⊤ ↔ ∀ x : A, x ∈ S :=
⟨λ h x, by rw h; exact mem_top, λ h, by ext x; exact ⟨λ _, mem_top, λ _, h x⟩⟩

end star_subalgebra

namespace star_alg_hom
open star_subalgebra

variables {F R A B : Type*} [comm_semiring R] [star_ring R]
variables [semiring A] [algebra R A] [star_ring A] [star_module R A]
variables [semiring B] [algebra R B] [star_ring B]
variables [hF : star_alg_hom_class F R A B] (f g : F)

include hF

/-- The equalizer of two star `R`-algebra homomorphisms. -/
def equalizer : star_subalgebra R A :=
{ carrier := {a | f a = g a},
  mul_mem' := λ a b (ha : f a = g a) (hb : f b = g b),
    by rw [set.mem_set_of_eq, map_mul f, map_mul g, ha, hb],
  add_mem' := λ a b (ha : f a = g a) (hb : f b = g b),
    by rw [set.mem_set_of_eq, map_add f, map_add g, ha, hb],
  algebra_map_mem' := λ r, by simp only [set.mem_set_of_eq, alg_hom_class.commutes],
  star_mem' := λ a (ha : f a = g a), by rw [set.mem_set_of_eq, map_star f, map_star g, ha] }

@[simp] lemma mem_equalizer (x : A) : x ∈ star_alg_hom.equalizer f g ↔ f x = g x := iff.rfl

lemma adjoin_le_equalizer {s : set A} (h : s.eq_on f g) : adjoin R s ≤ star_alg_hom.equalizer f g :=
adjoin_le h

lemma ext_of_adjoin_eq_top {s : set A}
  (h : adjoin R s = ⊤) ⦃f g : F⦄ (hs : s.eq_on f g) : f = g :=
fun_like.ext f g $ λ x, star_alg_hom.adjoin_le_equalizer f g hs $ h.symm ▸ trivial

omit hF

lemma map_adjoin [star_module R B] (f : A →⋆ₐ[R] B) (s : set A) :
  map f (adjoin R s) = adjoin R (f '' s) :=
galois_connection.l_comm_of_u_comm set.image_preimage (gc_map_comap f) star_subalgebra.gc
  star_subalgebra.gc (λ _, rfl)

lemma ext_adjoin {s : set A} [star_alg_hom_class F R (adjoin R s) B] {f g : F}
  (h : ∀ x : adjoin R s, (x : A) ∈ s → f x = g x) : f = g :=
begin
  refine fun_like.ext f g (λ a, adjoin_induction' a (λ x hx, _) (λ r, _) (λ x y hx hy, _)
    (λ x y hx hy, _) (λ x hx, _)),
  { exact h ⟨x, subset_adjoin R s hx⟩ hx },
  { simp only [alg_hom_class.commutes] },
  { rw [map_add, map_add, hx, hy] },
  { rw [map_mul, map_mul, hx, hy] },
  { rw [map_star, map_star, hx] },
end

lemma ext_adjoin_singleton {a : A} [star_alg_hom_class F R (adjoin R ({a} : set A)) B] {f g : F}
  (h : f ⟨a, self_mem_adjoin_singleton R a⟩ = g ⟨a, self_mem_adjoin_singleton R a⟩) : f = g :=
ext_adjoin $ λ x hx, (show x = ⟨a, self_mem_adjoin_singleton R a⟩,
  from subtype.ext $ set.mem_singleton_iff.mp hx).symm ▸ h

end star_alg_hom
