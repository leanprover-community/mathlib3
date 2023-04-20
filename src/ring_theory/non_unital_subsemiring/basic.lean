/-
Copyright (c) 2022 Jireh Loreaux All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/

import algebra.ring.equiv
import algebra.ring.prod
import data.set.finite
import group_theory.submonoid.membership
import group_theory.subsemigroup.membership
import group_theory.subsemigroup.centralizer

/-!
# Bundled non-unital subsemirings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define bundled non-unital subsemirings and some standard constructions:
`complete_lattice` structure, `subtype` and `inclusion` ring homomorphisms, non-unital subsemiring
`map`, `comap` and range (`srange`) of a `non_unital_ring_hom` etc.
-/

open_locale big_operators

universes u v w

variables {R : Type u} {S : Type v} {T : Type w} [non_unital_non_assoc_semiring R]
  (M : subsemigroup R)

/-- `non_unital_subsemiring_class S R` states that `S` is a type of subsets `s ⊆ R` that
are both an additive submonoid and also a multiplicative subsemigroup. -/
class non_unital_subsemiring_class (S : Type*) (R : Type u)
  [non_unital_non_assoc_semiring R] [set_like S R] extends add_submonoid_class S R :=
(mul_mem : ∀ {s : S} {a b : R}, a ∈ s → b ∈ s → a * b ∈ s)

@[priority 100] -- See note [lower instance priority]
instance non_unital_subsemiring_class.mul_mem_class (S : Type*) (R : Type u)
  [non_unital_non_assoc_semiring R] [set_like S R] [h : non_unital_subsemiring_class S R] :
  mul_mem_class S R :=
{ .. h }

namespace non_unital_subsemiring_class

variables [set_like S R] [non_unital_subsemiring_class S R] (s : S)
include R S

open add_submonoid_class

/-- A non-unital subsemiring of a `non_unital_non_assoc_semiring` inherits a
`non_unital_non_assoc_semiring` structure -/
@[priority 75] /- Prefer subclasses of `non_unital_non_assoc_semiring` over subclasses of
`non_unital_subsemiring_class`. -/
instance to_non_unital_non_assoc_semiring : non_unital_non_assoc_semiring s :=
subtype.coe_injective.non_unital_non_assoc_semiring coe rfl (by simp) (λ _ _, rfl) (λ _ _, rfl)

instance no_zero_divisors [no_zero_divisors R] : no_zero_divisors s :=
subtype.coe_injective.no_zero_divisors coe rfl (λ x y, rfl)

/-- The natural non-unital ring hom from a non-unital subsemiring of a non-unital semiring `R` to
`R`. -/
def subtype : s →ₙ+* R :=
{ to_fun := coe, .. add_submonoid_class.subtype s, .. mul_mem_class.subtype s }

@[simp] theorem coe_subtype : (subtype s : s → R) = coe := rfl

omit R S

/-- A non-unital subsemiring of a `non_unital_semiring` is a `non_unital_semiring`. -/
instance to_non_unital_semiring {R} [non_unital_semiring R] [set_like S R]
  [non_unital_subsemiring_class S R] : non_unital_semiring s :=
subtype.coe_injective.non_unital_semiring coe rfl (by simp) (λ _ _, rfl) (λ _ _, rfl)

/-- A non-unital subsemiring of a `non_unital_comm_semiring` is a `non_unital_comm_semiring`. -/
instance to_non_unital_comm_semiring {R} [non_unital_comm_semiring R] [set_like S R]
  [non_unital_subsemiring_class S R] : non_unital_comm_semiring s :=
subtype.coe_injective.non_unital_comm_semiring coe rfl (by simp) (λ _ _, rfl) (λ _ _, rfl)

/-! Note: currently, there are no ordered versions of non-unital rings. -/

end non_unital_subsemiring_class

variables [non_unital_non_assoc_semiring S] [non_unital_non_assoc_semiring T]

set_option old_structure_cmd true

/-- A non-unital subsemiring of a non-unital semiring `R` is a subset `s` that is both an additive
submonoid and a semigroup. -/
structure non_unital_subsemiring (R : Type u) [non_unital_non_assoc_semiring R]
  extends add_submonoid R, subsemigroup R

/-- Reinterpret a `non_unital_subsemiring` as a `subsemigroup`. -/
add_decl_doc non_unital_subsemiring.to_subsemigroup

/-- Reinterpret a `non_unital_subsemiring` as an `add_submonoid`. -/
add_decl_doc non_unital_subsemiring.to_add_submonoid

namespace non_unital_subsemiring

instance : set_like (non_unital_subsemiring R) R :=
{ coe := non_unital_subsemiring.carrier,
  coe_injective' := λ p q h, by cases p; cases q; congr' }

instance : non_unital_subsemiring_class (non_unital_subsemiring R) R :=
{ zero_mem := zero_mem',
  add_mem := add_mem',
  mul_mem := mul_mem' }

@[simp]
lemma mem_carrier {s : non_unital_subsemiring R} {x : R} : x ∈ s.carrier ↔ x ∈ s := iff.rfl

/-- Two non-unital subsemirings are equal if they have the same elements. -/
@[ext] theorem ext {S T : non_unital_subsemiring R} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
set_like.ext h

/-- Copy of a non-unital subsemiring with a new `carrier` equal to the old one. Useful to fix
definitional equalities.-/
protected def copy (S : non_unital_subsemiring R) (s : set R) (hs : s = ↑S) :
  non_unital_subsemiring R :=
{ carrier := s,
  ..S.to_add_submonoid.copy s hs,
  ..S.to_subsemigroup.copy s hs }

@[simp] lemma coe_copy (S : non_unital_subsemiring R) (s : set R) (hs : s = ↑S) :
  (S.copy s hs : set R) = s := rfl

lemma copy_eq (S : non_unital_subsemiring R) (s : set R) (hs : s = ↑S) : S.copy s hs = S :=
set_like.coe_injective hs

lemma to_subsemigroup_injective :
  function.injective (to_subsemigroup : non_unital_subsemiring R → subsemigroup R)
| r s h := ext (set_like.ext_iff.mp h : _)

@[mono] lemma to_subsemigroup_strict_mono :
  strict_mono (to_subsemigroup : non_unital_subsemiring R → subsemigroup R) :=
λ _ _, id

@[mono] lemma to_subsemigroup_mono :
  monotone (to_subsemigroup : non_unital_subsemiring R → subsemigroup R) :=
to_subsemigroup_strict_mono.monotone

lemma to_add_submonoid_injective :
  function.injective (to_add_submonoid : non_unital_subsemiring R → add_submonoid R)
| r s h := ext (set_like.ext_iff.mp h : _)

@[mono] lemma to_add_submonoid_strict_mono :
  strict_mono (to_add_submonoid : non_unital_subsemiring R → add_submonoid R) := λ _ _, id

@[mono]
lemma to_add_submonoid_mono :
  monotone (to_add_submonoid : non_unital_subsemiring R → add_submonoid R) :=
to_add_submonoid_strict_mono.monotone

/-- Construct a `non_unital_subsemiring R` from a set `s`, a subsemigroup `sg`, and an additive
submonoid `sa` such that `x ∈ s ↔ x ∈ sg ↔ x ∈ sa`. -/
protected def mk' (s : set R) (sg : subsemigroup R) (hg : ↑sg = s)
  (sa : add_submonoid R) (ha : ↑sa = s) :
  non_unital_subsemiring R :=
{ carrier := s,
  zero_mem' := ha ▸ sa.zero_mem,
  add_mem' := λ x y, by simpa only [← ha] using sa.add_mem,
  mul_mem' := λ x y, by simpa only [← hg] using sg.mul_mem }

@[simp] lemma coe_mk' {s : set R} {sg : subsemigroup R} (hg : ↑sg = s)
  {sa : add_submonoid R} (ha : ↑sa = s) :
  (non_unital_subsemiring.mk' s sg hg sa ha : set R) = s := rfl

@[simp] lemma mem_mk' {s : set R} {sg : subsemigroup R} (hg : ↑sg = s)
  {sa : add_submonoid R} (ha : ↑sa = s) {x : R} :
  x ∈ non_unital_subsemiring.mk' s sg hg sa ha ↔ x ∈ s :=
iff.rfl

@[simp] lemma mk'_to_subsemigroup {s : set R} {sg : subsemigroup R} (hg : ↑sg = s)
  {sa : add_submonoid R} (ha : ↑sa = s) :
  (non_unital_subsemiring.mk' s sg hg sa ha).to_subsemigroup = sg :=
set_like.coe_injective hg.symm

@[simp] lemma mk'_to_add_submonoid {s : set R} {sg : subsemigroup R} (hg : ↑sg = s)
  {sa : add_submonoid R} (ha : ↑sa  =s) :
  (non_unital_subsemiring.mk' s sg hg sa ha).to_add_submonoid = sa :=
set_like.coe_injective ha.symm

end non_unital_subsemiring

namespace non_unital_subsemiring

variables {F G : Type*} [non_unital_ring_hom_class F R S] [non_unital_ring_hom_class G S T]
  (s : non_unital_subsemiring R)

@[simp, norm_cast] lemma coe_zero : ((0 : s) : R) = (0 : R) := rfl
@[simp, norm_cast] lemma coe_add (x y : s) : ((x + y : s) : R) = (x + y : R) := rfl
@[simp, norm_cast] lemma coe_mul (x y : s) : ((x * y : s) : R) = (x * y : R) := rfl

/-! Note: currently, there are no ordered versions of non-unital rings. -/

@[simp] lemma mem_to_subsemigroup {s : non_unital_subsemiring R} {x : R} :
  x ∈ s.to_subsemigroup ↔ x ∈ s := iff.rfl
@[simp] lemma coe_to_subsemigroup (s : non_unital_subsemiring R) :
  (s.to_subsemigroup : set R) = s := rfl
@[simp] lemma mem_to_add_submonoid {s : non_unital_subsemiring R} {x : R} :
  x ∈ s.to_add_submonoid ↔ x ∈ s := iff.rfl
@[simp] lemma coe_to_add_submonoid (s : non_unital_subsemiring R) :
  (s.to_add_submonoid : set R) = s := rfl

/-- The non-unital subsemiring `R` of the non-unital semiring `R`. -/
instance : has_top (non_unital_subsemiring R) :=
⟨{ .. (⊤ : subsemigroup R), .. (⊤ : add_submonoid R) }⟩

@[simp] lemma mem_top (x : R) : x ∈ (⊤ : non_unital_subsemiring R) := set.mem_univ x

@[simp] lemma coe_top : ((⊤ : non_unital_subsemiring R) : set R) = set.univ := rfl

/-- The preimage of a non-unital subsemiring along a non-unital ring homomorphism is a
non-unital subsemiring. -/
def comap (f : F) (s : non_unital_subsemiring S) : non_unital_subsemiring R :=
{ carrier := f ⁻¹' s,
  .. s.to_subsemigroup.comap (f : mul_hom R S), .. s.to_add_submonoid.comap (f : R →+ S) }

@[simp] lemma coe_comap (s : non_unital_subsemiring S) (f : F) :
  (s.comap f : set R) = f ⁻¹' s := rfl

@[simp]
lemma mem_comap {s : non_unital_subsemiring S} {f : F} {x : R} :
  x ∈ s.comap f ↔ f x ∈ s := iff.rfl

-- this has some nasty coercions, how to deal with it?
lemma comap_comap (s : non_unital_subsemiring T) (g : G) (f : F) :
  ((s.comap g : non_unital_subsemiring S).comap f : non_unital_subsemiring R) =
  s.comap ((g : S →ₙ+* T).comp (f : R →ₙ+* S)) :=
rfl

/-- The image of a non-unital subsemiring along a ring homomorphism is a non-unital subsemiring. -/
def map (f : F) (s : non_unital_subsemiring R) : non_unital_subsemiring S :=
{ carrier := f '' s,
  .. s.to_subsemigroup.map (f : R →ₙ* S), .. s.to_add_submonoid.map (f : R →+ S) }

@[simp] lemma coe_map (f : F) (s : non_unital_subsemiring R) : (s.map f : set S) = f '' s := rfl

@[simp] lemma mem_map {f : F} {s : non_unital_subsemiring R} {y : S} :
  y ∈ s.map f ↔ ∃ x ∈ s, f x = y :=
set.mem_image_iff_bex

@[simp] lemma map_id : s.map (non_unital_ring_hom.id R) = s :=
set_like.coe_injective $ set.image_id _

-- unavoidable coercions?
lemma map_map (g : G) (f : F) :
  (s.map (f : R →ₙ+* S)).map (g : S →ₙ+* T) = s.map ((g : S →ₙ+* T).comp (f : R →ₙ+* S)) :=
set_like.coe_injective $ set.image_image _ _ _

lemma map_le_iff_le_comap {f : F} {s : non_unital_subsemiring R} {t : non_unital_subsemiring S} :
  s.map f ≤ t ↔ s ≤ t.comap f :=
set.image_subset_iff

lemma gc_map_comap (f : F) :
  @galois_connection (non_unital_subsemiring R) (non_unital_subsemiring S) _ _ (map f) (comap f) :=
λ S T, map_le_iff_le_comap
/-- A non-unital subsemiring is isomorphic to its image under an injective function -/

noncomputable def equiv_map_of_injective
  (f : F) (hf : function.injective (f : R → S)) : s ≃+* s.map f :=
{ map_mul' := λ _ _, subtype.ext (map_mul f _ _),
  map_add' := λ _ _, subtype.ext (map_add f _ _),
  ..equiv.set.image f s hf }

@[simp] lemma coe_equiv_map_of_injective_apply
  (f : F) (hf : function.injective f) (x : s) :
  (equiv_map_of_injective s f hf x : S) = f x := rfl

end non_unital_subsemiring

namespace non_unital_ring_hom

open non_unital_subsemiring

variables {F G : Type*} [non_unital_ring_hom_class F R S] [non_unital_ring_hom_class G S T]
  (f : F) (g : G)

/-- The range of a non-unital ring homomorphism is a non-unital subsemiring.
See note [range copy pattern]. -/
def srange : non_unital_subsemiring S :=
((⊤ : non_unital_subsemiring R).map (f : R →ₙ+* S)).copy (set.range f) set.image_univ.symm

@[simp] lemma coe_srange : (@srange R S _ _ _ _ f : set S) = set.range f := rfl

@[simp] lemma mem_srange {f : F} {y : S} : y ∈ (@srange R S _ _ _ _ f) ↔ ∃ x, f x = y :=
iff.rfl

lemma srange_eq_map : @srange R S _ _ _ _ f = (⊤ : non_unital_subsemiring R).map f :=
by { ext, simp }

lemma mem_srange_self (f : F) (x : R) : f x ∈ @srange R S _ _ _ _ f :=
mem_srange.mpr ⟨x, rfl⟩

lemma map_srange (g : S →ₙ+* T) (f : R →ₙ+* S) : map g (srange f) = srange (g.comp f) :=
by simpa only [srange_eq_map] using (⊤ : non_unital_subsemiring R).map_map g f

/-- The range of a morphism of non-unital semirings is finite if the domain is a finite. -/
instance finite_srange [finite R] (f : F) : finite (srange f : non_unital_subsemiring S) :=
(set.finite_range f).to_subtype

end non_unital_ring_hom

namespace non_unital_subsemiring

-- should we define this as the range of the zero homomorphism?
instance : has_bot (non_unital_subsemiring R) :=
⟨{ carrier := {0},
   add_mem' := λ _ _ _ _, by simp * at *,
   zero_mem' := set.mem_singleton 0,
   mul_mem' := λ _ _ _ _, by simp * at *}⟩

instance : inhabited (non_unital_subsemiring R) := ⟨⊥⟩

lemma coe_bot : ((⊥ : non_unital_subsemiring R) : set R) = {0} := rfl

lemma mem_bot {x : R} : x ∈ (⊥ : non_unital_subsemiring R) ↔ x = 0 := set.mem_singleton_iff

/-- The inf of two non-unital subsemirings is their intersection. -/
instance : has_inf (non_unital_subsemiring R) :=
⟨λ s t,
  { carrier := s ∩ t,
    .. s.to_subsemigroup ⊓ t.to_subsemigroup,
    .. s.to_add_submonoid ⊓ t.to_add_submonoid }⟩

@[simp] lemma coe_inf (p p' : non_unital_subsemiring R) :
  ((p ⊓ p' : non_unital_subsemiring R) : set R) = p ∩ p' := rfl

@[simp] lemma mem_inf {p p' : non_unital_subsemiring R} {x : R} :x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' :=
iff.rfl

instance : has_Inf (non_unital_subsemiring R) :=
⟨λ s, non_unital_subsemiring.mk' (⋂ t ∈ s, ↑t) (⨅ t ∈ s, non_unital_subsemiring.to_subsemigroup t)
  (by simp) (⨅ t ∈ s, non_unital_subsemiring.to_add_submonoid t) (by simp)⟩

@[simp, norm_cast] lemma coe_Inf (S : set (non_unital_subsemiring R)) :
  ((Inf S : non_unital_subsemiring R) : set R) = ⋂ s ∈ S, ↑s := rfl

lemma mem_Inf {S : set (non_unital_subsemiring R)} {x : R} : x ∈ Inf S ↔ ∀ p ∈ S, x ∈ p :=
set.mem_Inter₂

@[simp] lemma Inf_to_subsemigroup (s : set (non_unital_subsemiring R)) :
  (Inf s).to_subsemigroup = ⨅ t ∈ s, non_unital_subsemiring.to_subsemigroup t :=
mk'_to_subsemigroup _ _

@[simp] lemma Inf_to_add_submonoid (s : set (non_unital_subsemiring R)) :
  (Inf s).to_add_submonoid = ⨅ t ∈ s, non_unital_subsemiring.to_add_submonoid t :=
mk'_to_add_submonoid _ _

/-- Non-unital subsemirings of a non-unital semiring form a complete lattice. -/
instance : complete_lattice (non_unital_subsemiring R) :=
{ bot := (⊥),
  bot_le := λ s x hx, (mem_bot.mp hx).symm ▸ zero_mem s,
  top := (⊤),
  le_top := λ s x hx, trivial,
  inf := (⊓),
  inf_le_left := λ s t x, and.left,
  inf_le_right := λ s t x, and.right,
  le_inf := λ s t₁ t₂ h₁ h₂ x hx, ⟨h₁ hx, h₂ hx⟩,
  .. complete_lattice_of_Inf (non_unital_subsemiring R)
    (λ s, is_glb.of_image (λ s t,
      show (s : set R) ≤ t ↔ s ≤ t, from set_like.coe_subset_coe) is_glb_binfi)}

lemma eq_top_iff' (A : non_unital_subsemiring R) : A = ⊤ ↔ ∀ x : R, x ∈ A :=
eq_top_iff.trans ⟨λ h m, h $ mem_top m, λ h m _, h m⟩

section center

/-- The center of a semiring `R` is the set of elements that commute with everything in `R` -/
def center (R) [non_unital_semiring R] : non_unital_subsemiring R :=
{ carrier := set.center R,
  zero_mem' := set.zero_mem_center R,
  add_mem' := λ a b, set.add_mem_center,
  .. subsemigroup.center R }

lemma coe_center (R) [non_unital_semiring R] : ↑(center R) = set.center R := rfl

@[simp]
lemma center_to_subsemigroup (R) [non_unital_semiring R] :
  (center R).to_subsemigroup = subsemigroup.center R := rfl

lemma mem_center_iff {R} [non_unital_semiring R] {z : R} : z ∈ center R ↔ ∀ g, g * z = z * g :=
iff.rfl

instance decidable_mem_center {R} [non_unital_semiring R] [decidable_eq R] [fintype R] :
  decidable_pred (∈ center R) :=
λ _, decidable_of_iff' _ mem_center_iff

@[simp] lemma center_eq_top (R) [non_unital_comm_semiring R] : center R = ⊤ :=
set_like.coe_injective (set.center_eq_univ R)

/-- The center is commutative. -/
instance {R} [non_unital_semiring R] : non_unital_comm_semiring (center R) :=
{ ..subsemigroup.center.comm_semigroup,
  ..(non_unital_subsemiring_class.to_non_unital_semiring (center R)) }

end center

section centralizer

/-- The centralizer of a set as non-unital subsemiring. -/
def centralizer {R} [non_unital_semiring R] (s : set R) : non_unital_subsemiring R :=
{ carrier := s.centralizer,
  zero_mem' := set.zero_mem_centralizer _,
  add_mem' := λ x y hx hy, set.add_mem_centralizer hx hy,
  ..subsemigroup.centralizer s }

@[simp, norm_cast]
lemma coe_centralizer {R} [non_unital_semiring R] (s : set R) :
  (centralizer s : set R) = s.centralizer := rfl

lemma centralizer_to_subsemigroup {R} [non_unital_semiring R] (s : set R) :
  (centralizer s).to_subsemigroup = subsemigroup.centralizer s := rfl

lemma mem_centralizer_iff {R} [non_unital_semiring R] {s : set R} {z : R} :
  z ∈ centralizer s ↔ ∀ g ∈ s, g * z = z * g :=
iff.rfl

lemma centralizer_le {R} [non_unital_semiring R] (s t : set R) (h : s ⊆ t) :
  centralizer t ≤ centralizer s :=
set.centralizer_subset h

@[simp]
lemma centralizer_univ {R} [non_unital_semiring R] : centralizer set.univ = center R :=
set_like.ext' (set.centralizer_univ R)

end centralizer

/-- The `non_unital_subsemiring` generated by a set. -/
def closure (s : set R) : non_unital_subsemiring R := Inf {S | s ⊆ S}

lemma mem_closure {x : R} {s : set R} : x ∈ closure s ↔ ∀ S :
  non_unital_subsemiring R, s ⊆ S → x ∈ S := mem_Inf

/-- The non-unital subsemiring generated by a set includes the set. -/
@[simp] lemma subset_closure {s : set R} : s ⊆ closure s := λ x hx, mem_closure.2 $ λ S hS, hS hx

lemma not_mem_of_not_mem_closure {s : set R} {P : R} (hP : P ∉ closure s) : P ∉ s :=
λ h, hP (subset_closure h)

/-- A non-unital subsemiring `S` includes `closure s` if and only if it includes `s`. -/
@[simp]
lemma closure_le {s : set R} {t : non_unital_subsemiring R} : closure s ≤ t ↔ s ⊆ t :=
⟨set.subset.trans subset_closure, λ h, Inf_le h⟩

/-- Subsemiring closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
lemma closure_mono ⦃s t : set R⦄ (h : s ⊆ t) : closure s ≤ closure t :=
closure_le.2 $ set.subset.trans h subset_closure

lemma closure_eq_of_le {s : set R} {t : non_unital_subsemiring R} (h₁ : s ⊆ t)
  (h₂ : t ≤ closure s) : closure s = t :=
le_antisymm (closure_le.2 h₁) h₂

lemma mem_map_equiv {f : R ≃+* S} {K : non_unital_subsemiring R} {x : S} :
  x ∈ K.map (f : R →ₙ+* S) ↔ f.symm x ∈ K :=
@set.mem_image_equiv _ _ ↑K f.to_equiv x

lemma map_equiv_eq_comap_symm (f : R ≃+* S) (K : non_unital_subsemiring R) :
  K.map (f : R →ₙ+* S) = K.comap f.symm :=
set_like.coe_injective (f.to_equiv.image_eq_preimage K)

lemma comap_equiv_eq_map_symm (f : R ≃+* S) (K : non_unital_subsemiring S) :
  K.comap (f : R →ₙ+* S) = K.map f.symm :=
(map_equiv_eq_comap_symm f.symm K).symm

end non_unital_subsemiring

namespace subsemigroup

/-- The additive closure of a non-unital subsemigroup is a non-unital subsemiring. -/
def non_unital_subsemiring_closure (M : subsemigroup R) : non_unital_subsemiring R :=
{ mul_mem' := λ x y, mul_mem_class.mul_mem_add_closure,
  ..add_submonoid.closure (M : set R)}

lemma non_unital_subsemiring_closure_coe :
  (M.non_unital_subsemiring_closure : set R) = add_submonoid.closure (M : set R) := rfl

lemma non_unital_subsemiring_closure_to_add_submonoid :
  M.non_unital_subsemiring_closure.to_add_submonoid = add_submonoid.closure (M : set R) := rfl

/-- The `non_unital_subsemiring` generated by a multiplicative subsemigroup coincides with the
`non_unital_subsemiring.closure` of the subsemigroup itself . -/
lemma non_unital_subsemiring_closure_eq_closure :
  M.non_unital_subsemiring_closure = non_unital_subsemiring.closure (M : set R) :=
begin
  ext,
  refine ⟨λ hx, _,
    λ hx, (non_unital_subsemiring.mem_closure.mp hx) M.non_unital_subsemiring_closure (λ s sM, _)⟩;
  rintros - ⟨H1, rfl⟩;
  rintros - ⟨H2, rfl⟩,
  { exact add_submonoid.mem_closure.mp hx H1.to_add_submonoid H2 },
  { exact H2 sM }
end

end subsemigroup

namespace non_unital_subsemiring

@[simp]
lemma closure_subsemigroup_closure (s : set R) : closure ↑(subsemigroup.closure s) = closure s :=
le_antisymm
  (closure_le.mpr (λ y hy, (subsemigroup.mem_closure.mp hy)
    (closure s).to_subsemigroup subset_closure))
  (closure_mono (subsemigroup.subset_closure))

/-- The elements of the non-unital subsemiring closure of `M` are exactly the elements of the
additive closure of a multiplicative subsemigroup `M`. -/
lemma coe_closure_eq (s : set R) :
  (closure s : set R) = add_submonoid.closure (subsemigroup.closure s : set R) :=
by simp [← subsemigroup.non_unital_subsemiring_closure_to_add_submonoid,
  subsemigroup.non_unital_subsemiring_closure_eq_closure]

lemma mem_closure_iff {s : set R} {x} :
  x ∈ closure s ↔ x ∈ add_submonoid.closure (subsemigroup.closure s : set R) :=
set.ext_iff.mp (coe_closure_eq s) x

@[simp]
lemma closure_add_submonoid_closure {s : set R} : closure ↑(add_submonoid.closure s) = closure s :=
begin
  ext x,
  refine ⟨λ hx, _, λ hx, closure_mono add_submonoid.subset_closure hx⟩,
  rintros - ⟨H, rfl⟩,
  rintros - ⟨J, rfl⟩,
  refine (add_submonoid.mem_closure.mp (mem_closure_iff.mp hx)) H.to_add_submonoid (λ y hy, _),
  refine (subsemigroup.mem_closure.mp hy) H.to_subsemigroup (λ z hz, _),
  exact (add_submonoid.mem_closure.mp hz) H.to_add_submonoid (λ w hw, J hw),
end

/-- An induction principle for closure membership. If `p` holds for `0`, `1`, and all elements
of `s`, and is preserved under addition and multiplication, then `p` holds for all elements
of the closure of `s`. -/
@[elab_as_eliminator]
lemma closure_induction {s : set R} {p : R → Prop} {x} (h : x ∈ closure s)
  (Hs : ∀ x ∈ s, p x) (H0 : p 0)
  (Hadd : ∀ x y, p x → p y → p (x + y)) (Hmul : ∀ x y, p x → p y → p (x * y)) : p x :=
(@closure_le _ _ _ ⟨p, Hadd, H0, Hmul⟩).2 Hs h

/-- An induction principle for closure membership for predicates with two arguments. -/
@[elab_as_eliminator]
lemma closure_induction₂ {s : set R} {p : R → R → Prop} {x} {y : R} (hx : x ∈ closure s)
  (hy : y ∈ closure s)
  (Hs : ∀ (x ∈ s) (y ∈ s), p x y)
  (H0_left : ∀ x, p 0 x)
  (H0_right : ∀ x, p x 0)
  (Hadd_left : ∀ x₁ x₂ y, p x₁ y → p x₂ y → p (x₁ + x₂) y)
  (Hadd_right : ∀ x y₁ y₂, p x y₁ → p x y₂ → p x (y₁ + y₂))
  (Hmul_left : ∀ x₁ x₂ y, p x₁ y → p x₂ y → p (x₁ * x₂) y)
  (Hmul_right : ∀ x y₁ y₂, p x y₁ → p x y₂ → p x (y₁ * y₂))
  : p x y :=
closure_induction hx
  (λ x₁ x₁s, closure_induction hy (Hs x₁ x₁s) (H0_right x₁) (Hadd_right x₁) (Hmul_right x₁))
  (H0_left y) (λ z z', Hadd_left z z' y) (λ z z', Hmul_left z z' y)

variable (R)

/-- `closure` forms a Galois insertion with the coercion to set. -/
protected def gi : galois_insertion (@closure R _) coe :=
{ choice := λ s _, closure s,
  gc := λ s t, closure_le,
  le_l_u := λ s, subset_closure,
  choice_eq := λ s h, rfl }

variables {R} {F : Type*} [non_unital_ring_hom_class F R S]

/-- Closure of a non-unital subsemiring `S` equals `S`. -/
lemma closure_eq (s : non_unital_subsemiring R) : closure (s : set R) = s :=
(non_unital_subsemiring.gi R).l_u_eq s

@[simp] lemma closure_empty : closure (∅ : set R) = ⊥ := (non_unital_subsemiring.gi R).gc.l_bot

@[simp] lemma closure_univ : closure (set.univ : set R) = ⊤ := @coe_top R _ ▸ closure_eq ⊤

lemma closure_union (s t : set R) : closure (s ∪ t) = closure s ⊔ closure t :=
(non_unital_subsemiring.gi R).gc.l_sup

lemma closure_Union {ι} (s : ι → set R) : closure (⋃ i, s i) = ⨆ i, closure (s i) :=
(non_unital_subsemiring.gi R).gc.l_supr

lemma closure_sUnion (s : set (set R)) : closure (⋃₀ s) = ⨆ t ∈ s, closure t :=
(non_unital_subsemiring.gi R).gc.l_Sup

lemma map_sup (s t : non_unital_subsemiring R) (f : F) :
  (map f (s ⊔ t) : non_unital_subsemiring S) = map f s ⊔ map f t :=
@galois_connection.l_sup _ _ s t  _ _ _ _ (gc_map_comap f)

lemma map_supr {ι : Sort*} (f : F) (s : ι → non_unital_subsemiring R) :
  (map f (supr s) : non_unital_subsemiring S) = ⨆ i, map f (s i) :=
@galois_connection.l_supr _ _ _ _ _ _ _ (gc_map_comap f) s

lemma comap_inf (s t : non_unital_subsemiring S) (f : F) :
  (comap f (s ⊓ t) : non_unital_subsemiring R) = comap f s ⊓ comap f t :=
@galois_connection.u_inf _ _ s t  _ _ _ _ (gc_map_comap f)

lemma comap_infi {ι : Sort*} (f : F) (s : ι → non_unital_subsemiring S) :
  (comap f (infi s) : non_unital_subsemiring R) = ⨅ i, comap f (s i) :=
@galois_connection.u_infi _ _ _ _ _ _ _ (gc_map_comap f) s

@[simp] lemma map_bot (f : F) :
  map f (⊥ : non_unital_subsemiring R) = (⊥ : non_unital_subsemiring S) :=
(gc_map_comap f).l_bot

@[simp] lemma comap_top (f : F) :
  comap f (⊤ : non_unital_subsemiring S) = (⊤ : non_unital_subsemiring R) :=
(gc_map_comap f).u_top

/-- Given `non_unital_subsemiring`s `s`, `t` of semirings `R`, `S` respectively, `s.prod t` is
`s × t` as a non-unital subsemiring of `R × S`. -/
def prod (s : non_unital_subsemiring R) (t : non_unital_subsemiring S) :
  non_unital_subsemiring (R × S) :=
{ carrier := (s : set R) ×ˢ (t : set S),
  .. s.to_subsemigroup.prod t.to_subsemigroup, .. s.to_add_submonoid.prod t.to_add_submonoid}

@[norm_cast]
lemma coe_prod (s : non_unital_subsemiring R) (t : non_unital_subsemiring S) :
  (s.prod t : set (R × S)) = (s : set R) ×ˢ (t : set S) :=
rfl

lemma mem_prod {s : non_unital_subsemiring R} {t : non_unital_subsemiring S} {p : R × S} :
  p ∈ s.prod t ↔ p.1 ∈ s ∧ p.2 ∈ t := iff.rfl

@[mono] lemma prod_mono ⦃s₁ s₂ : non_unital_subsemiring R⦄ (hs : s₁ ≤ s₂)
  ⦃t₁ t₂ : non_unital_subsemiring S⦄ (ht : t₁ ≤ t₂) : s₁.prod t₁ ≤ s₂.prod t₂ :=
set.prod_mono hs ht

lemma prod_mono_right (s : non_unital_subsemiring R) :
  monotone (λ t : non_unital_subsemiring S, s.prod t) :=
prod_mono (le_refl s)

lemma prod_mono_left (t : non_unital_subsemiring S) :
  monotone (λ s : non_unital_subsemiring R, s.prod t) :=
λ s₁ s₂ hs, prod_mono hs (le_refl t)

lemma prod_top (s : non_unital_subsemiring R) :
  s.prod (⊤ : non_unital_subsemiring S) = s.comap (non_unital_ring_hom.fst R S) :=
ext $ λ x, by simp [mem_prod, monoid_hom.coe_fst]

lemma top_prod (s : non_unital_subsemiring S) :
  (⊤ : non_unital_subsemiring R).prod s = s.comap (non_unital_ring_hom.snd R S) :=
ext $ λ x, by simp [mem_prod, monoid_hom.coe_snd]

@[simp]
lemma top_prod_top : (⊤ : non_unital_subsemiring R).prod (⊤ : non_unital_subsemiring S) = ⊤ :=
(top_prod _).trans $ comap_top _

/-- Product of non-unital subsemirings is isomorphic to their product as semigroups. -/
def prod_equiv (s : non_unital_subsemiring R) (t : non_unital_subsemiring S) : s.prod t ≃+* s × t :=
{ map_mul' := λ x y, rfl, map_add' := λ x y, rfl, .. equiv.set.prod ↑s ↑t }

lemma mem_supr_of_directed {ι} [hι : nonempty ι] {S : ι → non_unital_subsemiring R}
  (hS : directed (≤) S) {x : R} :
  x ∈ (⨆ i, S i) ↔ ∃ i, x ∈ S i :=
begin
  refine ⟨_, λ ⟨i, hi⟩, (set_like.le_def.1 $ le_supr S i) hi⟩,
  let U : non_unital_subsemiring R := non_unital_subsemiring.mk' (⋃ i, (S i : set R))
    (⨆ i, (S i).to_subsemigroup) (subsemigroup.coe_supr_of_directed $ hS.mono_comp _ (λ _ _, id))
    (⨆ i, (S i).to_add_submonoid) (add_submonoid.coe_supr_of_directed $ hS.mono_comp _ (λ _ _, id)),
  suffices : (⨆ i, S i) ≤ U, by simpa using @this x,
  exact supr_le (λ i x hx, set.mem_Union.2 ⟨i, hx⟩),
end

lemma coe_supr_of_directed {ι} [hι : nonempty ι] {S : ι → non_unital_subsemiring R}
  (hS : directed (≤) S) : ((⨆ i, S i : non_unital_subsemiring R) : set R) = ⋃ i, ↑(S i) :=
set.ext $ λ x, by simp [mem_supr_of_directed hS]

lemma mem_Sup_of_directed_on {S : set (non_unital_subsemiring R)} (Sne : S.nonempty)
  (hS : directed_on (≤) S) {x : R} :
  x ∈ Sup S ↔ ∃ s ∈ S, x ∈ s :=
begin
  haveI : nonempty S := Sne.to_subtype,
  simp only [Sup_eq_supr', mem_supr_of_directed hS.directed_coe, set_coe.exists, subtype.coe_mk]
end

lemma coe_Sup_of_directed_on {S : set (non_unital_subsemiring R)} (Sne : S.nonempty)
  (hS : directed_on (≤) S) : (↑(Sup S) : set R) = ⋃ s ∈ S, ↑s :=
set.ext $ λ x, by simp [mem_Sup_of_directed_on Sne hS]

end non_unital_subsemiring

namespace non_unital_ring_hom

variables {F : Type*} [non_unital_non_assoc_semiring T] [non_unital_ring_hom_class F R S]
  {s : non_unital_subsemiring R}

open non_unital_subsemiring_class non_unital_subsemiring

/-- Restriction of a non-unital ring homomorphism to a non-unital subsemiring of the codomain. -/
def cod_restrict (f : F) (s : non_unital_subsemiring S) (h : ∀ x, f x ∈ s) : R →ₙ+* s :=
{ to_fun := λ n, ⟨f n, h n⟩,
  .. (f : R →ₙ* S).cod_restrict s.to_subsemigroup h,
  .. (f : R →+ S).cod_restrict s.to_add_submonoid h }

/-- Restriction of a non-unital ring homomorphism to its range interpreted as a
non-unital subsemiring.

This is the bundled version of `set.range_factorization`. -/
def srange_restrict (f : F) : R →ₙ+* (srange f : non_unital_subsemiring S) :=
cod_restrict f (srange f) (mem_srange_self f)

@[simp] lemma coe_srange_restrict (f : F) (x : R) :
  (srange_restrict f x : S) = f x :=
rfl

lemma srange_restrict_surjective (f : F) :
  function.surjective (srange_restrict f : R → (srange f : non_unital_subsemiring S)) :=
λ ⟨y, hy⟩, let ⟨x, hx⟩ := mem_srange.mp hy in ⟨x, subtype.ext hx⟩

lemma srange_top_iff_surjective {f : F} :
  srange f = (⊤ : non_unital_subsemiring S) ↔ function.surjective (f : R → S):=
set_like.ext'_iff.trans $ iff.trans (by rw [coe_srange, coe_top]) set.range_iff_surjective

/-- The range of a surjective non-unital ring homomorphism is the whole of the codomain. -/
lemma srange_top_of_surjective (f : F) (hf : function.surjective (f : R → S)) :
  srange f = (⊤ : non_unital_subsemiring S) :=
srange_top_iff_surjective.2 hf

/-- The non-unital subsemiring of elements `x : R` such that `f x = g x` -/
def eq_slocus (f g : F) : non_unital_subsemiring R :=
{ carrier := {x | f x = g x},
  .. (f : R →ₙ* S).eq_mlocus (g : R →ₙ* S),
  .. (f : R →+ S).eq_mlocus g }

/-- If two non-unital ring homomorphisms are equal on a set, then they are equal on its
non-unital subsemiring closure. -/
lemma eq_on_sclosure {f g : F} {s : set R} (h : set.eq_on (f : R → S) (g : R → S) s) :
  set.eq_on f g (closure s) :=
show closure s ≤ eq_slocus f g, from closure_le.2 h

lemma eq_of_eq_on_stop {f g : F} (h : set.eq_on (f : R → S) (g : R → S)
  (⊤ : non_unital_subsemiring R)) : f = g :=
fun_like.ext _ _ (λ x, h trivial)

lemma eq_of_eq_on_sdense {s : set R} (hs : closure s = ⊤) {f g : F}
  (h : s.eq_on (f : R → S) (g : R → S)) :
  f = g :=
eq_of_eq_on_stop $ hs ▸ eq_on_sclosure h

lemma sclosure_preimage_le (f : F) (s : set S) :
  closure ((f : R → S) ⁻¹' s) ≤ (closure s).comap f :=
closure_le.2 $ λ x hx, set_like.mem_coe.2 $ mem_comap.2 $ subset_closure hx

/-- The image under a ring homomorphism of the subsemiring generated by a set equals
the subsemiring generated by the image of the set. -/
lemma map_sclosure (f : F) (s : set R) :
  (closure s).map f = closure ((f : R → S) '' s) :=
le_antisymm
  (map_le_iff_le_comap.2 $ le_trans (closure_mono $ set.subset_preimage_image _ _)
    (sclosure_preimage_le _ _))
  (closure_le.2 $ set.image_subset _ subset_closure)

end non_unital_ring_hom

namespace non_unital_subsemiring

open non_unital_ring_hom non_unital_subsemiring_class

/-- The non-unital ring homomorphism associated to an inclusion of
non-unital subsemirings. -/
def inclusion {S T : non_unital_subsemiring R} (h : S ≤ T) : S →ₙ+* T :=
cod_restrict (subtype S) _ (λ x, h x.2)

@[simp] lemma srange_subtype (s : non_unital_subsemiring R) : (subtype s).srange = s :=
set_like.coe_injective $ (coe_srange _).trans subtype.range_coe

@[simp]
lemma range_fst : (fst R S).srange = ⊤ :=
non_unital_ring_hom.srange_top_of_surjective (fst R S) prod.fst_surjective

@[simp]
lemma range_snd : (snd R S).srange = ⊤ :=
non_unital_ring_hom.srange_top_of_surjective (snd R S) $ prod.snd_surjective

end non_unital_subsemiring

namespace ring_equiv

open non_unital_ring_hom non_unital_subsemiring_class

variables {s t : non_unital_subsemiring R}
variables {F : Type*} [non_unital_ring_hom_class F R S]

/-- Makes the identity isomorphism from a proof two non-unital subsemirings of a multiplicative
monoid are equal. -/
def non_unital_subsemiring_congr (h : s = t) : s ≃+* t :=
{ map_mul' :=  λ _ _, rfl, map_add' := λ _ _, rfl, ..equiv.set_congr $ congr_arg _ h }

/-- Restrict a non-unital ring homomorphism with a left inverse to a ring isomorphism to its
`non_unital_ring_hom.srange`. -/
def sof_left_inverse' {g : S → R} {f : F} (h : function.left_inverse g f) :
  R ≃+* srange f :=
{ to_fun := srange_restrict f,
  inv_fun := λ x, g (subtype (srange f) x),
  left_inv := h,
  right_inv := λ x, subtype.ext $
    let ⟨x', hx'⟩ := non_unital_ring_hom.mem_srange.mp x.prop in
    show f (g x) = x, by rw [←hx', h x'],
  ..(srange_restrict f) }

@[simp] lemma sof_left_inverse'_apply
  {g : S → R} {f : F} (h : function.left_inverse g f) (x : R) :
  ↑(sof_left_inverse' h x) = f x := rfl

@[simp] lemma sof_left_inverse'_symm_apply
  {g : S → R} {f : F} (h : function.left_inverse g f) (x : srange f) :
  (sof_left_inverse' h).symm x = g x := rfl

/-- Given an equivalence `e : R ≃+* S` of non-unital semirings and a non-unital subsemiring
`s` of `R`, `non_unital_subsemiring_map e s` is the induced equivalence between `s` and
`s.map e` -/
@[simps] def non_unital_subsemiring_map (e : R ≃+* S) (s : non_unital_subsemiring R) :
  s ≃+* non_unital_subsemiring.map e.to_non_unital_ring_hom s :=
{ ..e.to_add_equiv.add_submonoid_map s.to_add_submonoid,
  ..e.to_mul_equiv.subsemigroup_map s.to_subsemigroup }

end ring_equiv
