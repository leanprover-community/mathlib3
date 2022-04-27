/-
Copyright (c) 2020 Yury Kudryashov All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/

import algebra.module.basic
import algebra.ring.equiv
import algebra.ring.prod
import data.set.finite
import group_theory.submonoid.centralizer
import group_theory.submonoid.membership

/-!
# Bundled subsemirings

We define bundled non-unital subsemirings and some standard constructions:
`complete_lattice` structure, `subtype` and `inclusion` ring homomorphisms, subsemiring `map`,
`comap` and range (`srange`) of a `non_unital_ring_hom` etc.
-/

-- this needs to get removed
infixr ` →ₙ* `:25 := mul_hom

open_locale big_operators

universes u v w

variables {R : Type u} {S : Type v} {T : Type w} [non_unital_non_assoc_semiring R]
  (M : add_submonoid R)

section non_unital_subsemiring_class

/-- `non_unital_subsemiring_class S R` states that `S` is a type of subsets `s ⊆ R` that
are both an additive submonoid and also a multiplicative subsemigroup. -/
class non_unital_subsemiring_class (S : Type*) (R : out_param $ Type u)
  [non_unital_non_assoc_semiring R] [set_like S R] extends add_submonoid_class S R :=
(mul_mem : ∀ {s : S} {a b : R}, a ∈ s → b ∈ s → a * b ∈ s)

@[priority 100] -- See note [lower instance priority]
instance non_unital_subsemiring_class.mul_mem_class (S : Type*) (R : out_param $ Type u)
  [non_unital_non_assoc_semiring R] [set_like S R] [h : non_unital_subsemiring_class S R] :
  mul_mem_class S R :=
{ .. h }

variables [set_like S R] [hSR : non_unital_subsemiring_class S R] (s : S)
include hSR

open add_submonoid_class

namespace non_unital_subsemiring_class

/-- A non-unital subsemiring of a `non_unital_non_assoc_semiring` inherits a
`non_unital_non_assoc_semiring` structure -/
@[priority 75] /- Prefer subclasses of `non_unital_non_assoc_semiring` over subclasses of
`non_unital_subsemiring_class`. -/
instance to_non_unital_non_assoc_semiring : non_unital_non_assoc_semiring s :=
subtype.coe_injective.non_unital_non_assoc_semiring coe rfl (by simp) (λ _ _, rfl) (λ _ _, rfl)

instance no_zero_divisors [no_zero_divisors R] : no_zero_divisors s :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := λ x y h,
  or.cases_on (eq_zero_or_eq_zero_of_mul_eq_zero $ subtype.ext_iff.mp h)
    (λ h, or.inl $ subtype.eq h) (λ h, or.inr $ subtype.eq h) }

/-- The natural non-unital ring hom from a non-unital subsemiring of a non-unital semiring `R` to
`R`. -/
def subtype : s →ₙ+* R :=
{ to_fun := coe, .. add_submonoid_class.subtype s, .. mul_mem_class.subtype s }

@[simp] theorem coe_subtype : (subtype s : s → R) = coe := rfl

omit hSR

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

end non_unital_subsemiring_class

variables [non_unital_non_assoc_semiring S] [non_unital_non_assoc_semiring T]

set_option old_structure_cmd true

/-- A non-unital subsemiring of a non-unital semiring `R` is a subset `s` that is both an additive
submonoid and a semigroup. -/
structure non_unital_subsemiring (R : Type u) [non_unital_non_assoc_semiring R]
  extends add_submonoid R, subsemigroup R

/-- Reinterpret a `subsemiring` as a `subsemigroup`. -/
add_decl_doc non_unital_subsemiring.to_subsemigroup

/-- Reinterpret a `subsemiring` as an `add_submonoid`. -/
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

/-- The image of a subsemiring along a ring homomorphism is a subsemiring. -/
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
/-- A subsemiring is isomorphic to its image under an injective function -/

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

variables {F G : Type*} [non_unital_ring_hom_class F R S] [non_unital_ring_hom_class G S T]
  (f : F) (g : G)

/-- The range of a non-unital ring homomorphism is a non-unital subsemiring.
See Note [range copy pattern]. -/
def srange : non_unital_subsemiring S :=
((⊤ : non_unital_subsemiring R).map (f : R →ₙ+* S)).copy (set.range f) set.image_univ.symm

@[simp] lemma coe_srange : (@srange R S _ _ _ _ f : set S) = set.range f := rfl

@[simp] lemma mem_srange {f : F} {y : S} : y ∈ (@srange R S _ _ _ _ f) ↔ ∃ x, f x = y :=
iff.rfl

lemma srange_eq_map : @srange R S _ _ _ _ f = (⊤ : non_unital_subsemiring R).map f :=
by { ext, simp }

lemma mem_srange_self (f : F) (x : R) : f x ∈ @srange R S _ _ _ _ f :=
mem_srange.mpr ⟨x, rfl⟩

lemma map_srange : (srange f).map g = ((g : S →ₙ+* T).comp (f : R →ₙ+* S)).srange :=
by simpa only [srange_eq_map] using (⊤ : non_unital_subsemiring R).map_map g f

/-- The range of a morphism of non-unital semirings is a fintype, if the domain is a fintype.
Note: this instance can form a diamond with `subtype.fintype` in the
  presence of `fintype S`.-/
instance fintype_srange [fintype R] [decidable_eq S] (f : F) : fintype (srange f) :=
set.fintype_range f

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
