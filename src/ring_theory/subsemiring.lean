/-
Copyright (c) 2020 Yury Kudryashov All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/

import algebra.ring.prod
import group_theory.submonoid
import group_theory.submonoid.center
import data.equiv.ring

/-!
# Bundled subsemirings

We define bundled subsemirings and some standard constructions: `complete_lattice` structure,
`subtype` and `inclusion` ring homomorphisms, subsemiring `map`, `comap` and range (`srange`) of
a `ring_hom` etc.
-/

open_locale big_operators

universes u v w

variables {R : Type u} {S : Type v} {T : Type w}
  [non_assoc_semiring R] [non_assoc_semiring S] [non_assoc_semiring T]
  (M : submonoid R)

set_option old_structure_cmd true

/-- A subsemiring of a semiring `R` is a subset `s` that is both a multiplicative and an additive
submonoid. -/
structure subsemiring (R : Type u) [non_assoc_semiring R] extends submonoid R, add_submonoid R

/-- Reinterpret a `subsemiring` as a `submonoid`. -/
add_decl_doc subsemiring.to_submonoid

/-- Reinterpret a `subsemiring` as an `add_submonoid`. -/
add_decl_doc subsemiring.to_add_submonoid

namespace subsemiring

instance : set_like (subsemiring R) R :=
⟨subsemiring.carrier, λ p q h, by cases p; cases q; congr'⟩

@[simp]
lemma mem_carrier {s : subsemiring R} {x : R} : x ∈ s.carrier ↔ x ∈ s := iff.rfl

/-- Two subsemirings are equal if they have the same elements. -/
@[ext] theorem ext {S T : subsemiring R} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := set_like.ext h

/-- Copy of a subsemiring with a new `carrier` equal to the old one. Useful to fix definitional
equalities.-/
protected def copy (S : subsemiring R) (s : set R) (hs : s = ↑S) : subsemiring R :=
{ carrier := s,
  ..S.to_add_submonoid.copy s hs,
  ..S.to_submonoid.copy s hs }

@[simp] lemma coe_copy (S : subsemiring R) (s : set R) (hs : s = ↑S) :
  (S.copy s hs : set R) = s := rfl

lemma copy_eq (S : subsemiring R) (s : set R) (hs : s = ↑S) : S.copy s hs = S :=
set_like.coe_injective hs

lemma to_submonoid_injective : function.injective (to_submonoid : subsemiring R → submonoid R)
| r s h := ext (set_like.ext_iff.mp h : _)

@[mono] lemma to_submonoid_strict_mono : strict_mono (to_submonoid : subsemiring R → submonoid R) :=
λ _ _, id

@[mono] lemma to_submonoid_mono : monotone (to_submonoid : subsemiring R → submonoid R) :=
to_submonoid_strict_mono.monotone

lemma to_add_submonoid_injective :
  function.injective (to_add_submonoid : subsemiring R → add_submonoid R)
| r s h := ext (set_like.ext_iff.mp h : _)

@[mono] lemma to_add_submonoid_strict_mono :
  strict_mono (to_add_submonoid : subsemiring R → add_submonoid R) := λ _ _, id

@[mono]
lemma to_add_submonoid_mono : monotone (to_add_submonoid : subsemiring R → add_submonoid R) :=
to_add_submonoid_strict_mono.monotone

/-- Construct a `subsemiring R` from a set `s`, a submonoid `sm`, and an additive
submonoid `sa` such that `x ∈ s ↔ x ∈ sm ↔ x ∈ sa`. -/
protected def mk' (s : set R) (sm : submonoid R) (hm : ↑sm = s)
  (sa : add_submonoid R) (ha : ↑sa = s) :
  subsemiring R :=
{ carrier := s,
  zero_mem' := ha ▸ sa.zero_mem,
  one_mem' := hm ▸ sm.one_mem,
  add_mem' := λ x y, by simpa only [← ha] using sa.add_mem,
  mul_mem' := λ x y, by simpa only [← hm] using sm.mul_mem }

@[simp] lemma coe_mk' {s : set R} {sm : submonoid R} (hm : ↑sm = s)
  {sa : add_submonoid R} (ha : ↑sa = s) :
  (subsemiring.mk' s sm hm sa ha : set R) = s := rfl

@[simp] lemma mem_mk' {s : set R} {sm : submonoid R} (hm : ↑sm = s)
  {sa : add_submonoid R} (ha : ↑sa = s) {x : R} :
  x ∈ subsemiring.mk' s sm hm sa ha ↔ x ∈ s :=
iff.rfl

@[simp] lemma mk'_to_submonoid {s : set R} {sm : submonoid R} (hm : ↑sm = s)
  {sa : add_submonoid R} (ha : ↑sa = s) :
  (subsemiring.mk' s sm hm sa ha).to_submonoid = sm :=
set_like.coe_injective hm.symm

@[simp] lemma mk'_to_add_submonoid {s : set R} {sm : submonoid R} (hm : ↑sm = s)
  {sa : add_submonoid R} (ha : ↑sa  =s) :
  (subsemiring.mk' s sm hm sa ha).to_add_submonoid = sa :=
set_like.coe_injective ha.symm

end subsemiring

namespace subsemiring

variables (s : subsemiring R)

/-- A subsemiring contains the semiring's 1. -/
theorem one_mem : (1 : R) ∈ s := s.one_mem'

/-- A subsemiring contains the semiring's 0. -/
theorem zero_mem : (0 : R) ∈ s := s.zero_mem'

/-- A subsemiring is closed under multiplication. -/
theorem mul_mem : ∀ {x y : R}, x ∈ s → y ∈ s → x * y ∈ s := s.mul_mem'

/-- A subsemiring is closed under addition. -/
theorem add_mem : ∀ {x y : R}, x ∈ s → y ∈ s → x + y ∈ s := s.add_mem'

/-- Product of a list of elements in a `subsemiring` is in the `subsemiring`. -/
lemma list_prod_mem {R : Type*} [semiring R] (s : subsemiring R) {l : list R} :
  (∀x ∈ l, x ∈ s) → l.prod ∈ s :=
s.to_submonoid.list_prod_mem

/-- Sum of a list of elements in a `subsemiring` is in the `subsemiring`. -/
lemma list_sum_mem {l : list R} : (∀x ∈ l, x ∈ s) → l.sum ∈ s :=
s.to_add_submonoid.list_sum_mem

/-- Product of a multiset of elements in a `subsemiring` of a `comm_semiring`
    is in the `subsemiring`. -/
lemma multiset_prod_mem {R} [comm_semiring R] (s : subsemiring R) (m : multiset R) :
  (∀a ∈ m, a ∈ s) → m.prod ∈ s :=
s.to_submonoid.multiset_prod_mem m

/-- Sum of a multiset of elements in a `subsemiring` of a `semiring` is
in the `add_subsemiring`. -/
lemma multiset_sum_mem (m : multiset R) :
  (∀a ∈ m, a ∈ s) → m.sum ∈ s :=
s.to_add_submonoid.multiset_sum_mem m

/-- Product of elements of a subsemiring of a `comm_semiring` indexed by a `finset` is in the
    subsemiring. -/
lemma prod_mem {R : Type*} [comm_semiring R] (s : subsemiring R)
  {ι : Type*} {t : finset ι} {f : ι → R} (h : ∀c ∈ t, f c ∈ s) :
  ∏ i in t, f i ∈ s :=
s.to_submonoid.prod_mem h

/-- Sum of elements in an `subsemiring` of an `semiring` indexed by a `finset`
is in the `add_subsemiring`. -/
lemma sum_mem (s : subsemiring R)
  {ι : Type*} {t : finset ι} {f : ι → R} (h : ∀c ∈ t, f c ∈ s) :
  ∑ i in t, f i ∈ s :=
s.to_add_submonoid.sum_mem h

lemma pow_mem {R : Type*} [semiring R] (s : subsemiring R) {x : R} (hx : x ∈ s) (n : ℕ) :
  x^n ∈ s := s.to_submonoid.pow_mem hx n

lemma nsmul_mem {x : R} (hx : x ∈ s) (n : ℕ) :
  n • x ∈ s := s.to_add_submonoid.nsmul_mem hx n

lemma coe_nat_mem (n : ℕ) : (n : R) ∈ s :=
by simp only [← nsmul_one, nsmul_mem, one_mem]

/-- A subsemiring of a `non_assoc_semiring` inherits a `non_assoc_semiring` structure -/
instance to_non_assoc_semiring : non_assoc_semiring s :=
{ mul_zero := λ x, subtype.eq $ mul_zero x,
  zero_mul := λ x, subtype.eq $ zero_mul x,
  right_distrib := λ x y z, subtype.eq $ right_distrib x y z,
  left_distrib := λ x y z, subtype.eq $ left_distrib x y z,
  .. s.to_submonoid.to_mul_one_class, .. s.to_add_submonoid.to_add_comm_monoid }

@[simp, norm_cast] lemma coe_one : ((1 : s) : R) = (1 : R) := rfl
@[simp, norm_cast] lemma coe_zero : ((0 : s) : R) = (0 : R) := rfl
@[simp, norm_cast] lemma coe_add (x y : s) : ((x + y : s) : R) = (x + y : R) := rfl
@[simp, norm_cast] lemma coe_mul (x y : s) : ((x * y : s) : R) = (x * y : R) := rfl

instance nontrivial [nontrivial R] : nontrivial s :=
nontrivial_of_ne 0 1 $ λ H, zero_ne_one (congr_arg subtype.val H)

instance no_zero_divisors [no_zero_divisors R] : no_zero_divisors s :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := λ x y h,
  or.cases_on (eq_zero_or_eq_zero_of_mul_eq_zero $ subtype.ext_iff.mp h)
    (λ h, or.inl $ subtype.eq h) (λ h, or.inr $ subtype.eq h) }

/-- A subsemiring of a `semiring` is a `semiring`. -/
instance to_semiring {R} [semiring R] (s : subsemiring R) : semiring s :=
{ ..s.to_non_assoc_semiring, ..s.to_submonoid.to_monoid }

@[simp, norm_cast] lemma coe_pow {R} [semiring R] (s : subsemiring R) (x : s) (n : ℕ) :
  ((x^n : s) : R) = (x^n : R) :=
begin
  induction n with n ih,
  { simp, },
  { simp [pow_succ, ih], },
end

/-- A subsemiring of a `comm_semiring` is a `comm_semiring`. -/
instance to_comm_semiring {R} [comm_semiring R] (s : subsemiring R) : comm_semiring s :=
{ mul_comm := λ _ _, subtype.eq $ mul_comm _ _, ..s.to_semiring}

/-- The natural ring hom from a subsemiring of semiring `R` to `R`. -/
def subtype : s →+* R :=
{ to_fun := coe, .. s.to_submonoid.subtype, .. s.to_add_submonoid.subtype }

@[simp] theorem coe_subtype : ⇑s.subtype = coe := rfl

/-- A subsemiring of an `ordered_semiring` is an `ordered_semiring`. -/
instance to_ordered_semiring {R} [ordered_semiring R] (s : subsemiring R) : ordered_semiring s :=
subtype.coe_injective.ordered_semiring coe rfl rfl (λ _ _, rfl) (λ _ _, rfl)

/-- A subsemiring of an `ordered_comm_semiring` is an `ordered_comm_semiring`. -/
instance to_ordered_comm_semiring {R} [ordered_comm_semiring R] (s : subsemiring R) :
  ordered_comm_semiring s :=
subtype.coe_injective.ordered_comm_semiring coe rfl rfl (λ _ _, rfl) (λ _ _, rfl)

/-- A subsemiring of a `linear_ordered_semiring` is a `linear_ordered_semiring`. -/
instance to_linear_ordered_semiring {R} [linear_ordered_semiring R] (s : subsemiring R) :
  linear_ordered_semiring s :=
subtype.coe_injective.linear_ordered_semiring coe rfl rfl (λ _ _, rfl) (λ _ _, rfl)

/-! Note: currently, there is no `linear_ordered_comm_semiring`. -/


@[simp] lemma mem_to_submonoid {s : subsemiring R} {x : R} : x ∈ s.to_submonoid ↔ x ∈ s := iff.rfl
@[simp] lemma coe_to_submonoid (s : subsemiring R) : (s.to_submonoid : set R) = s := rfl
@[simp] lemma mem_to_add_submonoid {s : subsemiring R} {x : R} :
  x ∈ s.to_add_submonoid ↔ x ∈ s := iff.rfl
@[simp] lemma coe_to_add_submonoid (s : subsemiring R) : (s.to_add_submonoid : set R) = s := rfl

/-- The subsemiring `R` of the semiring `R`. -/
instance : has_top (subsemiring R) :=
⟨{ .. (⊤ : submonoid R), .. (⊤ : add_submonoid R) }⟩

@[simp] lemma mem_top (x : R) : x ∈ (⊤ : subsemiring R) := set.mem_univ x

@[simp] lemma coe_top : ((⊤ : subsemiring R) : set R) = set.univ := rfl

/-- The preimage of a subsemiring along a ring homomorphism is a subsemiring. -/
def comap (f : R →+* S) (s : subsemiring S) : subsemiring R :=
{ carrier := f ⁻¹' s,
  .. s.to_submonoid.comap (f : R →* S), .. s.to_add_submonoid.comap (f : R →+ S) }

@[simp] lemma coe_comap (s : subsemiring S) (f : R →+* S) : (s.comap f : set R) = f ⁻¹' s := rfl

@[simp]
lemma mem_comap {s : subsemiring S} {f : R →+* S} {x : R} : x ∈ s.comap f ↔ f x ∈ s := iff.rfl

lemma comap_comap (s : subsemiring T) (g : S →+* T) (f : R →+* S) :
  (s.comap g).comap f = s.comap (g.comp f) :=
rfl

/-- The image of a subsemiring along a ring homomorphism is a subsemiring. -/
def map (f : R →+* S) (s : subsemiring R) : subsemiring S :=
{ carrier := f '' s,
  .. s.to_submonoid.map (f : R →* S), .. s.to_add_submonoid.map (f : R →+ S) }

@[simp] lemma coe_map (f : R →+* S) (s : subsemiring R) : (s.map f : set S) = f '' s := rfl

@[simp] lemma mem_map {f : R →+* S} {s : subsemiring R} {y : S} :
  y ∈ s.map f ↔ ∃ x ∈ s, f x = y :=
set.mem_image_iff_bex

@[simp] lemma map_id : s.map (ring_hom.id R) = s :=
set_like.coe_injective $ set.image_id _

lemma map_map (g : S →+* T) (f : R →+* S) : (s.map f).map g = s.map (g.comp f) :=
set_like.coe_injective $ set.image_image _ _ _

lemma map_le_iff_le_comap {f : R →+* S} {s : subsemiring R} {t : subsemiring S} :
  s.map f ≤ t ↔ s ≤ t.comap f :=
set.image_subset_iff

lemma gc_map_comap (f : R →+* S) : galois_connection (map f) (comap f) :=
λ S T, map_le_iff_le_comap

/-- A subsemiring is isomorphic to its image under an injective function -/
noncomputable def equiv_map_of_injective
  (f : R →+* S) (hf : function.injective f) : s ≃+* s.map f :=
{ map_mul' := λ _ _, subtype.ext (f.map_mul _ _),
  map_add' := λ _ _, subtype.ext (f.map_add _ _),
  ..equiv.set.image f s hf }

@[simp] lemma coe_equiv_map_of_injective_apply
  (f : R →+* S) (hf : function.injective f) (x : s) :
  (equiv_map_of_injective s f hf x : S) = f x := rfl

end subsemiring

namespace ring_hom

variables (g : S →+* T) (f : R →+* S)

/-- The range of a ring homomorphism is a subsemiring. See Note [range copy pattern]. -/
def srange : subsemiring S :=
((⊤ : subsemiring R).map f).copy (set.range f) set.image_univ.symm

@[simp] lemma coe_srange : (f.srange : set S) = set.range f := rfl

@[simp] lemma mem_srange {f : R →+* S} {y : S} : y ∈ f.srange ↔ ∃ x, f x = y :=
iff.rfl

lemma srange_eq_map (f : R →+* S) : f.srange = (⊤ : subsemiring R).map f :=
by { ext, simp }

lemma mem_srange_self (f : R →+* S) (x : R) : f x ∈ f.srange :=
mem_srange.mpr ⟨x, rfl⟩

lemma map_srange : f.srange.map g = (g.comp f).srange :=
by simpa only [srange_eq_map] using (⊤ : subsemiring R).map_map g f

/-- The range of a morphism of semirings is a fintype, if the domain is a fintype.
Note: this instance can form a diamond with `subtype.fintype` in the
  presence of `fintype S`.-/
instance fintype_srange [fintype R] [decidable_eq S] (f : R →+* S) : fintype (srange f) :=
set.fintype_range f

end ring_hom

namespace subsemiring

instance : has_bot (subsemiring R) := ⟨(nat.cast_ring_hom R).srange⟩

instance : inhabited (subsemiring R) := ⟨⊥⟩

lemma coe_bot : ((⊥ : subsemiring R) : set R) = set.range (coe : ℕ → R) :=
(nat.cast_ring_hom R).coe_srange

lemma mem_bot {x : R} : x ∈ (⊥ : subsemiring R) ↔ ∃ n : ℕ, ↑n=x := ring_hom.mem_srange

/-- The inf of two subsemirings is their intersection. -/
instance : has_inf (subsemiring R) :=
⟨λ s t,
  { carrier := s ∩ t,
    .. s.to_submonoid ⊓ t.to_submonoid,
    .. s.to_add_submonoid ⊓ t.to_add_submonoid }⟩

@[simp] lemma coe_inf (p p' : subsemiring R) : ((p ⊓ p' : subsemiring R) : set R) = p ∩ p' := rfl

@[simp] lemma mem_inf {p p' : subsemiring R} {x : R} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' := iff.rfl

instance : has_Inf (subsemiring R) :=
⟨λ s, subsemiring.mk' (⋂ t ∈ s, ↑t) (⨅ t ∈ s, subsemiring.to_submonoid t) (by simp)
  (⨅ t ∈ s, subsemiring.to_add_submonoid t) (by simp)⟩

@[simp, norm_cast] lemma coe_Inf (S : set (subsemiring R)) :
  ((Inf S : subsemiring R) : set R) = ⋂ s ∈ S, ↑s := rfl

lemma mem_Inf {S : set (subsemiring R)} {x : R} : x ∈ Inf S ↔ ∀ p ∈ S, x ∈ p := set.mem_bInter_iff

@[simp] lemma Inf_to_submonoid (s : set (subsemiring R)) :
  (Inf s).to_submonoid = ⨅ t ∈ s, subsemiring.to_submonoid t :=
mk'_to_submonoid _ _

@[simp] lemma Inf_to_add_submonoid (s : set (subsemiring R)) :
  (Inf s).to_add_submonoid = ⨅ t ∈ s, subsemiring.to_add_submonoid t :=
mk'_to_add_submonoid _ _

/-- Subsemirings of a semiring form a complete lattice. -/
instance : complete_lattice (subsemiring R) :=
{ bot := (⊥),
  bot_le := λ s x hx, let ⟨n, hn⟩ := mem_bot.1 hx in hn ▸ s.coe_nat_mem n,
  top := (⊤),
  le_top := λ s x hx, trivial,
  inf := (⊓),
  inf_le_left := λ s t x, and.left,
  inf_le_right := λ s t x, and.right,
  le_inf := λ s t₁ t₂ h₁ h₂ x hx, ⟨h₁ hx, h₂ hx⟩,
  .. complete_lattice_of_Inf (subsemiring R)
    (λ s, is_glb.of_image (λ s t,
      show (s : set R) ≤ t ↔ s ≤ t, from set_like.coe_subset_coe) is_glb_binfi)}

lemma eq_top_iff' (A : subsemiring R) : A = ⊤ ↔ ∀ x : R, x ∈ A :=
eq_top_iff.trans ⟨λ h m, h $ mem_top m, λ h m _, h m⟩

section

/-- The center of a semiring `R` is the set of elements that commute with everything in `R` -/
def center (R) [semiring R] : subsemiring R :=
{ carrier := set.center R,
  zero_mem' := set.zero_mem_center R,
  add_mem' := λ a b, set.add_mem_center,
  .. submonoid.center R }

lemma coe_center (R) [semiring R] : ↑(center R) = set.center R := rfl

@[simp]
lemma center_to_submonoid (R) [semiring R] : (center R).to_submonoid = submonoid.center R := rfl

lemma mem_center_iff {R} [semiring R] {z : R} : z ∈ center R ↔ ∀ g, g * z = z * g :=
iff.rfl

instance decidable_mem_center {R} [semiring R] [decidable_eq R] [fintype R] :
  decidable_pred (∈ center R) :=
λ _, decidable_of_iff' _ mem_center_iff

@[simp] lemma center_eq_top (R) [comm_semiring R] : center R = ⊤ :=
set_like.coe_injective (set.center_eq_univ R)

/-- The center is commutative. -/
instance {R} [semiring R] : comm_semiring (center R) :=
{ ..submonoid.center.comm_monoid,
  ..(center R).to_semiring}

end

/-- The `subsemiring` generated by a set. -/
def closure (s : set R) : subsemiring R := Inf {S | s ⊆ S}

lemma mem_closure {x : R} {s : set R} : x ∈ closure s ↔ ∀ S : subsemiring R, s ⊆ S → x ∈ S :=
mem_Inf

/-- The subsemiring generated by a set includes the set. -/
@[simp] lemma subset_closure {s : set R} : s ⊆ closure s := λ x hx, mem_closure.2 $ λ S hS, hS hx

lemma not_mem_of_not_mem_closure {s : set R} {P : R} (hP : P ∉ closure s) : P ∉ s :=
λ h, hP (subset_closure h)

/-- A subsemiring `S` includes `closure s` if and only if it includes `s`. -/
@[simp]
lemma closure_le {s : set R} {t : subsemiring R} : closure s ≤ t ↔ s ⊆ t :=
⟨set.subset.trans subset_closure, λ h, Inf_le h⟩

/-- Subsemiring closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
lemma closure_mono ⦃s t : set R⦄ (h : s ⊆ t) : closure s ≤ closure t :=
closure_le.2 $ set.subset.trans h subset_closure

lemma closure_eq_of_le {s : set R} {t : subsemiring R} (h₁ : s ⊆ t) (h₂ : t ≤ closure s) :
  closure s = t :=
le_antisymm (closure_le.2 h₁) h₂

lemma mem_map_equiv {f : R ≃+* S} {K : subsemiring R} {x : S} :
  x ∈ K.map (f : R →+* S) ↔ f.symm x ∈ K :=
@set.mem_image_equiv _ _ ↑K f.to_equiv x

lemma map_equiv_eq_comap_symm (f : R ≃+* S) (K : subsemiring R) :
  K.map (f : R →+* S) = K.comap f.symm :=
set_like.coe_injective (f.to_equiv.image_eq_preimage K)

lemma comap_equiv_eq_map_symm (f : R ≃+* S) (K : subsemiring S) :
  K.comap (f : R →+* S) = K.map f.symm :=
(map_equiv_eq_comap_symm f.symm K).symm

end subsemiring

namespace submonoid

/-- The additive closure of a submonoid is a subsemiring. -/
def subsemiring_closure (M : submonoid R) : subsemiring R :=
{ one_mem' := add_submonoid.mem_closure.mpr (λ y hy, hy M.one_mem),
  mul_mem' := λ x y, M.mul_mem_add_closure,
  ..add_submonoid.closure (M : set R)}

lemma subsemiring_closure_coe :
  (M.subsemiring_closure : set R) = add_submonoid.closure (M : set R) := rfl

lemma subsemiring_closure_to_add_submonoid :
  M.subsemiring_closure.to_add_submonoid = add_submonoid.closure (M : set R) := rfl

/-- The `subsemiring` generated by a multiplicative submonoid coincides with the
`subsemiring.closure` of the submonoid itself . -/
lemma subsemiring_closure_eq_closure : M.subsemiring_closure = subsemiring.closure (M : set R) :=
begin
  ext,
  refine ⟨λ hx, _, λ hx, (subsemiring.mem_closure.mp hx) M.subsemiring_closure (λ s sM, _)⟩;
  rintros - ⟨H1, rfl⟩;
  rintros - ⟨H2, rfl⟩,
  { exact add_submonoid.mem_closure.mp hx H1.to_add_submonoid H2 },
  { exact H2 sM }
end

end submonoid

namespace subsemiring

@[simp]
lemma closure_submonoid_closure (s : set R) : closure ↑(submonoid.closure s) = closure s :=
le_antisymm
  (closure_le.mpr (λ y hy, (submonoid.mem_closure.mp hy) (closure s).to_submonoid subset_closure))
  (closure_mono (submonoid.subset_closure))

/-- The elements of the subsemiring closure of `M` are exactly the elements of the additive closure
of a multiplicative submonoid `M`. -/
lemma coe_closure_eq (s : set R) :
  (closure s : set R) = add_submonoid.closure (submonoid.closure s : set R) :=
by simp [← submonoid.subsemiring_closure_to_add_submonoid, submonoid.subsemiring_closure_eq_closure]

lemma mem_closure_iff {s : set R} {x} :
  x ∈ closure s ↔ x ∈ add_submonoid.closure (submonoid.closure s : set R) :=
set.ext_iff.mp (coe_closure_eq s) x

@[simp]
lemma closure_add_submonoid_closure {s : set R} : closure ↑(add_submonoid.closure s) = closure s :=
begin
  ext x,
  refine ⟨λ hx, _, λ hx, closure_mono add_submonoid.subset_closure hx⟩,
  rintros - ⟨H, rfl⟩,
  rintros - ⟨J, rfl⟩,
  refine (add_submonoid.mem_closure.mp (mem_closure_iff.mp hx)) H.to_add_submonoid (λ y hy, _),
  refine (submonoid.mem_closure.mp hy) H.to_submonoid (λ z hz, _),
  exact (add_submonoid.mem_closure.mp hz) H.to_add_submonoid (λ w hw, J hw),
end

/-- An induction principle for closure membership. If `p` holds for `0`, `1`, and all elements
of `s`, and is preserved under addition and multiplication, then `p` holds for all elements
of the closure of `s`. -/
@[elab_as_eliminator]
lemma closure_induction {s : set R} {p : R → Prop} {x} (h : x ∈ closure s)
  (Hs : ∀ x ∈ s, p x) (H0 : p 0) (H1 : p 1)
  (Hadd : ∀ x y, p x → p y → p (x + y)) (Hmul : ∀ x y, p x → p y → p (x * y)) : p x :=
(@closure_le _ _ _ ⟨p, H1, Hmul, H0, Hadd⟩).2 Hs h

lemma mem_closure_iff_exists_list {R} [semiring R] {s : set R} {x} : x ∈ closure s ↔
  ∃ L : list (list R), (∀ t ∈ L, ∀ y ∈ t, y ∈ s) ∧ (L.map list.prod).sum = x :=
⟨λ hx, add_submonoid.closure_induction (mem_closure_iff.1 hx)
  (λ x hx, suffices ∃ t : list R, (∀ y ∈ t, y ∈ s) ∧ t.prod = x,
    from let ⟨t, ht1, ht2⟩ := this in ⟨[t], list.forall_mem_singleton.2 ht1,
      by rw [list.map_singleton, list.sum_singleton, ht2]⟩,
    submonoid.closure_induction hx
      (λ x hx, ⟨[x], list.forall_mem_singleton.2 hx, one_mul x⟩)
      ⟨[], list.forall_mem_nil _, rfl⟩
      (λ x y ⟨t, ht1, ht2⟩ ⟨u, hu1, hu2⟩, ⟨t ++ u, list.forall_mem_append.2 ⟨ht1, hu1⟩,
        by rw [list.prod_append, ht2, hu2]⟩))
  ⟨[], list.forall_mem_nil _, rfl⟩
  (λ x y ⟨L, HL1, HL2⟩ ⟨M, HM1, HM2⟩, ⟨L ++ M, list.forall_mem_append.2 ⟨HL1, HM1⟩,
    by rw [list.map_append, list.sum_append, HL2, HM2]⟩),
λ ⟨L, HL1, HL2⟩, HL2 ▸ list_sum_mem _ (λ r hr, let ⟨t, ht1, ht2⟩ := list.mem_map.1 hr in
  ht2 ▸ list_prod_mem _ (λ y hy, subset_closure $ HL1 t ht1 y hy))⟩

variable (R)

/-- `closure` forms a Galois insertion with the coercion to set. -/
protected def gi : galois_insertion (@closure R _) coe :=
{ choice := λ s _, closure s,
  gc := λ s t, closure_le,
  le_l_u := λ s, subset_closure,
  choice_eq := λ s h, rfl }

variable {R}

/-- Closure of a subsemiring `S` equals `S`. -/
lemma closure_eq (s : subsemiring R) : closure (s : set R) = s := (subsemiring.gi R).l_u_eq s

@[simp] lemma closure_empty : closure (∅ : set R) = ⊥ := (subsemiring.gi R).gc.l_bot

@[simp] lemma closure_univ : closure (set.univ : set R) = ⊤ := @coe_top R _ ▸ closure_eq ⊤

lemma closure_union (s t : set R) : closure (s ∪ t) = closure s ⊔ closure t :=
(subsemiring.gi R).gc.l_sup

lemma closure_Union {ι} (s : ι → set R) : closure (⋃ i, s i) = ⨆ i, closure (s i) :=
(subsemiring.gi R).gc.l_supr

lemma closure_sUnion (s : set (set R)) : closure (⋃₀ s) = ⨆ t ∈ s, closure t :=
(subsemiring.gi R).gc.l_Sup

lemma map_sup (s t : subsemiring R) (f : R →+* S) : (s ⊔ t).map f = s.map f ⊔ t.map f :=
(gc_map_comap f).l_sup

lemma map_supr {ι : Sort*} (f : R →+* S) (s : ι → subsemiring R) :
  (supr s).map f = ⨆ i, (s i).map f :=
(gc_map_comap f).l_supr

lemma comap_inf (s t : subsemiring S) (f : R →+* S) : (s ⊓ t).comap f = s.comap f ⊓ t.comap f :=
(gc_map_comap f).u_inf

lemma comap_infi {ι : Sort*} (f : R →+* S) (s : ι → subsemiring S) :
  (infi s).comap f = ⨅ i, (s i).comap f :=
(gc_map_comap f).u_infi

@[simp] lemma map_bot (f : R →+* S) : (⊥ : subsemiring R).map f = ⊥ :=
(gc_map_comap f).l_bot

@[simp] lemma comap_top (f : R →+* S) : (⊤ : subsemiring S).comap f = ⊤ :=
(gc_map_comap f).u_top

/-- Given `subsemiring`s `s`, `t` of semirings `R`, `S` respectively, `s.prod t` is `s × t`
as a subsemiring of `R × S`. -/
def prod (s : subsemiring R) (t : subsemiring S) : subsemiring (R × S) :=
{ carrier := (s : set R).prod t,
  .. s.to_submonoid.prod t.to_submonoid, .. s.to_add_submonoid.prod t.to_add_submonoid}

@[norm_cast]
lemma coe_prod (s : subsemiring R) (t : subsemiring S) :
  (s.prod t : set (R × S)) = (s : set R).prod (t : set S) :=
rfl

lemma mem_prod {s : subsemiring R} {t : subsemiring S} {p : R × S} :
  p ∈ s.prod t ↔ p.1 ∈ s ∧ p.2 ∈ t := iff.rfl

@[mono] lemma prod_mono ⦃s₁ s₂ : subsemiring R⦄ (hs : s₁ ≤ s₂) ⦃t₁ t₂ : subsemiring S⦄
  (ht : t₁ ≤ t₂) : s₁.prod t₁ ≤ s₂.prod t₂ :=
set.prod_mono hs ht

lemma prod_mono_right (s : subsemiring R) : monotone (λ t : subsemiring S, s.prod t) :=
prod_mono (le_refl s)

lemma prod_mono_left (t : subsemiring S) : monotone (λ s : subsemiring R, s.prod t) :=
λ s₁ s₂ hs, prod_mono hs (le_refl t)

lemma prod_top (s : subsemiring R) :
  s.prod (⊤ : subsemiring S) = s.comap (ring_hom.fst R S) :=
ext $ λ x, by simp [mem_prod, monoid_hom.coe_fst]

lemma top_prod (s : subsemiring S) :
  (⊤ : subsemiring R).prod s = s.comap (ring_hom.snd R S) :=
ext $ λ x, by simp [mem_prod, monoid_hom.coe_snd]

@[simp]
lemma top_prod_top : (⊤ : subsemiring R).prod (⊤ : subsemiring S) = ⊤ :=
(top_prod _).trans $ comap_top _

/-- Product of subsemirings is isomorphic to their product as monoids. -/
def prod_equiv (s : subsemiring R) (t : subsemiring S) : s.prod t ≃+* s × t :=
{ map_mul' := λ x y, rfl, map_add' := λ x y, rfl, .. equiv.set.prod ↑s ↑t }

lemma mem_supr_of_directed {ι} [hι : nonempty ι] {S : ι → subsemiring R} (hS : directed (≤) S)
  {x : R} :
  x ∈ (⨆ i, S i) ↔ ∃ i, x ∈ S i :=
begin
  refine ⟨_, λ ⟨i, hi⟩, (set_like.le_def.1 $ le_supr S i) hi⟩,
  let U : subsemiring R := subsemiring.mk' (⋃ i, (S i : set R))
    (⨆ i, (S i).to_submonoid) (submonoid.coe_supr_of_directed $ hS.mono_comp _ (λ _ _, id))
    (⨆ i, (S i).to_add_submonoid) (add_submonoid.coe_supr_of_directed $ hS.mono_comp _ (λ _ _, id)),
  suffices : (⨆ i, S i) ≤ U, by simpa using @this x,
  exact supr_le (λ i x hx, set.mem_Union.2 ⟨i, hx⟩),
end

lemma coe_supr_of_directed {ι} [hι : nonempty ι] {S : ι → subsemiring R} (hS : directed (≤) S) :
  ((⨆ i, S i : subsemiring R) : set R) = ⋃ i, ↑(S i) :=
set.ext $ λ x, by simp [mem_supr_of_directed hS]

lemma mem_Sup_of_directed_on {S : set (subsemiring R)} (Sne : S.nonempty)
  (hS : directed_on (≤) S) {x : R} :
  x ∈ Sup S ↔ ∃ s ∈ S, x ∈ s :=
begin
  haveI : nonempty S := Sne.to_subtype,
  simp only [Sup_eq_supr', mem_supr_of_directed hS.directed_coe, set_coe.exists, subtype.coe_mk]
end

lemma coe_Sup_of_directed_on {S : set (subsemiring R)} (Sne : S.nonempty) (hS : directed_on (≤) S) :
  (↑(Sup S) : set R) = ⋃ s ∈ S, ↑s :=
set.ext $ λ x, by simp [mem_Sup_of_directed_on Sne hS]

end subsemiring

namespace ring_hom

variables [non_assoc_semiring T] {s : subsemiring R}

open subsemiring

/-- Restriction of a ring homomorphism to a subsemiring of the domain. -/
def srestrict (f : R →+* S) (s : subsemiring R) : s →+* S := f.comp s.subtype

@[simp] lemma srestrict_apply (f : R →+* S) (x : s) : f.srestrict s x = f x := rfl

/-- Restriction of a ring homomorphism to a subsemiring of the codomain. -/
def cod_srestrict (f : R →+* S) (s : subsemiring S) (h : ∀ x, f x ∈ s) : R →+* s :=
{ to_fun := λ n, ⟨f n, h n⟩,
  .. (f : R →* S).cod_mrestrict s.to_submonoid h,
  .. (f : R →+ S).cod_mrestrict s.to_add_submonoid h }

/-- Restriction of a ring homomorphism to its range interpreted as a subsemiring.

This is the bundled version of `set.range_factorization`. -/
def srange_restrict (f : R →+* S) : R →+* f.srange :=
f.cod_srestrict f.srange f.mem_srange_self

@[simp] lemma coe_srange_restrict (f : R →+* S) (x : R) :
  (f.srange_restrict x : S) = f x :=
rfl

lemma srange_restrict_surjective (f : R →+* S) : function.surjective f.srange_restrict :=
λ ⟨y, hy⟩, let ⟨x, hx⟩ := mem_srange.mp hy in ⟨x, subtype.ext hx⟩

lemma srange_top_iff_surjective {f : R →+* S} :
  f.srange = (⊤ : subsemiring S) ↔ function.surjective f :=
set_like.ext'_iff.trans $ iff.trans (by rw [coe_srange, coe_top]) set.range_iff_surjective

/-- The range of a surjective ring homomorphism is the whole of the codomain. -/
lemma srange_top_of_surjective (f : R →+* S) (hf : function.surjective f) :
  f.srange = (⊤ : subsemiring S) :=
srange_top_iff_surjective.2 hf

/-- The subsemiring of elements `x : R` such that `f x = g x` -/
def eq_slocus (f g : R →+* S) : subsemiring R :=
{ carrier := {x | f x = g x}, .. (f : R →* S).eq_mlocus g, .. (f : R →+ S).eq_mlocus g }

/-- If two ring homomorphisms are equal on a set, then they are equal on its subsemiring closure. -/
lemma eq_on_sclosure {f g : R →+* S} {s : set R} (h : set.eq_on f g s) :
  set.eq_on f g (closure s) :=
show closure s ≤ f.eq_slocus g, from closure_le.2 h

lemma eq_of_eq_on_stop {f g : R →+* S} (h : set.eq_on f g (⊤ : subsemiring R)) :
  f = g :=
ext $ λ x, h trivial

lemma eq_of_eq_on_sdense {s : set R} (hs : closure s = ⊤) {f g : R →+* S} (h : s.eq_on f g) :
  f = g :=
eq_of_eq_on_stop $ hs ▸ eq_on_sclosure h

lemma sclosure_preimage_le (f : R →+* S) (s : set S) :
  closure (f ⁻¹' s) ≤ (closure s).comap f :=
closure_le.2 $ λ x hx, set_like.mem_coe.2 $ mem_comap.2 $ subset_closure hx

/-- The image under a ring homomorphism of the subsemiring generated by a set equals
the subsemiring generated by the image of the set. -/
lemma map_sclosure (f : R →+* S) (s : set R) :
  (closure s).map f = closure (f '' s) :=
le_antisymm
  (map_le_iff_le_comap.2 $ le_trans (closure_mono $ set.subset_preimage_image _ _)
    (sclosure_preimage_le _ _))
  (closure_le.2 $ set.image_subset _ subset_closure)

end ring_hom

namespace subsemiring

open ring_hom

/-- The ring homomorphism associated to an inclusion of subsemirings. -/
def inclusion {S T : subsemiring R} (h : S ≤ T) : S →* T :=
S.subtype.cod_srestrict _ (λ x, h x.2)

@[simp] lemma srange_subtype (s : subsemiring R) : s.subtype.srange = s :=
set_like.coe_injective $ (coe_srange _).trans subtype.range_coe

@[simp]
lemma range_fst : (fst R S).srange = ⊤ :=
(fst R S).srange_top_of_surjective $ prod.fst_surjective

@[simp]
lemma range_snd : (snd R S).srange = ⊤ :=
(snd R S).srange_top_of_surjective $ prod.snd_surjective

@[simp]
lemma prod_bot_sup_bot_prod (s : subsemiring R) (t : subsemiring S) :
  (s.prod ⊥) ⊔ (prod ⊥ t) = s.prod t :=
le_antisymm (sup_le (prod_mono_right s bot_le) (prod_mono_left t bot_le)) $
assume p hp, prod.fst_mul_snd p ▸ mul_mem _
  ((le_sup_left : s.prod ⊥ ≤ s.prod ⊥ ⊔ prod ⊥ t) ⟨hp.1, set_like.mem_coe.2 $ one_mem ⊥⟩)
  ((le_sup_right : prod ⊥ t ≤ s.prod ⊥ ⊔ prod ⊥ t) ⟨set_like.mem_coe.2 $ one_mem ⊥, hp.2⟩)

end subsemiring

namespace ring_equiv

variables {s t : subsemiring R}

/-- Makes the identity isomorphism from a proof two subsemirings of a multiplicative
    monoid are equal. -/
def subsemiring_congr (h : s = t) : s ≃+* t :=
{ map_mul' :=  λ _ _, rfl, map_add' := λ _ _, rfl, ..equiv.set_congr $ congr_arg _ h }

/-- Restrict a ring homomorphism with a left inverse to a ring isomorphism to its
`ring_hom.srange`. -/
def sof_left_inverse {g : S → R} {f : R →+* S} (h : function.left_inverse g f) :
  R ≃+* f.srange :=
{ to_fun := λ x, f.srange_restrict x,
  inv_fun := λ x, (g ∘ f.srange.subtype) x,
  left_inv := h,
  right_inv := λ x, subtype.ext $
    let ⟨x', hx'⟩ := ring_hom.mem_srange.mp x.prop in
    show f (g x) = x, by rw [←hx', h x'],
  ..f.srange_restrict }

@[simp] lemma sof_left_inverse_apply
  {g : S → R} {f : R →+* S} (h : function.left_inverse g f) (x : R) :
  ↑(sof_left_inverse h x) = f x := rfl

@[simp] lemma sof_left_inverse_symm_apply
  {g : S → R} {f : R →+* S} (h : function.left_inverse g f) (x : f.srange) :
  (sof_left_inverse h).symm x = g x := rfl

end ring_equiv

/-! ### Actions by `subsemiring`s

These are just copies of the definitions about `submonoid` starting from `submonoid.mul_action`.
The only new result is `subsemiring.module`.

When `R` is commutative, `algebra.of_subsemiring` provides a stronger result than those found in
this file, which uses the same scalar action.
-/
section actions

namespace subsemiring

variables {R' α β : Type*} [semiring R']

/-- The action by a subsemiring is the action by the underlying semiring. -/
instance [mul_action R' α] (S : subsemiring R') : mul_action S α :=
S.to_submonoid.mul_action

lemma smul_def [mul_action R' α] {S : subsemiring R'} (g : S) (m : α) : g • m = (g : R') • m := rfl

instance smul_comm_class_left
  [mul_action R' β] [has_scalar α β] [smul_comm_class R' α β] (S : subsemiring R') :
  smul_comm_class S α β :=
S.to_submonoid.smul_comm_class_left

instance smul_comm_class_right
  [has_scalar α β] [mul_action R' β] [smul_comm_class α R' β] (S : subsemiring R') :
  smul_comm_class α S β :=
S.to_submonoid.smul_comm_class_right

/-- Note that this provides `is_scalar_tower S R R` which is needed by `smul_mul_assoc`. -/
instance
  [has_scalar α β] [mul_action R' α] [mul_action R' β] [is_scalar_tower R' α β]
  (S : subsemiring R') :
  is_scalar_tower S α β :=
S.to_submonoid.is_scalar_tower

instance [mul_action R' α] [has_faithful_scalar R' α] (S : subsemiring R') :
  has_faithful_scalar S α :=
S.to_submonoid.has_faithful_scalar

/-- The action by a subsemiring is the action by the underlying semiring. -/
instance [add_monoid α] [distrib_mul_action R' α] (S : subsemiring R') : distrib_mul_action S α :=
S.to_submonoid.distrib_mul_action

/-- The action by a subsemiring is the action by the underlying semiring. -/
instance [monoid α] [mul_distrib_mul_action R' α] (S : subsemiring R') :
  mul_distrib_mul_action S α :=
S.to_submonoid.mul_distrib_mul_action

/-- The action by a subsemiring is the action by the underlying semiring. -/
instance [add_comm_monoid α] [module R' α] (S : subsemiring R') : module S α :=
{ smul := (•), .. module.comp_hom _ S.subtype }

end subsemiring

end actions

-- While this definition is not about `subsemiring`s, this is the earliest we have
-- both `ordered_semiring` and `submonoid` available.


/-- Submonoid of positive elements of an ordered semiring. -/
def pos_submonoid (R : Type*) [ordered_semiring R] [nontrivial R] : submonoid R :=
{ carrier := {x | 0 < x},
  one_mem' := show (0 : R) < 1, from zero_lt_one,
  mul_mem' := λ x y (hx : 0 < x) (hy : 0 < y), mul_pos hx hy }

@[simp] lemma mem_pos_monoid {R : Type*} [ordered_semiring R] [nontrivial R] (u : units R) :
  ↑u ∈ pos_submonoid R ↔ (0 : R) < u := iff.rfl
