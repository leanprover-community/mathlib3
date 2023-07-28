/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov, Yakov Pechersky, Jireh Loreaux
-/
import group_theory.subsemigroup.basic
import algebra.group.prod
import algebra.group.type_tags

/-!
# Operations on `subsemigroup`s

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define various operations on `subsemigroup`s and `mul_hom`s.

## Main definitions

### Conversion between multiplicative and additive definitions

* `subsemigroup.to_add_subsemigroup`, `subsemigroup.to_add_subsemigroup'`,
  `add_subsemigroup.to_subsemigroup`, `add_subsemigroup.to_subsemigroup'`:
  convert between multiplicative and additive subsemigroups of `M`,
  `multiplicative M`, and `additive M`. These are stated as `order_iso`s.

### (Commutative) semigroup structure on a subsemigroup

* `subsemigroup.to_semigroup`, `subsemigroup.to_comm_semigroup`: a subsemigroup inherits a
  (commutative) semigroup structure.

### Operations on subsemigroups

* `subsemigroup.comap`: preimage of a subsemigroup under a semigroup homomorphism as a subsemigroup
  of the domain;
* `subsemigroup.map`: image of a subsemigroup under a semigroup homomorphism as a subsemigroup of
  the codomain;
* `subsemigroup.prod`: product of two subsemigroups `s : subsemigroup M` and `t : subsemigroup N`
  as a subsemigroup of `M × N`;

### Semigroup homomorphisms between subsemigroups

* `subsemigroup.subtype`: embedding of a subsemigroup into the ambient semigroup.
* `subsemigroup.inclusion`: given two subsemigroups `S`, `T` such that `S ≤ T`, `S.inclusion T` is
  the inclusion of `S` into `T` as a semigroup homomorphism;
* `mul_equiv.subsemigroup_congr`: converts a proof of `S = T` into a semigroup isomorphism between
  `S` and `T`.
* `subsemigroup.prod_equiv`: semigroup isomorphism between `s.prod t` and `s × t`;

### Operations on `mul_hom`s

* `mul_hom.srange`: range of a semigroup homomorphism as a subsemigroup of the codomain;
* `mul_hom.restrict`: restrict a semigroup homomorphism to a subsemigroup;
* `mul_hom.cod_restrict`: restrict the codomain of a semigroup homomorphism to a subsemigroup;
* `mul_hom.srange_restrict`: restrict a semigroup homomorphism to its range;

### Implementation notes

This file follows closely `group_theory/submonoid/operations.lean`, omitting only that which is
necessary.

## Tags

subsemigroup, range, product, map, comap
-/

variables {M N P σ : Type*}

/-!
### Conversion to/from `additive`/`multiplicative`
-/

section

variables [has_mul M]

/-- Subsemigroups of semigroup `M` are isomorphic to additive subsemigroups of `additive M`. -/
@[simps]
def subsemigroup.to_add_subsemigroup : subsemigroup M ≃o add_subsemigroup (additive M) :=
{ to_fun := λ S,
  { carrier := additive.to_mul ⁻¹' S,
    add_mem' := λ _ _, S.mul_mem' },
  inv_fun := λ S,
  { carrier := additive.of_mul ⁻¹' S,
    mul_mem' := λ _ _, S.add_mem' },
  left_inv := λ x, by cases x; refl,
  right_inv := λ x, by cases x; refl,
  map_rel_iff' := λ a b, iff.rfl, }

/-- Additive subsemigroups of an additive semigroup `additive M` are isomorphic to subsemigroups
of `M`. -/
abbreviation add_subsemigroup.to_subsemigroup' : add_subsemigroup (additive M) ≃o subsemigroup M :=
subsemigroup.to_add_subsemigroup.symm

lemma subsemigroup.to_add_subsemigroup_closure (S : set M) :
  (subsemigroup.closure S).to_add_subsemigroup = add_subsemigroup.closure (additive.to_mul ⁻¹' S) :=
le_antisymm
  (subsemigroup.to_add_subsemigroup.le_symm_apply.1 $
    subsemigroup.closure_le.2 add_subsemigroup.subset_closure)
  (add_subsemigroup.closure_le.2 subsemigroup.subset_closure)

lemma add_subsemigroup.to_subsemigroup'_closure (S : set (additive M)) :
  (add_subsemigroup.closure S).to_subsemigroup' =
    subsemigroup.closure (multiplicative.of_add ⁻¹' S) :=
le_antisymm
  (add_subsemigroup.to_subsemigroup'.le_symm_apply.1 $
    add_subsemigroup.closure_le.2 subsemigroup.subset_closure)
  (subsemigroup.closure_le.2 add_subsemigroup.subset_closure)

end

section

variables {A : Type*} [has_add A]

/-- Additive subsemigroups of an additive semigroup `A` are isomorphic to
multiplicative subsemigroups of `multiplicative A`. -/
@[simps]
def add_subsemigroup.to_subsemigroup : add_subsemigroup A ≃o subsemigroup (multiplicative A) :=
{ to_fun := λ S,
  { carrier := multiplicative.to_add ⁻¹' S,
    mul_mem' := λ _ _, S.add_mem' },
  inv_fun := λ S,
  { carrier := multiplicative.of_add ⁻¹' S,
    add_mem' := λ _ _, S.mul_mem' },
  left_inv := λ x, by cases x; refl,
  right_inv := λ x, by cases x; refl,
  map_rel_iff' := λ a b, iff.rfl, }

/-- Subsemigroups of a semigroup `multiplicative A` are isomorphic to additive subsemigroups
of `A`. -/
abbreviation subsemigroup.to_add_subsemigroup' :
  subsemigroup (multiplicative A) ≃o add_subsemigroup A :=
add_subsemigroup.to_subsemigroup.symm

lemma add_subsemigroup.to_subsemigroup_closure (S : set A) :
  (add_subsemigroup.closure S).to_subsemigroup =
    subsemigroup.closure (multiplicative.to_add ⁻¹' S) :=
le_antisymm
  (add_subsemigroup.to_subsemigroup.to_galois_connection.l_le $
    add_subsemigroup.closure_le.2 subsemigroup.subset_closure)
  (subsemigroup.closure_le.2 add_subsemigroup.subset_closure)

lemma subsemigroup.to_add_subsemigroup'_closure (S : set (multiplicative A)) :
  (subsemigroup.closure S).to_add_subsemigroup' =
    add_subsemigroup.closure (additive.of_mul ⁻¹' S) :=
le_antisymm
  (subsemigroup.to_add_subsemigroup'.to_galois_connection.l_le $
    subsemigroup.closure_le.2 add_subsemigroup.subset_closure)
  (add_subsemigroup.closure_le.2 subsemigroup.subset_closure)

end

namespace subsemigroup

open set

/-!
### `comap` and `map`
-/

variables [has_mul M] [has_mul N] [has_mul P] (S : subsemigroup M)

/-- The preimage of a subsemigroup along a semigroup homomorphism is a subsemigroup. -/
@[to_additive "The preimage of an `add_subsemigroup` along an `add_semigroup` homomorphism is an
`add_subsemigroup`."]
def comap (f : M →ₙ* N) (S : subsemigroup N) : subsemigroup M :=
{ carrier := (f ⁻¹' S),
  mul_mem' := λ a b ha hb,
    show f (a * b) ∈ S, by rw map_mul; exact mul_mem ha hb }

@[simp, to_additive]
lemma coe_comap (S : subsemigroup N) (f : M →ₙ* N) : (S.comap f : set M) = f ⁻¹' S := rfl

@[simp, to_additive]
lemma mem_comap {S : subsemigroup N} {f : M →ₙ* N} {x : M} : x ∈ S.comap f ↔ f x ∈ S := iff.rfl

@[to_additive]
lemma comap_comap (S : subsemigroup P) (g : N →ₙ* P) (f : M →ₙ* N) :
  (S.comap g).comap f = S.comap (g.comp f) :=
rfl

@[simp, to_additive]
lemma comap_id (S : subsemigroup P) : S.comap (mul_hom.id _) = S :=
ext (by simp)

/-- The image of a subsemigroup along a semigroup homomorphism is a subsemigroup. -/
@[to_additive "The image of an `add_subsemigroup` along an `add_semigroup` homomorphism is
an `add_subsemigroup`."]
def map (f : M →ₙ* N) (S : subsemigroup M) : subsemigroup N :=
{ carrier := (f '' S),
  mul_mem' := begin rintros _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩,
    exact ⟨x * y, @mul_mem (subsemigroup M) M _ _ _ _ _ _ hx hy, by rw map_mul; refl⟩ end }

@[simp, to_additive]
lemma coe_map (f : M →ₙ* N) (S : subsemigroup M) :
  (S.map f : set N) = f '' S := rfl

@[simp, to_additive]
lemma mem_map {f : M →ₙ* N} {S : subsemigroup M} {y : N} :
  y ∈ S.map f ↔ ∃ x ∈ S, f x = y :=
mem_image_iff_bex

@[to_additive]
lemma mem_map_of_mem (f : M →ₙ* N) {S : subsemigroup M} {x : M} (hx : x ∈ S) : f x ∈ S.map f :=
mem_image_of_mem f hx

@[to_additive]
lemma apply_coe_mem_map (f : M →ₙ* N) (S : subsemigroup M) (x : S) : f x ∈ S.map f :=
mem_map_of_mem f x.prop

@[to_additive]
lemma map_map (g : N →ₙ* P) (f : M →ₙ* N) : (S.map f).map g = S.map (g.comp f) :=
set_like.coe_injective $ image_image _ _ _

@[to_additive]
lemma mem_map_iff_mem {f : M →ₙ* N} (hf : function.injective f) {S : subsemigroup M} {x : M} :
  f x ∈ S.map f ↔ x ∈ S :=
hf.mem_set_image

@[to_additive]
lemma map_le_iff_le_comap {f : M →ₙ* N} {S : subsemigroup M} {T : subsemigroup N} :
  S.map f ≤ T ↔ S ≤ T.comap f :=
image_subset_iff

@[to_additive]
lemma gc_map_comap (f : M →ₙ* N) : galois_connection (map f) (comap f) :=
λ S T, map_le_iff_le_comap

@[to_additive]
lemma map_le_of_le_comap {T : subsemigroup N} {f : M →ₙ* N} : S ≤ T.comap f → S.map f ≤ T :=
(gc_map_comap f).l_le

@[to_additive]
lemma le_comap_of_map_le {T : subsemigroup N} {f : M →ₙ* N} : S.map f ≤ T → S ≤ T.comap f :=
(gc_map_comap f).le_u

@[to_additive]
lemma le_comap_map {f : M →ₙ* N} : S ≤ (S.map f).comap f :=
(gc_map_comap f).le_u_l _

@[to_additive]
lemma map_comap_le {S : subsemigroup N} {f : M →ₙ* N} : (S.comap f).map f ≤ S :=
(gc_map_comap f).l_u_le _

@[to_additive]
lemma monotone_map {f : M →ₙ* N} : monotone (map f) :=
(gc_map_comap f).monotone_l

@[to_additive]
lemma monotone_comap {f : M →ₙ* N} : monotone (comap f) :=
(gc_map_comap f).monotone_u

@[simp, to_additive]
lemma map_comap_map {f : M →ₙ* N} : ((S.map f).comap f).map f = S.map f :=
(gc_map_comap f).l_u_l_eq_l _

@[simp, to_additive]
lemma comap_map_comap {S : subsemigroup N} {f : M →ₙ* N} :
  ((S.comap f).map f).comap f = S.comap f :=
(gc_map_comap f).u_l_u_eq_u _

@[to_additive]
lemma map_sup (S T : subsemigroup M) (f : M →ₙ* N) : (S ⊔ T).map f = S.map f ⊔ T.map f :=
(gc_map_comap f).l_sup

@[to_additive]
lemma map_supr {ι : Sort*} (f : M →ₙ* N) (s : ι → subsemigroup M) :
  (supr s).map f = ⨆ i, (s i).map f :=
(gc_map_comap f).l_supr

@[to_additive]
lemma comap_inf (S T : subsemigroup N) (f : M →ₙ* N) : (S ⊓ T).comap f = S.comap f ⊓ T.comap f :=
(gc_map_comap f).u_inf

@[to_additive]
lemma comap_infi {ι : Sort*} (f : M →ₙ* N) (s : ι → subsemigroup N) :
  (infi s).comap f = ⨅ i, (s i).comap f :=
(gc_map_comap f).u_infi

@[simp, to_additive] lemma map_bot (f : M →ₙ* N) : (⊥ : subsemigroup M).map f = ⊥ :=
(gc_map_comap f).l_bot

@[simp, to_additive] lemma comap_top (f : M →ₙ* N) : (⊤ : subsemigroup N).comap f = ⊤ :=
(gc_map_comap f).u_top

@[simp, to_additive] lemma map_id (S : subsemigroup M) : S.map (mul_hom.id M) = S :=
ext (λ x, ⟨λ ⟨_, h, rfl⟩, h, λ h, ⟨_, h, rfl⟩⟩)

section galois_coinsertion

variables {ι : Type*} {f : M →ₙ* N} (hf : function.injective f)

include hf

/-- `map f` and `comap f` form a `galois_coinsertion` when `f` is injective. -/
@[to_additive /-" `map f` and `comap f` form a `galois_coinsertion` when `f` is injective. "-/]
def gci_map_comap : galois_coinsertion (map f) (comap f) :=
(gc_map_comap f).to_galois_coinsertion
  (λ S x, by simp [mem_comap, mem_map, hf.eq_iff])

@[to_additive]
lemma comap_map_eq_of_injective (S : subsemigroup M) : (S.map f).comap f = S :=
(gci_map_comap hf).u_l_eq _

@[to_additive]
lemma comap_surjective_of_injective : function.surjective (comap f) :=
(gci_map_comap hf).u_surjective

@[to_additive]
lemma map_injective_of_injective : function.injective (map f) :=
(gci_map_comap hf).l_injective

@[to_additive]
lemma comap_inf_map_of_injective (S T : subsemigroup M) : (S.map f ⊓ T.map f).comap f = S ⊓ T :=
(gci_map_comap hf).u_inf_l _ _

@[to_additive]
lemma comap_infi_map_of_injective (S : ι → subsemigroup M) : (⨅ i, (S i).map f).comap f = infi S :=
(gci_map_comap hf).u_infi_l _

@[to_additive]
lemma comap_sup_map_of_injective (S T : subsemigroup M) : (S.map f ⊔ T.map f).comap f = S ⊔ T :=
(gci_map_comap hf).u_sup_l _ _

@[to_additive]
lemma comap_supr_map_of_injective (S : ι → subsemigroup M) : (⨆ i, (S i).map f).comap f = supr S :=
(gci_map_comap hf).u_supr_l _

@[to_additive]
lemma map_le_map_iff_of_injective {S T : subsemigroup M} : S.map f ≤ T.map f ↔ S ≤ T :=
(gci_map_comap hf).l_le_l_iff

@[to_additive]
lemma map_strict_mono_of_injective : strict_mono (map f) :=
(gci_map_comap hf).strict_mono_l

end galois_coinsertion

section galois_insertion

variables {ι : Type*} {f : M →ₙ* N} (hf : function.surjective f)

include hf

/-- `map f` and `comap f` form a `galois_insertion` when `f` is surjective. -/
@[to_additive /-" `map f` and `comap f` form a `galois_insertion` when `f` is surjective. "-/]
def gi_map_comap : galois_insertion (map f) (comap f) :=
(gc_map_comap f).to_galois_insertion
  (λ S x h, let ⟨y, hy⟩ := hf x in mem_map.2 ⟨y, by simp [hy, h]⟩)

@[to_additive]
lemma map_comap_eq_of_surjective (S : subsemigroup N) : (S.comap f).map f = S :=
(gi_map_comap hf).l_u_eq _

@[to_additive]
lemma map_surjective_of_surjective : function.surjective (map f) :=
(gi_map_comap hf).l_surjective

@[to_additive]
lemma comap_injective_of_surjective : function.injective (comap f) :=
(gi_map_comap hf).u_injective

@[to_additive]
lemma map_inf_comap_of_surjective (S T : subsemigroup N) : (S.comap f ⊓ T.comap f).map f = S ⊓ T :=
(gi_map_comap hf).l_inf_u _ _

@[to_additive]
lemma map_infi_comap_of_surjective (S : ι → subsemigroup N) : (⨅ i, (S i).comap f).map f = infi S :=
(gi_map_comap hf).l_infi_u _

@[to_additive]
lemma map_sup_comap_of_surjective (S T : subsemigroup N) : (S.comap f ⊔ T.comap f).map f = S ⊔ T :=
(gi_map_comap hf).l_sup_u _ _

@[to_additive]
lemma map_supr_comap_of_surjective (S : ι → subsemigroup N) : (⨆ i, (S i).comap f).map f = supr S :=
(gi_map_comap hf).l_supr_u _

@[to_additive]
lemma comap_le_comap_iff_of_surjective {S T : subsemigroup N} : S.comap f ≤ T.comap f ↔ S ≤ T :=
(gi_map_comap hf).u_le_u_iff

@[to_additive]
lemma comap_strict_mono_of_surjective : strict_mono (comap f) :=
(gi_map_comap hf).strict_mono_u

end galois_insertion

end subsemigroup

namespace mul_mem_class

variables {A : Type*} [has_mul M] [set_like A M] [hA : mul_mem_class A M] (S' : A)
include hA

/-- A submagma of a magma inherits a multiplication. -/
@[to_additive "An additive submagma of an additive magma inherits an addition.",
priority 900] -- lower priority so other instances are found first
instance has_mul : has_mul S' := ⟨λ a b, ⟨a.1 * b.1, mul_mem a.2 b.2⟩⟩

@[simp, norm_cast, to_additive, priority 900]
-- lower priority so later simp lemmas are used first; to appease simp_nf
lemma coe_mul (x y : S') : (↑(x * y) : M) = ↑x * ↑y := rfl

@[simp, to_additive, priority 900]
-- lower priority so later simp lemmas are used first; to appease simp_nf
lemma mk_mul_mk (x y : M) (hx : x ∈ S') (hy : y ∈ S') :
  (⟨x, hx⟩ : S') * ⟨y, hy⟩ = ⟨x * y, mul_mem hx hy⟩ := rfl

@[to_additive] lemma mul_def (x y : S') : x * y = ⟨x * y, mul_mem x.2 y.2⟩ := rfl

omit hA

/-- A subsemigroup of a semigroup inherits a semigroup structure. -/
@[to_additive "An `add_subsemigroup` of an `add_semigroup` inherits an `add_semigroup` structure."]
instance to_semigroup {M : Type*} [semigroup M] {A : Type*} [set_like A M] [mul_mem_class A M]
  (S : A) : semigroup S :=
subtype.coe_injective.semigroup coe (λ _ _, rfl)

/-- A subsemigroup of a `comm_semigroup` is a `comm_semigroup`. -/
@[to_additive "An `add_subsemigroup` of an `add_comm_semigroup` is an `add_comm_semigroup`."]
instance to_comm_semigroup {M} [comm_semigroup M] {A : Type*} [set_like A M] [mul_mem_class A M]
  (S : A) : comm_semigroup S :=
subtype.coe_injective.comm_semigroup coe (λ _ _, rfl)

include hA

/-- The natural semigroup hom from a subsemigroup of semigroup `M` to `M`. -/
@[to_additive "The natural semigroup hom from an `add_subsemigroup` of `add_semigroup` `M` to `M`."]
def subtype : S' →ₙ* M := ⟨coe, λ _ _, rfl⟩

@[simp, to_additive] theorem coe_subtype : (mul_mem_class.subtype S' : S' → M) = coe := rfl

end mul_mem_class

namespace subsemigroup

variables [has_mul M] [has_mul N] [has_mul P] (S : subsemigroup M)

/-- The top subsemigroup is isomorphic to the semigroup. -/
@[to_additive "The top additive subsemigroup is isomorphic to the additive semigroup.", simps]
def top_equiv : (⊤ : subsemigroup M) ≃* M :=
{ to_fun    := λ x, x,
  inv_fun   := λ x, ⟨x, mem_top x⟩,
  left_inv  := λ x, x.eta _,
  right_inv := λ _, rfl,
  map_mul'  := λ _ _, rfl }

@[simp, to_additive] lemma top_equiv_to_mul_hom :
  (top_equiv : _ ≃* M).to_mul_hom = mul_mem_class.subtype (⊤ : subsemigroup M) :=
rfl

/-- A subsemigroup is isomorphic to its image under an injective function -/
@[to_additive "An additive subsemigroup is isomorphic to its image under an injective function"]
noncomputable def equiv_map_of_injective
  (f : M →ₙ* N) (hf : function.injective f) : S ≃* S.map f :=
{ map_mul' := λ _ _, subtype.ext (map_mul f _ _), ..equiv.set.image f S hf }

@[simp, to_additive] lemma coe_equiv_map_of_injective_apply
  (f : M →ₙ* N) (hf : function.injective f) (x : S) :
  (equiv_map_of_injective S f hf x : N) = f x := rfl

@[simp, to_additive]
lemma closure_closure_coe_preimage {s : set M} : closure ((coe : closure s → M) ⁻¹' s) = ⊤ :=
eq_top_iff.2 $ λ x, subtype.rec_on x $ λ x hx _, begin
  refine closure_induction' _ (λ g hg, _) (λ g₁ g₂ hg₁ hg₂, _) hx,
  { exact subset_closure hg },
  { exact subsemigroup.mul_mem _ },
end

/-- Given `subsemigroup`s `s`, `t` of semigroups `M`, `N` respectively, `s × t` as a subsemigroup
of `M × N`. -/
@[to_additive prod "Given `add_subsemigroup`s `s`, `t` of `add_semigroup`s `A`, `B` respectively,
`s × t` as an `add_subsemigroup` of `A × B`."]
def prod (s : subsemigroup M) (t : subsemigroup N) : subsemigroup (M × N) :=
{ carrier := s ×ˢ t,
  mul_mem' := λ p q hp hq, ⟨s.mul_mem hp.1 hq.1, t.mul_mem hp.2 hq.2⟩ }

@[to_additive coe_prod]
lemma coe_prod (s : subsemigroup M) (t : subsemigroup N) : (s.prod t : set (M × N)) = s ×ˢ t := rfl

@[to_additive mem_prod]
lemma mem_prod {s : subsemigroup M} {t : subsemigroup N} {p : M × N} :
  p ∈ s.prod t ↔ p.1 ∈ s ∧ p.2 ∈ t := iff.rfl

@[to_additive prod_mono]
lemma prod_mono {s₁ s₂ : subsemigroup M} {t₁ t₂ : subsemigroup N} (hs : s₁ ≤ s₂) (ht : t₁ ≤ t₂) :
  s₁.prod t₁ ≤ s₂.prod t₂ :=
set.prod_mono hs ht

@[to_additive prod_top]
lemma prod_top (s : subsemigroup M) :
  s.prod (⊤ : subsemigroup N) = s.comap (mul_hom.fst M N) :=
ext $ λ x, by simp [mem_prod, mul_hom.coe_fst]

@[to_additive top_prod]
lemma top_prod (s : subsemigroup N) :
  (⊤ : subsemigroup M).prod s = s.comap (mul_hom.snd M N) :=
ext $ λ x, by simp [mem_prod, mul_hom.coe_snd]

@[simp, to_additive top_prod_top]
lemma top_prod_top : (⊤ : subsemigroup M).prod (⊤ : subsemigroup N) = ⊤ :=
(top_prod _).trans $ comap_top _

@[to_additive] lemma bot_prod_bot : (⊥ : subsemigroup M).prod (⊥ : subsemigroup N) = ⊥ :=
set_like.coe_injective $ by simp [coe_prod, prod.one_eq_mk]

/-- The product of subsemigroups is isomorphic to their product as semigroups. -/
@[to_additive prod_equiv "The product of additive subsemigroups is isomorphic to their product
as additive semigroups"]
def prod_equiv (s : subsemigroup M) (t : subsemigroup N) : s.prod t ≃* s × t :=
{ map_mul' := λ x y, rfl, .. equiv.set.prod ↑s ↑t }

open mul_hom

@[to_additive]
lemma mem_map_equiv {f : M ≃* N} {K : subsemigroup M} {x : N} :
  x ∈ K.map f.to_mul_hom ↔ f.symm x ∈ K :=
@set.mem_image_equiv _ _ ↑K f.to_equiv x

@[to_additive]
lemma map_equiv_eq_comap_symm (f : M ≃* N) (K : subsemigroup M) :
  K.map f.to_mul_hom = K.comap f.symm.to_mul_hom :=
set_like.coe_injective (f.to_equiv.image_eq_preimage K)

@[to_additive]
lemma comap_equiv_eq_map_symm (f : N ≃* M) (K : subsemigroup M) :
  K.comap f.to_mul_hom = K.map f.symm.to_mul_hom :=
(map_equiv_eq_comap_symm f.symm K).symm

@[simp, to_additive]
lemma map_equiv_top (f : M ≃* N) : (⊤ : subsemigroup M).map f.to_mul_hom = ⊤ :=
set_like.coe_injective $ set.image_univ.trans f.surjective.range_eq

@[to_additive le_prod_iff]
lemma le_prod_iff {s : subsemigroup M} {t : subsemigroup N} {u : subsemigroup (M × N)} :
  u ≤ s.prod t ↔ u.map (fst M N) ≤ s ∧ u.map (snd M N) ≤ t :=
begin
  split,
  { intros h,
    split,
    { rintros x ⟨⟨y1,y2⟩, ⟨hy1,rfl⟩⟩, exact (h hy1).1 },
    { rintros x ⟨⟨y1,y2⟩, ⟨hy1,rfl⟩⟩, exact (h hy1).2 }, },
  { rintros ⟨hH, hK⟩ ⟨x1, x2⟩ h, exact ⟨hH ⟨_ , h, rfl⟩, hK ⟨ _, h, rfl⟩⟩, }
end

end subsemigroup

namespace mul_hom

open subsemigroup

variables [has_mul M] [has_mul N] [has_mul P] (S : subsemigroup M)

/-- The range of a semigroup homomorphism is a subsemigroup. See Note [range copy pattern]. -/
@[to_additive "The range of an `add_hom` is an `add_subsemigroup`."]
def srange (f : M →ₙ* N) : subsemigroup N :=
((⊤ : subsemigroup M).map f).copy (set.range f) set.image_univ.symm

@[simp, to_additive]
lemma coe_srange (f : M →ₙ* N) :
  (f.srange : set N) = set.range f :=
rfl

@[simp, to_additive] lemma mem_srange {f : M →ₙ* N} {y : N} :
  y ∈ f.srange ↔ ∃ x, f x = y :=
iff.rfl

@[to_additive] lemma srange_eq_map (f : M →ₙ* N) : f.srange = (⊤ : subsemigroup M).map f :=
copy_eq _

@[to_additive]
lemma map_srange (g : N →ₙ* P) (f : M →ₙ* N) : f.srange.map g = (g.comp f).srange :=
by simpa only [srange_eq_map] using (⊤ : subsemigroup M).map_map g f

@[to_additive]
lemma srange_top_iff_surjective {N} [has_mul N] {f : M →ₙ* N} :
  f.srange = (⊤ : subsemigroup N) ↔ function.surjective f :=
set_like.ext'_iff.trans $ iff.trans (by rw [coe_srange, coe_top]) set.range_iff_surjective

/-- The range of a surjective semigroup hom is the whole of the codomain. -/
@[to_additive "The range of a surjective `add_semigroup` hom is the whole of the codomain."]
lemma srange_top_of_surjective {N} [has_mul N] (f : M →ₙ* N) (hf : function.surjective f) :
  f.srange = (⊤ : subsemigroup N) :=
srange_top_iff_surjective.2 hf

@[to_additive]
lemma mclosure_preimage_le (f : M →ₙ* N) (s : set N) :
  closure (f ⁻¹' s) ≤ (closure s).comap f :=
closure_le.2 $ λ x hx, set_like.mem_coe.2 $ mem_comap.2 $ subset_closure hx

/-- The image under a semigroup hom of the subsemigroup generated by a set equals the subsemigroup
generated by the image of the set. -/
@[to_additive "The image under an `add_semigroup` hom of the `add_subsemigroup` generated by a set
equals the `add_subsemigroup` generated by the image of the set."]
lemma map_mclosure (f : M →ₙ* N) (s : set M) :
  (closure s).map f = closure (f '' s) :=
le_antisymm
  (map_le_iff_le_comap.2 $ le_trans (closure_mono $ set.subset_preimage_image _ _)
    (mclosure_preimage_le _ _))
  (closure_le.2 $ set.image_subset _ subset_closure)

/-- Restriction of a semigroup hom to a subsemigroup of the domain. -/
@[to_additive "Restriction of an add_semigroup hom to an `add_subsemigroup` of the domain."]
def restrict {N : Type*} [has_mul N] [set_like σ M] [mul_mem_class σ M] (f : M →ₙ* N) (S : σ) :
  S →ₙ* N :=
f.comp (mul_mem_class.subtype S)

@[simp, to_additive]
lemma restrict_apply {N : Type*} [has_mul N] [set_like σ M] [mul_mem_class σ M] (f : M →ₙ* N)
  {S : σ} (x : S) : f.restrict S x = f x :=
rfl

/-- Restriction of a semigroup hom to a subsemigroup of the codomain. -/
@[to_additive "Restriction of an `add_semigroup` hom to an `add_subsemigroup` of the
codomain.", simps]
def cod_restrict [set_like σ N] [mul_mem_class σ N] (f : M →ₙ* N) (S : σ) (h : ∀ x, f x ∈ S) :
  M →ₙ* S :=
{ to_fun := λ n, ⟨f n, h n⟩,
  map_mul' := λ x y, subtype.eq (map_mul f x y) }

/-- Restriction of a semigroup hom to its range interpreted as a subsemigroup. -/
@[to_additive "Restriction of an `add_semigroup` hom to its range interpreted as a subsemigroup."]
def srange_restrict {N} [has_mul N] (f : M →ₙ* N) : M →ₙ* f.srange :=
f.cod_restrict f.srange $ λ x, ⟨x, rfl⟩

@[simp, to_additive]
lemma coe_srange_restrict {N} [has_mul N] (f : M →ₙ* N) (x : M) :
  (f.srange_restrict x : N) = f x :=
rfl

@[to_additive]
lemma srange_restrict_surjective (f : M →ₙ* N) : function.surjective f.srange_restrict :=
λ ⟨_, ⟨x, rfl⟩⟩, ⟨x, rfl⟩

@[to_additive]
lemma prod_map_comap_prod' {M' : Type*} {N' : Type*} [has_mul M'] [has_mul N']
  (f : M →ₙ* N) (g : M' →ₙ* N') (S : subsemigroup N) (S' : subsemigroup N') :
  (S.prod S').comap (prod_map f g) = (S.comap f).prod (S'.comap g) :=
set_like.coe_injective $ set.preimage_prod_map_prod f g _ _

/-- The `mul_hom` from the preimage of a subsemigroup to itself. -/
@[to_additive "the `add_hom` from the preimage of an additive subsemigroup to itself.", simps]
def subsemigroup_comap (f : M →ₙ* N) (N' : subsemigroup N) :
  N'.comap f →ₙ* N' :=
{ to_fun := λ x, ⟨f x, x.prop⟩,
  map_mul' := λ x y, subtype.eq (@map_mul M N _ _ _ _ f x y) }

/-- The `mul_hom` from a subsemigroup to its image.
See `mul_equiv.subsemigroup_map` for a variant for `mul_equiv`s. -/
@[to_additive "the `add_hom` from an additive subsemigroup to its image. See
`add_equiv.add_subsemigroup_map` for a variant for `add_equiv`s.", simps]
def subsemigroup_map (f : M →ₙ* N) (M' : subsemigroup M) :
  M' →ₙ* M'.map f :=
{ to_fun := λ x, ⟨f x, ⟨x, x.prop, rfl⟩⟩,
  map_mul' := λ x y, subtype.eq $ @map_mul M N _ _ _ _ f x y }

@[to_additive]
lemma subsemigroup_map_surjective (f : M →ₙ* N) (M' : subsemigroup M) :
  function.surjective (f.subsemigroup_map M') :=
by { rintro ⟨_, x, hx, rfl⟩, exact ⟨⟨x, hx⟩, rfl⟩ }

end mul_hom

namespace subsemigroup
open mul_hom

variables [has_mul M] [has_mul N] [has_mul P] (S : subsemigroup M)

@[simp, to_additive]
lemma srange_fst [nonempty N] : (fst M N).srange = ⊤ :=
(fst M N).srange_top_of_surjective $ prod.fst_surjective

@[simp, to_additive]
lemma srange_snd [nonempty M] : (snd M N).srange = ⊤ :=
(snd M N).srange_top_of_surjective $ prod.snd_surjective

@[to_additive]
lemma prod_eq_top_iff [nonempty M] [nonempty N] {s : subsemigroup M} {t : subsemigroup N} :
  s.prod t = ⊤ ↔ s = ⊤ ∧ t = ⊤ :=
by simp only [eq_top_iff, le_prod_iff, ← (gc_map_comap _).le_iff_le, ← srange_eq_map,
  srange_fst, srange_snd]

/-- The semigroup hom associated to an inclusion of subsemigroups. -/
@[to_additive "The `add_semigroup` hom associated to an inclusion of subsemigroups."]
def inclusion {S T : subsemigroup M} (h : S ≤ T) : S →ₙ* T :=
(mul_mem_class.subtype S).cod_restrict _ (λ x, h x.2)

@[simp, to_additive]
lemma range_subtype (s : subsemigroup M) : (mul_mem_class.subtype s).srange = s :=
set_like.coe_injective $ (coe_srange _).trans $ subtype.range_coe

@[to_additive] lemma eq_top_iff' : S = ⊤ ↔ ∀ x : M, x ∈ S :=
eq_top_iff.trans ⟨λ h m, h $ mem_top m, λ h m _, h m⟩

end subsemigroup

namespace mul_equiv

variables [has_mul M] [has_mul N] {S T : subsemigroup M}

/-- Makes the identity isomorphism from a proof that two subsemigroups of a multiplicative
    semigroup are equal. -/
@[to_additive "Makes the identity additive isomorphism from a proof two
subsemigroups of an additive semigroup are equal."]
def subsemigroup_congr (h : S = T) : S ≃* T :=
{ map_mul' :=  λ _ _, rfl, ..equiv.set_congr $ congr_arg _ h }

-- this name is primed so that the version to `f.range` instead of `f.srange` can be unprimed.
/-- A semigroup homomorphism `f : M →ₙ* N` with a left-inverse `g : N → M` defines a multiplicative
equivalence between `M` and `f.srange`.

This is a bidirectional version of `mul_hom.srange_restrict`. -/
@[to_additive /-"
An additive semigroup homomorphism `f : M →+ N` with a left-inverse `g : N → M` defines an additive
equivalence between `M` and `f.srange`.

This is a bidirectional version of `add_hom.srange_restrict`. "-/, simps {simp_rhs := tt}]
def of_left_inverse (f : M →ₙ* N) {g : N → M} (h : function.left_inverse g f) : M ≃* f.srange :=
{ to_fun := f.srange_restrict,
  inv_fun := g ∘ (mul_mem_class.subtype f.srange),
  left_inv := h,
  right_inv := λ x, subtype.ext $
    let ⟨x', hx'⟩ := mul_hom.mem_srange.mp x.prop in
    show f (g x) = x, by rw [←hx', h x'],
  .. f.srange_restrict }

/-- A `mul_equiv` `φ` between two semigroups `M` and `N` induces a `mul_equiv` between
a subsemigroup `S ≤ M` and the subsemigroup `φ(S) ≤ N`.
See `mul_hom.subsemigroup_map` for a variant for `mul_hom`s. -/
@[to_additive "An `add_equiv` `φ` between two additive semigroups `M` and `N` induces an `add_equiv`
between a subsemigroup `S ≤ M` and the subsemigroup `φ(S) ≤ N`. See `add_hom.add_subsemigroup_map`
for a variant for `add_hom`s.", simps]
def subsemigroup_map (e : M ≃* N) (S : subsemigroup M) : S ≃* S.map e.to_mul_hom :=
{ to_fun := λ x, ⟨e x, _⟩,
  inv_fun := λ x, ⟨e.symm x, _⟩, -- we restate this for `simps` to avoid `⇑e.symm.to_equiv x`
  ..e.to_mul_hom.subsemigroup_map S,
  ..e.to_equiv.image S }

end mul_equiv
