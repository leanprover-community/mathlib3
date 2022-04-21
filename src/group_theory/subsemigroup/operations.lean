/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov, Yakov Pechersky, Jireh Loreaux
-/
import group_theory.subsemigroup.basic

/-!
# Operations on `subsemigroup`s

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

* `mul_hom.mrange`: range of a semigroup homomorphism as a subsemigroup of the codomain;
* `mul_hom.mrestrict`: restrict a semigroup homomorphism to a subsemigroup;
* `mul_hom.cod_mrestrict`: restrict the codomain of a semigroup homomorphism to a subsemigroup;
* `mul_hom.mrange_restrict`: restrict a semigroup homomorphism to its range;

### Implementation notes

This file follows closely `group_theory/submonoid/operations.lean`, omitting only that which is
necessary.

## Tags

subsemigroup, range, product, map, comap
-/

variables {M N P : Type*}

/-!
### Conversion to/from `additive`/`multiplicative`
-/

section

variables [has_mul M]

/-- subsemigroups of magma `M` are isomorphic to additive subsemigroups of `additive M`. -/
@[simps]
def subsemigroup.to_add_subsemigroup : subsemigroup M ≃o add_subsemigroup (additive M) :=
{ to_fun := λ S,
  { carrier := additive.to_mul ⁻¹' S,
    add_mem' := S.mul_mem' },
  inv_fun := λ S,
  { carrier := additive.of_mul ⁻¹' S,
    mul_mem' := S.add_mem' },
  left_inv := λ x, by cases x; refl,
  right_inv := λ x, by cases x; refl,
  map_rel_iff' := λ a b, iff.rfl, }

/-- Additive subsemigroups of an additive magma `additive M` are isomorphic to
subsemigroups of `M`. -/
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

/-- Additive subsemigroups of an additive magma `A` are isomorphic to
multiplicative subsemigroups of `multiplicative A`. -/
@[simps]
def add_subsemigroup.to_subsemigroup : add_subsemigroup A ≃o subsemigroup (multiplicative A) :=
{ to_fun := λ S,
  { carrier := multiplicative.to_add ⁻¹' S,
    mul_mem' := S.add_mem' },
  inv_fun := λ S,
  { carrier := multiplicative.of_add ⁻¹' S,
    add_mem' := S.mul_mem' },
  left_inv := λ x, by cases x; refl,
  right_inv := λ x, by cases x; refl,
  map_rel_iff' := λ a b, iff.rfl, }

/-- subsemigroups of a magma `multiplicative A` are isomorphic to additive subsemigroups of `A`. -/
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

/-- The preimage of a subsemigroup along a mul homomorphism is a subsemigroup. -/
@[to_additive "The preimage of an `add_subsemigroup` along an add homomorphism is an
`add_subsemigroup`."]
def comap (f : mul_hom M N) (S : subsemigroup N) : subsemigroup M :=
{ carrier := (f ⁻¹' S),
  mul_mem' := λ a b ha hb,
    show f (a * b) ∈ S, by rw f.map_mul; exact S.mul_mem ha hb }

@[simp, to_additive]
lemma coe_comap (S : subsemigroup N) (f : mul_hom M N) : (S.comap f : set M) = f ⁻¹' S := rfl

@[simp, to_additive]
lemma mem_comap {S : subsemigroup N} {f : mul_hom M N} {x : M} : x ∈ S.comap f ↔ f x ∈ S := iff.rfl

@[to_additive]
lemma comap_comap (S : subsemigroup P) (g : mul_hom N P) (f : mul_hom M N) :
  (S.comap g).comap f = S.comap (g.comp f) :=
rfl

@[simp, to_additive]
lemma comap_id (S : subsemigroup P) : S.comap (mul_hom.id _) = S :=
ext (by simp)

/-- The image of a subsemigroup along a mul homomorphism is a subsemigroup. -/
@[to_additive "The image of an `add_subsemigroup` along an add homomorphism is
an `add_subsemigroup`."]
def map (f : mul_hom M N) (S : subsemigroup M) : subsemigroup N :=
{ carrier := (f '' S),
  mul_mem' := begin rintros _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩, exact ⟨x * y, S.mul_mem hx hy,
    by rw f.map_mul; refl⟩ end }

@[simp, to_additive]
lemma coe_map (f : mul_hom M N) (S : subsemigroup M) :
  (S.map f : set N) = f '' S := rfl

@[simp, to_additive]
lemma mem_map {f : mul_hom M N} {S : subsemigroup M} {y : N} :
  y ∈ S.map f ↔ ∃ x ∈ S, f x = y :=
mem_image_iff_bex

@[to_additive]
lemma mem_map_of_mem (f : mul_hom M N) {S : subsemigroup M} {x : M} (hx : x ∈ S) : f x ∈ S.map f :=
mem_image_of_mem f hx

@[to_additive]
lemma apply_coe_mem_map (f : mul_hom M N) (S : subsemigroup M) (x : S) : f x ∈ S.map f :=
mem_map_of_mem f x.prop

@[to_additive]
lemma map_map (g : mul_hom N P) (f : mul_hom M N) : (S.map f).map g = S.map (g.comp f) :=
set_like.coe_injective $ image_image _ _ _

@[to_additive]
lemma mem_map_iff_mem {f : mul_hom M N} (hf : function.injective f) {S : subsemigroup M} {x : M} :
  f x ∈ S.map f ↔ x ∈ S :=
hf.mem_set_image

@[to_additive]
lemma map_le_iff_le_comap {f : mul_hom M N} {S : subsemigroup M} {T : subsemigroup N} :
  S.map f ≤ T ↔ S ≤ T.comap f :=
image_subset_iff

@[to_additive]
lemma gc_map_comap (f : mul_hom M N) : galois_connection (map f) (comap f) :=
λ S T, map_le_iff_le_comap

@[to_additive]
lemma map_le_of_le_comap {T : subsemigroup N} {f : mul_hom M N} : S ≤ T.comap f → S.map f ≤ T :=
(gc_map_comap f).l_le

@[to_additive]
lemma le_comap_of_map_le {T : subsemigroup N} {f : mul_hom M N} : S.map f ≤ T → S ≤ T.comap f :=
(gc_map_comap f).le_u

@[to_additive]
lemma le_comap_map {f : mul_hom M N} : S ≤ (S.map f).comap f :=
(gc_map_comap f).le_u_l _

@[to_additive]
lemma map_comap_le {S : subsemigroup N} {f : mul_hom M N} : (S.comap f).map f ≤ S :=
(gc_map_comap f).l_u_le _

@[to_additive]
lemma monotone_map {f : mul_hom M N} : monotone (map f) :=
(gc_map_comap f).monotone_l

@[to_additive]
lemma monotone_comap {f : mul_hom M N} : monotone (comap f) :=
(gc_map_comap f).monotone_u

@[simp, to_additive]
lemma map_comap_map {f : mul_hom M N} : ((S.map f).comap f).map f = S.map f :=
(gc_map_comap f).l_u_l_eq_l _

@[simp, to_additive]
lemma comap_map_comap {S : subsemigroup N} {f : mul_hom M N} :
  ((S.comap f).map f).comap f = S.comap f :=
(gc_map_comap f).u_l_u_eq_u _

@[to_additive]
lemma map_sup (S T : subsemigroup M) (f : mul_hom M N) : (S ⊔ T).map f = S.map f ⊔ T.map f :=
(gc_map_comap f).l_sup

@[to_additive]
lemma map_supr {ι : Sort*} (f : mul_hom M N) (s : ι → subsemigroup M) :
  (supr s).map f = ⨆ i, (s i).map f :=
(gc_map_comap f).l_supr

@[to_additive]
lemma comap_inf (S T : subsemigroup N) (f : mul_hom M N) :
  (S ⊓ T).comap f = S.comap f ⊓ T.comap f :=
(gc_map_comap f).u_inf

@[to_additive]
lemma comap_infi {ι : Sort*} (f : mul_hom M N) (s : ι → subsemigroup N) :
  (infi s).comap f = ⨅ i, (s i).comap f :=
(gc_map_comap f).u_infi

@[simp, to_additive] lemma map_bot (f : mul_hom M N) : (⊥ : subsemigroup M).map f = ⊥ :=
(gc_map_comap f).l_bot

@[simp, to_additive] lemma comap_top (f : mul_hom M N) : (⊤ : subsemigroup N).comap f = ⊤ :=
(gc_map_comap f).u_top

@[simp, to_additive] lemma map_id (S : subsemigroup M) : S.map (mul_hom.id M) = S :=
ext (λ x, ⟨λ ⟨_, h, rfl⟩, h, λ h, ⟨_, h, rfl⟩⟩)

section galois_coinsertion

variables {ι : Type*} {f : mul_hom M N} (hf : function.injective f)

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

variables {ι : Type*} {f : mul_hom M N} (hf : function.surjective f)

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

/-- A subsemigroup of a magma inherits a multiplication. -/
@[to_additive "An `add_subsemigroup` of an additive magma inherits an addition."]
instance has_mul : has_mul S := ⟨λ a b, ⟨a.1 * b.1, S.mul_mem a.2 b.2⟩⟩

@[simp, norm_cast, to_additive] lemma coe_mul (x y : S) : (↑(x * y) : M) = ↑x * ↑y := rfl

@[simp, to_additive] lemma mk_mul_mk (x y : M) (hx : x ∈ S) (hy : y ∈ S) :
  (⟨x, hx⟩ : S) * ⟨y, hy⟩ = ⟨x * y, S.mul_mem hx hy⟩ := rfl

@[to_additive] lemma mul_def (x y : S) : x * y = ⟨x * y, S.mul_mem x.2 y.2⟩ := rfl

/-- A subsemigroup of a semigroup inherits a semigroup structure. -/
@[to_additive "An `add_subsemigroup` of an semigroup inherits an additive semigroup
structure."]
instance to_semigroup {M : Type*} [semigroup M] (S : subsemigroup M) : semigroup S :=
subtype.coe_injective.semigroup coe (λ _ _, rfl)

/-- A subsemigroup of a `comm_semigroup` is a `comm_semigroup`. -/
@[to_additive "An `add_subsemigroup` of an `add_comm_semigroup` is
an `add_comm_semigroup`."]
instance to_comm_semigroup {M} [comm_semigroup M] (S : subsemigroup M) : comm_semigroup S :=
subtype.coe_injective.comm_semigroup coe (λ _ _, rfl)

/-- The natural mul hom from a subsemigroup of magma `M` to `M`. -/
@[to_additive "The natural add hom from an `add_subsemigroup` of additive magma `M` to `M`."]
def subtype : mul_hom S M := ⟨coe, λ _ _, rfl⟩

@[simp, to_additive] theorem coe_subtype : ⇑S.subtype = coe := rfl

/-- A subsemigroup is isomorphic to its image under an injective function -/
@[to_additive "An additive subsemigroup is isomorphic to its image under an injective function"]
noncomputable def equiv_map_of_injective
  (f : mul_hom M N) (hf : function.injective f) : S ≃* S.map f :=
{ map_mul' := λ _ _, subtype.ext (f.map_mul _ _), ..equiv.set.image f S hf }

@[simp, to_additive] lemma coe_equiv_map_of_injective_apply
  (f : mul_hom M N) (hf : function.injective f) (x : S) :
  (equiv_map_of_injective S f hf x : N) = f x := rfl

@[simp, to_additive]
lemma closure_closure_coe_preimage {s : set M} : closure ((coe : closure s → M) ⁻¹' s) = ⊤ :=
eq_top_iff.2 $ λ x, subtype.rec_on x $ λ x hx _, begin
  refine closure_induction' _ (λ g hg, _) (λ g₁ g₂ hg₁ hg₂, _) hx,
  { exact subset_closure hg },
  { exact subsemigroup.mul_mem _ },
end

/-- Given `subsemigroup`s `s`, `t` of magma `M`, `N` respectively, `s × t` as a subsemigroup
of `M × N`. -/
@[to_additive prod "Given `add_subsemigroup`s `s`, `t` of additive magmas `A`, `B`
respectively, `s × t` as an `add_subsemigroup` of `A × B`."]
def prod (s : subsemigroup M) (t : subsemigroup N) : subsemigroup (M × N) :=
{ carrier := (s : set M) ×ˢ (t : set N),
  mul_mem' := λ p q hp hq, ⟨s.mul_mem hp.1 hq.1, t.mul_mem hp.2 hq.2⟩ }

@[to_additive coe_prod]
lemma coe_prod (s : subsemigroup M) (t : subsemigroup N) :
 (s.prod t : set (M × N)) = (s : set M) ×ˢ (t : set N) :=
rfl

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

/-- The product of subsemigroups is isomorphic to their product as monoids. -/
@[to_additive prod_equiv "The product of additive subsemigroups is isomorphic to their product
as additive monoids"]
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

/-- The range of a mul homomorphism is a subsemigroup. See Note [range copy pattern]. -/
@[to_additive "The range of an `add_hom` is an `add_subsemigroup`."]
def mrange (f : mul_hom M N) : subsemigroup N :=
((⊤ : subsemigroup M).map f).copy (set.range f) set.image_univ.symm

@[simp, to_additive]
lemma coe_mrange (f : mul_hom M N) :
  (f.mrange : set N) = set.range f :=
rfl

@[simp, to_additive] lemma mem_mrange {f : mul_hom M N} {y : N} :
  y ∈ f.mrange ↔ ∃ x, f x = y :=
iff.rfl

@[to_additive] lemma mrange_eq_map (f : mul_hom M N) : f.mrange = (⊤ : subsemigroup M).map f :=
copy_eq _

@[to_additive]
lemma map_mrange (g : mul_hom N P) (f : mul_hom M N) : f.mrange.map g = (g.comp f).mrange :=
by simpa only [mrange_eq_map] using (⊤ : subsemigroup M).map_map g f

@[to_additive]
lemma mrange_top_iff_surjective {N} [has_mul N] {f : mul_hom M N} :
  f.mrange = (⊤ : subsemigroup N) ↔ function.surjective f :=
set_like.ext'_iff.trans $ iff.trans (by rw [coe_mrange, coe_top]) set.range_iff_surjective

/-- The range of a surjective monoid hom is the whole of the codomain. -/
@[to_additive "The range of a surjective `add_monoid` hom is the whole of the codomain."]
lemma mrange_top_of_surjective {N} [has_mul N] (f : mul_hom M N) (hf : function.surjective f) :
  f.mrange = (⊤ : subsemigroup N) :=
mrange_top_iff_surjective.2 hf

@[to_additive]
lemma mclosure_preimage_le (f : mul_hom M N) (s : set N) :
  closure (f ⁻¹' s) ≤ (closure s).comap f :=
closure_le.2 $ λ x hx, set_like.mem_coe.2 $ mem_comap.2 $ subset_closure hx

/-- The image under a mul hom of the subsemigroup generated by a set equals the
    subsemigroup generated by the image of the set. -/
@[to_additive "The image under an add hom of the `add_subsemigroup` generated by a set equals
the `add_subsemigroup` generated by the image of the set."]
lemma map_mclosure (f : mul_hom M N) (s : set M) :
  (closure s).map f = closure (f '' s) :=
le_antisymm
  (map_le_iff_le_comap.2 $ le_trans (closure_mono $ set.subset_preimage_image _ _)
    (mclosure_preimage_le _ _))
  (closure_le.2 $ set.image_subset _ subset_closure)

/-- Restriction of a mul hom to a subsemigroup of the domain. -/
@[to_additive "Restriction of an add hom to an `add_subsemigroup` of the domain."]
def mrestrict {N : Type*} [has_mul N] (f : mul_hom M N) (S : subsemigroup M) : mul_hom S N :=
f.comp S.subtype

@[simp, to_additive]
lemma mrestrict_apply {N : Type*} [has_mul N] (f : mul_hom M N) (x : S) : f.mrestrict S x = f x :=
rfl

/-- Restriction of a mul hom to a subsemigroup of the codomain. -/
@[to_additive "Restriction of an add hom to an `add_subsemigroup` of the codomain.", simps]
def cod_mrestrict (f : mul_hom M N) (S : subsemigroup N) (h : ∀ x, f x ∈ S) : mul_hom M S :=
{ to_fun := λ n, ⟨f n, h n⟩,
  map_mul' := λ x y, subtype.eq (f.map_mul x y) }

/-- Restriction of a mul hom to its range interpreted as a subsemigroup. -/
@[to_additive "Restriction of an add hom to its range interpreted as a subsemigroup."]
def mrange_restrict {N} [has_mul N] (f : mul_hom M N) : mul_hom M f.mrange :=
f.cod_mrestrict f.mrange $ λ x, ⟨x, rfl⟩

@[simp, to_additive]
lemma coe_mrange_restrict {N} [has_mul N] (f : mul_hom M N) (x : M) :
  (f.mrange_restrict x : N) = f x :=
rfl

@[to_additive]
lemma prod_map_comap_prod' {M' : Type*} {N' : Type*} [has_mul M'] [has_mul N']
  (f : mul_hom M N) (g : mul_hom M' N') (S : subsemigroup N) (S' : subsemigroup N') :
  (S.prod S').comap (prod_map f g) = (S.comap f).prod (S'.comap g) :=
set_like.coe_injective $ set.preimage_prod_map_prod f g _ _

/-- The `mul_hom` from the preimage of a subsemigroup to itself. -/
@[to_additive "the `add__hom` from the preimage of an additive subsemigroup to itself.", simps]
def subsemigroup_comap (f : mul_hom M N) (N' : subsemigroup N) :
  mul_hom (N'.comap f) N' :=
{ to_fun := λ x, ⟨f x, x.prop⟩,
  map_mul' := λ x y, subtype.eq (f.map_mul x y) }

/-- The `mul_hom` from a subsemigroup to its image.
See `mul_equiv.subsemigroup_map` for a variant for `mul_equiv`s. -/
@[to_additive "the `add_hom` from an additive subsemigroup to its image. See
`add_equiv.add_subsemigroup_map` for a variant for `add_equiv`s.", simps]
def subsemigroup_map (f : mul_hom M N) (M' : subsemigroup M) :
  mul_hom M' (M'.map f) :=
{ to_fun := λ x, ⟨f x, ⟨x, x.prop, rfl⟩⟩,
  map_mul' := λ x y, subtype.eq $ f.map_mul x y }

@[to_additive]
lemma subsemigroup_map_surjective (f : mul_hom M N) (M' : subsemigroup M) :
  function.surjective (f.subsemigroup_map M') :=
by { rintro ⟨_, x, hx, rfl⟩, exact ⟨⟨x, hx⟩, rfl⟩ }

end mul_hom

namespace subsemigroup
open mul_hom

variables [has_mul M] [has_mul N] [has_mul P] (S : subsemigroup M)

@[simp, to_additive]
lemma mrange_fst [nonempty N] : (fst M N).mrange = ⊤ :=
(fst M N).mrange_top_of_surjective $ @prod.fst_surjective _ _ _

@[simp, to_additive]
lemma mrange_snd [nonempty M] : (snd M N).mrange = ⊤ :=
(snd M N).mrange_top_of_surjective $ @prod.snd_surjective _ _ _

/-- The mul hom associated to an inclusion of subsemigroups. -/
@[to_additive "The add hom associated to an inclusion of additive subsemigroups."]
def inclusion {S T : subsemigroup M} (h : S ≤ T) : mul_hom S T :=
S.subtype.cod_mrestrict _ (λ x, h x.2)

@[simp, to_additive]
lemma range_subtype (s : subsemigroup M) : s.subtype.mrange = s :=
set_like.coe_injective $ (coe_mrange _).trans $ subtype.range_coe

@[to_additive] lemma eq_top_iff' : S = ⊤ ↔ ∀ x : M, x ∈ S :=
eq_top_iff.trans ⟨λ h m, h $ mem_top m, λ h m _, h m⟩

end subsemigroup

namespace mul_equiv

variables [has_mul M] [has_mul N] {S T : subsemigroup M}

/-- Makes the identity isomorphism from a proof that two subsemigroups of a magma are equal. -/
@[to_additive "Makes the identity additive isomorphism from a proof two
subsemigroups of an additive magma are equal."]
def subsemigroup_congr (h : S = T) : S ≃* T :=
{ map_mul' :=  λ _ _, rfl, ..equiv.set_congr $ congr_arg _ h }

-- this name is primed so that the version to `f.range` instead of `f.mrange` can be unprimed.
/-- A mul homomorphism `f : mul_hom M N` with a left-inverse `g : N → M` defines a multiplicative
equivalence between `M` and `f.mrange`.

This is a bidirectional version of `mul_hom.mrange_restrict`. -/
@[to_additive /-"
An additive homomorphism `f : M →+ N` with a left-inverse `g : N → M` defines an additive
equivalence between `M` and `f.mrange`.

This is a bidirectional version of `add_mul_hom.mrange_restrict`. "-/, simps {simp_rhs := tt}]
def of_left_inverse'' (f : mul_hom M N) {g : N → M} (h : function.left_inverse g f) :
  M ≃* f.mrange :=
{ to_fun := f.mrange_restrict,
  inv_fun := g ∘ f.mrange.subtype,
  left_inv := h,
  right_inv := λ x, subtype.ext $
    let ⟨x', hx'⟩ := mul_hom.mem_mrange.mp x.prop in
    show f (g x) = x, by rw [←hx', h x'],
  .. f.mrange_restrict }

/-- A `mul_equiv` `φ` between two magmas `M` and `N` induces a `mul_equiv` between
a subsemigroup `S ≤ M` and the subsemigroup `φ(S) ≤ N`.
See `mul_hom.subsemigroup_map` for a variant for `mul_hom`s. -/
@[to_additive "An `add_equiv` `φ` between two additive magmas `M` and `N` induces an `add_equiv`
between a subsemigroup `S ≤ M` and the subsemigroup `φ(S) ≤ N`. See
`add_mul_hom.add_subsemigroup_map` for a variant for `add_mul_hom`s.", simps]
def subsemigroup_map (e : M ≃* N) (S : subsemigroup M) : S ≃* S.map e.to_mul_hom :=
{ to_fun := λ x, ⟨e x, _⟩,
  inv_fun := λ x, ⟨e.symm x, _⟩, -- we restate this for `simps` to avoid `⇑e.symm.to_equiv x`
  ..e.to_mul_hom.subsemigroup_map S,
  ..e.to_equiv.image S }

end mul_equiv
