/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import algebra.algebra.basic

/-!
# Subfields

Let `K` be a field. This file defines the "bundled" subfield type `subfield K`, a type
whose terms correspond to subfields of `K`. This is the preferred way to talk
about subfields in mathlib. Unbundled subfields (`s : set K` and `is_subfield s`)
are not in this file, and they will ultimately be deprecated.

We prove that subfields are a complete lattice, and that you can `map` (pushforward) and
`comap` (pull back) them along ring homomorphisms.

We define the `closure` construction from `set R` to `subfield R`, sending a subset of `R`
to the subfield it generates, and prove that it is a Galois insertion.

## Main definitions

Notation used here:

`(K : Type u) [field K] (L : Type u) [field L] (f g : K →+* L)`
`(A : subfield K) (B : subfield L) (s : set K)`

* `subfield R` : the type of subfields of a ring `R`.

* `instance : complete_lattice (subfield R)` : the complete lattice structure on the subfields.

* `subfield.closure` : subfield closure of a set, i.e., the smallest subfield that includes the set.

* `subfield.gi` : `closure : set M → subfield M` and coercion `coe : subfield M → set M`
  form a `galois_insertion`.

* `comap f B : subfield K` : the preimage of a subfield `B` along the ring homomorphism `f`

* `map f A : subfield L` : the image of a subfield `A` along the ring homomorphism `f`.

* `prod A B : subfield (K × L)` : the product of subfields

* `f.field_range : subfield B` : the range of the ring homomorphism `f`.

* `eq_locus_field f g : subfield K` : given ring homomorphisms `f g : K →+* R`,
     the subfield of `K` where `f x = g x`

## Implementation notes

A subfield is implemented as a subring which is is closed under `⁻¹`.

Lattice inclusion (e.g. `≤` and `⊓`) is used rather than set notation (`⊆` and `∩`), although
`∈` is defined as membership of a subfield's underlying set.

## Tags
subfield, subfields
-/

open_locale big_operators
universes u v w

variables {K : Type u} {L : Type v} {M : Type w} [field K] [field L] [field M]

set_option old_structure_cmd true

/-- `subfield R` is the type of subfields of `R`. A subfield of `R` is a subset `s` that is a
  multiplicative submonoid and an additive subgroup. Note in particular that it shares the
  same 0 and 1 as R. -/
structure subfield (K : Type u) [field K] extends subring K :=
(inv_mem' : ∀ x ∈ carrier, x⁻¹ ∈ carrier)

/-- Reinterpret a `subfield` as a `subring`. -/
add_decl_doc subfield.to_subring

namespace subfield

/-- The underlying `add_subgroup` of a subfield. -/
def to_add_subgroup (s : subfield K) : add_subgroup K :=
{ ..s.to_subring.to_add_subgroup }

/-- The underlying submonoid of a subfield. -/
def to_submonoid (s : subfield K) : submonoid K :=
{ ..s.to_subring.to_submonoid }


instance : set_like (subfield K) K :=
⟨subfield.carrier, λ p q h, by cases p; cases q; congr'⟩

@[simp]
lemma mem_carrier {s : subfield K} {x : K} : x ∈ s.carrier ↔ x ∈ s := iff.rfl

@[simp]
lemma mem_mk {S : set K} {x : K} (h₁ h₂ h₃ h₄ h₅ h₆) :
  x ∈ (⟨S, h₁, h₂, h₃, h₄, h₅, h₆⟩ : subfield K) ↔ x ∈ S := iff.rfl

@[simp] lemma coe_set_mk (S : set K) (h₁ h₂ h₃ h₄ h₅ h₆) :
  ((⟨S, h₁, h₂, h₃, h₄, h₅, h₆⟩ : subfield K) : set K) = S := rfl

@[simp]
lemma mk_le_mk {S S' : set K} (h₁ h₂ h₃  h₄ h₅ h₆ h₁' h₂' h₃'  h₄' h₅' h₆') :
  (⟨S, h₁, h₂, h₃, h₄, h₅, h₆⟩ : subfield K) ≤ (⟨S', h₁', h₂', h₃', h₄', h₅', h₆'⟩ : subfield K) ↔
  S ⊆ S' :=
iff.rfl

/-- Two subfields are equal if they have the same elements. -/
@[ext] theorem ext {S T : subfield K} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := set_like.ext h

/-- Copy of a subfield with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (S : subfield K) (s : set K) (hs : s = ↑S) : subfield K :=
{ carrier := s,
  inv_mem' := hs.symm ▸ S.inv_mem',
  ..S.to_subring.copy s hs }

@[simp] lemma coe_copy (S : subfield K) (s : set K) (hs : s = ↑S) :
  (S.copy s hs : set K) = s := rfl

lemma copy_eq (S : subfield K) (s : set K) (hs : s = ↑S) : S.copy s hs = S :=
set_like.coe_injective hs

@[simp] lemma coe_to_subring (s : subfield K) : (s.to_subring : set K) = s :=
rfl

@[simp] lemma mem_to_subring (s : subfield K) (x : K) :
  x ∈ s.to_subring ↔ x ∈ s := iff.rfl

end subfield

/-- A `subring` containing inverses is a `subfield`. -/
def subring.to_subfield (s : subring K) (hinv : ∀ x ∈ s, x⁻¹ ∈ s) : subfield K :=
{ inv_mem' := hinv
  ..s }

namespace subfield

variables (s t : subfield K)

/-- A subfield contains the ring's 1. -/
theorem one_mem : (1 : K) ∈ s := s.one_mem'

/-- A subfield contains the ring's 0. -/
theorem zero_mem : (0 : K) ∈ s := s.zero_mem'

/-- A subfield is closed under multiplication. -/
theorem mul_mem : ∀ {x y : K}, x ∈ s → y ∈ s → x * y ∈ s := s.mul_mem'

/-- A subfield is closed under addition. -/
theorem add_mem : ∀ {x y : K}, x ∈ s → y ∈ s → x + y ∈ s := s.add_mem'

/-- A subfield is closed under negation. -/
theorem neg_mem : ∀ {x : K}, x ∈ s → -x ∈ s := s.neg_mem'

/-- A subfield is closed under subtraction. -/
theorem sub_mem {x y : K} : x ∈ s → y ∈ s → x - y ∈ s := s.to_subring.sub_mem

/-- A subfield is closed under inverses. -/
theorem inv_mem : ∀ {x : K}, x ∈ s → x⁻¹ ∈ s := s.inv_mem'

/-- A subfield is closed under division. -/
theorem div_mem {x y : K} (hx : x ∈ s) (hy : y ∈ s) : x / y ∈ s :=
by { rw div_eq_mul_inv, exact s.mul_mem hx (s.inv_mem hy) }

/-- Product of a list of elements in a subfield is in the subfield. -/
lemma list_prod_mem {l : list K} : (∀ x ∈ l, x ∈ s) → l.prod ∈ s :=
s.to_submonoid.list_prod_mem

/-- Sum of a list of elements in a subfield is in the subfield. -/
lemma list_sum_mem {l : list K} : (∀ x ∈ l, x ∈ s) → l.sum ∈ s :=
s.to_add_subgroup.list_sum_mem

/-- Product of a multiset of elements in a subfield is in the subfield. -/
lemma multiset_prod_mem (m : multiset K) :
  (∀ a ∈ m, a ∈ s) → m.prod ∈ s :=
s.to_submonoid.multiset_prod_mem m

/-- Sum of a multiset of elements in a `subfield` is in the `subfield`. -/
lemma multiset_sum_mem (m : multiset K) :
  (∀ a ∈ m, a ∈ s) → m.sum ∈ s :=
s.to_add_subgroup.multiset_sum_mem m

/-- Product of elements of a subfield indexed by a `finset` is in the subfield. -/
lemma prod_mem {ι : Type*} {t : finset ι} {f : ι → K} (h : ∀ c ∈ t, f c ∈ s) :
  ∏ i in t, f i ∈ s :=
s.to_submonoid.prod_mem h

/-- Sum of elements in a `subfield` indexed by a `finset` is in the `subfield`. -/
lemma sum_mem {ι : Type*} {t : finset ι} {f : ι → K} (h : ∀ c ∈ t, f c ∈ s) :
  ∑ i in t, f i ∈ s :=
s.to_add_subgroup.sum_mem h

lemma pow_mem {x : K} (hx : x ∈ s) (n : ℕ) : x^n ∈ s := s.to_submonoid.pow_mem hx n

lemma zsmul_mem {x : K} (hx : x ∈ s) (n : ℤ) :
  n • x ∈ s := s.to_add_subgroup.zsmul_mem hx n

lemma coe_int_mem (n : ℤ) : (n : K) ∈ s :=
by simp only [← zsmul_one, zsmul_mem, one_mem]

instance : ring s := s.to_subring.to_ring
instance : has_div s := ⟨λ x y, ⟨x / y, s.div_mem x.2 y.2⟩⟩
instance : has_inv s := ⟨λ x, ⟨x⁻¹, s.inv_mem x.2⟩⟩

/-- A subfield inherits a field structure -/
instance to_field : field s :=
subtype.coe_injective.field coe
  rfl rfl (λ _ _, rfl) (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl)

/-- A subfield of a `linear_ordered_field` is a `linear_ordered_field`. -/
instance to_linear_ordered_field {K} [linear_ordered_field K] (s : subfield K) :
  linear_ordered_field s :=
subtype.coe_injective.linear_ordered_field coe
  rfl rfl (λ _ _, rfl) (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl)

@[simp, norm_cast] lemma coe_add (x y : s) : (↑(x + y) : K) = ↑x + ↑y := rfl
@[simp, norm_cast] lemma coe_sub (x y : s) : (↑(x - y) : K) = ↑x - ↑y := rfl
@[simp, norm_cast] lemma coe_neg (x : s) : (↑(-x) : K) = -↑x := rfl
@[simp, norm_cast] lemma coe_mul (x y : s) : (↑(x * y) : K) = ↑x * ↑y := rfl
@[simp, norm_cast] lemma coe_div (x y : s) : (↑(x / y) : K) = ↑x / ↑y := rfl
@[simp, norm_cast] lemma coe_inv (x : s) : (↑(x⁻¹) : K) = (↑x)⁻¹ := rfl
@[simp, norm_cast] lemma coe_zero : ((0 : s) : K) = 0 := rfl
@[simp, norm_cast] lemma coe_one : ((1 : s) : K) = 1 := rfl

/-- The embedding from a subfield of the field `K` to `K`. -/
def subtype (s : subfield K) : s →+* K :=
{ to_fun := coe,
 .. s.to_submonoid.subtype, .. s.to_add_subgroup.subtype }

instance to_algebra : algebra s K := ring_hom.to_algebra s.subtype

@[simp] theorem coe_subtype : ⇑s.subtype = coe := rfl

lemma to_subring.subtype_eq_subtype (F : Type*) [field F] (S : subfield F) :
  S.to_subring.subtype = S.subtype := rfl

/-! # Partial order -/

variables (s t)

@[simp] lemma mem_to_submonoid {s : subfield K} {x : K} : x ∈ s.to_submonoid ↔ x ∈ s := iff.rfl
@[simp] lemma coe_to_submonoid : (s.to_submonoid : set K) = s := rfl
@[simp] lemma mem_to_add_subgroup {s : subfield K} {x : K} :
  x ∈ s.to_add_subgroup ↔ x ∈ s := iff.rfl
@[simp] lemma coe_to_add_subgroup : (s.to_add_subgroup : set K) = s := rfl

/-! # top -/

/-- The subfield of `K` containing all elements of `K`. -/
instance : has_top (subfield K) :=
⟨{ inv_mem' := λ x _, subring.mem_top x, .. (⊤ : subring K)}⟩

instance : inhabited (subfield K) := ⟨⊤⟩

@[simp] lemma mem_top (x : K) : x ∈ (⊤ : subfield K) := set.mem_univ x

@[simp] lemma coe_top : ((⊤ : subfield K) : set K) = set.univ := rfl

/-! # comap -/

variables (f : K →+* L)

/-- The preimage of a subfield along a ring homomorphism is a subfield. -/
def comap (s : subfield L) : subfield K :=
{ inv_mem' := λ x hx, show f (x⁻¹) ∈ s, by { rw f.map_inv, exact s.inv_mem hx },
  .. s.to_subring.comap f }

@[simp] lemma coe_comap (s : subfield L) : (s.comap f : set K) = f ⁻¹' s := rfl

@[simp]
lemma mem_comap {s : subfield L} {f : K →+* L} {x : K} : x ∈ s.comap f ↔ f x ∈ s := iff.rfl

lemma comap_comap (s : subfield M) (g : L →+* M) (f : K →+* L) :
  (s.comap g).comap f = s.comap (g.comp f) :=
rfl

/-! # map -/

/-- The image of a subfield along a ring homomorphism is a subfield. -/
def map (s : subfield K) : subfield L :=
{ inv_mem' := by { rintros _ ⟨x, hx, rfl⟩, exact ⟨x⁻¹, s.inv_mem hx, f.map_inv x⟩ },
  .. s.to_subring.map f }

@[simp] lemma coe_map : (s.map f : set L) = f '' s := rfl

@[simp] lemma mem_map {f : K →+* L} {s : subfield K} {y : L} :
  y ∈ s.map f ↔ ∃ x ∈ s, f x = y :=
set.mem_image_iff_bex

lemma map_map (g : L →+* M) (f : K →+* L) : (s.map f).map g = s.map (g.comp f) :=
set_like.ext' $ set.image_image _ _ _

lemma map_le_iff_le_comap {f : K →+* L} {s : subfield K} {t : subfield L} :
  s.map f ≤ t ↔ s ≤ t.comap f :=
set.image_subset_iff

lemma gc_map_comap (f : K →+* L) : galois_connection (map f) (comap f) :=
λ S T, map_le_iff_le_comap

end subfield

namespace ring_hom

variables (g : L →+* M) (f : K →+* L)

/-! # range -/

/-- The range of a ring homomorphism, as a subfield of the target. See Note [range copy pattern]. -/
def field_range : subfield L :=
((⊤ : subfield K).map f).copy (set.range f) set.image_univ.symm

@[simp] lemma coe_field_range : (f.field_range : set L) = set.range f := rfl

@[simp] lemma mem_field_range {f : K →+* L} {y : L} : y ∈ f.field_range ↔ ∃ x, f x = y := iff.rfl

lemma field_range_eq_map : f.field_range = subfield.map f ⊤ :=
by { ext, simp }

lemma map_field_range : f.field_range.map g = (g.comp f).field_range :=
by simpa only [field_range_eq_map] using (⊤ : subfield K).map_map g f

/-- The range of a morphism of fields is a fintype, if the domain is a fintype.

Note that this instance can cause a diamond with `subtype.fintype` if `L` is also a fintype.-/
instance fintype_field_range [fintype K] [decidable_eq L] (f : K →+* L) : fintype f.field_range :=
set.fintype_range f

end ring_hom

namespace subfield

/-! # inf -/

/-- The inf of two subfields is their intersection. -/
instance : has_inf (subfield K) :=
⟨λ s t,
  { inv_mem' := λ x hx, subring.mem_inf.mpr
      ⟨s.inv_mem (subring.mem_inf.mp hx).1,
       t.inv_mem (subring.mem_inf.mp hx).2⟩,
    .. s.to_subring ⊓ t.to_subring }⟩

@[simp] lemma coe_inf (p p' : subfield K) : ((p ⊓ p' : subfield K) : set K) = p ∩ p' := rfl

@[simp] lemma mem_inf {p p' : subfield K} {x : K} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' := iff.rfl

instance : has_Inf (subfield K) :=
⟨λ S,
  { inv_mem' := begin
      rintros x hx,
      apply subring.mem_Inf.mpr,
      rintro _ ⟨p, p_mem, rfl⟩,
      exact p.inv_mem (subring.mem_Inf.mp hx p.to_subring ⟨p, p_mem, rfl⟩),
    end,
    .. Inf (subfield.to_subring '' S) }⟩

@[simp, norm_cast] lemma coe_Inf (S : set (subfield K)) :
  ((Inf S : subfield K) : set K) = ⋂ s ∈ S, ↑s :=
show ((Inf (subfield.to_subring '' S) : subring K) : set K) = ⋂ s ∈ S, ↑s,
begin
  ext x,
  rw [subring.coe_Inf, set.mem_Inter, set.mem_Inter],
  exact ⟨λ h s s' ⟨s_mem, s'_eq⟩, h s.to_subring _ ⟨⟨s, s_mem, rfl⟩, s'_eq⟩,
         λ h s s' ⟨⟨s'', s''_mem, s_eq⟩, (s'_eq : ↑s = s')⟩,
           h s'' _ ⟨s''_mem, by simp [←s_eq, ← s'_eq]⟩⟩
end

lemma mem_Inf {S : set (subfield K)} {x : K} : x ∈ Inf S ↔ ∀ p ∈ S, x ∈ p :=
subring.mem_Inf.trans
  ⟨λ h p hp, h p.to_subring ⟨p, hp, rfl⟩,
   λ h p ⟨p', hp', p_eq⟩, p_eq ▸ h p' hp'⟩

@[simp] lemma Inf_to_subring (s : set (subfield K)) :
  (Inf s).to_subring = ⨅ t ∈ s, subfield.to_subring t :=
begin
  ext x,
  rw [mem_to_subring, mem_Inf],
  erw subring.mem_Inf,
  exact ⟨λ h p ⟨p', hp⟩, hp ▸ subring.mem_Inf.mpr (λ p ⟨hp', hp⟩, hp ▸ h _ hp'),
         λ h p hp, h p.to_subring ⟨p, subring.ext (λ x,
           ⟨λ hx, subring.mem_Inf.mp hx _ ⟨hp, rfl⟩,
            λ hx, subring.mem_Inf.mpr (λ p' ⟨hp, p'_eq⟩, p'_eq ▸ hx)⟩)⟩⟩
end

lemma is_glb_Inf (S : set (subfield K)) : is_glb S (Inf S) :=
begin
  refine is_glb.of_image (λ s t, show (s : set K) ≤ t ↔ s ≤ t, from set_like.coe_subset_coe) _,
  convert is_glb_binfi,
  exact coe_Inf _
end

/-- Subfields of a ring form a complete lattice. -/
instance : complete_lattice (subfield K) :=
{ top := ⊤,
  le_top := λ s x hx, trivial,
  inf := (⊓),
  inf_le_left := λ s t x, and.left,
  inf_le_right := λ s t x, and.right,
  le_inf := λ s t₁ t₂ h₁ h₂ x hx, ⟨h₁ hx, h₂ hx⟩,
  .. complete_lattice_of_Inf (subfield K) is_glb_Inf }

/-! # subfield closure of a subset -/

/-- The `subfield` generated by a set. -/
def closure (s : set K) : subfield K :=
{ carrier := { (x / y) | (x ∈ subring.closure s) (y ∈ subring.closure s) },
  zero_mem' := ⟨0, subring.zero_mem _, 1, subring.one_mem _, div_one _⟩,
  one_mem' := ⟨1, subring.one_mem _, 1, subring.one_mem _, div_one _⟩,
  neg_mem' := λ x ⟨y, hy, z, hz, x_eq⟩, ⟨-y, subring.neg_mem _ hy, z, hz, x_eq ▸ neg_div _ _⟩,
  inv_mem' := λ x ⟨y, hy, z, hz, x_eq⟩, ⟨z, hz, y, hy, x_eq ▸ inv_div.symm⟩,
  add_mem' := λ x y x_mem y_mem, begin
    obtain ⟨nx, hnx, dx, hdx, rfl⟩ := id x_mem,
    obtain ⟨ny, hny, dy, hdy, rfl⟩ := id y_mem,
    by_cases hx0 : dx = 0, { rwa [hx0, div_zero, zero_add] },
    by_cases hy0 : dy = 0, { rwa [hy0, div_zero, add_zero] },
    exact ⟨nx * dy + dx * ny,
          subring.add_mem _ (subring.mul_mem _ hnx hdy) (subring.mul_mem _ hdx hny),
          dx * dy, subring.mul_mem _ hdx hdy,
          (div_add_div nx ny hx0 hy0).symm⟩
  end,
  mul_mem' := λ x y x_mem y_mem, begin
    obtain ⟨nx, hnx, dx, hdx, rfl⟩ := id x_mem,
    obtain ⟨ny, hny, dy, hdy, rfl⟩ := id y_mem,
    exact ⟨nx * ny, subring.mul_mem _ hnx hny,
           dx * dy, subring.mul_mem _ hdx hdy,
           (div_mul_div _ _ _ _).symm⟩
  end }

lemma mem_closure_iff {s : set K} {x} :
  x ∈ closure s ↔ ∃ (y ∈ subring.closure s) (z ∈ subring.closure s), y / z = x := iff.rfl

lemma subring_closure_le (s : set K) : subring.closure s ≤ (closure s).to_subring :=
λ x hx, ⟨x, hx, 1, subring.one_mem _, div_one x⟩

/-- The subfield generated by a set includes the set. -/
@[simp] lemma subset_closure {s : set K} : s ⊆ closure s :=
set.subset.trans subring.subset_closure (subring_closure_le s)

lemma not_mem_of_not_mem_closure {s : set K} {P : K} (hP : P ∉ closure s) : P ∉ s :=
λ h, hP (subset_closure h)

lemma mem_closure {x : K} {s : set K} : x ∈ closure s ↔ ∀ S : subfield K, s ⊆ S → x ∈ S :=
⟨λ ⟨y, hy, z, hz, x_eq⟩ t le, x_eq ▸
  t.div_mem
    (subring.mem_closure.mp hy t.to_subring le)
    (subring.mem_closure.mp hz t.to_subring le),
  λ h, h (closure s) subset_closure⟩

/-- A subfield `t` includes `closure s` if and only if it includes `s`. -/
@[simp]
lemma closure_le {s : set K} {t : subfield K} : closure s ≤ t ↔ s ⊆ t :=
⟨set.subset.trans subset_closure, λ h x hx, mem_closure.mp hx t h⟩

/-- Subfield closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
lemma closure_mono ⦃s t : set K⦄ (h : s ⊆ t) : closure s ≤ closure t :=
closure_le.2 $ set.subset.trans h subset_closure

lemma closure_eq_of_le {s : set K} {t : subfield K} (h₁ : s ⊆ t) (h₂ : t ≤ closure s) :
  closure s = t :=
le_antisymm (closure_le.2 h₁) h₂

/-- An induction principle for closure membership. If `p` holds for `1`, and all elements
of `s`, and is preserved under addition, negation, and multiplication, then `p` holds for all
elements of the closure of `s`. -/
@[elab_as_eliminator]
lemma closure_induction {s : set K} {p : K → Prop} {x} (h : x ∈ closure s)
  (Hs : ∀ x ∈ s, p x) (H1 : p 1)
  (Hadd : ∀ x y, p x → p y → p (x + y))
  (Hneg : ∀ x, p x → p (-x))
  (Hinv : ∀ x, p x → p (x⁻¹))
  (Hmul : ∀ x y, p x → p y → p (x * y)) : p x :=
(@closure_le _ _ _ ⟨p, H1, Hmul,
  @add_neg_self K _ 1 ▸ Hadd _ _ H1 (Hneg _ H1), Hadd, Hneg, Hinv⟩).2 Hs h

variable (K)
/-- `closure` forms a Galois insertion with the coercion to set. -/
protected def gi : galois_insertion (@closure K _) coe :=
{ choice := λ s _, closure s,
  gc := λ s t, closure_le,
  le_l_u := λ s, subset_closure,
  choice_eq := λ s h, rfl }

variable {K}

/-- Closure of a subfield `S` equals `S`. -/
lemma closure_eq (s : subfield K) : closure (s : set K) = s := (subfield.gi K).l_u_eq s

@[simp] lemma closure_empty : closure (∅ : set K) = ⊥ := (subfield.gi K).gc.l_bot

@[simp] lemma closure_univ : closure (set.univ : set K) = ⊤ := @coe_top K _ ▸ closure_eq ⊤

lemma closure_union (s t : set K) : closure (s ∪ t) = closure s ⊔ closure t :=
(subfield.gi K).gc.l_sup

lemma closure_Union {ι} (s : ι → set K) : closure (⋃ i, s i) = ⨆ i, closure (s i) :=
(subfield.gi K).gc.l_supr

lemma closure_sUnion (s : set (set K)) : closure (⋃₀ s) = ⨆ t ∈ s, closure t :=
(subfield.gi K).gc.l_Sup

lemma map_sup (s t : subfield K) (f : K →+* L) : (s ⊔ t).map f = s.map f ⊔ t.map f :=
(gc_map_comap f).l_sup

lemma map_supr {ι : Sort*} (f : K →+* L) (s : ι → subfield K) :
  (supr s).map f = ⨆ i, (s i).map f :=
(gc_map_comap f).l_supr

lemma comap_inf (s t : subfield L) (f : K →+* L) : (s ⊓ t).comap f = s.comap f ⊓ t.comap f :=
(gc_map_comap f).u_inf

lemma comap_infi {ι : Sort*} (f : K →+* L) (s : ι → subfield L) :
  (infi s).comap f = ⨅ i, (s i).comap f :=
(gc_map_comap f).u_infi

@[simp] lemma map_bot (f : K →+* L) : (⊥ : subfield K).map f = ⊥ :=
(gc_map_comap f).l_bot

@[simp] lemma comap_top (f : K →+* L) : (⊤ : subfield L).comap f = ⊤ :=
(gc_map_comap f).u_top

/-- The underlying set of a non-empty directed Sup of subfields is just a union of the subfields.
  Note that this fails without the directedness assumption (the union of two subfields is
  typically not a subfield) -/
lemma mem_supr_of_directed {ι} [hι : nonempty ι] {S : ι → subfield K} (hS : directed (≤) S)
  {x : K} : x ∈ (⨆ i, S i) ↔ ∃ i, x ∈ S i :=
begin
  refine ⟨_, λ ⟨i, hi⟩, (set_like.le_def.1 $ le_supr S i) hi⟩,
  suffices : x ∈ closure (⋃ i, (S i : set K)) → ∃ i, x ∈ S i,
  by simpa only [closure_Union, closure_eq],
  refine λ hx, closure_induction hx (λ x, set.mem_Union.mp) _ _ _ _ _,
  { exact hι.elim (λ i, ⟨i, (S i).one_mem⟩) },
  { rintros x y ⟨i, hi⟩ ⟨j, hj⟩,
    obtain ⟨k, hki, hkj⟩ := hS i j,
    exact ⟨k, (S k).add_mem (hki hi) (hkj hj)⟩ },
  { rintros x ⟨i, hi⟩,
    exact ⟨i, (S i).neg_mem hi⟩ },
  { rintros x ⟨i, hi⟩,
    exact ⟨i, (S i).inv_mem hi⟩ },
  { rintros x y ⟨i, hi⟩ ⟨j, hj⟩,
    obtain ⟨k, hki, hkj⟩ := hS i j,
    exact ⟨k, (S k).mul_mem (hki hi) (hkj hj)⟩ }
end

lemma coe_supr_of_directed {ι} [hι : nonempty ι] {S : ι → subfield K} (hS : directed (≤) S) :
  ((⨆ i, S i : subfield K) : set K) = ⋃ i, ↑(S i) :=
set.ext $ λ x, by simp [mem_supr_of_directed hS]

lemma mem_Sup_of_directed_on {S : set (subfield K)} (Sne : S.nonempty)
  (hS : directed_on (≤) S) {x : K} :
  x ∈ Sup S ↔ ∃ s ∈ S, x ∈ s :=
begin
  haveI : nonempty S := Sne.to_subtype,
  simp only [Sup_eq_supr', mem_supr_of_directed hS.directed_coe, set_coe.exists, subtype.coe_mk]
end

lemma coe_Sup_of_directed_on {S : set (subfield K)} (Sne : S.nonempty) (hS : directed_on (≤) S) :
  (↑(Sup S) : set K) = ⋃ s ∈ S, ↑s :=
set.ext $ λ x, by simp [mem_Sup_of_directed_on Sne hS]

end subfield

namespace ring_hom

variables {s : subfield K}

open subfield

/-- Restrict the codomain of a ring homomorphism to a subfield that includes the range. -/
def cod_restrict_field (f : K →+* L)
  (s : subfield L) (h : ∀ x, f x ∈ s) : K →+* s :=
{ to_fun := λ x, ⟨f x, h x⟩,
  map_add' := λ x y, subtype.eq $ f.map_add x y,
  map_zero' := subtype.eq f.map_zero,
  map_mul' := λ x y, subtype.eq $ f.map_mul x y,
  map_one' := subtype.eq f.map_one }

/-- Restriction of a ring homomorphism to a subfield of the domain. -/
def restrict_field (f : K →+* L) (s : subfield K) : s →+* L := f.comp s.subtype

@[simp] lemma restrict_field_apply (f : K →+* L) (x : s) : f.restrict_field s x = f x := rfl

/-- Restriction of a ring homomorphism to its range interpreted as a subfield. -/
def range_restrict_field (f : K →+* L) : K →+* f.field_range :=
f.srange_restrict

@[simp] lemma coe_range_restrict_field (f : K →+* L) (x : K) :
  (f.range_restrict_field x : L) = f x := rfl

/-- The subfield of elements `x : R` such that `f x = g x`, i.e.,
the equalizer of f and g as a subfield of R -/
def eq_locus_field (f g : K →+* L) : subfield K :=
{ inv_mem' := λ x (hx : f x = g x), show f x⁻¹ = g x⁻¹, by rw [f.map_inv, g.map_inv, hx],
  carrier := {x | f x = g x}, .. (f : K →+* L).eq_locus g }

/-- If two ring homomorphisms are equal on a set, then they are equal on its subfield closure. -/
lemma eq_on_field_closure {f g : K →+* L} {s : set K} (h : set.eq_on f g s) :
  set.eq_on f g (closure s) :=
show closure s ≤ f.eq_locus_field g, from closure_le.2 h

lemma eq_of_eq_on_subfield_top {f g : K →+* L} (h : set.eq_on f g (⊤ : subfield K)) :
  f = g :=
ext $ λ x, h trivial

lemma eq_of_eq_on_of_field_closure_eq_top {s : set K} (hs : closure s = ⊤) {f g : K →+* L}
  (h : s.eq_on f g) : f = g :=
eq_of_eq_on_subfield_top $ hs ▸ eq_on_field_closure h

lemma field_closure_preimage_le (f : K →+* L) (s : set L) :
  closure (f ⁻¹' s) ≤ (closure s).comap f :=
closure_le.2 $ λ x hx, set_like.mem_coe.2 $ mem_comap.2 $ subset_closure hx

/-- The image under a ring homomorphism of the subfield generated by a set equals
the subfield generated by the image of the set. -/
lemma map_field_closure (f : K →+* L) (s : set K) :
  (closure s).map f = closure (f '' s) :=
le_antisymm
  (map_le_iff_le_comap.2 $ le_trans (closure_mono $ set.subset_preimage_image _ _)
    (field_closure_preimage_le _ _))
  (closure_le.2 $ set.image_subset _ subset_closure)

end ring_hom

namespace subfield

open ring_hom

/-- The ring homomorphism associated to an inclusion of subfields. -/
def inclusion {S T : subfield K} (h : S ≤ T) : S →+* T :=
S.subtype.cod_restrict_field _ (λ x, h x.2)

@[simp] lemma field_range_subtype (s : subfield K) : s.subtype.field_range = s :=
set_like.ext' $ (coe_srange _).trans subtype.range_coe

end subfield

namespace ring_equiv

variables {s t : subfield K}

/-- Makes the identity isomorphism from a proof two subfields of a multiplicative
    monoid are equal. -/
def subfield_congr (h : s = t) : s ≃+* t :=
{ map_mul' :=  λ _ _, rfl, map_add' := λ _ _, rfl, ..equiv.set_congr $ set_like.ext'_iff.1 h }

end ring_equiv

namespace subfield

variables {s : set K}

lemma closure_preimage_le (f : K →+* L) (s : set L) :
  closure (f ⁻¹' s) ≤ (closure s).comap f :=
closure_le.2 $ λ x hx, set_like.mem_coe.2 $ mem_comap.2 $ subset_closure hx

end subfield
