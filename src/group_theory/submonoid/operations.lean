import group_theory.submonoid.basic
import data.equiv.mul_add
import algebra.group.prod

/-!
# Operations on `submonoid`s

In this file we define the following operations on `submonoid`s:

* `submonoid.to_add_submonoid`, `submonoid.of_add_submonoid`, `add_submonoid.to_submonoid`,
  `add_submonoid.of_submonoid`: convert between multiplicative and additive submonoids of `M`,
  `multiplicative M`, and `additive M`.
* `submonoid.add_submonoid_equiv`: equivalence between `submonoid M`
  and `add_submonoid (additive M)`.
* `submonoid.comap`: preimage of a submonoid under a monoid homomorphism as a submonoid of the
  domain;
* `submonoid.map`: image of a submonoid under a monoid homomorphism as a submonoid of the codomain;
* `monoid_hom.mrange`: range of a monoid homomorphism as a submonoid of the codomain;

-/

/-!
### Conversion to/from `additive`/`multiplicative`
-/

/-- Map from submonoids of monoid `M` to `add_submonoid`s of `additive M`. -/
def submonoid.to_add_submonoid {M : Type*} [monoid M] (S : submonoid M) :
  add_submonoid (additive M) :=
{ carrier := S.carrier,
  zero_mem' := S.one_mem',
  add_mem' := S.mul_mem' }

/-- Map from `add_submonoid`s of `additive M` to submonoids of `M`. -/
def submonoid.of_add_submonoid {M : Type*} [monoid M] (S : add_submonoid (additive M)) :
  submonoid M :=
{ carrier := S.carrier,
  one_mem' := S.zero_mem',
  mul_mem' := S.add_mem' }

/-- Map from `add_submonoid`s of `add_monoid M` to submonoids of `multiplicative M`. -/
def add_submonoid.to_submonoid {M : Type*} [add_monoid M] (S : add_submonoid M) :
  submonoid (multiplicative M) :=
{ carrier := S.carrier,
  one_mem' := S.zero_mem',
  mul_mem' := S.add_mem' }

/-- Map from submonoids of `multiplicative M` to `add_submonoid`s of `add_monoid M`. -/
def add_submonoid.of_submonoid {M : Type*} [add_monoid M] (S : submonoid (multiplicative M)) :
  add_submonoid M :=
{ carrier := S.carrier,
  zero_mem' := S.one_mem',
  add_mem' := S.mul_mem' }

/-- Submonoids of monoid `M` are isomorphic to additive submonoids of `additive M`. -/
def submonoid.add_submonoid_equiv (M : Type*) [monoid M] :
  submonoid M ≃ add_submonoid (additive M) :=
{ to_fun := submonoid.to_add_submonoid,
  inv_fun := submonoid.of_add_submonoid,
  left_inv := λ x, by cases x; refl,
  right_inv := λ x, by cases x; refl }

namespace submonoid

variables {M N : Type*} [monoid M] [monoid N]

/-!
### `comap` and `map`
-/

/-- The preimage of a submonoid along a monoid homomorphism is a submonoid. -/
@[to_additive "The preimage of an `add_submonoid` along an `add_monoid` homomorphism is an
`add_submonoid`."]
def comap (f : M →* N) (S : submonoid N) : submonoid M :=
{ carrier := (f ⁻¹' S),
  one_mem' := show f 1 ∈ S, by rw f.map_one; exact S.one_mem,
  mul_mem' := λ a b ha hb,
    show f (a * b) ∈ S, by rw f.map_mul; exact S.mul_mem ha hb }

@[simp, to_additive]
lemma coe_comap (S : submonoid N) (f : M →* N) : (S.comap f : set M) = f ⁻¹' S := rfl

@[simp, to_additive]
lemma mem_comap {S : submonoid N} {f : M →* N} {x : M} : x ∈ S.comap f ↔ f x ∈ S := iff.rfl

@[to_additive]
lemma comap_comap (S : submonoid P) (g : N →* P) (f : M →* N) :
  (S.comap g).comap f = S.comap (g.comp f) :=
rfl

/-- The image of a submonoid along a monoid homomorphism is a submonoid. -/
@[to_additive "The image of an `add_submonoid` along an `add_monoid` homomorphism is
an `add_submonoid`."]
def map (f : M →* N) (S : submonoid M) : submonoid N :=
{ carrier := (f '' S),
  one_mem' := ⟨1, S.one_mem, f.map_one⟩,
  mul_mem' := begin rintros _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩, exact ⟨x * y, S.mul_mem hx hy,
    by rw f.map_mul; refl⟩ end }

@[simp, to_additive]
lemma coe_map (f : M →* N) (S : submonoid M) :
  (S.map f : set N) = f '' S := rfl

@[simp, to_additive]
lemma mem_map {f : M →* N} {S : submonoid M} {y : N} :
  y ∈ S.map f ↔ ∃ x ∈ S, f x = y :=
mem_image_iff_bex

@[to_additive]
lemma map_map (g : N →* P) (f : M →* N) : (S.map f).map g = S.map (g.comp f) :=
ext' $ image_image _ _ _

@[to_additive]
lemma map_le_iff_le_comap {f : M →* N} {S : submonoid M} {T : submonoid N} :
  S.map f ≤ T ↔ S ≤ T.comap f :=
image_subset_iff

@[to_additive]
lemma gc_map_comap (f : M →* N) : galois_connection (map f) (comap f) :=
λ S T, map_le_iff_le_comap

@[to_additive]
lemma map_sup (S T : submonoid M) (f : M →* N) : (S ⊔ T).map f = S.map f ⊔ T.map f :=
(gc_map_comap f).l_sup

@[to_additive]
lemma map_supr {ι : Sort*} (f : M →* N) (s : ι → submonoid M) :
  (supr s).map f = ⨆ i, (s i).map f :=
(gc_map_comap f).l_supr

@[to_additive]
lemma comap_inf (S T : submonoid N) (f : M →* N) : (S ⊓ T).comap f = S.comap f ⊓ T.comap f :=
(gc_map_comap f).u_inf

@[to_additive]
lemma comap_infi {ι : Sort*} (f : M →* N) (s : ι → submonoid N) :
  (infi s).comap f = ⨅ i, (s i).comap f :=
(gc_map_comap f).u_infi

@[simp, to_additive] lemma map_bot (f : M →* N) : (⊥ : submonoid M).map f = ⊥ :=
(gc_map_comap f).l_bot

@[simp, to_additive] lemma comap_top (f : M →* N) : (⊤ : submonoid N).comap f = ⊤ :=
(gc_map_comap f).u_top

@[simp, to_additive] lemma map_id (S : submonoid M) : S.map (monoid_hom.id M) = S :=
ext (λ x, ⟨λ ⟨_, h, rfl⟩, h, λ h, ⟨_, h, rfl⟩⟩)

end submonoid

namespace monoid_hom

variables {N : Type*} {P : Type*} [monoid N] [monoid P] (S : submonoid M)

open submonoid

/-- The range of a monoid homomorphism is a submonoid. -/
@[to_additive "The range of an `add_monoid_hom` is an `add_submonoid`."]
def mrange (f : M →* N) : submonoid N := (⊤ : submonoid M).map f

@[simp, to_additive] lemma coe_mrange (f : M →* N) :
  (f.mrange : set N) = set.range f :=
set.image_univ

@[simp, to_additive] lemma mem_mrange {f : M →* N} {y : N} :
  y ∈ f.mrange ↔ ∃ x, f x = y :=
by simp [mrange]

@[to_additive]
lemma map_mrange (g : N →* P) (f : M →* N) : f.mrange.map g = (g.comp f).mrange :=
(⊤ : submonoid M).map_map g f

@[to_additive]
lemma mrange_top_iff_surjective {N} [monoid N] {f : M →* N} :
  f.mrange = (⊤ : submonoid N) ↔ function.surjective f :=
submonoid.ext'_iff.trans $ iff.trans (by rw [coe_mrange, coe_top]) set.range_iff_surjective

/-- The range of a surjective monoid hom is the whole of the codomain. -/
@[to_additive "The range of a surjective `add_monoid` hom is the whole of the codomain."]
lemma mrange_top_of_surjective {N} [monoid N] (f : M →* N) (hf : function.surjective f) :
  f.mrange = (⊤ : submonoid N) :=
mrange_top_iff_surjective.2 hf

@[to_additive]
lemma mclosure_preimage_le (f : M →* N) (s : set N) :
  closure (f ⁻¹' s) ≤ (closure s).comap f :=
closure_le.2 $ λ x hx, mem_coe.2 $ mem_comap.2 $ subset_closure hx

/-- The image under a monoid hom of the submonoid generated by a set equals the submonoid generated
    by the image of the set. -/
@[to_additive "The image under an `add_monoid` hom of the `add_submonoid` generated by a set equals
the `add_submonoid` generated by the image of the set."]
lemma map_mclosure (f : M →* N) (s : set M) :
  (closure s).map f = closure (f '' s) :=
le_antisymm
  (map_le_iff_le_comap.2 $ le_trans (closure_mono $ set.subset_preimage_image _ _)
    (mclosure_preimage_le _ _))
  (closure_le.2 $ set.image_subset _ subset_closure)

end monoid_hom
