/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/

import algebra.algebra.basic
import algebra.category.Ring.basic
import ring_theory.ideal.operations

/-!

# Local rings

Define local rings as commutative rings having a unique maximal ideal.

## Main definitions

* `local_ring`: A predicate on commutative semirings, stating that for any pair of elements that
  adds up to `1`, one of them is a unit. This is shown to be equivalent to the condition that there
  exists a unique maximal ideal.
* `local_ring.maximal_ideal`: The unique maximal ideal for a local rings. Its carrier set is the
  set of non units.
* `is_local_ring_hom`: A predicate on semiring homomorphisms, requiring that it maps nonunits
  to nonunits. For local rings, this means that the image of the unique maximal ideal is again
  contained in the unique maximal ideal.
* `local_ring.residue_field`: The quotient of a local ring by its maximal ideal.

-/

universes u v w u'

variables {R : Type u} {S : Type v} {T : Type w} {K : Type u'}

/-- A semiring is local if it is nontrivial and `a` or `b` is a unit whenever `a + b = 1`.
Note that `local_ring` is a predicate. -/
class local_ring (R : Type u) [semiring R] extends nontrivial R : Prop :=
of_is_unit_or_is_unit_of_add_one ::
(is_unit_or_is_unit_of_add_one {a b : R} (h : a + b = 1) : is_unit a ∨ is_unit b)

section comm_semiring
variables [comm_semiring R]

namespace local_ring

lemma of_is_unit_or_is_unit_of_is_unit_add [nontrivial R]
  (h : ∀ a b : R, is_unit (a + b) → is_unit a ∨ is_unit b) :
  local_ring R :=
⟨λ a b hab,  h a b $ hab.symm ▸ is_unit_one⟩

/-- A semiring is local if it is nontrivial and the set of nonunits is closed under the addition. -/
lemma of_nonunits_add [nontrivial R]
  (h : ∀ a b : R, a ∈ nonunits R → b ∈ nonunits R → a + b ∈ nonunits R) :
  local_ring R :=
⟨λ a b hab, or_iff_not_and_not.2 $ λ H, h a b H.1 H.2 $ hab.symm ▸ is_unit_one⟩

/-- A semiring is local if it has a unique maximal ideal. -/
lemma of_unique_max_ideal (h : ∃! I : ideal R, I.is_maximal) :
  local_ring R :=
@of_nonunits_add _ _ (nontrivial_of_ne (0 : R) 1 $
  let ⟨I, Imax, _⟩ := h in (λ (H : 0 = 1), Imax.1.1 $ I.eq_top_iff_one.2 $ H ▸ I.zero_mem)) $
  λ x y hx hy H,
    let ⟨I, Imax, Iuniq⟩ := h in
    let ⟨Ix, Ixmax, Hx⟩ := exists_max_ideal_of_mem_nonunits hx in
    let ⟨Iy, Iymax, Hy⟩ := exists_max_ideal_of_mem_nonunits hy in
    have xmemI : x ∈ I, from Iuniq Ix Ixmax ▸ Hx,
    have ymemI : y ∈ I, from Iuniq Iy Iymax ▸ Hy,
    Imax.1.1 $ I.eq_top_of_is_unit_mem (I.add_mem xmemI ymemI) H

lemma of_unique_nonzero_prime (h : ∃! P : ideal R, P ≠ ⊥ ∧ ideal.is_prime P) :
  local_ring R :=
of_unique_max_ideal begin
  rcases h with ⟨P, ⟨hPnonzero, hPnot_top, _⟩, hPunique⟩,
  refine ⟨P, ⟨⟨hPnot_top, _⟩⟩, λ M hM, hPunique _ ⟨_, ideal.is_maximal.is_prime hM⟩⟩,
  { refine ideal.maximal_of_no_maximal (λ M hPM hM, ne_of_lt hPM _),
    exact (hPunique _ ⟨ne_bot_of_gt hPM, ideal.is_maximal.is_prime hM⟩).symm },
  { rintro rfl,
    exact hPnot_top (hM.1.2 P (bot_lt_iff_ne_bot.2 hPnonzero)) },
end

variables [local_ring R]

lemma is_unit_or_is_unit_of_is_unit_add {a b : R} (h : is_unit (a + b)) :
  is_unit a ∨ is_unit b :=
begin
  rcases h with ⟨u, hu⟩,
  rw [units.eq_iff_inv_mul, mul_add] at hu,
  apply or.imp _ _ (is_unit_or_is_unit_of_add_one hu);
    exact is_unit_of_mul_is_unit_right,
end

lemma nonunits_add {a b : R} (ha : a ∈ nonunits R) (hb : b ∈ nonunits R) : a + b ∈ nonunits R:=
λ H, not_or ha hb (is_unit_or_is_unit_of_is_unit_add H)

variables (R)

/-- The ideal of elements that are not units. -/
def maximal_ideal : ideal R :=
{ carrier := nonunits R,
  zero_mem' := zero_mem_nonunits.2 $ zero_ne_one,
  add_mem' := λ x y hx hy, nonunits_add hx hy,
  smul_mem' := λ a x, mul_mem_nonunits_right }

instance maximal_ideal.is_maximal : (maximal_ideal R).is_maximal :=
begin
  rw ideal.is_maximal_iff,
  split,
  { intro h, apply h, exact is_unit_one },
  { intros I x hI hx H,
    erw not_not at hx,
    rcases hx with ⟨u,rfl⟩,
    simpa using I.mul_mem_left ↑u⁻¹ H }
end

lemma maximal_ideal_unique : ∃! I : ideal R, I.is_maximal :=
⟨maximal_ideal R, maximal_ideal.is_maximal R,
  λ I hI, hI.eq_of_le (maximal_ideal.is_maximal R).1.1 $
  λ x hx, hI.1.1 ∘ I.eq_top_of_is_unit_mem hx⟩

variable {R}

lemma eq_maximal_ideal {I : ideal R} (hI : I.is_maximal) : I = maximal_ideal R :=
unique_of_exists_unique (maximal_ideal_unique R) hI $ maximal_ideal.is_maximal R

lemma le_maximal_ideal {J : ideal R} (hJ : J ≠ ⊤) : J ≤ maximal_ideal R :=
begin
  rcases ideal.exists_le_maximal J hJ with ⟨M, hM1, hM2⟩,
  rwa ←eq_maximal_ideal hM1
end

@[simp] lemma mem_maximal_ideal (x) : x ∈ maximal_ideal R ↔ x ∈ nonunits R := iff.rfl

end local_ring

end comm_semiring

section comm_ring
variables [comm_ring R]

namespace local_ring

lemma of_is_unit_or_is_unit_one_sub_self [nontrivial R]
  (h : ∀ a : R, is_unit a ∨ is_unit (1 - a)) : local_ring R :=
⟨λ a b hab, add_sub_cancel' a b ▸ hab.symm ▸ h a⟩

variables [local_ring R]

lemma is_unit_or_is_unit_one_sub_self (a : R) : is_unit a ∨ is_unit (1 - a) :=
is_unit_or_is_unit_of_is_unit_add $ (add_sub_cancel'_right a 1).symm ▸ is_unit_one

lemma is_unit_of_mem_nonunits_one_sub_self (a : R) (h : 1 - a ∈ nonunits R) :
  is_unit a :=
or_iff_not_imp_right.1 (is_unit_or_is_unit_one_sub_self a) h

lemma is_unit_one_sub_self_of_mem_nonunits (a : R) (h : a ∈ nonunits R) :
  is_unit (1 - a) :=
or_iff_not_imp_left.1 (is_unit_or_is_unit_one_sub_self a) h

lemma of_surjective' [comm_ring S] [nontrivial S] (f : R →+* S) (hf : function.surjective f) :
  local_ring S :=
of_is_unit_or_is_unit_one_sub_self
begin
  intros b,
  obtain ⟨a, rfl⟩ := hf b,
  apply (is_unit_or_is_unit_one_sub_self a).imp f.is_unit_map _,
  rw [← f.map_one, ← f.map_sub],
  apply f.is_unit_map,
end

end local_ring

end comm_ring

/-- A local ring homomorphism is a homomorphism `f` between local rings such that `a` in the domain
  is a unit if `f a` is a unit for any `a`. See `local_ring.local_hom_tfae` for other equivalent
  definitions. -/
class is_local_ring_hom [semiring R] [semiring S] (f : R →+* S) : Prop :=
(map_nonunit : ∀ a, is_unit (f a) → is_unit a)

section
variables [semiring R] [semiring S] [semiring T]

instance is_local_ring_hom_id (R : Type*) [semiring R] : is_local_ring_hom (ring_hom.id R) :=
{ map_nonunit := λ a, id }

@[simp] lemma is_unit_map_iff (f : R →+* S) [is_local_ring_hom f] (a) :
  is_unit (f a) ↔ is_unit a :=
⟨is_local_ring_hom.map_nonunit a, f.is_unit_map⟩

@[simp] lemma map_mem_nonunits_iff (f : R →+* S) [is_local_ring_hom f] (a) :
  f a ∈ nonunits S ↔ a ∈ nonunits R :=
⟨λ h ha, h $ (is_unit_map_iff f a).mpr ha, λ h ha, h $ (is_unit_map_iff f a).mp ha⟩

instance is_local_ring_hom_comp
  (g : S →+* T) (f : R →+* S) [is_local_ring_hom g] [is_local_ring_hom f] :
  is_local_ring_hom (g.comp f) :=
{ map_nonunit := λ a, is_local_ring_hom.map_nonunit a ∘ is_local_ring_hom.map_nonunit (f a) }

instance is_local_ring_hom_equiv (f : R ≃+* S) :
  is_local_ring_hom (f : R →+* S) :=
{ map_nonunit := λ a ha,
  begin
    convert (f.symm : S →+* R).is_unit_map ha,
    exact (ring_equiv.symm_apply_apply f a).symm,
  end }

@[simp] lemma is_unit_of_map_unit (f : R →+* S) [is_local_ring_hom f]
  (a) (h : is_unit (f a)) : is_unit a :=
is_local_ring_hom.map_nonunit a h

theorem of_irreducible_map (f : R →+* S) [h : is_local_ring_hom f] {x}
  (hfx : irreducible (f x)) : irreducible x :=
⟨λ h, hfx.not_unit $ is_unit.map f h, λ p q hx, let ⟨H⟩ := h in
or.imp (H p) (H q) $ hfx.is_unit_or_is_unit $ f.map_mul p q ▸ congr_arg f hx⟩

lemma is_local_ring_hom_of_comp (f : R →+* S) (g : S →+* T) [is_local_ring_hom (g.comp f)] :
  is_local_ring_hom f :=
⟨λ a ha, (is_unit_map_iff (g.comp f) _).mp (g.is_unit_map ha)⟩

instance _root_.CommRing.is_local_ring_hom_comp {R S T : CommRing} (f : R ⟶ S) (g : S ⟶ T)
  [is_local_ring_hom g] [is_local_ring_hom f] :
  is_local_ring_hom (f ≫ g) := is_local_ring_hom_comp _ _

/-- If `f : R →+* S` is a local ring hom, then `R` is a local ring if `S` is. -/
lemma _root_.ring_hom.domain_local_ring {R S : Type*} [comm_semiring R] [comm_semiring S]
  [H : _root_.local_ring S] (f : R →+* S)
  [is_local_ring_hom f] : _root_.local_ring R :=
begin
  haveI : nontrivial R := pullback_nonzero f f.map_zero f.map_one,
  apply local_ring.of_nonunits_add,
  intros a b,
  simp_rw [←map_mem_nonunits_iff f, f.map_add],
  exact local_ring.nonunits_add
end

section
open category_theory

lemma is_local_ring_hom_of_iso {R S : CommRing} (f : R ≅ S) : is_local_ring_hom f.hom :=
{ map_nonunit := λ a ha,
  begin
    convert f.inv.is_unit_map ha,
    rw category_theory.iso.hom_inv_id_apply,
  end }

@[priority 100] -- see Note [lower instance priority]
instance is_local_ring_hom_of_is_iso {R S : CommRing} (f : R ⟶ S) [is_iso f] :
  is_local_ring_hom f :=
is_local_ring_hom_of_iso (as_iso f)

end

end

section
open local_ring
variables [comm_semiring R] [local_ring R] [comm_semiring S] [local_ring S]

/--
The image of the maximal ideal of the source is contained within the maximal ideal of the target.
-/
lemma map_nonunit (f : R →+* S) [is_local_ring_hom f] (a : R) (h : a ∈ maximal_ideal R) :
  f a ∈ maximal_ideal S :=
λ H, h $ is_unit_of_map_unit f a H

end

namespace local_ring

section
variables [comm_semiring R] [local_ring R] [comm_semiring S] [local_ring S]

/--
A ring homomorphism between local rings is a local ring hom iff it reflects units,
i.e. any preimage of a unit is still a unit. https://stacks.math.columbia.edu/tag/07BJ
-/
theorem local_hom_tfae (f : R →+* S) :
  tfae [is_local_ring_hom f,
        f '' (maximal_ideal R).1 ⊆ maximal_ideal S,
        (maximal_ideal R).map f ≤ maximal_ideal S,
        maximal_ideal R ≤ (maximal_ideal S).comap f,
        (maximal_ideal S).comap f = maximal_ideal R] :=
begin
  tfae_have : 1 → 2, rintros _ _ ⟨a,ha,rfl⟩,
    resetI, exact map_nonunit f a ha,
  tfae_have : 2 → 4, exact set.image_subset_iff.1,
  tfae_have : 3 ↔ 4, exact ideal.map_le_iff_le_comap,
  tfae_have : 4 → 1, intro h, fsplit, exact λ x, not_imp_not.1 (@h x),
  tfae_have : 1 → 5, intro, resetI, ext,
    exact not_iff_not.2 (is_unit_map_iff f x),
  tfae_have : 5 → 4, exact λ h, le_of_eq h.symm,
  tfae_finish,
end

end

lemma of_surjective [comm_semiring R] [local_ring R] [comm_semiring S] [nontrivial S]
  (f : R →+* S) [is_local_ring_hom f] (hf : function.surjective f) :
  local_ring S :=
of_is_unit_or_is_unit_of_is_unit_add
begin
  intros a b hab,
  obtain ⟨a, rfl⟩ := hf a,
  obtain ⟨b, rfl⟩ := hf b,
  rw ←map_add at hab,
  exact (is_unit_or_is_unit_of_is_unit_add $ is_local_ring_hom.map_nonunit _ hab).imp
    f.is_unit_map f.is_unit_map
end

section
variables (R) [comm_ring R] [local_ring R] [comm_ring S] [local_ring S]

/-- The residue field of a local ring is the quotient of the ring by its maximal ideal. -/
def residue_field := R ⧸ maximal_ideal R

noncomputable instance residue_field.field : field (residue_field R) :=
ideal.quotient.field (maximal_ideal R)

noncomputable instance : inhabited (residue_field R) := ⟨37⟩

/-- The quotient map from a local ring to its residue field. -/
def residue : R →+* (residue_field R) :=
ideal.quotient.mk _

noncomputable
instance residue_field.algebra : algebra R (residue_field R) := (residue R).to_algebra

variables {R}

namespace residue_field

/-- The map on residue fields induced by a local homomorphism between local rings -/
noncomputable def map (f : R →+* S) [is_local_ring_hom f] :
  residue_field R →+* residue_field S :=
ideal.quotient.lift (maximal_ideal R) ((ideal.quotient.mk _).comp f) $
λ a ha,
begin
  erw ideal.quotient.eq_zero_iff_mem,
  exact map_nonunit f a ha
end

end residue_field

lemma ker_eq_maximal_ideal [field K] (φ : R →+* K) (hφ : function.surjective φ) :
  φ.ker = maximal_ideal R :=
local_ring.eq_maximal_ideal $ φ.ker_is_maximal_of_surjective hφ

end

end local_ring

namespace field
variables (K) [field K]

open_locale classical

@[priority 100] -- see Note [lower instance priority]
instance : local_ring K :=
local_ring.of_is_unit_or_is_unit_one_sub_self $ λ a,
  if h : a = 0
  then or.inr (by rw [h, sub_zero]; exact is_unit_one)
  else or.inl $ is_unit.mk0 a h

end field
