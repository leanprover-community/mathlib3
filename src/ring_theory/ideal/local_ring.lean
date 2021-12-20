/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/

import algebra.algebra.basic
import algebra.category.CommRing.basic
import ring_theory.ideal.operations

/-!

# Local rings

Define local rings as commutative rings having a unique maximal ideal.

## Main definitions

* `local_ring`: A predicate on commutative rings, stating that every element `a` is either a unit
  or `1 - a` is a unit. This is shown to be equivalent to the condition that there exists a unique
  maximal ideal.
* `local_ring.maximal_ideal`: The unique maximal ideal for a local rings. Its carrier set is the set
  of non units.
* `is_local_ring_hom`: A predicate on semiring homomorphisms, requiring that it maps nonunits
  to nonunits. For local rings, this means that the image of the unique maximal ideal is again
  contained in the unique maximal ideal.
* `local_ring.residue_field`: The quotient of a local ring by its maximal ideal.

-/

universes u v w

/-- A commutative ring is local if it has a unique maximal ideal. Note that
  `local_ring` is a predicate. -/
class local_ring (R : Type u) [comm_ring R] extends nontrivial R : Prop :=
(is_local : ∀ (a : R), (is_unit a) ∨ (is_unit (1 - a)))

namespace local_ring

variables {R : Type u} [comm_ring R] [local_ring R]

lemma is_unit_or_is_unit_one_sub_self (a : R) :
  (is_unit a) ∨ (is_unit (1 - a)) :=
is_local a

lemma is_unit_of_mem_nonunits_one_sub_self (a : R) (h : (1 - a) ∈ nonunits R) :
  is_unit a :=
or_iff_not_imp_right.1 (is_local a) h

lemma is_unit_one_sub_self_of_mem_nonunits (a : R) (h : a ∈ nonunits R) :
  is_unit (1 - a) :=
or_iff_not_imp_left.1 (is_local a) h

lemma nonunits_add {x y} (hx : x ∈ nonunits R) (hy : y ∈ nonunits R) :
  x + y ∈ nonunits R :=
begin
  rintros ⟨u, hu⟩,
  apply hy,
  suffices : is_unit ((↑u⁻¹ : R) * y),
  { rcases this with ⟨s, hs⟩,
    use u * s,
    convert congr_arg (λ z, (u : R) * z) hs,
    rw ← mul_assoc, simp },
  rw show (↑u⁻¹ * y) = (1 - ↑u⁻¹ * x),
  { rw eq_sub_iff_add_eq,
    replace hu := congr_arg (λ z, (↑u⁻¹ : R) * z) hu.symm,
    simpa [mul_add, add_comm] using hu },
  apply is_unit_one_sub_self_of_mem_nonunits,
  exact mul_mem_nonunits_right hx
end

variable (R)

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

lemma maximal_ideal_unique :
  ∃! I : ideal R, I.is_maximal :=
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

@[simp] lemma mem_maximal_ideal (x) :
  x ∈ maximal_ideal R ↔ x ∈ nonunits R := iff.rfl

end local_ring

variables {R : Type u} {S : Type v} {T : Type w}

lemma local_of_nonunits_ideal [comm_ring R] (hnze : (0:R) ≠ 1)
  (h : ∀ x y ∈ nonunits R, x + y ∈ nonunits R) : local_ring R :=
{ exists_pair_ne := ⟨0, 1, hnze⟩,
  is_local := λ x, or_iff_not_imp_left.mpr $ λ hx,
  begin
    by_contra H,
    apply h _ _ hx H,
    simp [-sub_eq_add_neg, add_sub_cancel'_right]
  end }

lemma local_of_unique_max_ideal [comm_ring R] (h : ∃! I : ideal R, I.is_maximal) :
  local_ring R :=
local_of_nonunits_ideal
(let ⟨I, Imax, _⟩ := h in (λ (H : 0 = 1), Imax.1.1 $ I.eq_top_iff_one.2 $ H ▸ I.zero_mem))
$ λ x y hx hy H,
let ⟨I, Imax, Iuniq⟩ := h in
let ⟨Ix, Ixmax, Hx⟩ := exists_max_ideal_of_mem_nonunits hx in
let ⟨Iy, Iymax, Hy⟩ := exists_max_ideal_of_mem_nonunits hy in
have xmemI : x ∈ I, from ((Iuniq Ix Ixmax) ▸ Hx),
have ymemI : y ∈ I, from ((Iuniq Iy Iymax) ▸ Hy),
Imax.1.1 $ I.eq_top_of_is_unit_mem (I.add_mem xmemI ymemI) H

lemma local_of_unique_nonzero_prime (R : Type u) [comm_ring R]
  (h : ∃! P : ideal R, P ≠ ⊥ ∧ ideal.is_prime P) : local_ring R :=
local_of_unique_max_ideal begin
  rcases h with ⟨P, ⟨hPnonzero, hPnot_top, _⟩, hPunique⟩,
  refine ⟨P, ⟨⟨hPnot_top, _⟩⟩, λ M hM, hPunique _ ⟨_, ideal.is_maximal.is_prime hM⟩⟩,
  { refine ideal.maximal_of_no_maximal (λ M hPM hM, ne_of_lt hPM _),
    exact (hPunique _ ⟨ne_bot_of_gt hPM, ideal.is_maximal.is_prime hM⟩).symm },
  { rintro rfl,
    exact hPnot_top (hM.1.2 P (bot_lt_iff_ne_bot.2 hPnonzero)) },
end

lemma local_of_surjective [comm_ring R] [local_ring R] [comm_ring S] [nontrivial S]
  (f : R →+* S) (hf : function.surjective f) :
  local_ring S :=
{ is_local :=
  begin
    intros b,
    obtain ⟨a, rfl⟩ := hf b,
    apply (local_ring.is_unit_or_is_unit_one_sub_self a).imp f.is_unit_map _,
    rw [← f.map_one, ← f.map_sub],
    apply f.is_unit_map,
  end,
  .. ‹nontrivial S› }

/-- A local ring homomorphism is a homomorphism between local rings
  such that the image of the maximal ideal of the source is contained within
  the maximal ideal of the target. -/
class is_local_ring_hom [semiring R] [semiring S] (f : R →+* S) : Prop :=
(map_nonunit : ∀ a, is_unit (f a) → is_unit a)

instance is_local_ring_hom_id (R : Type*) [semiring R] : is_local_ring_hom (ring_hom.id R) :=
{ map_nonunit := λ a, id }

@[simp] lemma is_unit_map_iff [semiring R] [semiring S] (f : R →+* S)
  [is_local_ring_hom f] (a) :
  is_unit (f a) ↔ is_unit a :=
⟨is_local_ring_hom.map_nonunit a, f.is_unit_map⟩

instance is_local_ring_hom_comp [semiring R] [semiring S] [semiring T]
  (g : S →+* T) (f : R →+* S) [is_local_ring_hom g] [is_local_ring_hom f] :
  is_local_ring_hom (g.comp f) :=
{ map_nonunit := λ a, is_local_ring_hom.map_nonunit a ∘ is_local_ring_hom.map_nonunit (f a) }

instance _root_.CommRing.is_local_ring_hom_comp {R S T : CommRing} (f : R ⟶ S) (g : S ⟶ T)
  [is_local_ring_hom g] [is_local_ring_hom f] :
  is_local_ring_hom (f ≫ g) := is_local_ring_hom_comp _ _

/-- If `f : R →+* S` is a local ring hom, then `R` is a local ring if `S` is. -/
lemma _root_.ring_hom.domain_local_ring {R S : Type*} [comm_ring R] [comm_ring S]
  [H : _root_.local_ring S] (f : R →+* S)
  [is_local_ring_hom f] : _root_.local_ring R :=
begin
  haveI : nontrivial R := pullback_nonzero f f.map_zero f.map_one,
  constructor,
  intro x,
  rw [← is_unit_map_iff f, ← is_unit_map_iff f, f.map_sub, f.map_one],
  exact _root_.local_ring.is_local (f x)
end

lemma is_local_ring_hom_of_comp {R S T: Type*} [comm_ring R] [comm_ring S] [comm_ring T]
  (f : R →+* S) (g : S →+* T) [is_local_ring_hom (g.comp f)] : is_local_ring_hom f :=
⟨λ a ha, (is_unit_map_iff (g.comp f) _).mp (g.is_unit_map ha)⟩

instance is_local_ring_hom_equiv [semiring R] [semiring S] (f : R ≃+* S) :
  is_local_ring_hom f.to_ring_hom :=
{ map_nonunit := λ a ha,
  begin
    convert f.symm.to_ring_hom.is_unit_map ha,
    rw ring_equiv.symm_to_ring_hom_apply_to_ring_hom_apply,
  end }

@[simp] lemma is_unit_of_map_unit [semiring R] [semiring S] (f : R →+* S) [is_local_ring_hom f]
  (a) (h : is_unit (f a)) : is_unit a :=
is_local_ring_hom.map_nonunit a h

theorem of_irreducible_map [semiring R] [semiring S] (f : R →+* S) [h : is_local_ring_hom f] {x : R}
  (hfx : irreducible (f x)) : irreducible x :=
⟨λ h, hfx.not_unit $ is_unit.map f.to_monoid_hom h, λ p q hx, let ⟨H⟩ := h in
or.imp (H p) (H q) $ hfx.is_unit_or_is_unit $ f.map_mul p q ▸ congr_arg f hx⟩

section
open category_theory

lemma is_local_ring_hom_of_iso {R S : CommRing} (f : R ≅ S) : is_local_ring_hom f.hom :=
{ map_nonunit := λ a ha,
  begin
    convert f.inv.is_unit_map ha,
    rw category_theory.coe_hom_inv_id,
  end }

@[priority 100] -- see Note [lower instance priority]
instance is_local_ring_hom_of_is_iso {R S : CommRing} (f : R ⟶ S) [is_iso f] :
  is_local_ring_hom f :=
is_local_ring_hom_of_iso (as_iso f)

end

section
open local_ring
variables [comm_ring R] [local_ring R] [comm_ring S] [local_ring S]
variables (f : R →+* S) [is_local_ring_hom f]

lemma map_nonunit (a : R) (h : a ∈ maximal_ideal R) : f a ∈ maximal_ideal S :=
λ H, h $ is_unit_of_map_unit f a H

end

namespace local_ring
variables [comm_ring R] [local_ring R] [comm_ring S] [local_ring S]

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

variable (R)
/-- The residue field of a local ring is the quotient of the ring by its maximal ideal. -/
def residue_field := R ⧸ maximal_ideal R

noncomputable instance residue_field.field : field (residue_field R) :=
ideal.quotient.field (maximal_ideal R)

noncomputable instance : inhabited (residue_field R) := ⟨37⟩

/-- The quotient map from a local ring to its residue field. -/
def residue : R →+* (residue_field R) :=
ideal.quotient.mk _

noncomputable instance residue_field.algebra : algebra R (residue_field R) := (residue R).to_algebra

namespace residue_field


variables {R S}
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

variables {R}

lemma ker_eq_maximal_ideal {K : Type*} [field K]
  (φ : R →+* K) (hφ : function.surjective φ) : φ.ker = maximal_ideal R :=
local_ring.eq_maximal_ideal $ φ.ker_is_maximal_of_surjective hφ

end local_ring

namespace field
variables [field R]

open_locale classical

@[priority 100] -- see Note [lower instance priority]
instance : local_ring R :=
{ is_local := λ a,
  if h : a = 0
  then or.inr (by rw [h, sub_zero]; exact is_unit_one)
  else or.inl $ is_unit.mk0 a h }

end field
