/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
import ring_theory.ideal.basic

/-!

# Local rings

Define local rings as commutative rings having a unique maximal ideal.

## Main definitions

* `nonunits`: The subset of elements of a monoid that are not units.
* `local_ring`: A predicate on commutative rings, stating that every element `a` is either a unit
  or `1 - a` is a unit. An equivalent condition in terms of maximal ideals is also given.
* `local_ring.maximal_ideal`: The unique maximal ideal for a local rings. Its carrier set is given
  by the `nonunits` above.
* `is_local_ring_hom`: A predicate on (semi)ring homomorphisms, requiring that it maps nonunits
  to nonunits. For local rings, this means that the image of the unique maximal ideal is again
  contained in the unique maximal ideal.

-/

universes u v

variables {α : Type u} {β : Type v}
variables {a b : α}

/-- The set of non-invertible elements of a monoid. -/
def nonunits (α : Type u) [monoid α] : set α := { a | ¬is_unit a }

@[simp] theorem mem_nonunits_iff [monoid α] : a ∈ nonunits α ↔ ¬ is_unit a := iff.rfl

theorem mul_mem_nonunits_right [comm_monoid α] :
  b ∈ nonunits α → a * b ∈ nonunits α :=
mt is_unit_of_mul_is_unit_right

theorem mul_mem_nonunits_left [comm_monoid α] :
  a ∈ nonunits α → a * b ∈ nonunits α :=
mt is_unit_of_mul_is_unit_left

theorem zero_mem_nonunits [semiring α] : 0 ∈ nonunits α ↔ (0:α) ≠ 1 :=
not_congr is_unit_zero_iff

@[simp] theorem one_not_mem_nonunits [monoid α] : (1:α) ∉ nonunits α :=
not_not_intro is_unit_one

theorem coe_subset_nonunits [semiring α] {I : ideal α} (h : I ≠ ⊤) :
  (I : set α) ⊆ nonunits α :=
λ x hx hu, h $ I.eq_top_of_is_unit_mem hx hu

lemma exists_max_ideal_of_mem_nonunits [comm_semiring α] (h : a ∈ nonunits α) :
  ∃ I : ideal α, I.is_maximal ∧ a ∈ I :=
begin
  have : ideal.span ({a} : set α) ≠ ⊤,
  { intro H, rw ideal.span_singleton_eq_top at H, contradiction },
  rcases ideal.exists_le_maximal _ this with ⟨I, Imax, H⟩,
  use [I, Imax], apply H, apply ideal.subset_span, exact set.mem_singleton a
end

/-- A commutative ring is local if it has a unique maximal ideal. Note that
  `local_ring` is a predicate. -/
class local_ring (α : Type u) [comm_ring α] extends nontrivial α : Prop :=
(is_local : ∀ (a : α), (is_unit a) ∨ (is_unit (1 - a)))

namespace local_ring

variables [comm_ring α] [local_ring α]

lemma is_unit_or_is_unit_one_sub_self (a : α) :
  (is_unit a) ∨ (is_unit (1 - a)) :=
is_local a

lemma is_unit_of_mem_nonunits_one_sub_self (a : α) (h : (1 - a) ∈ nonunits α) :
  is_unit a :=
or_iff_not_imp_right.1 (is_local a) h

lemma is_unit_one_sub_self_of_mem_nonunits (a : α) (h : a ∈ nonunits α) :
  is_unit (1 - a) :=
or_iff_not_imp_left.1 (is_local a) h

lemma nonunits_add {x y} (hx : x ∈ nonunits α) (hy : y ∈ nonunits α) :
  x + y ∈ nonunits α :=
begin
  rintros ⟨u, hu⟩,
  apply hy,
  suffices : is_unit ((↑u⁻¹ : α) * y),
  { rcases this with ⟨s, hs⟩,
    use u * s,
    convert congr_arg (λ z, (u : α) * z) hs,
    rw ← mul_assoc, simp },
  rw show (↑u⁻¹ * y) = (1 - ↑u⁻¹ * x),
  { rw eq_sub_iff_add_eq,
    replace hu := congr_arg (λ z, (↑u⁻¹ : α) * z) hu.symm,
    simpa [mul_add, add_comm] using hu },
  apply is_unit_one_sub_self_of_mem_nonunits,
  exact mul_mem_nonunits_right hx
end

variable (α)

/-- The ideal of elements that are not units. -/
def maximal_ideal : ideal α :=
{ carrier := nonunits α,
  zero_mem' := zero_mem_nonunits.2 $ zero_ne_one,
  add_mem' := λ x y hx hy, nonunits_add hx hy,
  smul_mem' := λ a x, mul_mem_nonunits_right }

instance maximal_ideal.is_maximal : (maximal_ideal α).is_maximal :=
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
  ∃! I : ideal α, I.is_maximal :=
⟨maximal_ideal α, maximal_ideal.is_maximal α,
  λ I hI, hI.eq_of_le (maximal_ideal.is_maximal α).1.1 $
  λ x hx, hI.1.1 ∘ I.eq_top_of_is_unit_mem hx⟩

variable {α}

lemma eq_maximal_ideal {I : ideal α} (hI : I.is_maximal) : I = maximal_ideal α :=
unique_of_exists_unique (maximal_ideal_unique α) hI $ maximal_ideal.is_maximal α

lemma le_maximal_ideal {J : ideal α} (hJ : J ≠ ⊤) : J ≤ maximal_ideal α :=
begin
  rcases ideal.exists_le_maximal J hJ with ⟨M, hM1, hM2⟩,
  rwa ←eq_maximal_ideal hM1
end

@[simp] lemma mem_maximal_ideal (x) :
  x ∈ maximal_ideal α ↔ x ∈ nonunits α := iff.rfl

end local_ring

lemma local_of_nonunits_ideal [comm_ring α] (hnze : (0:α) ≠ 1)
  (h : ∀ x y ∈ nonunits α, x + y ∈ nonunits α) : local_ring α :=
{ exists_pair_ne := ⟨0, 1, hnze⟩,
  is_local := λ x, or_iff_not_imp_left.mpr $ λ hx,
  begin
    by_contra H,
    apply h _ _ hx H,
    simp [-sub_eq_add_neg, add_sub_cancel'_right]
  end }

lemma local_of_unique_max_ideal [comm_ring α] (h : ∃! I : ideal α, I.is_maximal) :
  local_ring α :=
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

lemma local_of_surjective {A B : Type*} [comm_ring A] [local_ring A] [comm_ring B] [nontrivial B]
  (f : A →+* B) (hf : function.surjective f) :
  local_ring B :=
{ is_local :=
  begin
    intros b,
    obtain ⟨a, rfl⟩ := hf b,
    apply (local_ring.is_unit_or_is_unit_one_sub_self a).imp f.is_unit_map _,
    rw [← f.map_one, ← f.map_sub],
    apply f.is_unit_map,
  end,
  .. ‹nontrivial B› }

/-- A local ring homomorphism is a homomorphism between local rings
  such that the image of the maximal ideal of the source is contained within
  the maximal ideal of the target. -/
class is_local_ring_hom [semiring α] [semiring β] (f : α →+* β) : Prop :=
(map_nonunit : ∀ a, is_unit (f a) → is_unit a)

instance is_local_ring_hom_id (A : Type*) [semiring A] : is_local_ring_hom (ring_hom.id A) :=
{ map_nonunit := λ a, id }

@[simp] lemma is_unit_map_iff {A B : Type*} [semiring A] [semiring B] (f : A →+* B)
  [is_local_ring_hom f] (a) :
  is_unit (f a) ↔ is_unit a :=
⟨is_local_ring_hom.map_nonunit a, f.is_unit_map⟩

instance is_local_ring_hom_comp {A B C : Type*} [semiring A] [semiring B] [semiring C]
  (g : B →+* C) (f : A →+* B) [is_local_ring_hom g] [is_local_ring_hom f] :
  is_local_ring_hom (g.comp f) :=
{ map_nonunit := λ a, is_local_ring_hom.map_nonunit a ∘ is_local_ring_hom.map_nonunit (f a) }

@[simp] lemma is_unit_of_map_unit [semiring α] [semiring β] (f : α →+* β) [is_local_ring_hom f]
  (a) (h : is_unit (f a)) : is_unit a :=
is_local_ring_hom.map_nonunit a h

theorem of_irreducible_map [semiring α] [semiring β] (f : α →+* β) [h : is_local_ring_hom f] {x : α}
  (hfx : irreducible (f x)) : irreducible x :=
⟨λ h, hfx.not_unit $ is_unit.map f.to_monoid_hom h, λ p q hx, let ⟨H⟩ := h in
or.imp (H p) (H q) $ hfx.is_unit_or_is_unit $ f.map_mul p q ▸ congr_arg f hx⟩

section
open local_ring
variables [comm_ring α] [local_ring α] [comm_ring β] [local_ring β]
variables (f : α →+* β) [is_local_ring_hom f]

lemma map_nonunit (a) (h : a ∈ maximal_ideal α) : f a ∈ maximal_ideal β :=
λ H, h $ is_unit_of_map_unit f a H

end

namespace local_ring
variables [comm_ring α] [local_ring α] [comm_ring β] [local_ring β]

variable (α)
/-- The residue field of a local ring is the quotient of the ring by its maximal ideal. -/
def residue_field := (maximal_ideal α).quotient

noncomputable instance residue_field.field : field (residue_field α) :=
ideal.quotient.field (maximal_ideal α)

noncomputable instance : inhabited (residue_field α) := ⟨37⟩

/-- The quotient map from a local ring to its residue field. -/
def residue : α →+* (residue_field α) :=
ideal.quotient.mk _

namespace residue_field

variables {α β}
/-- The map on residue fields induced by a local homomorphism between local rings -/
noncomputable def map (f : α →+* β) [is_local_ring_hom f] :
  residue_field α →+* residue_field β :=
ideal.quotient.lift (maximal_ideal α) ((ideal.quotient.mk _).comp f) $
λ a ha,
begin
  erw ideal.quotient.eq_zero_iff_mem,
  exact map_nonunit f a ha
end

end residue_field

end local_ring

namespace field
variables [field α]

open_locale classical

@[priority 100] -- see Note [lower instance priority]
instance : local_ring α :=
{ is_local := λ a,
  if h : a = 0
  then or.inr (by rw [h, sub_zero]; exact is_unit_one)
  else or.inl $ is_unit.mk0 a h }

end field
