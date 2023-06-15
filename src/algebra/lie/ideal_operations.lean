/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.lie.submodule

/-!
# Ideal operations for Lie algebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Given a Lie module `M` over a Lie algebra `L`, there is a natural action of the Lie ideals of `L`
on the Lie submodules of `M`. In the special case that `M = L` with the adjoint action, this
provides a pairing of Lie ideals which is especially important. For example, it can be used to
define solvability / nilpotency of a Lie algebra via the derived / lower-central series.

## Main definitions

  * `lie_submodule.has_bracket`
  * `lie_submodule.lie_ideal_oper_eq_linear_span`
  * `lie_ideal.map_bracket_le`
  * `lie_ideal.comap_bracket_le`

## Notation

Given a Lie module `M` over a Lie algebra `L`, together with a Lie submodule `N ⊆ M` and a Lie
ideal `I ⊆ L`, we introduce the notation `⁅I, N⁆` for the Lie submodule of `M` corresponding to
the action defined in this file.

## Tags

lie algebra, ideal operation
-/

universes u v w w₁ w₂

namespace lie_submodule

variables {R : Type u} {L : Type v} {M : Type w} {M₂ : Type w₁}
variables [comm_ring R] [lie_ring L] [lie_algebra R L]
variables [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M]
variables [add_comm_group M₂] [module R M₂] [lie_ring_module L M₂] [lie_module R L M₂]
variables (N N' : lie_submodule R L M) (I J : lie_ideal R L) (N₂ : lie_submodule R L M₂)

section lie_ideal_operations

/-- Given a Lie module `M` over a Lie algebra `L`, the set of Lie ideals of `L` acts on the set
of submodules of `M`. -/
instance has_bracket : has_bracket (lie_ideal R L) (lie_submodule R L M) :=
⟨λ I N, lie_span R L { m | ∃ (x : I) (n : N), ⁅(x : L), (n : M)⁆ = m }⟩

lemma lie_ideal_oper_eq_span :
  ⁅I, N⁆ = lie_span R L { m | ∃ (x : I) (n : N), ⁅(x : L), (n : M)⁆ = m } := rfl

/-- See also `lie_submodule.lie_ideal_oper_eq_linear_span'` and
`lie_submodule.lie_ideal_oper_eq_tensor_map_range`. -/
lemma lie_ideal_oper_eq_linear_span :
  (↑⁅I, N⁆ : submodule R M) = submodule.span R { m | ∃ (x : I) (n : N), ⁅(x : L), (n : M)⁆ = m } :=
begin
  apply le_antisymm,
  { let s := {m : M | ∃ (x : ↥I) (n : ↥N), ⁅(x : L), (n : M)⁆ = m},
    have aux : ∀ (y : L) (m' ∈ submodule.span R s), ⁅y, m'⁆ ∈ submodule.span R s,
    { intros y m' hm', apply submodule.span_induction hm',
      { rintros m'' ⟨x, n, hm''⟩, rw [← hm'', leibniz_lie],
        refine submodule.add_mem _ _ _; apply submodule.subset_span,
        { use [⟨⁅y, ↑x⁆, I.lie_mem x.property⟩, n], refl, },
        { use [x, ⟨⁅y, ↑n⁆, N.lie_mem n.property⟩], refl, }, },
      { simp only [lie_zero, submodule.zero_mem], },
      { intros m₁ m₂ hm₁ hm₂, rw lie_add, exact submodule.add_mem _ hm₁ hm₂, },
      { intros t m'' hm'', rw lie_smul, exact submodule.smul_mem _ t hm'', }, },
    change _ ≤ ↑({ lie_mem := aux, ..submodule.span R s } : lie_submodule R L M),
    rw [coe_submodule_le_coe_submodule, lie_ideal_oper_eq_span, lie_span_le],
    exact submodule.subset_span, },
  { rw lie_ideal_oper_eq_span, apply submodule_span_le_lie_span, },
end

lemma lie_ideal_oper_eq_linear_span' :
  (↑⁅I, N⁆ : submodule R M) = submodule.span R { m | ∃ (x ∈ I) (n ∈ N), ⁅x, n⁆ = m } :=
begin
  rw lie_ideal_oper_eq_linear_span,
  congr,
  ext m,
  split,
  { rintros ⟨⟨x, hx⟩, ⟨n, hn⟩, rfl⟩,
    exact ⟨x, hx, n, hn, rfl⟩, },
  { rintros ⟨x, hx, n, hn, rfl⟩,
    exact ⟨⟨x, hx⟩, ⟨n, hn⟩, rfl⟩, },
end

lemma lie_le_iff : ⁅I, N⁆ ≤ N' ↔ ∀ (x ∈ I) (m ∈ N), ⁅x, m⁆ ∈ N' :=
begin
  rw [lie_ideal_oper_eq_span, lie_submodule.lie_span_le],
  refine ⟨λ h x hx m hm, h ⟨⟨x, hx⟩, ⟨m, hm⟩, rfl⟩, _⟩,
  rintros h _ ⟨⟨x, hx⟩, ⟨m, hm⟩, rfl⟩,
  exact h x hx m hm,
end

lemma lie_coe_mem_lie (x : I) (m : N) : ⁅(x : L), (m : M)⁆ ∈ ⁅I, N⁆ :=
by { rw lie_ideal_oper_eq_span, apply subset_lie_span, use [x, m], }

lemma lie_mem_lie {x : L} {m : M} (hx : x ∈ I) (hm : m ∈ N) : ⁅x, m⁆ ∈ ⁅I, N⁆ :=
N.lie_coe_mem_lie I ⟨x, hx⟩ ⟨m, hm⟩

lemma lie_comm : ⁅I, J⁆ = ⁅J, I⁆ :=
begin
  suffices : ∀ (I J : lie_ideal R L), ⁅I, J⁆ ≤ ⁅J, I⁆, { exact le_antisymm (this I J) (this J I), },
  clear I J, intros I J,
  rw [lie_ideal_oper_eq_span, lie_span_le], rintros x ⟨y, z, h⟩, rw ← h,
  rw [← lie_skew, ← lie_neg, ← lie_submodule.coe_neg],
  apply lie_coe_mem_lie,
end

lemma lie_le_right : ⁅I, N⁆ ≤ N :=
begin
  rw [lie_ideal_oper_eq_span, lie_span_le], rintros m ⟨x, n, hn⟩, rw ← hn,
  exact N.lie_mem n.property,
end

lemma lie_le_left : ⁅I, J⁆ ≤ I :=
by { rw lie_comm, exact lie_le_right I J, }

lemma lie_le_inf : ⁅I, J⁆ ≤ I ⊓ J :=
by { rw le_inf_iff, exact ⟨lie_le_left I J, lie_le_right J I⟩, }

@[simp] lemma lie_bot : ⁅I, (⊥ : lie_submodule R L M)⁆ = ⊥ :=
by { rw eq_bot_iff, apply lie_le_right, }

@[simp] lemma bot_lie : ⁅(⊥ : lie_ideal R L), N⁆ = ⊥ :=
begin
  suffices : ⁅(⊥ : lie_ideal R L), N⁆ ≤ ⊥, { exact le_bot_iff.mp this, },
  rw [lie_ideal_oper_eq_span, lie_span_le], rintros m ⟨⟨x, hx⟩, n, hn⟩, rw ← hn,
  change x ∈ (⊥ : lie_ideal R L) at hx, rw mem_bot at hx, simp [hx],
end

lemma lie_eq_bot_iff : ⁅I, N⁆ = ⊥ ↔ ∀ (x ∈ I) (m ∈ N), ⁅(x : L), m⁆ = 0 :=
begin
  rw [lie_ideal_oper_eq_span, lie_submodule.lie_span_eq_bot_iff],
  refine ⟨λ h x hx m hm, h ⁅x, m⁆ ⟨⟨x, hx⟩, ⟨m, hm⟩, rfl⟩, _⟩,
  rintros h - ⟨⟨x, hx⟩, ⟨⟨n, hn⟩, rfl⟩⟩,
  exact h x hx n hn,
end

lemma mono_lie (h₁ : I ≤ J) (h₂ : N ≤ N') : ⁅I, N⁆ ≤ ⁅J, N'⁆ :=
begin
  intros m h,
  rw [lie_ideal_oper_eq_span, mem_lie_span] at h, rw [lie_ideal_oper_eq_span, mem_lie_span],
  intros N hN, apply h, rintros m' ⟨⟨x, hx⟩, ⟨n, hn⟩, hm⟩, rw ← hm, apply hN,
  use [⟨x, h₁ hx⟩, ⟨n, h₂ hn⟩], refl,
end

lemma mono_lie_left (h : I ≤ J) : ⁅I, N⁆ ≤ ⁅J, N⁆ := mono_lie _ _ _ _ h (le_refl N)

lemma mono_lie_right (h : N ≤ N') : ⁅I, N⁆ ≤ ⁅I, N'⁆ := mono_lie _ _ _ _ (le_refl I) h

@[simp] lemma lie_sup : ⁅I, N ⊔ N'⁆ = ⁅I, N⁆ ⊔ ⁅I, N'⁆ :=
begin
  have h : ⁅I, N⁆ ⊔ ⁅I, N'⁆ ≤ ⁅I, N ⊔ N'⁆,
  { rw sup_le_iff, split; apply mono_lie_right; [exact le_sup_left, exact le_sup_right], },
  suffices : ⁅I, N ⊔ N'⁆ ≤ ⁅I, N⁆ ⊔ ⁅I, N'⁆, { exact le_antisymm this h, }, clear h,
  rw [lie_ideal_oper_eq_span, lie_span_le], rintros m ⟨x, ⟨n, hn⟩, h⟩, erw lie_submodule.mem_sup,
  erw lie_submodule.mem_sup at hn, rcases hn with ⟨n₁, hn₁, n₂, hn₂, hn'⟩,
  use ⁅(x : L), (⟨n₁, hn₁⟩ : N)⁆, split, { apply lie_coe_mem_lie, },
  use ⁅(x : L), (⟨n₂, hn₂⟩ : N')⁆, split, { apply lie_coe_mem_lie, },
  simp [← h, ← hn'],
end

@[simp] lemma sup_lie : ⁅I ⊔ J, N⁆ = ⁅I, N⁆ ⊔ ⁅J, N⁆ :=
begin
  have h : ⁅I, N⁆ ⊔ ⁅J, N⁆ ≤ ⁅I ⊔ J, N⁆,
  { rw sup_le_iff, split; apply mono_lie_left; [exact le_sup_left, exact le_sup_right], },
  suffices : ⁅I ⊔ J, N⁆ ≤ ⁅I, N⁆ ⊔ ⁅J, N⁆, { exact le_antisymm this h, }, clear h,
  rw [lie_ideal_oper_eq_span, lie_span_le], rintros m ⟨⟨x, hx⟩, n, h⟩, erw lie_submodule.mem_sup,
  erw lie_submodule.mem_sup at hx, rcases hx with ⟨x₁, hx₁, x₂, hx₂, hx'⟩,
  use ⁅((⟨x₁, hx₁⟩ : I) : L), (n : N)⁆, split, { apply lie_coe_mem_lie, },
  use ⁅((⟨x₂, hx₂⟩ : J) : L), (n : N)⁆, split, { apply lie_coe_mem_lie, },
  simp [← h, ← hx'],
end

@[simp] lemma lie_inf : ⁅I, N ⊓ N'⁆ ≤ ⁅I, N⁆ ⊓ ⁅I, N'⁆ :=
by { rw le_inf_iff, split; apply mono_lie_right; [exact inf_le_left, exact inf_le_right], }

@[simp] lemma inf_lie : ⁅I ⊓ J, N⁆ ≤ ⁅I, N⁆ ⊓ ⁅J, N⁆ :=
by { rw le_inf_iff, split; apply mono_lie_left; [exact inf_le_left, exact inf_le_right], }

variables (f : M →ₗ⁅R,L⁆ M₂)

lemma map_bracket_eq : map f ⁅I, N⁆ = ⁅I, map f N⁆ :=
begin
  rw [← coe_to_submodule_eq_iff, coe_submodule_map, lie_ideal_oper_eq_linear_span,
    lie_ideal_oper_eq_linear_span, submodule.map_span],
  congr,
  ext m,
  split,
  { rintros ⟨-, ⟨⟨x, ⟨n, hn⟩, rfl⟩, hm⟩⟩,
    simp only [lie_module_hom.coe_to_linear_map, lie_module_hom.map_lie] at hm,
    exact ⟨x, ⟨f n, (mem_map (f n)).mpr ⟨n, hn, rfl⟩⟩, hm⟩, },
  { rintros ⟨x, ⟨m₂, hm₂ : m₂ ∈ map f N⟩, rfl⟩,
    obtain ⟨n, hn, rfl⟩ := (mem_map m₂).mp hm₂,
    exact ⟨⁅x, n⁆, ⟨x, ⟨n, hn⟩, rfl⟩, by simp⟩, },
end

lemma map_comap_le : map f (comap f N₂) ≤ N₂ :=
(N₂ : set M₂).image_preimage_subset f

lemma map_comap_eq (hf : N₂ ≤ f.range) : map f (comap f N₂) = N₂ :=
begin
  rw set_like.ext'_iff,
  exact set.image_preimage_eq_of_subset hf,
end

lemma le_comap_map : N ≤ comap f (map f N) :=
(N : set M).subset_preimage_image f

lemma comap_map_eq (hf : f.ker = ⊥) : comap f (map f N) = N :=
begin
  rw set_like.ext'_iff,
  exact (N : set M).preimage_image_eq (f.ker_eq_bot.mp hf),
end

lemma comap_bracket_eq (hf₁ : f.ker = ⊥) (hf₂ : N₂ ≤ f.range) :
  comap f ⁅I, N₂⁆ = ⁅I, comap f N₂⁆ :=
begin
  conv_lhs { rw ← map_comap_eq N₂ f hf₂, },
  rw [← map_bracket_eq, comap_map_eq _ f hf₁],
end

@[simp] lemma map_comap_incl : map N.incl (comap N.incl N') = N ⊓ N' :=
begin
  rw ← coe_to_submodule_eq_iff,
  exact (N : submodule R M).map_comap_subtype N',
end

end lie_ideal_operations

end lie_submodule

namespace lie_ideal

open lie_algebra

variables {R : Type u} {L : Type v} {L' : Type w₂}
variables [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L']
variables (f : L →ₗ⁅R⁆ L') (I : lie_ideal R L) (J : lie_ideal R L')

/-- Note that the inequality can be strict; e.g., the inclusion of an Abelian subalgebra of a
simple algebra. -/
lemma map_bracket_le {I₁ I₂ : lie_ideal R L} : map f ⁅I₁, I₂⁆ ≤ ⁅map f I₁, map f I₂⁆ :=
begin
  rw map_le_iff_le_comap, erw lie_submodule.lie_span_le,
  intros x hx, obtain ⟨⟨y₁, hy₁⟩, ⟨y₂, hy₂⟩, hx⟩ := hx, rw ← hx,
  let fy₁ : ↥(map f I₁) := ⟨f y₁, mem_map hy₁⟩,
  let fy₂ : ↥(map f I₂) := ⟨f y₂, mem_map hy₂⟩,
  change _ ∈ comap f ⁅map f I₁, map f I₂⁆,
  simp only [submodule.coe_mk, mem_comap, lie_hom.map_lie],
  exact lie_submodule.lie_coe_mem_lie _ _ fy₁ fy₂,
end

lemma map_bracket_eq {I₁ I₂ : lie_ideal R L} (h : function.surjective f) :
  map f ⁅I₁, I₂⁆ = ⁅map f I₁, map f I₂⁆ :=
begin
  suffices : ⁅map f I₁, map f I₂⁆ ≤ map f ⁅I₁, I₂⁆, { exact le_antisymm (map_bracket_le f) this, },
  rw [← lie_submodule.coe_submodule_le_coe_submodule, coe_map_of_surjective h,
    lie_submodule.lie_ideal_oper_eq_linear_span,
    lie_submodule.lie_ideal_oper_eq_linear_span, linear_map.map_span],
  apply submodule.span_mono,
  rintros x ⟨⟨z₁, h₁⟩, ⟨z₂, h₂⟩, rfl⟩,
  obtain ⟨y₁, rfl⟩ := mem_map_of_surjective h h₁,
  obtain ⟨y₂, rfl⟩ := mem_map_of_surjective h h₂,
  use [⁅(y₁ : L), (y₂ : L)⁆, y₁, y₂],
  apply f.map_lie,
end

lemma comap_bracket_le {J₁ J₂ : lie_ideal R L'} : ⁅comap f J₁, comap f J₂⁆ ≤ comap f ⁅J₁, J₂⁆ :=
begin
  rw ← map_le_iff_le_comap,
  exact le_trans (map_bracket_le f) (lie_submodule.mono_lie _ _ _ _ map_comap_le map_comap_le),
end

variables {f}

lemma map_comap_incl {I₁ I₂ : lie_ideal R L} : map I₁.incl (comap I₁.incl I₂) = I₁ ⊓ I₂ :=
by { conv_rhs { rw ← I₁.incl_ideal_range, }, rw ← map_comap_eq, exact I₁.incl_is_ideal_morphism, }

lemma comap_bracket_eq {J₁ J₂ : lie_ideal R L'} (h : f.is_ideal_morphism) :
  comap f ⁅f.ideal_range ⊓ J₁, f.ideal_range ⊓ J₂⁆ = ⁅comap f J₁, comap f J₂⁆ ⊔ f.ker :=
begin
  rw [← lie_submodule.coe_to_submodule_eq_iff, comap_coe_submodule,
    lie_submodule.sup_coe_to_submodule, f.ker_coe_submodule, ← submodule.comap_map_eq,
    lie_submodule.lie_ideal_oper_eq_linear_span, lie_submodule.lie_ideal_oper_eq_linear_span,
    linear_map.map_span],
  congr, simp only [lie_hom.coe_to_linear_map, set.mem_set_of_eq], ext y,
  split,
  { rintros ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩, hy⟩, rw ← hy,
    erw [lie_submodule.mem_inf, f.mem_ideal_range_iff h] at hx₁ hx₂,
    obtain ⟨⟨z₁, hz₁⟩, hz₁'⟩ := hx₁, rw ← hz₁ at hz₁',
    obtain ⟨⟨z₂, hz₂⟩, hz₂'⟩ := hx₂, rw ← hz₂ at hz₂',
    use [⁅z₁, z₂⁆, ⟨z₁, hz₁'⟩, ⟨z₂, hz₂'⟩, rfl],
    simp only [hz₁, hz₂, submodule.coe_mk, lie_hom.map_lie], },
  { rintros ⟨x, ⟨⟨z₁, hz₁⟩, ⟨z₂, hz₂⟩, hx⟩, hy⟩, rw [← hy, ← hx],
    have hz₁' : f z₁ ∈ f.ideal_range ⊓ J₁,
    { rw lie_submodule.mem_inf, exact ⟨f.mem_ideal_range, hz₁⟩, },
    have hz₂' : f z₂ ∈ f.ideal_range ⊓ J₂,
    { rw lie_submodule.mem_inf, exact ⟨f.mem_ideal_range, hz₂⟩, },
    use [⟨f z₁, hz₁'⟩, ⟨f z₂, hz₂'⟩], simp only [submodule.coe_mk, lie_hom.map_lie], },
end

lemma map_comap_bracket_eq {J₁ J₂ : lie_ideal R L'} (h : f.is_ideal_morphism) :
  map f ⁅comap f J₁, comap f J₂⁆ = ⁅f.ideal_range ⊓ J₁, f.ideal_range ⊓ J₂⁆ :=
by { rw [← map_sup_ker_eq_map, ← comap_bracket_eq h, map_comap_eq h, inf_eq_right],
     exact le_trans (lie_submodule.lie_le_left _ _) inf_le_left, }

lemma comap_bracket_incl {I₁ I₂ : lie_ideal R L} :
  ⁅comap I.incl I₁, comap I.incl I₂⁆ = comap I.incl ⁅I ⊓ I₁, I ⊓ I₂⁆ :=
begin
  conv_rhs { congr, skip, rw ← I.incl_ideal_range, }, rw comap_bracket_eq,
  simp only [ker_incl, sup_bot_eq], exact I.incl_is_ideal_morphism,
end

/-- This is a very useful result; it allows us to use the fact that inclusion distributes over the
Lie bracket operation on ideals, subject to the conditions shown. -/
lemma comap_bracket_incl_of_le {I₁ I₂ : lie_ideal R L} (h₁ : I₁ ≤ I) (h₂ : I₂ ≤ I) :
  ⁅comap I.incl I₁, comap I.incl I₂⁆ = comap I.incl ⁅I₁, I₂⁆ :=
by { rw comap_bracket_incl, rw ← inf_eq_right at h₁ h₂, rw [h₁, h₂], }

end lie_ideal
