/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

Definition and basic properties of finite dimensional vector spaces.

The class `finite_dimensional` is defined to be `is_noetherian`, for ease of transfer of proofs.
However an additional constructor `finite_dimensional.of_fg` is provided to prove
finite dimensionality in a conventional manner.

Also defined is `findim`, the dimension of a finite dimensional space, returning a `nat`,
as opposed to `dim`, which returns a `cardinal`,
-/

import ring_theory.noetherian linear_algebra.dimension
import ring_theory.principal_ideal_domain

universes u v w

open vector_space cardinal submodule module function

variables {K : Type u} {V : Type v} [discrete_field K] [add_comm_group V] [vector_space K V]

/-- `finite_dimensional` vector spaces are defined to be noetherian modules.
  Use `finite_dimensional.of_fg` to prove finite dimensional from a conventional
  definition. -/
@[reducible] def finite_dimensional (K V : Type*) [discrete_field K]
  [add_comm_group V] [vector_space K V] := is_noetherian K V

namespace finite_dimensional

open is_noetherian

lemma finite_dimensional_iff_dim_lt_omega : finite_dimensional K V ↔ dim K V < omega.{v} :=
begin
  cases exists_is_basis K V with b hb,
  have := is_basis.mk_eq_dim hb,
  simp only [lift_id] at this,
  rw [← this, lt_omega_iff_fintype, ← @set.set_of_mem_eq _ b, ← subtype.val_range],
  split,
  { intro, resetI, convert finite_of_linear_independent hb.1, simp },
  { assume hbfinite,
    refine @is_noetherian_of_linear_equiv K (⊤ : submodule K V) V _
      _ _ _ _ (linear_equiv.of_top _ rfl) (id _),
    refine is_noetherian_of_fg_of_noetherian _ ⟨set.finite.to_finset hbfinite, _⟩,
    rw [set.finite.coe_to_finset, ← hb.2], refl }
end

lemma dim_lt_omega (K V : Type*) [discrete_field K] [add_comm_group V] [vector_space K V] :
  ∀ [finite_dimensional K V], dim K V < omega.{v} :=
finite_dimensional_iff_dim_lt_omega.1

set_option pp.universes true

lemma of_fg (hfg : (⊤ : submodule K V).fg) : finite_dimensional K V :=
let ⟨s, hs⟩ := hfg in
begin
  rw [finite_dimensional_iff_dim_lt_omega, ← dim_top, ← hs],
  exact lt_of_le_of_lt (dim_span_le _) (lt_omega_iff_finite.2 (set.finite_mem_finset s))
end

lemma exists_is_basis_finite (K V : Type*) [discrete_field K]
  [add_comm_group V] [vector_space K V] [finite_dimensional K V] :
  ∃ s : set V, (is_basis K (subtype.val : s → V)) ∧ s.finite :=
begin
  cases exists_is_basis K V with s hs,
  exact ⟨s, hs, finite_of_linear_independent hs.1⟩
end

instance [finite_dimensional K V] (S : submodule K V) : finite_dimensional K S :=
finite_dimensional_iff_dim_lt_omega.2 (lt_of_le_of_lt (dim_submodule_le _) (dim_lt_omega K V))

noncomputable def findim (K V : Type*) [discrete_field K]
  [add_comm_group V] [vector_space K V] [finite_dimensional K V] : ℕ :=
classical.some (lt_omega.1 (dim_lt_omega K V))

lemma findim_eq_dim (K : Type u) (V : Type v) [discrete_field K]
  [add_comm_group V] [vector_space K V] [finite_dimensional K V] :
  (findim K V : cardinal.{v}) = dim K V :=
(classical.some_spec (lt_omega.1 (dim_lt_omega K V))).symm

lemma card_eq_findim [finite_dimensional K V] {s : set V} {hfs : fintype s}
  (hs : is_basis K (λ x : s, x.val)) : fintype.card s = findim K V :=
by rw [← nat_cast_inj.{v}, findim_eq_dim, ← fintype_card, ← lift_inj, ← hs.mk_eq_dim]

lemma eq_top_of_findim_eq [finite_dimensional K V] {S : submodule K V}
  (h : findim K S = findim K V) : S = ⊤ :=
begin
  cases exists_is_basis K S with bS hbS,
  have : linear_independent K (subtype.val : (subtype.val '' bS : set V) → V),
    from @linear_independent.image_subtype _ _ _ _ _ _ _ _ _
      (submodule.subtype S) hbS.1 (by simp),
  cases exists_subset_is_basis this with b hb,
  letI : fintype b := classical.choice (finite_of_linear_independent hb.2.1),
  letI : fintype (subtype.val '' bS) := classical.choice (finite_of_linear_independent this),
  letI : fintype bS := classical.choice (finite_of_linear_independent hbS.1),
  have : subtype.val '' bS = b, from set.eq_of_subset_of_card_le hb.1
    (by rw [set.card_image_of_injective _ subtype.val_injective, card_eq_findim hbS,
         card_eq_findim hb.2, h]),
  erw [← hb.2.2, subtype.val_range, ← this, set.set_of_mem_eq, ← subtype_eq_val, span_image],
  have := hbS.2,
  erw [subtype.val_range, set.set_of_mem_eq] at this,
  rw [this, map_top (submodule.subtype S), range_subtype],
end

end finite_dimensional

namespace linear_map

open finite_dimensional

lemma surjective_of_injective [finite_dimensional K V] {f : V →ₗ[K] V}
  (hinj : injective f) : surjective f :=
begin
  have h := dim_eq_injective _ hinj,
  rw [← findim_eq_dim, ← findim_eq_dim, nat_cast_inj] at h,
  exact range_eq_top.1 (eq_top_of_findim_eq h.symm)
end

lemma injective_iff_surjective [finite_dimensional K V] {f : V →ₗ[K] V} :
  injective f ↔ surjective f :=
by classical; exact
⟨surjective_of_injective,
  λ hsurj, let ⟨g, hg⟩ := exists_right_inverse_linear_map_of_surjective
    (range_eq_top.2 hsurj) in
  have function.right_inverse g f,
    from λ x, show (linear_map.comp f g) x = (@linear_map.id K V _ _ _ : V → V) x, by rw hg,
  injective_of_has_left_inverse ⟨g, left_inverse_of_surjective_of_right_inverse
    (surjective_of_injective (injective_of_has_left_inverse ⟨_, this⟩))
      this⟩⟩

lemma ker_eq_bot_iff_range_eq_top [finite_dimensional K V] {f : V →ₗ[K] V} :
  f.ker = ⊥ ↔ f.range = ⊤ :=
by rw [range_eq_top, ker_eq_bot, injective_iff_surjective]

lemma mul_eq_one_of_mul_eq_one [finite_dimensional K V] {f g : V →ₗ[K] V} (hfg : f * g = 1) :
  g * f = 1 :=
by classical; exact
have ginj : injective g, from injective_of_has_left_inverse
  ⟨f, λ x, show (f * g) x = (1 : V →ₗ[K] V) x, by rw hfg; refl⟩,
let ⟨i, hi⟩ := exists_right_inverse_linear_map_of_surjective
  (range_eq_top.2 (injective_iff_surjective.1 ginj)) in
have f * (g * i) = f * 1, from congr_arg _ hi,
by rw [← mul_assoc, hfg, one_mul, mul_one] at this; rwa ← this

lemma mul_eq_one_comm [finite_dimensional K V] {f g : V →ₗ[K] V} : f * g = 1 ↔ g * f = 1 :=
⟨mul_eq_one_of_mul_eq_one, mul_eq_one_of_mul_eq_one⟩

end linear_map
