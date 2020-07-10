/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import ring_theory.algebra_tower
import linear_algebra.finite_dimensional

/-! # Tower of field extensions
Tower law for arbitrary extensions and finite extensions. -/

universes u v w u₁ v₁ w₁
open_locale classical big_operators

section semiring

variables {R : Type u} {S : Type v} {A : Type w}
variables [comm_semiring R] [comm_semiring S] [semiring A]
variables [algebra R S] [algebra S A] [algebra R A] [is_algebra_tower R S A]

namespace submodule

open is_algebra_tower

theorem smul_mem_span_smul_of_mem {s : set S} {t : set A} {k : S} (hks : k ∈ span R s)
  {x : A} (hx : x ∈ t) : k • x ∈ span R (s • t) :=
span_induction hks (λ c hc, subset_span $ set.mem_smul.2 ⟨c, x, hc, hx, rfl⟩)
  (by { rw zero_smul, exact zero_mem _ })
  (λ c₁ c₂ ih₁ ih₂, by { rw add_smul, exact add_mem _ ih₁ ih₂ })
  (λ b c hc, by { rw is_algebra_tower.smul_assoc, exact smul_mem _ _ hc })

theorem smul_mem_span_smul {s : set S} (hs : span R s = ⊤) {t : set A} {k : S}
  {x : A} (hx : x ∈ span R t) :
  k • x ∈ span R (s • t) :=
span_induction hx (λ x hx, smul_mem_span_smul_of_mem (hs.symm ▸ mem_top) hx)
  (by { rw smul_zero, exact zero_mem _ })
  (λ x y ihx ihy, by { rw smul_add, exact add_mem _ ihx ihy })
  (λ c x hx, smul_left_comm c k x ▸ smul_mem _ _ hx)

theorem smul_mem_span_smul' {s : set S} (hs : span R s = ⊤) {t : set A} {k : S}
  {x : A} (hx : x ∈ span R (s • t)) :
  k • x ∈ span R (s • t) :=
span_induction hx (λ x hx, let ⟨p, q, hp, hq, hpq⟩ := set.mem_smul.1 hx in
    by { rw [← hpq, smul_smul], exact smul_mem_span_smul_of_mem (hs.symm ▸ mem_top) hq })
  (by { rw smul_zero, exact zero_mem _ })
  (λ x y ihx ihy, by { rw smul_add, exact add_mem _ ihx ihy })
  (λ c x hx, smul_left_comm c k x ▸ smul_mem _ _ hx)

theorem span_smul {s : set S} (hs : span R s = ⊤) (t : set A) :
  span R (s • t) = (span S t).restrict_scalars' R :=
le_antisymm (span_le.2 $ λ x hx, let ⟨p, q, hps, hqt, hpqx⟩ := set.mem_smul.1 hx in
  hpqx ▸ (span S t).smul_mem p (subset_span hqt)) $
λ p hp, span_induction hp (λ x hx, one_smul S x ▸ smul_mem_span_smul hs (subset_span hx))
  (zero_mem _)
  (λ _ _, add_mem _)
  (λ k x hx, smul_mem_span_smul' hs hx)

end submodule

end semiring

section ring

variables {R : Type u} {S : Type v} {A : Type w}
variables [comm_ring R] [comm_ring S] [ring A]
variables [algebra R S] [algebra S A] [algebra R A] [is_algebra_tower R S A]

theorem linear_independent_smul {ι : Type v₁} {b : ι → S} {κ : Type w₁} {c : κ → A}
  (hb : linear_independent R b) (hc : linear_independent S c) :
  linear_independent R (λ p : ι × κ, b p.1 • c p.2) :=
begin
  rw linear_independent_iff' at hb hc, rw linear_independent_iff'', rintros s g hg hsg ⟨i, k⟩ hik,
  have h1 : ∑ i in (s.image prod.fst).product (s.image prod.snd), g i • b i.1 • c i.2 = 0,
  { rw ← hsg, exact (finset.sum_subset finset.subset_product $ λ p _ hp,
      show g p • b p.1 • c p.2 = 0, by rw [hg p hp, zero_smul]).symm },
  rw [finset.sum_product, finset.sum_comm] at h1,
  simp_rw [← is_algebra_tower.smul_assoc, ← finset.sum_smul] at h1,
  exact hb _ _ (hc _ _ h1 k (finset.mem_image_of_mem _ hik)) i (finset.mem_image_of_mem _ hik),
end

theorem is_basis.smul {ι : Type v₁} {b : ι → S} {κ : Type w₁} {c : κ → A}
  (hb : is_basis R b) (hc : is_basis S c) : is_basis R (λ p : ι × κ, b p.1 • c p.2) :=
⟨linear_independent_smul hb.1 hc.1,
by rw [← set.range_smul_range, submodule.span_smul hb.2, ← submodule.restrict_scalars'_top R S A,
    submodule.restrict_scalars'_inj, hc.2]⟩

end ring

section field

open cardinal

variables (F : Type u) (K : Type v) (A : Type w)
variables [field F] [field K] [ring A]
variables [algebra F K] [algebra K A] [algebra F A] [is_algebra_tower F K A]

/-- Tower law. -/
theorem dim_mul_dim' :
  (cardinal.lift.{v w} (vector_space.dim F K) *
      cardinal.lift.{w v} (vector_space.dim K A) : cardinal.{max w v}) =
  cardinal.lift.{w v} (vector_space.dim F A) :=
let ⟨b, hb⟩ := exists_is_basis F K, ⟨c, hc⟩ := exists_is_basis K A in
by rw [← (vector_space.dim F K).lift_id, ← hb.mk_eq_dim,
    ← (vector_space.dim K A).lift_id, ← hc.mk_eq_dim,
    ← lift_umax.{w v}, ← (hb.smul hc).mk_eq_dim, mk_prod, lift_mul,
    lift_lift, lift_lift, lift_lift, lift_lift, lift_umax]

/-- Tower law. -/
theorem dim_mul_dim (F : Type u) (K A : Type v) [field F] [field K] [ring A]
  [algebra F K] [algebra K A] [algebra F A] [is_algebra_tower F K A] :
  vector_space.dim F K * vector_space.dim K A = vector_space.dim F A :=
by convert dim_mul_dim' F K A; rw lift_id

namespace finite_dimensional

theorem trans [finite_dimensional F K] [finite_dimensional K A] : finite_dimensional F A :=
let ⟨b, hb⟩ := finite_dimensional.exists_is_basis_finset F K in
let ⟨c, hc⟩ := finite_dimensional.exists_is_basis_finset K A in
finite_dimensional.of_finite_basis $ hb.smul hc

/-- Tower law. -/
theorem findim_mul_findim
  [finite_dimensional F K] [finite_dimensional K A] [finite_dimensional F A] :
  findim F K * findim K A = findim F A :=
let ⟨b, hb⟩ := finite_dimensional.exists_is_basis_finset F K in
let ⟨c, hc⟩ := finite_dimensional.exists_is_basis_finset K A in
by rw [findim_eq_card_basis hb, findim_eq_card_basis hc,
    findim_eq_card_basis (hb.smul hc), fintype.card_prod]

end finite_dimensional

end field
