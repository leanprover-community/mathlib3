/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import model_theory.elementary_maps

/-!
# Skolem Functions and Downward Löwenheim–Skolem

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main Definitions
* `first_order.language.skolem₁` is a language consisting of Skolem functions for another language.

## Main Results
* `first_order.language.exists_elementary_substructure_card_eq` is the Downward Löwenheim–Skolem
  theorem: If `s` is a set in an `L`-structure `M` and `κ` an infinite cardinal such that
  `max (# s, L.card) ≤ κ` and `κ ≤ # M`, then `M` has an elementary substructure containing `s` of
  cardinality `κ`.

## TODO
* Use `skolem₁` recursively to construct an actual Skolemization of a language.

-/

universes u v w w'

namespace first_order
namespace language
open Structure cardinal
open_locale cardinal

variables (L : language.{u v}) {M : Type w} [nonempty M] [L.Structure M]

/-- A language consisting of Skolem functions for another language.
Called `skolem₁` because it is the first step in building a Skolemization of a language. -/
@[simps] def skolem₁ : language := ⟨λ n, L.bounded_formula empty (n + 1), λ _, empty⟩

variables {L}

theorem card_functions_sum_skolem₁ :
  # (Σ n, (L.sum L.skolem₁).functions n) = # (Σ n, L.bounded_formula empty (n + 1)) :=
begin
  simp only [card_functions_sum, skolem₁_functions, lift_id', mk_sigma, sum_add_distrib'],
  rw [add_comm, add_eq_max, max_eq_left],
  { refine sum_le_sum _ _ (λ n, _),
    rw [← lift_le, lift_lift, lift_mk_le],
    refine ⟨⟨λ f, (func f default).bd_equal (func f default), λ f g h, _⟩⟩,
    rcases h with ⟨rfl, ⟨rfl⟩⟩,
    refl },
  { rw ← mk_sigma,
    exact infinite_iff.1 (infinite.of_injective (λ n, ⟨n, ⊥⟩) (λ x y xy, (sigma.mk.inj xy).1)) }
end

theorem card_functions_sum_skolem₁_le :
  # (Σ n, (L.sum L.skolem₁).functions n) ≤ max ℵ₀ L.card :=
begin
  rw card_functions_sum_skolem₁,
  transitivity # (Σ n, L.bounded_formula empty n),
  { exact ⟨⟨sigma.map nat.succ (λ _, id), nat.succ_injective.sigma_map
    (λ _, function.injective_id)⟩⟩ },
  { refine trans bounded_formula.card_le (lift_le.1 _),
    simp only [mk_empty, lift_zero, lift_uzero, zero_add] }
end

/-- The structure assigning each function symbol of `L.skolem₁` to a skolem function generated with
choice. -/
noncomputable instance skolem₁_Structure : L.skolem₁.Structure M :=
⟨λ n φ x, classical.epsilon (λ a, φ.realize default (fin.snoc x a : _ → M)), λ _ r, empty.elim r⟩

namespace substructure

lemma skolem₁_reduct_is_elementary (S : (L.sum L.skolem₁).substructure M) :
  (Lhom.sum_inl.substructure_reduct S).is_elementary :=
begin
  apply (Lhom.sum_inl.substructure_reduct S).is_elementary_of_exists,
  intros n φ x a h,
  let φ' : (L.sum L.skolem₁).functions n := (Lhom.sum_inr.on_function φ),
  exact ⟨⟨fun_map φ' (coe ∘ x), S.fun_mem (Lhom.sum_inr.on_function φ) (coe ∘ x) (λ i, (x i).2)⟩,
    classical.epsilon_spec ⟨a, h⟩⟩,
end

/-- Any `L.sum L.skolem₁`-substructure is an elementary `L`-substructure. -/
noncomputable def elementary_skolem₁_reduct (S : (L.sum L.skolem₁).substructure M) :
  L.elementary_substructure M :=
⟨Lhom.sum_inl.substructure_reduct S, S.skolem₁_reduct_is_elementary⟩

lemma coe_sort_elementary_skolem₁_reduct
  (S : (L.sum L.skolem₁).substructure M) :
  (S.elementary_skolem₁_reduct : Type w) = S :=
rfl

end substructure

open substructure

variables (L) (M)

instance : small (⊥ : (L.sum L.skolem₁).substructure M).elementary_skolem₁_reduct :=
begin
  rw [coe_sort_elementary_skolem₁_reduct],
  apply_instance,
end

theorem exists_small_elementary_substructure :
  ∃ (S : L.elementary_substructure M), small.{max u v} S :=
⟨substructure.elementary_skolem₁_reduct ⊥, infer_instance⟩

variables {M}

/-- The Downward Löwenheim–Skolem theorem :
  If `s` is a set in an `L`-structure `M` and `κ` an infinite cardinal such that
  `max (# s, L.card) ≤ κ` and `κ ≤ # M`, then `M` has an elementary substructure containing `s` of
  cardinality `κ`.  -/
theorem exists_elementary_substructure_card_eq (s : set M) (κ : cardinal.{w'})
  (h1 : ℵ₀ ≤ κ)
  (h2 : cardinal.lift.{w'} (# s) ≤ cardinal.lift.{w} κ)
  (h3 : cardinal.lift.{w'} L.card ≤ cardinal.lift.{max u v} κ)
  (h4 : cardinal.lift.{w} κ ≤ cardinal.lift.{w'} (# M)) :
  ∃ (S : L.elementary_substructure M), s ⊆ S ∧
    cardinal.lift.{w'} (# S) = cardinal.lift.{w} κ :=
begin
  obtain ⟨s', hs'⟩ := cardinal.le_mk_iff_exists_set.1 h4,
  rw ← aleph_0_le_lift at h1,
  rw ← hs' at *,
  refine ⟨elementary_skolem₁_reduct (closure (L.sum L.skolem₁)
    (s ∪ (equiv.ulift '' s'))),
    (s.subset_union_left _).trans subset_closure, _⟩,
  have h := mk_image_eq_lift _ s' equiv.ulift.injective,
  rw [lift_umax, lift_id'] at h,
  rw [coe_sort_elementary_skolem₁_reduct, ← h, lift_inj],
  refine le_antisymm (lift_le.1 (lift_card_closure_le.trans _))
    (mk_le_mk_of_subset ((set.subset_union_right _ _).trans subset_closure)),
  rw [max_le_iff, aleph_0_le_lift, ← aleph_0_le_lift, h, add_eq_max, max_le_iff, lift_le],
  refine ⟨h1, (mk_union_le _ _).trans _, (lift_le.2 card_functions_sum_skolem₁_le).trans _⟩,
  { rw [← lift_le, lift_add, h, add_comm, add_eq_max h1],
    exact max_le le_rfl h2 },
  { rw [lift_max, lift_aleph_0, max_le_iff, aleph_0_le_lift, and_comm,
      ← lift_le.{_ w'}, lift_lift, lift_lift, ← aleph_0_le_lift, h],
    refine ⟨_, h1⟩,
    simp only [← lift_lift, lift_umax, lift_umax'],
    rw [lift_lift, ← lift_lift.{w' w} L.card],
    refine trans ((lift_le.{_ w}).2 h3) _,
    rw [lift_lift, ← lift_lift.{w (max u v)}, ← hs', ← h, lift_lift, lift_lift, lift_lift] },
  { refine trans _ (lift_le.2 (mk_le_mk_of_subset (set.subset_union_right _ _))),
    rw [aleph_0_le_lift, ← aleph_0_le_lift, h],
    exact h1 }
end

end language
end first_order
