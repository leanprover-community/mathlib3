/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import model_theory.elementary_maps

/-!
# Skolem Functions and Downward Löwenheim–Skolem

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

universes u v w

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
  simp only [card_functions_sum, skolem₁_functions, mk_sum, lift_id'],
  rw [add_comm, add_eq_max, max_eq_left],
  { rw [← lift_le, lift_lift, lift_mk_le],
    refine ⟨⟨sigma.map id (λ _ f, (func f default).bd_equal (func f default)),
      function.injective_id.sigma_map (λ a f g h, _)⟩⟩,
    simp only [sigma.map, sigma.ext_iff, id.def, pi.default_def] at h,
    rcases h with ⟨rfl, ⟨rfl⟩⟩,
    refl },
  { exact infinite_iff.1 (infinite.of_injective (λ n, ⟨n, ⊥⟩) (λ x y xy, (sigma.mk.inj xy).1)) }
end

theorem card_functions_sum_skolem₁_le :
  # (Σ n, (L.sum L.skolem₁).functions n) ≤ max ω L.card :=
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
⟨Lhom.sum_inl.substructure_reduct S, λ _, S.skolem₁_reduct_is_elementary⟩

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

variables {L M}

/-- The Downward Löwenheim–Skolem theorem :
  If `s` is a set in an `L`-structure `M` and `κ` an infinite cardinal such that
  `max (# s, L.card) ≤ κ` and `κ ≤ # M`, then `M` has an elementary substructure containing `s` of
  cardinality `κ`.  -/
theorem exists_elementary_substructure_card_eq (s : set M) (κ : cardinal.{max u v w})
  (h1 : ω ≤ κ)
  (h2 : cardinal.lift.{max u v} (# s) ≤ κ)
  (h3 : cardinal.lift.{w} L.card ≤ κ)
  (h4 : κ ≤ cardinal.lift.{max u v} (# M)) :
  ∃ (S : L.elementary_substructure M), s ⊆ S ∧ cardinal.lift.{max u v} (# S) = κ :=
begin
  obtain ⟨s', rfl⟩ := cardinal.le_mk_iff_exists_set.1 h4,
  refine ⟨elementary_skolem₁_reduct (closure (L.sum L.skolem₁)
    (s ∪ (equiv.ulift.{(max u v) w} '' s'))),
    (s.subset_union_left _).trans subset_closure, _⟩,
  rw [coe_sort_elementary_skolem₁_reduct],
  refine le_antisymm (lift_le.1 _) _,
  { rw lift_lift,
    refine lift_card_closure_le.trans _,
    rw max_le_iff at *,
    rw [← lift_le, lift_lift, lift_le, add_comm, add_eq_max, max_le_iff, lift_id'],
    { refine ⟨h1, _, _⟩,
      { refine (lift_le.2 card_functions_sum_skolem₁_le).trans _,
        rw [lift_max', lift_omega, max_le_iff, ← lift_lift, lift_id],
        exact ⟨h1, h3⟩, },
      { refine ((lift_le.2 (mk_union_le _ _)).trans _),
        rw [lift_add, add_comm, mk_image_eq_lift _ _ equiv.ulift.injective, ← lift_lift, lift_id',
          add_eq_max h1, lift_id', max_eq_left h2] } },
    { rw [← lift_lift, lift_id, ← lift_omega, lift_le, ← infinite_iff],
      exact infinite.of_injective (λ n, ⟨n, sum.inr bounded_formula.falsum⟩)
        (λ x y xy, (sigma.ext_iff.1 xy).1) } },
  { rw [← lift_le, lift_lift, ← mk_image_eq_lift _ s' equiv.ulift.injective, lift_mk_le],
    exact ⟨⟨set.inclusion ((set.subset_union_right _ _).trans subset_closure),
      set.inclusion_injective _⟩⟩ },
end

end language
end first_order
