import data.fintype.basic

/--
Given any `s : setoid α` on a `fintype α`,
there is an `equiv` between `α` and the sigma type with base `quotient s`,
and fiber over `q` given by `fin (fintype.card {x // ⟦x⟧ = q})`.

Moreover, this equivalence takes each term `x : α`
to a point in the fiber over its equivalence class.

See also `equiv.sigma_quotient_fin_card` for the nonconstructive version.
-/
def equiv.sigma_quotient_fin_card_trunc
  {α : Type*} [fa : fintype α] [decidable_eq α] (s : setoid α) [decidable_rel s.r] :
  trunc { e : α ≃ Σ (q : quotient s), fin (fintype.card {x // ⟦x⟧ = q}) // ∀ x, (e x).1 = ⟦x⟧ } :=
begin
  unfreezingI { rcases fa with ⟨⟨S, hS₁⟩, hS₂⟩, },
  refine quotient.rec_on_subsingleton S (λ l h₁ h₂, trunc.mk _) hS₁ hS₂, clear hS₂ hS₁ S,
  fsplit,
  { exact (equiv.sigma_preimage_equiv quotient.mk).symm.trans (equiv.sigma_congr_right (λ q,
    fintype.equiv_fin_of_forall_mem_list
      (λ ⟨x, px⟩, list.mem_pmap.2 ⟨x, list.mem_filter.2 ⟨h₂ _, px⟩, rfl⟩)
      (list.nodup_pmap (λ a _ b _, congr_arg subtype.val) (list.nodup_filter _ h₁)))), },
  { intro x, refl, }
end

open_locale classical

/--
Given any `s : setoid α` on a `fintype α`,
there is an `equiv` between `α` and the sigma type with base `quotient s`,
and fiber over `q` given by `fin (fintype.card {x // ⟦x⟧ = q})`.

See also `equiv.sigma_quotient_fin_card_trunc` for the constructive version (wrapped in `trunc`).
-/
noncomputable def equiv.sigma_quotient_fin_card {α : Type*} [fintype α] (s : setoid α) :
   α ≃ Σ (q : quotient s), fin (fintype.card {x // ⟦x⟧ = q}) :=
(trunc.out (equiv.sigma_quotient_fin_card_trunc s)).1

@[simp]
lemma equiv.sigma_quot_fin_card_apply_fst {α : Type*} [fintype α] (s : setoid α) (x : α) :
  ((equiv.sigma_quotient_fin_card s) x).1 = ⟦x⟧ :=
(trunc.out (equiv.sigma_quotient_fin_card_trunc s)).2 x
