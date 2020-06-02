import data.fintype.basic

open_locale classical

-- It would be possible to make a computable `trunc` valued version of this,
-- by picking an ordering on `α`,
-- and using that to get an induced ordering on each equivalence class.
noncomputable def equiv.sigma_quotient_fin_card {α : Type*} [fintype α] (s : setoid α) :
   α ≃ Σ (q : quotient s), fin (fintype.card {x // ⟦x⟧ = q}) :=
(equiv.sigma_preimage_equiv (λ x, ⟦x⟧)).symm.trans
  (equiv.sigma_congr_right (λ q : quotient s, trunc.out (fintype.equiv_fin {x // ⟦x⟧ = q})))

@[simp]
lemma equiv.sigma_quot_fin_card_apply_fst {α : Type*} [fintype α] (s : setoid α) (x : α) :
  ((equiv.sigma_quotient_fin_card s) x).1 = ⟦x⟧ :=
rfl
