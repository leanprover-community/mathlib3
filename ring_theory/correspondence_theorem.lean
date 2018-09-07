import ring_theory.submodule
import linear_algebra.quotient_module -- I propose moving this to ring_theory
import tactic.tidy
import order.order_iso

open is_submodule
open quotient_module

definition module.correspondence_equiv (R) [ring R] (M) [module R M] (N : set M) [is_submodule N] :
(has_le.le : submodule R (quotient M N) → submodule R (quotient M N) → Prop) ≃o 
(has_le.le : {X : submodule R M // N ⊆ X} → {X : submodule R M // N ⊆ X} → Prop) := {
  to_fun := λ Xbar, ⟨submodule.pullback (mk : M → (quotient M N))
    (is_linear_map_quotient_mk N) Xbar,λ n Hn,begin
      show ↑n ∈ Xbar.s,
      haveI := Xbar.sub,
      have : ((0 : M) : quotient M N) ∈ Xbar.s,
        exact @is_submodule.zero _ _ _ _ Xbar.s _,
      suffices : (n : quotient M N) = (0 : M),
        rwa this,
      rw quotient_module.eq,
      simp [Hn],
    end⟩,
  inv_fun := λ X, submodule.pushforward mk (is_linear_map_quotient_mk N) X.val,
  left_inv := λ P, submodule.eq $ set.image_preimage_eq quotient_module.quotient.exists_rep,
  right_inv := λ ⟨P,HP⟩, subtype.eq $ begin
    show submodule.pullback mk _ (submodule.pushforward mk _ P) = P,
    ext x,
    split,swap,apply set.subset_preimage_image,
    rintro ⟨y,Hy,Hyx⟩,
    change (y : quotient M N) = x at Hyx,
    rw quotient_module.eq at Hyx,
    suffices : y - (y - x) ∈ P,
      simpa,
    haveI := P.sub,
    exact is_submodule.sub Hy (HP Hyx),
  end,
  ord := by tidy
}

namespace quotient_module

definition le_order_embedding (R) [ring R] (M) [module R M] (N : set M) [is_submodule N] :
  (has_le.le : submodule R (quotient M N) → submodule R (quotient M N) → Prop) ≼o
  (has_le.le : submodule R M → submodule R M → Prop) :=
order_embedding.trans (order_iso.to_order_embedding $ module.correspondence_equiv R M N) (subtype.order_embedding _ _)

definition lt_order_embedding (R) [ring R] (M) [module R M] (N : set M) [is_submodule N] :
  (has_lt.lt : submodule R (quotient M N) → submodule R (quotient M N) → Prop) ≼o
  (has_lt.lt : submodule R M → submodule R M → Prop) :=
order_embedding.lt_embedding_of_le_embedding $ quotient_module.le_order_embedding R M N

end quotient_module
