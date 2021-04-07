import tactic
import data.real.basic
import linear_algebra.affine_space.independent
import linear_algebra.std_basis
import linear_algebra.affine_space.finite_dimensional
import linear_algebra.affine_space.combination
import linear_algebra.finite_dimensional
import analysis.convex.topology

open_locale big_operators
open finset

@[to_additive]
lemma coe_prod {α β : Type*} [comm_monoid β] (s : finset α) (f : α → β) :
  ∏ (i : (s : set α)), f i = ∏ i in s, f i :=
begin
  classical,
  rw ←prod_image,
  apply prod_congr _ (λ _ _, rfl),
  { ext, simp },
  { simp },
end
