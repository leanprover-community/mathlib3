import analysis.convex
import topology.algebra.module

section vector_space
variables {α : Type*} {β : Type*} {ι : Sort _}
  [add_comm_group α] [vector_space ℝ α] [add_comm_group β] [vector_space ℝ β]
  (A : set α) (B : set α) (x : α)

local attribute [instance] set.pointwise_add

lemma convex_iff':
convex A ↔ ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → a + b = 1 →
  ((λ x, a • x) '' A) + ((λ x, b • x) '' A) ⊆ A :=
⟨λ hA a b ha hb hab w ⟨au, ⟨u, hu, hau⟩, bv, ⟨v, hv, hbv⟩, hw⟩,
  by { rw [←hau, ←hbv] at hw; rw hw; exact hA _ _ _ _ hu hv ha hb hab },
 λ h x y a b hx hy ha hb hab,
  (h ha hb hab) (set.add_mem_pointwise_add ⟨_, hx, rfl⟩ ⟨_, hy, rfl⟩)⟩

end vector_space



section topological_vector_space

variables {α : Type*} [add_comm_group α] [vector_space ℝ α]
[topological_space α] [topological_add_group α] [topological_vector_space ℝ α]

local attribute [instance] set.pointwise_add

open set

/-- In a topological vector space, the interior of a convex set is convex. -/
lemma convex_interior {A : set α} (hA : convex A) : convex (interior A) :=
(convex_iff' _).mpr $ λ a b ha hb hab,
  have h : is_open ((λ x, a • x) '' interior A + (λ x, b • x) '' interior A), from
  or.elim (classical.em (a = 0))
  (λ heq,
    have hne : b ≠ 0, from by { rw [heq, zero_add] at hab, rw hab, exact one_ne_zero },
    is_open_pointwise_add_left ((is_open_map_smul_of_ne_zero hne _) is_open_interior))
  (λ hne,
    is_open_pointwise_add_right ((is_open_map_smul_of_ne_zero hne _) is_open_interior)),
  (subset_interior_iff_subset_of_open h).mpr $ subset.trans
    (by { apply pointwise_add_subset_add; exact image_subset _ interior_subset })
    ((convex_iff' _).mp hA ha hb hab)

/-- In a topological vector space, the closure of a convex set is convex. -/
lemma convex_closure {A : set α} (hA : convex A) : convex (closure A) :=
λ x y a b hx hy ha hb hab,
let f : α → α → α := λ x' y', a • x' + b • y' in
have hf : continuous ((λ p : α × α, p.fst + p.snd) ∘ (λ p : α × α, (a • p.fst, b • p.snd))), from
  continuous.comp continuous_add (continuous.prod_mk
    (continuous_smul continuous_const continuous_fst)
    (continuous_smul continuous_const continuous_snd)),
show f x y ∈ closure A, from
  mem_closure_of_continuous2 hf hx hy (λ x' hx' y' hy', subset_closure
  (hA _ _ _ _ hx' hy' ha hb hab))


end topological_vector_space
