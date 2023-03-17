/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import algebra.order.with_zero
import topology.algebra.order.field

/-!
# The topology on linearly ordered commutative groups with zero

Let `Γ₀` be a linearly ordered commutative group to which we have adjoined a zero element.
Then `Γ₀` may naturally be endowed with a topology that turns `Γ₀` into a topological monoid.
Neighborhoods of zero are sets containing `{γ | γ < γ₀}` for some invertible element `γ₀`
and every invertible element is open.
In particular the topology is the following:
"a subset `U ⊆ Γ₀` is open if `0 ∉ U` or if there is an invertible
`γ₀ ∈ Γ₀` such that `{γ | γ < γ₀} ⊆ U`", see `linear_ordered_comm_group_with_zero.is_open_iff`.

We prove this topology is ordered and T₃ (in addition to be compatible with the monoid
structure).

All this is useful to extend a valuation to a completion. This is an abstract version of how the
absolute value (resp. `p`-adic absolute value) on `ℚ` is extended to `ℝ` (resp. `ℚₚ`).

## Implementation notes

This topology is not defined as a global instance since it may not be the desired topology on a
linearly ordered commutative group with zero. You can locally activate this topology using
`open_locale with_zero_topology`.
-/

open_locale topology filter
open topological_space filter set function

namespace with_zero_topology

variables {α Γ₀ : Type*} [linear_ordered_comm_group_with_zero Γ₀] {γ γ₁ γ₂ : Γ₀} {l : filter α}
  {f : α → Γ₀}

/-- The topology on a linearly ordered commutative group with a zero element adjoined.
A subset U is open if 0 ∉ U or if there is an invertible element γ₀ such that {γ | γ < γ₀} ⊆ U. -/
protected def topological_space : topological_space Γ₀ :=
topological_space.mk_of_nhds $ update pure 0 $ ⨅ γ ≠ 0, 𝓟 (Iio γ)

localized "attribute [instance] with_zero_topology.topological_space" in with_zero_topology

lemma nhds_eq_update : (𝓝 : Γ₀ → filter Γ₀) = update pure 0 (⨅ γ ≠ 0, 𝓟 (Iio γ)) :=
funext $ nhds_mk_of_nhds_single $ le_infi₂ $ λ γ h₀, le_principal_iff.2 $ zero_lt_iff.2 h₀

/-!
### Neighbourhoods of zero
-/

lemma nhds_zero : 𝓝 (0 : Γ₀) = ⨅ γ ≠ 0, 𝓟 (Iio γ) := by rw [nhds_eq_update, update_same]

/-- In a linearly ordered group with zero element adjoined, `U` is a neighbourhood of `0` if and
only if there exists a nonzero element `γ₀` such that `Iio γ₀ ⊆ U`. -/
lemma has_basis_nhds_zero : (𝓝 (0 : Γ₀)).has_basis (λ γ : Γ₀, γ ≠ 0) Iio :=
begin
  rw [nhds_zero],
  refine has_basis_binfi_principal _ ⟨1, one_ne_zero⟩,
  exact directed_on_iff_directed.2 (directed_of_inf $ λ a b hab, Iio_subset_Iio hab)
end

lemma Iio_mem_nhds_zero (hγ : γ ≠ 0) : Iio γ ∈ 𝓝 (0 : Γ₀) := has_basis_nhds_zero.mem_of_mem hγ

/-- If `γ` is an invertible element of a linearly ordered group with zero element adjoined, then
`Iio (γ : Γ₀)` is a neighbourhood of `0`. -/
lemma nhds_zero_of_units (γ : Γ₀ˣ) : Iio ↑γ ∈ 𝓝 (0 : Γ₀) := Iio_mem_nhds_zero γ.ne_zero

lemma tendsto_zero : tendsto f l (𝓝 (0 : Γ₀)) ↔ ∀ γ₀ ≠ 0, ∀ᶠ x in l, f x < γ₀ := by simp [nhds_zero]

/-!
### Neighbourhoods of non-zero elements
-/

/-- The neighbourhood filter of a nonzero element consists of all sets containing that
element. -/
@[simp] lemma nhds_of_ne_zero {γ : Γ₀} (h₀ : γ ≠ 0) : 𝓝 γ = pure γ :=
by rw [nhds_eq_update, update_noteq h₀]

/-- The neighbourhood filter of an invertible element consists of all sets containing that
element. -/
lemma nhds_coe_units (γ : Γ₀ˣ) : 𝓝 (γ : Γ₀) = pure (γ : Γ₀) := nhds_of_ne_zero γ.ne_zero

/-- If `γ` is an invertible element of a linearly ordered group with zero element adjoined, then
`{γ}` is a neighbourhood of `γ`. -/
lemma singleton_mem_nhds_of_units (γ : Γ₀ˣ) : ({γ} : set Γ₀) ∈ 𝓝 (γ : Γ₀) := by simp

/-- If `γ` is a nonzero element of a linearly ordered group with zero element adjoined, then `{γ}`
is a neighbourhood of `γ`. -/
lemma singleton_mem_nhds_of_ne_zero (h : γ ≠ 0) : ({γ} : set Γ₀) ∈ 𝓝 (γ : Γ₀) := by simp [h]

lemma has_basis_nhds_of_ne_zero {x : Γ₀} (h : x ≠ 0) :
  has_basis (𝓝 x) (λ i : unit, true) (λ i, {x}) :=
by { rw [nhds_of_ne_zero h], exact has_basis_pure _ }

lemma has_basis_nhds_units (γ : Γ₀ˣ) :
  has_basis (𝓝 (γ : Γ₀)) (λ i : unit, true) (λ i, {γ}) :=
has_basis_nhds_of_ne_zero γ.ne_zero

lemma tendsto_of_ne_zero {γ : Γ₀} (h : γ ≠ 0) : tendsto f l (𝓝 γ) ↔ ∀ᶠ x in l, f x = γ :=
by rw [nhds_of_ne_zero h, tendsto_pure]

lemma tendsto_units {γ₀ : Γ₀ˣ} : tendsto f l (𝓝 (γ₀ : Γ₀)) ↔ ∀ᶠ x in l, f x = γ₀ :=
tendsto_of_ne_zero γ₀.ne_zero

lemma Iio_mem_nhds (h : γ₁ < γ₂) : Iio γ₂ ∈ 𝓝 γ₁ :=
by rcases eq_or_ne γ₁ 0 with rfl|h₀; simp [*, h.ne', Iio_mem_nhds_zero]

/-!
### Open/closed sets
-/

lemma is_open_iff {s : set Γ₀} : is_open s ↔ (0 : Γ₀) ∉ s ∨ ∃ γ ≠ 0, Iio γ ⊆ s :=
begin
  rw [is_open_iff_mem_nhds, ← and_forall_ne (0 : Γ₀)],
  simp [nhds_of_ne_zero, imp_iff_not_or, has_basis_nhds_zero.mem_iff] { contextual := tt }
end

lemma is_closed_iff {s : set Γ₀} : is_closed s ↔ (0 : Γ₀) ∈ s ∨ ∃ γ ≠ 0, s ⊆ Ici γ :=
by simp only [← is_open_compl_iff, is_open_iff, mem_compl_iff, not_not, ← compl_Ici,
  compl_subset_compl]

lemma is_open_Iio {a : Γ₀} : is_open (Iio a) :=
is_open_iff.mpr $ imp_iff_not_or.mp $ λ ha, ⟨a, ne_of_gt ha, subset.rfl⟩

/-!
### Instances
-/

/-- The topology on a linearly ordered group with zero element adjoined is compatible with the order
structure: the set `{p : Γ₀ × Γ₀ | p.1 ≤ p.2}` is closed. -/
protected lemma order_closed_topology : order_closed_topology Γ₀ :=
{ is_closed_le' :=
  begin
    simp only [← is_open_compl_iff, compl_set_of, not_le, is_open_iff_mem_nhds],
    rintros ⟨a, b⟩ (hab : b < a),
    rw [nhds_prod_eq, nhds_of_ne_zero (zero_le'.trans_lt hab).ne', pure_prod],
    exact Iio_mem_nhds hab
  end }

localized "attribute [instance] with_zero_topology.order_closed_topology" in with_zero_topology

/-- The topology on a linearly ordered group with zero element adjoined is T₃. -/
lemma t3_space : t3_space Γ₀ :=
{ to_regular_space := regular_space.of_lift'_closure $ λ γ,
    begin
      rcases ne_or_eq γ 0 with h₀|rfl,
      { rw [nhds_of_ne_zero h₀, lift'_pure (monotone_closure Γ₀), closure_singleton,
          principal_singleton] },
      { exact has_basis_nhds_zero.lift'_closure_eq_self
        (λ x hx, is_closed_iff.2 $ or.inl $ zero_lt_iff.2 hx) },
    end }

localized "attribute [instance] with_zero_topology.t3_space" in with_zero_topology

/-- The topology on a linearly ordered group with zero element adjoined makes it a topological
monoid. -/
protected lemma has_continuous_mul : has_continuous_mul Γ₀ :=
⟨begin
  rw continuous_iff_continuous_at,
  rintros ⟨x, y⟩,
  wlog hle : x ≤ y generalizing x y,
  { have := tendsto.comp (this y x (le_of_not_le hle)) (continuous_swap.tendsto (x,y)),
    simpa only [mul_comm, function.comp, prod.swap], },
  rcases eq_or_ne x 0 with rfl|hx; [rcases eq_or_ne y 0 with rfl|hy, skip],
  { rw [continuous_at, zero_mul],
    refine ((has_basis_nhds_zero.prod_nhds has_basis_nhds_zero).tendsto_iff has_basis_nhds_zero).2
      (λ γ hγ, ⟨(γ, 1), ⟨hγ, one_ne_zero⟩, _⟩),
    rintro ⟨x, y⟩ ⟨hx : x < γ, hy : y < 1⟩,
    exact (mul_lt_mul₀ hx hy).trans_eq (mul_one γ) },
  { rw [continuous_at, zero_mul, nhds_prod_eq, nhds_of_ne_zero hy, prod_pure, tendsto_map'_iff],
    refine (has_basis_nhds_zero.tendsto_iff has_basis_nhds_zero).2 (λ γ hγ, _),
    refine ⟨γ / y, div_ne_zero hγ hy, λ x hx, _⟩,
    calc x * y < γ / y * y : mul_lt_right₀ _ hx hy
           ... = γ         : div_mul_cancel _ hy },
  { have hy : y ≠ 0, from ((zero_lt_iff.mpr hx).trans_le hle).ne',
    rw [continuous_at, nhds_prod_eq, nhds_of_ne_zero hx, nhds_of_ne_zero hy, prod_pure_pure],
    exact pure_le_nhds (x * y) }
end⟩

localized "attribute [instance] with_zero_topology.has_continuous_mul" in with_zero_topology

protected lemma has_continuous_inv₀ : has_continuous_inv₀ Γ₀ :=
⟨λ γ h, by { rw [continuous_at, nhds_of_ne_zero h], exact pure_le_nhds γ⁻¹ }⟩

localized "attribute [instance] with_zero_topology.has_continuous_inv₀" in with_zero_topology

end with_zero_topology
