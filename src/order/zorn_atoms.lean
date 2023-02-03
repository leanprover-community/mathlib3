/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import order.zorn
import order.atoms

/-!
# Zorn lemma for (co)atoms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we use Zorn's lemma to prove that a partial order is atomic if every nonempty chain
`c`, `⊥ ∉ c`, has a lower bound not equal to `⊥`. We also prove the order dual version of this
statement.
-/

open set

/-- **Zorn's lemma**: A partial order is coatomic if every nonempty chain `c`, `⊤ ∉ c`, has an upper
bound not equal to `⊤`. -/
lemma is_coatomic.of_is_chain_bounded {α : Type*} [partial_order α] [order_top α]
  (h : ∀ c : set α, is_chain (≤) c → c.nonempty → ⊤ ∉ c → ∃ x ≠ ⊤, x ∈ upper_bounds c) :
  is_coatomic α :=
begin
  refine ⟨λ x, le_top.eq_or_lt.imp_right $ λ hx, _⟩,
  rcases zorn_nonempty_partial_order₀ (Ico x ⊤) (λ c hxc hc y hy, _) x (left_mem_Ico.2 hx)
    with ⟨y, ⟨hxy, hy⟩, -, hy'⟩,
  { refine ⟨y, ⟨hy.ne, λ z hyz, le_top.eq_or_lt.resolve_right $ λ hz, _⟩, hxy⟩,
    exact hyz.ne' (hy' z ⟨hxy.trans hyz.le, hz⟩ hyz.le) },
  { rcases h c hc ⟨y, hy⟩ (λ h, (hxc h).2.ne rfl) with ⟨z, hz, hcz⟩,
    exact ⟨z, ⟨le_trans (hxc hy).1 (hcz hy), hz.lt_top⟩, hcz⟩ }
end

/-- **Zorn's lemma**: A partial order is atomic if every nonempty chain `c`, `⊥ ∉ c`, has an lower
bound not equal to `⊥`. -/
lemma is_atomic.of_is_chain_bounded {α : Type*} [partial_order α] [order_bot α]
  (h : ∀ c : set α, is_chain (≤) c → c.nonempty → ⊥ ∉ c → ∃ x ≠ ⊥, x ∈ lower_bounds c) :
  is_atomic α :=
is_coatomic_dual_iff_is_atomic.mp $ is_coatomic.of_is_chain_bounded $ λ c hc, h c hc.symm
