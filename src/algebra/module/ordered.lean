/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import algebra.module.pi
import algebra.ordered_smul
import algebra.module.prod
import algebra.ordered_field

/-!
# Ordered module

In this file we provide lemmas about `ordered_smul` that hold once a module structure is present.

## References

* https://en.wikipedia.org/wiki/Ordered_module

## Tags

ordered module, ordered scalar, ordered smul, ordered action, ordered vector space
-/

variables {k M N : Type*}

section field

variables [linear_ordered_field k] [ordered_add_comm_group M] [module k M] [ordered_smul k M]
  [ordered_add_comm_group N] [module k N] [ordered_smul k N]

lemma smul_le_smul_iff_of_neg
  {a b : M} {c : k} (hc : c < 0) : c • a ≤ c • b ↔ b ≤ a :=
begin
  rw [← neg_neg c, neg_smul, neg_smul (-c), neg_le_neg_iff, smul_le_smul_iff_of_pos (neg_pos.2 hc)],
  apply_instance,
end

-- TODO: solve `prod.has_lt` and `prod.has_le` misalignment issue
instance prod.ordered_smul : ordered_smul k (M × N) :=
ordered_smul.mk' $ λ (v u : M × N) (c : k) h hc,
  ⟨smul_le_smul_of_nonneg h.1.1 hc.le, smul_le_smul_of_nonneg h.1.2 hc.le⟩

instance pi.ordered_smul {ι : Type*} {M : ι → Type*} [Π i, ordered_add_comm_group (M i)]
  [Π i, mul_action_with_zero k (M i)] [∀ i, ordered_smul k (M i)] :
  ordered_smul k (Π i : ι, M i) :=
begin
  refine (ordered_smul.mk' $ λ v u c h hc i, _),
  change c • v i ≤ c • u i,
  exact smul_le_smul_of_nonneg (h.le i) hc.le,
end

-- Sometimes Lean fails to apply the dependent version to non-dependent functions,
-- so we define another instance
instance pi.ordered_smul' {ι : Type*} {M : Type*} [ordered_add_comm_group M]
  [mul_action_with_zero k M] [ordered_smul k M] :
  ordered_smul k (ι → M) :=
pi.ordered_smul

end field

namespace order_dual

instance [semiring k] [ordered_add_comm_monoid M] [module k M] : module k (order_dual M) :=
{ add_smul := λ r s x, order_dual.rec (add_smul _ _) x,
  zero_smul := λ m, order_dual.rec (zero_smul _) m }

end order_dual
