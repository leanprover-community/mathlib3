/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.monoid_algebra.basic

/-!
# Division of `add_monoid_algebra` by monomials

## Main definitions

* `div_of`

-/


variables {k G : Type*} [semiring k] [add_cancel_monoid G] [partial_order G]
  [has_exists_add_of_le G]

namespace add_monoid_algebra

noncomputable def div_of (x : add_monoid_algebra k G) (g : G) : add_monoid_algebra k G :=
finsupp.comap_domain ((+) g) x $ function.injective.inj_on (add_right_injective g) _

@[simp] lemma div_of_apply (x : add_monoid_algebra k G) (g g' : G) :
  div_of x g g' = x (g + g') := rfl

noncomputable def mod_of (x : add_monoid_algebra k G) (g : G) : add_monoid_algebra k G :=
x.filter (λ g', g' < g)

@[simp] lemma mod_of_apply_of_lt (x : add_monoid_algebra k G) {g g' : G} (h : g' < g) :
  mod_of x g g' = x g' :=
finsupp.filter_apply_pos _ _ h

lemma div_of_add_mod_of (x : add_monoid_algebra k G) (g : G):
  of' k G g * x.div_of g + x.mod_of g = x :=
begin
  ext g',
  simp_rw [finsupp.add_apply],
  by_cases h : g' < g,
  { rw [mod_of_apply_of_lt _ h, of'_apply, single_mul_apply_aux, one_mul], },

end

#check exists_add_lt_and_pos_of_lt


end add_monoid_algebra
