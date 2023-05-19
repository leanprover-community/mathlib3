/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import algebra.big_operators.basic
import data.finset.basic
import data.multiset.basic
import group_theory.group_action.defs

/-!
# Lemmas about group actions on big operators

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Note that analogous lemmas for `module`s like `finset.sum_smul` appear in other files.
-/

variables {α β γ : Type*}

open_locale big_operators

section
variables [add_monoid β] [distrib_smul α β]

lemma list.smul_sum {r : α} {l : list β} :
  r • l.sum = (l.map ((•) r)).sum :=
(distrib_smul.to_add_monoid_hom β r).map_list_sum l

end

section
variables [monoid α] [monoid β] [mul_distrib_mul_action α β]

lemma list.smul_prod {r : α} {l : list β} :
  r • l.prod = (l.map ((•) r)).prod :=
(mul_distrib_mul_action.to_monoid_hom β r).map_list_prod l

end

section
variables [add_comm_monoid β] [distrib_smul α β]

lemma multiset.smul_sum {r : α} {s : multiset β} :
  r • s.sum = (s.map ((•) r)).sum :=
(distrib_smul.to_add_monoid_hom β r).map_multiset_sum s

lemma finset.smul_sum {r : α} {f : γ → β} {s : finset γ} :
  r • ∑ x in s, f x = ∑ x in s, r • f x :=
(distrib_smul.to_add_monoid_hom β r).map_sum f s

end

section
variables [monoid α] [comm_monoid β] [mul_distrib_mul_action α β]

lemma multiset.smul_prod {r : α} {s : multiset β} :
  r • s.prod = (s.map ((•) r)).prod :=
(mul_distrib_mul_action.to_monoid_hom β r).map_multiset_prod s

lemma finset.smul_prod {r : α} {f : γ → β} {s : finset γ} :
  r • ∏ x in s, f x = ∏ x in s, r • f x :=
(mul_distrib_mul_action.to_monoid_hom β r).map_prod f s

end
