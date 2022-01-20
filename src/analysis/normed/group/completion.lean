/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.normed.group.basic
import topology.algebra.group_completion
import topology.metric_space.completion

/-!
# Completion of a normed group

In this file we prove that the completion of a (semi)normed group is a normed group.

## Tags

normed group, completion
-/

noncomputable theory

namespace uniform_space
namespace completion

variables (E : Type*)

instance [uniform_space E] [has_norm E] :
  has_norm (completion E) :=
{ norm := completion.extension has_norm.norm }

@[simp] lemma norm_coe {E} [semi_normed_group E] (x : E) :
  ∥(x : completion E)∥ = ∥x∥ :=
completion.extension_coe uniform_continuous_norm x

instance [semi_normed_group E] : normed_group (completion E) :=
{ dist_eq :=
  begin
    intros x y,
    apply completion.induction_on₂ x y; clear x y,
    { refine is_closed_eq (completion.uniform_continuous_extension₂ _).continuous _,
      exact continuous.comp completion.continuous_extension continuous_sub },
    { intros x y,
      rw [← completion.coe_sub, norm_coe, metric.completion.dist_eq, dist_eq_norm] }
  end,
  .. uniform_space.completion.add_comm_group,
  .. metric.completion.metric_space }

end completion
end uniform_space
