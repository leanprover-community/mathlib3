import topology.algebra.group_completion
import topology.metric_space.completion

noncomputable theory

variables (V : Type*)

namespace uniform_space
namespace completion

instance [uniform_space V] [has_norm V] :
  has_norm (completion V) :=
{ norm := completion.extension has_norm.norm }

@[simp] lemma norm_coe {V} [normed_group V] (v : V) :
  ∥(v : completion V)∥ = ∥v∥ :=
completion.extension_coe uniform_continuous_norm v

instance [normed_group V] : normed_group (completion V) :=
{ dist_eq :=
  begin
    intros x y,
    apply completion.induction_on₂ x y; clear x y,
    { refine is_closed_eq (completion.uniform_continuous_extension₂ _).continuous _,
      exact continuous.comp completion.continuous_extension continuous_sub },
    { intros x y,
      rw [← completion.coe_sub, norm_coe, metric.completion.dist_eq, dist_eq_norm] }
  end,
  .. (show add_comm_group (completion V), by apply_instance),
  .. (show metric_space (completion V), by apply_instance) }

end completion
end uniform_space
