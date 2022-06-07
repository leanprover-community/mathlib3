import algebra.ring
import data.real.basic
import data.matrix.basic
import dynamics.topological.compact_metrizable
import dynamics.topological.topological_dynamics_basic
import dynamics.topological.top_dyn_sys_constructors
import dynamics.topological.transition_matrices


/-noncomputable theory-/

/-universes u-/
/-variables {I : Type} [fintype I]-/
/-variables {A : matrix I I ℤ}-/


/- Question : utiliser instance plutôt que lemma dans les différents types de matrices de transition ?-/
/- Cela permettrait-il d'avoir une preuve plus propre de primitive -> basique ? -/


namespace subshifts


variables (I : Type)

/- Voir : topology.metric_space.pi_nat-/

def shift_map :
  (ℕ → I) → (ℕ → I) :=
 (λ f, (λ n, f (n+1)))


variables [topological_space I] [discrete_topology I]


def shift_space :
  topological_space (ℕ → I) :=
@Pi.topological_space ℕ (λ n, I) (λ n, _inst_1)


variables [fintype I] [decidable_eq I]


def compact_metrizable_shift :
  @compact_metrizable.compact_metrizable_space (ℕ → I) (shift_space I) :=
{ compact := by apply pi.compact_space,
  t2 := by apply Pi.t2_space,
  second_countable :=
  begin
    haveI I_secound_countable : topological_space.second_countable_topology I :=
    begin
      apply topological_space.is_topological_basis.second_countable_topology (is_topological_basis_singletons I),
      apply set.countable.mono _ (set.countable_set_of_finite_subset (set.finite.countable (@set.finite_univ I _))),
      simp,
    end,
    apply topological_space.second_countable_topology_encodable,
  end }


instance one_sided_full_shift :
  @topological_dynamics_basic.top_dyn_sys (ℕ → I) (shift_map I) :=
{ top := shift_space I,
  compact_metrizable := compact_metrizable_shift I,
  continuous := by { apply continuous_pi_iff.2, intro i, apply continuous_apply } }


variable (A : matrix I I ℤ)


def subshift_space := {x : ℕ → I | ∀ n : ℕ, A (x n) (x (n+1)) = 1}


lemma subshift_space_is_Inter :
  subshift_space I A = ⋂ (n : ℕ), {x : ℕ → I | A (x n) (x (n+1)) = 1} :=
begin
  unfold subshift_space,
  apply subset_antisymm,
  { intro x, simp },
  { intro x, simp },
end


instance : topological_dynamics_basic.invariant_closed (shift_map I) (subshift_space I A) :=
{ is_closed :=
  begin
    rw subshift_space_is_Inter I A,
    apply is_closed_Inter,
    intro n,
    let F := { ij : I × I | A ij.1 ij.2 = 1 },
    let f : (ℕ → I) → I × I := λ x, (x n, x (n+1)),
    change is_closed (f ⁻¹' F),
    exact (is_closed_discrete F).preimage (by continuity),
  end,
  is_invariant := by tauto }


def subshift := top_dyn_sys_constructors.induced_top_dyn_sys (shift_map I) (subshift_space I A)


end subshifts
