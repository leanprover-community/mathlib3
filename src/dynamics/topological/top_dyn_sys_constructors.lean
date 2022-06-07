import dynamics.topological.compact_metrizable
import dynamics.topological.topological_dynamics_basic


/- Reference : [K] Petr Kurka, Topological and symbolic dynamics, SMF, Cours spécialisés, 2003 -/

/- The notions of orbit and trajectory are permuted,
to keep more coherence with the group-theoretic notion of orbit (cf. /dynamics). -/


open topological_dynamics_basic

namespace top_dyn_sys_constructors

variables {X : Type} (T : X → X) [top_dyn_sys X T]


/-- Definition of iterations of a dynamical system. -/
def iterated_top_dyn_sys (n : ℕ) :
  top_dyn_sys X (T^[n]) :=
{ top := by apply_instance,
  compact_metrizable := by apply_instance,
  continuous := continuous.iterate _inst_1.continuous n }


/-- Definition of product of two dynamical systems. -/
def prod_top_dyn_sys {Y : Type} (S : Y → Y) [top_dyn_sys Y S] :
  top_dyn_sys (X × Y) (λ (xy : X × Y), (T xy.fst, S xy.snd)) :=
{ top := by apply_instance,
  compact_metrizable := by apply_instance,
  continuous := continuous.prod_map _inst_1.continuous _inst_2.continuous }


/-- Definition of dynamical system induced on an invariant subset. -/
lemma inv_clos_cod_stab (F : set X) [invariant_closed T F] :
  ∀ (x : F), T x ∈ F :=
by { intro x, apply _inst_2.is_invariant, simp }


def inv_clos_cod_restrict (F : set X) [invariant_closed T F] :
  F → F :=
set.cod_restrict (set.restrict F T) F (inv_clos_cod_stab T F)


def induced_top_dyn_sys (F : set X) [invariant_closed T F] :
  top_dyn_sys F (inv_clos_cod_restrict T F) :=
{ top := subtype.topological_space,
  compact_metrizable := compact_metrizable.closed_of_comp_met_is_comp_met _inst_2.is_closed,
  continuous :=
  begin
    apply continuous.cod_restrict,
    exact continuous_on_iff_continuous_restrict.1 (continuous.continuous_on _inst_1.continuous)
  end }


end top_dyn_sys_constructors
