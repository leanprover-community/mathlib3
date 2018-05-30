import algebraic_topology.simplex_category algebraic_topology.simplicial_set analysis.topology.topological_space analysis.probability_mass_function
noncomputable theory
open finset

namespace pmf

instance {n : ℕ} : topological_space (pmf (fin n)) := subtype.topological_space

end pmf

local notation ` [`n`] ` := fin (n+1)

/-- The n-th standard topological simplex: Δ_n = { x ∈ ℝ^{n+1} | ∀ i, x_i ≥ 0, and ∑ x_i = 1 } -/
definition standard_topological_simplex (n : ℕ) := pmf [n]

local notation ` Δ ` := standard_topological_simplex

namespace standard_topological_simplex

variables {m n : ℕ}

instance : topological_space (Δ n) := by unfold standard_topological_simplex; apply_instance

namespace nnreal
local attribute [instance] classical.prop_decidable

def pure {X : Type*} (x : X) : (X → nnreal) :=
λ y, if y = x then 1 else 0

end nnreal

theorem continuous_pmf_map (f : [m] → [n]) : continuous (pmf.map f) :=
continuous_subtype_mk _ $ continuous_pi $ assume j,
  show continuous (λ x : Δ m, ∑ i : [m], x.val i * (pmf.pure ∘ f) i j), from
    begin
      rw show (λ x : Δ m, ∑ i : [m], x.val i * (pmf.pure ∘ f) i j) =
        λ (x : Δ m), univ.sum (λ i, x.val i * (nnreal.pure ∘ f) i j),
      begin
        funext x,
        apply tsum_eq_sum,
        intros a ani,
        exfalso,
        exact ani (mem_univ a)
      end,
      apply continuous_finset_sum,
      intros i hin,
      rw show (λ (x : Δ m), x.val i * (nnreal.pure ∘ f) i j) =
        ((λ (p : nnreal × nnreal), p.fst * p.snd) ∘ (λ x : Δ m, (x.val i, ite (j = f i) 1 0))),
      begin
        funext x,
        simp [function.comp, nnreal.pure],
        split_ifs; simp
      end,
      refine continuous.comp (continuous.prod_mk (continuous.comp continuous_induced_dom (continuous_apply i)) _)
                            (@topological_monoid.continuous_mul nnreal _ _ _),
      split_ifs; apply @continuous_const (Δ m) nnreal _ _ _
    end

/-- The i-th face map from Δ_n to Δ_{n+1} -/
def δ (i : [n+1]) : Δ n → Δ n.succ := pmf.map (simplex_category.δ i)

lemma continuous_δ (i : [n+1]) : continuous (δ i) := continuous_pmf_map (simplex_category.δ i)

end standard_topological_simplex

namespace singular_set

open simplicial_set standard_topological_simplex

/-- The singular set associated with a topological space X: its n-simplices are the continuous maps from Δ_n to X -/
definition S {X: Type*} [topological_space X] : simplicial_set :=
{ objs := λ n, {φ : Δ n → X // continuous φ},
  maps := λ m n f hf φ, ⟨φ.val ∘ pmf.map f, continuous.comp (continuous_pmf_map f) φ.property⟩,
  id := λ n, funext $ assume φ,
  begin
    apply subtype.eq,
    simp [function.comp],
    funext x,
    rw pmf.map_id
  end,
  comp := λ l m n f g hf hg, funext $ assume φ,
  begin
    simp,
    rw function.comp.assoc,
    congr,
    funext x,
    rw ←pmf.map_comp
  end}

end singular_set