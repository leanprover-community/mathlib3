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

variable {n : ℕ}

instance : topological_space (Δ n) := by unfold standard_topological_simplex; apply_instance

definition induced_map {m n : ℕ} (f : [m] → [n]): Δ m → Δ n := pmf.map f

@[simp] lemma induced_map_id {n : ℕ} : induced_map (@id [n]) = id :=
begin
  funext x,
  simp [induced_map],
  exact pmf.map_id x
end

lemma induced_map_comp {l m n : ℕ} (f : [l] → [m]) (g : [m] → [n]) :
induced_map (g ∘ f) = (induced_map g) ∘ (induced_map f) :=
begin
  funext x,
  simp [induced_map],
  apply eq.symm,
  exact pmf.map_comp _ f g,
end

namespace nnreal
local attribute [instance] classical.prop_decidable

def pure {X : Type*} (x : X) : (X → nnreal) :=
λ y, if y = x then 1 else 0

end nnreal

variables  {α : Type*} [decidable_eq α] [fintype α] {s : finset α}

definition sum_map (f : α → fin n) (x : α → nnreal) : (fin n → nnreal) :=
λj, (∑i, x i * ((nnreal.pure ∘ f) i j))

lemma commuting_square {m : ℕ} (f : [m] → [n]) :
subtype.val ∘ (pmf.map f) = (sum_map f) ∘ subtype.val := rfl

lemma continuous_sums
{f : α → fin n} {j : fin n} : continuous (λ (x : α → nnreal), sum_map f x j) :=
begin
  unfold sum_map,
  rw show (λ (x : α → nnreal), ∑ (i : α), x i * (nnreal.pure ∘ f) i j) =
    λ (x : α → nnreal), univ.sum (λ i, x i * (nnreal.pure ∘ f) i j),
  begin
    funext x,
    apply tsum_eq_sum,
    intros a ani,
    exfalso,
    exact ani (mem_univ a)
  end,
  generalize : univ = s,
  apply finset.induction_on s,
  { rw show (λ (x : α → nnreal), sum ∅ (λ (i : α), x i * (nnreal.pure ∘ f) i j)) = λ (x : α → nnreal), (0 : nnreal),
    begin
      funext x,
      apply finset.sum_empty
    end,
    apply @continuous_const _ _ _ _ _ },
  { intros a s ha hs,
    rw show (λ (x : α → nnreal), sum (insert a s) (λ (i : α), x i * (nnreal.pure ∘ f) i j)) =
                ((λ (p : nnreal × nnreal), p.fst + p.snd) ∘
                (λ x, ((x a * (nnreal.pure ∘ f) a j), sum s (λ (i : α), x i * (nnreal.pure ∘ f) i j)))),
    begin
      funext x,
      simp,
      apply finset.sum_insert ha
    end,
    refine continuous.comp (continuous.prod_mk _ hs) (@topological_add_monoid.continuous_add nnreal _ _ _),
    rw show (λ (x : α → nnreal), x a * (nnreal.pure ∘ f) a j) =
      ((λ (p : nnreal × nnreal), p.fst * p.snd) ∘ (λ x : α → nnreal, (x a, (nnreal.pure ∘ f) a j))),
    begin
      simp
    end,
    refine continuous.comp (continuous.prod_mk (@continuous_apply nnreal _ _ _ _ a) _)
                           (@topological_monoid.continuous_mul nnreal _ _ _),
    rw show (λ (x : α → nnreal), (nnreal.pure ∘ f) a j) = (λ (x : α → nnreal), ite (j = f a) 1 0),
    begin
      funext x,
      simp [function.comp, nnreal.pure],
      split_ifs; refl
    end,
    split_ifs; apply @continuous_const _ _ _ _ _ }
end

lemma continuous_sum_map {m n : ℕ} (f : fin m → fin n) : continuous (sum_map f) :=
begin
  apply @continuous_pi _ _ _ _ _ (sum_map f),
  intro j,
  exact continuous_sums
end

theorem continuous_pmf_map {m n : ℕ} (f : [m] → [n]) : continuous (pmf.map f : Δ m → Δ n) :=
begin
  rw continuous_iff_induced_le,
  unfold pmf.topological_space,
  unfold subtype.topological_space,
  rw show topological_space.induced (pmf.map f) (topological_space.induced subtype.val Pi.topological_space) =
    ((topological_space.induced (pmf.map f)) ∘ (topological_space.induced subtype.val)) Pi.topological_space, by unfold function.comp,
  rw [←induced_comp, commuting_square, ←continuous_iff_induced_le],
  apply continuous.comp continuous_induced_dom (continuous_sum_map f)
end

/-- The i-th face map from Δ_n to Δ_{n+1} -/
def δ {n : ℕ} (i : [n+1]) : Δ n → Δ n.succ := induced_map (simplex_category.δ i)

lemma continuous_δ {n : ℕ} (i : [n+1]) : continuous (δ i) := continuous_pmf_map (simplex_category.δ i)

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