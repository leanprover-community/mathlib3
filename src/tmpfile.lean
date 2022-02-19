import topology.algebra.monoid

variables {M : Type*} [monoid M] [topological_space M] [has_continuous_mul M]
  [t2_space M]

local notation `𝓒` := submonoid.topological_closure

lemma submonoid.inclusion_topological_closure_dense_range (s : submonoid M) :
  dense_range (submonoid.inclusion s.submonoid_topological_closure) :=
begin
  intro x,
   sorry
end

example {s : submonoid M} : topological_space s.topological_closure := by apply_instance
example {s : submonoid M} : t2_space (𝓒 s × 𝓒 s) := by apply_instance

def submonoid.comm_monoid_topological_closure {s : submonoid M} (hs : ∀ (x y : s), x * y = y * x) :
  comm_monoid s.topological_closure :=
{ mul_comm :=
  begin
    intros a b,
    refine s.inclusion_topological_closure_dense_range.induction_on₂ _ _ a b,
    { refine is_closed_eq continuous_mul _,
      have : (λ (x : 𝓒 s × 𝓒 s), x.2 * x.1) = (λ (x : 𝓒 s × 𝓒 s), x.1 * x.2) ∘ prod.swap := rfl,
      rw [this],
      exact continuous_mul.comp continuous_swap },
    { intros x y,
      ext,
      simp [submonoid.inclusion],
      simp only [←submonoid.coe_mul, hs x y] }
  end,
  ..show monoid s.topological_closure, by apply_instance }

-- is_closed_property2
