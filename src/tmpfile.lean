import topology.algebra.ring

variables {M : Type*} [ring M] [topological_space M] [topological_ring M] [t2_space M]

/-- If a subring of a topological ring is commutative, then so is its topological closure. -/
def subring.comm_ring_topological_closure {s : subring M} (hs : ∀ (x y : s), x * y = y * x) :
  comm_ring s.topological_closure :=
{ mul_comm :=
  begin
    intros a b,
    have h₁ : (s.topological_closure : set M) = closure s := rfl,
    let f₁ := λ (x : M × M), x.1 * x.2,
    let f₂ := λ (x : M × M), x.2 * x.1,
    have hf₁ : continuous f₁ := continuous_mul,
    have hf₂ : continuous f₂,
    { rw [show f₂ = f₁ ∘ prod.swap, from rfl], exact continuous_mul.comp continuous_swap },
    let S : set (M × M) := (s : set M) ×ˢ (s : set M),
    have h₃ : set.eq_on f₁ f₂ (closure S) := begin
      refine set.eq_on.closure _ hf₁ hf₂,
      intros x hx,
      rw [set.mem_prod] at hx,
      rcases hx with ⟨hx₁, hx₂⟩,
      change ((⟨x.1, hx₁⟩ : s) : M) * (⟨x.2, hx₂⟩ : s) = (⟨x.2, hx₂⟩ : s) * (⟨x.1, hx₁⟩ : s),
      exact_mod_cast hs _ _,
    end,
    ext,
    change f₁ ⟨a, b⟩ = f₂ ⟨a, b⟩,
    refine h₃ _,
    rw [closure_prod_eq, set.mem_prod],
    exact ⟨by simp [←h₁], by simp [←h₁]⟩
  end,
  ..show ring s.topological_closure, by apply_instance }
