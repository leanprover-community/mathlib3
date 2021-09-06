-- import topology.compact_open
import topology.uniform_space.pi
import topology.continuous_function.basic

open_locale uniformity filter

variables {α : Type*} {β : Type*} [topological_space α] [_i : uniform_space β]


-- def uniform_convergence_on (s : set α) : uniform_space (α → β) :=
-- uniform_space.of_core (⨅ a ∈ s, uniform_space.comap (λ f : (α → β), f a) _i).to_core

include _i



def compact_open.gen (u : set β) : set C(α,β) := {f | set.range f ⊆ u}

def baz : set C(α, β) := ⋃ (u : set β) (hu : is_open u), {f : C(α, β) | set.range f ⊆ u}

-- The compact-open topology on the space of continuous maps α → β.
instance uniform_convergence_on (s : set α) : topological_space C(α, β) :=
topological_space.generate_from
  {m | ∃ (u : set β) (hu : is_open u), m = compact_open.gen u}

example : (uniform_convergence_on set.univ : uniform_space (α → β)) = Pi.uniform_space (λ a : α, β) :=
rfl


lemma uniform_convergence_on.uniformity (s : set α) :
  @uniformity C(α, β) (uniform_convergence_on s)
  = ⨅ a ∈ s, filter.comap (λ p, (p.1 a, p.2 a)) $ 𝓤 β :=
binfi_uniformity (λ a : α, uniform_space.comap (λ f : C(α, β), f a) _i)

lemma Pi.uniform_continuous_proj {s : set α} {a : α} (hs : a ∈ s) :
  @uniform_continuous _ _ (uniform_convergence_on s) _ (λ f : C(α, β), f a) :=
begin
  rw uniform_continuous_iff,
  exact binfi_le a hs,
end

def foo (s : set α) : uniform_space.core C(α, β) :=
{ uniformity := ⨅ V ∈ 𝓤 β,  𝓟 {p : C(α, β) × C(α, β) | ∀ x ∈ s, (p.1 x, p.2 x) ∈ V},
  refl := begin
    intros A,
    simp [filter.mem_infi],
    rintros a ha f h rfl p,
    rw set.mem_Inter,
    rintros t,
    have := h a,
  end,
  symm := _,
  comp := _ }
-- { uniformity := ⨅ (V ∈ 𝓤 β),
--                   𝓟 { p : C(α, β) × C(α, β) | ∀ x ∈ s, (p.1 x, p.2 x) ∈ V },,
--   refl := _,
--   symm := _,
--   comp := _,
--   is_open_uniformity := _ }
