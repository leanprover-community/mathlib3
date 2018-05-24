import order.basic algebraic_topology.simplex_category data.finset data.finsupp

local notation ` [`n`] ` := fin (n+1)

class simplicial_set :=
(objs : Π n : ℕ, Type*)
(maps {m n : ℕ} {f : [m] → [n]} (hf : monotone f) : objs n → objs m)
(comp {l m n : ℕ} {f : [l] → [m]} {g : [m] → [n]} (hf : monotone f) (hg : monotone g) :
  (maps hf) ∘ (maps hg) = (maps (monotone_comp hf hg)))

namespace simplicial_set
def δ {X : simplicial_set} (n : ℕ) (i : [n+1]) :=
simplicial_set.maps (simplex_category.δ_monotone i)
end simplicial_set


namespace simplicial_complex
open finset finsupp simplicial_set group

def C (n : ℕ) (X : simplicial_set) := (@simplicial_set.objs X n) →₀ ℤ

instance (n : ℕ) (X : simplicial_set) : decidable_eq (@simplicial_set.objs X n) := sorry

instance (n : ℕ) (X : simplicial_set) : add_comm_group (C n X)
 := finsupp.add_comm_group

definition induced_map {X G : Type*} [add_comm_group G] (b : X → G) (f : X →₀ ℤ) : G
 := f.support.sum (λ x, gsmul (f x) (b x))

definition boundary (n : ℕ) (X : simplicial_set) : C (n+1) X → C n X
 :=
begin
apply induced_map,
intro x,
exact sum univ (λ i : fin (n.succ), finsupp.single ((simplicial_set.δ n i) x) ((-1 : ℤ)^i.val))
end

instance (n : ℕ) (X : simplicial_set) : is_add_group_hom (boundary n X)
:= begin
sorry
end

lemma C_is_a_complex (n : ℕ) (X : simplicial_set)
: (boundary n X) ∘ (boundary (n+1) X) = (λ γ x, (@has_zero.zero (C n X) _))
begin

sorry
end

end simplicial_complex