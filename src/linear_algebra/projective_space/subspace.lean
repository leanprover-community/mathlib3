import linear_algebra.projective_space.dependent

variables (K V : Type*) [field K] [add_comm_group V] [module K V]

namespace projectivization

structure subspace :=
(carrier : set (ℙ K V))
(mem_of_dependent' (x y z : ℙ K V) (h : x ≠ y) (hdep : dependent ![x,y,z]) :
  x ∈ carrier → y ∈ carrier → z ∈ carrier)

namespace subspace

variables {K V}

instance : set_like (subspace K V) (ℙ K V) :=
{ coe := carrier,
  coe_injective' := λ A B, by { cases A, cases B, simp } }

lemma mem_of_dependent (T : subspace K V) (x y z : ℙ K V)
  (h : x ≠ y) (hdep : dependent ![x,y,z]) (hx : x ∈ T) (hy : y ∈ T) :
  z ∈ T := T.mem_of_dependent' x y _ h hdep hx hy

inductive span_carrier (S : set (ℙ K V)) : set (ℙ K V)
| of (x : ℙ K V) (hx : x ∈ S) : span_carrier x
| mem_of_dependent (x y z : ℙ K V) (h : x ≠ y)
    (hdep : dependent ![x,y,z]) : span_carrier x → span_carrier y → span_carrier z

def span (S : set (ℙ K V)) : subspace K V :=
{ carrier := span_carrier S,
  mem_of_dependent' := λ x y z h hdep hx hy,
    span_carrier.mem_of_dependent x y z h hdep hx hy }

lemma subset_span (S : set (ℙ K V)) : S ⊆ span S :=
λ x hx, span_carrier.of _ hx

def gi : galois_insertion (span : set (ℙ K V) → subspace K V) coe :=
{ choice := λ S hS, span S,
  gc := λ A B, ⟨λ h, le_trans (subset_span _) h, begin
    intros h x hx,
    induction hx,
    { apply h, assumption },
    { apply B.mem_of_dependent, assumption' }
  end⟩,
  le_l_u := λ S, subset_span _,
  choice_eq := λ _ _, rfl }

instance : complete_lattice (subspace K V) :=
gi.lift_complete_lattice

def of_submodule (H : submodule K V) : subspace K V :=
{ carrier := { x | x.submodule ≤ H },
  mem_of_dependent' := sorry }

def equiv : subspace K V ≃o submodule K V :=
{ to_fun := λ S, ⨆ (x : ℙ K V) (hx : x ∈ S), x.submodule,
  inv_fun := of_submodule,
  left_inv := sorry,
  right_inv := sorry,
  map_rel_iff' := sorry }

end subspace

end projectivization
