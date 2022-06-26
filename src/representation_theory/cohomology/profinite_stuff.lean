import topology.category.Profinite.as_limit
import topology.algebra.open_subgroup
#exit
universes v u

variables (G : Type*) [group G] [topological_space G] [topological_group G]

#check CompHaus
#check set_of
#check quotient_group.left_rel
#check left_coset
--left_rel_r_eq_left_coset_equivalence

#check open_subgroup
#check topological_group_quotient
lemma open_iff_closed_finite_index (hG : compact_space G) (H : subgroup G) :
  is_open (H : set G) ↔ is_closed (H : set G)
    ∧ nonempty (fintype (quotient $ quotient_group.left_rel H)) :=
begin
  split,
  { intro h,
    split,
    { exact open_subgroup.is_closed ⟨H, h⟩ },
    { refine hG.induction_on _, }},

end
