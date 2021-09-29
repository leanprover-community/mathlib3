import data.setoid.basic
import group_theory.subgroup.basic

variables {G : Type*} [group G]

def double_coset_rel (H K : subgroup G) : G → G → Prop :=
λ x y, (∃ (a ∈  H) (b ∈  K), a*x*b=y)

lemma double_coset_rel_is_equiv  (H K : subgroup G) : equivalence (double_coset_rel H K) :=
begin
rw equivalence,
sorry,
end


def left_rel (H K : subgroup G) : setoid G :=
⟨double_coset_rel H K, double_coset_rel_is_equiv H K⟩
