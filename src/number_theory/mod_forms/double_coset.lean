import data.setoid.basic
import group_theory.subgroup.basic

variables {G : Type*} [group G]

def double_coset_rel (H K : subgroup G) : G → G → Prop :=
λ x y, (∃ (a ∈  H) (b ∈  K), a*x*b=y)

lemma double_coset_rel_is_equiv  (H K : subgroup G) : equivalence (double_coset_rel H K) :=
begin
  rw double_coset_rel,
  rw equivalence,
  split,
  simp only [exists_prop],
  intro x,
  use 1,
  simp [H.one_mem, K.one_mem],
  split,
  intros x y,
  simp only [and_imp, exists_prop, forall_exists_index],
  intros a ha b hb hx,
  use a⁻¹,
  have haa:= subgroup.inv_mem H ha,
  simp only [haa, true_and],
  use b⁻¹,
  have hbb:= subgroup.inv_mem K hb,
  simp only [hbb, true_and],
  rw ← hx,
  simp_rw ← mul_assoc,
  simp only [one_mul, mul_left_inv, mul_inv_cancel_right],
  intros x y z,
  simp only [and_imp, exists_prop, forall_exists_index],
  intros a ha b hb hxy c hc d hd hyz,
  use c*a,
  have hac:= H.mul_mem hc ha,
  simp only [hac, true_and],
  use b*d,
  have hdb:=  (K.mul_mem hb hd),
  simp only [hdb, true_and],
  rw ← hyz,
  rw ← hxy,
  simp_rw ← mul_assoc,
end

def double_coset_setoid (H K : subgroup G) : setoid G :=
⟨double_coset_rel H K, double_coset_rel_is_equiv H K⟩

def double_coset_quotient (H K : subgroup G) : Type* := quotient (double_coset_setoid H K)
