import data.setoid.basic
import group_theory.subgroup.basic

variables {G : Type*} [group G] {α : Type*} [has_mul α]

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

def doset  (s t : set α) (a : α) : set α :={ b : α | ∃ (x ∈ s) (y ∈ t), b=x*a*y }

@[simp]
lemma doset_mem (s t : set α) (a b : α) : b ∈ (doset s t a) ↔ ∃ (x ∈ s) (y ∈ t), b=x*a*y :=iff.rfl

lemma sub_doset  (H K : subgroup G) (a b : G) : b ∈ (doset H.1 K a) → (doset H.1 K b) ⊆  (doset H K a) :=
begin
  intro hb,
  intro x,
  simp only [and_imp, exists_prop, forall_exists_index, doset_mem, subgroup.mem_carrier,
    set_like.mem_coe] at *,
  let L:=classical.some_spec hb,
  have hL:=L.2,
  let R:=(classical.some_spec hL),
  intros g hg h hh hx,
  rw R.2 at hx,
  use g*(classical.some hb),
  simp only [H.mul_mem hg L.1, true_and],
  use (classical.some hL)*h,
  simp only [K.mul_mem R.1 hh, true_and],
  simp_rw ← mul_assoc at *,
  exact hx,
end

lemma disjoint_doset  (H K : subgroup G) (a b : G) : ¬ disjoint (doset H.1 K a  ) (doset H K b)
  →  (doset H.1 K a  ) = (doset H K b) :=

begin
intro h,
rw set.not_disjoint_iff at h,
have hb :  b ∈ (doset H.1 K a), by {
  simp at *,
  let x:=classical.some_spec h,
  have hx:= x.1,
  have xh:= x.2,
  let n:=classical.some_spec hx,
  let m:=classical.some_spec n.2,
  let nn:=classical.some_spec xh,
  let mm:=classical.some_spec nn.2,
  have hm:=m.2,
  have hmm:=mm.2,



sorry,
},
sorry,
end
