import data.setoid.basic
import group_theory.subgroup.basic
import group_theory.coset
import data.set.basic

variables {G : Type*} [group G] {α : Type*} [has_mul α]

namespace double_coset

def double_coset_rel (H K : subgroup G) : G → G → Prop :=
λ x y, (∃ (a ∈  H) (b ∈  K), y=a*x*b)

@[simp]
lemma rel_iff (H K : subgroup G) (x y : G) :
  double_coset_rel H K x y  ↔  (∃ (a ∈  H) (b ∈  K), y=a*x*b) := iff.rfl

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
  rw  hx,
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
  rw  hyz,
  rw  hxy,
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

lemma disjoint_sub (H K : subgroup G) (a b : G) :
¬ disjoint (doset H.1 K a  ) (doset H K b) →  b ∈ (doset H.1 K a) :=
begin
  intro h,
  rw set.not_disjoint_iff at h,
  simp at *,
  let x:=classical.some_spec h,
  let xx:=classical.some h,
  have hx:= x.1,
  have xh:= x.2,
  let n:=classical.some_spec hx,
  let xe:=classical.some hx,
  have n2:=n.2,
  let m:=classical.some_spec n2,
  let ne:=classical.some n2,
  let nn:=classical.some_spec xh,
  let ex:=classical.some xh,
  have nn2:=nn.2,
  let mm:=classical.some_spec nn2,
  let me:=classical.some nn2,
  have hm:=m.2,
  have hmm:=mm.2,
  simp_rw ← xe at hm,
  simp_rw ← ne at hm,
  simp_rw ← xx at hm,
  simp_rw ← ex at hmm,
  simp_rw ← me at hmm,
  simp_rw ← xx at hmm,
  rw hm at hmm,
  use ex⁻¹ * xe,
  simp only [H.mul_mem (subgroup.inv_mem H nn.1) n.1, true_and],
  use ne * me⁻¹,
  simp only [K.mul_mem  m.1 (subgroup.inv_mem K mm.1), true_and],
  simp_rw ←  mul_assoc,
  have : ∀ (a b c d e : G),  a*b*c*d*e=a*(b*c*d)*e , by {intros a b c d e, simp_rw ← mul_assoc,},
  erw this,
  rw hmm,
  simp_rw ← mul_assoc,
  simp,
end

lemma disjoint_doset  (H K : subgroup G) (a b : G) : ¬ disjoint (doset H.1 K a  ) (doset H K b)
  →  (doset H.1 K a  ) = (doset H K b) :=

begin
  intro h,
  have hb :  b ∈ (doset H.1 K a), by {apply disjoint_sub _ _ _ _ h, },
  rw disjoint.comm at h,
  have ha :  a ∈ (doset H.1 K b), by {apply disjoint_sub _ _ _ _ h, },
  rw set.subset.antisymm_iff,
  split,
  apply sub_doset H K b a ha,
  apply sub_doset H K a b hb,
end

def quot_to_doset (H K : subgroup G) (q : double_coset_quotient H K ) : set G :=  (doset H.1 K q.out')

abbreviation mk (H K : subgroup G) (a : G) : double_coset_quotient H K  :=
quotient.mk' a

lemma eq (H K : subgroup G) (a b : G): mk H K a = mk H K b ↔ ∃ (h ∈ H) (k ∈  K), b=h*a*k :=
begin
rw quotient.eq',
apply  (rel_iff H K a b),
end

lemma out_eq' (H K : subgroup G) (q : double_coset_quotient H K ) : mk H K q.out' = q :=
quotient.out_eq' q

lemma mk_out'_eq_mul  (H K : subgroup G)  (g : G) :
  ∃ (h k : G), (h ∈ H) ∧ (k ∈ K) ∧   (mk H K g :  double_coset_quotient H K).out' = h * g * k :=
begin
have := eq  H K (mk H K g :  double_coset_quotient H K).out' g,
rw out_eq' at this,
simp only [exists_prop] at this,
have h: mk H K g = mk H K g, by {refl,},
have hh:= this.1 h,
let l:=classical.some_spec hh,
let le:=classical.some hh,
have hr:= l.2,
let r:=classical.some_spec hr,
let re:=classical.some hr,
use le⁻¹,
use re⁻¹,
simp only [H.inv_mem l.left, K.inv_mem r.left, true_and],
have fl:=r.2,
simp_rw ← le at fl,
simp_rw ← re at fl,
rw  fl,
simp_rw ← mul_assoc,
simp only [one_mul, mul_left_inv, mul_inv_cancel_right],
exact congr_arg quotient.out' (congr_arg (mk H K) (eq.symm fl)),
end

lemma doset_eq_quot_eq (H K : subgroup G) (a b : G) :
  (doset H.1 K a)= (doset H K b) → mk H K a = mk H K b :=
begin
intro h,
rw eq,
have : b ∈ doset H.1 K a, by { rw h, simp, use 1, simp, simp [H.one_mem, K.one_mem], },
simp_rw doset at this,
simp at *,
apply this,
end

lemma disjoint_doset'  (H K : subgroup G) (a b : double_coset_quotient H K) :
   a ≠ b → disjoint (doset H.1 K a.out'  ) (doset H K b.out') :=
begin
simp,
contrapose,
simp,
intro h,
have := disjoint_doset H K _ _ h,
have h2:= doset_eq_quot_eq _ _ _ _ this,
simp_rw [out_eq'] at h2,
apply h2,
end


lemma top_eq_union_dosets (H K : subgroup G) : (⊤ : set G) = ⋃ q, quot_to_doset H K q :=
begin
  simp only [set.top_eq_univ],
  ext,
  simp only [set.mem_Union, true_iff, set.mem_univ],
  use mk H K x,
  rw quot_to_doset,
  simp only [exists_prop, doset_mem, subgroup.mem_carrier, set_like.mem_coe],
  have:= mk_out'_eq_mul H K x,
  let l:=classical.some_spec this,
  let le:=classical.some this,
  let r:=classical.some_spec l,
  let re:=classical.some l,
  have rf:= r.2.2,
  use le⁻¹,
  simp only [H.inv_mem r.left, true_and],
  use re⁻¹,
  simp [K.inv_mem r.2.1],
  simp_rw ← le at rf,
  simp_rw ← re at rf,
  rw rf,
  simp_rw ← mul_assoc,
  simp only [one_mul, mul_left_inv, mul_inv_cancel_right],
end

lemma doset_union_right_coset (H K : subgroup G) (a : G):
  (doset H.1 K a) = ⋃ (k : K), (right_coset H (a*k)) :=
begin
  ext,
  simp only [mem_right_coset_iff, exists_prop, mul_inv_rev, set.mem_Union, doset_mem,
    subgroup.mem_carrier, set_like.mem_coe],
  split,
  intro h,
  have h1:=classical.some_spec h,
  let l:=classical.some h,
  have h2:=h1.2,
  let r:=classical.some h2,
  have h3:=classical.some_spec h2,
  use r,
  simp [h3.1],
  simp_rw ← r at h3,
  simp_rw ← l at h3,
  have := h3.2,
  simp_rw this,
  simp_rw ← mul_assoc,
  simp only [mul_inv_cancel_right, subgroup.coe_mk],
  apply h1.1,
  intro h,
  let r:=classical.some h,
  have hh:=classical.some_spec h,
  use x*r⁻¹*a⁻¹,
  simp_rw ← r at hh,
  simp_rw ← mul_assoc at *,
  simp only [hh, true_and, inv_mul_cancel_right],
  use r,
  simp only [set_like.coe_mem, eq_self_iff_true, and_self, inv_mul_cancel_right],
end

lemma doset_union_left_coset (H K : subgroup G) (a : G):
  (doset H.1 K a) = ⋃ (h : H), (left_coset (h*a) K) :=
begin
  ext,
  simp only [mem_left_coset_iff, exists_prop, mul_inv_rev, set.mem_Union, doset_mem,
    subgroup.mem_carrier, set_like.mem_coe],
  split,
  intro h,
  have h1:=classical.some_spec h,
  let l:=classical.some h,
  have h2:=h1.2,
  let r:=classical.some h2,
  have h3:=classical.some_spec h2,
  use l,
  simp [h1.1],
  simp_rw ← r at h3,
  simp_rw ← l at h3,
  have := h3.2,
  simp_rw this,
  simp_rw ← mul_assoc,
  simp only [one_mul, mul_left_inv, subgroup.coe_mk, inv_mul_cancel_right],
  apply h3.1,
  intro h,
  let r:=classical.some h,
  have hh:=classical.some_spec h,
  use r ,
  simp_rw ← r at hh,
  simp only [true_and, set_like.coe_mem],
  use a⁻¹*r⁻¹*x,
  simp only [hh, true_and],
  simp_rw ← mul_assoc at *,
  simp only [one_mul, mul_right_inv, mul_inv_cancel_right],
end


end double_coset
