import linear_algebra.finite_dimensional

open_locale classical

variables (K : Type*) [field K] (V : Type*) [add_comm_group V] [vector_space K V]

open vector_space submodule finite_dimensional

lemma finite_dimensional_of_findim_pos : 0 < findim K V → finite_dimensional K V :=
begin
  intro h,
  rw finite_dimensional_iff_dim_lt_omega,
  unfold findim at h,
  split_ifs at h,
  assumption,
  exfalso,
  exact ne_of_lt h rfl,
end

def proj := { H : submodule K V // findim K H = 1 }

namespace proj

variables {K V}

instance : has_coe (proj K V) (submodule K V) := ⟨subtype.val⟩
instance : has_mem V (proj K V) := ⟨λ v H, v ∈ (H : submodule K V)⟩
instance : has_coe_to_sort (proj K V) := ⟨Type*, λ H, ↥(H : submodule K V)⟩

@[simp]
lemma dim_eq_one {H : proj K V} : findim K H = 1 := H.2

instance {H : proj K V} : finite_dimensional K H :=
begin
  apply finite_dimensional_of_findim_pos,
  simp,
end

@[ext]
lemma ext (A B : proj K V) : (A : submodule K V) = B → A = B := subtype.ext

@[simp]
def mk (v : V) (hv : v ≠ 0) : proj K V := ⟨K ∙ v, findim_span_singleton hv⟩

lemma mk_eq_iff {v w : V} {hv : v ≠ 0} {hw : w ≠ 0} :
  (mk v hv : proj K V) = mk w hw ↔ ∃ a : K, a • v = w :=
begin
  simp only [subtype.mk_eq_mk, mk],
  rw eq_span_singleton_iff,
  split,
  { rintro ⟨h1,h2⟩,
    rcases h2 v (mem_span_singleton_self _) with ⟨r,rfl⟩,
    have : r ≠ 0, by {intro c, finish},
    refine ⟨r⁻¹,_⟩,
    simp [← mul_smul, inv_mul_cancel this] },
  { rintros ⟨a,rfl⟩,
    have : a ≠ 0, by {intro c, finish},
    refine ⟨smul_mem _ _ (mem_span_singleton_self _), _ ⟩,
    intros w hw,
    obtain ⟨r,rfl⟩ := mem_span_singleton.mp hw,
    use r * a⁻¹,
    simp [← mul_smul, mul_assoc, inv_mul_cancel this] }
end

lemma exists_rep (A : proj K V) : ∃ (v : V) (hv : v ≠ 0), A = mk v hv :=
begin
  --cases A with A hA,
  obtain ⟨S,hS1,hS2⟩ := exists_is_basis_finite K A,
  have := @findim_eq_card_finset_basis K A _ _ _ (set.finite.to_finset hS2) ⟨_,_⟩,
  simp at this, -- nonterminal
  replace this := this.symm,
  rw finset.card_eq_one at this,
  rcases this with ⟨a,ha⟩,
  have hSsing : S = {a},
  { rw finset.eq_singleton_iff_unique_mem at ha,
    cases ha with ha1 ha2,
    rw set.eq_singleton_iff_unique_mem,
    refine ⟨_,_⟩,
    rwa set.finite.mem_to_finset at ha1,
    intros b hb,
    apply ha2,
    rwa set.finite.mem_to_finset },
  cases hS1 with hS1 hS2,
  let b : ↥S := ⟨a,by simp [hSsing]⟩,
  have : (coe b : A) ≠ 0 := linear_independent.ne_zero _ hS1,
  simp at this,
  refine ⟨a,_,_⟩,
  { cases a, simpa using this, },
  simp [mk],
  ext1,
  dsimp,
  rw eq_span_singleton_iff,
  refine ⟨a.2,_⟩,
  intros v hv,
  simp [hSsing] at hS2,
  replace hS2 := hS2.symm,
  rw eq_span_singleton_iff at hS2,
  rcases hS2 with ⟨_,hh⟩,
  obtain ⟨r,hr⟩ := hh ⟨v,hv⟩ (by tauto),
  refine ⟨r,_⟩,
  change ↑(r • a) = v,
  rw hr,
  refl,
  convert hS1.1,
  ext,
  erw set.finite.mem_to_finset,
  ext,
  erw set.finite.mem_to_finset,
  convert hS1.2,
  ext,
  erw set.finite.mem_to_finset,
  ext,
  erw set.finite.mem_to_finset,
  -- THIS PROOF IS TERRIBLE.
  -- TODO: Break it up into smaller usable parts.
end

end proj
