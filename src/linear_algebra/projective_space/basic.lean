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

lemma top_eq_span_singleton_of_findim_eq_one : findim K V = 1 → (∃ (v : V) (hv : v ≠ 0), ⊤ = (K ∙ v)) :=
begin
  intro h,
  have : finite_dimensional K V,
  { apply finite_dimensional_of_findim_pos,
    simp [h] },
  resetI,
  obtain ⟨b,hb⟩ := exists_is_basis_finset K V,
  have := findim_eq_card_finset_basis hb,
  rw h at this,
  replace this := this.symm,
  obtain ⟨a,ha⟩ := finset.card_eq_one.mp this,
  have hbset : (b : set V) = {a}, by simp [ha],
  cases hb with hb1 hb2,
  refine ⟨a,_,_⟩,
  let ι : (b : set V) → V := λ x, x,
  let x : ↥(b : set V) := ⟨a,_⟩,
  change ι x ≠ 0,
  refine @linear_independent.ne_zero (b : set V) K V ι _ _ _ _ x hb1,
  simp [hbset],
  rw ← hbset,
  symmetry,
  convert hb2,
  simp,
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
  cases A with A hA,
  obtain ⟨v,hv,h⟩ := top_eq_span_singleton_of_findim_eq_one _ _ hA,
  refine ⟨v,_,_⟩,
  simp [hv],
  simp [eq_span_singleton_iff] at *,
  intros w hw,
  specialize h ⟨w,hw⟩,
  convert h,
  funext,
  simp,
  tidy,
end

end proj
