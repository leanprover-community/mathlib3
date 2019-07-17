import ring_theory.algebra data.matrix
import linear_algebra.basis linear_algebra.dimension linear_algebra.determinant linear_algebra.matrix

universes u v

structure field_extension (α : Type u) [discrete_field α] :=
(extension : Type u)
(is_field : discrete_field extension)
(i : α → extension)
(is_hom : is_field_hom i)

namespace field_extension

instance {α : Type*} [discrete_field α] : has_coe_to_sort (field_extension α) :=
⟨_, field_extension.extension⟩

variables {α : Type u} [discrete_field α] {K : field_extension α}

instance : discrete_field K := K.is_field

instance : algebra α K := algebra.of_ring_hom K.i K.is_hom

def base_extension (α : Type u) [discrete_field α] : field_extension α :=
{ extension := α,
  is_field := by apply_instance,
  i := id,
  is_hom := is_ring_hom.id }

class is_finite_dimensional (K : field_extension α) :=
(basis : set K)
(finite : fintype basis)
(is_basis : is_basis α (λ (i : basis), i.val))

section finite_dimensional

variable [is_finite_dimensional K]

instance : fintype (is_finite_dimensional.basis K) := is_finite_dimensional.finite K

def degree (K : field_extension α) [is_finite_dimensional K] : ℕ :=
fintype.card $ is_finite_dimensional.basis K

end finite_dimensional

section field_norm

open vector_space matrix

variable [is_finite_dimensional K]

noncomputable def mul_matrix (a : K) :
  matrix (is_finite_dimensional.basis K) (is_finite_dimensional.basis K) α :=
λ i j, (is_basis.repr (is_finite_dimensional.is_basis K)).to_fun (a * i) j

noncomputable def field_norm (K : field_extension α) [is_finite_dimensional K] : K → α :=
λ a, det (mul_matrix a)

lemma repr_mul {ι α β : Type*} {v : ι → β} [decidable_eq ι]
  [decidable_eq α] [decidable_eq β] [ring α] [add_comm_group β] [module α β]
  (hv : is_basis α v) (a : α) (b : β) :
  (hv.repr).to_fun (a • b) = finsupp.map_range (λ x, a*x) (mul_zero a) (hv.repr b) :=
begin
sorry
end

lemma norm_base {K : field_extension α} [is_finite_dimensional K] (a : α) :
  field_norm K (K.i a) = a ^ (degree K) :=
have h : mul_matrix (K.i a) = diagonal (λ _, a),
  begin
    funext,
    unfold mul_matrix,
    unfold diagonal,
    apply congr_fun,
    change ((is_basis.repr _).to_fun (a • i.val)).to_fun = _,
    rw [repr_mul],
    funext,
    rw [is_basis.repr_eq_single],
    change (finsupp.map_range (λ (x : α), a * x) _ (finsupp.single i 1)) x = _,
    rw [finsupp.map_range_apply],
    { rw [finsupp.single_apply],
      split_ifs,
      { exact mul_one a },
      { exact mul_zero a} },
    { exact mul_zero a }
  end,
begin
change det (mul_matrix (K.i a)) = a ^ (degree K),
rw [h, det_diagonal],
unfold finset.prod,
have : multiset.map (λ (_x : is_finite_dimensional.basis K), a) (finset.univ.val) = multiset.repeat a (degree K),
  begin
    rw [multiset.eq_repeat],
    split,
    { rw [multiset.card_map], refl },
    { intros b hb,
      rw [multiset.mem_map] at hb,
      cases hb with _ he,
      symmetry,
      exact he.2 }
  end,
rw [this, multiset.prod_repeat]
end

lemma norm_mul (a b : K) : field_norm K (a * b) = field_norm K a * field_norm K b := sorry

end field_norm

end field_extension
