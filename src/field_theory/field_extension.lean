import ring_theory.algebra data.matrix
import linear_algebra.finite_dimensional linear_algebra.matrix linear_algebra.determinant

universes u v

namespace field_extension

section field_norm

open finite_dimensional

variables (α : Type u) [discrete_field α]

def mul_map {β : Type v} [discrete_field β] [algebra α β] [finite_dimensional α β] (b : β) : β →ₗ[α] β :=
{ to_fun := λ x, b * x,
  add := mul_add b,
  smul := λ a, algebra.mul_smul_comm a b }

lemma mul_map_mul {β : Type v} [discrete_field β] [algebra α β] [finite_dimensional α β] (b c : β) :
  mul_map α (b * c) = (mul_map α b).comp (mul_map α c) := sorry

variables (β : Type v) [discrete_field β] [algebra α β] [finite_dimensional α β]

def fin_basis : set β :=
classical.some $ exists_is_basis_finite α β

noncomputable instance fin_basis_fintype : fintype (fin_basis α β) :=
(classical.some_spec $ exists_is_basis_finite α β).2.fintype

lemma fin_basis_is_basis : is_basis α (subtype.val : fin_basis α β → β) :=
(classical.some_spec $ exists_is_basis_finite α β).1

--instance : module α β := by apply_instance
--noncomputable def mul_matrix (b : β) : matrix {x // x ∈ fin_basis α β} {x // x ∈ fin_basis α β} α :=
--@linear_equiv.to_fun α (β →ₗ[α] β) _ _ _ _ linear_map.module matrix.module
--  (lin_equiv_matrix (fin_basis_is_basis α β) (fin_basis_is_basis α β)) (mul_map α b)

noncomputable def mul_matrix (b : β) : matrix {x // x ∈ fin_basis α β} {x // x ∈ fin_basis α β} α :=
by { letI : module α β := algebra.to_module α β,
     letI : module α (β →ₗ[α] β) := linear_map.module,
     letI : module α (matrix {x // x ∈ fin_basis α β} {x // x ∈ fin_basis α β} α) := matrix.module,
     exact (lin_equiv_matrix (fin_basis_is_basis α β) (fin_basis_is_basis α β)).to_fun (mul_map α b) }

noncomputable def field_norm (b : β) : α := matrix.det $ mul_matrix α β b

lemma test (α β γ : Type*) [discrete_field α] [add_comm_group β] [add_comm_group γ]
  [module α β] [module α γ] (e : β ≃ₗ[α] γ) : e.to_fun = e.to_linear_map.to_fun := rfl

@[simp] lemma norm_mul (b c : β) : field_norm α β (b * c) = field_norm α β b * field_norm α β c :=
begin
unfold field_norm,
unfold mul_matrix,
simp,
rw [←matrix.det_mul],
congr,
conv_rhs { rw [←smul_eq_mul], congr, skip, rw [test] },
rw[←linear_map.smul (lin_equiv_matrix _ _).to_linear_map ((lin_equiv_matrix _ _).to_fun (mul_map α b)) (mul_map α c)],

end

end field_norm

end field_extension

/-
universes u v

class field_extension (α : Type u) (β : Type v) [discrete_field α] [discrete_field β] extends algebra α β

namespace field_extension

instance (α : Type u) (β : Type v) [discrete_field α] [discrete_field β] [field_extension α β] :
  algebra α β := by apply_instance

instance base_extension (α : Type u) [discrete_field α]: field_extension α α := {..algebra.id α}

section findim

variables (α : Type u) [discrete_field α] (β : Type v) [discrete_field β]

class findim_field_extension extends field_extension α β :=
(finite_dimensional : finite_dimensional α β)

instance [findim_field_extension α β]: finite_dimensional α β :=
findim_field_extension.finite_dimensional α β

instance findim_base_extension : findim_field_extension α α :=
{ finite_dimensional := is_noetherian_ring.to_is_noetherian,
  ..field_extension.base_extension α }

end findim

section field_norm

open finite_dimensional

variables (α : Type u) [discrete_field α]

def mul_map {β : Type v} [discrete_field β] [findim_field_extension α β] (b : β) : β →ₗ[α] β :=
{ to_fun := λ x, b * x,
  add := mul_add b,
  smul := λ a, algebra.mul_smul_comm a b }

variables (β : Type v) [discrete_field β] [findim_field_extension α β]

def fin_basis : set β :=
classical.some $ exists_is_basis_finite α β

noncomputable instance fin_basis_fintype : fintype (fin_basis α β) :=
(classical.some_spec $ exists_is_basis_finite α β).2.fintype

lemma fin_basis_is_basis : is_basis α (subtype.val : fin_basis α β → β) :=
(classical.some_spec $ exists_is_basis_finite α β).1

--instance : module α β := by apply_instance
--noncomputable def mul_matrix (b : β) : matrix {x // x ∈ fin_basis α β} {x // x ∈ fin_basis α β} α :=
--@linear_equiv.to_fun α (β →ₗ[α] β) _ _ _ _ linear_map.module matrix.module
--  (lin_equiv_matrix (fin_basis_is_basis α β) (fin_basis_is_basis α β)) (mul_map α b)

noncomputable def mul_matrix (b : β) : matrix {x // x ∈ fin_basis α β} {x // x ∈ fin_basis α β} α :=
by { letI : module α β := algebra.to_module α β,
     letI : module α (β →ₗ[α] β) := linear_map.module,
     letI : module α (matrix {x // x ∈ fin_basis α β} {x // x ∈ fin_basis α β} α) := matrix.module,
     exact (lin_equiv_matrix (fin_basis_is_basis α β) (fin_basis_is_basis α β)).to_fun (mul_map α b) }

--def field_norm (b : β) : α := lin_equiv_matrix (mul_map α b)

end field_norm

end field_extension
-/

/-structure field_extension (α : Type u) [discrete_field α] :=
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

/-
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
-/

end field_norm

end field_extension-/
