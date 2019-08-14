import ring_theory.algebra data.matrix
import linear_algebra.finite_dimensional linear_algebra.matrix linear_algebra.determinant
import ring_theory.polynomial

universes u v

class field_extension (α : Type u) (β : Type v) [discrete_field α] [discrete_field β] extends algebra α β

namespace field_extension

section field_norm

open finite_dimensional

variables (α : Type u) [discrete_field α]

def mul_map {β : Type v} [discrete_field β] [field_extension α β] [finite_dimensional α β] (b : β) : β →ₗ[α] β :=
{ to_fun := λ x, b * x,
  add := mul_add b,
  smul := λ a, algebra.mul_smul_comm a b }

lemma mul_map_mul {β : Type v} [discrete_field β] [field_extension α β] [finite_dimensional α β] (b c : β) :
  mul_map α (b * c) = (mul_map α b).comp (mul_map α c) := sorry

variables (β : Type v) [discrete_field β] [field_extension α β] [finite_dimensional α β]

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
sorry
/-begin
unfold field_norm,
unfold mul_matrix,
simp,
rw [←matrix.det_mul],
congr,
conv_rhs { rw [←smul_eq_mul], congr, skip, rw [test] },
rw[←linear_map.smul (lin_equiv_matrix _ _).to_linear_map ((lin_equiv_matrix _ _).to_fun (mul_map α b)) (mul_map α c)],

end-/

lemma norm_base (a : α) : field_norm α β (algebra_map β a) = a ^ findim α β := sorry

lemma norm_zero : field_norm α β 0 = 0 := sorry

lemma norm_zero_iff_zero (b : β) : field_norm α β b = 0 ↔ b = 0 := sorry

end field_norm

section minimal_polynomial

open polynomial

section
variables (α : Type u) [comm_ring α] [division_ring α] [decidable_eq α]
variables (β : Type v) [discrete_field β] [algebra α β] --[field_extension α β]
variables (b : β)

/-- The ideal of polynomial over α that vanish at b. -/
def vanishing_ideal : ideal (polynomial α) := is_ring_hom.ker (aeval α β b)

/-- A minimal polynomial for b is a non-zero monic polynomial vanishing at b of minimal degree. -/
class is_minimal_polynomial (p : polynomial α) : Prop :=
(vanish : p ∈ vanishing_ideal α β b)
(monic : p.monic)
(nonzero : p ≠ 0)
(minimal : ∀ q ∈ (vanishing_ideal α β b), q ≠ 0 → degree p ≤ degree q)

end

variables {α : Type u} [comm_ring α] [division_ring α] [decidable_eq α]
variables {β : Type v} [discrete_field β] [algebra α β] --[field_extension α β]
variables {b : β}

set_option class.instance_max_depth 200
--set_option timeout 1000000

--set_option trace.class_instances true
variables (I : ideal (polynomial α))
#check (I : ideal (polynomial α))
#check (I : submodule (polynomial α) (polynomial α))


variables {γ : Type u} [integral_domain γ] [decidable_eq γ]
variables (J : ideal (polynomial γ))
#check J.carrier



lemma mem_polynomial_ideal (p : polynomial α) : p ∈ (vanishing_ideal α β b) ↔ aeval α β b p = 0 :=
is_add_group_hom.mem_ker _

lemma minimal_polynomial.degree_unique {p q : polynomial α}
  (hp : is_minimal_polynomial α β b p) (hq : is_minimal_polynomial α β b q) : degree p = degree q :=
le_antisymm (is_minimal_polynomial.minimal p q hq.1 hq.3) (is_minimal_polynomial.minimal q p hp.1 hp.3)

lemma minimal_polynomial.unique (p q : polynomial α)
  [hp : is_minimal_polynomial α β b p] [hq : is_minimal_polynomial α β b q] : p = q :=
have h1 : p - q ∈ vanishing_ideal α β b, from ideal.sub_mem _ hp.vanish hq.vanish,
have h2 : ¬degree p ≤ degree (p - q), from not_le_of_lt $ degree_sub_lt
  (minimal_polynomial.degree_unique hp hq) (hp.nonzero)
  (by rw [monic.def.mp hp.monic, monic.def.mp hq.monic]),
classical.by_contradiction
  (λ h, absurd (is_minimal_polynomial.minimal p (p-q) h1 (sub_ne_zero.mpr h)) h2)
#check nat.find

lemma test4 : (0 : polynomial α) ∈ vanishing_ideal α β b := submodule.zero_mem _

lemma exists_mem_ne_zero_of_ne_bot (h : vanishing_ideal α β b ≠ ⊥) :
  ∃ p : polynomial α, p ∈ (vanishing_ideal α β b) ∧ p ≠ 0 := sorry --exists_mem_ne_zero_of_ne_bot h
/-begin
  classical,
  by_contradiction hex,
  have : ∀ x ∈ vanishing_ideal α β b, (x : polynomial α) = 0, { simpa only [not_exists, not_and, not_not, ne.def] using hex },
  exact (h $ (begin ext, rw [submodule.mem_bot], split, exact this x, { intro h0, rw h0, exact submodule.zero_mem _ } end))--lattice.bot_unique $ assume s hs, (submodule.mem_bot α).2 $ this s hs)
end-/

lemma minimal_polynomial.exists_iff :
  (∃ p, is_minimal_polynomial α β b p) ↔ vanishing_ideal α β b ≠ ⊥ :=
begin
split,
{ assume h hb,
  cases h with p hp,
  have : p = 0, from (submodule.mem_bot (polynomial α)).mp (hb ▸ hp.1),
  have : p ≠ 0, from hp.nonzero,
  contradiction },
{ assume h,
  cases exists_mem_ne_zero_of_ne_bot h with q1 hq1,
  have h2 : ∃ n : ℕ, (∃ q2, (q2 ∈ vanishing_ideal α β b ∧ q2 ≠ 0) ∧ nat_degree q2 = n), from
    ⟨nat_degree q1, q1, ⟨hq1, rfl⟩⟩,
  classical,
  let m := nat.find h2,
  cases nat.find_spec h2 with q2 hq2,
  existsi (q2 / leading_coeff q2),
 }

end

end minimal_polynomial

end field_extension
