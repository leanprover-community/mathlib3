import linear_algebra.quadratic_form.basic
.

universes u v w
variables {S : Type*}
variables {R : Type*} {M : Type*}

variables (R M)

namespace bilin_form

section semiring
variables [comm_semiring R] [add_comm_monoid M] [module R M]

/-- The symmetric bilinear form defined as `B (f, x) (g, y) = f y + g x`. -/
@[simps]
def dual_prod : bilin_form R (module.dual R M × M) :=
linear_map.to_bilin $
  (linear_map.applyₗ.comp (linear_map.snd R (module.dual R M) M)).compl₂
    (linear_map.fst R (module.dual R M) M) +
  ((linear_map.applyₗ.comp (linear_map.snd R (module.dual R M) M)).compl₂
    (linear_map.fst R (module.dual R M) M)).flip

lemma is_symm_dual_prod : (dual_prod R M).is_symm :=
λ x y, add_comm _ _

end semiring

section ring
variables [comm_ring R] [add_comm_group M] [module R M]

@[simp] lemma prod.map_injective {α β γ δ} [nonempty α] [nonempty β] {f : α → γ} {g : β → δ} :
  function.injective (prod.map f g) ↔ function.injective f ∧ function.injective g :=
⟨λ h, ⟨λ a₁ a₂ ha, begin
  inhabit β,
  injection @h (a₁, default) (a₂, default) (congr_arg (λ c : γ, prod.mk c (g default)) ha : _),
end, λ b₁ b₂ hb, begin
  inhabit α,
  injection @h (default, b₁) (default, b₂) (congr_arg (prod.mk (f default)) hb : _),
end⟩, λ h, h.1.prod_map h.2⟩

lemma prod.map_surjective {α β γ δ} [nonempty γ] [nonempty δ] {f : α → γ} {g : β → δ} :
  function.surjective (prod.map f g) ↔ function.surjective f ∧ function.surjective g :=
⟨λ h, ⟨λ c, begin
  inhabit δ,
  obtain ⟨⟨a, b⟩, h⟩ := h (c, default),
  exact ⟨a, congr_arg prod.fst h⟩,
end, λ d, begin
  inhabit γ,
  obtain ⟨⟨a, b⟩, h⟩ := h (default, d),
  exact ⟨b, congr_arg prod.snd h⟩,
end⟩, λ h, h.1.prod_map h.2⟩

lemma prod.map_bijective {α β γ δ} [nonempty α] [nonempty β] [nonempty γ] [nonempty δ] {f : α → γ}
  {g : β → δ} :
  function.bijective (prod.map f g) ↔ function.bijective f ∧ function.bijective g :=
(prod.map_injective.and prod.map_surjective).trans $ and_and_and_comm _ _ _ _

lemma nondenerate_dual_prod : (dual_prod R M).nondegenerate ↔ function.bijective (module.dual.eval R M) :=
begin
  classical,
  rw nondegenerate_iff_ker_eq_bot,
  rw linear_map.ker_eq_bot,
  let e := (linear_equiv.prod_comm R _ _) ≪≫ₗ (module.dual_prod_dual_equiv_dual R (module.dual R M) M),
  let h_d := e.symm.to_linear_map.comp (dual_prod R M).to_lin,
  refine (function.injective.of_comp_iff e.symm.injective (dual_prod R M).to_lin).symm.trans _,
  rw [←linear_equiv.coe_to_linear_map, ←linear_map.coe_comp],
  change function.injective h_d ↔ _,
  /-
  h_d is represented by the matrix

  !![[0, dual.eval],
     [1, 0]]

  (TODO: is it? Don't we need a basis to make that claim)
  -/
  have : h_d = linear_map.prod_map (linear_map.id) (module.dual.eval R M),
  { refine linear_map.ext (λ x, prod.ext _ _),
    { ext,
      dsimp [h_d, module.dual.eval, linear_equiv.prod_comm],
      simp },
    { ext,
      dsimp [h_d, module.dual.eval, linear_equiv.prod_comm],
      simp } },
  rw [this],
  dsimp [linear_map.prod_map],
  refine prod.map_injective.trans _,
  /- Therefore it is invertible iff `dual.eval` is -/
  sorry
end

end monoid


lemma nondenerate_dual_prod [field R] [add_comm_group M] [module R M]
  [finite_dimensional R M] : (dual_prod R M).nondegenerate :=
begin
  classical,
  rw nondegenerate_iff_ker_eq_bot,
  let bM := basis.of_vector_space R M,
  let := linear_map.to_matrix
    ((finite_dimensional.fin_basis R _).prod bM)
     (finite_dimensional.fin_basis R _) (to_lin (dual_prod R M)),
  -- rw linera_map.det,
  -- intros p h,
  -- let := dual_prod R M p,
  -- have : (dual_prod R M).to_lin.to_matrix = _,
  -- rintros ⟨f, x⟩ h,
  -- rw prod.forall at h,
  -- dsimp at h,
end

#check module.dual_basis

end bilin_form

/-- The quadratic form defined as `Q (f, x) = f x`. -/
def quadratic_form.dual_prod : quadratic_form R (module.dual R M × M) :=
{ to_fun := λ p, p.1 p.2,
  to_fun_smul := λ a p, by rw [prod.smul_fst, prod.smul_snd, linear_map.smul_apply, map_smul,
                               smul_eq_mul, smul_eq_mul, mul_assoc],
  exists_companion' := ⟨bilin_form.dual_prod R M, λ p q, begin
    rw [bilin_form.dual_prod_apply, prod.fst_add, prod.snd_add, linear_map.add_apply, map_add,
      map_add, add_right_comm _ (q.1 q.2), add_comm (q.1 p.2) (p.1 q.2), ←add_assoc, ←add_assoc],
  end⟩ }
