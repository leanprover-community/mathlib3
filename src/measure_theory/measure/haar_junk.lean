

/-
theorem tsum_smul_const {ι : Type u_1} {R : Type u_2} {M : Type u_4} [semiring R] [topological_space R] [topological_space M] [add_comm_monoid M] [module R M] [has_continuous_smul R M] {f : ι → R} [t2_space M] (hf : summable f) (a : M) :
∑' (z : ι), f z • a = (∑' (z : ι), f z) • a
-/
theorem tsum_smul_const' {ι : Type*} {R : Type*} {M : Type*}  [field R] [topological_space R]
  [topological_space M] [add_comm_group M] [module R M] [has_continuous_smul R M]
  {f : ι → R} [t2_space M] (g : M) :
  ∑' (i : ι), f i • g = (∑' (i : ι), f i) • g :=
begin
  by_cases hf : summable f,
  { exact tsum_smul_const hf _, },
  rw tsum_eq_zero_of_not_summable hf,
  simp only [zero_smul],
  by_cases hg : g = 0,
  { simp [hg], },
  have := linear_equiv.to_span_nonzero_singleton R M g hg,
  let mul_g := distrib_mul_action.to_add_equiv M g, -- wrong side multiplication... ALEX HOMEWORK!
  rw ← @summable.map_iff_of_equiv R ι R _ _ f _ _ _ _ _ _ _ at hf,
  -- _ _ f _ _ _ _ mul_g (continuous_const_smul _)
--    (continuous_const_smul _),
  rw ← @summable.map_iff_of_equiv M R M _ _ f _ _ _ _ mul_g (continuous_const_smul _)
    (continuous_const_smul _) at hf,
  apply tsum_eq_zero_of_not_summable hf,
end


lemma mul_action.automorphize_smul_right {α : Type*} {β : Type*} [group α] [mul_action α β]
  {γ : Type*} [topological_space γ] [add_comm_monoid γ] [t2_space γ] [division_ring γ]
  (f : quotient (mul_action.orbit_rel α β) → γ) {R : Type*} [topological_space R] [t2_space R]
  [semiring R] [module R γ] [has_continuous_const_smul R γ] [has_continuous_smul R γ] (g : β → R) :
  (mul_action.automorphize (g • (f ∘ quotient.mk')) : quotient (mul_action.orbit_rel α β) → γ)
  = (mul_action.automorphize g : quotient (mul_action.orbit_rel α β) → R) • f :=
begin
  ext x,
  apply quotient.induction_on' x,
  intro b,
  simp only [mul_action.automorphize, pi.smul_apply', function.comp_app],
  set π : β → quotient (mul_action.orbit_rel α β) := quotient.mk',
  have H₁ : ∀ a : α, π (a • b) = π b,
  { intro a,
    rw quotient.eq_rel,
    fconstructor,
    exact a,
    simp, },
  change ∑' a : α, g (a • b) • f (π (a • b)) = (∑' a : α, g (a • b)) • f _,
  simp_rw [H₁],
  convert tsum_smul_const' _,
  { exact _inst_22, },
  { sorry, },
  {
  fconstructor,
  { intro a,
--    rw smul_zero,
--  simp [mul_zero],
  sorry,
   },
  intros a x y,
  simp [mul_add],

    sorry,  -- ALEX HOMEWORK!
  },
  { exact _inst_15, },
end


--@[to_additive]
lemma quotient_group.automorphize_smul_right {G : Type*} [group G] {Γ : subgroup G}
  {γ : Type*} [topological_space γ] [add_comm_monoid γ] [t2_space γ]
  (f : G ⧸ Γ → γ)
  {R : Type*} [topological_space R] [t2_space R] [division_ring R]
  [module R γ] [has_continuous_const_smul R γ]
  (g : G → R) :
  (mul_action.automorphize (g • (f ∘ quotient.mk')) : G ⧸ Γ → γ)
  = (mul_action.automorphize g : G ⧸ Γ → R) • f :=
mul_action.automorphize_smul_right f g
