import representation_theory.Rep
import representation_theory.basic
noncomputable theory
universes v u
variables (k G : Type u) [comm_ring k]

/-! A proof that `k[Gⁿ⁺¹]` is a free `k[G]`-module -/

open monoid_algebra (lift) (of)

section
variables [monoid G] (n : ℕ)

@[simps] def mul_action_to_ρ (H : Type*) [monoid H] [mul_action G H] :
  representation k G (monoid_algebra k H) :=
{ to_fun := λ g, finsupp.lmap_domain k k ((•) g),
  map_one' := by { ext x y, dsimp, simp },
  map_mul' := λ x y, by { ext z w, simp [mul_smul] }}

abbreviation mul_action_to_Rep (H : Type u) [monoid H] [mul_action G H] :
  Rep k G := Rep.of (mul_action_to_ρ k G H)

-- is this ok?
instance Rep.module' (V : Rep k G) : module (monoid_algebra k G) V :=
representation.as_module V.ρ

lemma Rep.smul_def {V : Type u} [add_comm_group V] [module k V] (ρ : representation k G V)
  (g : monoid_algebra k G) (x : Rep.of ρ) :
  g • x = lift k G _ ρ g x := rfl

lemma single_smul_single {H : Type u} [monoid H] [mul_action G H]
  (g : G) (x : H) (r s : k) :
  ((•) : monoid_algebra k G → mul_action_to_Rep k G H → mul_action_to_Rep k G H)
  (finsupp.single g r) (finsupp.single x s) =
  finsupp.single (g • x) (r * s) :=
begin
  rw [Rep.smul_def, monoid_algebra.lift_single],
  dsimp,
  rw [finsupp.map_domain_single, finsupp.smul_single'],
end

lemma of_smul_of {H : Type u} [monoid H] [mul_action G H] (g : G) (x : H) :
  (of k G g • of k H x : mul_action_to_Rep k G H) = of k H (g • x) :=
by simp only [monoid_algebra.of_apply, single_smul_single, one_mul]

instance Rep.smul_comm_class {V : Type u} [add_comm_group V] [module k V]
  (ρ : representation k G V) :
  smul_comm_class (monoid_algebra k G) k (Rep.of ρ) :=
@has_scalar.comp.smul_comm_class _ (monoid_algebra k G) (Rep.of ρ) k _ _ _ _

instance Rep.is_scalar_tower {V : Type u} [add_comm_group V] [module k V]
  (ρ : representation k G V) :
  is_scalar_tower k (monoid_algebra k G) (Rep.of ρ) :=
{ smul_assoc := λ x y z, by
    simp only [Rep.smul_def, alg_hom.map_smul, linear_map.smul_apply] }

lemma map_smul_of_map_smul_of {H : Type u} [monoid H]
  (ρ : representation k G (monoid_algebra k H))
  {P : Type u} [add_comm_monoid P] [module k P]
  [module (monoid_algebra k G) P] [is_scalar_tower k (monoid_algebra k G) P]
  (f : Rep.of ρ →ₗ[k] P)
  (h : ∀ (g : G) (x : H), f (of k G g • (of k H x)) = of k G g • f (of k H x))
  (g : monoid_algebra k G) (x : Rep.of ρ) : f (g • x) = g • f x :=
begin
  refine (monoid_algebra.equivariant_of_linear_of_comm f _).map_smul _ _,
  intros a b,
  refine b.induction_on (by exact h a) _ _,
  { intros s t hs ht,
    simp only [smul_add, f.map_add, hs, ht] },
  { intros r s hs,
    rw [smul_comm (_ : monoid_algebra k G), f.map_smul, hs,
      smul_comm _ (_ : monoid_algebra k G), f.map_smul];
    { apply_instance }}
end

end

variables [group G] (n : ℕ) (k G)

def cons_one_mul_hom : (fin n → G) →* (fin (n + 1) → G) :=
{ to_fun := @fin.cons n (λ i, G) 1,
  map_one' := by
  { ext,
    refine fin.induction_on x _ _,
    { rw fin.cons_zero,
      refl },
    { intros i ih,
      simp only [fin.cons_succ],
      refl }},
  map_mul' := by
  { intros x y,
    ext i,
    refine fin.induction_on i _ _,
    { rw [fin.cons_zero],
      exact (one_mul _).symm },
    { intros i ih,
      simp only [fin.cons_succ, pi.mul_apply] }}, }

/-- The hom sending `k[Gⁿ] → k[Gⁿ⁺¹]` sending `(g₁, ..., gₙ) ↦ (1, g₁, ..., gₙ)` -/
noncomputable def cons_one (n : ℕ) :
  monoid_algebra k (fin n → G) →ₐ[k] monoid_algebra k (fin (n + 1) → G) :=
monoid_algebra.map_domain_alg_hom k k (cons_one_mul_hom G n)

lemma cons_one_of {n : ℕ} (g : fin n → G) :
  cons_one k G n (of k _ g) = of k (fin (n + 1) → G) (fin.cons 1 g) :=
finsupp.map_domain_single

variables (G n)

/-- The quotient of `Gⁿ⁺¹` by the left action of `G` -/
abbreviation orbit_quot := quotient (mul_action.orbit_rel G (fin (n + 1) → G))

instance knjk : is_scalar_tower k (monoid_algebra k G) (orbit_quot G n →₀ monoid_algebra k G) :=
finsupp.is_scalar_tower _ _

/-- The map sending `g = (g₀, ..., gₙ) ∈ k[Gⁿ⁺¹]` to `g₀ • ⟦g⟧`, as an element of the free
  `k[G]`-module on the set `Gⁿ⁺¹` modulo the left action of `G`. -/
noncomputable def to_basis_aux :
  monoid_algebra k (fin (n + 1) → G) →ₗ[k] (orbit_quot G n →₀ monoid_algebra k G) :=
(@finsupp.lmap_domain (fin (n + 1) → G) (monoid_algebra k G) k
 _ _ _ (orbit_quot G n) quotient.mk').comp
(finsupp.lift (monoid_algebra (monoid_algebra k G) (fin (n + 1) → G))
  k (fin (n + 1) → G) $ λ g, finsupp.single g (finsupp.single (g 0) 1))

variables {G n}

lemma to_basis_single (g : fin (n + 1) → G) (r : k) :
  to_basis_aux k G n (finsupp.single g r)
    = finsupp.single (quotient.mk' g : orbit_quot G n) (finsupp.single (g 0) r) :=
begin
  simp [to_basis_aux]
end

variables (G n)

/-- The `k[G]`-linear map on `k[Gⁿ⁺¹]` sending `g` to `g₀ • ⟦g⟧` as an element of the free
  `k[G]`-module on the set `Gⁿ⁺¹` modulo the left action of `G`. -/
noncomputable def to_basis :
  mul_action_to_Rep k G (fin (n + 1) → G) →ₗ[monoid_algebra k G] (orbit_quot G n →₀ monoid_algebra k G) :=
monoid_algebra.equivariant_of_linear_of_comm (to_basis_aux k G n) $ λ h y,
begin
  refine map_smul_of_map_smul_of _ _ _ _ _ _ _,
  intros,
  rw of_smul_of,
  simp [to_basis_single, @quotient.sound' _ (mul_action.orbit_rel G (fin (n + 1) → G))
     _ _ (set.mem_range_self g)],
end


/-- Inverse of `to_basis` from the free `k[G]`-module on `Gⁿ⁺¹/G` to `k[Gⁿ⁺¹]`,
  sending `⟦g⟧ ∈ Gⁿ⁺¹/G` to `g₀⁻¹ • g ∈ k[Gⁿ⁺¹]` -/
def of_basis : (orbit_quot G n →₀ (monoid_algebra k G))
  →ₗ[monoid_algebra k G] mul_action_to_Rep k G (fin (n + 1) → G) :=
finsupp.lift (mul_action_to_Rep k G (fin (n + 1) → G)) (monoid_algebra k G) (orbit_quot G n)
  (λ y, quotient.lift_on' y (λ x, of _ _ ((x 0)⁻¹ • x)) $
  begin
    rintros a b ⟨c, rfl⟩,
    dsimp,
    congr' 1,
    ext i,
    simp [mul_assoc]
  end)

instance fsddsffds : linear_map.compatible_smul (mul_action_to_Rep k G (fin n → G))
  (mul_action_to_Rep k G (fin n → G)) k
      (monoid_algebra k G) := by apply_instance

lemma left_inverse (x : mul_action_to_Rep k G (fin (n + 1) → G)) :
  of_basis k G n (to_basis k G n x) = x :=
begin
  refine add_monoid_hom.ext_iff.1 (@finsupp.add_hom_ext _ _ _ _ _
    ((of_basis k G n).comp $ to_basis k G n).to_add_monoid_hom
     (add_monoid_hom.id _) _) x,
  intros g y,
  dsimp [of_basis],
  erw to_basis_single,
  simp [single_smul_single, smul_inv_smul],
end

lemma basis_right_inverse (x : orbit_quot G n →₀ monoid_algebra k G) :
  to_basis k G n (of_basis k G n x) = x :=
begin
  refine x.induction_linear _ _ _,
  { simp only [linear_map.map_zero] },
  { intros f g hf hg,
    simp only [linear_map.map_add, hf, hg] },
  { intros a b,
    refine quotient.induction_on' a (λ c, _),
    unfold of_basis,
    simp only [quotient.lift_on'_mk', zero_smul, monoid_algebra.of_apply,
      finsupp.sum_single_index, linear_map.map_smul, finsupp.lift_apply],
    erw to_basis_single,
    simp only [finsupp.smul_single', smul_eq_mul, monoid_algebra.of_apply,
      pi.smul_apply, mul_left_inv],
    erw mul_one,
    congr' 1,
    exact quotient.sound' (mul_action.mem_orbit _ _) }
end

/-- An isomorphism of `k[Gⁿ⁺¹]` with the free `k[G]`-module on the set `Gⁿ⁺¹`
  modulo the left action of `G`, given by `to_basis`. -/
def monoid_algebra_basis : basis (orbit_quot G n)
  (monoid_algebra k G) (mul_action_to_Rep k G (fin (n + 1) → G)) :=
{ repr :=
  { inv_fun := of_basis k G n,
    left_inv := left_inverse k G n,
    right_inv := basis_right_inverse k G n, ..to_basis _ G n } }
