import m4r.cx algebra.homology.homology algebra.category.Module.abelian tactic.linarith

universes u v

def is_projective
  (R : Type u) [ring R] (M : Type u) [add_comm_group M] [module R M] :
-- M is the R-module on which `projective` is a predicate
  Prop := -- `projective R M` is a proposition
-- this rather obscure definition says that the map from the free R-module on
-- the set M to M splits as R-module map; it doesn't matter what the
-- actual definition is though, because we're going to make an API.
∃ s : M →ₗ[R] (M →₀ R), ∀ (m : M), finsupp.total M M R id (s m) = m

namespace function

variables {α β : Type u} (f : α → β) (hf : surjective f)

@[simp] lemma surj_inv.apply (b) : f (surj_inv hf b) = b := surj_inv_eq hf b

end function
namespace chain_complex

def pure (R M : Type u) [ring R] [add_comm_group M] [semimodule R M] :
  chain_complex (Module R) :=
  { X := λ n, if n = 0 then Module.of R M else Module.of R punit,
    d := λ n, 0,
    d_squared' := rfl }

variables {R : Type u} [ring R] (F : chain_complex (Module R))
def cx_cast (j k : ℤ) (h : j = k) : F.X j ≅ F.X k :=
{ hom := { to_fun := λ x, eq.rec x h,
    map_add' := λ x y, by cases h; refl,
    map_smul' := λ r x, by cases h; refl },
  inv := { to_fun := λ x, eq.rec x h.symm,
    map_add' := λ x y, by cases h; refl,
    map_smul' := λ r x, by cases h; refl },
  hom_inv_id' := by ext; cases h; refl,
  inv_hom_id' := by ext; cases h; refl }

@[simp] lemma cast_d_cast_eq_d (j k : ℤ) (h : j = k) (x : F.X j) :
  ((cx_cast F _ _ h).hom ≫ F.d k ≫ (cx_cast F _ _ ((add_left_inj _).2 h.symm)).hom) x = F.d j x :=
begin
  cases h,
  refl,
end

@[simp] lemma cast_d_eq_d_cast (j k : ℤ) (h : j = k) (x : F.X j) :
  ((cx_cast F _ _ h).hom ≫ F.d k) x = (F.d j ≫ (cx_cast F _ _ ((add_left_inj _).2 h)).hom) x :=
begin
  cases h,
  refl,
end

@[simp] lemma d_squared_cast (j k : ℤ) (h : j - 1 = k) (x : F.X j) :
    (F.d j ≫ (cx_cast F (j - 1) k (h ▸ rfl)).hom ≫ F.d k) x = 0 :=
begin
  have := (cast_d_eq_d_cast F (j - 1) k h (F.d j x)).symm,
  simp only [function.comp_app, Module.coe_comp] at *,
  erw [←this, linear_map.ext_iff.1 (F.d_squared j)],
  rw [linear_map.zero_apply, linear_map.map_zero],
end

-- alt def because `homological_complex.homology` is slow and I'm not sure how to prove
-- things about it.
@[reducible] def homology (R : Type u) [ring R] (F : chain_complex.{u u+1} (Module.{u} R))
  (n : ℤ) : Type u :=
((F.d (n + 1)).cod_restrict (F.d (n + 1 - 1)).ker $ λ x, linear_map.mem_ker.2 (linear_map.ext_iff.1
  (F.d_squared (n + 1)) _)).range.quotient

def d_alt (F : chain_complex (Module R)) (n : ℤ) :
  F.X (n + 1) ⟶ F.X n :=
(cx_cast F _ _ (add_sub_cancel _ _)).hom.comp (F.d (n + 1))

lemma d_alt_squared (F : chain_complex (Module R)) (n : ℤ) :
  (F.d_alt n) ≫ F.d n = 0 :=
begin
  unfold d_alt,
  ext,
  exact d_squared_cast F (n + 1) n (add_sub_cancel _ _) x,
end

def ker_cast (F : chain_complex (Module R)) (j k : ℤ) (h : j = k) :
  (F.d j).ker ≃ₗ[R] (F.d k).ker :=
linear_equiv.of_submodules (cx_cast F j k h).to_linear_equiv (F.d j).ker (F.d k).ker
begin
  ext,
  split,
  { rintro ⟨y, hym, hy⟩,
    cases h,
    rw ←hy,
    erw linear_map.mem_ker at ⊢ hym,
    rw ←hym,
    refl },
  { intro hx,
    use (F.cx_cast j k h).inv x,
    split,
    { erw linear_map.mem_ker at hx ⊢,
      cases h,
      rw ←hx,
      refl },
    { exact category_theory.coe_inv_hom_id _ x } }
end

def range_cast (F : chain_complex (Module R)) (j k : ℤ) (h : j = k) :
  (F.d j).range ≃ₗ[R] (F.d k).range :=
linear_equiv.of_submodules (cx_cast F (j - 1) (k - 1) $ by rw h).to_linear_equiv _ _
begin
  ext,
  split,
  { rintro ⟨y, ⟨z, hzm, hz⟩, hy⟩,
    cases h,
    rw [← hy, ← hz],
    exact linear_map.mem_range_self _ _ },
  { rintro ⟨y, hym, hy⟩,
    use (F.cx_cast (j - 1) (k - 1) (by rw h)).inv x,
    split,
    { rw ← hy,
      cases h,
      exact linear_map.mem_range_self _ _ },
    { exact category_theory.coe_inv_hom_id _ x } }
end

@[simp] lemma ker_cast_apply {F : chain_complex (Module R)} {j k : ℤ} (h : j = k) (x) :
  (F.ker_cast j k h x : F.X k) = eq.rec x h :=
begin
  cases h,
  refl,
end

variables (n : ℤ)

def homology_isom (F : chain_complex (Module R)) (n : ℤ) :
  homology R F n ≃ₗ[R] (((F.d_alt n).cod_restrict (F.d n).ker
    (λ x, linear_map.mem_ker.2 $ linear_map.ext_iff.1 (F.d_alt_squared n) _)).range.quotient) :=
linear_equiv.of_linear (submodule.mapq _ _ (ker_cast F _ _ (add_sub_cancel n 1)).to_linear_map
  $ begin
    rintro x ⟨y, hym, hy⟩,
    rw subtype.ext_iff at hy,
    rw linear_map.cod_restrict_apply at hy,
    rw submodule.mem_comap,
    sorry
  end)
(submodule.mapq _ _ (ker_cast F _ _ (add_sub_cancel n 1)).symm.to_linear_map sorry)
sorry sorry

noncomputable def homology_of_d_eq_zero {R : Type u} [ring R] (F : chain_complex (Module R))
  (h : ∀ n, F.d n = 0) (n : ℤ) :
  homology R F n ≃ₗ[R] F.X n :=
linear_equiv.of_bijective (submodule.liftq _ ((cx_cast F _ _ $ add_sub_cancel n 1).hom.comp
  (F.d (n + 1 - 1)).ker.subtype)
begin
  rintro x ⟨y, hym, hy⟩,
  rw [←hy, linear_map.mem_ker],
  dsimp,
  rw [h, linear_map.zero_apply, linear_map.map_zero],
end) (begin
  rw eq_bot_iff,
  intro x,
  refine quotient.induction_on' x (λ y hy, _),
  rw linear_map.mem_ker at hy,
  erw submodule.liftq_apply at hy,
  rw linear_map.comp_apply at hy,
  rw [linear_map.ker_eq_bot'.1 (submodule.ker_subtype (linear_map.ker (F.d (n + 1 - 1)))) _
    (linear_map.ker_eq_bot'.1 (linear_equiv.ker (cx_cast F _ _
    $ add_sub_cancel n 1).to_linear_equiv) _ hy), submodule.mem_bot],
  exact (submodule.mkq _).map_zero,
end)
(begin
  rw linear_map.range_eq_top,
  intro x,
  use quotient.mk' (⟨(cx_cast F _ _ (add_sub_cancel _ _)).inv x, linear_map.mem_ker.2
    $ by rw h; refl⟩ : (F.d (n + 1 - 1)).ker),
  dsimp,
  rw category_theory.coe_inv_hom_id,
end)

end chain_complex
namespace is_projective
open chain_complex
variables {R : Type u} [ring R] {M : Type u} [add_comm_group M] [module R M] (h : is_projective R M)

theorem universal_property {R A B M : Type u} [ring R] [add_comm_group M] [semimodule R M]
  (h : is_projective R M)
[add_comm_group A] [add_comm_group B]
  [module R A] [module R B] (f : A →ₗ[R] B) (g : M →ₗ[R] B) -- the R-linear maps
(hf : function.surjective f) : ∃ (h : M →ₗ[R] A), f.comp h = g :=
begin
  /- Maths proof
  M is a direct summand of R^M. The universal property says that to a set map X -> A
  we get an R-module map R^X -> A. Apply this to a noncomputable map M → A coming
  the map M → B and a random splitting of the surjection A → B,
  and we get R^M →ₗ A. Now compose with the map `s` coming from `is_projective R M`.
  This works.
  -/
  let fma : M → A := λ m, function.surj_inv hf (g m),
  -- now apply universal property to fma
  let hmlin : (M →₀ R) →ₗ[R] A := finsupp.total _ _ _ fma,
  cases h with s hs,
  use hmlin.comp s,
  ext m,
--  show f (hmlin (s m)) = _,
  have hg2 : ∀ m : M, f (fma m) = g m,
    simp [fma, function.surj_inv.apply _ hf],
  conv_rhs {rw ← hs m},
  simp [hmlin, finsupp.total_apply, hg2],
end

theorem is_projective_of_universal_property
  {R M : Type u} [ring R] [add_comm_group M] [semimodule R M]
  (huniv : ∀ {A B : Type u} [add_comm_group A] [add_comm_group B], by exactI ∀
  [module R A] [module R B], by exactI
  ∀ (f : A →ₗ[R] B) (g : M →ₗ[R] B), -- the R-linear maps
  function.surjective f → ∃ (h : M →ₗ[R] A), f.comp h = g) : is_projective R M :=
begin
  -- let f be the universal map (M →₀ R) →ₗ[R] M coming from the identity map
  -- so it's finsupp.sum
  specialize huniv (finsupp.total M M R (id : M → M)) (linear_map.id),
  specialize huniv _,
    intro m,
    use finsupp.single m 1,
    simp [finsupp.total_single],
  cases huniv with s hs,
  use s,
  rw linear_map.ext_iff at hs,
  exact hs,
end

structure projective_resolution (R : Type u) [ring R] (M : Type u)
  [add_comm_group M] [module R M] :=
(complex : chain_complex (Module R))  -- `Module R` with a capital M is the type of objects in
-- the category of R-modules.
(bounded : ∀ (n : ℤ), n < 0 → subsingleton (complex.X n)) -- The modules to the right of the
-- zeroth module are trivial.
(projective : ∀ (n : ℤ), is_projective R (complex.X n))
(resolution : ∀ (n : ℤ), homology R complex n ≃ₗ[R] (chain_complex.pure R M).X n)
-- The homology of the complex is isomorphic to `M` at 0 and trivial elsewhere.

lemma projective_of_subsingleton (R : Type u) [ring R] (M : Type u)
  [add_comm_group M] [module R M] [subsingleton M] :
is_projective R M :=
begin
  use 0,
  simp,
end

noncomputable def projective_resolution_of_projective (R : Type u) [ring R]
  (M : Type u) [add_comm_group M] [module R M] (H : is_projective R M) :
  projective_resolution R M :=
{ complex :=
  { X := λ n, if n = 0 then Module.of R M else Module.of R punit,
    d := λ n, 0,
    d_squared' := rfl },
  bounded := λ n hn, -- let n ∈ ℤ be negative
  begin
    dsimp,
    rw if_neg (int.ne_of_lt hn), -- apply the fact that n cannot be 0
    exact punit.subsingleton,
  end,
  projective := λ n,
  begin
    dsimp,
    split_ifs, -- split into the cases n = 0 and n ≠ 0
    { rwa if_pos h }, -- apply the assumptions that n = 0 and M is projective
    { rw if_neg h, -- apply the assumption n ≠ 0
      apply projective_of_subsingleton } -- apply that trivial modules are projective
  end,
  resolution := homology_of_d_eq_zero _ (λ n, rfl) } -- apply the fact that in a complex whose
  -- maps are all zero, Hₙ ≅ Cₙ for each n.

def lift {M N : Type u} [add_comm_group M] [add_comm_group N] [module R M]
  [module R N] (F : projective_resolution R M) (G : projective_resolution R N)
  (f : M →ₗ[R] N) :
  F.complex ⟶ G.complex :=
{ f := sorry,
  comm' := sorry }

theorem lift_comp {M N : Type u} [add_comm_group M] [add_comm_group N] [module R M]
  [module R N] (F : projective_resolution R M) (G : projective_resolution R N)
  (f : M →ₗ[R] N) : sorry := sorry

theorem lift_unique {M N : Type u} [add_comm_group M] [add_comm_group N] [module R M]
  [module R N] (F : projective_resolution R M) (G : projective_resolution R N)
  (f : M →ₗ[R] N) (ϕ : F.complex ⟶ G.complex) : sorry := sorry

end is_projective
