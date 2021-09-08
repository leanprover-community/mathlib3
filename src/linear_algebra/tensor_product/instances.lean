import linear_algebra.tensor_product.lift

noncomputable theory

open_locale tensor_product big_operators

namespace tensor_product

variables {R M N T Q Q' : Type*}
variables [comm_semiring R]
variables [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid T] [add_comm_monoid Q]
variables [add_comm_monoid Q']
variables [module R M] [module R N] [module R T] [module R Q] [module R Q']
variables [is_tensor_product R M N T]


variables {M N}
section
variables (R M)

instance lid : is_tensor_product R R M M :=
{ smul_tmul' := smul_assoc,
  tmul_smul' := λ r s x, smul_comm _ _ _,
  add_tmul' := add_smul,
  tmul_add' := smul_add,
  span_tmul :=
  begin
    rw [submodule.eq_top_iff'],
    intros x,
    apply submodule.subset_span,
    exact ⟨1, x, one_smul _ _⟩,
  end,
  add_con := sorry }

/--
The base ring is a left identity for the tensor product of modules, up to linear equivalence.
-/
protected def lid : R ⊗[R] M ≃ₗ[R] M :=
linear_equiv.of_linear (lift $ linear_map.lsmul R M) (mk R R M 1)
  (linear_map.ext $ λ _, by simp)
  (ext' $ λ r m, by simp; rw [← tmul_smul, ← smul_tmul, smul_eq_mul, mul_one])
end

@[simp] lemma lid_tmul (m : M) (r : R) :
  ((tensor_product.lid R M) : (R ⊗[R] M → M)) (r ⊗[R] m) = r • m :=
begin
  dsimp [tensor_product.lid],
  simp,
end

@[simp] lemma lid_symm_apply (m : M) :
  (tensor_product.lid R M).symm m = 1 ⊗[R] m := rfl

section
variables (R M N)

/--
The tensor product of modules is commutative, up to linear equivalence.
-/
protected def comm : M ⊗[R] N ≃ₗ[R] N ⊗[R] M :=
linear_equiv.of_linear (lift (mk R N M).flip) (lift (mk R M N).flip)
  (ext' $ λ m n, rfl)
  (ext' $ λ m n, rfl)

@[simp] lemma comm_tmul (m : M) (n : N) :
  (tensor_product.comm R M N) (m ⊗[R] n) = n ⊗[R] m := rfl

@[simp] lemma comm_symm_tmul (m : M) (n : N) :
  (tensor_product.comm R M N).symm (n ⊗[R] m) = m ⊗[R] n := rfl

end

section
variables (R M)

/--
The base ring is a right identity for the tensor product of modules, up to linear equivalence.
-/
protected def rid : M ⊗ₜ[R] R ≃ₗ[R] M :=
linear_equiv.trans (tensor_product.comm R M R) (tensor_product.lid R M)
end

@[simp] lemma rid_tmul (m : M) (r : R) :
  (tensor_product.rid R M) (m ⊗[R] r) = r • m :=
begin
  dsimp [tensor_product.rid, tensor_product.comm, tensor_product.lid],
  simp,
end

@[simp] lemma rid_symm_apply (m : M) :
  (tensor_product.rid R M).symm m = m ⊗[R] 1 := rfl

open linear_map
section
variables (R M N P)

/-- The associator for tensor product of R-modules, as a linear equivalence. -/
protected def assoc : (M ⊗ₜ[R] N) ⊗ₜ[R] P ≃ₗ[R] M ⊗ₜ[R] (N ⊗ₜ[R] P) :=
begin
  refine linear_equiv.of_linear
    (lift $ lift $ comp (lcurry R _ _ _) $ mk _ _ _)
    (lift $ comp (uncurry R _ _ _) $ curry $ mk _ _ _)
    (ext $ linear_map.ext $ λ m, ext' $ λ n p, _)
    (ext $ flip_inj $ linear_map.ext $ λ p, ext' $ λ m n, _);
  repeat { rw lift.tmul <|> rw compr₂_apply <|> rw comp_apply <|>
    rw mk_apply <|> rw flip_apply <|> rw lcurry_apply <|>
    rw uncurry_apply <|> rw curry_apply <|> rw id_apply }
end
end

@[simp] lemma assoc_tmul (m : M) (n : N) (p : P) :
  (tensor_product.assoc R M N P) ((m ⊗[R] n) ⊗[R] p) = m ⊗[R] (n ⊗[R] p) := rfl

@[simp] lemma assoc_symm_tmul (m : M) (n : N) (p : P) :
  (tensor_product.assoc R M N P).symm (m ⊗[R] (n ⊗[R] p)) = (m ⊗[R] n) ⊗[R] p := rfl

/-- The tensor product of a pair of linear maps between modules. -/
def map (f : M →ₗ[R] P) (g : N →ₗ[R] Q) : M ⊗[R] N →ₗ[R] P ⊗[R] Q :=
lift $ comp (compl₂ (mk _ _ _) g) f

@[simp] lemma map_tmul (f : M →ₗ[R] P) (g : N →ₗ[R] Q) (m : M) (n : N) :
  map f g (m ⊗[R] n) = f m ⊗[R] g n :=
rfl

lemma map_range_eq_span_tmul (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
  (map f g).range = submodule.span R { t | ∃ m n, (f m) ⊗[R] (g n) = t } :=
begin
  simp only [← submodule.map_top, ← span_tmul_eq_top, submodule.map_span, set.mem_image,
    set.mem_set_of_eq],
  congr, ext t,
  split,
  { rintros ⟨_, ⟨⟨m, n, rfl⟩, rfl⟩⟩, use [m, n], simp only [map_tmul], },
  { rintros ⟨m, n, rfl⟩, use [m ⊗[R] n, m, n], simp only [map_tmul], },
end

/-- Given submodules `p ⊆ P` and `q ⊆ Q`, this is the natural map: `p ⊗[R] q → P ⊗[R] Q`. -/
@[simp] def map_incl (p : submodule R P) (q : submodule R Q) : p ⊗ₜ[R] q →ₗ[R] P ⊗ₜ[R] Q :=
map p.subtype q.subtype

section
variables {P' Q' : Type*}
variables [add_comm_monoid P'] [module R P']
variables [add_comm_monoid Q'] [module R Q']

lemma map_comp (f₂ : P →ₗ[R] P') (f₁ : M →ₗ[R] P) (g₂ : Q →ₗ[R] Q') (g₁ : N →ₗ[R] Q) :
  map (f₂.comp f₁) (g₂.comp g₁) = (map f₂ g₂).comp (map f₁ g₁) :=
ext' $ λ _ _, by simp only [linear_map.comp_apply, map_tmul]

lemma lift_comp_map (i : P →ₗ[R] Q →ₗ[R] Q') (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
  (lift i).comp (map f g) = lift ((i.comp f).compl₂ g) :=
ext' $ λ _ _, by simp only [lift.tmul, map_tmul, linear_map.compl₂_apply, linear_map.comp_apply]

local attribute [ext] ext

@[simp] lemma map_id : map (id : M →ₗ[R] M) (id : N →ₗ[R] N) = id :=
by { ext, simp only [mk_apply, id_coe, compr₂_apply, id.def, map_tmul], }

@[simp] lemma map_one : map (1 : M →ₗ[R] M) (1 : N →ₗ[R] N) = 1 := map_id

lemma map_mul (f₁ f₂ : M →ₗ[R] M) (g₁ g₂ : N →ₗ[R] N) :
  map (f₁ * f₂) (g₁ * g₂) = (map f₁ g₁) * (map f₂ g₂) :=
map_comp f₁ f₂ g₁ g₂

@[simp] lemma map_pow (f : M →ₗ[R] M) (g : N →ₗ[R] N) (n : ℕ) :
  (map f g)^n = map (f^n) (g^n) :=
begin
  induction n with n ih,
  { simp only [pow_zero, map_one], },
  { simp only [pow_succ', ih, map_mul], },
end

end

/-- If `M` and `P` are linearly equivalent and `N` and `Q` are linearly equivalent
then `M ⊗[R] N` and `P ⊗[R] Q` are linearly equivalent. -/
def congr (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) : M ⊗[R] N ≃ₗ[R] P ⊗[R] Q :=
linear_equiv.of_linear (map f g) (map f.symm g.symm)
  (ext' $ λ m n, by simp; simp only [linear_equiv.apply_symm_apply])
  (ext' $ λ m n, by simp; simp only [linear_equiv.symm_apply_apply])

@[simp] lemma congr_tmul (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) (m : M) (n : N) :
  congr f g (m ⊗[R] n) = f m ⊗[R] g n :=
rfl

@[simp] lemma congr_symm_tmul (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) (p : P) (q : Q) :
  (congr f g).symm (p ⊗[R] q) = f.symm p ⊗[R] g.symm q :=
rfl

variables (R M N P Q)

/-- A tensor product analogue of `mul_left_comm`. -/
def left_comm : M ⊗ₜ[R] (N ⊗ₜ[R] P) ≃ₗ[R] N ⊗ₜ[R] (M ⊗ₜ[R] P) :=
let e₁ := (tensor_product.assoc R M N P).symm,
    e₂ := congr (tensor_product.comm R M N) (1 : P ≃ₗ[R] P),
    e₃ := (tensor_product.assoc R N M P) in
e₁ ≪≫ₗ (e₂ ≪≫ₗ e₃)

variables {M N P Q}

@[simp] lemma left_comm_tmul (m : M) (n : N) (p : P) :
  left_comm R M N P (m ⊗[R] (n ⊗[R] p)) = n ⊗[R] (m ⊗[R] p) :=
rfl

@[simp] lemma left_comm_symm_tmul (m : M) (n : N) (p : P) :
  (left_comm R M N P).symm (n ⊗[R] (m ⊗[R] p)) = m ⊗[R] (n ⊗[R] p) :=
rfl

variables (M N P Q)

/-- This special case is worth defining explicitly since it is useful for defining multiplication
on tensor products of modules carrying multiplications (e.g., associative rings, Lie rings, ...).

E.g., suppose `M = P` and `N = Q` and that `M` and `N` carry bilinear multiplications:
`M ⊗[R] M → M` and `N ⊗[R] N → N`. Using `map`, we can define `(M ⊗[R] M) ⊗[R] (N ⊗[R] N) → M ⊗[R] N` which, when
combined with this definition, yields a bilinear multiplication on `M ⊗[R] N`:
`(M ⊗[R] N) ⊗[R] (M ⊗[R] N) → M ⊗[R] N`. In particular we could use this to define the multiplication in
the `tensor_product.semiring` instance (currently defined "by hand" using `tensor_product.mul`).

See also `mul_mul_mul_comm`. -/
def tensor_tensor_tensor_comm : (M ⊗ₜ[R] N) ⊗ₜ[R] (P ⊗ₜ[R] Q) ≃ₗ[R] (M ⊗ₜ[R] P) ⊗ₜ[R] (N ⊗ₜ[R] Q) :=
let e₁ := tensor_product.assoc R M N (P ⊗ₜ[R] Q),
    e₂ := congr (1 : M ≃ₗ[R] M) (left_comm R N P Q),
    e₃ := (tensor_product.assoc R M P (N ⊗ₜ[R] Q)).symm in
e₁ ≪≫ₗ (e₂ ≪≫ₗ e₃)

variables {M N P Q}

@[simp] lemma tensor_tensor_tensor_comm_tmul (m : M) (n : N) (p : P) (q : Q) :
  tensor_tensor_tensor_comm R M N P Q ((m ⊗[R] n) ⊗[R] (p ⊗[R] q)) = (m ⊗[R] p) ⊗[R] (n ⊗[R] q) :=
rfl

@[simp] lemma tensor_tensor_tensor_comm_symm_tmul (m : M) (n : N) (p : P) (q : Q) :
  (tensor_tensor_tensor_comm R M N P Q).symm ((m ⊗[R] p) ⊗[R] (n ⊗[R] q)) = (m ⊗[R] n) ⊗[R] (p ⊗[R] q) :=
rfl

end tensor_product

namespace linear_map

variables {R} (M) {N P Q}

/-- `ltensor M f : M ⊗[R] N →ₗ M ⊗[R] P` is the natural linear map induced by `f : N →ₗ P`. -/
def ltensor (f : N →ₗ[R] P) : M ⊗[R] N →ₗ[R] M ⊗[R] P :=
tensor_product.map id f

/-- `rtensor f M : N₁ ⊗[R] M →ₗ N₂ ⊗[R] M` is the natural linear map induced by `f : N₁ →ₗ N₂`. -/
def rtensor (f : N →ₗ[R] P) : N ⊗[R] M →ₗ[R] P ⊗[R] M :=
tensor_product.map f id

variables (g : P →ₗ[R] Q) (f : N →ₗ[R] P)

@[simp] lemma ltensor_tmul (m : M) (n : N) : f.ltensor M (m ⊗[R] n) = m ⊗[R] (f n) := rfl

@[simp] lemma rtensor_tmul (m : M) (n : N) : f.rtensor M (n ⊗[R] m) = (f n) ⊗[R] m := rfl

open tensor_product

local attribute [ext] tensor_product.ext

/-- `ltensor_hom M` is the natural linear map that sends a linear map `f : N →ₗ P` to `M ⊗ f`. -/
def ltensor_hom : (N →ₗ[R] P) →ₗ[R] (M ⊗ₜ[R] N →ₗ[R] M ⊗ₜ[R] P) :=
{ to_fun := ltensor M,
  map_add' := λ f g, by {
    ext x y, simp only [compr₂_apply, mk_apply, add_apply, ltensor_tmul, tmul_add] },
  map_smul' := λ r f, by {
    ext x y, simp only [compr₂_apply, mk_apply, tmul_smul, smul_apply, ltensor_tmul] } }

/-- `rtensor_hom M` is the natural linear map that sends a linear map `f : N →ₗ P` to `M ⊗[R] f`. -/
def rtensor_hom : (N →ₗ[R] P) →ₗ[R] (N ⊗ₜ[R] M →ₗ[R] P ⊗ₜ[R] M) :=
{ to_fun := λ f, f.rtensor M,
  map_add' := λ f g, by {
    ext x y, simp only [compr₂_apply, mk_apply, add_apply, rtensor_tmul, add_tmul] },
  map_smul' := λ r f, by {
    ext x y, simp only [compr₂_apply, mk_apply, smul_tmul, tmul_smul, smul_apply, rtensor_tmul] } }

@[simp] lemma coe_ltensor_hom :
  (ltensor_hom M : (N →ₗ[R] P) → (M ⊗ₜ[R] N →ₗ[R] M ⊗ₜ[R] P)) = ltensor M := rfl

@[simp] lemma coe_rtensor_hom :
  (rtensor_hom M : (N →ₗ[R] P) → (N ⊗ₜ[R] M →ₗ[R] P ⊗ₜ[R] M)) = rtensor M := rfl

@[simp] lemma ltensor_add (f g : N →ₗ[R] P) : (f + g).ltensor M = f.ltensor M + g.ltensor M :=
(ltensor_hom M).map_add f g

@[simp] lemma rtensor_add (f g : N →ₗ[R] P) : (f + g).rtensor M = f.rtensor M + g.rtensor M :=
(rtensor_hom M).map_add f g

@[simp] lemma ltensor_zero : ltensor M (0 : N →ₗ[R] P) = 0 :=
(ltensor_hom M).map_zero

@[simp] lemma rtensor_zero : rtensor M (0 : N →ₗ[R] P) = 0 :=
(rtensor_hom M).map_zero

@[simp] lemma ltensor_smul (r : R) (f : N →ₗ[R] P) : (r • f).ltensor M = r • (f.ltensor M) :=
(ltensor_hom M).map_smul r f

@[simp] lemma rtensor_smul (r : R) (f : N →ₗ[R] P) : (r • f).rtensor M = r • (f.rtensor M) :=
(rtensor_hom M).map_smul r f

lemma ltensor_comp : (g.comp f).ltensor M = (g.ltensor M).comp (f.ltensor M) :=
by { ext m n, simp only [compr₂_apply, mk_apply, comp_apply, ltensor_tmul] }

lemma rtensor_comp : (g.comp f).rtensor M = (g.rtensor M).comp (f.rtensor M) :=
by { ext m n, simp only [compr₂_apply, mk_apply, comp_apply, rtensor_tmul] }

lemma ltensor_mul (f g : module.End R N) : (f * g).ltensor M = (f.ltensor M) * (g.ltensor M) :=
ltensor_comp M f g

lemma rtensor_mul (f g : module.End R N) : (f * g).rtensor M = (f.rtensor M) * (g.rtensor M) :=
rtensor_comp M f g

variables (N)

@[simp] lemma ltensor_id : (id : N →ₗ[R] N).ltensor M = id := map_id

@[simp] lemma rtensor_id : (id : N →ₗ[R] N).rtensor M = id := map_id

variables {N}

@[simp] lemma ltensor_comp_rtensor (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
  (g.ltensor P).comp (f.rtensor N) = map f g :=
by simp only [ltensor, rtensor, ← map_comp, id_comp, comp_id]

@[simp] lemma rtensor_comp_ltensor (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
  (f.rtensor Q).comp (g.ltensor M) = map f g :=
by simp only [ltensor, rtensor, ← map_comp, id_comp, comp_id]

@[simp] lemma map_comp_rtensor (f : M →ₗ[R] P) (g : N →ₗ[R] Q) (f' : S →ₗ[R] M) :
  (map f g).comp (f'.rtensor _) = map (f.comp f') g :=
by simp only [ltensor, rtensor, ← map_comp, id_comp, comp_id]

@[simp] lemma map_comp_ltensor (f : M →ₗ[R] P) (g : N →ₗ[R] Q) (g' : S →ₗ[R] N) :
  (map f g).comp (g'.ltensor _) = map f (g.comp g') :=
by simp only [ltensor, rtensor, ← map_comp, id_comp, comp_id]

@[simp] lemma rtensor_comp_map (f' : P →ₗ[R] S) (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
  (f'.rtensor _).comp (map f g) = map (f'.comp f) g :=
by simp only [ltensor, rtensor, ← map_comp, id_comp, comp_id]

@[simp] lemma ltensor_comp_map (g' : Q →ₗ[R] S) (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
  (g'.ltensor _).comp (map f g) = map f (g'.comp g) :=
by simp only [ltensor, rtensor, ← map_comp, id_comp, comp_id]

variables {M}

@[simp] lemma rtensor_pow (f : M →ₗ[R] M) (n : ℕ) : (f.rtensor N)^n = (f^n).rtensor N :=
by { have h := map_pow f (id : N →ₗ[R] N) n, rwa id_pow at h, }

@[simp] lemma ltensor_pow (f : N →ₗ[R] N) (n : ℕ) : (f.ltensor M)^n = (f^n).ltensor M :=
by { have h := map_pow (id : M →ₗ[R] M) f n, rwa id_pow at h, }

end linear_map

end semiring

section ring

variables {R : Type*} [comm_semiring R]
variables {M : Type*} {N : Type*} {P : Type*} {Q : Type*} {S : Type*}

variables [add_comm_group M] [add_comm_group N] [add_comm_group P] [add_comm_group Q]
  [add_comm_group S]
variables [module R M] [module R N] [module R P] [module R Q] [module R S]

namespace tensor_product

open_locale tensor_product
open linear_map

variables (R)

/-- Auxiliary function to defining negation multiplication on tensor product. -/
def neg.aux : free_add_monoid (M × N) →+ M ⊗ₜ[R] N :=
free_add_monoid.lift $ λ p : M × N, (-p.1) ⊗[R] p.2

variables {R}

lemma neg.aux_of (m : M) (n : N) :
  neg.aux R (free_add_monoid.of (m, n)) = (-m) ⊗[R] n :=
rfl

instance : has_neg (M ⊗ₜ[R] N) :=
{ neg := (add_con_gen (tensor_product.eqv R M N)).lift (neg.aux R) $ add_con.add_con_gen_le $
    λ x y hxy, match x, y, hxy with
    | _, _, (eqv.of_zero_left n)       := (add_con.ker_rel _).2 $
        by simp_rw [add_monoid_hom.map_zero, neg.aux_of, neg_zero, zero_tmul]
    | _, _, (eqv.of_zero_right m)      := (add_con.ker_rel _).2 $
        by simp_rw [add_monoid_hom.map_zero, neg.aux_of, tmul_zero]
    | _, _, (eqv.of_add_left m₁ m₂ n)  := (add_con.ker_rel _).2 $
        by simp_rw [add_monoid_hom.map_add, neg.aux_of, neg_add, add_tmul]
    | _, _, (eqv.of_add_right m n₁ n₂) := (add_con.ker_rel _).2 $
        by simp_rw [add_monoid_hom.map_add, neg.aux_of, tmul_add]
    | _, _, (eqv.of_smul s m n)        := (add_con.ker_rel _).2 $
        by simp_rw [neg.aux_of, tmul_smul s, smul_tmul', smul_neg]
    | _, _, (eqv.add_comm x y)         := (add_con.ker_rel _).2 $
        by simp_rw [add_monoid_hom.map_add, add_comm]
    end }

protected lemma add_left_neg (x : M ⊗ₜ[R] N) : -x + x = 0 :=
tensor_product.induction_on x
  (by { rw [add_zero], apply (neg.aux R).map_zero, })
  (λ x y, by { convert (add_tmul (-x) x y).symm, rw [add_left_neg, zero_tmul], })
  (λ x y hx hy, by {
    unfold has_neg.neg sub_neg_monoid.neg,
    rw add_monoid_hom.map_add,
    ac_change (-x + x) + (-y + y) = 0,
    rw [hx, hy, add_zero], })

instance : add_comm_group (M ⊗ₜ[R] N) :=
{ neg := has_neg.neg,
  sub := _,
  sub_eq_add_neg := λ _ _, rfl,
  add_left_neg := λ x, by exact tensor_product.add_left_neg x,
  gsmul := λ n v, n • v,
  gsmul_zero' := by simp [tensor_product.zero_smul],
  gsmul_succ' := by simp [nat.succ_eq_one_add, tensor_product.one_smul, tensor_product.add_smul],
  gsmul_neg' := λ n x, begin
    change (- n.succ : ℤ) • x = - (((n : ℤ) + 1) • x),
    rw [← zero_add (-↑(n.succ) • x), ← tensor_product.add_left_neg (↑(n.succ) • x), add_assoc,
      ← add_smul, ← sub_eq_add_neg, sub_self, zero_smul, add_zero],
    refl,
  end,
  .. tensor_product.add_comm_monoid }

lemma neg_tmul (m : M) (n : N) : (-m) ⊗[R] n = -(m ⊗[R] n) := rfl

lemma tmul_neg (m : M) (n : N) : m ⊗[R] (-n) = -(m ⊗[R] n) := (mk R M N _).map_neg _

lemma tmul_sub (m : M) (n₁ n₂ : N) : m ⊗[R] (n₁ - n₂) = (m ⊗[R] n₁) - (m ⊗[R] n₂) :=
(mk R M N _).map_sub _ _

lemma sub_tmul (m₁ m₂ : M) (n : N) : (m₁ - m₂) ⊗[R] n = (m₁ ⊗[R] n) - (m₂ ⊗[R] n) :=
(mk R M N).map_sub₂ _ _ _

/--
While the tensor product will automatically inherit a ℤ-module structure from
`add_comm_group.int_module`, that structure won't be compatible with lemmas like `tmul_smul` unless
we use a `ℤ-module` instance provided by `tensor_product.left_module`.

When `R` is a `ring` we get the required `tensor_product.compatible_smul` instance through
`is_scalar_tower`, but when it is only a `semiring` we need to build it from scratch.
The instance diamond in `compatible_smul` doesn't matter because it's in `Prop`.
-/
instance compatible_smul.int [module ℤ M] [module ℤ N] : compatible_smul R ℤ M N :=
⟨λ r m n, int.induction_on r
  (by simp)
  (λ r ih, by simpa [add_smul, tmul_add, add_tmul] using ih)
  (λ r ih, by simpa [sub_smul, tmul_sub, sub_tmul] using ih)⟩

instance compatible_smul.unit {S} [monoid S] [distrib_mul_action S M] [distrib_mul_action S N]
  [compatible_smul R S M N] :
  compatible_smul R (units S) M N :=
⟨λ s m n, (compatible_smul.smul_tmul (s : S) m n : _)⟩

end tensor_product

namespace linear_map

@[simp] lemma ltensor_sub (f g : N →ₗ[R] P) : (f - g).ltensor M = f.ltensor M - g.ltensor M :=
by simp only [← coe_ltensor_hom, map_sub]

@[simp] lemma rtensor_sub (f g : N →ₗ[R] P) : (f - g).rtensor M = f.rtensor M - g.rtensor M :=
by simp only [← coe_rtensor_hom, map_sub]

@[simp] lemma ltensor_neg (f : N →ₗ[R] P) : (-f).ltensor M = -(f.ltensor M) :=
by simp only [← coe_ltensor_hom, map_neg]

@[simp] lemma rtensor_neg (f : N →ₗ[R] P) : (-f).rtensor M = -(f.rtensor M) :=
by simp only [← coe_rtensor_hom, map_neg]

end linear_map

end ring
