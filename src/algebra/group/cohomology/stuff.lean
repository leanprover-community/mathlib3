import algebra.group.cohomology.ext

universes v u

variables (G : Type u) [group G] (M : Type u) [add_comm_group M] [distrib_mul_action G M]
noncomputable theory
def invariants : add_subgroup M :=
{ carrier := { x | ∀ g : G, g • x = x },
  zero_mem' := λ g, smul_zero _,
  add_mem' := λ x y hx hy g, by rw [smul_add, hx, hy],
  neg_mem' := λ x hx g, by rw [smul_neg, hx] }

open category_theory category_theory.limits

variables {R : Type*} [ring R] (C : cochain_complex (Module R) ℕ)
#check preadditive
open_locale zero_object

def cochain_complex.zeroth {V : Type u} [category.{v} V] [has_zero_object V]
  [has_zero_morphisms V] [has_kernels V] [has_images V] [has_cokernels V]
  (C : cochain_complex V ℕ) :
  C.homology 0 ≅ homology (0 : 0 ⟶ C.X 0) (C.d 0 1) zero_comp :=
homology.map_iso _ zero_comp
 (arrow.iso_mk (C.X_prev_iso_zero cochain_complex.prev_nat_zero) (iso.refl _)
   (by { simp only [cochain_complex.prev_nat_zero, homological_complex.d_to_eq_zero, zero_comp, exact.w, arrow.mk_hom], }))
 (arrow.iso_mk (iso.refl _) (C.X_next_iso rfl) (by {simp only [iso.refl_hom, arrow.mk_hom,
   category.id_comp, homological_complex.d_from_comp_X_next_iso] }))
  (by { simp only [iso.refl_hom, arrow.iso_mk_hom_left, arrow.iso_mk_hom_right], refl })

def cochain_complex.zeroth_iso_ker {R : Type*} [ring R] (C : cochain_complex (Module R) ℕ) :
  C.homology 0 ≅ Module.of R (C.d 0 1).ker :=
(C.zeroth.trans (homology_of_zero_left _)).trans
  ((kernel_subobject_iso _).trans (Module.kernel_iso_ker _))

open group_cohomology


--why don't these coercions compose....
/-variables (x : (cochain_succ.complex G M).X 0) (g : fin 1 → G)
  (y : cochain_succ G M 1)
#check y g
--#check x g
#check (x : cochain_succ G M 1)
--#check (x : cochain_succ G M 1) g
--#check (x : (fin 1 → G) → M) g-/

instance (n : ℕ) : has_coe_to_fun ((cochain_succ.complex G M).X n)
  (λ _, (fin (n + 1) → G) → M) :=
{ coe := cochain_succ.to_fun }

lemma cochain_succ.d_zero (x : (cochain_succ.complex G M).X 0) (g : fin 2 → G) :
  cochain_succ.d rfl x g = x (λ i : fin 1, g (fin.delta rfl 0 i)) - x (λ i : fin 1, g (fin.delta rfl 1 i)) :=
begin
  unfold cochain_succ.d,
  simp only [cochain_succ.int_smul_apply, add_monoid_hom.coe_mk,
    cochain_succ.coe_eval, zero_add],
  rw finset.range_succ,
  simp only [nat.one_ne_zero, finset.sum_insert, pow_one, one_zsmul, not_false_iff, finset.mem_singleton, finset.sum_singleton,
  neg_smul, finset.range_one, pow_zero],
  rw sub_eq_add_neg, rw add_comm,
end

@[simps] def cochain_succ.eval_hom (n : ℕ) (x : fin n → G) :
  cochain_succ G M n →+ M :=
{ to_fun := λ f, f x,
  map_zero' := rfl,
  map_add' := λ f g, rfl }

@[simps] def cochain_succ.const_hom (n : ℕ) :
  invariants G M →+ cochain_succ G M n :=
{ to_fun := λ m,
  { to_fun := λ f, m,
    smul_apply' := λ g f, m.2 g },
  map_zero' := rfl,
  map_add' := λ f g, rfl }

lemma yah (x : cochain_succ G M 1) (h : (cochain_succ.complex G M).d 0 1 x = 0)
  (f g : fin 1 → G) : x f = x g :=
begin
  symmetry,
  rw cochain_succ.ext_iff' at h,
  rw ←sub_eq_zero,
  convert h (fin.cons (f 0) g),
  erw [cochain_complex.of_d, cochain_succ.d_zero],
  congr,
  all_goals {ext y, rw subsingleton.elim y 0 },
  { rw fin.cons_delta_zero_apply g (f 0) },
  { rw ←cons_delta_two_apply g (f 0) 0,
    congr, }
end

def ker_to_invar : ((cochain_succ.complex G M).d 0 1).ker →+
  invariants G M :=
add_monoid_hom.cod_restrict ((cochain_succ.eval_hom G M 1 1).to_int_linear_map.dom_restrict
  ((cochain_succ.complex G M).d 0 1).ker).to_add_monoid_hom _ $ λ ⟨x, h⟩ g,
begin
  show g • (x 1) = x 1,
  rwa [x.smul_apply, yah],
end

def invar_to_ker : invariants G M →+ ((cochain_succ.complex G M).d 0 1).ker :=
add_monoid_hom.cod_restrict (cochain_succ.const_hom G M 1) ((cochain_succ.complex G M).d 0 1).ker.to_add_subgroup $
begin
  rintro ⟨x, h⟩,
  erw [linear_map.mem_ker, cochain_complex.of_d],
  dsimp,
  ext,
  rw cochain_succ.d_zero,
  exact sub_self _,
end

def ker_equiv_invar : ((cochain_succ.complex G M).d 0 1).ker ≃+ invariants G M :=
{ inv_fun := invar_to_ker G M,
  left_inv := λ x, by {unfold invar_to_ker ker_to_invar, dsimp, ext, simp only [cochain_succ.const_hom_apply_to_fun,
    add_subgroup.coe_mk],
    rw yah,
    exact x.2 },
  right_inv := λ x, subtype.coe_eta _ _,
  .. ker_to_invar G M }

def add_equiv.to_int_linear_equiv {M : Type*} {N : Type*} [add_comm_group M]
  [add_comm_group N] (f : M ≃+ N) :
  M ≃ₗ[ℤ] N :=
{ inv_fun := f.inv_fun,
  left_inv := λ x, f.left_inv x,
  right_inv := λ x, f.right_inv x, .. f.to_add_monoid_hom.to_int_linear_map }

def zeroth : (cochain_succ.complex G M).homology 0 ≃+ (invariants G M) :=
(cochain_complex.zeroth_iso_ker _).to_linear_equiv.to_add_equiv.trans (ker_equiv_invar G M)
