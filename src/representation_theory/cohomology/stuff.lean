#exit
import representation_theory.invariants
import representation_theory.cohomology.op_complex

universes v u w
--deprecated


/-variables {k : Type u} [comm_ring k] {G : Type u} [group G] {V : Type v}
  [add_comm_group V] [module k V] (ρ : representation k G V)
noncomputable theory

section zeroth_cohomology
open representation
set_option pp.universes true
variables (M : Rep k G) (x : invariants M.ρ)
-- ok.
#check (↑x : M.V)
#check has_coe.{u+1 u+1} (invariants M.ρ) M
-- i feel like i didn't used to have to define coercions like this, what's going on
instance fucksake (M : Rep k G) : has_coe (invariants M.ρ) M :=
⟨λ x, x.1⟩
/-lemma representation.comm {M N : Type u} [add_comm_group M] [add_comm_group N]
  [module k M] [module k N] {ρM : representation k G M} {ρN : representation k G N}
  (f : Rep.of ρM ⟶ Rep.of ρN) (g : G) (x : M) :
  f.hom (ρM g x) = ρN g (f.hom x) :=
linear_map.ext_iff.1 (f.comm _) _-/

lemma Rep.comm_apply {M N : Rep k G} (f : M ⟶ N) (g : G) (x : M) :
  f.hom ((M.ρ g).as_hom (x : M)) = (N.ρ g).as_hom (f.hom x : N) :=
linear_map.ext_iff.1 (f.comm _) _

lemma Rep.mem_invariants {M : Rep k G} (x : M) :
  x ∈ invariants M.ρ ↔ ∀ g : G, (M.ρ g).as_hom x = x := iff.rfl

def invariants_map {M N : Rep k G} (f : M ⟶ N) :
  invariants M.ρ →ₗ[k] invariants N.ρ :=
(f.hom.comp (invariants M.ρ).subtype).cod_restrict
  _ (λ x g, by {
    erw ←Rep.comm_apply,
  dsimp,
  rw (Rep.mem_invariants (x : M)).1 x.2 })

lemma invariants_map_apply {M N : Rep k G} (f : M ⟶ N) (x : invariants M.ρ) :
  (invariants_map f x : N) = f.hom (x : M) :=
rfl

open category_theory category_theory.limits

open_locale zero_object

def cochain_complex.zeroth {V : Type u} [category.{v} V] [has_zero_object V]
  [has_zero_morphisms V] [has_kernels V] [has_images V] [has_cokernels V]
  (C : cochain_complex V ℕ) :
  C.homology 0 ≅ homology (0 : 0 ⟶ C.X 0) (C.d 0 1) zero_comp :=
homology.map_iso _ zero_comp
 (arrow.iso_mk (C.X_prev_iso_zero cochain_complex.prev_nat_zero) (iso.refl _)
   (by { simp only [cochain_complex.prev_nat_zero, homological_complex.d_to_eq_zero,
     zero_comp, exact.w, arrow.mk_hom, comp_zero]}))
 (arrow.iso_mk (iso.refl _) (C.X_next_iso rfl) (by {simp only [iso.refl_hom, arrow.mk_hom,
   category.id_comp, homological_complex.d_from_comp_X_next_iso] }))
  (by { simp only [iso.refl_hom, arrow.iso_mk_hom_left, arrow.iso_mk_hom_right], refl })

def cochain_complex.Module_zeroth_iso_ker {R : Type*} [ring R] (C : cochain_complex (Module R) ℕ) :
  C.homology 0 ≅ Module.of R (C.d 0 1).ker :=
(C.zeroth.trans (homology_of_zero_left _)).trans
  ((kernel_subobject_iso _).trans (Module.kernel_iso_ker _))

def cochain_complex.Ab_zeroth_iso_ker (C : cochain_complex Ab ℕ) :
  C.homology 0 ≅ AddCommGroup.of (C.d 0 1).ker :=
(C.zeroth.trans (homology_of_zero_left _)).trans
  ((kernel_subobject_iso _).trans (AddCommGroup.kernel_iso_ker _))

abbreviation forfucksake : (cochain.d ρ 0).ker →ₗ[k] invariants ρ :=
((linear_equiv.fun_unique (fin 0 → G) k V).to_linear_map.comp
    (cochain.d ρ 0).ker.subtype).cod_restrict _
  (begin
    rintros ⟨x, h'⟩ g,
    have h : cochain.d ρ 0 x (λ y : fin 1, g) = 0 :=
      congr_fun (linear_map.mem_ker.1 h') (λ y : fin 1, g),
    rwa [cochain.d_zero_apply, sub_eq_zero] at h,
  end)

def ker_equiv_invariants : (cochain.d ρ 0).ker ≃ₗ[k] invariants ρ :=
{ inv_fun := ((linear_equiv.fun_unique (fin 0 → G) k V).symm.to_linear_map.comp
    (invariants ρ).subtype).cod_restrict _
  (begin
    intro x,
    rw linear_map.mem_ker,
    ext f,
    simp [cochain.d_zero_apply, (mem_invariants ρ (x : V)).1 x.2],
  end),
  left_inv := λ x, by ext; dsimp; exact congr_arg _ (subsingleton.elim _ _),
  right_inv := λ x, by ext; refl,
  ..(forfucksake ρ) }

def zeroth : (cochain_cx ρ).homology 0 ≃ₗ[k] invariants ρ :=
(cochain_complex.Module_zeroth_iso_ker _).to_linear_equiv.trans
  (ker_equiv_invariants ρ)

end zeroth_cohomology

section first_cohomology

-- why can't I find this omg
def homology_of_rel {V : Type u} [category.{v} V] [has_zero_object V]
  [has_zero_morphisms V] [has_kernels V] [has_images V] [has_cokernels V]
  {ι : Type*} {c : complex_shape ι} (C : homological_complex V c)
  {i j k : ι} (hij : c.rel i j) (hjk : c.rel j k) :
  C.homology j ≅ homology (C.d i j) (C.d j k) (C.d_comp_d i j k) :=
homology.map_iso _ _ (arrow.iso_mk (C.X_prev_iso hij) (iso.refl _)
(by simp only [C.d_to_eq hij, arrow.mk_hom]; dsimp; rw category.comp_id))
  (arrow.iso_mk (iso.refl _) (C.X_next_iso hjk)
  (by simp [C.d_from_eq hjk])) (by dsimp; refl)

example : 1 + 1 = 2 := rfl

#check (homology_of_rel (cochain_cx G M) (show 0 + 1 = 1, from rfl)
  (show 1 + 1 = 2, from rfl)).AddCommGroup_iso_to_add_equiv
#check AddCommGroup.cokernel_iso_quotient (image_to_kernel _ _ _)
#check AddCommGroup.kernel_iso_ker
#check kernel_subobject_iso
#check quotient_add_group.equiv_quotient_of_eq

-- dunno why I can't find this or the quickest way to get it
@[to_additive] def quotient_group.equiv_quotient_of_equiv {G : Type*} {H : Type*}
  [group G] [group H] (e : G ≃* H) (A : subgroup G) (B : subgroup H)
  [A.normal] [B.normal] (h : A.map e.to_monoid_hom = B) :
  G ⧸ A ≃* H ⧸ B :=
{ inv_fun := (quotient_group.map B A e.symm.to_monoid_hom $ λ x hx,
  show e.symm.to_monoid_hom x ∈ A,
  begin
    rw ←h at hx,
    rcases hx with ⟨y, hym, hy⟩,
    erw [←hy, e.symm_apply_apply],
    exact hym
  end),
  left_inv := λ y, quotient_group.induction_on' y $ λ x,
    by dsimp; rw [quotient_group.map_coe, quotient_group.map_coe];
    exact congr_arg _ (e.symm_apply_apply x),
  right_inv := λ y, quotient_group.induction_on' y $ λ x,
    by dsimp; rw [quotient_group.map_coe, quotient_group.map_coe];
    exact congr_arg _ (e.apply_symm_apply x),
  ..(quotient_group.map A B e.to_monoid_hom
  $ λ x hx, h ▸ subgroup.apply_coe_mem_map e.to_monoid_hom _ ⟨x, hx⟩) }

#check subgroup.subgroup_of
abbreviation firstcoh :=
one_cocycles ρ ⧸ ((one_coboundaries ρ).comap (one_cocycles ρ).subtype)

abbreviation firstcoh2 := one_cocycles \rh⧸ (add_subgroup.inclusion
  (λ f hf, mem_one_cocycles_of_mem_one_coboundaries (⟨f, hf⟩ : one_coboundaries G M))).range

instance fdjsdf : ((one_coboundaries G M).add_subgroup_of (one_cocycles G M)).normal := by apply_instance
instance jhnkj : (add_subgroup.inclusion
  (λ f hf, mem_one_cocycles_of_mem_one_coboundaries (⟨f, hf⟩ : one_coboundaries G M))).range.normal := by apply_instance
/-
def first_iso2 : (cochain_cx G M).homology 1 ≃+ firstcoh G M := sorry
/-(homology_of_rel (cochain_cx G M) (show 0 + 1 = 1, from rfl)
  (show 1 + 1 = 2, from rfl)).trans _-/

lemma ehoh :
  add_subgroup.map ((kernel_subobject_iso ((cochain_cx G M).d 1 2) ≪≫ AddCommGroup.kernel_iso_ker
  ((cochain_cx G M).d 1 2)).AddCommGroup_iso_to_add_equiv.trans
    (ker_equiv_one_cocycles G M)).to_add_monoid_hom (add_monoid_hom.range
  (image_to_kernel ((cochain_cx G M).d 0 1) ((cochain_cx G M).d 1 2) ((cochain_cx G M).d_comp_d _ _ _)))
    = (one_coboundaries G M).add_subgroup_of (one_cocycles G M) :=
begin
  ext,
  split,
  { rintros ⟨y, ⟨⟨z, hz⟩, hy⟩⟩,
    rw add_subgroup.mem_add_subgroup_of,
    let Z := (image_subobject_iso ((cochain_cx G M).d 0 1)).hom z,
    let ZZ := (AddCommGroup.kernel_iso_ker _).hom Z,},
  { sorry },
end
-/

def first_iso : (cochain_cx G M).homology 1 ≃+ firstcoh G M :=
((homology_of_rel (cochain_cx G M) (show 0 + 1 = 1, from rfl)
  (show 1 + 1 = 2, from rfl)).trans
  (AddCommGroup.cokernel_iso_quotient _)).AddCommGroup_iso_to_add_equiv.trans $
  quotient_add_group.equiv_quotient_of_equiv
  (((kernel_subobject_iso _).trans $
    AddCommGroup.kernel_iso_ker _).AddCommGroup_iso_to_add_equiv.trans $
  ker_equiv_one_cocycles G M) _ _ $
sorry
 -- the category library stumps me once again

end first_cohomology-/
