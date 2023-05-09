import algebra.category.Module.images
import algebra.category.Module.subobject
import representation_theory.group_cohomology.basic
import representation_theory.invariants
universes v u
noncomputable theory
open category_theory category_theory.limits

variables {V : Type u} [category.{v} V] [has_zero_morphisms V]

section
variables {A B C : V} (f : A ⟶ B) (g : B ⟶ C) [has_image f] [has_kernel g]

@[simp, reassoc] lemma π_comp_homology_of_zero_right_hom
  [has_cokernel (image_to_kernel f (0 : B ⟶ C) comp_zero)]
  [has_cokernel f] [has_cokernel (image.ι f)] [epi (factor_thru_image f)] :
  homology.π f (0 : B ⟶ C) comp_zero ≫ (homology_of_zero_right f).hom =
  (kernel_subobject (0 : B ⟶ C)).arrow ≫ cokernel.π f :=
begin
  simp only [homology.π, homology_of_zero_right, iso.trans_hom, kernel_zero_iso_source_hom,
    kernel_subobject_arrow, cokernel.map_iso_hom, cokernel_image_ι_hom, cokernel.π_desc_assoc,
    category.assoc, cokernel.π_desc],
end

@[simp, reassoc] lemma π_comp_homology_of_zero_right_inv
  [has_cokernel (image_to_kernel f (0 : B ⟶ C) comp_zero)]
  [has_cokernel f] [has_cokernel (image.ι f)] [epi (factor_thru_image f)] :
  cokernel.π f ≫ (homology_of_zero_right f).inv =
  inv (kernel_subobject (0 : B ⟶ C)).arrow ≫ homology.π f (0 : B ⟶ C) comp_zero :=
begin
  simp only [iso.comp_inv_eq, category.assoc, π_comp_homology_of_zero_right_hom,
    is_iso.inv_hom_id_assoc],
end

@[simp, reassoc] lemma homology_of_zero_left_hom_comp_ι [has_zero_object V] [has_kernels V]
  [has_image (0 : A ⟶ B)] [has_cokernel (image_to_kernel (0 : A ⟶ B) g zero_comp)] :
  (homology_of_zero_left g).hom ≫ kernel.ι g =
  homology.desc (0 : A ⟶ B) _ _ (kernel_subobject g).arrow
    (by rw [image_to_kernel_zero_left, zero_comp]) :=
begin
  rw ←cancel_epi (cokernel.π _),
  simp only [homology_of_zero_left, homology.desc, iso.trans_hom, category.assoc,
    π_comp_cokernel_iso_of_eq_hom_assoc, cokernel_zero_iso_target_hom,
    cokernel.π_desc, cokernel.π_desc_assoc, category.id_comp, kernel_subobject_arrow],
  { apply_instance },
end

end

section
variables {ι : Type*} {c : complex_shape ι} [has_kernels V] [has_images V] [has_cokernels V]
  (C : homological_complex V c) {i j k : ι} (hij : c.rel i j) (hjk : c.rel j k)

@[reassoc] lemma π_comp_homology_iso_hom :
  homology.π _ _ _ ≫ (C.homology_iso hij hjk).hom
    = (subobject.iso_of_eq _ _ (C.cycles_eq_kernel_subobject hjk)).hom ≫ homology.π _ _ _ :=
begin
  dunfold homological_complex.homology_iso homology.map_iso
    homological_complex.cycles,
  simp only [homology.π_map, subobject.iso_of_eq_hom],
  dunfold kernel_subobject_map,
  simp only [arrow.iso_mk_hom_left, iso.refl_hom],
  dsimp,
  simp only [category.comp_id (kernel_subobject (C.d_from j)).arrow],
  congr,
  ext,
  rw subobject.factor_thru_arrow,
  simp only [subobject.of_le_arrow],
end

end

section

variables [has_kernels V] [has_images V] [has_cokernels V]
  (C : chain_complex V ℕ) [epi (factor_thru_image (C.d 1 0))]

@[reassoc] lemma π_comp_homology_zero_iso_hom :
  homology.π _ _ _ ≫ C.homology_zero_iso.hom = (C.cycles 0).arrow ≫ cokernel.π _ :=
begin
  dunfold chain_complex.homology_zero_iso homology.map_iso,
  dsimp,
  simp only [homology.π_map_assoc, π_comp_homology_of_zero_right_hom,
    kernel_subobject_map_arrow_assoc, arrow.iso_mk_hom_left],
  dsimp,
  rw category.id_comp,
end

@[reassoc] lemma π_comp_homology_succ_iso_hom (n : ℕ) :
  homology.π _ _ _ ≫ (C.homology_succ_iso n).hom
  = (subobject.iso_of_eq _ _ (C.cycles_eq_kernel_subobject rfl)).hom
   ≫ homology.π _ _ _ :=
π_comp_homology_iso_hom _ _ _

end
section

variables [has_zero_object V] [has_kernels V] [has_images V]
  [has_cokernels V] (C : cochain_complex V ℕ)

@[reassoc] lemma π_comp_homology_zero_iso_hom' :
  homology.π _ _ _ ≫ C.homology_zero_iso.hom = (C.cycles_iso_kernel rfl).hom :=
begin
  dunfold cochain_complex.homology_zero_iso homology.map_iso,
  dsimp,
  simp only [homology.π_map_assoc],
  ext,
  dsimp,
  simp only [category.assoc, homology_of_zero_left_hom_comp_ι, homology.π_desc,
    kernel_subobject_map_arrow, arrow.iso_mk_hom_left],
  dsimp,
  rw category.comp_id,
  dunfold homological_complex.cycles_iso_kernel,
  simp only [iso.trans_hom, subobject.iso_of_eq_hom, category.assoc,
    kernel_subobject_arrow, subobject.of_le_arrow],
end

@[reassoc] lemma π_comp_homology_succ_iso_hom' (n : ℕ) :
  homology.π _ _ _ ≫ (C.homology_succ_iso n).hom
  = (subobject.iso_of_eq _ _ (C.cycles_eq_kernel_subobject rfl)).hom
    ≫ homology.π _ _ _ :=
π_comp_homology_iso_hom _ _ _

end

variables {k G : Type u} [comm_ring k] [group G] (A : Rep k G)

@[simp] lemma fin.mul_nth_zero_one {α : Type*} [has_mul α] (f : fin 1 → α) :
  fin.mul_nth 0 f = default :=
by ext x; exact fin.elim0 x

@[simp] lemma fin.mul_nth_zero_two {α : Type*} [has_mul α] (f : fin 2 → α) :
  fin.mul_nth 0 f = λ i, f 0 * f 1 :=
by ext x; simpa only [subsingleton.elim x 0, fin.mul_nth_eq_apply f (fin.coe_zero _),
    fin.add_nat_one, fin.succ_zero_eq_one']

namespace group_cohomology
open category_theory category_theory.limits
section zeroth

def zero_cochains_iso : (inhomogeneous_cochains A).X 0 ≅ Module.of k A :=
(linear_equiv.fun_unique (fin 0 → G) k A).to_Module_iso

def one_cochains_iso : (inhomogeneous_cochains A).X 1 ≅ Module.of k (G → A) :=
(linear_equiv.fun_congr_left k A (equiv.fun_unique (fin 1) G).symm).to_Module_iso

@[simps] def d_zero : A →ₗ[k] (G → A) :=
{ to_fun := λ m g, A.ρ g m - m,
  map_add' := λ x y, funext $ λ g, by simpa only [map_add, add_sub_add_comm],
  map_smul' := λ r x, funext $ λ g, by dsimp; rw [map_smul, smul_sub] }

@[reassoc] lemma comp_d_zero_eq : (zero_cochains_iso A).hom ≫ Module.of_hom (d_zero A)
  = (inhomogeneous_cochains A).d 0 1 ≫ (one_cochains_iso A).hom :=
begin
  ext x y,
  simp only [Module.coe_comp, function.comp_app, inhomogeneous_cochains.d_def,
    inhomogeneous_cochains.d_apply, finset.range_one, finset.sum_singleton, pow_one, neg_smul,
    one_smul, zero_cochains_iso, one_cochains_iso, linear_equiv.to_Module_iso_hom,
    linear_equiv.coe_coe, linear_equiv.fun_unique_apply, function.eval_apply,
    linear_equiv.fun_congr_left_apply, linear_map.fun_left_apply, fin.default_eq_zero,
    Module.of_hom, id.def, d_zero_apply, sub_eq_add_neg],
  congr,
end

open representation

def H_0 : Module k := Module.of k (invariants A.ρ)

lemma d_zero_ker_eq_invariants : (d_zero A).ker = invariants A.ρ :=
begin
  ext,
  simpa only [linear_map.mem_ker, mem_invariants, ←@sub_eq_zero _ _ _ x, function.funext_iff],
end

open category_theory category_theory.limits

def H_0_iso : group_cohomology A 0 ≅ H_0 A :=
(inhomogeneous_cochains A).homology_zero_iso ≪≫ kernel.map_iso _ _
  (zero_cochains_iso A) (one_cochains_iso A)
  (by rw [←iso.eq_comp_inv, category.assoc]; exact ((iso.comp_inv_eq _).2 (comp_d_zero_eq A)).symm)
  ≪≫ Module.kernel_iso_ker (Module.of_hom (d_zero A))
  ≪≫ (linear_equiv.of_eq _ _ (d_zero_ker_eq_invariants A)).to_Module_iso

@[reassoc] lemma π_comp_H_0_iso_hom_comp_subtype :
  homology.π ((inhomogeneous_cochains A).d_to 0) ((inhomogeneous_cochains A).d_from 0)
    (homological_complex.d_to_comp_d_from _ _) ≫ (H_0_iso A).hom
    ≫ Module.of_hom (invariants A.ρ).subtype
  = ((inhomogeneous_cochains A).cycles 0).arrow ≫ (zero_cochains_iso A).hom :=
begin
  simp only [←iso.comp_inv_eq, H_0_iso, iso.trans_hom, category.assoc,
    π_comp_homology_zero_iso_hom'_assoc],
  rw [←iso.eq_inv_comp, ←iso.eq_inv_comp],
  simpa only [homological_complex.cycles_iso_kernel,
  linear_equiv.to_Module_iso_hom, kernel.map_iso_inv, iso.trans_inv,
    subobject.iso_of_eq_inv, category.assoc, subobject.of_le_arrow,
    kernel_subobject_arrow', kernel.lift_ι],
end

end zeroth
section first

def two_cochains_iso : (inhomogeneous_cochains A).X 2 ≅ Module.of k (G × G → A) :=
(linear_equiv.fun_congr_left k A $ (pi_fin_two_equiv (λ i, G)).symm).to_Module_iso

@[simps] def d_one : (G → A) →ₗ[k] (G × G → A) :=
{ to_fun := λ f g, A.ρ g.1 (f g.2) - f (g.1 * g.2) + f g.1,
  map_add' := λ x y, funext $ λ g, by dsimp; rw [map_add, add_add_add_comm, add_sub_add_comm],
  map_smul' := λ r x, funext $ λ g, by dsimp; rw [map_smul, smul_add, smul_sub], }

@[reassoc] lemma comp_d_one_eq : (one_cochains_iso A).hom ≫ Module.of_hom (d_one A)
  = (inhomogeneous_cochains A).d 1 2 ≫ (two_cochains_iso A).hom :=
begin
  ext x y,
  simp only [Module.coe_comp, function.comp_app, inhomogeneous_cochains.d_def,
    inhomogeneous_cochains.d_apply, two_cochains_iso, one_cochains_iso,
    linear_equiv.to_Module_iso_hom, linear_equiv.coe_coe, linear_equiv.fun_congr_left_apply,
    linear_map.fun_left_apply, fin.default_eq_zero, Module.of_hom, d_one_apply, sub_eq_add_neg,
    pi_fin_two_equiv_symm_apply, equiv.fun_unique_symm_apply, add_assoc, finset.range_add_one],
  rw [finset.sum_insert, finset.sum_insert finset.not_mem_range_self, add_comm (-x _)],
  simp only [finset.range_zero, finset.sum_empty, neg_one_sq, one_smul, pow_one,
    fin.mul_nth_zero_two, neg_smul, add_zero],
  congr,
  { ext i,
    rw [subsingleton.elim i 0, fin.add_nat_one, fin.cons_succ, fin.cons_zero], },
  { ext i,
    simpa only [subsingleton.elim i 0, fin.mul_nth_lt_apply _
      (show ((0 : fin 1) : ℕ) < 1, from zero_lt_one)] },
  { simp only [finset.range_zero, insert_emptyc_eq, finset.mem_singleton,
      nat.one_ne_zero, not_false_iff]},
end

lemma d_one_comp_d_zero : d_one A ∘ₗ d_zero A = 0 :=
by ext; simpa only [linear_map.coe_comp, function.comp_app, d_one_apply A, d_zero_apply A, map_sub,
  map_mul, linear_map.mul_apply, sub_sub_sub_cancel_left, sub_add_sub_cancel, sub_self]

abbreviation one_cocycles := (d_one A).ker
abbreviation one_coboundaries := ((d_zero A).cod_restrict (one_cocycles A) $
λ c, linear_map.ext_iff.1 (d_one_comp_d_zero.{u} A) c).range

-- why doesn't it work...
--@[priority 1000000] instance wtf : has_coe (one_cocycles A) (G → A) := by apply_instance
variables {A}

lemma mem_one_cocycles_iff (f : G → A) :
  f ∈ one_cocycles A ↔ ∀ g : G × G, A.ρ g.1 (f g.2) - f (g.1 * g.2) + f g.1 = 0 :=
linear_map.mem_ker.trans function.funext_iff

lemma mem_one_cocycles_iff' (f : G → A) :
  f ∈ one_cocycles A ↔ ∀ g : G × G, f (g.1 * g.2) = A.ρ g.1 (f g.2) + f g.1 :=
by simp_rw [mem_one_cocycles_iff, sub_add_eq_add_sub, sub_eq_zero, eq_comm]

lemma mem_one_coboundaries_of_mem_range (f : G → A) (h : f ∈ (d_zero A).range) :
  (⟨f, by rcases h with ⟨x, rfl⟩; exact linear_map.ext_iff.1
    (d_one_comp_d_zero.{u} A) x⟩ : one_cocycles A) ∈ one_coboundaries A :=
by rcases h with ⟨x, rfl⟩; exact ⟨x, rfl⟩

lemma mem_range_of_mem_one_coboundaries (f : one_coboundaries A) :
  (f : G → A) ∈ (d_zero A).range :=
by rcases f with ⟨f, x, rfl⟩; exact ⟨x, rfl⟩

variables (A)

lemma one_coboundaries_of_trivial_eq (H : ∀ g x, A.ρ g x = x) :
  one_coboundaries A = ⊥ :=
begin
  rw eq_bot_iff,
  rintros x ⟨y, rfl⟩,
  ext,
  show A.ρ x y - y = 0,
  rw [H, sub_self],
end

-- using predicate rather than Rep.of 1 because wanna coerce Z¹(G, A) to Fun(G, A).
def one_cocycles_of_trivial_equiv (H : ∀ g x, A.ρ g x = x) :
  one_cocycles A ≃ₗ[k] (additive G →+ A) :=
{ to_fun := λ f,
  { to_fun := (f : G → A),
    map_zero' :=
    begin
      have : A.ρ 1 ((f : G → A) 1) - (f : G → A) (1 * 1) + (f : G → A) 1 = 0 :=
        (mem_one_cocycles_iff (f : G → A)).1 f.2 (1, 1),
      simpa only [H, mul_one, sub_self, zero_add, (mem_one_cocycles_iff (f : G → A)).1 f.2 (1, 1)], -- wow, simpa works on assumptions too?
    end,
    map_add' := λ x y,
    begin
      have : (f : G → A) (x * y) = A.ρ x ((f : G → A) y) + (f : G → A) x :=
        (mem_one_cocycles_iff' (f : G → A)).1 f.2 (x, y),
      simpa only [H, add_comm ((f : G → A) x)],
    end },
  map_add' := λ x y, rfl,
  map_smul' := λ r x, rfl,
  inv_fun := λ f,
  { val := f,
    property := (mem_one_cocycles_iff' f).2 (λ g, by simpa only [H, ←map_add, add_comm (f g.2)]) },
  left_inv := λ f, by ext; refl,
  right_inv := λ f, by ext; refl }

def H_1 : Module k := Module.of k (one_cocycles A ⧸ one_coboundaries A)

section
variables {R : Type u} [comm_ring R] {M N P : Module.{u} R} (f : M ⟶ N) (g : N ⟶ P)

@[reassoc] lemma Module.factor_thru_image_comp_image_iso_range_hom :
  factor_thru_image f ≫ (Module.image_iso_range f).hom
    = Module.of_hom f.range_restrict :=
begin
  simp only [←iso.eq_comp_inv, ←cancel_mono (limits.image.ι f), category.assoc,
    Module.image_iso_range_inv_image_ι, image.fac],
  ext,
  refl,
end

lemma Module.image_to_kernel_eq (w : f ≫ g = 0) : image_to_kernel f g w =
  (image_subobject_iso f ≪≫ Module.image_iso_range f).hom
    ≫ Module.of_hom (f.range.subtype.cod_restrict g.ker (λ x, linear_map.range_le_ker_iff.2 w x.2))
    ≫ (kernel_subobject_iso g ≪≫ Module.kernel_iso_ker g).inv :=
begin
  simp only [←cancel_mono (kernel_subobject g).arrow, ←cancel_epi (factor_thru_image_subobject f),
    image_to_kernel_arrow, image_subobject_arrow_comp, iso.trans_hom, iso.trans_inv, category.assoc,
    kernel_subobject_arrow', Module.kernel_iso_ker_inv_kernel_ι, factor_thru_image_subobject,
    iso.inv_hom_id_assoc, image_subobject_arrow', image.fac],
  simp only [←category.assoc, Module.factor_thru_image_comp_image_iso_range_hom],
  ext,
  refl,
end

lemma image_to_kernel_comp_eq_zero (w : f ≫ g = 0) :
  image_to_kernel f g w ≫ (kernel_subobject_iso g ≪≫ Module.kernel_iso_ker g).hom
    ≫ Module.of_hom (f.cod_restrict g.ker (λ c, linear_map.mem_ker.2
    (linear_map.ext_iff.1 w c))).range.mkq = 0 :=
begin
  simp only [Module.image_to_kernel_eq, iso.trans_hom, iso.trans_inv, category.assoc,
    iso.inv_hom_id_assoc, preadditive.is_iso.comp_left_eq_zero, Module.of_hom],
  refine linear_map.range_le_ker_iff.1 _,
  simp only [linear_map.range_eq_map, linear_map.map_cod_restrict,
    submodule.map_subtype_top, submodule.ker_mkq, le_refl _],
end

def cokernel_cocone (w : f ≫ g = 0) : cokernel_cofork (image_to_kernel f g w) :=
cokernel_cofork.of_π ((kernel_subobject_iso g ≪≫ Module.kernel_iso_ker g).hom ≫
  Module.of_hom (submodule.mkq (linear_map.cod_restrict (linear_map.ker g) f $
  λ c, linear_map.mem_ker.2 (linear_map.ext_iff.1 w c)).range))
  (image_to_kernel_comp_eq_zero f g w)

def cokernel_is_colimit (w : f ≫ g = 0) : is_colimit (cokernel_cocone f g w) :=
cofork.is_colimit.mk _
  (λ s, ((f.cod_restrict g.ker _).range).liftq
    ((kernel_subobject_iso g ≪≫ Module.kernel_iso_ker g).inv ≫ cofork.π s)
    (begin
      have := cokernel_cofork.condition s,
      simp only [Module.image_to_kernel_eq, category.assoc, ←iso.eq_inv_comp, comp_zero,
        Module.of_hom] at this,
      simp only [Module.comp_def, ←linear_map.range_le_ker_iff, linear_map.range_eq_map,
        linear_map.map_cod_restrict, submodule.map_subtype_top] at this,
      simpa only [linear_map.range_eq_map, linear_map.map_cod_restrict]
    end))
  (λ s, linear_map.ext $ λ x,
    show s.π ((kernel_subobject_iso g ≪≫ Module.kernel_iso_ker g).inv
      ((kernel_subobject_iso g ≪≫ Module.kernel_iso_ker g).hom x)) = s.π x,
    by rw iso.hom_inv_id_apply)
  (λ s m h,
    begin
    ext,
    simp only [←h],
    show m (submodule.quotient.mk x) = m (submodule.quotient.mk
      ((kernel_subobject_iso g ≪≫ Module.kernel_iso_ker g).hom
      ((kernel_subobject_iso g ≪≫ Module.kernel_iso_ker g).inv x))),
    rw iso.inv_hom_id_apply,
  end)

def homology_iso (w : f ≫ g = 0) :
  homology f g w ≅ Module.of R (g.ker ⧸ (f.cod_restrict g.ker _).range) :=
colimit.iso_colimit_cocone ⟨_, cokernel_is_colimit f g _⟩

lemma homology_iso_hom (w : f ≫ g = 0) :
  (homology_iso f g w).hom
    = cokernel.desc _ ((kernel_subobject_iso g ≪≫ Module.kernel_iso_ker g).hom
    ≫ Module.of_hom (submodule.mkq _)) (image_to_kernel_comp_eq_zero f g w) :=
begin
  dunfold homology_iso cokernel_cocone,
  simp only [←cancel_epi (cokernel.π (image_to_kernel f g w)), colimit.iso_colimit_cocone_ι_hom,
    cofork.of_π_ι_app, category.assoc, cokernel.π_desc, iso.cancel_iso_hom_left],
end

@[reassoc] lemma π_comp_homology_iso_hom' (w : f ≫ g = 0) :
  homology.π _ _ _ ≫ (homology_iso f g w).hom
  = (kernel_subobject_iso g ≪≫ Module.kernel_iso_ker g).hom ≫ Module.of_hom (submodule.mkq _) :=
by rw [homology_iso_hom, homology.π, cokernel.π_desc]

@[reassoc] lemma mkq_comp_homology_iso_inv (w : f ≫ g = 0) :
  Module.of_hom (f.cod_restrict g.ker _).range.mkq ≫ (homology_iso f g w).inv
  = (kernel_subobject_iso g ≪≫ Module.kernel_iso_ker g).inv ≫ homology.π f g w :=
by rw [iso.comp_inv_eq, category.assoc, π_comp_homology_iso_hom', iso.inv_hom_id_assoc]

def H_1_iso : group_cohomology A 1 ≅ H_1 A :=
(inhomogeneous_cochains A).homology_succ_iso 0 ≪≫
by apply (homology.map_iso _ _
  (arrow.iso_mk' ((inhomogeneous_cochains A).d 0 1) (Module.of_hom (d_zero A))
    (zero_cochains_iso A) (one_cochains_iso A) (comp_d_zero_eq A))
  (arrow.iso_mk' ((inhomogeneous_cochains A).d 1 2) (Module.of_hom (d_one A))
    (one_cochains_iso A) (two_cochains_iso A) (comp_d_one_eq A)) rfl)
  ≪≫ homology_iso (Module.of_hom $ d_zero A) (Module.of_hom $ d_one A) (d_one_comp_d_zero A)

end

-- should this be an equality of subobjects or an iso? well iso has been working well.
def one_cocycles_iso :
  ((inhomogeneous_cochains A).cycles 1 : Module.{u} k) ≅ Module.of k (one_cocycles A) :=
((inhomogeneous_cochains A).cycles_iso_kernel rfl) ≪≫ kernel.map_iso _ (Module.of_hom (d_one A))
  (one_cochains_iso A) (two_cochains_iso A) (comp_d_one_eq A).symm ≪≫ Module.kernel_iso_ker _

-- why don't kernel.map_ι and cokernel.π_map exist.... ah well
-- slow with dunfold and quick with delta.
/- Not sure whether the statement should have Module.of_hom in it; helps when you need to
rewrite lemmas about ⟶s, but the lemma Module.kernel_iso_ker_hom_ker_subtype isn't
stated this way. -/
@[reassoc] lemma one_cocycles_iso_hom_comp_subtype :
  (one_cocycles_iso A).hom ≫ Module.of_hom (one_cocycles A).subtype
  = ((inhomogeneous_cochains A).cycles 1).arrow ≫ (one_cochains_iso A).hom :=
begin
  delta one_cocycles_iso homological_complex.cycles_iso_kernel one_cocycles Module.of_hom
    kernel.map_iso kernel.map,
  simp only [category.assoc, iso.trans_hom, Module.kernel_iso_ker_hom_ker_subtype,
    kernel.lift_ι, kernel_subobject_arrow_assoc, subobject.iso_of_eq_hom,
    subobject.of_le_arrow_assoc],
end

@[reassoc] lemma one_cocycles_iso_inv_comp_arrow :
  (one_cocycles_iso A).inv ≫ ((inhomogeneous_cochains A).cycles 1).arrow
  = Module.of_hom (one_cocycles A).subtype ≫ (one_cochains_iso A).inv :=
by rw [iso.inv_comp_eq, one_cocycles_iso_hom_comp_subtype_assoc, iso.hom_inv_id, category.comp_id]

@[reassoc] lemma π_comp_H_1_iso_hom :
  homology.π _ _ _ ≫ (H_1_iso A).hom
  = (one_cocycles_iso A).hom ≫ Module.of_hom (one_coboundaries A).mkq :=
begin
  simpa only [H_1_iso, iso.trans_hom, category.assoc, π_comp_homology_succ_iso_hom'_assoc,
    homology.map_iso, homology.π_map_assoc, π_comp_homology_iso_hom',
    ←kernel_subobject_iso_comp_kernel_map_assoc],
end

@[reassoc] lemma mkq_comp_H_1_iso_inv :
  Module.of_hom (one_coboundaries A).mkq ≫ (H_1_iso A).inv
  = (one_cocycles_iso A).inv ≫ homology.π _ _ _ :=
by rw [iso.comp_inv_eq, category.assoc, π_comp_H_1_iso_hom, iso.inv_hom_id_assoc]

def H_1_of_trivial (H : ∀ g x, A.ρ g x = x) :
  H_1 A ≅ Module.of k (additive G →+ A) :=
(submodule.quot_equiv_of_eq_bot _ (one_coboundaries_of_trivial_eq A H)
  ≪≫ₗ one_cocycles_of_trivial_equiv A H).to_Module_iso

end first
section second

def three_cochains_iso : (inhomogeneous_cochains A).X 3 ≅ Module.of k (G × G × G → A) :=
(linear_equiv.fun_congr_left k A $ ((equiv.pi_fin_succ 2 G).trans
  ((equiv.refl G).prod_congr (pi_fin_two_equiv (λ i, G)))).symm).to_Module_iso

@[simps] def d_two : (G × G → A) →ₗ[k] (G × G × G → A) :=
{ to_fun := λ f g, A.ρ g.1 (f (g.2.1, g.2.2)) - f (g.1 * g.2.1, g.2.2)
    + f (g.1, g.2.1 * g.2.2) - f (g.1, g.2.1),
  map_add' := λ x y, funext $ λ g, by dsimp; rw [map_add, add_sub_add_comm (A.ρ _ _),
    add_sub_assoc, add_sub_add_comm, add_add_add_comm, add_sub_assoc, add_sub_assoc],
  map_smul' := λ r x, funext $ λ g, by dsimp; simp only [map_smul, smul_add, smul_sub] }

@[reassoc] lemma comp_d_two_eq : (two_cochains_iso A).hom ≫ Module.of_hom (d_two A)
  = (inhomogeneous_cochains A).d 2 3 ≫ (three_cochains_iso A).hom :=
begin
  ext x y,
  simp only [Module.coe_comp, function.comp_app, inhomogeneous_cochains.d_def,
    inhomogeneous_cochains.d_apply, two_cochains_iso, three_cochains_iso,
    linear_equiv.to_Module_iso_inv, linear_equiv.fun_congr_left_symm,
    linear_equiv.to_Module_iso_hom, linear_equiv.coe_coe, linear_equiv.fun_congr_left_apply,
    linear_map.fun_left_apply, Module.of_hom, d_two_apply, sub_eq_add_neg, add_assoc,
    fin.succ_zero_eq_one', pi_fin_two_equiv_symm_apply],
  rw [finset.range_succ, finset.range_succ, finset.sum_insert, finset.sum_insert
    finset.not_mem_range_self],
  { simp only [finset.range_one, finset.sum_singleton, neg_one_sq, pow_one, pow_succ _ 2,
      one_smul, mul_one, fin.mul_nth_zero_two, neg_smul],
    rw [add_comm (-x _), add_comm (x _), add_assoc (-x _)],
    congr,
    all_goals {ext x y, fin_cases x },
    { simpa only [fin.cons_zero] },
    all_goals { simpa only [fin.cons_zero, ←fin.succ_zero_eq_one, @fin.cons_succ 2 (λ i, G),
      @fin.cons_succ 1 (λ i, G), fin.mul_nth_lt_apply _ (show ((0 : fin 2) : ℕ) < 2,
      from nat.zero_lt_succ _), fin.mul_nth_lt_apply _ (show ((0 : fin 2) : ℕ) < 1,
      from nat.zero_lt_succ _), fin.mul_nth_eq_apply _ (show ((fin.succ 0 : fin 2) : ℕ) = 1,
      from rfl), fin.mul_nth_eq_apply _ (show ((0 : fin 2) : ℕ) = 0, from rfl),
      fin.mul_nth_neg_apply _ (show ¬((fin.succ 0 : fin 2) : ℕ) < 0, from nat.not_lt_zero _)
      (ne.symm zero_ne_one)] }},
  { simp only [finset.range_one, finset.mem_insert, nat.succ_succ_ne_one,
    finset.mem_singleton, bit0_eq_zero, nat.one_ne_zero, or_self, not_false_iff] },
end

lemma d_two_comp_d_one : d_two A ∘ₗ d_one A = 0 :=
show Module.of_hom (d_one A) ≫ Module.of_hom (d_two A) = _,
by simp only [(iso.eq_inv_comp _).2 (comp_d_two_eq A), (iso.eq_inv_comp _).2 (comp_d_one_eq A),
  category.assoc, iso.hom_inv_id_assoc, homological_complex.d_comp_d_assoc, zero_comp, comp_zero]

/-lemma range_d_one_le_ker_d_two : (d_one A).range ≤ (d_two A).ker :=
linear_map.range_le_ker_iff.2 $ show Module.of_hom (d_one A) ≫ Module.of_hom (d_two A) = _,
by simp only [(iso.eq_inv_comp _).2 (comp_d_two_eq A), (iso.eq_inv_comp _).2 (comp_d_one_eq A),
  category.assoc, iso.hom_inv_id_assoc, homological_complex.d_comp_d_assoc, zero_comp, comp_zero]-/

def two_cocycles := (d_two A).ker
def two_coboundaries := ((d_one A).cod_restrict (two_cocycles A) $
λ c, linear_map.ext_iff.1 (d_two_comp_d_one.{u} A) c).range

-- don't know which helpful lemmas should exist. don't know how to organise API
lemma mem_two_cocycles_iff (f : G × G → A) :
  f ∈ two_cocycles A ↔ ∀ g : G × G × G, A.ρ g.1 (f (g.2.1, g.2.2)) - f (g.1 * g.2.1, g.2.2)
    + f (g.1, g.2.1 * g.2.2) - f (g.1, g.2.1) = 0 :=
linear_map.mem_ker.trans function.funext_iff

lemma mem_two_cocycles_iff' (f : G × G → A) :
  f ∈ two_cocycles A ↔ ∀ g : G × G × G, f (g.1 * g.2.1, g.2.2) + f (g.1, g.2.1)
    = A.ρ g.1 (f (g.2.1, g.2.2)) + f (g.1, g.2.1 * g.2.2) :=
by simp_rw [mem_two_cocycles_iff, sub_eq_zero, sub_add_eq_add_sub, sub_eq_iff_eq_add,
  eq_comm, add_comm (f (prod.fst _, _))]

lemma mem_two_coboundaries_of_mem_range (f : G × G → A) (h : f ∈ (d_one A).range) :
  (⟨f, by rcases h with ⟨x, rfl⟩; exact linear_map.ext_iff.1
    (d_two_comp_d_one.{u} A) x⟩ : two_cocycles A) ∈ two_coboundaries A :=
by rcases h with ⟨x, rfl⟩; exact ⟨x, rfl⟩

lemma mem_range_of_mem_two_coboundaries (f : two_coboundaries A) :
  (f : G × G → A) ∈ (d_one A).range :=
by rcases f with ⟨f, x, rfl⟩; exact ⟨x, rfl⟩

def H_2 : Module k := Module.of k (two_cocycles A ⧸ two_coboundaries A)

def H_2_iso : group_cohomology A 2 ≅ H_2 A :=
(inhomogeneous_cochains A).homology_succ_iso 1 ≪≫
by apply (homology.map_iso _ _
(arrow.iso_mk' ((inhomogeneous_cochains A).d 1 2) (Module.of_hom (d_one A))
  (one_cochains_iso A) (two_cochains_iso A) (comp_d_one_eq A))
(arrow.iso_mk' ((inhomogeneous_cochains A).d 2 3) (Module.of_hom (d_two A))
  (two_cochains_iso A) (three_cochains_iso A) (comp_d_two_eq A)) rfl)
≪≫ homology_iso (Module.of_hom $ d_one A) (Module.of_hom $ d_two A) (d_two_comp_d_one A)

def two_cocycles_iso :
  ((inhomogeneous_cochains A).cycles 2 : Module.{u} k) ≅ Module.of k (two_cocycles A) :=
((inhomogeneous_cochains A).cycles_iso_kernel rfl) ≪≫ kernel.map_iso _ (Module.of_hom (d_two A))
  (two_cochains_iso A) (three_cochains_iso A) (comp_d_two_eq A).symm ≪≫ Module.kernel_iso_ker _

@[reassoc] lemma two_cocycles_iso_hom_comp_subtype :
  (two_cocycles_iso A).hom ≫ Module.of_hom (two_cocycles A).subtype
  = ((inhomogeneous_cochains A).cycles 2).arrow ≫ (two_cochains_iso A).hom :=
begin
  delta two_cocycles_iso homological_complex.cycles_iso_kernel two_cocycles Module.of_hom
    kernel.map_iso kernel.map,
  simp only [category.assoc, iso.trans_hom, Module.kernel_iso_ker_hom_ker_subtype,
    kernel.lift_ι, kernel_subobject_arrow_assoc, subobject.iso_of_eq_hom,
    subobject.of_le_arrow_assoc],
end

@[reassoc] lemma two_cocycles_iso_inv_comp_arrow :
  (two_cocycles_iso A).inv ≫ ((inhomogeneous_cochains A).cycles 2).arrow
  = Module.of_hom (two_cocycles A).subtype ≫ (two_cochains_iso A).inv :=
by rw [iso.inv_comp_eq, two_cocycles_iso_hom_comp_subtype_assoc, iso.hom_inv_id, category.comp_id]

@[reassoc] lemma π_comp_H_2_iso_hom :
  homology.π _ _ _ ≫ (H_2_iso A).hom
  = (two_cocycles_iso A).hom ≫ Module.of_hom (two_coboundaries A).mkq :=
begin
  simpa only [H_2_iso, iso.trans_hom, category.assoc, π_comp_homology_succ_iso_hom'_assoc,
    homology.map_iso, homology.π_map_assoc, π_comp_homology_iso_hom',
    ←kernel_subobject_iso_comp_kernel_map_assoc],
end

@[reassoc] lemma mkq_comp_H_2_iso_inv :
  Module.of_hom (two_coboundaries A).mkq ≫ (H_2_iso A).inv
  = (two_cocycles_iso A).inv ≫ homology.π _ _ _ :=
by rw [iso.comp_inv_eq, category.assoc, π_comp_H_2_iso_hom, iso.inv_hom_id_assoc]

end second
end group_cohomology
