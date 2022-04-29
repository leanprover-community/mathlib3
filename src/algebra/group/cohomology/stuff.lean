import algebra.group.cohomology.inhomog_iso

universes v u

variables (G : Type u) [group G] (M : Type u)
  [add_comm_group M] [distrib_mul_action G M]
noncomputable theory

section zeroth_cohomology

def invariants : add_subgroup M :=
{ carrier := { x | ∀ g : G, g • x = x },
  zero_mem' := λ g, smul_zero _,
  add_mem' := λ x y hx hy g, by rw [smul_add, hx, hy],
  neg_mem' := λ x hx g, by rw [smul_neg, hx] }

def invariants_map {M N : Type u} [add_comm_group M] [add_comm_group N]
  [distrib_mul_action G M] [distrib_mul_action G N] (f : M →+[G] N) :
  invariants G M →+ invariants G N :=
add_monoid_hom.cod_restrict (f.to_add_monoid_hom.comp (invariants G M).subtype)
  _ (λ x h, by { dsimp, erw [←f.map_smul, x.2 h], refl })

variables {G M}

@[simp] lemma coe_invariants {x : invariants G M} (g : G) :
  g • (x : M) = x := x.2 g

open category_theory category_theory.limits

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

def cochain_complex.Module_zeroth_iso_ker {R : Type*} [ring R] (C : cochain_complex (Module R) ℕ) :
  C.homology 0 ≅ Module.of R (C.d 0 1).ker :=
(C.zeroth.trans (homology_of_zero_left _)).trans
  ((kernel_subobject_iso _).trans (Module.kernel_iso_ker _))

def cochain_complex.Ab_zeroth_iso_ker (C : cochain_complex Ab ℕ) :
  C.homology 0 ≅ AddCommGroup.of (C.d 0 1).ker :=
(C.zeroth.trans (homology_of_zero_left _)).trans
  ((kernel_subobject_iso _).trans (AddCommGroup.kernel_iso_ker _))

open group_cohomology

def add_equiv.fun_unique (α : Type*) (β : Type*) [unique α] [has_add β] :
  (α → β) ≃+ β :=
{ map_add' := λ x y, rfl, .. equiv.fun_unique _ _ }

@[simp] lemma add_equiv.fun_unique_apply {α : Type*} {β : Type*}
  [unique α] [has_add β] (x : α → β) :
  add_equiv.fun_unique α β x = x (default _) := rfl

@[simp] lemma add_equiv.fun_unique_symm_apply {α : Type*} {β : Type*}
  [unique α] [has_add β] {y : α} (x : β) :
  (add_equiv.fun_unique α β).symm x y = x := rfl

variables (G M)

def ker_equiv_invariants : (cochain.d G M 0).ker ≃+ invariants G M :=
{ inv_fun := ((add_equiv.fun_unique (fin 0 → G) M).symm.to_add_monoid_hom.comp
    (invariants G M).subtype).cod_restrict _
  (begin
    intro x,
    rw add_monoid_hom.mem_ker,
    ext f,
    simp [cochain.d_zero_apply]
  end),
  left_inv := λ x, by ext; dsimp; exact congr_arg _ (subsingleton.elim _ _),
  right_inv := λ x, by ext; refl,
  ..((add_equiv.fun_unique (fin 0 → G) M).to_add_monoid_hom.comp
    (cochain.d G M 0).ker.subtype).cod_restrict _
  (begin
    rintros ⟨x, h'⟩ g,
    have h := congr_fun ((cochain.d G M 0).mem_ker.1 h') (λ y, g),
    rwa [cochain.d_zero_apply, pi.zero_apply, sub_eq_zero] at h,
  end) }

def zeroth : (cochain_cx G M).homology 0 ≃+ invariants G M :=
(cochain_complex.Ab_zeroth_iso_ker _).AddCommGroup_iso_to_add_equiv.trans
  (ker_equiv_invariants G M)

end zeroth_cohomology

section first_cohomology

variables (G M)

def one_cocycles : add_subgroup (G → M) :=
{ carrier := { f | ∀ (g h : G), g • f h - f (g * h) + f g = 0 },
  zero_mem' := λ g h, by simp,
  add_mem' := λ f g hf hg x y,
  begin
    replace hf := hf x y,
    replace hg := hg x y,
    simp only [smul_add, pi.add_apply] at *,
    rw [sub_add, sub_eq_zero] at hf hg,
    rw [hf, hg],
    abel,
  end,
  neg_mem' := λ f hf g h,
  begin
    replace hf := hf g h,
    rw [sub_add, sub_eq_zero] at hf,
    simp only [neg_sub_neg, pi.neg_apply, smul_neg, hf],
    abel,
  end }

variables {G M}

lemma mem_ker_iff_mem_one_cocycles (f : (fin 1 → G) → M) :
  f ∈ (cochain.d G M 1).ker ↔ (λ (g : G), f (λ i, g)) ∈ one_cocycles G M :=
⟨λ hf' g h, by
  have hf := congr_fun ((cochain.d G M 1).mem_ker.1 hf') (fin.cons g (λ y, h));
  rwa cochain.d_one_apply at hf,
λ hf, (add_monoid_hom.mem_ker _).2 $
  begin
    ext,
    rw cochain.d_one_apply,
    convert hf (x 0) (x 1),
  end⟩

lemma mem_one_cocycles_iff_mem_ker (f : G → M) :
  f ∈ one_cocycles G M ↔ (λ (i : fin 1 → G), f (i 0)) ∈ (cochain.d G M 1).ker :=
by convert (mem_ker_iff_mem_one_cocycles (λ (i : fin 1 → G), f (i 0))).symm

variables (G M)

def ker_equiv_one_cocycles :
  (cochain.d G M 1).ker ≃+ one_cocycles G M :=
let E := (add_equiv.refl M).arrow_congr (equiv.fun_unique (fin 1) G) in
{ inv_fun := (E.symm.to_add_monoid_hom.comp (one_cocycles G M).subtype).cod_restrict
  _ (by rintros ⟨f, hf⟩; exact (mem_one_cocycles_iff_mem_ker f).1 hf),
  left_inv := λ x, subtype.ext $ E.symm_apply_eq.2 $ rfl,
  right_inv := λ x, by ext; refl,
  ..(E.to_add_monoid_hom.comp (cochain.d G M 1).ker.subtype).cod_restrict _
  (by rintros ⟨f, hf⟩; exact (mem_ker_iff_mem_one_cocycles f).1 hf) }

def one_coboundaries : add_subgroup (G → M) :=
{ carrier := { f | ∃ (m : M), ∀ g : G, (f : G → M) g = g • m - m },
  zero_mem' := ⟨0, λ g, by simp⟩,
  add_mem' := λ x y ⟨m, hm⟩ ⟨n, hn⟩, ⟨m + n, λ g,
  begin
    dsimp,
    rw [hm g, hn g, smul_add],
    abel,
  end⟩,
  neg_mem' := λ x ⟨m, hm⟩, ⟨-m, λ g, by simp [hm g]⟩ }

variables {G M}

lemma mem_one_cocycles_of_mem_one_coboundaries (f : one_coboundaries G M) :
  (f : G → M) ∈ one_cocycles G M :=
λ g h, by rcases f with ⟨f, m, hf⟩; simp [smul_sub, mul_smul, hf]

lemma mem_range_iff_mem_one_coboundaries (f : (fin 1 → G) → M) :
  f ∈ (cochain.d G M 0).range ↔ (λ g : G, f (λ i, g)) ∈ one_coboundaries G M :=
⟨λ ⟨x, hx⟩, ⟨x (default _), λ g, by convert (cochain.d_zero_apply x (λ i, g)); rw ←hx⟩,
λ ⟨m, hm⟩, ⟨λ i, m,
begin
  ext,
  rw [cochain.d_zero_apply, ←hm (x 0)],
  dsimp,
  congr,
  ext y,
  rw subsingleton.elim 0 y,
end⟩⟩

lemma mem_one_coboundaries_iff_mem_range (f : G → M) :
  f ∈ one_coboundaries G M ↔ (λ i : fin 1 → G, f (i 0)) ∈ (cochain.d G M 0).range :=
by convert (mem_range_iff_mem_one_coboundaries (λ i : fin 1 → G, f (i 0))).symm

variables (G M)

def range_equiv_one_coboundaries :
  (cochain.d G M 0).range ≃+ one_coboundaries G M :=
let E := (add_equiv.refl M).arrow_congr (equiv.fun_unique (fin 1) G) in
{ inv_fun := (E.symm.to_add_monoid_hom.comp (one_coboundaries G M).subtype).cod_restrict _
  (by rintros ⟨f, hf⟩; exact (mem_one_coboundaries_iff_mem_range f).1 hf),
  left_inv := λ x, subtype.ext $ E.symm_apply_eq.2 $ rfl,
  right_inv := λ x, by ext; refl,
  ..(E.to_add_monoid_hom.comp (cochain.d G M 0).range.subtype).cod_restrict
    _ (by rintros ⟨f, hf⟩; exact (mem_range_iff_mem_one_coboundaries f).1 hf) }

open category_theory category_theory.limits

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

def first : (cochain_cx G M).homology 1 ≃+ one_cocycles G M ⧸ (add_subgroup.inclusion
  (λ f hf, mem_one_cocycles_of_mem_one_coboundaries (⟨f, hf⟩ : one_coboundaries G M))).range :=
((homology_of_rel (cochain_cx G M) (show 0 + 1 = 1, from rfl)
  (show 1 + 1 = 2, from rfl)).trans
  (AddCommGroup.cokernel_iso_quotient _)).AddCommGroup_iso_to_add_equiv.trans $
  quotient_add_group.equiv_quotient_of_equiv
  (((kernel_subobject_iso _).trans $
    AddCommGroup.kernel_iso_ker _).AddCommGroup_iso_to_add_equiv.trans $
  ker_equiv_one_cocycles G M) _ _ $
sorry -- the category library stumps me once again


end first_cohomology
