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

variables {G M}

@[simp] lemma smul_coe_invariants (m : invariants G M) (g : G) :
  g • (m : M) = m := m.2 g

variables (G M)

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
   (by { simp only [cochain_complex.prev_nat_zero, homological_complex.d_to_eq_zero, zero_comp, exact.w, arrow.mk_hom], sorry}))
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
  add_equiv.fun_unique α β x = x default := rfl

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

lemma one_cocycle_map_one (f : one_cocycles G M) : (↑f : G → M) 1 = 0 :=
begin
  have := f.2 1 1,
  simp only [subtype.val_eq_coe, one_smul, mul_one, sub_self, zero_add] at this,
  assumption,
end

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
⟨λ ⟨x, hx⟩, ⟨x default, λ g, by convert (cochain.d_zero_apply x (λ i, g)); rw ←hx⟩,
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

abbreviation firstcoh := one_cocycles G M ⧸ (add_subgroup.inclusion
  (λ f hf, mem_one_cocycles_of_mem_one_coboundaries (⟨f, hf⟩ : one_coboundaries G M))).range

instance jhnkj : (add_subgroup.inclusion
  (λ f hf, mem_one_cocycles_of_mem_one_coboundaries (⟨f, hf⟩ : one_coboundaries G M))).range.normal := by apply_instance

def first_iso : (cochain_cx G M).homology 1 ≃+ firstcoh G M :=
((homology_of_rel (cochain_cx G M) (show 0 + 1 = 1, from rfl)
  (show 1 + 1 = 2, from rfl)).trans
  (AddCommGroup.cokernel_iso_quotient _)).AddCommGroup_iso_to_add_equiv.trans $
  quotient_add_group.equiv_quotient_of_equiv
  (((kernel_subobject_iso _).trans $
    AddCommGroup.kernel_iso_ker _).AddCommGroup_iso_to_add_equiv.trans $
  ker_equiv_one_cocycles G M) _ _ $
sorry -- the category library stumps me once again

namespace stuff

class pair {G H : Type u} [group G] [group H]
  {M N : Type u} [add_comm_group M] [add_comm_group N] [distrib_mul_action G M]
  [distrib_mul_action H N] (f : G →* H) (φ : N →+ M) :=
(compatible : ∀ (g : G) (x : N), φ (f(g) • x) = g • φ x)

@[simps] def pair_chain_map_aux  {G H : Type u} [group G] [group H]
  {M N : Type u} [add_comm_group M] [add_comm_group N] [distrib_mul_action G M]
  [distrib_mul_action H N] (f : G →* H) (φ : N →+ M) (n : ℕ) :
  ((fin n → H) → N) →+ ((fin n → G) → M) :=
{ to_fun := λ F x, φ (F (f ∘ x)),
  map_zero' := by ext; exact φ.map_zero,
  map_add' := λ x y, by ext; exact φ.map_add _ _ }

variables  (H : subgroup G) [h1 : H.normal] (g : G) (m : invariants H M)
 (h : H)

def fucksake (H : subgroup G) [h1 : H.normal] (g : G) (m : invariants H M) :
  invariants H M := ⟨g • m, λ h, by { have : (g⁻¹ * h * g) • (m : M) = m,
  by {refine m.2 (⟨g⁻¹ * h * g, _⟩ : H),
  convert subgroup.normal.conj_mem h1 (h : H) h.2 g⁻¹, rw inv_inv},
  conv_rhs {rw ←this},
  rw [←mul_smul, ←mul_assoc, mul_inv_cancel_left, mul_smul],
  refl }⟩

instance (H : subgroup G) [H.normal] :
  distrib_mul_action (G ⧸ H) (invariants H M) :=
{ smul := λ g, quotient.lift_on' g (λ (g : G), fucksake G M H g) $ λ a b hab,
  begin
    ext,
    show (a • x : M) = b • x,
    have : (a⁻¹  * b) • (x : M) = x, from x.2 (⟨a⁻¹ * b, hab⟩),
    conv_lhs {rw ←this},
    rw [←mul_smul, mul_inv_cancel_left],
  end,
  one_smul := λ x, by { ext, show ((1 : G) • x : M) = x, from one_smul _ _ },
  mul_smul := λ x y z, quotient.induction_on₂' x y $ λ v w, by {show quotient.mk' _ • z = _,
    dsimp, ext, exact mul_smul _ _ _ },
  smul_add := λ x y z, quotient.induction_on' x $ λ w, by {show quotient.mk' _ • _ = _,
    dsimp, ext, exact smul_add _ _ _ },
  smul_zero := λ x, quotient.induction_on' x $ λ y, by {dsimp, ext, exact smul_zero _ } }

instance jfdks (H : subgroup G) [H.normal] : pair (quotient_group.mk' H) (invariants H M).subtype :=
⟨λ x y, rfl⟩

instance dsadsa (H : subgroup G) : pair H.subtype (add_monoid_hom.id M) :=
⟨λ x y, rfl⟩

lemma pair_chain_map_aux_comm {G H : Type u} [group G] [group H]
  {M N : Type u} [add_comm_group M] [add_comm_group N] [distrib_mul_action G M]
  [distrib_mul_action H N] (f : G →* H) (φ : N →+ M) [pair f φ] (n : ℕ) :
  (cochain.d G M n).comp (pair_chain_map_aux f φ n)
    = (pair_chain_map_aux f φ (n + 1)).comp (cochain.d H N n) :=
begin
  ext x g,
  dsimp [d_to_fun, pair_chain_map_aux],
  simp only [φ.map_add, φ.map_sum, φ.map_zsmul, pair.compatible],
  congr,
  ext i,
  congr,
  ext j,
  dsimp,
  by_cases h : ((j : ℕ) < i),
  { simp only [F_lt_apply _ _ _ h] },
  { by_cases heq : ((j : ℕ) = i),
    { simp only [F_eq_apply _ _ _ heq, f.map_mul] },
    { simp only [F_neg_apply _ _ _ h heq] }}
end

def pair_chain_map {G H : Type u} [group G] [group H]
  {M N : Type u} [add_comm_group M] [add_comm_group N] [distrib_mul_action G M]
  [distrib_mul_action H N] (f : G →* H) (φ : N →+ M) [pair f φ] :
  cochain_cx H N ⟶ cochain_cx G M :=
{ f := λ i, pair_chain_map_aux f φ i,
  comm' := λ i j hij, by
  { cases hij,
    dsimp,
    erw [cochain_complex.of_d, cochain_complex.of_d],
    exact pair_chain_map_aux_comm f φ i }}

def pair_homology_map {G H : Type u} [group G] [group H]
  {M N : Type u} [add_comm_group M] [add_comm_group N] [distrib_mul_action G M]
  [distrib_mul_action H N] (f : G →* H) (φ : N →+ M) [pair f φ] (n : ℕ) :
  (cochain_cx H N).homology n →+ (cochain_cx G M).homology n :=
(homology_functor _ _ n).map (pair_chain_map f φ)

variables {G}

def Res (H : subgroup G) (n : ℕ) :
  (cochain_cx G M).homology n →+ (cochain_cx H M).homology n :=
pair_homology_map H.subtype (add_monoid_hom.id M) n

def Res_one (H : subgroup G) :
  firstcoh G M →+ firstcoh H M :=
((first_iso H M).to_add_monoid_hom.comp (Res M H 1)).comp (first_iso G M).symm.to_add_monoid_hom

lemma myearhurtssss (H : subgroup G) (x : one_cocycles G M) :
  (↑x ∘ H.subtype) ∈ one_cocycles H M :=
λ g h, x.2 g h

@[simp] lemma Res_one_apply (H : subgroup G) (x : one_cocycles G M) :
  Res_one M H x = (⟨↑x ∘ H.subtype, myearhurtssss _ _ _⟩ : one_cocycles H M) :=
begin
  dsimp [Res_one, Res, first_iso],
  simp only [comp_apply],
  sorry
end

def Inf (H : subgroup G) [h1 : H.normal] (n : ℕ) :
  (cochain_cx (G ⧸ H) (invariants H M)).homology n →+ (cochain_cx G M).homology n :=
pair_homology_map (quotient_group.mk' H) (invariants H M).subtype n

def Inf_one (H : subgroup G) [h1 : H.normal] :
  firstcoh (G ⧸ H) (invariants H M) →+ firstcoh G M :=
((first_iso G M).to_add_monoid_hom.comp (Inf M H 1)).comp
  (first_iso (G ⧸ H) (invariants H M)).symm.to_add_monoid_hom

lemma owww (H : subgroup G) [h1 : H.normal] (x : one_cocycles (G ⧸ H) (invariants H M)) :
  (invariants H M).subtype ∘ ↑x ∘ (coe : G → G ⧸ H)  ∈ one_cocycles G M :=
λ g h, subtype.ext_iff.1 (x.2 g h)

lemma Inf_one_apply (H : subgroup G) [h1 : H.normal] (x : one_cocycles (G ⧸ H) (invariants H M)) :
  Inf_one M H x =
    (⟨(invariants H M).subtype ∘ ↑x ∘ (coe : G → G ⧸ H), owww M H x⟩ : one_cocycles G M) :=
begin
  dsimp [Inf_one, Inf, first_iso],
  sorry
end

def ibuprofenrules (H : subgroup G) [h1 : H.normal]
  (x : one_cocycles (G ⧸ H) (invariants H M)) (m : M)
  (h : ∀ g : G, ((↑x : G ⧸ H → invariants H M) (g : G ⧸ H) : M) = g • m - m) :
  G ⧸ H → M :=
λ g, quotient.lift_on' g (λ y, y • m - m) $ λ a b hab,
begin
  dsimp,
  rw [←h a, ←h b, quotient_group.eq.2 hab],
end

def ibuprofen (H : subgroup G) [h1 : H.normal]
  (x : one_cocycles (G ⧸ H) (invariants H M)) (m : M)
  (h : ∀ g : G, ((↑x : G ⧸ H → invariants H M) (g : G ⧸ H) : M) = g • m - m) :
  G ⧸ H → invariants H M :=
λ g, ⟨ibuprofenrules M H x m h g,
begin
  intros a,
  refine g.induction_on' _,
  intro y,
  dsimp [ibuprofenrules],
  rw ←h,
  exact coe_invariants _,
end⟩

lemma Inf_ker_eq_bot_aux (H : subgroup G) [h1 : H.normal]
  (x : one_cocycles (G ⧸ H) (invariants H M)) (m : M)
  (h : ∀ g : G, ((↑x : G ⧸ H → invariants H M) (g : G ⧸ H) : M) = g • m - m) :
  m ∈ invariants H M :=
begin
  intro y,
  rw ←sub_eq_zero,
  erw ←h y,
  rw (quotient_group.eq_one_iff (y : G)).2 y.2,
  rw one_cocycle_map_one _ _, refl,
end

lemma ughhhh (H : subgroup G) [h1 : H.normal]
  (x : one_cocycles (G ⧸ H) (invariants H M)) (m : M)
  (h : ∀ g : G, ((↑x : G ⧸ H → invariants H M) (g : G ⧸ H) : M) = g • m - m) (v : G) :
  (ibuprofen M H x m h v : M) = (x : G ⧸ H → invariants H M) (v : G ⧸ H) :=
(h v).symm

lemma Inf_ker_eq_bot (H : subgroup G) [h1 : H.normal] :
  (Inf_one M H).ker = ⊥ :=
begin
  rw eq_bot_iff,
  intros x,
  refine x.induction_on' _,
  intros y hy,
  erw [add_monoid_hom.mem_ker, Inf_one_apply] at hy,
  show quotient.mk' y = 0,
  refine (quotient_add_group.eq_zero_iff y).2 _,
  obtain ⟨⟨w, hw⟩, hy'⟩ := (quotient_add_group.eq_zero_iff _).1 hy,
  obtain ⟨m, hm⟩ := hw,
  --constructor,
  have ffs := subtype.ext_iff.1 hy',
  dsimp at hy',
  let F := ibuprofen M H y m (λ g, by {rw ←hm, exact congr_fun ffs.symm g}),
  use F,
  use m,
  exact Inf_ker_eq_bot_aux _ _ y _ (λ g, by {rw ←hm, exact congr_fun ffs.symm g}),
  intro,
  ext,
  refine quotient_group.induction_on' g _,
  intro v,
  refl,
  ext g,
  refine quotient_group.induction_on' g _,
  intro v,
  have := congr_fun ffs v,
  dsimp at this,
  rw ←this,
  exact (hm v).symm,
end

end stuff

end first_cohomology
