import representation_theory.group_cohomology.low_degree

universes v u
noncomputable theory
namespace group_cohomology
open category_theory

variables {k G H : Type u} [comm_ring k] [group G] [group H]
  (A : Rep k G) (B : Rep k H) (f : G →* H) (φ : B.V →ₗ[k] A.V) (n : ℕ)

lemma map_mul_nth (j : ℕ) (g : fin (n + 1) → G) :
  f ∘ fin.mul_nth j g = fin.mul_nth j (f ∘ g) :=
begin
  ext,
  rw function.comp_app,
  by_cases (x : ℕ) < j,
  { simp only [fin.mul_nth_lt_apply _ h] },
  { by_cases h1 : (x : ℕ) = j,
    { simp only [fin.mul_nth_eq_apply _ h1, f.map_mul], },
    { simp only [fin.mul_nth_neg_apply _ h h1] }}
end

def compatible : Prop := ∀ (g : G) (x : B.V), φ (B.ρ (f g) x) = A.ρ g (φ x)

/-def compatible_chain_map_aux (n : ℕ) :
  ((fin n → H) → B.V) →ₗ[k] ((fin n → G) → A.V) :=
(φ.comp_left (fin n → G)).comp (linear_map.fun_left k B.V (λ x : fin n → G, f ∘ x))

@[simp] lemma compatible_chain_map_aux_apply (n : ℕ) (x : (fin n → H) → B.V) (g : fin n → G) :
  compatible_chain_map_aux A B f φ n x g = φ (x (f ∘ g)) := rfl-/

open representation

variables (A) (S : subgroup G)

def Inf_rep_aux [h1 : S.normal] : representation k G (invariants (A.ρ.comp S.subtype)) :=
{ to_fun := λ g, linear_map.cod_restrict _ ((A.ρ g).comp (submodule.subtype _))
  (λ x h,
  begin
    dsimp,
    rw [←one_mul (h : G), ←mul_inv_self g, mul_assoc, A.ρ.map_mul,
    ←linear_map.mul_apply, mul_assoc, ←A.ρ.map_mul],
    exact linear_map.congr_arg (x.2 (⟨g⁻¹ * h * g, by nth_rewrite 1 ←inv_inv g;
      exact subgroup.normal.conj_mem h1 (h : S) h.2 g⁻¹⟩))
  end),
  map_one' := by ext; show A.ρ 1 _ = _; simpa only [A.ρ.map_one],
  map_mul' := λ x y, by ext; show A.ρ (x * y) _ = _; simpa only [A.ρ.map_mul] }

-- general version of this needs to be in the library..
def Inf_rep [S.normal] : Rep k (G ⧸ S) :=
@Rep.of k (G ⧸ S) _ _ (invariants (A.ρ.comp S.subtype)) _ _ $
(quotient_group.con S).lift (Inf_rep_aux A S)
(λ x y h, linear_map.ext (λ w, subtype.ext $
begin
  rcases h with ⟨z, rfl⟩,
  show A.ρ (y * mul_opposite.unop z) w = A.ρ y w,
  rw A.ρ.map_mul,
  exact linear_map.congr_arg (w.2 (⟨mul_opposite.unop z, z.2⟩)),
end))

def Res_rep : Rep k S := Rep.of (A.ρ.comp S.subtype)

lemma quotient_pair (S : subgroup G) [S.normal] :
  compatible A (Inf_rep A S) (quotient_group.mk' S) (invariants (A.ρ.comp S.subtype)).subtype :=
λ x y, rfl

lemma subgroup_pair (S : subgroup G) :
  compatible (Res_rep A S) A S.subtype linear_map.id :=
λ x y, rfl

lemma rep_hom_pair {k : Type u} [comm_ring k] {G : Type u} [group G]
  {A B : Rep k G} (f : A ⟶ B) :
  compatible B A (monoid_hom.id G) f.hom :=
λ g, linear_map.ext_iff.1 (f.comm _)

/- not an aesthetically pleasing proof.
lemma pair_chain_map_aux_comm (hp : compatible A B f φ) (n : ℕ) :
  ((inhomogeneous_cochains A).d n (n + 1)).comp (compatible_chain_map_aux A B f φ n)
    = (compatible_chain_map_aux A B f φ (n + 1)).comp ((inhomogeneous_cochains B).d n (n + 1)) :=
begin
  ext x g,
  dsimp [compatible_chain_map_aux],
  simp only [inhomogeneous_cochains.d_def, inhomogeneous_cochains.d_apply,
    φ.map_add, φ.map_sum, φ.map_smul, hp (g 0)],
  dsimp,
  congr,
  ext i,
  congr,
  ext j,
  by_cases h : ((j : ℕ) < i),
  { simp only [function.comp_app, fin.mul_nth_lt_apply _ h] },
  { by_cases heq : ((j : ℕ) = i),
    { simp only [fin.mul_nth_eq_apply _ heq, f.map_mul, function.comp_app] },
    { simp only [fin.mul_nth_neg_apply _ h heq, function.comp_app] }}
end-/

@[simps] def pair_chain_map (hp : compatible A B f φ) :
  inhomogeneous_cochains B ⟶ inhomogeneous_cochains A :=
{ f := λ i, φ.comp_left (fin i → G) ∘ₗ linear_map.fun_left k B.V (λ x : fin i → G, f ∘ x),
  comm' := λ i j (hij : _ = _),
  begin
    subst hij,
    ext x g,
    simp only [Module.coe_comp, linear_map.coe_comp, function.comp_app, linear_map.comp_left_apply,
      linear_map.fun_left_apply, inhomogeneous_cochains.d_def, inhomogeneous_cochains.d_apply,
      φ.map_add, φ.map_sum, φ.map_smul, hp (g 0), add_right_inj, map_mul_nth],
  end }

lemma pair_chain_map_f_apply {hp : compatible A B f φ} (x : (fin n → H) → B) (g : fin n → G) :
  (pair_chain_map A B f φ hp).f n x g = φ (x (f ∘ g)) :=
rfl

def pair_cohomology_map (hp : compatible A B f φ) (n : ℕ) :
  group_cohomology B n ⟶ group_cohomology A n :=
(homology_functor _ _ n).map (pair_chain_map A B f φ hp)

-- ⟶ or →ₗ[k]? ⟶ makes sense w defn, don't have to rw an of_hom
def pair_H_0_map (hp : compatible A B f φ) :
  H_0 B ⟶ H_0 A :=
(H_0_iso B).inv ≫ pair_cohomology_map A B f φ hp 0 ≫ (H_0_iso A).hom

lemma pair_H_0_map_comp_subtype (hp : compatible A B f φ) :
  (A.ρ.invariants.subtype).comp (pair_H_0_map A B f φ hp) =
  φ.comp B.ρ.invariants.subtype :=
begin
  show (_ ≫ _) ≫ Module.of_hom A.ρ.invariants.subtype
    = Module.of_hom B.ρ.invariants.subtype ≫ Module.of_hom φ,
  rw [category.assoc, iso.inv_comp_eq, ←cancel_epi (homology.π _ _ _)],
  simp only [category.assoc, π_comp_H_0_iso_hom_comp_subtype_assoc, pair_cohomology_map,
    homology_functor_map, homology.π_map_assoc, π_comp_H_0_iso_hom_comp_subtype],
  delta homological_complex.cycles,
  rw limits.kernel_subobject_map_arrow_assoc,
  ext,
  show φ ((((inhomogeneous_cochains B).cycles 0).arrow x) (f ∘ default))
    = φ ((((inhomogeneous_cochains B).cycles 0).arrow x) default),
  rw unique.eq_default (f ∘ default),
  { delta homology.π,
    apply_instance }
end

-- would need some Module.of's for this to be a ⟶
def pair_one_cocycles_map (hp : compatible A B f φ) :
  one_cocycles B →ₗ[k] one_cocycles A :=
(one_cocycles_iso B).inv ≫ (cycles_functor _ _ 1).map (pair_chain_map A B f φ hp)
  ≫ (one_cocycles_iso A).hom

lemma pair_one_cocycles_map_comp_subtype (hp : compatible A B f φ) (x : one_cocycles B) (g : G) :
  (one_cocycles A).subtype (pair_one_cocycles_map A B f φ hp x) g
    = φ ((one_cocycles B).subtype x (f g)) :=
begin
  show ((one_cocycles_iso A).hom ≫ Module.of_hom (one_cocycles A).subtype)
    (((one_cocycles_iso B).inv ≫ _) x) g = _,
  simpa only [one_cocycles_iso_hom_comp_subtype, ←linear_map.comp_apply, ←Module.comp_def,
    category.assoc, cycles_functor_map, cycles_map_arrow_assoc,
    one_cocycles_iso_inv_comp_arrow_assoc],
end

def pair_H_1_map (hp : compatible A B f φ) :
  H_1 B ⟶ H_1 A :=
(H_1_iso B).inv ≫ pair_cohomology_map A B f φ hp 1 ≫ (H_1_iso A).hom

lemma mkq_comp_pair_H_1_map (hp : compatible A B f φ) :
  Module.of_hom (one_coboundaries B).mkq ≫ pair_H_1_map A B f φ hp
  = (one_coboundaries A).mkq.comp (pair_one_cocycles_map A B f φ hp) :=
begin
  simpa only [pair_H_1_map, mkq_comp_H_1_iso_inv_assoc, pair_cohomology_map, homology_functor_map,
    homology.π_map_assoc, π_comp_H_1_iso_hom, ←Module.comp_def, category.assoc,
    pair_one_cocycles_map],
end

def pair_two_cocycles_map (hp : compatible A B f φ) :
  two_cocycles B →ₗ[k] two_cocycles A :=
(two_cocycles_iso B).inv ≫ (cycles_functor _ _ 2).map (pair_chain_map A B f φ hp)
  ≫ (two_cocycles_iso A).hom

lemma pair_two_cocycles_map_comp_subtype (hp : compatible A B f φ) (x : one_cocycles B) (g : G) :
  (one_cocycles A).subtype (pair_one_cocycles_map A B f φ hp x) g
    = φ ((one_cocycles B).subtype x (f g)) :=
begin
  show ((one_cocycles_iso A).hom ≫ Module.of_hom (one_cocycles A).subtype)
    (((one_cocycles_iso B).inv ≫ _) x) g = _,
  simpa only [one_cocycles_iso_hom_comp_subtype, ←linear_map.comp_apply, ←Module.comp_def,
    category.assoc, cycles_functor_map, cycles_map_arrow_assoc,
    one_cocycles_iso_inv_comp_arrow_assoc],
end

def pair_H_2_map (hp : compatible A B f φ) :
  H_2 B ⟶ H_2 A :=
(H_2_iso B).inv ≫ pair_cohomology_map A B f φ hp 2 ≫ (H_2_iso A).hom

lemma mkq_comp_pair_H_2_map (hp : compatible A B f φ) :
  Module.of_hom (two_coboundaries B).mkq ≫ pair_H_2_map A B f φ hp
  = (two_coboundaries A).mkq.comp (pair_two_cocycles_map A B f φ hp) :=
begin
  simpa only [pair_H_2_map, mkq_comp_H_2_iso_inv_assoc, pair_cohomology_map, homology_functor_map,
    homology.π_map_assoc, π_comp_H_2_iso_hom, ←Module.comp_def, category.assoc,
    pair_two_cocycles_map],
end

variables {G}

noncomputable def cohomology_map {A B : Rep k G} (φ : A.V →ₗ[k] B.V)
  (hp : compatible B A (monoid_hom.id G) φ) (n : ℕ) :
  group_cohomology A n ⟶ group_cohomology B n :=
(pair_cohomology_map B A (monoid_hom.id G) φ hp n)

noncomputable def cohomology_map' {A B : Rep k G} (φ : A ⟶ B) (n : ℕ) :
  group_cohomology A n ⟶ group_cohomology B n :=
(pair_cohomology_map _ _ (monoid_hom.id G) φ.hom (rep_hom_pair φ) n)

def Res (S : subgroup G) (n : ℕ) :
  group_cohomology A n ⟶ group_cohomology (Res_rep A S) n :=
pair_cohomology_map _ _ S.subtype linear_map.id (subgroup_pair A S) n

def Res_one (S : subgroup G) : H_1 A ⟶ H_1 (Res_rep A S) :=
pair_H_1_map _ _ S.subtype linear_map.id (subgroup_pair A S)

def Inf (S : subgroup G) [h1 : S.normal] (n : ℕ) :
  group_cohomology (Inf_rep A S) n ⟶ group_cohomology A n :=
pair_cohomology_map _ _ (quotient_group.mk' S) (invariants (A.ρ.comp S.subtype)).subtype
  (quotient_pair A S) n

def Inf_one (S : subgroup G) [h1 : S.normal] :
  H_1 (Inf_rep A S) ⟶ H_1 A :=
pair_H_1_map _ _ (quotient_group.mk' S) (invariants (A.ρ.comp S.subtype)).subtype
  (quotient_pair A S)

/-lemma Inf_one_apply_aux (S : subgroup G) [h1 : S.normal] (x : one_cocycles (inf_rep A.ρ S)) :
  (invariants (A.ρ.comp S.subtype)).subtype ∘ ↑x ∘ (coe : G → G ⧸ S) ∈ one_cocycles A.ρ :=
λ g h, subtype.ext_iff.1 (x.2 g h)
#exit
lemma Inf_one_apply (S : subgroup G) [h1 : S.normal] (x : one_cocycles (inf_rep A.ρ H)) :
  Inf_one A.ρ H (quotient.mk' x) =
    (⟨(invariants (A.ρ.comp S.subtype)).subtype ∘ ↑x ∘ (coe : G → G ⧸ H), Inf_one_apply_aux A.ρ H x⟩ : one_cocycles A.ρ) :=
begin
  sorry
end-/

#exit
def ibuprofenrules (S : subgroup G) [h1 : S.normal]
  (x : one_cocycles (Inf_rep A S)) (m : A)
  (h : ∀ g : G, ((↑x : G ⧸ H → invariants H M) (g : G ⧸ H) : M) = g • m - m) :
  G ⧸ H → M :=
λ g, quotient.lift_on' g (λ y, y • m - m) $ λ a b hab,
begin
  dsimp,
  rw [←h a, ←h b, quotient_group.eq.2 hab],
end

def ibuprofen (S : subgroup G) [h1 : S.normal]
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

lemma Inf_ker_eq_bot_aux (S : subgroup G) [h1 : S.normal]
  (x : one_cocycles (G ⧸ H) (invariants H M)) (m : M)
  (h : ∀ g : G, ((↑x : G ⧸ H → invariants H M) (g : G ⧸ H) : M) = g • m - m) :
  m ∈ invariants H M :=
begin
  intro y,
  rw ←sub_eq_zero,
  erw ←h y,
  rw [(quotient_group.eq_one_iff (y : G)).2 y.2, one_cocycles_map_one _],
  refl,
end

lemma Inf_ker_eq_bot (S : subgroup G) [h1 : S.normal] :
  (Inf_one M H).ker = ⊥ :=
begin
  rw eq_bot_iff,
  intros x,
  refine x.induction_on' _,
  intros y hy,
  erw [add_monoid_hom.mem_ker, Inf_one_apply] at hy,
  refine (quotient_add_group.eq_zero_iff y).2 _,
  obtain ⟨m, hm⟩ := (quotient_add_group.eq_zero_iff _).1 hy,
  let F := ibuprofen M H y m hm,
  use [m, Inf_ker_eq_bot_aux _ _ y _ hm],
  intro g,
  refine g.induction_on' _,
  { intro z, ext, exact hm z },
end

lemma Inf_one_range_le_Res_one_ker (S : subgroup G) [h1 : S.normal] :
  (Inf_one M H).range ≤ (Res_one M H).ker :=
begin
  intros x hx,
  obtain ⟨y, rfl⟩ := add_monoid_hom.mem_range.1 hx,
  refine quotient_add_group.induction_on' y (λ z, _),
  rw [add_monoid_hom.mem_ker, Inf_one_apply, Res_one_apply, quotient_add_group.eq_zero_iff],
  use 0,
  intro g,
  simp only [add_subgroup.coe_subtype, add_subgroup.coe_mk, subgroup.coe_subtype,
    function.comp_app, smul_zero, sub_zero, add_submonoid_class.coe_eq_zero],
  rw [(quotient_group.eq_one_iff (g : G)).2 g.2, one_cocycles_map_one],
end

lemma seriously (S : subgroup G) [h1 : S.normal] (h : H) (g : G) :
  g⁻¹ * h * g ∈ H :=
by {convert subgroup.normal.conj_mem h1 h h.2 g⁻¹, rw inv_inv }

lemma helper (S : subgroup G) [h1 : S.normal]  (y : one_cocycles G M) (m : M)
  (Hy : ∀ h : H, (y : G → M) h = h • m - m) (g : G) (h : H) :
  h • ((y : G → M) g - g • m + m) = (y : G → M) g - g • m + m :=
begin
  have := one_cocycles_map_mul y g (g⁻¹ * h * g),
  rw [mul_assoc, mul_inv_cancel_left, one_cocycles_map_mul, Hy, ←mul_assoc, (show
    (y : G → M) (g⁻¹ * h * g) = (g⁻¹ * h * g) • m - m, from Hy (⟨g⁻¹ * h * g, seriously _ _ _⟩)),
    smul_sub, mul_assoc, mul_smul, smul_inv_smul, mul_smul, ←eq_sub_iff_add_eq] at this,
  rw [smul_add, smul_sub],
  erw this,
  show h • g • m - _ + _ - _ - _ + _ = _,
  abel,
end

lemma Inf_one_range_eq_Res_one_ker (S : subgroup G) [h1 : S.normal] :
  (Inf_one M H).range = (Res_one M H).ker :=
le_antisymm (Inf_one_range_le_Res_one_ker M H) $ λ x,
begin
  refine quotient_add_group.induction_on' x _,
  intros y hy,
  rw [add_monoid_hom.mem_ker, Res_one_apply] at hy,
  obtain ⟨m, hm⟩ := (quotient_add_group.eq_zero_iff _).1 hy,
  let F' : G ⧸ H → M := λ g, quotient.lift_on' g
    (λ g, (y : G → M) g - g • m + m)
    (λ a b hab, by
    {dsimp,
     congr' 1,
     have Hy : (y : G → M) (a⁻¹ * b) = (a⁻¹ * b) • m - m := hm ⟨a⁻¹ * b, hab⟩,
     rw [one_cocycles_map_mul] at Hy,
     replace Hy := congr_arg ((•) a) Hy,
     simp only [smul_add, smul_sub, smul_inv_smul, mul_smul] at Hy,
     rw [one_cocycles_map_inv, add_neg_eq_iff_eq_add] at Hy,
     rw Hy,
     abel }),
  let F : G ⧸ H → invariants H M :=
  λ g, ⟨F' g, by {refine g.induction_on' _, intro x, dsimp [F'], exact helper M H y m hm x}⟩,
  have HF : F ∈ one_cocycles (G ⧸ H) (invariants H M) := λ g h,
  begin
    refine quotient.induction_on₂' g h _,
    intros a b,
    show _ - F (quotient.mk' (a * b)) + _ = _,
    ext,
    dsimp [F, F', (•), quotient_action_aux],
    rw [one_cocycles_map_mul, smul_add, smul_sub, mul_smul],
    abel,
  end,
  let FF : firstcoh (G ⧸ H) (invariants H M) := (⟨F, HF⟩ : one_cocycles _ _),
  use FF,
  rw Inf_one_apply,
  dsimp [FF, F, F'],
  rw quotient_add_group.eq,
  use m,
  intro g,
  dsimp,
  abel,
end

end stuff
