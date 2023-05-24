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

@[simps] def Inf_rep_aux [h1 : S.normal] : representation k G (invariants (A.ρ.comp S.subtype)) :=
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

-- IS THIS SAFE? DONT FUCKING KNOW. WHY CANT I EVER GET SUBMODULES TO FUCKING COERCE
instance [S.normal] : has_coe (Inf_rep A S) A :=
⟨λ x, x.1⟩

lemma Inf_rep_apply [S.normal] (g : G) (x : invariants (A.ρ.comp S.subtype)) :
  (((Inf_rep A S).ρ (g : G ⧸ S) x : invariants (A.ρ.comp S.subtype)) : A) = A.ρ g x :=
rfl

def Res_rep : Rep k S := Rep.of (A.ρ.comp S.subtype)

lemma Res_rep_apply (g : S) (x : A) : (Res_rep A S).ρ g x = A.ρ g x :=
rfl

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

def Ind (H : subgroup G) (A : Rep k H) : Rep k G :=
sorry /-{ V := Module.of k (Rep.of_mul_action k H G ⟶ A),
  ρ :=
  { to_fun := λ g,
    { to_fun := λ f,
      { hom := finsupp.lift _ _ _ (λ g, _),
        comm' := _ },
      map_add' := _,
      map_smul' := _ },
    map_one' := _,
    map_mul' := _ }}-/

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
#check subobject
#check (inhomogeneous_cochains B).cycles n
#check (inhomogeneous_cochains B).X n

def pair_cocycles_map (hp : compatible A B f φ) (n : ℕ) :
  (inhomogeneous_cochains B).cycles n →ₗ[k] (inhomogeneous_cochains A).cycles n :=
(cycles_functor _ _ n).map (pair_chain_map A B f φ hp)

def pair_coboundaries_map (hp : compatible A B f φ) (n : ℕ) :
  (inhomogeneous_cochains B).boundaries n →ₗ[k] (inhomogeneous_cochains A).boundaries n :=
(boundaries_functor _ _ n).map (pair_chain_map A B f φ hp)

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

lemma pair_one_cocycles_map_apply (hp : compatible A B f φ) (x : one_cocycles B) (g : G) :
  (pair_one_cocycles_map A B f φ hp x : G → A) g
    = φ ((x : H → B) (f g)) :=
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

lemma pair_two_cocycles_map_apply (hp : compatible A B f φ) (x : one_cocycles B) (g : G) :
  (pair_one_cocycles_map A B f φ hp x : G → A) g
    = φ ((x : H → B) (f g)) :=
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

noncomputable def group_cohomology_map' {A B : Rep k G} (φ : A.V →ₗ[k] B.V)
  (hp : compatible B A (monoid_hom.id G) φ) (n : ℕ) :
  group_cohomology A n ⟶ group_cohomology B n :=
(pair_cohomology_map B A (monoid_hom.id G) φ hp n)

noncomputable def group_cohomology_map {A B : Rep k G} (φ : A ⟶ B) (n : ℕ) :
  group_cohomology A n ⟶ group_cohomology B n :=
(pair_cohomology_map _ _ (monoid_hom.id G) φ.hom (rep_hom_pair φ) n)

def Res (S : subgroup G) (n : ℕ) :
  group_cohomology A n ⟶ group_cohomology (Res_rep A S) n :=
pair_cohomology_map _ _ S.subtype linear_map.id (subgroup_pair A S) n

def Res_one_cocycles : one_cocycles A →ₗ[k] one_cocycles (Res_rep A S) :=
pair_one_cocycles_map _ _ S.subtype linear_map.id (subgroup_pair A S)

def Res_one (S : subgroup G) : H_1 A ⟶ H_1 (Res_rep A S) :=
pair_H_1_map _ _ S.subtype linear_map.id (subgroup_pair A S)

def Inf (S : subgroup G) [h1 : S.normal] (n : ℕ) :
  group_cohomology (Inf_rep A S) n ⟶ group_cohomology A n :=
pair_cohomology_map _ _ (quotient_group.mk' S) (invariants (A.ρ.comp S.subtype)).subtype
  (quotient_pair A S) n

def Inf_one_cocycles (S : subgroup G) [h1 : S.normal] :
  one_cocycles (Inf_rep A S) →ₗ[k] one_cocycles A :=
pair_one_cocycles_map A (Inf_rep A S) (quotient_group.mk' S)
  (invariants (A.ρ.comp S.subtype)).subtype (quotient_pair A S)

def Inf_one (S : subgroup G) [h1 : S.normal] :
  H_1 (Inf_rep A S) ⟶ H_1 A :=
pair_H_1_map _ _ (quotient_group.mk' S) (invariants (A.ρ.comp S.subtype)).subtype
  (quotient_pair A S)

variables {A S}

lemma Res_one_cocycles_apply (x : one_cocycles A) (g : S) :
  (Res_one_cocycles A S x : S → Res_rep A S) g = (x : G → A) g :=
begin
  rw [Res_one_cocycles, pair_one_cocycles_map_apply],
  refl,
end

lemma Inf_one_cocycles_apply [h1 : S.normal] (x : one_cocycles (Inf_rep A S)) (g : G) :
  ((Inf_one_cocycles A S x) : G → A) g = (x : G ⧸ S → Inf_rep A S) g :=
begin
  rw [Inf_one_cocycles, pair_one_cocycles_map_apply],
  refl,
end

variables (A S)

lemma Inf_one_comp_mkq [h1 : S.normal] :
  (Inf_one A S).comp (one_coboundaries (Inf_rep A S)).mkq
    = (one_coboundaries A).mkq.comp (Inf_one_cocycles A S) :=
mkq_comp_pair_H_1_map A (Inf_rep A S) (quotient_group.mk' S)
  (invariants (A.ρ.comp S.subtype)).subtype (quotient_pair A S)

lemma Res_one_comp_mkq :
  (Res_one A S).comp (one_coboundaries A).mkq
    = (one_coboundaries (Res_rep A S)).mkq.comp (Res_one_cocycles A S) :=
mkq_comp_pair_H_1_map (Res_rep A S) A S.subtype linear_map.id (subgroup_pair A S)

lemma Inf_one_apply [h1 : S.normal] (x : one_cocycles (Inf_rep A S)) :
  Inf_one A S (quotient.mk' x) = quotient.mk' (Inf_one_cocycles A S x) :=
linear_map.ext_iff.1 (by apply Inf_one_comp_mkq A S) x

lemma Res_one_apply (x : one_cocycles A) :
  Res_one A S (quotient.mk' x) = quotient.mk' (Res_one_cocycles A S x) :=
linear_map.ext_iff.1 (by apply Res_one_comp_mkq A S) x

lemma Inf_ker_eq_bot (S : subgroup G) [h1 : S.normal] :
  (Inf_one A S).ker = ⊥ :=
begin
  rw eq_bot_iff,
  intros x,
  refine x.induction_on' _,
  intros y hy,
  erw [linear_map.mem_ker, Inf_one_apply] at hy,
  refine (submodule.quotient.mk_eq_zero _).2 _,
  obtain ⟨m, hm⟩ := (submodule.quotient.mk_eq_zero _).1 hy,
  refine ⟨⟨m, _⟩, _⟩,
  { intros g,
    dsimp,
    have := function.funext_iff.1 (subtype.ext_iff.1 hm) g,
    simp only [linear_map.cod_restrict_apply, d_zero_apply] at this,
    rw [←sub_eq_zero, this, Inf_one_cocycles_apply,
      (quotient_group.eq_one_iff (g : G)).2 g.2, one_cocycles_map_one, submodule.coe_zero] },
  { ext z,
    refine quotient_group.induction_on' z (λ w, _),
    rw ←Inf_one_cocycles_apply y w,
    exact function.funext_iff.1 (subtype.ext_iff.1 hm) w }
end

lemma Inf_one_range_le_Res_one_ker (S : subgroup G) [h1 : S.normal] :
  (Inf_one A S).range ≤ (Res_one A S).ker :=
begin
  intros x hx,
  obtain ⟨y, rfl⟩ := hx,
  refine quotient.induction_on' y (λ z, _),
  rw [linear_map.mem_ker, Inf_one_apply, Res_one_apply,
    submodule.quotient.mk'_eq_mk, submodule.quotient.mk_eq_zero],
  use 0,
  ext,
  simp only [Res_one_cocycles_apply, Inf_one_cocycles_apply, map_zero,
    submodule.coe_zero, pi.zero_apply, (quotient_group.eq_one_iff (x : G)).2 x.2,
    one_cocycles_map_one, submodule.coe_zero],
end

lemma seriously (S : subgroup G) [h1 : S.normal] (h : S) (g : G) :
  g⁻¹ * h * g ∈ S :=
by {convert subgroup.normal.conj_mem h1 h h.2 g⁻¹, rw inv_inv }

lemma helper (S : subgroup G) [h1 : S.normal]  (y : one_cocycles A) (m : A)
  (Hy : ∀ h : S, (y : G → A) h = A.ρ h m - m) (g : G) (h : S) :
  A.ρ h ((y : G → A) g - A.ρ g m + m) = (y : G → A) g - A.ρ g m + m :=
begin
  have := (mem_one_cocycles_iff' (y : G → A)).1 y.2 (g, (g⁻¹ * h * g)),
  simp only [prod.fst] at this,
  rw [mul_assoc, mul_inv_cancel_left, (mem_one_cocycles_iff' (y : G → A)).1 y.2 (h, g), Hy,
    ←mul_assoc, (show (y : G → A) (g⁻¹ * h * g) = A.ρ (g⁻¹ * h * g) m - m, from Hy (⟨g⁻¹ * h * g,
    seriously _ _ _⟩)), map_sub, ←linear_map.mul_apply, ←map_mul, ←mul_assoc, mul_inv_cancel_left,
    sub_add_comm, ←sub_eq_sub_iff_add_eq_add] at this,
  rw [map_add, map_sub, ←linear_map.mul_apply, ←map_mul, this,
    sub_add_eq_add_sub, add_sub_assoc, sub_sub_self],
end

lemma Inf_one_range_eq_Res_one_ker (S : subgroup G) [h1 : S.normal] :
  (Inf_one A S).range = (Res_one A S).ker :=
le_antisymm (Inf_one_range_le_Res_one_ker A S) $ λ x,
begin
  refine quotient.induction_on' x _,
  intros y hy,
  rw [linear_map.mem_ker, Res_one_apply] at hy,
  obtain ⟨m, hm⟩ := (submodule.quotient.mk_eq_zero _).1 hy,
  refine ⟨quotient.mk' ⟨λ (g : G ⧸ S), quotient.lift_on' g (λ x : G, (⟨(y : G → A) x - A.ρ x m + m,
    λ g, helper A S y m (λ h, _) x g⟩
    : invariants (A.ρ.comp S.subtype))) (λ a b hab, _), _⟩, _⟩,
  { simp only [subtype.ext_iff, function.funext_iff, Res_one_cocycles_apply] at hm,
    exact (hm h).symm },
  { ext,
    dsimp only [subtype.coe_mk],
    congr' 1,
    have := function.funext_iff.1 (subtype.ext_iff.1 hm) (⟨a⁻¹ * b,
      quotient_group.eq.1 (quotient.eq'.2 hab)⟩),
    simp only [Res_one_cocycles_apply, linear_map.cod_restrict_apply, d_zero_apply,
        subgroup.coe_mk, Res_rep_apply, (mem_one_cocycles_iff' (y : G → A)).1 y.2 (a⁻¹, b)] at this,
    replace this := congr_arg (A.ρ a) this,
    simp only [map_sub, ←linear_map.mul_apply, ←map_mul, map_add, mul_inv_cancel_left,
      mul_inv_self, map_one, linear_map.one_apply, one_cocycles_map_inv, ←sub_eq_add_neg,
      sub_eq_sub_iff_add_eq_add] at this,
    rw [sub_eq_sub_iff_add_eq_add, add_comm, this] },
  { refine (mem_one_cocycles_iff' _).2 _,
    rintros ⟨g, h⟩,
    refine quotient.induction_on₂' g h (λ w z, _),
    show quotient.lift_on' (quotient.mk' (_ * _)) _ _ = _,
    ext,
    simp only [quotient.lift_on'_mk', subtype.coe_mk, submodule.coe_add],
    simp only [show quotient.mk' w = (w : G ⧸ S), from rfl, Inf_rep_apply, subtype.coe_mk, map_sub,
      map_add, ←linear_map.mul_apply, ←map_mul, ←add_assoc, add_left_inj],
    simp only [add_assoc, add_sub_cancel'_right, sub_add_eq_add_sub, sub_left_inj,
        (mem_one_cocycles_iff' (y : G → A)).1 y.2 (w, z)] },
  { rw Inf_one_apply,
    refine (submodule.quotient.eq _).2 ⟨-m, subtype.ext (funext $ λ g, _)⟩,
    simp only [linear_map.cod_restrict_apply, submodule.coe_sub, pi.sub_apply,
      Inf_one_cocycles_apply],
    simp only [d_zero_apply, subtype.coe_mk, quotient_group.quotient_lift_on_coe],
    rw [map_neg, neg_sub_neg, eq_sub_iff_add_eq', ←add_sub_assoc, sub_add_eq_add_sub] }
end

end group_cohomology
