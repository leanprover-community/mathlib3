import algebra.group.cohomology.stuff

universes v u

variables (G : Type u) [group G] (M : Type u)
  [add_comm_group M] [distrib_mul_action G M]
noncomputable theory


namespace stuff

def pair {G H : Type u} [group G] [group H]
  {M N : Type u} [add_comm_group M] [add_comm_group N] [distrib_mul_action G M]
  [distrib_mul_action H N] (f : G →* H) (φ : N →+ M) : Prop :=
∀ (g : G) (x : N), φ (f(g) • x) = g • φ x

@[simps] def pair_chain_map_aux  {G H : Type u} [group G] [group H]
  {M N : Type u} [add_comm_group M] [add_comm_group N] [distrib_mul_action G M]
  [distrib_mul_action H N] (f : G →* H) (φ : N →+ M) (n : ℕ) :
  ((fin n → H) → N) →+ ((fin n → G) → M) :=
{ to_fun := λ F x, φ (F (f ∘ x)),
  map_zero' := by ext; exact φ.map_zero,
  map_add' := λ x y, by ext; exact φ.map_add _ _ }

variables  (H : subgroup G) [h1 : H.normal] (g : G) (m : invariants H M)
 (h : H)

def quotient_action_aux (H : subgroup G) [h1 : H.normal] (g : G) (m : invariants H M) :
  invariants H M := ⟨g • m, λ h, by { have : (g⁻¹ * h * g) • (m : M) = m,
  by {refine m.2 (⟨g⁻¹ * h * g, _⟩ : H),
  convert subgroup.normal.conj_mem h1 (h : H) h.2 g⁻¹, rw inv_inv},
  conv_rhs {rw ←this},
  rw [←mul_smul, ←mul_assoc, mul_inv_cancel_left, mul_smul],
  refl }⟩

instance (H : subgroup G) [H.normal] :
  distrib_mul_action (G ⧸ H) (invariants H M) :=
{ smul := λ g, quotient.lift_on' g (λ (g : G), quotient_action_aux G M H g) $ λ a b hab,
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

lemma quotient_pair (H : subgroup G) [H.normal] : pair (quotient_group.mk' H) (invariants H M).subtype :=
λ x y, rfl

lemma subgroup_pair (H : subgroup G) : pair H.subtype (add_monoid_hom.id M) :=
λ x y, rfl

lemma distrib_mul_action_hom_pair {M N : Type u} [add_comm_group M] [add_comm_group N]
  [distrib_mul_action G M] [distrib_mul_action G N] (f : M →+[G] N) :
  pair (monoid_hom.id G) f.to_add_monoid_hom :=
f.map_smul

lemma pair_chain_map_aux_comm {G H : Type u} [group G] [group H]
  {M N : Type u} [add_comm_group M] [add_comm_group N] [distrib_mul_action G M]
  [distrib_mul_action H N] (f : G →* H) (φ : N →+ M) (hp : pair f φ) (n : ℕ) :
  (cochain.d G M n).comp (pair_chain_map_aux f φ n)
    = (pair_chain_map_aux f φ (n + 1)).comp (cochain.d H N n) :=
begin
  ext x g,
  dsimp [d_to_fun, pair_chain_map_aux],
  simp only [φ.map_add, φ.map_sum, φ.map_zsmul, hp (g 0)],
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
  [distrib_mul_action H N] (f : G →* H) (φ : N →+ M) (hp : pair f φ) :
  cochain_cx H N ⟶ cochain_cx G M :=
{ f := λ i, pair_chain_map_aux f φ i,
  comm' := λ i j hij, by
  { cases hij,
    dsimp,
    erw [cochain_complex.of_d, cochain_complex.of_d],
    exact pair_chain_map_aux_comm f φ hp i }}

def pair_homology_map {G H : Type u} [group G] [group H]
  {M N : Type u} [add_comm_group M] [add_comm_group N] [distrib_mul_action G M]
  [distrib_mul_action H N] (f : G →* H) (φ : N →+ M) (hp : pair f φ) (n : ℕ) :
  (cochain_cx H N).homology n →+ (cochain_cx G M).homology n :=
(homology_functor _ _ n).map (pair_chain_map f φ hp)

variables {G}

noncomputable def cohomology_map {M N : Type u} [add_comm_group M] [add_comm_group N]
  [distrib_mul_action G M] [distrib_mul_action G N] (f : M →+[G] N) (n : ℕ) :
  (cochain_cx G M).homology n →+ (cochain_cx G N).homology n :=
(pair_homology_map (monoid_hom.id G) f.to_add_monoid_hom (distrib_mul_action_hom_pair G f) n)

def Res (H : subgroup G) (n : ℕ) :
  (cochain_cx G M).homology n →+ (cochain_cx H M).homology n :=
pair_homology_map H.subtype (add_monoid_hom.id M) (subgroup_pair G M H) n

def Res_one (H : subgroup G) :
  firstcoh G M →+ firstcoh H M :=
((first_iso H M).to_add_monoid_hom.comp (Res M H 1)).comp (first_iso G M).symm.to_add_monoid_hom

@[simp] lemma Res_one_apply (H : subgroup G) (x : one_cocycles G M) :
  Res_one M H x = (⟨↑x ∘ H.subtype, λ g h, x.2 g h⟩ : one_cocycles H M) :=
begin
  sorry
end

def Inf (H : subgroup G) [h1 : H.normal] (n : ℕ) :
  (cochain_cx (G ⧸ H) (invariants H M)).homology n →+ (cochain_cx G M).homology n :=
pair_homology_map (quotient_group.mk' H) (invariants H M).subtype (quotient_pair G M H) n

def Inf_one (H : subgroup G) [h1 : H.normal] :
  firstcoh (G ⧸ H) (invariants H M) →+ firstcoh G M :=
((first_iso G M).to_add_monoid_hom.comp (Inf M H 1)).comp
  (first_iso (G ⧸ H) (invariants H M)).symm.to_add_monoid_hom

lemma Inf_one_apply_aux (H : subgroup G) [h1 : H.normal] (x : one_cocycles (G ⧸ H) (invariants H M)) :
  (invariants H M).subtype ∘ ↑x ∘ (coe : G → G ⧸ H)  ∈ one_cocycles G M :=
λ g h, subtype.ext_iff.1 (x.2 g h)

lemma Inf_one_apply (H : subgroup G) [h1 : H.normal] (x : one_cocycles (G ⧸ H) (invariants H M)) :
  Inf_one M H x =
    (⟨(invariants H M).subtype ∘ ↑x ∘ (coe : G → G ⧸ H), Inf_one_apply_aux M H x⟩ : one_cocycles G M) :=
begin
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
  rw [(quotient_group.eq_one_iff (y : G)).2 y.2, one_cocycles_map_one _],
  refl,
end

lemma Inf_ker_eq_bot (H : subgroup G) [h1 : H.normal] :
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

lemma Inf_one_range_le_Res_one_ker (H : subgroup G) [h1 : H.normal] :
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

lemma seriously (H : subgroup G) [h1 : H.normal] (h : H) (g : G) :
  g⁻¹ * h * g ∈ H :=
by {convert subgroup.normal.conj_mem h1 h h.2 g⁻¹, rw inv_inv }

lemma helper (H : subgroup G) [h1 : H.normal]  (y : one_cocycles G M) (m : M)
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

lemma Inf_one_range_eq_Res_one_ker (H : subgroup G) [h1 : H.normal] :
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
