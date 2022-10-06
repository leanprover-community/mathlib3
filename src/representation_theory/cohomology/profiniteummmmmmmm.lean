import topology.category.Profinite.as_limit
import tactic.transport
import group_theory.quotient_group
import topology.algebra.open_subgroup
import representation_theory.cohomology.ProfiniteGroup

universes v u

noncomputable theory

open category_theory

variables (G : ProfiniteGroup)

set_option old_structure_cmd true

@[ext] structure discrete_quotient_group extends discrete_quotient G :=
(mul : ∀ {w x y z}, rel w x → rel y z → rel (w * y) (x * z))
/-
variables {G}
@[simps] def open_subgroup.to_discrete_quotient (H : open_subgroup G) : discrete_quotient G :=
{ rel := left_coset_equivalence (H : set G),
  equiv := left_coset_equivalence_rel (H : set G),
  clopen :=
  begin
    intro g,
    split,
    erw set_of_left_coset_equivalence,
    exact is_open.left_coset H.2 _,
    erw set_of_left_coset_equivalence,
    exact is_closed.left_coset H.is_closed _,
  end }

def open_subgroup.to_disc_of_normal (H : open_subgroup G) [subgroup.normal (H : subgroup G)] :
  discrete_quotient_group G :=
{ mul := λ w x y z,
  begin
    dsimp,
    erw [←quotient_group.left_rel_r_eq_left_coset_equivalence],
    exact (quotient_group.con (H : subgroup G)).mul,
  end, ..H.to_discrete_quotient }-/

namespace discrete_quotient_group

variables {G}

def con (Q : discrete_quotient_group G) : con G :=
{ r := Q.rel,
  iseqv := Q.equiv,
  mul' := Q.mul }

lemma con_inj : function.injective (@discrete_quotient_group.con G) := sorry

instance : has_coe_to_sort (discrete_quotient_group G) (Type*) :=
⟨λ X, X.to_discrete_quotient⟩

instance (Q : discrete_quotient_group G) : group Q := Q.con.group

open quotient_group
/-
lemma to_disc_quot_inj : function.injective (@discrete_quotient_group.to_discrete_quotient G _ _) :=
begin
  intros X Y h,
  ext1,
  exact (discrete_quotient.ext_iff _ _).1 h,
end-/

def proj (Q : discrete_quotient_group G) : G →* Q :=
{ to_fun := Q.to_discrete_quotient.proj,
  map_one' := @con.coe_one _ _ Q.con,
  map_mul' := @con.coe_mul _ _ Q.con }

variables {G}

instance : partial_order (discrete_quotient_group G) :=
partial_order.lift (@con G) con_inj

instance : has_top (discrete_quotient_group G) :=
{ top := { mul := λ w x y z h1 h2, by trivial, ..(⊤ : discrete_quotient G) }}

instance : order_top (discrete_quotient_group G) :=
order_top.lift (discrete_quotient_group.to_discrete_quotient) (λ a b, id) (by ext; refl)

instance : semilattice_inf (discrete_quotient_group G) :=
{ inf := λ A B, { mul := λ w x y z h1 h2, ⟨A.mul h1.1 h2.1, B.mul h1.2 h2.2⟩,
  .. A.to_discrete_quotient ⊓ B.to_discrete_quotient },
  inf_le_left := sorry,
  inf_le_right := sorry,
  le_inf := sorry,
  ..discrete_quotient_group.partial_order }

instance : category_theory.category (discrete_quotient G) := by apply_instance

lemma umm (U V : discrete_quotient_group G) (hUV : U ≤ V) :
  U.to_discrete_quotient ≤ V.to_discrete_quotient := hUV

def of_le {A B : discrete_quotient_group G} (h : A ≤ B) : A →* B :=
{ to_fun := discrete_quotient.of_le h,
  map_one' := rfl,
  map_mul' := λ x y, quotient.induction_on₂' x y (λ z w, rfl) }

instance : inhabited (discrete_quotient_group G) := ⟨⊤⟩

lemma exists_of_compat (Qs : Π (Q : discrete_quotient_group G), Q)
  (compat : ∀ (A B : discrete_quotient_group G) (h : A ≤ B), of_le h (Qs _) = Qs _) :
  ∃ x : G, ∀ Q : discrete_quotient_group G, Q.proj x = Qs _ :=
begin
  obtain ⟨x,hx⟩ := is_compact.nonempty_Inter_of_directed_nonempty_compact_closed
    (λ (Q : discrete_quotient_group G), Q.proj ⁻¹' {Qs _}) (λ A B, _) (λ i, _)
    (λ i, (discrete_quotient.fiber_closed _ _).is_compact) (λ i, discrete_quotient.fiber_closed _ _),
  { refine ⟨x, λ Q, _⟩,
    specialize hx _ ⟨Q,rfl⟩,
    dsimp at hx,
    rcases discrete_quotient.proj_surjective _ (Qs Q) with ⟨y,hy⟩,
    rw ← hy at *,
    sorry
    /- erw discrete_quotient.fiber_eq at hx,
    exact quotient.sound' (Q.equiv.2.1 hx) -/
    },
  { refine ⟨A ⊓ B, λ a ha, _, λ a ha, _⟩,
    { dsimp only,
      erw ← compat (A ⊓ B) A inf_le_left,
      exact discrete_quotient.fiber_le_of_le _ _ ha },
    { dsimp only,
      erw ← compat (A ⊓ B) B inf_le_right,
      exact discrete_quotient.fiber_le_of_le _ _ ha } },
  { obtain ⟨x,hx⟩ := discrete_quotient.proj_surjective i.to_discrete_quotient (Qs i),
    refine ⟨x,_⟩,
    dsimp only,
    erw [← hx, discrete_quotient.fiber_eq],
    apply i.equiv.1 },
end

lemma eq_of_proj_eq {x y : G} (h : ∀ Q : discrete_quotient_group G, Q.proj x = Q.proj y) : x = y :=
begin
  refine discrete_quotient.eq_of_proj_eq _, -- suffices to show `x = y` in all set-theoretic discrete quotients
  intro Q,
  suffices : ∃ Q₁ : discrete_quotient_group G, Q₁.to_discrete_quotient ≤ Q,
  begin
    cases this with Q₁ hQ₁,
    simp only [←discrete_quotient.of_le_proj_apply hQ₁],
    congr' 1,
    exact h Q₁,
  end,
  sorry,
end

end discrete_quotient_group
namespace ProfiniteGroup
variables (G)

/-- The functor `discrete_quotient X ⥤ Fintype` whose limit is isomorphic to `X`. -/
def fin_diag : discrete_quotient_group G ⥤ FinGroup :=
{ obj := λ S, FinGroup.of S,
  map := λ S T f, discrete_quotient_group.of_le f.le }

/-- An abbreviation for `X.fintype_diagram ⋙ Fintype_to_Profinite`. -/
abbreviation diag : discrete_quotient_group G ⥤ ProfiniteGroup :=
G.fin_diag ⋙ FinGroup.to_ProfiniteGroup

/-- A cone over `X.diagram` whose cone point is `X`. -/
def as_limit_cone : category_theory.limits.cone G.diag :=
{ X := G,
  π := { app := λ S, ⟨S.proj, S.to_discrete_quotient.proj_is_locally_constant.continuous⟩ } }
#check discrete_quotient.eq_of_proj_eq
instance is_iso_as_limit_cone_lift :
  is_iso ((limit_cone_is_limit G.diag).lift G.as_limit_cone) :=
is_iso_of_bij _
begin
  refine ⟨λ a b, _, λ a, _⟩,
  { intro h, sorry },
  { obtain ⟨b, hb⟩ := discrete_quotient_group.exists_of_compat
      (λ S, a.val S) (λ _ _ h, a.prop (hom_of_le h)),
    refine ⟨b, _⟩,
    ext S : 3,
    apply hb },
end

abbreviation open_normal :=
order_dual $ @subtype (subgroup G) (λ U, is_open (U : set G) ∧ U.normal)

instance : has_coe (open_normal G) (subgroup G) :=
⟨λ U, U.1⟩

instance open_normal_normal (U : open_normal G) : (U : subgroup G).normal := U.2.2

def n_prods {G : Type*} [monoid G] (T : set G) (n : ℕ) : set G :=
{ g | ∃ f : fin n → T, (list.of_fn (coe ∘ f)).prod = g }

def invs {G : Type*} [group G] (T : set G) : set G := { g | ∃ t : T, (t : G)⁻¹ = g }

lemma invs_open (T : set G) (hT : is_open T) : is_open (invs T) :=
begin
  convert is_open.preimage continuous_inv hT,
  ext,
  split,
  { rintros ⟨y, rfl⟩,
    dsimp,
    rw inv_inv,
    exact y.2 },
  { intro h,
    use x⁻¹,
    { exact h },
    { exact inv_inv _ } }
end

variables {G}

lemma lemma1 (x : G) (H : x ≠ 1) : ∃ (U : {U : set G // is_clopen U ∧ (1 : G) ∈ U}), x ∉ (U : set G) :=
begin
  have := totally_disconnected_space_iff_connected_component_singleton.1
    ProfiniteGroup.totally_disconnected_space (1 : G),
  rw connected_component_eq_Inter_clopen at this,
  rw ←not_forall,
  intros H1,
  refine H _,
  have h' := set.mem_Inter.2 H1,
  rw this at h',
  rw set.mem_singleton_iff.1 h',
end

lemma lemma2 (U : set G) (hU : is_clopen U) : is_compact (Uᶜ ∩ n_prods U 2) :=
begin
  refine (compact_of_is_closed_subset G.1.1.2.1 (is_closed_compl_iff.2 hU.1)
    (set.subset_univ _)).inter _,
  let F : G × G → G := λ x, x.1 * x.2,
    have : is_compact (F '' (U ×ˢ U)) := ((compact_of_is_closed_subset G.1.1.2.1 hU.2 (set.subset_univ _)).prod
      (compact_of_is_closed_subset G.1.1.2.1 hU.2 (set.subset_univ _))).image continuous_mul,
    convert this,
    ext g,
    split,
    { rintro ⟨f, hg⟩,
      let X : ((U : set G) ×ˢ (U : set G) : set (G × G)) := ⟨(f 0, f 1), ⟨(f 0).2, (f 1).2⟩⟩,
      use X,
      use X.2,
      rw ←hg,
      simp },
    { rintro ⟨x, hg⟩,
      use (fin.cons (⟨x.1, hg.1.1⟩) (λ i, ⟨x.2, hg.1.2⟩) : fin 2 → U),
      cases hg with hg1 hg2,
      simpa using hg2 }
end

def inter_conjugates (H : subgroup G) : subgroup G :=
{ carrier := set.Inter (λ g, (λ h : G, g * h * g⁻¹) '' H),
  mul_mem' := sorry,
  one_mem' := sorry,
  inv_mem' := sorry }

theorem ummmm (x : G) : (∀ U : open_normal G, x ∈ (U : subgroup G)) → x = 1 :=
begin
  contrapose!,
  intro H,
  have := totally_disconnected_space_iff_connected_component_singleton.1
    ProfiniteGroup.totally_disconnected_space (1 : G),
  rw connected_component_eq_Inter_clopen at this,
  obtain ⟨U, hU⟩ := lemma1 x H,
  let V := (U : set G)ᶜ ∩ n_prods U 2,
  have hm : is_compact ((U : set G) ×ˢ (U : set G)),
  begin
    refine is_compact.prod _ _,
    all_goals { exact compact_of_is_closed_subset G.1.1.2.1 U.2.1.2 (set.subset_univ _) },
  end,
  have hm2 : is_compact (n_prods (U : set G) 2) :=
  begin
    sorry/-let F : G × G → G := λ x, x.1 * x.2,
    have := is_compact.image hm continuous_mul,
    convert this,
    ext g,
    split,
    { rintro ⟨f, hg⟩,
      let X : ((U : set G) ×ˢ (U : set G) : set (G × G)) := ⟨(f 0, f 1), ⟨(f 0).2, (f 1).2⟩⟩,
      use X,
      use X.2,
      rw ←hg,
      simp },
    { rintro ⟨x, hg⟩,
      use (fin.cons (⟨x.1, hg.1.1⟩) (λ i, ⟨x.2, hg.1.2⟩) : fin 2 → U),
      cases hg with hg1 hg2,
      simpa using hg2 }-/
  end,
  have hV : is_compact V := (compact_of_is_closed_subset G.1.1.2.1 (is_closed_compl_iff.2 U.2.1.1)
    (set.subset_univ _)).inter hm2,
  have hV1 : is_open ((λ g : G × G, g.1 * g.2) ⁻¹' Vᶜ) :=
  is_open.preimage continuous_mul (is_open_compl_iff.2 $ is_compact.is_closed hV),
  have hV2 : (U : set G) ⊆ Vᶜ := λ y hy, show y ∈ (_ ∩ _)ᶜ, by simpa using hy,
  have hV3 := ((topological_space.is_topological_basis_opens).prod
    topological_space.is_topological_basis_opens).is_open_iff.1 hV1,
  let im : U → set (G × G) := λ h, classical.some (hV3 (h, 1) $ hV2 $
    show (h : G) * (1 : G) ∈ _, by rw mul_one; exact h.2),
  have Him := λ (h : U), classical.some_spec (hV3 (h, 1) $ hV2 $
    show (h : G) * (1 : G) ∈ _, by rw mul_one; exact h.2),
  have Him1 := λ h : U, classical.some (Him h),
  have Him2 := λ h : U, classical.some_spec (Him h),
  let W1 := λ h : U, classical.some (Him1 h),
  have HW1X11 := λ h : U, classical.some_spec (Him1 h),
  let X1 := λ h : U, classical.some (HW1X11 h),
  let HW1X1 := λ h : U, classical.some_spec (HW1X11 h),
  let W : U → set G := λ h : U, W1 h ∩ U,
  let X : U → set G := λ h : U, X1 h ∩ U,
  have hW1 : ∀ h : U, is_open (W h) := λ h, (HW1X1 h).1.inter U.2.1.1,
  have hW2 : ∀ h : U, (h : G) ∈ W h := λ h,
    set.mem_inter (show _ ∈ classical.some _, by
    {have Hx := (Him2 ⟨h, h.2⟩).1, rw ←(HW1X1 ⟨h, h.2⟩).2.2 at Hx, exact Hx.1 }) h.2,
  have hW3 : (U : set G) ⊆ set.Union (λ h : U, W h) := λ x hx,
    set.mem_Union.2 ⟨⟨x, hx⟩, hW2 ⟨x, hx⟩⟩,
  have hX1 : ∀ h : U, (1 : G) ∈ X h := λ h,
    set.mem_inter (show _ ∈ classical.some _, by
    { have H1 := (Him2 h).1, rw ←(HW1X1 h).2.2 at H1, exact H1.2 }) U.2.2,
  have hWX1 : ∀ h : U, (λ x : G × G, x.1 * x.2) '' (W h ×ˢ X h) ⊆ Vᶜ := λ h,
  begin
    intros x hx,
    rcases hx with ⟨y, hy⟩,
    have hy2 : y ∈ W1 h ×ˢ X1 h := ⟨hy.1.1.1, hy.1.2.1⟩,
    rw (HW1X1 h).2.2 at hy2,
    rw ←hy.2,
    exact (Him2 h).2 hy2,
  end,
  have hWX2 : ∀ h : U, (λ x : G × G, x.1 * x.2) '' (W h ×ˢ X h) ⊆ n_prods U 2 := λ h,
  begin
    intros x hx,
    rcases hx with ⟨y, hy⟩,
    use (fin.cons ⟨y.1, hy.1.1.2⟩ (λ i, ⟨y.2, hy.1.2.2⟩) : fin 2 → U),
    simpa using hy.2,
  end,
  obtain ⟨t, ht⟩ := is_compact.elim_finite_subcover (compact_of_is_closed_subset G.1.1.2.1 U.2.1.2
    (set.subset_univ _)) W hW1 hW3,
  let X2 := set.Inter (λ i : t, X i),
  let Y := X2 ∩ invs X2,
  have hY1 : is_open Y :=
  begin
    have hX2 : is_open X2 := is_open_Inter (λ t, (HW1X1 _).2.1.inter U.2.1.1),
    exact hX2.inter (invs_open _ _ hX2),
  end,
  have hY2 : (1 : G) ∈ Y := ⟨set.mem_Inter.2 (λ i, hX1 i),
    ⟨⟨1, set.mem_Inter.2 (λ i, hX1 i)⟩, inv_one⟩⟩,
  have hY3 : Y ⊆ U :=
    (set.inter_subset_left _ _).trans
    (begin
      have hex : ∃ i : U, i ∈ t,
      sorry,
      cases hex with i hi,
      exact set.Inter_subset_of_subset ⟨i, hi⟩ (set.inter_subset_right _ _)
    end),
  have hY4 : (λ g : G × G, g.1 * g.2) '' ((U : set G) ×ˢ Y) ⊆ U := sorry,
  have hY5 : ∀ i : ℕ, (λ g : G × G, g.1 * g.2) '' ((U : set G) ×ˢ n_prods Y (i + 1)) ⊆ U := sorry,
  let S' : subgroup G :=
  { carrier := set.Union (λ i : ℕ, n_prods Y (i + 1)),
    mul_mem' := sorry,
    one_mem' := sorry,
    inv_mem' := sorry },
  have hS'1 : is_open (S' : set G) := sorry,
  have hS'2 : (S' : set G) ⊆ U := sorry,
  let S := inter_conjugates S',
  have hS1 : is_open (S : set G) := sorry,
  have hS2 : S.normal := sorry,
  use ⟨S, hS1, hS2⟩,
  sorry,
end

#exit

/--
The isomorphism between `X` and the explicit limit of `X.diagram`,
induced by lifting `X.as_limit_cone`.
-/
def iso_as_limit_cone_lift : X ≅ (limit_cone X.diagram).X :=
as_iso $ (limit_cone_is_limit _).lift X.as_limit_cone

/--
The isomorphism of cones `X.as_limit_cone` and `Profinite.limit_cone X.diagram`.
The underlying isomorphism is defeq to `X.iso_as_limit_cone_lift`.
-/
def as_limit_cone_iso : X.as_limit_cone ≅ limit_cone _ :=
limits.cones.ext (iso_as_limit_cone_lift _) (λ _, rfl)

/-- `X.as_limit_cone` is indeed a limit cone. -/
def as_limit : category_theory.limits.is_limit X.as_limit_cone :=
limits.is_limit.of_iso_limit (limit_cone_is_limit _) X.as_limit_cone_iso.symm

/-- A bundled version of `X.as_limit_cone` and `X.as_limit`. -/
def lim : limits.limit_cone X.diagram := ⟨X.as_limit_cone, X.as_limit⟩

#exit
def to_disc_quot_functor :
  discrete_quotient_group G ⥤ discrete_quotient G :=
{ obj := discrete_quotient_group.to_discrete_quotient,
  map := λ X Y f, f,
  map_id' := λ X, rfl,
  map_comp' := λ X Y Z f g, rfl }

namespace Profinite
noncomputable def fintype_diag :
  discrete_quotient_group G ⥤ FinGroup :=
to_disc_quot_functor G ⋙ Profinite.fintype_diagram G

/-- An abbreviation for `X.fintype_diagram ⋙ Fintype_to_Profinite`. -/
noncomputable abbreviation diag : discrete_quotient_group G ⥤ Profinite :=
fintype_diag G ⋙ Fintype.to_Profinite

/-- A cone over `X.diagram` whose cone point is `X`. -/
noncomputable def as_limit_cone : category_theory.limits.cone (diag G) :=
{ X := G,
  π := { app := λ S, G.as_limit_cone.π.app S.to_discrete_quotient } }

instance : group (as_limit_cone G).X := by assumption

instance : topological_group (as_limit_cone G).X := by assumption

def hom_to_cone : G ⟶ (Profinite.limit_cone (diag G)).X :=
(Profinite.limit_cone_is_limit (diag G)).lift (as_limit_cone G)
#check Profinite.forget_preserves_limits
#check forget ()
#check preserves_limits
