import topology.category.Profinite.as_limit
import tactic.transport
import group_theory.quotient_group
import topology.algebra.open_subgroup
import representation_theory.cohomology.ProfiniteGroup
import tactic.omega
universes v u

noncomputable theory

open category_theory

variables (G : ProfiniteGroup)

set_option old_structure_cmd true
/-
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
end-/

abbreviation open_normal :=
order_dual $ @subtype (subgroup G) (λ U, is_open (U : set G) ∧ U.normal)

instance : has_coe (open_normal G) (subgroup G) :=
⟨λ U, U.1⟩

instance open_normal_normal (U : open_normal G) : (U : subgroup G).normal := U.2.2

def n_prods {G : Type*} [monoid G] (T : set G) (n : ℕ) : set G :=
{ g | ∃ f : fin n → T, (list.of_fn (coe ∘ f)).prod = g }

lemma continuous_list_of_fn_prod
  {G : Type*} [topological_space G] [group G] [topological_group G] (n : ℕ) :
  continuous (λ f : fin n → G, (list.of_fn f).prod) :=
begin
  simp_rw list.of_fn_eq_map,
  refine continuous_list_prod _ (λ i hi, continuous_apply _),
end

lemma is_open_fin_pi {G : Type*} [topological_space G] [group G] [topological_group G] (n : ℕ)
  (U : set G) (hU : is_open U) :
  is_open ({f : fin n → G | ∀ i : fin n, f i ∈ U}) :=
begin
  convert @is_open_set_pi (fin n) (λ i, G) _ set.univ (λ i, U) set.finite_univ (λ i _, hU),
  simp only [set.mem_univ, forall_true_left],
end

lemma is_closed_fin_pi {G : Type*} [topological_space G] [group G] [topological_group G] (n : ℕ)
  (U : set G) (hU : is_closed U) :
  is_closed ({f : fin n → G | ∀ i : fin n, f i ∈ U}) :=
begin
  convert @is_closed_set_pi (fin n) (λ i, G) _ set.univ (λ i, U) (λ i _, hU),
  simp only [set.mem_univ, forall_true_left],
end

lemma n_prods_as_image {G : Type*} [monoid G] (T : set G) (n : ℕ) :
  n_prods T n = (λ f : fin n → G, (list.of_fn f).prod) '' ({f : fin n → G | ∀ i : fin n, f i ∈ T}) :=
begin
  ext,
  split,
  rintros ⟨f, rfl⟩,
  use (coe ∘ f),
  split,
  exact (λ i, (f i).2),
  simp only,
  rintros ⟨f, hf, rfl⟩,
  use (λ i, ⟨f i, hf i⟩),
  congr,
end

lemma one_prods {G : Type*} [monoid G] (T : set G) :
  n_prods T 1 = T :=
begin
  ext,
  split,
  { rintros ⟨f, rfl⟩,
    simp },
  { intro hx,
    use fin.cons ⟨x, hx⟩ default,
    simp, }
end

open_locale pointwise

lemma two_prods {G : Type*} [monoid G] (T : set G) :
  n_prods T 2 = T * T :=
set.ext $ λ x,
⟨by rintros ⟨f, rfl⟩; exact ⟨f 0, f 1, (f 0).2, (f 1).2, by simp⟩,
  by rintros ⟨y, z, hy, hz, rfl⟩; exact ⟨fin.cons ⟨y, hy⟩ (λ i, ⟨z, hz⟩), by simp⟩⟩

lemma n_prods_succ {G : Type*} [monoid G] (T : set G) (n : ℕ) :
  T * n_prods T n = n_prods T (n + 1) :=
set.ext $ λ x, ⟨by rintros ⟨y, z, (hy : y ∈ T), ⟨f, (rfl : _ = z)⟩, rfl⟩;
    exact ⟨fin.cons ⟨y, hy⟩ f, by simp⟩,
  by rintros ⟨f, rfl⟩; exact ⟨(f 0 : G), (list.of_fn (coe ∘ fin.tail f)).prod,
    (f 0).2, ⟨fin.tail f, rfl⟩, by simpa⟩⟩

/-lemma is_open_of_is_closed_of_has_open_subset {U V : set G} (hU : is_open U) (hUV : U ⊆ V) (hV : is_closed V) :
  is_open V :=
sorry-/

lemma is_open_of_n_prods {U : set G} (hU : is_open U) (n : ℕ) :
  is_open (n_prods U (n + 1)) :=
begin
  induction n with n hn,
  { rwa one_prods },
  { rw ←n_prods_succ,
    exact is_open.mul_left hn }
end

lemma mul_subset_trans {G : Type*} [monoid G] {S T U V W : set G}
  (HS : S * T ⊆ U) (HV : U * V ⊆ W) : S * T * V ⊆ W :=
begin
  rintros x ⟨y, z, ⟨w, v, hw, hv, rfl⟩, hz, rfl⟩,
  exact HV ⟨w * v, z, HS ⟨w, v, hw, hv, rfl⟩, hz, rfl⟩,
end

lemma mul_subset_left {G : Type*} [monoid G] {S T U W : set G}
  (HS : S ⊆ T) (HT : T * U ⊆ W) : S * U ⊆ W :=
begin
  rintros x ⟨y, z, hy, hz, rfl⟩,
  exact HT ⟨y, z, HS hy, hz, rfl⟩,
end

lemma inv_open (T : set G) (hT : is_open T) : is_open T⁻¹ :=
is_open.preimage continuous_inv hT

lemma list.of_fn_append {G : Type*} [monoid G] {m n o : ℕ} (f : fin m → G) (g : fin n → G)
  (h : o = m + n) :
  list.of_fn (fin.append h f g) = list.of_fn f ++ list.of_fn g :=
begin
  rw [list.of_fn_congr h, list.of_fn_add],
  congr,
  { ext,
    simp only [fin.append, dif_pos, fin.coe_cast, fin.coe_cast_add, not_lt,
      fin.eta, dite_eq_left_iff],
    intro H,
    exact false.elim (not_lt.2 H x.2) },
  { ext,
    simp [fin.append, dif_neg]}
end

lemma fin.comp_append {α β : Type*} (F : α → β) {m n o : ℕ} (f : fin m → α) (g : fin n → α)
  (ho : o = m + n) : F ∘ fin.append ho f g = fin.append ho (F ∘ f) (F ∘ g) :=
begin
  ext,
  unfold fin.append,
  split_ifs,
  { simp only [dif_pos h, function.comp_app] },
  { simp only [dif_neg h, function.comp_app] }
end

variables {G}

lemma lemma1 (x : G) (H : x ≠ 1) : ∃ (U : {U : set G // is_clopen U ∧ (1 : G) ∈ U}), x ∉ (U : set G) :=
not_forall.1 $ λ H1, H $
begin
  have h' := set.mem_Inter.2 H1,
  rw [←connected_component_eq_Inter_clopen,
    totally_disconnected_space_iff_connected_component_singleton.1
    Profinite.totally_disconnected_space (1 : G)] at h',
  rw set.mem_singleton_iff.1 h',
end

lemma lemma2 (U : set G) (hU : is_clopen U) : is_compact (Uᶜ ∩ n_prods U 2) :=
(compact_of_is_closed_subset G.1.1.2.1 (is_closed_compl_iff.2 hU.1) (set.subset_univ _)).inter $
by rw [two_prods, ←set.image_mul_prod]; exact ((compact_of_is_closed_subset
  G.1.1.2.1 hU.2 (set.subset_univ _)).prod (compact_of_is_closed_subset G.1.1.2.1 hU.2
  (set.subset_univ _))).image continuous_mul

def inter_conjugates (H : subgroup G) : subgroup G :=
{ carrier := set.Inter (λ g, (λ h : G, g * h * g⁻¹) '' H),
  mul_mem' := λ x z hx hz, set.mem_Inter.2 $ λ g, by
  { rcases set.mem_Inter.1 hx g with ⟨w, hw, rfl⟩,
    rcases set.mem_Inter.1 hz g with ⟨y, hy, rfl⟩,
    exact ⟨w * y, H.mul_mem hw hy, by simp⟩ },
  one_mem' := set.mem_Inter.2 $ λ g, ⟨1, H.one_mem, by simp⟩,
  inv_mem' := λ x hx, set.mem_Inter.2 $ λ g, by
  { rcases set.mem_Inter.1 hx g with ⟨y, hy, rfl⟩,
    exact ⟨y⁻¹, H.inv_mem hy, by simp⟩ } }

variables (U : {U : set G // is_clopen U ∧ (1 : G) ∈ U})

lemma lemma3 : is_compact ((U : set G) ×ˢ (U : set G)) :=
(compact_of_is_closed_subset G.1.1.2.1 U.2.1.2 (set.subset_univ _)).prod
  (compact_of_is_closed_subset G.1.1.2.1 U.2.1.2 (set.subset_univ _))

lemma lemma4 : is_open ((λ g : G × G, g.1 * g.2) ⁻¹' (Uᶜ ∩ n_prods U 2)ᶜ) :=
  is_open.preimage continuous_mul (is_open_compl_iff.2 $ is_compact.is_closed $ lemma2 U U.2.1)

lemma lemma5 : (U : set G) ⊆ (Uᶜ ∩ n_prods U 2)ᶜ := λ y hy, show y ∈ (_ ∩ _)ᶜ, by simpa using hy

abbreviation F (h : U) : set (G × G) :=
classical.some (((topological_space.is_topological_basis_opens).prod
topological_space.is_topological_basis_opens).is_open_iff.1 (lemma4 U) (h, 1) $ lemma5 U $
  show (h : G) * (1 : G) ∈ _, by rw mul_one; exact h.2)

variables {U}

lemma HF (h : U) : ∃ (H : ∃ (a b : set ↥G), is_open a ∧ is_open b ∧ a ×ˢ b = F U h), ((h, 1) : G × G) ∈ F U h
  ∧ F U h ⊆ (((λ (g : ↥G × ↥G), g.fst * g.snd) ⁻¹' ((U : set G)ᶜ ∩ n_prods ↑U 2)ᶜ)) :=
classical.some_spec (((topological_space.is_topological_basis_opens).prod
topological_space.is_topological_basis_opens).is_open_iff.1 (lemma4 U) (h, 1) $ lemma5 U $
  show (h : G) * (1 : G) ∈ _, by rw mul_one; exact h.2)

lemma HF1 (h : U) : ∃ (a b : set G), is_open a ∧ is_open b ∧ a ×ˢ b = F U h :=
classical.some (HF h)

lemma HF2 (h : U) : ((h, 1) : G × G) ∈ F U h
  ∧ F U h ⊆ (((λ (g : ↥G × ↥G), g.fst * g.snd) ⁻¹' ((U : set G)ᶜ ∩ n_prods ↑U 2)ᶜ)) :=
classical.some_spec (HF h)

abbreviation W1 (h : U) : set G := classical.some (HF1 h)
abbreviation X1 (h : U) : set G := classical.some (classical.some_spec (HF1 h))

lemma HW1X1 (h : U) : is_open (W1 h) ∧ is_open (X1 h) ∧ W1 h ×ˢ X1 h = F U h :=
classical.some_spec (classical.some_spec (HF1 h))

abbreviation W (h : U) : set G := W1 h ∩ U
abbreviation X (h : U) : set G := X1 h ∩ U

lemma hW1 (h : U) : is_open (W h) := (HW1X1 h).1.inter U.2.1.1
lemma hW2 (h : U) : (h : G) ∈ W h := set.mem_inter (by
  {have Hx := (HF2 h).1, rw ←(HW1X1 h).2.2 at Hx, exact Hx.1 }) h.2

variables (U)

lemma hW3 : (U : set G) ⊆ set.Union (λ h : U, W h) :=
λ x hx, set.mem_Union.2 ⟨⟨x, hx⟩, hW2 ⟨x, hx⟩⟩

variables {U}

lemma hX1 (h : U) : (1 : G) ∈ X h :=
set.mem_inter (by { have H1 := (HF2 h).1, rw ←(HW1X1 h).2.2 at H1, exact H1.2 }) U.2.2

lemma hWX1 (h : U) : (λ x : G × G, x.1 * x.2) '' (W h ×ˢ X h) ⊆ (Uᶜ ∩ n_prods U 2)ᶜ :=
begin
  intros x hx,
  rcases hx with ⟨y, hy⟩,
  have hy2 : y ∈ W1 h ×ˢ X1 h := ⟨hy.1.1.1, hy.1.2.1⟩,
  rw (HW1X1 h).2.2 at hy2,
  rw ←hy.2,
  exact (HF2 h).2 hy2,
end

lemma hWX2 (h : U) : (λ x : G × G, x.1 * x.2) '' (W h ×ˢ X h) ⊆ n_prods U 2 :=
begin
  intros x hx,
  rcases hx with ⟨y, hy⟩,
  use (fin.cons ⟨y.1, hy.1.1.2⟩ (λ i, ⟨y.2, hy.1.2.2⟩) : fin 2 → U),
  simpa using hy.2,
end

variables (U)

abbreviation t : finset U :=
classical.some (is_compact.elim_finite_subcover (compact_of_is_closed_subset G.1.1.2.1 U.2.1.2
    (set.subset_univ _)) W hW1 $ hW3 U)

lemma ht : (U : set G) ⊆ ⋃ (i : ↥U) (H : i ∈ t U), W i :=
classical.some_spec (is_compact.elim_finite_subcover (compact_of_is_closed_subset G.1.1.2.1 U.2.1.2
    (set.subset_univ _)) W hW1 $ hW3 U)

abbreviation X2 := set.Inter (λ i : t U, X (i : U))
abbreviation Y := X2 U ∩ (X2 U)⁻¹

lemma hY1 : is_open (Y U) :=
begin
  have hX2 : is_open (X2 U) := is_open_Inter (λ t, (HW1X1 _).2.1.inter U.2.1.1),
  exact hX2.inter (inv_open _ _ hX2),
end

lemma hY2 : (1 : G) ∈ Y U :=
⟨set.mem_Inter.2 (λ i, hX1 i), by rw [set.mem_inv, inv_one]; exact set.mem_Inter.2 (λ i, hX1 i)⟩

lemma hte : ∃ i : U, i ∈ t U :=
begin
  rw ←not_forall_not,
  intros hnot,
  refine set.not_mem_empty (1 : G) _,
  rw [←@set.bUnion_empty _ _ (λ i : U, W i), ←set.eq_empty_iff_forall_not_mem.2 hnot],
  exact ht U U.2.2,
end

lemma hY3 : Y U ⊆ U :=
(set.inter_subset_left _ _).trans
(begin
  cases hte U with i hi,
  exact set.Inter_subset_of_subset ⟨i, hi⟩ (set.inter_subset_right _ _)
end)

lemma hVU : ((U : set G)ᶜ ∩ n_prods U 2)ᶜ ∩ n_prods (U : set G) 2 ⊆ U :=
by simp [set.compl_inter, set.union_inter_distrib_right]

lemma hY4' : (λ g : G × G, g.1 * g.2) '' set.Union (λ i : t U, W (i : U) ×ˢ X (i : U)) ⊆ U :=
by rw set.image_Union; exact (set.Union_subset $ λ i,
  (set.subset_inter (hWX1 (i : U)) (hWX2 (i : U))).trans $ hVU U)

lemma hY4 : (U : set G) * Y U ⊆ U :=
begin
  refine set.subset.trans _ (hY4' U),
  rw ←set.image_mul_prod,
  refine set.image_subset _ _,
  intros z hz,
  rcases set.mem_Union₂.1 (ht U hz.1) with ⟨i, ⟨hti, hi⟩⟩,
  rw set.mem_Union,
  refine ⟨⟨i, hti⟩, hi, _⟩,
  convert set.mem_Inter.1 hz.2.1 ⟨i, hti⟩,
end

lemma hY5 (i : ℕ) : (U : set G) * n_prods (Y U) (i + 1) ⊆ U :=
begin
  induction i with i hi,
  { rw one_prods,
    exact hY4 U },
  { rw [←n_prods_succ, ←mul_assoc],
    exact mul_subset_trans (hY4 U) hi }
end

lemma nth_le_reverse_of_fn {α : Type*} {n : ℕ} (f : fin (n + 1) → α) (i : fin (n + 1)) :
  (list.of_fn f).reverse.nth_le i (by rw [list.length_reverse, list.length_of_fn]; exact i.2)
  = f (⟨n - i, lt_of_le_of_lt (nat.sub_le _ _) (nat.lt_succ_self _)⟩) :=
begin
  have : n - i < n + 1 := lt_of_le_of_lt (nat.sub_le _ _) (nat.lt_succ_self _),
  rw list.nth_le_reverse' (list.of_fn f) i
    (by rw [list.length_reverse, list.length_of_fn]; exact i.2) (by simp [list.length_of_fn, this]),
  have hn : (list.of_fn f).length - 1 - (i : ℕ) < n + 1,
  by rw list.length_of_fn; exact lt_of_le_of_lt (nat.sub_le _ _) (nat.lt_succ_self _),
  have h := list.nth_le_of_fn f ⟨_, hn⟩,
  simp only [fin.coe_mk] at h,
  rw h,
  simp only [list.length_of_fn, nat.add_sub_cancel],
end

lemma nth_le_reverse_of_fn' {α : Type*} {n : ℕ} (f : fin (n + 1) → α) (i : ℕ) (hi : i < n + 1) :
  (list.of_fn f).reverse.nth_le i (by rw [list.length_reverse, list.length_of_fn]; exact hi)
  = f (⟨n - i, lt_of_le_of_lt (nat.sub_le _ _) (nat.lt_succ_self _)⟩) :=
nth_le_reverse_of_fn f ⟨i, hi⟩

lemma reverse_map_of_fn {α β : Type*} {n : ℕ} (F : α → β) (f : fin n → α) :
  (list.map F (list.of_fn f)).reverse = list.of_fn (λ j : fin n,
  F ((list.of_fn f).reverse.nth_le j $ by
    rw [list.length_reverse, list.length_of_fn]; exact j.2)) :=
begin
  revert f,
  induction n with n hn,
  { simp },
  { intro f,
    refine list.ext_le (by simp) _,
    intros i h1 h2,
    simp only [←list.map_reverse],
    rw [list.nth_le_map, nth_le_reverse_of_fn' f, list.nth_le_of_fn', nth_le_reverse_of_fn],
    congr,
    rwa list.length_of_fn at h2, },
end

def S' : subgroup G :=
{ carrier := set.Union (λ i : ℕ, n_prods (Y U) (i + 1)),
  mul_mem' := λ x y hx hy,
  begin
    rcases set.mem_Union.1 hx with ⟨i, ⟨f, rfl⟩⟩,
    rcases set.mem_Union.1 hy with ⟨j, ⟨g, rfl⟩⟩,
    rw set.mem_Union,
    use i + 1 + j,
    use fin.append (add_assoc _ j 1) f g,
    rw [fin.comp_append, list.of_fn_append, list.prod_append],
  end,
  one_mem' :=
  begin
    rw set.mem_Union,
    use 0,
    use fin.cons (⟨1, hY2 U⟩) default,
    simp,
  end,
  inv_mem' := λ x hx,
  begin
    rcases set.mem_Union.1 hx with ⟨i, ⟨f, rfl⟩⟩,
    rw set.mem_Union,
    use i,
    let frev : list G := (list.of_fn (coe ∘ f)).reverse,
    have hfrev1 : ∀ j : fin (i + 1), (j : ℕ) < frev.length :=
    begin
      intro j,
      rw [list.length_reverse, list.length_of_fn],
      exact j.2
    end,
    have hfrev2 : ∀ j : fin (i + 1), (frev.nth_le j (hfrev1 j))⁻¹ ∈ Y U :=
    begin
      intro j,
      obtain ⟨s, hs⟩ := (list.mem_of_fn (coe ∘ f) _).1
        (list.mem_reverse.1 (frev.nth_le_mem j (hfrev1 j))),
      rw ←hs,
      split,
      { exact (f s).2.2 },
      { show _ ∈ X2 U,
        rw inv_inv, exact (f s).2.1 }
    end,
    use (λ j : fin (i + 1), ⟨(frev.nth_le j (hfrev1 j))⁻¹, hfrev2 j⟩),
    rw [list.prod_inv_reverse, reverse_map_of_fn],
    congr,
  end }

lemma nonempty_interior_of_open {G : Type*} [topological_space G] [group G] [topological_group G]
  (U : subgroup G) (hU : is_open (U : set G)) :
  (interior (U : set G)).nonempty :=
begin
  use 1,
  rw interior_eq_iff_open.2 hU,
  exact U.one_mem
end

open_locale classical

/-theorem topological_group.compact_is_open_iff_is_closed_and_finite_index
  {G : Type*} [topological_space G] [group G] [topological_group G]
  [is_compact (@set.univ G)] (U : subgroup G) :
  is_open (U : set G) ↔ is_closed (U : set G) ∧ 0 < U.index :=
begin
  split,
  intro H,
  rcases compact_covered_by_mul_left_translates (by assumption)
    (nonempty_interior_of_open U H),
  split,
  have : ∃ i, i ∈ w :=
  begin
    rw ←not_forall_not,
    intro Hw,
    rw finset.eq_empty_iff_forall_not_mem.2 Hw at h,
    simp only [set.Union_false, set.Union_empty] at h,
    exact h (set.mem_univ 1),
  end,
  cases this with i hi,
  sorry, sorry,
  --have : U = compl (⋃ (g : G) (H : g ∈ finset.erase w i), )
  sorry,
end-/

/-instance : is_cofiltered (discrete_quotient G) :=
{ cocone_objs := λ X Y, ⟨X ⊓ Y, ⟨⟨inf_le_left⟩⟩, ⟨⟨inf_le_right⟩⟩, trivial⟩,
  cocone_maps := λ X Y f g, ⟨X ⊓ Y, ⟨⟨inf_le_left⟩⟩, by ext⟩,
  nonempty := by apply_instance }-/

lemma hS'1 : is_open (S' U : set G) :=
begin
  refine is_open_Union _,
  exact is_open_of_n_prods _ (hY1 U),
end

lemma hS'2 : (S' U : set G) ⊆ U :=
begin
  refine set.Union_subset _,
  intro,
  induction i with i hi,
  rw one_prods,
  exact hY3 U,
  rw ←n_prods_succ,
  refine mul_subset_left (hY3 U) (hY5 U _),
end

abbreviation S := inter_conjugates (S' U)
lemma hS1 : is_open (S U : set G) := sorry
lemma hS2 : (S U).normal :=
begin
  constructor,
  intros n h g,
  show _ ∈ set.Inter _,
  rw set.mem_Inter,
  intro a,
  rcases set.mem_Inter.1 h (g⁻¹ * a) with ⟨y, hy, rfl⟩,
  exact ⟨y, hy, by {dsimp, rw [mul_inv_rev, inv_inv],
    assoc_rw [mul_inv_cancel_left, mul_inv_cancel_right] }⟩
end

theorem yay (x : G) : (∀ U : open_normal G, x ∈ (U : subgroup G)) → x = 1 :=
begin
  contrapose!,
  intro H,
  have := totally_disconnected_space_iff_connected_component_singleton.1
    ProfiniteGroup.totally_disconnected_space (1 : G),
  rw connected_component_eq_Inter_clopen at this,
  obtain ⟨U, hU⟩ := lemma1 x H,
  use ⟨S U, hS1 U, hS2 U⟩,
  show x ∉ set.Inter _,
  intro hx,
  rcases set.mem_Inter.1 hx 1 with ⟨y, hyU, hy⟩,
  simp only [one_mul, inv_one, mul_one] at hy,
  rw hy at hyU,
  exact hU (hS'2 U hyU),
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
