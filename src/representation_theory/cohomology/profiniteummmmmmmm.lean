import topology.algebra.open_subgroup
import representation_theory.cohomology.ProfiniteGroup
import representation_theory.cohomology.topgrps
import data.set.pointwise
universes v u

noncomputable theory

open category_theory

set_option old_structure_cmd true

@[ext] structure discrete_quotient_group
  (G : Type*) [group G] [topological_space G]
  extends discrete_quotient G :=
(mul : ∀ {w x y z}, rel w x → rel y z → rel (w * y) (x * z))

def open_subgroup.to_disc_of_normal {G : Type*} [group G] [topological_space G]
  [topological_group G] (H : open_subgroup G) [subgroup.normal (H : subgroup G)] :
  discrete_quotient_group G :=
{ mul := λ w x y z, (quotient_group.con (H : subgroup G)).mul,
  ..H.to_discrete_quotient }

namespace discrete_quotient_group

variables {G : Type*} [group G] [topological_space G] [topological_group G]

def con (Q : discrete_quotient_group G) : con G :=
{ r := Q.rel,
  iseqv := Q.equiv,
  mul' := Q.mul }

lemma con_inj : function.injective (@discrete_quotient_group.con G _ _ _) := sorry

instance : has_coe_to_sort (discrete_quotient_group G) (Type*) :=
⟨λ X, X.to_discrete_quotient⟩

instance (Q : discrete_quotient_group G) : group Q := Q.con.group

open quotient_group

lemma to_disc_quot_inj :
  function.injective (@discrete_quotient_group.to_discrete_quotient G _ _) :=
begin
  intros X Y h,
  ext1,
  exact (discrete_quotient.ext_iff _ _).1 h,
end

def proj (Q : discrete_quotient_group G) : G →* Q := Q.con.mk'

lemma proj_eq_to_discrete_quotient_eq (Q : discrete_quotient_group G) :
  (Q.proj : G → Q) = Q.to_discrete_quotient.proj := rfl

lemma proj_ker_eq (Q : discrete_quotient_group G) :
  (Q.proj.ker : set G) = set_of (Q.rel 1) :=
begin
  dunfold proj,
  ext,
  split,
  { rintro (hx : _ = _),
    rw ←Q.proj.map_one at hx,
    exact quotient.eq'.1 hx.symm },
  { rintro (hx : Q.rel 1 x),
    show _ = _,
    rw ←Q.proj.map_one,
    exact quotient.eq'.2 (Q.equiv.2.1 hx) }
end

lemma r_eq (Q : discrete_quotient_group G) :
  @setoid.r _ (quotient_group.left_rel (Q.proj.ker)) = @setoid.r _ Q.con.to_setoid :=
begin
  rw left_rel_eq,
  ext x y,
  show _ = _ ↔ _,
  simp only [map_mul, map_inv, con.rel_eq_coe, inv_mul_eq_one],
  exact quotient.eq',
end

lemma rel_eq (Q : discrete_quotient_group G) :
  (quotient_group.left_rel Q.proj.ker).rel = Q.rel :=
r_eq Q

lemma coe_proj_eq_iff_proj_eq (Q : discrete_quotient_group G) (x y : G) :
  (x : G ⧸ Q.proj.ker) = (y : G ⧸ Q.proj.ker) ↔ Q.proj x = Q.proj y :=
begin
  show quotient.mk' _ = quotient.mk' _ ↔ quotient.mk' _ = quotient.mk' _,
  rw [quotient.eq_rel, quotient.eq_rel, rel_eq],
  refl,
end

end discrete_quotient_group

--instance : partial_order (open_normal )
@[ancestor open_subgroup]
structure open_normal (G : Type*) [group G] [topological_space G] extends
  open_subgroup G :=
(normal' : subgroup.normal _to_subgroup)

namespace open_normal

variables {G : Type*} [group G] [topological_space G]

def mk' (U : subgroup G) (hU : is_open (U : set G)) (hn : U.normal) :
  open_normal G := open_normal.mk U hU hn

instance has_coe_set : has_coe_t (open_normal G) (set G) := ⟨λ U, U.to_open_subgroup⟩

instance : has_mem G (open_normal G) := ⟨λ g U, g ∈ (U : set G)⟩

instance has_coe_open_subgroup : has_coe_t (open_normal G) (open_subgroup G) := ⟨open_normal.to_open_subgroup⟩

open topological_space
variables {U V : open_normal G} (g : G)

instance has_coe_subgroup : has_coe_t (open_normal G) (subgroup G) :=
⟨λ U, U.to_open_subgroup.to_subgroup⟩

instance has_coe_opens : has_coe_t (open_normal G) (topological_space.opens G) :=
⟨λ U, ⟨U, U.is_open'⟩⟩

@[simp, norm_cast] lemma coe_mk'
  (U : subgroup G) (hU : is_open (U : set G)) (hn : U.normal) :
  (mk' U hU hn : subgroup G) = U := rfl

@[simp, norm_cast] lemma mem_coe : g ∈ (U : set G) ↔ g ∈ U := iff.rfl
@[simp, norm_cast] lemma mem_coe_opens : g ∈ (U : opens G) ↔ g ∈ U := iff.rfl
@[simp, norm_cast]
lemma mem_coe_subgroup : g ∈ (U : subgroup G) ↔ g ∈ U := iff.rfl

lemma coe_injective : function.injective (coe : open_normal G → set G) :=
by { rintros ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨h⟩, congr, }

@[ext]
lemma ext (h : ∀ x, x ∈ U ↔ x ∈ V) : (U = V) := coe_injective $ set.ext h

lemma ext_iff : (U = V) ↔ (∀ x, x ∈ U ↔ x ∈ V) := ⟨λ h x, h ▸ iff.rfl, ext⟩

lemma ext_iff' : U = V ↔ (U : subgroup G) = (V : subgroup G) :=
by rw [ext_iff, set_like.ext_iff]; refl

variables {G}

instance normal (U : open_normal G) : (U : subgroup G).normal :=
U.normal'

instance normal'' (U : open_normal G) : (U.to_open_subgroup : subgroup G).normal :=
open_normal.normal _

variables [topological_group G]

def to_discrete_quotient_group (U : open_normal G) :
  discrete_quotient_group G :=
@open_subgroup.to_disc_of_normal _ _ _ _ U.to_open_subgroup _

open quotient_group

lemma rel_eq_left_rel_r (U : open_normal G) :
  @setoid.r _ (open_normal.to_discrete_quotient_group U).con.to_setoid
    = @setoid.r _ (left_rel (U : subgroup G)) :=
by rw left_rel_eq

lemma rel_eq_left_rel (U : open_normal G) :
  (open_normal.to_discrete_quotient_group U).rel = (left_rel (U : subgroup G)).rel :=
rel_eq_left_rel_r _

lemma proj_ker (U : open_normal G) :
  (open_normal.to_discrete_quotient_group U).proj.ker = U :=
begin
  show monoid_hom.ker (con.mk' _) = _,
  rw ←quotient_group.ker_mk (U : subgroup G),
  refl,
end

end open_normal
namespace discrete_quotient_group

variables (G : Type*) [group G] [topological_space G] [topological_group G]

open open_normal

def equiv_open_normal : discrete_quotient_group G ≃ open_normal G :=
{ to_fun := λ Q, open_normal.mk' Q.proj.ker (by rw proj_ker_eq; exact (Q.clopen _).1)
    infer_instance,
  inv_fun := λ N, open_normal.to_discrete_quotient_group N,
  left_inv := λ Q,
  begin
    ext x y,
    dsimp,
    rw [rel_eq_left_rel, coe_mk', rel_eq],
  end,
  right_inv := λ N,
  begin
    dsimp,
    rw ext_iff',
    exact @quotient_group.ker_mk G _ (N : subgroup G) _,
  end }

variables {G}

instance : partial_order (discrete_quotient_group G) :=
partial_order.lift (@con G _ _ _) con_inj

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

end discrete_quotient_group
namespace open_normal
variables {G : Type*} [group G] [topological_space G] [topological_group G]
open discrete_quotient_group
instance : partial_order (open_normal G) :=
partial_order.lift to_discrete_quotient_group (equiv_open_normal G).symm.bijective.1

instance : has_top (open_normal G) :=
{ top := equiv_open_normal G (⊤ : discrete_quotient_group G) }

instance : order_top (open_normal G) :=
order_top.lift to_discrete_quotient_group (λ a b, id) ((equiv_open_normal G).left_inv _)

instance : semilattice_inf (open_normal G) :=
{ inf := λ A B, equiv_open_normal G (A.to_discrete_quotient_group ⊓ B.to_discrete_quotient_group),
  inf_le_left := sorry,
  inf_le_right := sorry,
  le_inf := sorry,
  .. open_normal.partial_order }

end open_normal
namespace discrete_quotient_group

variables {G : Type*} [group G] [topological_space G] [topological_group G]
open open_normal

lemma umm (U V : discrete_quotient_group G) (hUV : U ≤ V) :
  U.to_discrete_quotient ≤ V.to_discrete_quotient := hUV

def of_le {A B : discrete_quotient_group G} (h : A ≤ B) : A →* B :=
{ to_fun := discrete_quotient.of_le h,
  map_one' := rfl,
  map_mul' := λ x y, quotient.induction_on₂' x y (λ z w, rfl) }

instance : inhabited (discrete_quotient_group G) := ⟨⊤⟩

lemma fiber_eq (S : discrete_quotient_group G) (x : G) :
  S.proj ⁻¹' ({S.proj x}) = set_of (S.rel x) :=
discrete_quotient.fiber_eq _ _

lemma exists_of_compat [compact_space G] (Qs : Π (Q : discrete_quotient_group G), Q)
  (compat : ∀ (A B : discrete_quotient_group G) (h : A ≤ B), of_le h (Qs _) = Qs _) :
  ∃ x : G, ∀ Q : discrete_quotient_group G, Q.proj x = Qs _ :=
begin
  obtain ⟨x,hx⟩ := is_compact.nonempty_Inter_of_directed_nonempty_compact_closed
    (λ (Q : discrete_quotient_group G), Q.proj ⁻¹' {Qs Q}) (λ A B, _) (λ i, _)
    (λ i, by simp_rw proj_eq_to_discrete_quotient_eq; exact (discrete_quotient.fiber_closed _ _).is_compact)
    (λ i, by simp_rw proj_eq_to_discrete_quotient_eq; exact discrete_quotient.fiber_closed _ _),
  { refine ⟨x, λ Q, _⟩,
    specialize hx _ ⟨Q,rfl⟩,
    dsimp at hx,
    rcases discrete_quotient.proj_surjective _ (Qs Q) with ⟨y,hy⟩,
    rwa ← hy at * },
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

end discrete_quotient_group
namespace ProfiniteGroup

section
variables (G : Type*) [group G] [topological_space G] [topological_group G]

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

end
section
variables {G : ProfiniteGroup}

lemma lemma1 (x : G) (H : x ≠ 1) :
  ∃ (U : {U : set G // is_clopen U ∧ (1 : G) ∈ U}), x ∉ (U : set G) :=
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

open_locale pointwise

def inter_conjugates (H : subgroup G) : subgroup G :=
Inf (set.range (λ g : conj_act G, g • H))

variables (U : {U : set G // is_clopen U ∧ (1 : G) ∈ U})

lemma lemma3 : is_compact ((U : set G) ×ˢ (U : set G)) :=
(compact_of_is_closed_subset G.1.1.2.1 U.2.1.2 (set.subset_univ _)).prod
  (compact_of_is_closed_subset G.1.1.2.1 U.2.1.2 (set.subset_univ _))

lemma lemma4 : is_open ((λ g : G × G, g.1 * g.2) ⁻¹' (Uᶜ ∩ n_prods U 2)ᶜ) :=
  is_open.preimage continuous_mul (is_open_compl_iff.2 $ is_compact.is_closed $ lemma2 U U.2.1)

lemma lemma5 (U : set G) : U ⊆ (Uᶜ ∩ n_prods U 2)ᶜ := λ y hy, show y ∈ (_ ∩ _)ᶜ, by simpa using hy

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
variables (H : subgroup G)
#check conj_act
open mul_action
#check mul_action.of_End_hom

instance : subgroup_class (subgroup G) (conj_act G) :=
by dunfold conj_act; apply_instance

lemma smul_eq_iff_mem_normalizer {g : conj_act G} {H : subgroup G} :
  g • H = H ↔ g ∈ H.normalizer :=
begin
  rw [eq_comm, set_like.ext_iff, ←inv_mem_iff, subgroup.mem_normalizer_iff, inv_inv],
  exact forall_congr (λ h, iff_congr iff.rfl ⟨λ ⟨a, b, c⟩, (congr_arg _ c).mp
    ((congr_arg (∈ H.1) (mul_aut.inv_apply_self G (mul_aut.conj g) a)).mpr b),
    λ hh, ⟨(mul_aut.conj g)⁻¹ h, hh, mul_aut.apply_inv_self G (mul_aut.conj g) h⟩⟩),
end

lemma stabilizer_eq_normalizer :
  stabilizer (conj_act G) H = H.normalizer :=
subgroup.ext (λ g, smul_eq_iff_mem_normalizer)

def equiv_quotient_of_eq {H J : subgroup G} (hHJ : H = J) :
  G ⧸ H ≃ G ⧸ J :=
quotient.congr (equiv.refl _) (λ x y, by
  rw [quotient_group.left_rel_eq, hHJ, quotient_group.left_rel_eq]; refl)

def orbit_iso_quotient_normalizer : orbit (conj_act G) H ≃ G ⧸ H.normalizer :=
(orbit_equiv_quotient_stabilizer (conj_act G) H).trans $
  equiv_quotient_of_eq (stabilizer_eq_normalizer H)

def quotient_to_conj_orbit : G ⧸ H → orbit (conj_act G) H :=
(orbit_iso_quotient_normalizer H).symm ∘ prod.fst
  ∘ (subgroup.quotient_equiv_prod_of_le subgroup.le_normalizer)

lemma quotient_to_conj_orbit_surj : function.surjective (quotient_to_conj_orbit H) :=
begin
  unfold quotient_to_conj_orbit,
  simp only [equiv_like.comp_surjective, equiv_like.surjective_comp, prod.fst_surjective]
end

instance hello [h : fintype (G ⧸ H)] : fintype (orbit (conj_act G) H) :=
fintype.of_surjective _ (quotient_to_conj_orbit_surj H)

abbreviation S := inter_conjugates (S' U)

lemma is_open.conj_act {U : subgroup G} (g : conj_act G) (hU : is_open (U : set G)) :
  is_open (g • (U : set G)) :=
begin
  have : is_open_map ((λ x : G, x * g⁻¹) ∘ (λ x : G, (g * x : G))) :=
    (is_open_map_mul_right _).comp  (is_open_map_mul_left _),
  exact this _ hU,
end

lemma hS1 : is_open (S U : set G) :=
begin
  show is_open (set.Inter _),
  refine is_open_bInter _ _,
  { constructor,
    exact @ProfiniteGroup.hello _ (S' U) (open_subgroup.quotient_fintype ⟨S' U, hS'1 U⟩) },
  { rintros i ⟨g, h⟩,
    rw ←h,
    dsimp,
    exact is_open.conj_act _ (hS'1 U) },
end

lemma hS2 : (S U).normal :=
begin
  constructor,
  intros n h g,
  show _ ∈ set.Inter _,
  rw set.mem_Inter₂,
  rintros H ⟨x, hx⟩,
  rcases set.mem_Inter₂.1 h ((g⁻¹ * x : conj_act G) • S' U)
    (set.mem_range_self _) with ⟨w, hwU, hw⟩,
  rw [←hx, ←hw],
  dsimp,
  use [w, hwU],
  show x * w * x⁻¹ = _ * (g⁻¹ * x * _ * (g⁻¹ * x)⁻¹) * _,
  simp only [mul_assoc, mul_inv_rev, inv_inv, mul_inv_cancel_left, mul_right_inv, mul_one],
end

open discrete_quotient_group
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
  exact hU (hS'2 U (set.mem_Inter₂.1 hx (S' U) ⟨1, one_smul _ _⟩)),
end

lemma eq_of_proj_eq {x y : G} (h : ∀ Q : discrete_quotient_group G, Q.proj x = Q.proj y) : x = y :=
begin
  rw ←mul_inv_eq_one,
  refine yay _ _,
  intro U,
  have := h (open_normal.to_discrete_quotient_group U),
  rw ←open_normal.proj_ker,
  show _ = _,
  simp [this],
end
/-
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
def lim : limits.limit_cone X.diagram := ⟨X.as_limit_cone, X.as_limit⟩-/
variables (G)

def fintype_diagram :
  discrete_quotient_group G ⥤ FinGroup :=
{ obj := λ G, FinGroup.of G,
  map := λ G H f, discrete_quotient_group.of_le f.le }

noncomputable abbreviation diagram : discrete_quotient_group G ⥤ ProfiniteGroup :=
fintype_diagram G ⋙ FinGroup.to_ProfiniteGroup

/-- A cone over `X.diagram` whose cone point is `X`. -/
noncomputable def as_limit_cone_cone : category_theory.limits.cone G.diagram :=
{ X := G,
  π := { app := λ G, ⟨G.proj, G.to_discrete_quotient.proj_is_locally_constant.continuous⟩ } }

instance fds : group (as_limit_cone_cone G).X := G.group
instance fdsfd : topological_group (as_limit_cone_cone G).X := G.topological_group

instance is_iso_as_limit_cone_lift :
  is_iso ((limit_cone_is_limit G.diagram).lift G.as_limit_cone_cone) :=
is_iso_of_bij _
begin
  refine ⟨λ a b, _, λ a, _⟩,
  { intro h,
    refine eq_of_proj_eq (λ S, _),
    apply_fun (λ f : (limit_cone_cone G.diagram).X, f.val S) at h,
    exact h },
  { obtain ⟨b, hb⟩ := discrete_quotient_group.exists_of_compat
      (λ S, a.val S) (λ _ _ h, a.prop (hom_of_le h)),
    refine ⟨b, _⟩,
    ext S : 3,
    apply hb },
end

def as_limit_cone : limits.limit_cone G.diagram :=
{ cone := G.as_limit_cone_cone,
  is_limit := limits.is_limit.of_point_iso (limit_cone_is_limit G.diagram) }

instance : limits.has_limit G.diagram := ⟨⟨G.as_limit_cone⟩⟩

def limit_iso : limits.limit G.diagram ≅ G :=
limits.limit.iso_limit_cone G.as_limit_cone

end
end ProfiniteGroup
