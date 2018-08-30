#exit

import analysis.topology.group_completion


section
variables {E : Type*} [topological_space E] [add_comm_group E] [topological_add_group E]

-- A is a dense subgroup of E, inclusion is denoted by e
variables {A : Type*} [topological_space A] [add_comm_group A] [topological_add_group A]
variables {e : A → E} [is_add_group_hom e] (de : dense_embedding e)
include de

lemma tendsto_sub_comap_self (x₀ : E) :
  tendsto (λ (t : A × A), t.2 - t.1) (comap (λ p : A × A, (e p.1, e p.2)) $ nhds (x₀, x₀)) (nhds 0) :=
begin
  have comm : (λ x : E × E, x.2-x.1) ∘ (λ (t : A × A), (e t.1, e t.2)) = e ∘ (λ (t : A × A), t.2 - t.1),
  { ext t,
    change e t.2 - e t.1 = e (t.2 - t.1),
    rwa ← is_add_group_hom.sub e t.2 t.1 },
  have lim : tendsto (λ x : E × E, x.2-x.1) (nhds (x₀, x₀)) (nhds (e 0)),
    { have := continuous.tendsto (continuous.comp continuous_swap continuous_sub') (x₀, x₀),
      simpa [-sub_eq_add_neg, sub_self, eq.symm (is_add_group_hom.zero e)] using this },
  have := de.tendsto_comap_nhds_nhds lim comm,
  simp [-sub_eq_add_neg, this]
end
end


namespace add_comm_group
variables {α : Type*} {β : Type*} {γ : Type*} [add_comm_group α] [add_comm_group β] [add_comm_group γ]

class is_Z_bilin (f : α × β → γ) : Prop :=
(add_left  : ∀ a a' b, f (a + a', b) = f (a, b) + f (a', b))
(add_right : ∀ a b b', f (a, b + b') = f (a, b) + f (a, b'))


variables (f : α × β → γ) [is_Z_bilin f]

instance is_Z_bilin.comp_swap : is_Z_bilin (f ∘ prod.swap) :=
⟨λ a a' b, is_Z_bilin.add_right f b a a',
 λ a b b', is_Z_bilin.add_left f b b' a⟩

lemma is_Z_bilin.zero_left : ∀ b, f (0, b) = 0 :=
begin
  intro b,
  apply add_self_iff_eq_zero.1,
  rw ←is_Z_bilin.add_left f,
  simp
end

lemma is_Z_bilin.zero_right : ∀ a, f (a, 0) = 0 :=
is_Z_bilin.zero_left (f ∘ prod.swap)

lemma is_Z_bilin.zero : f (0, 0) = 0 :=
is_Z_bilin.zero_left f 0

lemma is_Z_bilin.neg_left  : ∀ a b, f (-a, b) = -f (a, b) :=
begin
  intros a b,
  apply eq_of_sub_eq_zero,
  rw [sub_eq_add_neg, neg_neg, ←is_Z_bilin.add_left f, neg_add_self, is_Z_bilin.zero_left f]
end

lemma is_Z_bilin.neg_right  : ∀ a b, f (a, -b) = -f (a, b) :=
assume a b, is_Z_bilin.neg_left (f ∘ prod.swap) b a

lemma is_Z_bilin.sub_left : ∀ a a' b, f (a - a', b) = f (a, b) - f (a', b) :=
begin
  intros,
  dsimp [algebra.sub],
  rw [is_Z_bilin.add_left f, is_Z_bilin.neg_left f]
end

lemma is_Z_bilin.sub_right : ∀ a b b', f (a, b - b') = f (a, b) - f (a,b') :=
assume a b b', is_Z_bilin.sub_left (f ∘ prod.swap) b b' a
end add_comm_group

open add_comm_group filter set function

-- E, F and G are abelian topological groups, G is complete Hausdorff
variables {E : Type*} [topological_space E] [add_comm_group E] [topological_add_group E]
variables {F : Type*} [topological_space F] [add_comm_group F] [topological_add_group F]
variables {G : Type*} [topological_space G] [add_comm_group G] [topological_add_group G] [complete_space G] [separated G]

variables {ψ : E × F → G} (hψ : continuous ψ) [ψbilin : is_Z_bilin ψ]

include hψ ψbilin

lemma is_Z_bilin.tendsto_zero_left (x₁ : E) : tendsto ψ (nhds (x₁, 0)) (nhds 0) :=
begin
  have := continuous.tendsto hψ (x₁, 0),
  rwa [is_Z_bilin.zero_right ψ] at this
end

lemma is_Z_bilin.tendsto_zero_right (y₁ : F) : tendsto ψ (nhds (0, y₁)) (nhds 0) :=
begin
  have := continuous.tendsto hψ (0, y₁),
  rwa [is_Z_bilin.zero_left ψ] at this
end
omit hψ ψbilin

-- A is a dense subgroup of E, inclusion is denoted by e
variables {A : Type*} [topological_space A] [add_comm_group A] [topological_add_group A]
variables {e : A → E} [is_add_group_hom e] (de : dense_embedding e)
include de

-- A is a dense subgroup of E, inclusion is denoted by e
variables {B : Type*} [topological_space B] [add_comm_group B] [topological_add_group B]
variables {f : B → F} [is_add_group_hom f] (df : dense_embedding f)
include df

namespace dense_embedding
variables {φ : A × B → G} (hφ : continuous φ) [bilin : is_Z_bilin φ]
include hφ bilin

variables (x₀ : E) (y₀ : F) {W' : set G} (W'_nhd : W' ∈ (nhds (0 : G)).sets)
include W'_nhd

private lemma extend_Z_bilin_aux (x₀ : E) (y₁ : B) : ∃ U₂ ∈ (comap e (nhds x₀)).sets,
    ∀ x x' ∈ U₂, φ(x' - x, y₁) ∈ W' :=
begin
  let Nx := nhds x₀,
  let ee := λ u : A × A, (e u.1, e u.2),

  have lim1 : tendsto (λ a : A × A, (a.2 - a.1, y₁)) (filter.prod (comap e Nx) (comap e Nx)) (nhds (0, y₁)),
  { have := tendsto.prod_mk (tendsto_sub_comap_self de x₀) (tendsto_const_nhds : tendsto (λ (p : A × A), y₁) (comap ee $ nhds (x₀, x₀)) (nhds y₁)),
    rw [nhds_prod_eq, prod_comap_comap_eq, ←nhds_prod_eq],
    exact (this : _) },

  have lim := tendsto.comp lim1 (is_Z_bilin.tendsto_zero_right hφ y₁),
  rw tendsto_prod_self_iff at lim,
  exact lim W' W'_nhd,
end


private lemma extend_Z_bilin_key  : ∃ U ∈ (comap e (nhds x₀)).sets, ∃ V ∈ (comap f (nhds y₀)).sets,
      ∀ x x' ∈ U, ∀ y y' ∈ V, φ (x', y') - φ (x, y) ∈ W' :=
begin
  let Nx := nhds x₀,
  let Ny := nhds y₀,
  let dp := dense_embedding.prod de df,
  let ee := λ u : A × A, (e u.1, e u.2),
  let ff := λ u : B × B, (f u.1, f u.2),


  have lim_φ : filter.tendsto φ (nhds (0, 0)) (nhds 0),
  { have := continuous.tendsto hφ (0, 0),
    rwa [is_Z_bilin.zero φ] at this },

  have lim_φ_sub_sub : tendsto (λ (p : (A × A) × (B × B)), φ (p.1.2 - p.1.1, p.2.2 - p.2.1))
    (filter.prod (comap ee $ nhds (x₀, x₀)) (comap ff $ nhds (y₀, y₀))) (nhds 0),
  { have lim_sub_sub :  tendsto (λ (p : (A × A) × B × B), (p.1.2 - p.1.1, p.2.2 - p.2.1))
      (filter.prod (comap ee (nhds (x₀, x₀))) (comap ff (nhds (y₀, y₀)))) (filter.prod (nhds 0) (nhds 0)),
    { have := filter.prod_mono (tendsto_sub_comap_self de x₀) (tendsto_sub_comap_self df y₀),
      rwa prod_map_map_eq at this },
    rw ← nhds_prod_eq at lim_sub_sub,
    exact tendsto.comp lim_sub_sub lim_φ },

  rcases quarter_nhd W' W'_nhd with ⟨W, W_nhd, W4⟩,

  have : ∃ U₁ ∈ (comap e (nhds x₀)).sets, ∃ V₁ ∈ (comap f (nhds y₀)).sets,
    ∀ x x' ∈ U₁, ∀ y y' ∈ V₁,  φ (x'-x, y'-y) ∈ W,
  { have := tendsto_prod_iff.1 lim_φ_sub_sub W W_nhd,
    repeat { rw [nhds_prod_eq, ←prod_comap_comap_eq] at this },
    rcases this with ⟨U, U_in, V, V_in, H⟩,
    rw [mem_prod_same_iff] at U_in V_in,
    rcases U_in with ⟨U₁, U₁_in, HU₁⟩,
    rcases V_in with ⟨V₁, V₁_in, HV₁⟩,
    existsi [U₁, U₁_in, V₁, V₁_in],
    intros x x' x_in x'_in y y' y_in y'_in,
    exact H _ _ (HU₁ (mk_mem_prod x_in x'_in)) (HV₁ (mk_mem_prod y_in y'_in)) },
  rcases this with ⟨U₁, U₁_nhd, V₁, V₁_nhd, H⟩,

  have : ∃ x₁, x₁ ∈ U₁ := exists_mem_of_ne_empty
    (forall_sets_neq_empty_iff_neq_bot.2 de.comap_nhds_neq_bot U₁ U₁_nhd),
  rcases this with ⟨x₁, x₁_in⟩,

  have : ∃ y₁, y₁ ∈ V₁ := exists_mem_of_ne_empty
    (forall_sets_neq_empty_iff_neq_bot.2 df.comap_nhds_neq_bot V₁ V₁_nhd),
  rcases this with ⟨y₁, y₁_in⟩,

  rcases (extend_Z_bilin_aux de df hφ W_nhd x₀ y₁) with ⟨U₂, U₂_nhd, HU⟩,
  rcases (extend_Z_bilin_aux df de (continuous.comp continuous_swap hφ) W_nhd y₀ x₁) with ⟨V₂, V₂_nhd, HV⟩,


  existsi [U₁ ∩ U₂, inter_mem_sets U₁_nhd U₂_nhd,
            V₁ ∩ V₂, inter_mem_sets V₁_nhd V₂_nhd],

  rintros x x' ⟨xU₁, xU₂⟩ ⟨x'U₁, x'U₂⟩ y y' ⟨yV₁, yV₂⟩ ⟨y'V₁, y'V₂⟩,
  have key_formula : φ(x', y') - φ(x, y) = φ(x' - x, y₁) + φ(x' - x, y' - y₁) + φ(x₁, y' - y) + φ(x - x₁, y' - y),
  { repeat { rw is_Z_bilin.sub_left φ },
    repeat { rw is_Z_bilin.sub_right φ },
    apply eq_of_sub_eq_zero,
    simp },
  rw key_formula,
  have h₁ := HU x x' xU₂ x'U₂,
  have h₂ := H x x' xU₁ x'U₁ y₁ y' y₁_in y'V₁,
  have h₃ := HV y y' yV₂ y'V₂,
  have h₄ := H x₁ x x₁_in xU₁ y y' yV₁ y'V₁,

  exact W4 h₁ h₂ h₃ h₄,
end

/-- Bourbaki GT III.6.5 Theorem I:
    ℤ-bilinear continuous maps from dense sub-groups into a complete Hausdorff group extend by continuity.
    Note that Bourbaki assumes that E and F are also complete Hausdorff, but this is useless -/
theorem extend_Z_bilin  : continuous (extend (dense_embedding.prod de df) φ) :=
begin
  let dp := dense_embedding.prod de df,
  refine dense_embedding.continuous_extend_of_cauchy (dense_embedding.prod de df) _,
  rintro ⟨x₀, y₀⟩,
  split,
  { apply map_ne_bot,
    apply comap_neq_bot,

    intros U h,
    rcases exists_mem_of_ne_empty (mem_closure_iff_nhds.1 (dp.dense (x₀, y₀)) U h)
      with ⟨x, x_in, ⟨z, z_x⟩⟩,
    existsi z,
    cc },
  { suffices : map (λ (p : (A × B) × (A × B)), φ p.2 - φ p.1)
      (comap (λ (p : (A × B) × A × B), ((e p.1.1, f p.1.2), (e p.2.1, f p.2.2)))
         (filter.prod (nhds (x₀, y₀)) (nhds (x₀, y₀)))) ≤ nhds 0,
    by rwa [uniformity_eq_comap_nhds_zero, prod_map_map_eq, ←map_le_iff_le_comap, filter.map_map,
        prod_comap_comap_eq],

    intros W' W'_nhd,

    have key := extend_Z_bilin_key de df hφ x₀ y₀ W'_nhd,
    rcases key with ⟨U, U_nhd, V, V_nhd, h⟩,
    rw mem_comap_sets at U_nhd,
    rcases U_nhd with ⟨U', U'_nhd, U'_sub⟩,
    rw mem_comap_sets at V_nhd,
    rcases V_nhd with ⟨V', V'_nhd, V'_sub⟩,

    rw [mem_map, mem_comap_sets, nhds_prod_eq],
    existsi set.prod (set.prod U' V') (set.prod U' V'),
    rw mem_prod_same_iff,

    simp only [exists_prop],
    split,
    { have := prod_mem_prod U'_nhd V'_nhd,
      tauto },
    { intros p h',
      simp only [set.mem_preimage_eq, set.prod_mk_mem_set_prod_eq] at h',
      rcases p with ⟨⟨x, y⟩, ⟨x', y'⟩⟩,
      apply h ; tauto } }
end
end dense_embedding