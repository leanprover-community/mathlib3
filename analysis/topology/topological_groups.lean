#exit

lemma half_nhd (U ∈ (nhds (0 : G)).sets) :
  ∃ V ∈ (nhds (0 : G)).sets, ∀ v w ∈ V, v + w ∈ U :=
begin
  have nhdb_in_prod : ((λ a : G × G, a.1+a.2)⁻¹' U) ∈ (nhds ((0, 0) : G × G)).sets,
    by apply tendsto_add' ; simp [H],
  rw nhds_prod_eq at nhdb_in_prod,
  rcases mem_prod_iff.1 nhdb_in_prod with ⟨V₁, H₁, V₂, H₂, H⟩,
  have H12: V₁ ∩ V₂ ∈ (nhds (0 : G)).sets := inter_mem_sets H₁ H₂,
  existsi [(V₁ ∩ V₂), H12],
  intros v w Hv Hw,
  have : (v,w) ∈ set.prod V₁ V₂, by finish,
  simpa using H this
end

lemma quarter_nhd (U ∈ (nhds (0 : G)).sets) :
  ∃ V ∈ (nhds (0 : G)).sets, ∀ {v w s t}, v ∈ V → w ∈ V → s ∈ V → t ∈ V → v + w + s + t ∈ U :=
begin
  rcases half_nhd U H with ⟨W, W_nhd, h⟩,
  rcases half_nhd W W_nhd with ⟨V, V_nhd, h'⟩,
  existsi [V, V_nhd],
  intros v w s t v_in w_in s_in t_in,
  simpa using h _ _ (h' v w v_in w_in) (h' s t s_in t_in)
end

variable (G)
lemma nhds_zero_symm : comap (λ r : G, -r) (nhds (0 : G)) = nhds (0 : G) :=
begin
  let neg := (λ r : G, -r),
  have inv : neg ∘ neg = id, { funext x, simp[neg_eq_iff_neg_eq] },
  have lim : tendsto neg (nhds 0) (nhds 0) :=
    by simpa using continuous.tendsto (topological_add_group.continuous_neg G) 0,
  exact comap_eq_of_inverse inv inv lim lim
end

variable {G}

lemma nhds_translation (x : G) : nhds x = comap (λ y, y-x) (nhds (0 : G)) :=
begin
  have lim₁ : tendsto (λ (y : G), y-x) (nhds x) (nhds 0),
    by simpa using continuous.tendsto (continuous_neg_translation x) x,
  have lim₂ : tendsto (λ (y : G), y+x) (nhds 0) (nhds x),
    by simpa using continuous.tendsto (continuous_translation x) 0,

  have inv₁ : (λ y, y-x) ∘ (λ y, y+x) = id, by {funext x, dsimp[id, (∘)], rw [add_assoc, add_right_neg], simp },
  have inv₂ : (λ y, y+x) ∘ (λ y, y-x) = id, by {funext x, dsimp[id, (∘)], simp, },
  exact eq.symm (comap_eq_of_inverse inv₁ inv₂ lim₁ lim₂)
end
end topological_add_group

section topological_add_comm_group
variables {G : Type u} [add_comm_group G] [topological_space G] [topological_add_group G]

def δ : G × G → G := λ p, p.2 - p.1
def Δ : filter (G × G) := principal id_rel

variable (G)
def topological_add_group.to_uniform_space : uniform_space G :=
{ uniformity          := comap δ (nhds 0),
  refl                :=
  begin
    suffices : map δ Δ ≤ nhds (0 : G), from map_le_iff_le_comap.1 this,
    suffices : map δ Δ ≤ pure (0 : G), from le_trans this (pure_le_nhds 0),
    rw [Δ, map_principal, filter.pure_def, principal_mono],
    show (δ '' id_rel : set G) ⊆ {(0 : G)},
    { simp [δ, id_rel, subset_def, eq_comm] }
  end,
  symm                :=
    have δ_swap : (δ ∘ prod.swap : G × G → G) = (λ p, -p) ∘ δ, by {funext, simp[δ] },
    by simpa [tendsto_comap_iff, δ_swap] using tendsto_comap.comp (tendsto_neg (@tendsto_id G (nhds 0))),
  comp                :=
  begin
    intros D H,
    rw mem_lift'_sets,
    { rcases H with ⟨U, U_nhds, U_sub⟩,
      rcases half_nhd U U_nhds with ⟨V, ⟨V_nhds, V_sum⟩⟩,
      existsi δ⁻¹'V,
      have H : δ⁻¹'V ∈ (comap δ (nhds (0 : G))).sets,
        by existsi [V, V_nhds] ; refl,
      existsi H,
      have comp_rel_sub : comp_rel (δ⁻¹'V) (δ⁻¹'V) ⊆ δ⁻¹' U,
      begin
        intros p p_comp_rel,
        rcases p_comp_rel with ⟨z, ⟨Hz1, Hz2⟩⟩,
        simpa[δ] using V_sum _ _ Hz1 Hz2
      end,
      exact set.subset.trans comp_rel_sub U_sub },
    { exact monotone_comp_rel monotone_id monotone_id }
  end,
  is_open_uniformity  :=
  begin
    intro S,
    let S' := λ x, {p : G × G | p.1 = x → p.2 ∈ S},

    change is_open S ↔ ∀ (x : G), x ∈ S → S' x ∈ (comap δ (nhds (0 : G))).sets,
    have := calc
    is_open S ↔ ∀ (x : G), x ∈ S → S ∈ (nhds x).sets          : is_open_iff_mem_nhds
          ... ↔ ∀ (x : G), x ∈ S → S ∈ (comap (λ y, y-x) (nhds (0:G))).sets : by conv in (_ ∈ _) {rw (nhds_translation x)},
    have : (∀ x ∈ S, S ∈ (comap (λ y, y-x) (nhds (0 : G))).sets) ↔
        (∀ x ∈ S, S' x ∈ (comap δ (nhds (0 : G))).sets),
      { split ; intros H x x_in_S ; specialize H x x_in_S;
        { rcases H with ⟨U, U_nhds, U_prop⟩,
          existsi [U, U_nhds],
          have := calc
          (λ y, y-x)⁻¹' U ⊆ S ↔ (∀ y, y-x ∈ U → y ∈ S) : set.preimage_subset_iff
          ... ↔  (∀ p : G × G, p.2-p.1 ∈ U → p.1 = x → p.2 ∈ S) :
            begin
              split,
              { intros H h h' h'',
                apply H, cc },
              { intros H y h,
                specialize H (x,y),
                finish }
            end
          ... ↔  (∀ p : G × G, δ p ∈ U → p ∈ S' x) : by simp[δ, S' x]
          ... ↔ δ⁻¹'U ⊆ S' x : set.preimage_subset_iff,

          cc } },
    cc
  end,}

variable {G}
lemma uniformity_eq_comap_nhds_zero : uniformity = comap δ (nhds (0 : G)) := rfl

instance topological_add_group_is_uniform : uniform_add_group G :=
⟨begin
  rw [uniform_continuous, uniformity_prod_eq_prod],
  apply tendsto_map',
  apply tendsto_comap_iff.2,

  suffices : tendsto (λ (x : (G × G) × G × G), x.1.2 - x.1.1 - (x.2.2 - x.2.1))
    (filter.prod uniformity uniformity)
    (nhds 0),
  { simpa [(∘), δ] },

  suffices : tendsto (λ (x : (G × G) × G × G), (x.1).2 - (x.1).1 - ((x.2).2 - (x.2).1))
    (comap (λ (p : (G × G) × G × G), ((p.1).2 - (p.1).1, (p.2).2 - (p.2).1))
       (filter.prod (nhds 0) (nhds 0)))
    (nhds 0),
  by simpa [(∘), δ, uniformity_eq_comap_nhds_zero, prod_comap_comap_eq, -sub_eq_add_neg],

  conv { for (nhds _) [3] { rw [show (0:G) = 0 - 0, by simp] }},
  exact tendsto_sub (tendsto.comp tendsto_comap tendsto_fst) (tendsto.comp tendsto_comap tendsto_snd),
end⟩

