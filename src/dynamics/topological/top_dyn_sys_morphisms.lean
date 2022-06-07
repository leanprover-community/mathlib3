import dynamics.topological.compact_metrizable
import dynamics.topological.topological_dynamics_basic


/- Reference : [K] Petr Kurka, Topological and symbolic dynamics, SMF, Cours spécialisés, 2003 -/

/- The notions of orbit and trajectory are permuted, to keep more coherence with the group-theoretic notion of orbit. -/


open topological_dynamics_basic

namespace top_dyn_sys_morphisms


variables {X : Type} (T : X → X) [top_dyn_sys X T]
variables {Y : Type} (S : Y → Y) [top_dyn_sys Y S]



class top_dyn_sys_morphism [top_dyn_sys X T] [top_dyn_sys Y S] (φ : X → Y) :=
  ( continuous : continuous φ )
  ( commutes : φ ∘ T = S ∘ φ )


variables (φ : X → Y) [top_dyn_sys_morphism T S φ]


lemma top_dyn_sys_morph_comm_ite (n : ℕ) :
  φ ∘ (T^[n]) = (S^[n]) ∘ φ :=
begin
  induction n with n h_n,
  { simp },
  { simp,
    calc φ ∘ (T^[n]) ∘ T = (φ ∘ (T^[n])) ∘ T : by trivial
                     ... = (S^[n] ∘ φ) ∘ T   : by rw h_n
                     ... = (S^[n]) ∘ φ ∘ T   : by trivial
                     ... = (S^[n]) ∘ S ∘ φ   : by rw _inst_3.commutes },
end


lemma preimage_of_inv_clos_is_inv_clos (F : set Y) [invariant_closed S F] :
  invariant_closed T (φ⁻¹' F) :=
{ is_closed := continuous_iff_is_closed.1 _inst_3.continuous F _inst_4.is_closed,
  is_invariant :=
  begin
    rw [← set.preimage_comp, _inst_3.commutes, (set.preimage_comp : S ∘ φ ⁻¹' F = φ ⁻¹' (S ⁻¹' F))],
    exact set.preimage_mono _inst_4.is_invariant,
  end }


lemma image_of_inv_clos_is_inv_clos (F : set X) [invariant_closed T F] :
  invariant_closed S (φ '' F) :=
{ is_closed := (_inst_4.is_closed.is_compact.image _inst_3.continuous).is_closed,
  is_invariant :=
  begin
    rw [set.image_subset_iff, ← set.preimage_comp, ← _inst_3.commutes, set.preimage_comp],
    have := @set.preimage_mono X X T _ _ (set.subset_preimage_image φ F),
    exact set.subset.trans _inst_4.is_invariant this,
  end }


instance (F : set Y) [invariant_closed S F] :
  invariant_closed T (φ⁻¹' F) :=
preimage_of_inv_clos_is_inv_clos T S φ F

instance (F : set X) [invariant_closed T F] :
  invariant_closed S (φ '' F) :=
image_of_inv_clos_is_inv_clos T S φ F


lemma image_of_is_minimal_is_is_minimal (F : set X) [invariant_closed T F] :
  minimal_on T F → minimal_on S (φ '' F) :=
begin
  intro F_minimal,
  introsI G G_inv_clos G_sub_F,
  specialize F_minimal (F ∩ φ ⁻¹' G) (set.inter_subset_left F (φ ⁻¹' G)),
  cases F_minimal with preimage_empty preimage_full,
  { left,
    rw [← set.image_eq_empty, set.image_inter_preimage φ F G, set.inter_eq_self_of_subset_right G_sub_F] at preimage_empty,
    exact preimage_empty },
  { right,
    rw [set.inter_eq_left_iff_subset, ← set.image_subset_iff] at preimage_full,
    exact set.subset.antisymm G_sub_F preimage_full },
end


lemma image_of_minimal_by_surjective_is_minimal :
  function.surjective φ → minimal T → minimal S :=
begin
  intros φ_surj XT_minimal,
  introsI F F_inv_clos,
  have minimal_image := image_of_is_minimal_is_is_minimal T S φ set.univ ((minimal_iff_minimal_on_univ T).1 XT_minimal),
  specialize minimal_image F,
  rw set.image_univ_of_surjective φ_surj at minimal_image,
  exact minimal_image (set.subset_univ F),
end


lemma image_of_transitive_by_surjective_is_transitive :
  function.surjective φ → top_transitive T → top_transitive S :=
begin
  intros φ_surj XT_top_trans U V U_open V_open U_nonempty V_nonempty,
  specialize XT_top_trans (φ⁻¹' U) (φ⁻¹' V) (U_open.preimage _inst_3.continuous) (V_open.preimage _inst_3.continuous) ( (function.surjective.nonempty_preimage φ_surj).2 U_nonempty ) ( (function.surjective.nonempty_preimage φ_surj).2 V_nonempty ),
  rcases XT_top_trans with ⟨ n, n_spos, nonempty_inter ⟩,
  use [n, n_spos],
  apply (function.surjective.nonempty_preimage φ_surj).1,
  rw [set.preimage_inter, ← set.preimage_comp, ← top_dyn_sys_morph_comm_ite T S φ n],
  exact nonempty_inter,
end


lemma image_of_mixing_by_surjective_is_mixing :
  function.surjective φ → top_mixing T → top_mixing S :=
begin
  intros φ_surj XT_top_mix U V U_open V_open U_nonempty V_nonempty,
  specialize XT_top_mix (φ⁻¹' U) (φ⁻¹' V) (U_open.preimage _inst_3.continuous) (V_open.preimage _inst_3.continuous) ( (function.surjective.nonempty_preimage φ_surj).2 U_nonempty ) ( (function.surjective.nonempty_preimage φ_surj).2 V_nonempty ),
  cases XT_top_mix with N h_N,
  use N,
  intros n n_ge_N,
  specialize h_N n n_ge_N,
  apply (function.surjective.nonempty_preimage φ_surj).1,
  rw [set.preimage_inter, ← set.preimage_comp, ← top_dyn_sys_morph_comm_ite T S φ n],
  exact h_N,
end


end top_dyn_sys_morphisms
