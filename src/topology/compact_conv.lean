import topology.compact_open
import topology.uniform_space.basic
import topology.order

universes u₁ u₂

open_locale filter uniformity topological_space
open uniform_space set

variables {α : Type u₁} {β : Type u₂} [topological_space α] [uniform_space β]
variables (K : set α) (V : set (β × β)) (f : C(α, β))

/-- A subbase for the topology of compact convergence. -/
def uniform_gen : set C(α, β) := {g | ∀ (x ∈ K), (f x, g x) ∈ V }

/-- The topology of compact convergence. I claim this topology is induced by a uniform structure,
defined below. -/
def compact_convergence_topology : topological_space C(α, β) :=
topological_space.generate_from
  {m | ∃ (K : set α) (hK : is_compact K) (V ∈ 𝓤 β) (f : C(α, β)), m = uniform_gen K V f }

lemma uniform_gen_mono (f g : C(α, β)) (h : g ∈ uniform_gen K V f ) (hV : V ∈ 𝓤 β)  :
  uniform_gen K V g ⊆ uniform_gen K V f :=
begin
 simp_rw [uniform_gen] at *,
 simp at *,
 intros a ha x hx,
 have H := h x hx,
 have H2 := ha x hx,
 --is this even true??
 sorry,
end


lemma mem_uniform_gen_self (hV : V ∈ 𝓤 β) : f ∈ uniform_gen K V f := λ x hx, refl_mem_uniformity hV

/-- This should be sufficient to show we actually have a neighbourhood basis. -/
lemma uniform_gen_nhd_basis {g₁ g₂ : C(α, β)}
  (h₁ : g₁ ∈ uniform_gen K V f) (h₂ : g₂ ∈ uniform_gen K V g₁) :
  g₂ ∈ uniform_gen K (V ○ V) f :=
λ x hx, ⟨g₁ x, h₁ x hx, h₂ x hx⟩

/-- Any point of `compact_open.gen K U` is also an interior point wrt the topology of compact
convergence.

The topology of compact convergence is thus at least as fine as the compact-open topology. -/
lemma uniform_gen_subset_compact_open (hK : is_compact K) {U : set β} (hU : is_open U)
  (hf : f ∈ continuous_map.compact_open.gen K U) :
  ∃ (V ∈ 𝓤 β), uniform_gen K V f ⊆ continuous_map.compact_open.gen K U :=
begin
  obtain ⟨V, hV₁, hV₂, hV₃⟩ := lebesgue_number_of_compact_open (hK.image f.continuous) hU hf,
  refine ⟨V, hV₁, _⟩,
  rintros g hg - ⟨x, hx, rfl⟩,
  exact hV₃ (f x) ⟨x, hx, rfl⟩ (hg x hx),
end

/-- The point `f` in `uniform_gen K V f` is also an interior point wrt the compact-open topology.

From this it should follow that the compact-open topology is at least as fine as the topology of
compact convergence. -/
lemma Inter_compact_open_gen_subset_uniform_gen (hK : is_compact K) (hV : V ∈ 𝓤 β) :
  ∃ (ι : Sort (u₁ + 1)) [fintype ι]
  (C : ι → set α) (hC : ∀ i, is_compact (C i))
  (U : ι → set β) (hU : ∀ i, is_open (U i)),
  (f ∈ ⋂ i, continuous_map.compact_open.gen (C i) (U i)) ∧
  (⋂ i, continuous_map.compact_open.gen (C i) (U i)) ⊆ uniform_gen K V f :=
begin
  -- Below needs https://github.com/leanprover-community/mathlib/pull/9981
  obtain ⟨W, hW₁, hW₄, hW₂, hW₃⟩ := comp_open_symm_mem_uniformity_sets hV,
  obtain ⟨Z, hZ₁, hZ₄, hZ₂, hZ₃⟩ := comp_open_symm_mem_uniformity_sets hW₁,
  let U : α → set α := λ x, f⁻¹' (ball (f x) Z),
  have hU : ∀ x, is_open (U x) := λ x, f.continuous.is_open_preimage _ (is_open_ball _ hZ₄),
  have hUK : K ⊆ ⋃ (x : K), U (x : K),
  { intros x hx,
    simp only [exists_prop, mem_Union, Union_coe_set, mem_preimage],
    use (⟨x, hx⟩ : K),
    simp [hx, mem_ball_self (f x) hZ₁], },
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover _ (λ (x : K), hU x.val) hUK,
  let C : t → set α := λ i, K ∩ closure (U ((i : K) : α)),
  have hC : K ⊆ ⋃ i, C i,
  { rw [← K.inter_Union, subset_inter_iff],
    refine ⟨rfl.subset, ht.trans _⟩,
    simp only [set_coe.forall, subtype.coe_mk, Union_subset_iff],
    intros x hx₁ hx₂,
    apply subset_subset_Union (⟨_, hx₂⟩ : t),
    simp [subset_closure], },
  have hfC : ∀ (i : t), f '' C i ⊆ ball (f ((i : K) : α)) W,
  { rintros ⟨⟨x, hx₁⟩, hx₂⟩,
    calc f '' (K ∩ closure (U x))
          ⊆ f '' (closure (U x)) : by { mono, simp only [inter_subset_right], }
      ... ⊆ closure (f '' (U x)) : continuous_on.image_closure f.continuous.continuous_on
      ... ⊆ closure (ball (f x) Z) : by { mono, simp, }
      ... ⊆ ball (f x) W : by { intros y hy,
                                obtain ⟨z, hz₁,hz₂⟩ := uniform_space.mem_closure_iff_ball.mp hy hZ₁,
                                rw mem_ball_symmetry hZ₂ at hz₁,
                                exact ball_mono hZ₃ _ (mem_ball_comp hz₂ hz₁), }, },
  refine ⟨t,
          t.fintype_coe_sort,
          C,
          λ i, hK.inter_right is_closed_closure,
          λ i, ball (f ((i : K) : α)) W,
          λ i, is_open_ball _ hW₄,
          by simp [continuous_map.compact_open.gen, hfC, -image_subset_iff],
          _⟩,
  intros g hg x hx,
  apply hW₃,
  replace hx := mem_Union.mp (hC hx),
  obtain ⟨y, hy⟩ := hx,
  rw mem_comp_rel,
  use f y,
  simp only [mem_Inter, continuous_map.compact_open.gen, mem_set_of_eq, image_subset_iff] at hg,
  refine ⟨_, mem_preimage.mp (hg y hy)⟩,
  simp only [image_subset_iff, mem_preimage] at hfC,
  specialize hfC y hy,
  rw [ball_eq_of_symmetry hW₂] at hfC,
  exact hfC,
end


/-- This should follow from the various lemmas above. -/
lemma compact_open_eq_uniform :
  (compact_convergence_topology : topological_space C(α, β)) = continuous_map.compact_open :=
 begin

 rw [compact_convergence_topology],
 rw [continuous_map.compact_open],
 refine le_antisymm _ _,
 rw le_generate_from_iff_subset_is_open,
 simp,
 intros a x hx y hy ha,
 apply is_open_iff_forall_mem_open.2,
 intros f hf,
  simp_rw ha at hf,
 have := uniform_gen_subset_compact_open x f hx hy hf,
 obtain ⟨ V, hV, HV⟩ :=this,
 use (uniform_gen x V f),
 rw ← ha at HV,
 have:= mem_uniform_gen_self x _ f hV,
 simp [HV, this],
 apply topological_space.generate_open.basic _ _,
 simp,
 use x,
 simp [hx],
 use V,
 simp [hV],
rw le_generate_from_iff_subset_is_open,
simp,
intros a x hx V hV f hf,
apply is_open_iff_forall_mem_open.2,
intros s hs,
have:= Inter_compact_open_gen_subset_uniform_gen _ _ s hx hV,
obtain ⟨ι, hι, C, hC, U, hU, Hs1, Hs2⟩ := this,
use ⋂ (i : ι), continuous_map.compact_open.gen (C i) (U i),
rw hf,
simp [Hs1, Hs2],

sorry,
 end

/-- I believe the topology this induces is `compact_convergence_topology`. -/
instance : uniform_space C(α, β) :=
{ uniformity := ⨅ (K : set α) (hK : is_compact K) (V ∈ 𝓤 β),
                  𝓟 { p : C(α, β) × C(α, β) | ∀ (x : α), (p.1 x, p.2 x) ∈ V },
  refl := sorry, -- trivial
  symm := sorry, -- trivial
  comp := sorry, -- trivial
  is_open_uniformity := sorry, /- Should be easily reduced to `compact_open_eq_uniform` -/ }
