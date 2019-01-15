/-
Copyright (c) 2018 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton

Construction of the Stone-Čech compactification using ultrafilters.

Parts of the formalization are based on "Ultrafilters and Topology"
by Marius Stekelenburg, particularly section 5.
-/

import analysis.topology.continuity

noncomputable theory

open filter lattice set

universes u v

section ultrafilter
/- The set of ultrafilters on α carries a natural topology which makes
  it the Stone-Čech compactification of α (viewed as a discrete space). -/

/-- Basis for the topology on `ultrafilter α`. -/
def ultrafilter_basis (α : Type u) : set (set (ultrafilter α)) :=
{t | ∃ (s : set α), t = {u | s ∈ u.val.sets}}

variables {α : Type u}

instance : topological_space (ultrafilter α) :=
topological_space.generate_from (ultrafilter_basis α)

lemma ultrafilter_basis_is_basis :
  topological_space.is_topological_basis (ultrafilter_basis α) :=
⟨begin
   rintros _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ u ⟨ua, ub⟩,
   refine ⟨_, ⟨a ∩ b, rfl⟩, u.val.inter_sets ua ub, assume v hv, ⟨_, _⟩⟩;
   apply v.val.sets_of_superset hv; simp
 end,
 eq_univ_of_univ_subset $ subset_sUnion_of_mem $
   ⟨univ, eq.symm (eq_univ_of_forall (λ u, u.val.univ_sets))⟩,
 rfl⟩

/-- The basic open sets for the topology on ultrafilters are open. -/
lemma ultrafilter_is_open_basic (s : set α) :
  is_open {u : ultrafilter α | s ∈ u.val.sets} :=
topological_space.is_open_of_is_topological_basis ultrafilter_basis_is_basis ⟨s, rfl⟩

/-- The basic open sets for the topology on ultrafilters are also closed. -/
lemma ultrafilter_is_closed_basic (s : set α) :
  is_closed {u : ultrafilter α | s ∈ u.val.sets} :=
begin
  change is_open (- _),
  convert ultrafilter_is_open_basic (-s),
  ext u,
  exact (ultrafilter_iff_compl_mem_iff_not_mem.mp u.property s).symm
end

/-- Every ultrafilter `u` on `ultrafilter α` converges to a unique
  point of `ultrafilter α`, namely `mjoin u`. -/
lemma ultrafilter_converges_iff {u : ultrafilter (ultrafilter α)} {x : ultrafilter α} :
  u.val ≤ nhds x ↔ x = mjoin u :=
begin
  rw [eq_comm, ultrafilter.eq_iff_val_le_val],
  change u.val ≤ nhds x ↔ x.val.sets ⊆ {a | {v : ultrafilter α | a ∈ v.val.sets} ∈ u.val.sets},
  simp only [topological_space.nhds_generate_from, lattice.le_infi_iff, ultrafilter_basis,
    le_principal_iff],
  split; intro h,
  { intros a ha, exact h _ ⟨ha, a, rfl⟩ },
  { rintros _ ⟨xi, a, rfl⟩, exact h xi }
end

instance ultrafilter_compact : compact_space (ultrafilter α) :=
⟨compact_iff_ultrafilter_le_nhds.mpr $ assume f uf _,
   ⟨mjoin ⟨f, uf⟩, trivial, ultrafilter_converges_iff.mpr rfl⟩⟩

instance ultrafilter.t2_space : t2_space (ultrafilter α) :=
t2_iff_ultrafilter.mpr $ assume f x y u fx fy,
  have hx : x = mjoin ⟨f, u⟩, from ultrafilter_converges_iff.mp fx,
  have hy : y = mjoin ⟨f, u⟩, from ultrafilter_converges_iff.mp fy,
  hx.trans hy.symm

lemma ultrafilter_comap_pure_nhds (b : ultrafilter α) : comap pure (nhds b) ≤ b.val :=
begin
  rw topological_space.nhds_generate_from,
  simp only [comap_infi, comap_principal],
  intros s hs,
  rw ←le_principal_iff,
  refine lattice.infi_le_of_le {u | s ∈ u.val.sets} _,
  refine lattice.infi_le_of_le ⟨hs, ⟨s, rfl⟩⟩ _,
  rw principal_mono,
  intros a ha,
  exact mem_pure_iff.mp ha
end

section embedding

lemma ultrafilter_pure_injective : function.injective (pure : α → ultrafilter α) :=
begin
  intros x y h,
  have : {x} ∈ (pure x : ultrafilter α).val.sets := singleton_mem_pure_sets,
  rw h at this,
  exact (mem_singleton_iff.mp (mem_pure_sets.mp this)).symm
end

open topological_space

/-- `pure : α → ultrafilter α` defines a dense embedding of `α` in `ultrafilter α`. -/
lemma dense_embedding_pure : @dense_embedding _ _ ⊤ _ (pure : α → ultrafilter α) :=
by letI : topological_space α := ⊤; exact
dense_embedding.mk' pure continuous_top
  (assume x, mem_closure_iff_ultrafilter.mpr
     ⟨x.map ultrafilter.pure, range_mem_map,
      ultrafilter_converges_iff.mpr (bind_pure x).symm⟩)
  ultrafilter_pure_injective
  (assume a s as,
     ⟨{u | s ∈ u.val.sets},
      mem_nhds_sets (ultrafilter_is_open_basic s) (mem_pure_sets.mpr (mem_of_nhds as)),
      assume b hb, mem_pure_sets.mp hb⟩)

end embedding

section extension
/- Goal: Any function `α → γ` to a compact Hausdorff space `γ` has a
  unique extension to a continuous function `ultrafilter α → γ`. We
  already know it must be unique because `α → ultrafilter α` is a
  dense embedding and `γ` is Hausdorff. For existence, we will invoke
  `dense_embedding.continuous_extend`. -/

variables {γ : Type*} [topological_space γ]

/-- The extension of a function `α → γ` to a function `ultrafilter α → γ`.
  When `γ` is a compact Hausdorff space it will be continuous. -/
def ultrafilter.extend (f : α → γ) : ultrafilter α → γ :=
by letI : topological_space α := ⊤; exact dense_embedding_pure.extend f

lemma ultrafilter_extend_extends (f : α → γ) : ultrafilter.extend f ∘ pure = f :=
by letI : topological_space α := ⊤; exact funext dense_embedding_pure.extend_e_eq

variables [t2_space γ] [compact_space γ]

lemma continuous_ultrafilter_extend (f : α → γ) : continuous (ultrafilter.extend f) :=
have ∀ (b : ultrafilter α), ∃ c, tendsto f (comap ultrafilter.pure (nhds b)) (nhds c) := assume b,
  -- b.map f is an ultrafilter on γ, which is compact, so it converges to some c in γ.
  let ⟨c, _, h⟩ := compact_iff_ultrafilter_le_nhds.mp compact_univ (b.map f).val (b.map f).property
    (by rw [le_principal_iff]; exact univ_mem_sets) in
  ⟨c, le_trans (map_mono (ultrafilter_comap_pure_nhds _)) h⟩,
begin
  letI : topological_space α := ⊤,
  letI : normal_space γ := normal_of_compact_t2,
  exact dense_embedding_pure.continuous_extend this
end

/-- The value of `ultrafilter.extend f` on an ultrafilter `b` is the
  unique limit of the ultrafilter `b.map f` in `γ`. -/
lemma ultrafilter_extend_eq_iff {f : α → γ} {b : ultrafilter α} {c : γ} :
  ultrafilter.extend f b = c ↔ b.val.map f ≤ nhds c :=
⟨assume h, begin
   -- Write b as an ultrafilter limit of pure ultrafilters, and use
   -- the facts that ultrafilter.extend is a continuous extension of f.
   let b' : ultrafilter (ultrafilter α) := b.map pure,
   have t : b'.val ≤ nhds b,
     from ultrafilter_converges_iff.mpr (by exact (bind_pure _).symm),
   rw ←h,
   have := (continuous_ultrafilter_extend f).tendsto b,
   refine le_trans _ (le_trans (map_mono t) this),
   change _ ≤ map (ultrafilter.extend f ∘ pure) b.val,
   rw ultrafilter_extend_extends,
   exact le_refl _
 end,
 assume h, by letI : topological_space α := ⊤; exact
   dense_embedding_pure.extend_eq (le_trans (map_mono (ultrafilter_comap_pure_nhds _)) h)⟩

end extension

end ultrafilter


section stone_cech
/- Now, we start with a (not necessarily discrete) topological space α
  and we want to construct its Stone-Čech compactification. We can
  build it as a quotient of `ultrafilter α` by the relation which
  identifies two points if the extension of every continuous function
  α → γ to a compact Hausdorff space sends the two points to the same
  point of γ. -/

variables (α : Type u) [topological_space α]

instance stone_cech_setoid : setoid (ultrafilter α) :=
{ r := λ x y, ∀ (γ : Type u) [topological_space γ], by exactI
    ∀ [t2_space γ] [compact_space γ] (f : α → γ) (hf : continuous f),
    ultrafilter.extend f x = ultrafilter.extend f y,
  iseqv :=
    ⟨assume x γ tγ h₁ h₂ f hf, rfl,
     assume x y xy γ tγ h₁ h₂ f hf, by exactI (xy γ f hf).symm,
     assume x y z xy yz γ tγ h₁ h₂ f hf, by exactI (xy γ f hf).trans (yz γ f hf)⟩ }

/-- The Stone-Čech compactification of a topological space. -/
def stone_cech : Type u := quotient (stone_cech_setoid α)

variables {α}
instance : topological_space (stone_cech α) := by unfold stone_cech; apply_instance

/-- The natural map from α to its Stone-Čech compactification. -/
def stone_cech_unit (x : α) : stone_cech α := ⟦pure x⟧

/-- The image of stone_cech_unit is dense. (But stone_cech_unit need
  not be an embedding, for example if α is not Hausdorff.) -/
lemma stone_cech_unit_dense : closure (range (@stone_cech_unit α _)) = univ :=
begin
  convert quotient_dense_of_dense (eq_univ_iff_forall.mp dense_embedding_pure.closure_range),
  rw [←range_comp], refl
end

section extension

variables {γ : Type u} [topological_space γ] [t2_space γ] [compact_space γ]
variables {f : α → γ} (hf : continuous f)

local attribute [elab_with_expected_type] quotient.lift

/-- The extension of a continuous function from α to a compact
  Hausdorff space γ to the Stone-Čech compactification of α. -/
def stone_cech_extend : stone_cech α → γ :=
quotient.lift (ultrafilter.extend f) (λ x y xy, xy γ f hf)

lemma stone_cech_extend_extends : stone_cech_extend hf ∘ stone_cech_unit = f :=
ultrafilter_extend_extends f

lemma continuous_stone_cech_extend : continuous (stone_cech_extend hf) :=
continuous_quot_lift _ (continuous_ultrafilter_extend f)

end extension

lemma convergent_eqv_pure {u : ultrafilter α} {x : α} (ux : u.val ≤ nhds x) : u ≈ pure x :=
assume γ tγ h₁ h₂ f hf, begin
  resetI,
  transitivity f x, swap, symmetry,
  all_goals { refine ultrafilter_extend_eq_iff.mpr (le_trans (map_mono _) (hf.tendsto _)) },
  { apply pure_le_nhds }, { exact ux }
end

lemma continuous_stone_cech_unit : continuous (stone_cech_unit : α → stone_cech α) :=
continuous_iff_ultrafilter.mpr $ λ x g u gx,
  let g' : ultrafilter α := ⟨g, u⟩ in
  have (g'.map ultrafilter.pure).val ≤ nhds g',
    by rw ultrafilter_converges_iff; exact (bind_pure _).symm,
  have (g'.map stone_cech_unit).val ≤ nhds ⟦g'⟧, from
    (continuous_at_iff_ultrafilter g').mp
      (continuous_quotient_mk.tendsto g') _ (ultrafilter_map u) this,
  by rwa (show ⟦g'⟧ = ⟦pure x⟧, from quotient.sound $ convergent_eqv_pure gx) at this

instance stone_cech.t2_space : t2_space (stone_cech α) :=
begin
  rw t2_iff_ultrafilter,
  rintros g ⟨x⟩ ⟨y⟩ u gx gy,
  apply quotient.sound,
  intros γ tγ h₁ h₂ f hf,
  resetI,
  change stone_cech_extend hf ⟦x⟧ = stone_cech_extend hf ⟦y⟧,
  refine tendsto_nhds_unique u.1 _ _,
  { exact stone_cech_extend hf },
  all_goals
  { refine le_trans (map_mono _) ((continuous_stone_cech_extend hf).tendsto _),
    assumption }
end

instance stone_cech.compact_space : compact_space (stone_cech α) :=
quotient.compact_space

end stone_cech
