/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Direct sum of modules over commutative rings, indexed by a discrete type.
-/

import algebra.direct_sum
import linear_algebra.basic

universes u v w u₁

variables (R : Type u) [ring R]
variables (ι : Type v) [decidable_eq ι] (β : ι → Type w)
variables [Π i, add_comm_group (β i)] [Π i, module R (β i)]
include R

namespace direct_sum

variables {R ι β}

instance : module R (direct_sum ι β) := dfinsupp.to_module

variables R ι β
def lmk : Π s : finset ι, (Π i : (↑s : set ι), β i.1) →ₗ[R] direct_sum ι β :=
dfinsupp.lmk β R

def lof : Π i : ι, β i →ₗ[R] direct_sum ι β :=
dfinsupp.lsingle β R
variables {ι β}

lemma single_eq_lof (i : ι) (b : β i) :
  dfinsupp.single i b = lof R ι β i b := rfl

lemma lof_same (i : ι) (b : β i) : lof R ι β i b i = b :=
by rw [←single_eq_lof, dfinsupp.single_eq_same]

lemma lof_ne (i j : ι) (h : i ≠ j) (b : β i) : lof R ι β i b j = 0 :=
by rw [←single_eq_lof, dfinsupp.single_eq_of_ne h]

theorem mk_smul (s : finset ι) (c : R) (x) : mk β s (c • x) = c • mk β s x :=
(lmk R ι β s).map_smul c x

theorem of_smul (i : ι) (c : R) (x) : of β i (c • x) = c • of β i x :=
(lof R ι β i).map_smul c x

variables {γ : Type u₁} [add_comm_group γ] [module R γ]
variables (φ : Π i, β i →ₗ[R] γ)

variables (ι γ φ)
def to_module : direct_sum ι β →ₗ[R] γ :=
{ to_fun := to_group (λ i, φ i),
  add := to_group_add _,
  smul := λ c x, direct_sum.induction_on x
    (by rw [smul_zero, to_group_zero, smul_zero])
    (λ i x, by rw [← of_smul, to_group_of, to_group_of, (φ i).map_smul c x])
    (λ x y ihx ihy, by rw [smul_add, to_group_add, ihx, ihy, to_group_add, smul_add]) }
variables {ι γ φ}

@[simp] lemma to_module_lof (i) (x : β i) : to_module R ι γ φ (lof R ι β i x) = φ i x :=
to_group_of (λ i, φ i) i x

variables (ψ : direct_sum ι β →ₗ[R] γ)

theorem to_module.unique (f : direct_sum ι β) : ψ f = to_module R ι γ (λ i, ψ.comp $ lof R ι β i) f :=
to_group.unique ψ f

variables {ψ} {ψ' : direct_sum ι β →ₗ[R] γ}

theorem to_module.ext (H : ∀ i, ψ.comp (lof R ι β i) = ψ'.comp (lof R ι β i)) (f : direct_sum ι β) :
  ψ f = ψ' f :=
by rw [to_module.unique R ψ, to_module.unique R ψ', funext H]

def lset_to_set (S T : set ι) (H : S ⊆ T) :
  direct_sum S (β ∘ subtype.val) →ₗ direct_sum T (β ∘ subtype.val) :=
to_module R _ _ $ λ i, lof R T (β ∘ @subtype.val _ T) ⟨i.1, H i.2⟩

protected def lid (M : Type v) [add_comm_group M] [module R M] :
  direct_sum punit (λ _, M) ≃ₗ M :=
{ .. direct_sum.id M,
  .. to_module R punit M (λ i, linear_map.id) }

variables (ι β)
def component (i : ι) : direct_sum ι β →ₗ[R] β i :=
{ to_fun := λ f, f i,
  add := λ _ _, dfinsupp.add_apply,
  smul := λ _ _, dfinsupp.smul_apply }

variables {ι β}
@[simp] lemma lof_apply (i : ι) (b : β i) : ((lof R ι β i) b) i = b :=
by rw [lof, dfinsupp.lsingle_apply, dfinsupp.single_apply, dif_pos rfl]

lemma apply_eq_component (f : direct_sum ι β) (i : ι) :
  f i = component R ι β i f := rfl

@[simp] lemma component.lof_self (i : ι) (b : β i) :
  component R ι β i ((lof R ι β i) b) = b :=
lof_apply R i b

lemma component.of (i j : ι) (b : β j) :
  component R ι β i ((lof R ι β j) b) =
  if h : j = i then eq.rec_on h b else 0 :=
dfinsupp.single_apply

@[extensionality] lemma ext {f g : direct_sum ι β}
  (h : ∀ i, component R ι β i f = component R ι β i g) : f = g :=
dfinsupp.ext h

lemma ext_iff {f g : direct_sum ι β} : f = g ↔
  ∀ i, component R ι β i f = component R ι β i g :=
⟨λ h _, by rw h, ext R⟩

open linear_map lattice submodule

lemma ker_lof (i : ι) : ker (lof R ι β i) = ⊥ :=
ker_eq_bot.2 $ assume f g hfg,
  have lof R ι β i f i = lof R ι β i g i := hfg ▸ rfl,
  by simpa only [lof_same]

lemma supr_range_lof_le_infi_ker_component (I J : set ι) (h : disjoint I J) :
  (⨆i∈I, range (lof R ι β i)) ≤ (⨅i∈J, ker (component R ι β i)) :=
begin
  refine (supr_le $ assume i, supr_le $ assume hi, range_le_iff_comap.2 _),
  simp only [(ker_comp _ _).symm, eq_top_iff, le_def', mem_ker, comap_infi, mem_infi],
  assume b hb j hj,
  have : i ≠ j := assume eq, h ⟨hi, eq.symm ▸ hj⟩,
  rw [comp_apply, component.of, dif_neg this]
end

lemma infi_ker_component_le_supr_range_lof [∀i, decidable_eq (β i)] {I J : set ι} (hu : set.univ ⊆ I ∪ J) :
  (⨅ i∈J, ker (component R ι β i)) ≤ (⨆i∈I, range (lof R ι β i)) :=
submodule.le_def'.2
begin
  assume b hb,
  simp only [mem_infi, mem_ker, apply_eq_component] at hb,
  have : ∀ i, i ∈ b.support → i ∈ I,
  { intros i hib,
    refine set.mem_union.elim (set.mem_of_subset_of_mem hu $ set.mem_univ i) (λ h, h) _,
    rw [dfinsupp.mem_support_iff, ne.def] at hib,
    intro hiJ,
    exfalso,
    exact hib (hb i hiJ) },
  rw ← show b.support.sum (λi, lof R ι β i (b i)) = b,
  { ext i,
    rw [@dfinsupp.finset_sum_apply _ β _ _ _, ←lof_same R i (b i)],
    refine finset.sum_eq_single i (assume j hjI ne, lof_ne _ _ _ ne _) _,
    assume hiI,
    rw [lof_same],
    rwa [dfinsupp.mem_support_iff, ne.def, not_not] at hiI },
  exact sum_mem _ (assume i hiI, mem_supr_of_mem _ i $ mem_supr_of_mem _ (this i hiI) $
    linear_map.mem_range.2 ⟨_, rfl⟩)
end

lemma supr_range_lof [∀i, decidable_eq (β i)] : (⨆i:ι, range (lof R ι β i)) = ⊤ :=
have (set.univ : set ι) ⊆ set.univ ∪ ∅ := set.subset_union_left _ _,
begin
  apply top_unique,
  convert (infi_ker_component_le_supr_range_lof R this),
  exact infi_emptyset.symm,
  exact (funext $ λi, (@supr_pos _ _ _ (λh, (lof R ι β i).range) $ set.mem_univ i).symm),
  apply_instance
end

lemma disjoint_lof_lof (I J : set ι) (h : disjoint I J) :
  disjoint (⨆i∈I, range (lof R ι β i)) (⨆i∈J, range (lof R ι β i)) :=
begin
  refine disjoint_mono
    (supr_range_lof_le_infi_ker_component _ _ _ $ set.disjoint_compl I)
    (supr_range_lof_le_infi_ker_component _ _ _ $ set.disjoint_compl J) _,
  simp only [disjoint, submodule.le_def', mem_infi, mem_inf, mem_ker, mem_bot, apply_eq_component,
    dfinsupp.ext_iff],
  rintros b ⟨hI, hJ⟩ i,
  classical,
  by_cases hiI : i ∈ I,
  { by_cases hiJ : i ∈ J,
    { exact (h ⟨hiI, hiJ⟩).elim },
    { exact hJ i hiJ } },
  { exact hI i hiI }
end

/-- The finite direct sum of `R`-modules `Π₀i:ι, β i` is linearly equivalent to the product of modules
`Πi:ι, β i` when the index type `ι` is finite. -/
def direct_sum_linear_equiv_pi_fintype [fintype ι] : direct_sum ι β ≃ₗ[R] (Πi, β i) :=
dfinsupp.dfinsupp_equiv_pi_fintype.to_linear_equiv
  ⟨λ f g, funext $ λ _, dfinsupp.add_apply, λ c f, funext $ λ _, dfinsupp.smul_apply ⟩

--TODO:move
/-- Dependend finitely supported functions with domain `η` and constant codomain `β` are equivalent
to finitely supported functions `η →₀ β`. -/
def dfinsupp_equiv_finsupp {S} [has_zero S] [decidable_eq S] : (Π₀i:ι, (λ _, S) i) ≃ (ι →₀ S) :=
{ to_fun := λ f, ⟨f.support, f, f.mem_support_iff⟩,
  inv_fun := λ f, ⟦⟨f, f.support.val, λ i,
    by { rw [←finset.mem_def, finsupp.mem_support_iff, or_comm], exact classical.or_not }⟩⟧,
  left_inv := λ f, dfinsupp.ext $ (λ _, rfl),
  right_inv := λ f, finsupp.ext $ (λ _, rfl) }

/-- The direct sum of an `R`-module `S` indexed over a type `ι` is linearly equivalent to the
`R`-module of finitely supported functions from `ι` to `S`. -/
noncomputable def direct_sum_linear_equiv_finsupp {S} [add_comm_group S] [decidable_eq S] [module R S] :
  (direct_sum ι (λ _, S)) ≃ₗ[R] (ι →₀ S) :=
(@dfinsupp_equiv_finsupp R _ ι _ S _ _).to_linear_equiv
  ⟨λ f g, finsupp.ext $ (λ _, dfinsupp.add_apply), λ c f, finsupp.ext $ (λ _, dfinsupp.smul_apply)⟩

end direct_sum
