/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Linear independence and basis sets in a module or vector space.

This file is inspired by Isabelle/HOL's linear algebra, and hence indirectly by HOL Light.

We define the following concepts:

* `linear_independent α β v s`: states that the elements indexed by `s` are linear independent

* `linear_independent.repr s b`: choose the linear combination representing `b` on the linear
  independent vectors `s`. `b` should be in `span α b` (uses classical choice)

* `is_basis α s`: if `s` is a basis, i.e. linear independent and spans the entire space

* `is_basis.repr s b`: like `linear_independent.repr` but as a `linear_map`

* `is_basis.constr s g`: constructs a `linear_map` by extending `g` from the basis `s`

-/
import linear_algebra.basic linear_algebra.finsupp order.zorn
noncomputable theory

open function lattice set submodule
local attribute [instance] classical.prop_decidable
variables {ι : Type*} {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
          {v : ι → β}

section module
variables [ring α] [add_comm_group β] [add_comm_group γ] [add_comm_group δ]
variables [module α β] [module α γ] [module α δ]
variables {a b : α} {x y : β}
include α

section indexed
variables {s t : set ι}

local attribute [instance] finsupp.to_module

variables (α) (β) (v)
/-- Linearly independent set of vectors -/
def linear_independent (s : set ι) : Prop :=
disjoint (finsupp.supported α α s) (finsupp.total ι β α v).ker
variables {α} {β} {v}

theorem linear_independent_iff : linear_independent α β v s ↔
  ∀l ∈ finsupp.supported α α s, finsupp.total ι β α v l = 0 → l = 0 :=
by simp [linear_independent, linear_map.disjoint_ker]

theorem linear_independent_iff_total_on : linear_independent α β v s ↔ (finsupp.total_on ι β α v s).ker = ⊥ :=
by rw [finsupp.total_on, linear_map.ker, linear_map.comap_cod_restrict, map_bot, comap_bot,
  linear_map.ker_comp, linear_independent, disjoint, ← map_comap_subtype, map_le_iff_le_comap,
  comap_bot, ker_subtype, le_bot_iff]

lemma linear_independent_empty : linear_independent α β v (∅ : set ι) :=
by simp [linear_independent]

lemma linear_independent.mono (h : t ⊆ s) : linear_independent α β v s → linear_independent α β v t :=
disjoint_mono_left (finsupp.supported_mono h)

lemma linear_independent.unique (hs : linear_independent α β v s) {l₁ l₂ : ι  →₀ α} :
  l₁ ∈ finsupp.supported α α s → l₂ ∈ finsupp.supported α α s →
  finsupp.total ι β α v l₁ = finsupp.total ι β α v l₂ → l₁ = l₂ :=
linear_map.disjoint_ker'.1 hs _ _

lemma zero_not_mem_of_linear_independent
  {i : ι} (ne : 0 ≠ (1:α)) (hs : linear_independent α β v s) (hi : v i = 0) :
    i ∉ s :=
λ h, ne $ eq.symm begin
  suffices : (finsupp.single i 1 : ι →₀ α) i = 0, {simpa},
  rw disjoint_def.1 hs _ (finsupp.single_mem_supported _ 1 h),
  {refl}, {simp [hi]}
end

lemma linear_independent_union
  (hs : linear_independent α β v s) (ht : linear_independent α β v t)
  (hst : disjoint (span α (v '' s)) (span α (v '' t))) :
  linear_independent α β v (s ∪ t) :=
begin
  rw [linear_independent, disjoint_def, finsupp.supported_union],
  intros l h₁ h₂, rw mem_sup at h₁,
  rcases h₁ with ⟨ls, hls, lt, hlt, rfl⟩,
  rw [finsupp.span_eq_map_total, finsupp.span_eq_map_total] at hst,
  have : finsupp.total ι β α v ls ∈ map (finsupp.total ι β α v) (finsupp.supported α α t),
  { apply (add_mem_iff_left (map _ _) (mem_image_of_mem _ hlt)).1,
    rw [← linear_map.map_add, linear_map.mem_ker.1 h₂],
    apply zero_mem },
  have ls0 := disjoint_def.1 hs _ hls (linear_map.mem_ker.2 $
    disjoint_def.1 hst _ (mem_image_of_mem _ hls) this),
  subst ls0, simp [-linear_map.mem_ker] at this h₂ ⊢,
  exact disjoint_def.1 ht _ hlt h₂
end

lemma linear_independent_of_finite
  (H : ∀ t ⊆ s, finite t → linear_independent α β v t) :
  linear_independent α β v s :=
linear_independent_iff.2 $ λ l hl,
linear_independent_iff.1 (H _ hl (finset.finite_to_set _)) l (subset.refl _)

lemma linear_independent_Union_of_directed {η : Type*}
  {s : η → set ι} (hs : directed (⊆) s)
  (h : ∀ i, linear_independent α β v (s i)) : linear_independent α β v (⋃ i, s i) :=
begin
  by_cases hη : nonempty η,
  { refine linear_independent_of_finite (λ t ht ft, _),
    rcases finite_subset_Union ft ht with ⟨I, fi, hI⟩,
    rcases hs.finset_le hη fi.to_finset with ⟨i, hi⟩,
    exact (h i).mono (subset.trans hI $ bUnion_subset $
      λ j hj, hi j (finite.mem_to_finset.2 hj)) },
  { refine linear_independent_empty.mono _,
    rintro _ ⟨_, ⟨i, _⟩, _⟩, exact hη ⟨i⟩ }
end

lemma linear_independent_sUnion_of_directed {s : set (set ι)}
  (hs : directed_on (⊆) s)
  (h : ∀ a ∈ s, linear_independent α β v a) : linear_independent α β v (⋃₀ s) :=
by rw sUnion_eq_Union; exact
linear_independent_Union_of_directed
  ((directed_on_iff_directed _).1 hs) (by simpa using h)

lemma linear_independent_bUnion_of_directed {η} {s : set η} {t : η → set ι}
  (hs : directed_on (t ⁻¹'o (⊆)) s) (h : ∀a∈s, linear_independent α β v (t a)) :
  linear_independent α β v (⋃a∈s, t a) :=
by rw bUnion_eq_Union; exact
linear_independent_Union_of_directed
  ((directed_comp _ _ _).2 $ (directed_on_iff_directed _).1 hs)
  (by simpa using h)

lemma linear_independent_Union_finite {η : Type*} {f : η → set ι}
  (hl : ∀i, linear_independent α β v (f i))
  (hd : ∀i, ∀t:set η, finite t → i ∉ t →
  disjoint (span α (v '' (f i))) (⨆i∈t, span α (v '' (f i)))) :
  linear_independent α β v (⋃i, f i) :=
begin
  classical,
  rw [Union_eq_Union_finset f],
  refine linear_independent_Union_of_directed (directed_of_sup _) _,
  exact (assume t₁ t₂ ht, Union_subset_Union $ assume i, Union_subset_Union_const $ assume h, ht h),
  assume t, rw [set.Union, ← finset.sup_eq_supr],
  refine t.induction_on _ _,
  { exact linear_independent_empty },
  { rintros ⟨i⟩ s his ih,
    rw [finset.sup_insert],
    refine linear_independent_union (hl _) ih _,
    rw [finset.sup_eq_supr],
    refine disjoint_mono (le_refl _) _ (hd i _ _ his),
    { simp only [(span_Union _).symm, set.image_Union],
      refine span_mono (@supr_le_supr2 (set β) _ _ _ _ _ _),
      rintros ⟨i⟩, exact ⟨i, le_refl _⟩ },
    { change finite (plift.up ⁻¹' s.to_set),
      exact finite_preimage (assume i j, plift.up.inj) s.finite_to_set } }
end

section repr
variables (hs : linear_independent α β v s)

lemma linear_independent.injective (zero_ne_one : (0 : α) ≠ 1)
  (hs : linear_independent α β v s) (i j : ι) (hi : i ∈ s) (hi : j ∈ s)
  (hij: v i = v j) : i = j :=
begin
  let l : ι →₀ α := finsupp.single i (1 : α) - finsupp.single j 1,
  have h_supp : l ∈ finsupp.supported α α s,
  { dsimp only [l],
    rw [finsupp.mem_supported],
    intros k hk,
    apply or.elim (finset.mem_union.1 (finsupp.support_add (finset.mem_coe.1 hk))),
    { intro hk',
      rwa finset.mem_singleton.1 (finsupp.support_single_subset hk') },
    { intro hk',
      rw finsupp.support_neg at hk',
      rwa finset.mem_singleton.1 (finsupp.support_single_subset hk') } },
  have h_total : finsupp.total ι β α v l = 0,
  { rw finsupp.total_apply,
    rw finsupp.sum_sub_index,
    { simp [finsupp.sum_single_index, hij] },
    { intros, apply sub_smul } },
  have h_single_eq : finsupp.single i (1 : α) = finsupp.single j 1,
  { rw linear_independent_iff at hs,
    simp [eq_add_of_sub_eq' (hs l h_supp h_total)] },
  show i = j,
  { apply or.elim ((finsupp.single_eq_single_iff _ _ _ _).1 h_single_eq),
    simp,
    exact λ h, false.elim (zero_ne_one.symm h.1) }
end

def linear_independent.total_equiv : finsupp.supported α α s ≃ₗ span α (v '' s) :=
linear_equiv.of_bijective (finsupp.total_on ι β α v s)
  (linear_independent_iff_total_on.1 hs) (finsupp.total_on_range _ _)

-- TODO(Alex): How to add a local instance?
private def aux_linear_equiv_to_linear_map:
  has_coe (span α (v '' s) ≃ₗ[α] finsupp.supported α α s)
          (span α (v '' s) →ₗ[α] finsupp.supported α α s) :=
⟨linear_equiv.to_linear_map⟩
local attribute [instance] aux_linear_equiv_to_linear_map

def linear_independent.repr : span α (v '' s) →ₗ[α] ι →₀ α :=
(submodule.subtype _).comp (hs.total_equiv.symm : span α (v '' s) →ₗ[α] finsupp.supported α α s )

lemma linear_independent.total_repr (x) : finsupp.total ι β α v (hs.repr x) = x :=
subtype.ext.1 $ hs.total_equiv.right_inv x

lemma linear_independent.total_comp_repr : (finsupp.total ι β α v).comp hs.repr = submodule.subtype _ :=
linear_map.ext $ hs.total_repr

lemma linear_independent.repr_ker : hs.repr.ker = ⊥ :=
by rw [linear_independent.repr, linear_map.ker_comp, ker_subtype, comap_bot, linear_equiv.ker]

lemma linear_independent.repr_range : hs.repr.range = finsupp.supported α α s :=
by rw [linear_independent.repr, linear_map.range_comp, linear_equiv.range, map_top, range_subtype]

private def aux_linear_map_to_fun : has_coe_to_fun (finsupp.supported α α s →ₗ[α] span α (v '' s)) :=
  ⟨_, linear_map.to_fun⟩
local attribute [instance] aux_linear_map_to_fun

lemma linear_independent.repr_eq
  {l : ι →₀ α} (h : l ∈ finsupp.supported α α s) {x} (eq : finsupp.total ι β α v l = ↑x) :
  hs.repr x = l :=
by rw ← (subtype.eq' eq : (finsupp.total_on ι β α v s : finsupp.supported α α s →ₗ span α (v '' s)) ⟨l, h⟩ = x);
   exact subtype.ext.1 (hs.total_equiv.left_inv ⟨l, h⟩)

lemma linear_independent.repr_eq_single (i) (x) (hi : i ∈ s) (hx : ↑x = v i) : hs.repr x = finsupp.single i 1 :=
begin
  apply hs.repr_eq (finsupp.single_mem_supported _ _ hi),
  simp [finsupp.total_single, hx]
end

def aux_linear_map_to_fun : has_coe_to_fun (span α (v '' s) →ₗ[α] finsupp.supported α α s) :=
  ⟨_, linear_map.to_fun⟩
local attribute [instance] aux_linear_map_to_fun

lemma linear_independent.repr_supported (x) : hs.repr x ∈ finsupp.supported α α s :=
((hs.total_equiv.symm : span α (v '' s) →ₗ[α] finsupp.supported α α s) x).2

lemma linear_independent.repr_eq_repr_of_subset (h : t ⊆ s) (x y) (e : (↑x:β) = ↑y) :
  (hs.mono h).repr x = hs.repr y :=
eq.symm $ hs.repr_eq (finsupp.supported_mono h ((hs.mono h).repr_supported _) : _ ∈ ↑(finsupp.supported α α s))
  (by rw [← e, (hs.mono h).total_repr]).

lemma linear_independent_iff_not_smul_mem_span :
  linear_independent α β v s ↔ (∀ (i ∈ s) (a : α), a • (v i) ∈ span α (v '' (s \ {i})) → a = 0) :=
⟨λ hs i hi a ha, begin
  rw [finsupp.span_eq_map_total, mem_map] at ha,
  rcases ha with ⟨l, hl, e⟩,
  have := (finsupp.supported α α s).sub_mem
    (finsupp.supported_mono (diff_subset _ _) hl : _ ∈ ↑(finsupp.supported α α s))
    (finsupp.single_mem_supported α a hi),
  rw [sub_eq_zero.1 (linear_independent_iff.1 hs _ this $ by simp [e])] at hl,
  by_contra hn,
  exact (not_mem_of_mem_diff (hl $ by simp [hn])) (mem_singleton _)
end, λ H, linear_independent_iff.2 $ λ l ls l0, begin
  ext x, simp,
  by_contra hn,
  have xs : x ∈ s := ls (finsupp.mem_support_iff.2 hn),
  refine hn (H _ xs _ _),
  refine (finsupp.mem_span_iff_total _).2 ⟨finsupp.single x (l x) - l, _, _⟩,
  { have : finsupp.single x (l x) - l ∈ finsupp.supported α α s :=
      sub_mem _ (finsupp.single_mem_supported _ _ xs) ls,
    refine λ y hy, ⟨this hy, λ e, _⟩,
    simp at e hy, apply hy, simp [e] },
  { simp [l0] }
end⟩

end repr

lemma eq_of_linear_independent_of_span (nz : (1 : α) ≠ 0)
  (hs : linear_independent α β v s) (h : t ⊆ s) (hst : v '' s ⊆ span α (v '' t)) : s = t :=
begin
  refine subset.antisymm (λ i hi, _) h,
  have : (hs.mono h).repr ⟨v i, hst (set.mem_image_of_mem _ hi)⟩ = finsupp.single i 1 :=
    (hs.repr_eq_repr_of_subset h ⟨v i, hst (set.mem_image_of_mem _ hi)⟩
      ⟨v i, subset_span (set.mem_image_of_mem _ hi)⟩ rfl).trans
      (hs.repr_eq_single i ⟨v i, _⟩ hi (by simp)),
  have ss := (hs.mono h).repr_supported _,
  rw this at ss, exact ss (by simp [nz]),
end

end indexed

section
variables {s t : set β} {f : β →ₗ[α] γ}
variables (hf_inj : ∀ x y ∈ t, f x = f y → x = y)
variables (ht : linear_independent α γ id (f '' t))
include hf_inj ht
open linear_map

local attribute [instance] finsupp.to_module

lemma linear_independent.supported_disjoint_ker :
  disjoint (finsupp.supported α α t) (ker (f.comp (finsupp.total _ _ _ id))) :=
begin
  refine le_trans (le_inf inf_le_left _) (finsupp.map_disjoint_ker _ _ f hf_inj),
  haveI : inhabited β := ⟨0⟩,
  rw [linear_independent, disjoint_iff, ← finsupp.map_supported α α f t] at ht,
  rw [← @finsupp.map_total _ _ α _ _ _ _ _ _ _ _ _ _ _ id id f f (by simp), le_ker_iff_map],
  refine eq_bot_mono (le_inf (map_mono inf_le_left) _) ht,
  rw [map_le_iff_le_comap, ← ker_comp], exact inf_le_right,
end

lemma linear_independent.of_image : linear_independent α β id t :=
disjoint_mono_right (ker_le_ker_comp _ _) (ht.supported_disjoint_ker hf_inj)

lemma linear_independent.disjoint_ker : disjoint (span α t) f.ker :=
by rw [← set.image_id t, finsupp.span_eq_map_total, disjoint_iff, map_inf_eq_map_inf_comap,
  ← ker_comp, disjoint_iff.1 (ht.supported_disjoint_ker hf_inj), map_bot]

end

lemma linear_independent.inj_span_iff_inj
  {t : set β} {f : β →ₗ[α] γ}
  (ht : linear_independent α γ id (f '' t)) :
  disjoint (span α t) f.ker ↔ (∀ x y ∈ t, f x = f y → x = y) :=
⟨linear_map.inj_of_disjoint_ker subset_span, λ h, ht.disjoint_ker h⟩

open linear_map
local attribute [instance] finsupp.to_module

lemma linear_independent.image {s : set β} {f : β →ₗ γ} (hs : linear_independent α β id s)
  (hf_inj : disjoint (span α s) f.ker) : linear_independent α γ id (f '' s) :=
begin
  rw [disjoint, ← set.image_id s, finsupp.span_eq_map_total, map_inf_eq_map_inf_comap,
    map_le_iff_le_comap, comap_bot] at hf_inj,
  haveI : inhabited β := ⟨0⟩,
  rw [linear_independent, disjoint, ← finsupp.map_supported _ _ f, map_inf_eq_map_inf_comap,
      map_le_iff_le_comap, ← ker_comp, @finsupp.map_total _ _ α _ _ _ _ _ _ _ _ _ _ _ id id, ker_comp],
  { exact le_trans (le_inf inf_le_left hf_inj) (le_trans hs bot_le) },
  { simp }
end

lemma linear_map.linear_independent_image_iff {s : set β} {f : β →ₗ γ}
  (hf_inj : disjoint (span α s) f.ker) :
  linear_independent α γ id (f '' s) ↔ linear_independent α β id s :=
⟨λ hs, hs.of_image (linear_map.inj_of_disjoint_ker subset_span hf_inj),
 λ hs, hs.image hf_inj⟩

lemma linear_independent_inl_union_inr {s : set β} {t : set γ}
  (hs : linear_independent α β id s) (ht : linear_independent α γ id t) :
  linear_independent α (β × γ) id (inl α β γ '' s ∪ inr α β γ '' t) :=
linear_independent_union (hs.image $ by simp) (ht.image $ by simp) $
by rw [set.image_id, span_image, set.image_id, span_image];
    simp [disjoint_iff, prod_inf_prod]

variables (α)
/-- A set of vectors is a basis if it is linearly independent and all vectors are in the span α -/
def is_basis (s : set β) := linear_independent α β id s ∧ span α s = ⊤
variables {α}

section is_basis
variables {s t : set β} (hs : is_basis α s)

lemma is_basis.mem_span (hs : is_basis α s) : ∀ x, x ∈ span α s := eq_top_iff'.1 hs.2

def is_basis.repr : β →ₗ β →₀ α :=
(hs.1.repr).comp (linear_map.id.cod_restrict _ (by rw [set.image_id]; exact hs.mem_span))

lemma is_basis.total_repr (x) : finsupp.total β β α id (hs.repr x) = x :=
hs.1.total_repr ⟨x, _⟩

lemma is_basis.total_comp_repr : (finsupp.total β β α id).comp hs.repr = linear_map.id :=
linear_map.ext hs.total_repr

lemma is_basis.repr_ker : hs.repr.ker = ⊥ :=
linear_map.ker_eq_bot.2 $ injective_of_left_inverse hs.total_repr

lemma is_basis.repr_range : hs.repr.range = finsupp.supported α α s :=
by  rw [is_basis.repr, linear_map.range, submodule.map_comp,
  linear_map.map_cod_restrict, submodule.map_id, comap_top, map_top, hs.1.repr_range]

lemma is_basis.repr_supported (x) : hs.repr x ∈ finsupp.supported α α s :=
hs.1.repr_supported ⟨x, _⟩

lemma is_basis.repr_total (x) (hx : x ∈ finsupp.supported α α s) :
  hs.repr (finsupp.total β β α id x) = x :=
begin
  rw [← hs.repr_range, linear_map.mem_range] at hx,
  cases hx with v hv,
  rw [← hv, hs.total_repr],
end

lemma is_basis.repr_eq_single {x} : x ∈ s → hs.repr x = finsupp.single x 1 :=
λ hxs, hs.1.repr_eq_single x ⟨x, _⟩ hxs (by simp)

/-- Construct a linear map given the value at the basis. -/
def is_basis.constr (f : β → γ) : β →ₗ[α] γ :=
(finsupp.total γ γ α  id).comp $ (finsupp.lmap_domain α α f).comp hs.repr

theorem is_basis.constr_apply (f : β → γ) (x : β) :
  (hs.constr f : β → γ) x = (hs.repr x).sum (λb a, a • f b) :=
by dsimp [is_basis.constr];
   rw [finsupp.total_apply, finsupp.sum_map_domain_index]; simp [add_smul]

lemma is_basis.ext {f g : β →ₗ[α] γ} (hs : is_basis α s) (h : ∀x∈s, f x = g x) : f = g :=
linear_map.ext $ λ x, linear_eq_on s h (hs.mem_span x)

lemma constr_congr {f g : β → γ} {x : β} (hs : is_basis α s) (h : ∀x∈s, f x = g x) :
  hs.constr f = hs.constr g :=
by ext y; simp [is_basis.constr_apply]; exact
finset.sum_congr rfl (λ x hx, by simp [h x (hs.repr_supported _ hx)])

lemma constr_basis {f : β → γ} {b : β} (hs : is_basis α s) (hb : b ∈ s) :
  (hs.constr f : β → γ) b = f b :=
by simp [is_basis.constr_apply, hs.repr_eq_single hb, finsupp.sum_single_index]

lemma constr_eq {g : β → γ} {f : β →ₗ[α] γ} (hs : is_basis α s)
  (h : ∀x∈s, g x = f x) : hs.constr g = f :=
hs.ext $ λ x hx, (constr_basis hs hx).trans (h _ hx)

lemma constr_self (f : β →ₗ[α] γ) : hs.constr f = f :=
constr_eq hs $ λ x hx, rfl

lemma constr_zero (hs : is_basis α s) : hs.constr (λb, (0 : γ)) = 0 :=
constr_eq hs $ λ x hx, rfl

lemma constr_add {g f : β → γ} (hs : is_basis α s) :
  hs.constr (λb, f b + g b) = hs.constr f + hs.constr g :=
constr_eq hs $ by simp [constr_basis hs] {contextual := tt}

lemma constr_neg {f : β → γ} (hs : is_basis α s) : hs.constr (λb, - f b) = - hs.constr f :=
constr_eq hs $ by simp [constr_basis hs] {contextual := tt}

lemma constr_sub {g f : β → γ} (hs : is_basis α s) :
  hs.constr (λb, f b - g b) = hs.constr f - hs.constr g :=
by simp [constr_add, constr_neg]

-- this only works on functions if `α` is a commutative ring
lemma constr_smul {α β γ} [comm_ring α]
  [add_comm_group β] [add_comm_group γ] [module α β] [module α γ]
  {f : β → γ} {a : α} {s : set β} (hs : is_basis α s) {b : β} :
  hs.constr (λb, a • f b) = a • hs.constr f :=
constr_eq hs $ by simp [constr_basis hs] {contextual := tt}

lemma constr_range (hs : is_basis α s) {f : β → γ} :
  (hs.constr f).range = span α (f '' s) :=
by haveI : inhabited β := ⟨0⟩;
  rw [is_basis.constr, linear_map.range_comp, linear_map.range_comp, is_basis.repr_range,
    finsupp.map_supported, ←set.image_id (f '' s), finsupp.span_eq_map_total, set.image_id (f '' s)]

def module_equiv_finsupp (hs : is_basis α s) : β ≃ₗ finsupp.supported α α s :=
(hs.1.total_equiv.trans (linear_equiv.of_top _ (by rw set.image_id; exact hs.2))).symm

def equiv_of_is_basis {s : set β} {t : set γ} {f : β → γ} {g : γ → β}
  (hs : is_basis α s) (ht : is_basis α t) (hf : ∀b∈s, f b ∈ t) (hg : ∀c∈t, g c ∈ s)
  (hgf : ∀b∈s, g (f b) = b) (hfg : ∀c∈t, f (g c) = c) :
  β ≃ₗ γ :=
{ inv_fun := ht.constr g,
  left_inv :=
    have (ht.constr g).comp (hs.constr f) = linear_map.id,
    from hs.ext $ by simp [constr_basis, hs, ht, hf, hgf, (∘)] {contextual := tt},
    λ x, congr_arg (λ h:β →ₗ[α] β, h x) this,
  right_inv :=
    have (hs.constr f).comp (ht.constr g) = linear_map.id,
    from ht.ext $ by simp [constr_basis, hs, ht, hg, hfg, (∘)] {contextual := tt},
    λ y, congr_arg (λ h:γ →ₗ[α] γ, h y) this,
  ..hs.constr f }

lemma is_basis_inl_union_inr {s : set β} {t : set γ}
  (hs : is_basis α s) (ht : is_basis α t) : is_basis α (inl α β γ '' s ∪ inr α β γ '' t) :=
⟨linear_independent_inl_union_inr hs.1 ht.1,
  by rw [span_union, span_image, span_image]; simp [hs.2, ht.2]⟩

end is_basis

lemma is_basis_singleton_one (α : Type*) [ring α] : is_basis α ({1} : set α) :=
⟨ by simp [linear_independent_iff_not_smul_mem_span],
  top_unique $ assume a h, by simp [submodule.mem_span_singleton]⟩

lemma linear_equiv.is_basis {s : set β} (hs : is_basis α s)
  (f : β ≃ₗ[α] γ) : is_basis α (f '' s) :=
show is_basis α ((f : β →ₗ[α] γ) '' s), from
⟨hs.1.image $ by simp, by rw [span_image, hs.2, map_top, f.range]⟩

lemma is_basis_injective {s : set γ} {f : β →ₗ[α] γ}
  (hs : linear_independent α γ id s) (h : function.injective f) (hfs : span α s = f.range) :
  is_basis α (f ⁻¹' s) :=
have s_eq : f '' (f ⁻¹' s) = s :=
  image_preimage_eq_of_subset $ by rw [← linear_map.range_coe, ← hfs]; exact subset_span,
have linear_independent α γ id (f '' (f ⁻¹' s)), from hs.mono (image_preimage_subset _ _),
begin
  split,
  exact (this.of_image $ assume a ha b hb eq, h eq),
  refine (top_unique $ (linear_map.map_le_map_iff $ linear_map.ker_eq_bot.2 h).1 _),
  rw [← span_image f,s_eq, hfs, linear_map.range],
  exact le_refl _
end

lemma is_basis_span {s : set β} (hs : linear_independent α β id s) : is_basis α ((span α s).subtype ⁻¹' s) :=
is_basis_injective hs subtype.val_injective (range_subtype _).symm

lemma is_basis_empty (h : ∀x:β, x = 0) : is_basis α (∅ : set β) :=
⟨linear_independent_empty, eq_top_iff'.2 $ assume x, (h x).symm ▸ submodule.zero_mem _⟩

lemma is_basis_empty_bot : is_basis α ({x | false } : set (⊥ : submodule α β)) :=
is_basis_empty $ assume ⟨x, hx⟩,
  by change x ∈ (⊥ : submodule α β) at hx; simpa [subtype.ext] using hx

end module

section vector_space
variables [discrete_field α] [add_comm_group β] [add_comm_group γ]
  [vector_space α β] [vector_space α γ] {s t : set β} {x y z : β}
include α
open submodule

/- TODO: some of the following proofs can generalized with a zero_ne_one predicate type class
   (instead of a data containing type class) -/

set_option class.instance_max_depth 36

lemma mem_span_insert_exchange : x ∈ span α (insert y s) → x ∉ span α s → y ∈ span α (insert x s) :=
begin
  simp [mem_span_insert],
  rintro a z hz rfl h,
  refine ⟨a⁻¹, -a⁻¹ • z, smul_mem _ _ hz, _⟩,
  have a0 : a ≠ 0, {rintro rfl, simp * at *},
  simp [a0, smul_add, smul_smul]
end

set_option class.instance_max_depth 32

lemma linear_independent_iff_not_mem_span : linear_independent α β id s ↔ (∀x∈s, x ∉ span α (s \ {x})) :=
linear_independent_iff_not_smul_mem_span.trans
⟨λ H x xs hx, one_ne_zero (H x xs 1 $ by rw set.image_id; simpa),
 λ H x xs a hx, classical.by_contradiction $ λ a0,
   H x xs (by rw [← set.image_id (s \ {x})]; exact (smul_mem_iff _ a0).1 hx)⟩

lemma linear_independent_singleton {x : β} (hx : x ≠ 0) : linear_independent α β id ({x} : set β) :=
linear_independent_iff_not_mem_span.mpr $ by simp [hx] {contextual := tt}

lemma disjoint_span_singleton {p : submodule α β} {x : β} (x0 : x ≠ 0) :
  disjoint p (span α {x}) ↔ x ∉ p :=
⟨λ H xp, x0 (disjoint_def.1 H _ xp (singleton_subset_iff.1 subset_span:_)),
begin
  simp [disjoint_def, mem_span_singleton],
  rintro xp y yp a rfl,
  by_cases a0 : a = 0, {simp [a0]},
  exact xp.elim ((smul_mem_iff p a0).1 yp),
end⟩

lemma linear_independent.insert (hs : linear_independent α β id s) (hx : x ∉ span α s) :
  linear_independent α β id (insert x s) :=
begin
  rw ← union_singleton,
  have x0 : x ≠ 0 := mt (by rintro rfl; apply zero_mem _) hx,
  apply linear_independent_union hs (linear_independent_singleton x0),
  rw [set.image_id, set.image_id, disjoint_span_singleton x0],
  exact hx
end

lemma exists_linear_independent (hs : linear_independent α β id s) (hst : s ⊆ t) :
  ∃b⊆t, s ⊆ b ∧ t ⊆ span α b ∧ linear_independent α β id b :=
begin
  rcases zorn.zorn_subset₀ {b | b ⊆ t ∧ linear_independent α β id b} _ _
    ⟨hst, hs⟩ with ⟨b, ⟨bt, bi⟩, sb, h⟩,
  { refine ⟨b, bt, sb, λ x xt, _, bi⟩,
    by_contra hn,
    apply hn,
    rw ← h _ ⟨insert_subset.2 ⟨xt, bt⟩, bi.insert hn⟩ (subset_insert _ _),
    exact subset_span (mem_insert _ _) },
  { refine λ c hc cc c0, ⟨⋃₀ c, ⟨_, _⟩, λ x, _⟩,
    { exact sUnion_subset (λ x xc, (hc xc).1) },
    { exact linear_independent_sUnion_of_directed cc.directed_on (λ x xc, (hc xc).2) },
    { exact subset_sUnion_of_mem } }
end

lemma exists_subset_is_basis (hs : linear_independent α β id s) : ∃b, s ⊆ b ∧ is_basis α b :=
let ⟨b, hb₀, hx, hb₂, hb₃⟩ := exists_linear_independent hs (@subset_univ _ _) in
⟨b, hx, hb₃, eq_top_iff.2 hb₂⟩

variables (α β)
lemma exists_is_basis : ∃b : set β, is_basis α b :=
let ⟨b, _, hb⟩ := exists_subset_is_basis linear_independent_empty in ⟨b, hb⟩
variables {α β}

-- TODO(Mario): rewrite?
lemma exists_of_linear_independent_of_finite_span {t : finset β}
  (hs : linear_independent α β id s) (hst : s ⊆ (span α ↑t : submodule α β)) :
  ∃t':finset β, ↑t' ⊆ s ∪ ↑t ∧ s ⊆ ↑t' ∧ t'.card = t.card :=
have ∀t, ∀(s' : finset β), ↑s' ⊆ s → s ∩ ↑t = ∅ → s ⊆ (span α ↑(s' ∪ t) : submodule α β) →
  ∃t':finset β, ↑t' ⊆ s ∪ ↑t ∧ s ⊆ ↑t' ∧ t'.card = (s' ∪ t).card :=
assume t, finset.induction_on t
  (assume s' hs' _ hss',
    have s = ↑s',
      from eq_of_linear_independent_of_span (@one_ne_zero α _) hs hs' $
          by rw [set.image_id, set.image_id]; simpa using hss',
    ⟨s', by simp [this]⟩)
  (assume b₁ t hb₁t ih s' hs' hst hss',
    have hb₁s : b₁ ∉ s,
      from assume h,
      have b₁ ∈ s ∩ ↑(insert b₁ t), from ⟨h, finset.mem_insert_self _ _⟩,
      by rwa [hst] at this,
    have hb₁s' : b₁ ∉ s', from assume h, hb₁s $ hs' h,
    have hst : s ∩ ↑t = ∅,
      from eq_empty_of_subset_empty $ subset.trans
        (by simp [inter_subset_inter, subset.refl]) (le_of_eq hst),
    classical.by_cases
      (assume : s ⊆ (span α ↑(s' ∪ t) : submodule α β),
        let ⟨u, hust, hsu, eq⟩ := ih _ hs' hst this in
        have hb₁u : b₁ ∉ u, from assume h, (hust h).elim hb₁s hb₁t,
        ⟨insert b₁ u, by simp [insert_subset_insert hust],
          subset.trans hsu (by simp), by simp [eq, hb₁t, hb₁s', hb₁u]⟩)
      (assume : ¬ s ⊆ (span α ↑(s' ∪ t) : submodule α β),
        let ⟨b₂, hb₂s, hb₂t⟩ := not_subset.mp this in
        have hb₂t' : b₂ ∉ s' ∪ t, from assume h, hb₂t $ subset_span h,
        have s ⊆ (span α ↑(insert b₂ s' ∪ t) : submodule α β), from
          assume b₃ hb₃,
          have ↑(s' ∪ insert b₁ t) ⊆ insert b₁ (insert b₂ ↑(s' ∪ t) : set β),
            by simp [insert_eq, -singleton_union, -union_singleton, union_subset_union, subset.refl, subset_union_right],
          have hb₃ : b₃ ∈ span α (insert b₁ (insert b₂ ↑(s' ∪ t) : set β)),
            from span_mono this (hss' hb₃),
          have s ⊆ (span α (insert b₁ ↑(s' ∪ t)) : submodule α β),
            by simpa [insert_eq, -singleton_union, -union_singleton] using hss',
          have hb₁ : b₁ ∈ span α (insert b₂ ↑(s' ∪ t)),
            from mem_span_insert_exchange (this hb₂s) hb₂t,
          by rw [span_insert_eq_span hb₁] at hb₃; simpa using hb₃,
        let ⟨u, hust, hsu, eq⟩ := ih _ (by simp [insert_subset, hb₂s, hs']) hst this in
        ⟨u, subset.trans hust $ union_subset_union (subset.refl _) (by simp [subset_insert]),
          hsu, by rw [finset.union_comm] at hb₂t'; simp [eq, hb₂t', hb₁t, hb₁s']⟩)),
have eq : t.filter (λx, x ∈ s) ∪ t.filter (λx, x ∉ s) = t,
  from finset.ext.mpr $ assume x, by by_cases x ∈ s; simp *,
let ⟨u, h₁, h₂, h⟩ := this (t.filter (λx, x ∉ s)) (t.filter (λx, x ∈ s))
  (by simp [set.subset_def]) (by simp [set.ext_iff] {contextual := tt}) (by rwa [eq]) in
⟨u, subset.trans h₁ (by simp [subset_def, and_imp, or_imp_distrib] {contextual:=tt}),
  h₂, by rwa [eq] at h⟩

lemma exists_finite_card_le_of_finite_of_linear_independent_of_span
  (ht : finite t) (hs : linear_independent α β id s) (hst : s ⊆ span α t) :
  ∃h : finite s, h.to_finset.card ≤ ht.to_finset.card :=
have s ⊆ (span α ↑(ht.to_finset) : submodule α β), by simp; assumption,
let ⟨u, hust, hsu, eq⟩ := exists_of_linear_independent_of_finite_span hs this in
have finite s, from finite_subset u.finite_to_set hsu,
⟨this, by rw [←eq]; exact (finset.card_le_of_subset $ finset.coe_subset.mp $ by simp [hsu])⟩

lemma exists_left_inverse_linear_map_of_injective {f : β →ₗ[α] γ}
  (hf_inj : f.ker = ⊥) : ∃g:γ →ₗ β, g.comp f = linear_map.id :=
begin
  rcases exists_is_basis α β with ⟨B, hB⟩,
  have : linear_independent α γ id (f '' B) :=
    hB.1.image (by simp [hf_inj]),
  rcases exists_subset_is_basis this with ⟨C, BC, hC⟩,
  haveI : inhabited β := ⟨0⟩,
  refine ⟨hC.constr (inv_fun f), hB.ext $ λ b bB, _⟩,
  rw image_subset_iff at BC,
  simp [constr_basis hC (BC bB)],
  exact left_inverse_inv_fun (linear_map.ker_eq_bot.1 hf_inj) _
end

lemma exists_right_inverse_linear_map_of_surjective {f : β →ₗ[α] γ}
  (hf_surj : f.range = ⊤) : ∃g:γ →ₗ β, f.comp g = linear_map.id :=
begin
  rcases exists_is_basis α γ with ⟨C, hC⟩,
  haveI : inhabited β := ⟨0⟩,
  refine ⟨hC.constr (inv_fun f), hC.ext $ λ c cC, _⟩,
  simp [constr_basis hC cC],
  exact right_inverse_inv_fun (linear_map.range_eq_top.1 hf_surj) _
end

set_option class.instance_max_depth 49
open submodule linear_map
theorem quotient_prod_linear_equiv (p : submodule α β) :
  nonempty ((p.quotient × p) ≃ₗ[α] β) :=
begin
  rcases exists_right_inverse_linear_map_of_surjective p.range_mkq with ⟨f, hf⟩,
  have mkf : ∀ x, submodule.quotient.mk (f x) = x := linear_map.ext_iff.1 hf,
  have fp : ∀ x, x - f (p.mkq x) ∈ p :=
    λ x, (submodule.quotient.eq p).1 (mkf (p.mkq x)).symm,
  refine ⟨linear_equiv.of_linear (f.copair p.subtype)
    (p.mkq.pair (cod_restrict p (linear_map.id - f.comp p.mkq) fp))
    (by ext; simp) _⟩,
  ext ⟨⟨x⟩, y, hy⟩; simp,
  { apply (submodule.quotient.eq p).2,
    simpa using sub_mem p hy (fp x) },
  { refine subtype.coe_ext.2 _,
    simp [mkf, (submodule.quotient.mk_eq_zero p).2 hy] }
end

open fintype
variables (b : set β) (h : is_basis α b)

local attribute [instance] finsupp.to_module
local attribute [instance] submodule.module

noncomputable def equiv_fun_basis [fintype b] : β ≃ (b → α) :=
calc β ≃ finsupp.supported α α b : (module_equiv_finsupp h).to_equiv
   ... ≃ (b →₀ α)                : finsupp.restrict_support_equiv b
   ... ≃ (b → α)                 : finsupp.equiv_fun_on_fintype

theorem vector_space.card_fintype [fintype α] [fintype β] : card β = (card α) ^ (card b) :=
calc card β = card (b → α)    : card_congr (equiv_fun_basis b h)
        ... = card α ^ card b : card_fun

theorem vector_space.card_fintype' [fintype α] [fintype β] : ∃ n : ℕ, card β = (card α) ^ n :=
let ⟨b, hb⟩ := exists_is_basis α β in ⟨card b, vector_space.card_fintype b hb⟩

end vector_space

namespace pi
open set linear_map

section module
variables {φ : ι → Type*}
variables [ring α] [∀i, add_comm_group (φ i)] [∀i, module α (φ i)] [fintype ι] [decidable_eq ι]

lemma linear_independent_std_basis (s : Πi, set (φ i)) (hs : ∀i, linear_independent α _ id (s i)) :
  linear_independent α _ id (⋃i, std_basis α φ i '' s i) :=
begin
  refine linear_independent_Union_finite _ _,
  { assume i,
    refine (linear_independent_image_iff _).2 (hs i),
    simp only [ker_std_basis, disjoint_bot_right] },
  { assume i J _ hiJ,
    simp only [set.image_id],
    simp [(set.Union.equations._eqn_1 _).symm, submodule.span_image, submodule.span_Union],
    have h₁ : map (std_basis α φ i) (span α (s i)) ≤ (⨆j∈({i} : set ι), range (std_basis α φ j)),
    { exact (le_supr_of_le i $ le_supr_of_le (set.mem_singleton _) $ map_mono $ le_top) },
    have h₂ : (⨆j∈J, map (std_basis α φ j) (span α (s j))) ≤ (⨆j∈J, range (std_basis α φ j)),
    { exact supr_le_supr (assume i, supr_le_supr $ assume hi, map_mono $ le_top) },
    exact disjoint_mono h₁ h₂
      (disjoint_std_basis_std_basis _ _ _ _ $ set.disjoint_singleton_left.2 hiJ) }
end

lemma is_basis_std_basis [fintype ι] (s : Πi, set (φ i)) (hs : ∀i, is_basis α (s i)) :
  is_basis α (⋃i, std_basis α φ i '' s i) :=
begin
  refine ⟨linear_independent_std_basis _ (assume i, (hs i).1), _⟩,
  simp only [submodule.span_Union, submodule.span_image, (assume i, (hs i).2), submodule.map_top,
    supr_range_std_basis]
end

section
variables (α ι)
lemma is_basis_fun [fintype ι] : is_basis α (⋃i, std_basis α (λi:ι, α) i '' {1}) :=
is_basis_std_basis _ (assume i, is_basis_singleton_one _)
end

end module

end pi
