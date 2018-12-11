/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Linear independence and basis sets in a module or vector space.

This file is inspired by Isabelle/HOL's linear algebra, and hence indirectly by HOL Light.

We define the following concepts:

* `linear_independent s`: states that `s` are linear independent

* `linear_independent.repr s b`: choose the linear combination representing `b` on the linear
  independent vectors `s`. `b` should be in `span b` (uses classical choice)

* `is_basis s`: if `s` is a basis, i.e. linear independent and spans the entire space

* `is_basis.repr s b`: like `linear_independent.repr` but as a `linear_map`

* `is_basis.constr s g`: constructs a `linear_map` by extending `g` from the basis `s`

-/
import linear_algebra.lc order.zorn
noncomputable theory

open function lattice set submodule
local attribute [instance] classical.prop_decidable
variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

section module
variables [ring α] [add_comm_group β] [add_comm_group γ] [add_comm_group δ]
variables [module α β] [module α γ] [module α δ]
variables {a b : α} {s t : set β} {x y : β}
include α

/-- Linearly independent set of vectors -/
def linear_independent (s : set β) : Prop :=
disjoint (lc.supported s) (lc.total β).ker

theorem linear_independent_iff : linear_independent s ↔
  ∀l ∈ lc.supported s, lc.total β l = 0 → l = 0 :=
by simp [linear_independent, linear_map.disjoint_ker]

theorem linear_independent_iff_total_on : linear_independent s ↔ (lc.total_on s).ker = ⊥ :=
by rw [lc.total_on, linear_map.ker, linear_map.comap_cod_restrict, map_bot, comap_bot,
  linear_map.ker_comp, linear_independent, disjoint, ← map_comap_subtype, map_le_iff_le_comap,
  comap_bot, ker_subtype, le_bot_iff]

lemma linear_independent_empty : linear_independent (∅ : set β) :=
by simp [linear_independent]

lemma linear_independent.mono (h : t ⊆ s) : linear_independent s → linear_independent t :=
disjoint_mono_left (lc.supported_mono h)

lemma linear_independent.unique (hs : linear_independent s) {l₁ l₂ : lc α β} :
  l₁ ∈ lc.supported s → l₂ ∈ lc.supported s →
  lc.total β l₁ = lc.total β l₂ → l₁ = l₂ :=
linear_map.disjoint_ker'.1 hs _ _

lemma zero_not_mem_of_linear_independent (ne : 0 ≠ (1:α)) (hs : linear_independent s) : (0:β) ∉ s :=
λ h, ne $ eq.symm begin
  suffices : (finsupp.single 0 1 : lc α β) 0 = 0, {simpa},
  rw disjoint_def.1 hs _ (lc.single_mem_supported 1 h),
  {refl}, {simp}
end

lemma linear_independent_union {s t : set β}
  (hs : linear_independent s) (ht : linear_independent t)
  (hst : disjoint (span s) (span t)) : linear_independent (s ∪ t) :=
begin
  rw [linear_independent, disjoint_def, lc.supported_union],
  intros l h₁ h₂, rw mem_sup at h₁,
  rcases h₁ with ⟨ls, hls, lt, hlt, rfl⟩,
  rw [span_eq_map_lc, span_eq_map_lc] at hst,
  have : lc.total β ls ∈ map (lc.total β) (lc.supported t),
  { apply (add_mem_iff_left (map _ _) (mem_image_of_mem _ hlt)).1,
    rw [← linear_map.map_add, linear_map.mem_ker.1 h₂],
    apply zero_mem },
  have ls0 := disjoint_def.1 hs _ hls (linear_map.mem_ker.2 $
    disjoint_def.1 hst _ (mem_image_of_mem _ hls) this),
  subst ls0, simp [-linear_map.mem_ker] at this h₂ ⊢,
  exact disjoint_def.1 ht _ hlt h₂
end

lemma linear_independent_of_finite
  (H : ∀ t ⊆ s, finite t → linear_independent t) :
  linear_independent s :=
linear_independent_iff.2 $ λ l hl,
linear_independent_iff.1 (H _ hl (finset.finite_to_set _)) l (subset.refl _)

lemma linear_independent_Union_of_directed {ι : Type*}
  {s : ι → set β} (hs : directed (⊆) s)
  (h : ∀ i, linear_independent (s i)) : linear_independent (⋃ i, s i) :=
begin
  by_cases hι : nonempty ι,
  { refine linear_independent_of_finite (λ t ht ft, _),
    rcases finite_subset_Union ft ht with ⟨I, fi, hI⟩,
    rcases hs.finset_le hι fi.to_finset with ⟨i, hi⟩,
    exact (h i).mono (subset.trans hI $ bUnion_subset $
      λ j hj, hi j (finite.mem_to_finset.2 hj)) },
  { refine linear_independent_empty.mono _,
    rintro _ ⟨_, ⟨i, _⟩, _⟩, exact hι ⟨i⟩ }
end

lemma linear_independent_sUnion_of_directed {s : set (set β)}
  (hs : directed_on (⊆) s)
  (h : ∀ a ∈ s, linear_independent a) : linear_independent (⋃₀ s) :=
by rw sUnion_eq_Union; exact
linear_independent_Union_of_directed
  ((directed_on_iff_directed _).1 hs) (by simpa using h)

lemma linear_independent_bUnion_of_directed {ι} {s : set ι} {t : ι → set β}
  (hs : directed_on (t ⁻¹'o (⊆)) s) (h : ∀a∈s, linear_independent (t a)) :
  linear_independent (⋃a∈s, t a) :=
by rw bUnion_eq_Union; exact
linear_independent_Union_of_directed
  ((directed_comp _ _ _).2 $ (directed_on_iff_directed _).1 hs)
  (by simpa using h)

section repr
variables (hs : linear_independent s)

def linear_independent.total_equiv : lc.supported s ≃ₗ span s :=
linear_equiv.of_bijective (lc.total_on s)
  (linear_independent_iff_total_on.1 hs) (lc.total_on_range _)

def linear_independent.repr : span s →ₗ lc α β :=
(submodule.subtype _).comp (hs.total_equiv.symm : span s →ₗ lc.supported s)

lemma linear_independent.total_repr (x) : lc.total β (hs.repr x) = x :=
subtype.ext.1 $ hs.total_equiv.right_inv x

lemma linear_independent.total_comp_repr : (lc.total β).comp hs.repr = submodule.subtype _ :=
linear_map.ext $ hs.total_repr

lemma linear_independent.repr_ker : hs.repr.ker = ⊥ :=
by rw [linear_independent.repr, linear_map.ker_comp, ker_subtype, comap_bot,
       linear_equiv.ker]

lemma linear_independent.repr_range : hs.repr.range = lc.supported s :=
by rw [linear_independent.repr, linear_map.range_comp,
       linear_equiv.range, map_top, range_subtype]

lemma linear_independent.repr_eq {l : lc α β} (h : l ∈ lc.supported s) {x} (eq : lc.total β l = ↑x) : hs.repr x = l :=
by rw ← (subtype.eq' eq : (lc.total_on s : lc.supported s →ₗ span s) ⟨l, h⟩ = x);
   exact subtype.ext.1 (hs.total_equiv.left_inv ⟨l, h⟩)

lemma linear_independent.repr_eq_single (x) (hx : ↑x ∈ s) : hs.repr x = finsupp.single x 1 :=
hs.repr_eq (lc.single_mem_supported _ hx) (by simp)

lemma linear_independent.repr_supported (x) : hs.repr x ∈ lc.supported s :=
((hs.total_equiv.symm : span s →ₗ lc.supported s) x).2

lemma linear_independent.repr_eq_repr_of_subset
  (h : t ⊆ s) (x y) (e : (↑x:β) = ↑y) :
  (hs.mono h).repr x = hs.repr y :=
eq.symm $ hs.repr_eq (lc.supported_mono h $ (hs.mono h).repr_supported _)
  (by rw [← e, (hs.mono h).total_repr]).

lemma linear_independent_iff_not_smul_mem_span :
  linear_independent s ↔ (∀ (x ∈ s) (a : α), a • x ∈ span (s \ {x}) → a = 0) :=
⟨λ hs x hx a ha, begin
  rw [span_eq_map_lc, mem_map] at ha,
  rcases ha with ⟨l, hl, e⟩,
  have := (lc.supported s).sub_mem
    (lc.supported_mono (diff_subset _ _) hl) (lc.single_mem_supported a hx),
  rw [sub_eq_zero.1 (linear_independent_iff.1 hs _ this $ by simp [e])] at hl,
  by_contra hn,
  exact (not_mem_of_mem_diff (hl $ by simp [hn])) (mem_singleton _)
end, λ H, linear_independent_iff.2 $ λ l ls l0, begin
  ext x, simp,
  by_contra hn,
  have xs : x ∈ s := ls (finsupp.mem_support_iff.2 hn),
  refine hn (H _ xs _ _),
  refine mem_span_iff_lc.2 ⟨finsupp.single x (l x) - l, _, _⟩,
  { have : finsupp.single x (l x) - l ∈ lc.supported s :=
      sub_mem _ (lc.single_mem_supported _ xs) ls,
    refine λ y hy, ⟨this hy, λ e, _⟩,
    simp at e hy, apply hy, simp [e] },
  { simp [l0] }
end⟩

end repr

lemma eq_of_linear_independent_of_span (nz : (1 : α) ≠ 0)
  (hs : linear_independent s) (h : t ⊆ s) (hst : s ⊆ span t) : s = t :=
begin
  refine subset.antisymm (λ b hb, _) h,
  have : (hs.mono h).repr ⟨b, hst hb⟩ = finsupp.single b 1 :=
    (hs.repr_eq_repr_of_subset h ⟨b, hst hb⟩ ⟨b, subset_span hb⟩ rfl).trans
      (hs.repr_eq_single ⟨b, _⟩ hb),
  have ss := (hs.mono h).repr_supported _,
  rw this at ss, exact ss (by simp [nz]),
end

section
variables {f : β →ₗ γ}
  (hs : linear_independent (f '' s))
  (hf_inj : ∀ a b ∈ s, f a = f b → a = b)
include hs hf_inj
open linear_map

lemma linear_independent.supported_disjoint_ker :
  disjoint (lc.supported s) (ker (f.comp (lc.total β))) :=
begin
  refine le_trans (le_inf inf_le_left _) (lc.map_disjoint_ker f hf_inj),
  rw [linear_independent, disjoint_iff, ← lc.map_supported f] at hs,
  rw [← lc.map_total, le_ker_iff_map],
  refine eq_bot_mono (le_inf (map_mono inf_le_left) _) hs,
  rw [map_le_iff_le_comap, ← ker_comp], exact inf_le_right
end

lemma linear_independent.of_image : linear_independent s :=
disjoint_mono_right (ker_le_ker_comp _ _) (hs.supported_disjoint_ker hf_inj)

lemma linear_independent.disjoint_ker : disjoint (span s) f.ker :=
by rw [span_eq_map_lc, disjoint_iff, map_inf_eq_map_inf_comap,
  ← ker_comp, disjoint_iff.1 (hs.supported_disjoint_ker hf_inj), map_bot]

end

lemma linear_independent.inj_span_iff_inj {s : set β} {f : β →ₗ γ}
  (hfs : linear_independent (f '' s)) :
  disjoint (span s) f.ker ↔ (∀a b ∈ s, f a = f b → a = b) :=
⟨linear_map.inj_of_disjoint_ker subset_span, hfs.disjoint_ker⟩

open linear_map
lemma linear_independent.image {s : set β} {f : β →ₗ γ} (hs : linear_independent s)
  (hf_inj : disjoint (span s) f.ker) : linear_independent (f '' s) :=
by rw [disjoint, span_eq_map_lc, map_inf_eq_map_inf_comap,
    map_le_iff_le_comap, comap_bot] at hf_inj;
  rw [linear_independent, disjoint, ← lc.map_supported f, map_inf_eq_map_inf_comap,
    map_le_iff_le_comap, ← ker_comp, lc.map_total, ker_comp];
  exact le_trans (le_inf inf_le_left hf_inj) (le_trans hs bot_le)

lemma linear_map.linear_independent_image_iff {s : set β} {f : β →ₗ γ}
  (hf_inj : disjoint (span s) f.ker) :
  linear_independent (f '' s) ↔ linear_independent s :=
⟨λ hs, hs.of_image (linear_map.inj_of_disjoint_ker subset_span hf_inj),
 λ hs, hs.image hf_inj⟩

lemma linear_independent_inl_union_inr {s : set β} {t : set γ}
  (hs : linear_independent s) (ht : linear_independent t) :
  linear_independent (inl β γ '' s ∪ inr β γ '' t) :=
linear_independent_union (hs.image $ by simp) (ht.image $ by simp) $
by rw [span_image, span_image]; simp [disjoint_iff, prod_inf_prod]

/-- A set of vectors is a basis if it is linearly independent and all vectors are in the span -/
def is_basis (s : set β) := linear_independent s ∧ span s = ⊤

section is_basis
variables (hs : is_basis s)

lemma is_basis.mem_span (hs : is_basis s) : ∀ x, x ∈ span s := eq_top_iff'.1 hs.2

def is_basis.repr : β →ₗ lc α β :=
(hs.1.repr).comp (linear_map.id.cod_restrict _ hs.mem_span)

lemma is_basis.total_repr (x) : lc.total β (hs.repr x) = x :=
hs.1.total_repr ⟨x, _⟩

lemma is_basis.total_comp_repr : (lc.total β).comp hs.repr = linear_map.id :=
linear_map.ext hs.total_repr

lemma is_basis.repr_ker : hs.repr.ker = ⊥ :=
linear_map.ker_eq_bot.2 $ injective_of_left_inverse hs.total_repr

lemma is_basis.repr_range : hs.repr.range = lc.supported s :=
by  rw [is_basis.repr, linear_map.range, submodule.map_comp,
  linear_map.map_cod_restrict, submodule.map_id, comap_top, map_top, hs.1.repr_range]

lemma is_basis.repr_supported (x) : hs.repr x ∈ lc.supported s :=
hs.1.repr_supported ⟨x, _⟩

lemma is_basis.repr_eq_single {x} : x ∈ s → hs.repr x = finsupp.single x 1 :=
hs.1.repr_eq_single ⟨x, _⟩

/-- Construct a linear map given the value at the basis. -/
def is_basis.constr (f : β → γ) : β →ₗ γ :=
(lc.total γ).comp $ (lc.map f).comp hs.repr

theorem is_basis.constr_apply (f : β → γ) (x : β) :
  (hs.constr f : β → γ) x = (hs.repr x).sum (λb a, a • f b) :=
by dsimp [is_basis.constr];
   rw [lc.total_apply, finsupp.sum_map_domain_index]; simp [add_smul]

lemma is_basis.ext {f g : β →ₗ γ} (hs : is_basis s) (h : ∀x∈s, f x = g x) : f = g :=
linear_map.ext $ λ x, linear_eq_on h (hs.mem_span x)

lemma constr_congr {f g : β → γ} {x : β} (hs : is_basis s) (h : ∀x∈s, f x = g x) :
  hs.constr f = hs.constr g :=
by ext y; simp [is_basis.constr_apply]; exact
finset.sum_congr rfl (λ x hx, by simp [h x (hs.repr_supported _ hx)])

lemma constr_basis {f : β → γ} {b : β} (hs : is_basis s) (hb : b ∈ s) :
  (hs.constr f : β → γ) b = f b :=
by simp [is_basis.constr_apply, hs.repr_eq_single hb, finsupp.sum_single_index]

lemma constr_eq {g : β → γ} {f : β →ₗ γ} (hs : is_basis s)
  (h : ∀x∈s, g x = f x) : hs.constr g = f :=
hs.ext $ λ x hx, (constr_basis hs hx).trans (h _ hx)

lemma constr_self (f : β →ₗ γ) : hs.constr f = f :=
constr_eq hs $ λ x hx, rfl

lemma constr_zero (hs : is_basis s) : hs.constr (λb, (0 : γ)) = 0 :=
constr_eq hs $ λ x hx, rfl

lemma constr_add {g f : β → γ} (hs : is_basis s) :
  hs.constr (λb, f b + g b) = hs.constr f + hs.constr g :=
constr_eq hs $ by simp [constr_basis hs] {contextual := tt}

lemma constr_neg {f : β → γ} (hs : is_basis s) : hs.constr (λb, - f b) = - hs.constr f :=
constr_eq hs $ by simp [constr_basis hs] {contextual := tt}

lemma constr_sub {g f : β → γ} (hs : is_basis s) :
  hs.constr (λb, f b - g b) = hs.constr f - hs.constr g :=
by simp [constr_add, constr_neg]

-- this only works on functions if `α` is a commutative ring
lemma constr_smul {α β γ} [comm_ring α]
  [add_comm_group β] [add_comm_group γ] [module α β] [module α γ]
  {f : β → γ} {a : α} {s : set β} (hs : is_basis s) {b : β} :
  hs.constr (λb, a • f b) = a • hs.constr f :=
constr_eq hs $ by simp [constr_basis hs] {contextual := tt}

lemma constr_range (hs : is_basis s) {f : β → γ} : (hs.constr f).range = span (f '' s) :=
by rw [is_basis.constr, linear_map.range_comp, linear_map.range_comp,
       is_basis.repr_range, lc.map_supported, span_eq_map_lc]

def module_equiv_lc (hs : is_basis s) : β ≃ₗ lc.supported s :=
(hs.1.total_equiv.trans (linear_equiv.of_top _ hs.2)).symm

def equiv_of_is_basis {s : set β} {t : set γ} {f : β → γ} {g : γ → β}
  (hs : is_basis s) (ht : is_basis t) (hf : ∀b∈s, f b ∈ t) (hg : ∀c∈t, g c ∈ s)
  (hgf : ∀b∈s, g (f b) = b) (hfg : ∀c∈t, f (g c) = c) :
  β ≃ₗ γ :=
{ inv_fun := ht.constr g,
  left_inv :=
    have (ht.constr g).comp (hs.constr f) = linear_map.id,
    from hs.ext $ by simp [constr_basis, hs, ht, hf, hgf, (∘)] {contextual := tt},
    λ x, congr_arg (λ h:β →ₗ β, h x) this,
  right_inv :=
    have (hs.constr f).comp (ht.constr g) = linear_map.id,
    from ht.ext $ by simp [constr_basis, hs, ht, hg, hfg, (∘)] {contextual := tt},
    λ y, congr_arg (λ h:γ →ₗ γ, h y) this,
  ..hs.constr f }

lemma is_basis_inl_union_inr {s : set β} {t : set γ}
  (hs : is_basis s) (ht : is_basis t) : is_basis (inl β γ '' s ∪ inr β γ '' t) :=
⟨linear_independent_inl_union_inr hs.1 ht.1,
  by rw [span_union, span_image, span_image]; simp [hs.2, ht.2]⟩

end is_basis

lemma linear_equiv.is_basis {s : set β} (hs : is_basis s)
  (f : β ≃ₗ γ) : is_basis (f '' s) :=
show is_basis ((f : β →ₗ γ) '' s), from
⟨hs.1.image $ by simp, by rw [span_image, hs.2, map_top, f.range]⟩

end module

section vector_space
variables [discrete_field α] [add_comm_group β] [add_comm_group γ]
  [vector_space α β] [vector_space α γ] {s t : set β} {x y z : β}
include α
open submodule

/- TODO: some of the following proofs can generalized with a zero_ne_one predicate type class
   (instead of a data containing type classs) -/

lemma mem_span_insert_exchange : x ∈ span (insert y s) → x ∉ span s → y ∈ span (insert x s) :=
begin
  simp [mem_span_insert],
  rintro a z hz rfl h,
  refine ⟨a⁻¹, -a⁻¹ • z, smul_mem _ _ hz, _⟩,
  have a0 : a ≠ 0, {rintro rfl, simp * at *},
  simp [a0, smul_add, smul_smul]
end

lemma linear_independent_iff_not_mem_span : linear_independent s ↔ (∀x∈s, x ∉ span (s \ {x})) :=
linear_independent_iff_not_smul_mem_span.trans
⟨λ H x xs hx, one_ne_zero (H x xs 1 $ by simpa),
 λ H x xs a hx, classical.by_contradiction $ λ a0,
   H x xs ((smul_mem_iff _ a0).1 hx)⟩

lemma linear_independent_singleton {x : β} (hx : x ≠ 0) : linear_independent ({x} : set β) :=
linear_independent_iff_not_mem_span.mpr $ by simp [hx] {contextual := tt}

lemma disjoint_span_singleton {p : submodule α β} {x : β} (x0 : x ≠ 0) :
  disjoint p (span {x}) ↔ x ∉ p :=
⟨λ H xp, x0 (disjoint_def.1 H _ xp (singleton_subset_iff.1 subset_span:_)),
begin
  simp [disjoint_def, mem_span_singleton],
  rintro xp y yp a rfl,
  by_cases a0 : a = 0, {simp [a0]},
  exact xp.elim ((smul_mem_iff p a0).1 yp),
end⟩

lemma linear_independent.insert (hs : linear_independent s) (hx : x ∉ span s) :
  linear_independent (insert x s) :=
begin
  rw ← union_singleton,
  have x0 : x ≠ 0 := mt (by rintro rfl; apply zero_mem _) hx,
  exact linear_independent_union hs (linear_independent_singleton x0)
    ((disjoint_span_singleton x0).2 hx)
end

lemma exists_linear_independent (hs : linear_independent s) (hst : s ⊆ t) :
  ∃b⊆t, s ⊆ b ∧ t ⊆ span b ∧ linear_independent b :=
begin
  rcases zorn.zorn_subset₀ {b | b ⊆ t ∧ linear_independent b} _ _
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

lemma exists_subset_is_basis (hs : linear_independent s) : ∃b, s ⊆ b ∧ is_basis b :=
let ⟨b, hb₀, hx, hb₂, hb₃⟩ := exists_linear_independent hs (@subset_univ _ _) in
⟨b, hx, hb₃, eq_top_iff.2 hb₂⟩

variable (β)
lemma exists_is_basis : ∃b : set β, is_basis b :=
let ⟨b, _, hb⟩ := exists_subset_is_basis linear_independent_empty in ⟨b, hb⟩
variable {β}

-- TODO(Mario): rewrite?
lemma exists_of_linear_independent_of_finite_span {t : finset β}
  (hs : linear_independent s) (hst : s ⊆ (span ↑t : submodule α β)) :
  ∃t':finset β, ↑t' ⊆ s ∪ ↑t ∧ s ⊆ ↑t' ∧ t'.card = t.card :=
have ∀t, ∀(s' : finset β), ↑s' ⊆ s → s ∩ ↑t = ∅ → s ⊆ (span ↑(s' ∪ t) : submodule α β) →
  ∃t':finset β, ↑t' ⊆ s ∪ ↑t ∧ s ⊆ ↑t' ∧ t'.card = (s' ∪ t).card :=
assume t, finset.induction_on t
  (assume s' hs' _ hss',
    have s = ↑s', from eq_of_linear_independent_of_span one_ne_zero hs hs' $ by simpa using hss',
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
      (assume : s ⊆ (span ↑(s' ∪ t) : submodule α β),
        let ⟨u, hust, hsu, eq⟩ := ih _ hs' hst this in
        have hb₁u : b₁ ∉ u, from assume h, (hust h).elim hb₁s hb₁t,
        ⟨insert b₁ u, by simp [insert_subset_insert hust],
          subset.trans hsu (by simp), by simp [eq, hb₁t, hb₁s', hb₁u]⟩)
      (assume : ¬ s ⊆ (span ↑(s' ∪ t) : submodule α β),
        let ⟨b₂, hb₂s, hb₂t⟩ := not_subset.mp this in
        have hb₂t' : b₂ ∉ s' ∪ t, from assume h, hb₂t $ subset_span h,
        have s ⊆ (span ↑(insert b₂ s' ∪ t) : submodule α β), from
          assume b₃ hb₃,
          have ↑(s' ∪ insert b₁ t) ⊆ insert b₁ (insert b₂ ↑(s' ∪ t) : set β),
            by simp [insert_eq, -singleton_union, -union_singleton, union_subset_union, subset.refl, subset_union_right],
          have hb₃ : b₃ ∈ span (insert b₁ (insert b₂ ↑(s' ∪ t) : set β)),
            from span_mono this (hss' hb₃),
          have s ⊆ (span (insert b₁ ↑(s' ∪ t)) : submodule α β),
            by simpa [insert_eq, -singleton_union, -union_singleton] using hss',
          have hb₁ : b₁ ∈ span (insert b₂ ↑(s' ∪ t)),
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
  (ht : finite t) (hs : linear_independent s) (hst : s ⊆ span t) :
  ∃h : finite s, h.to_finset.card ≤ ht.to_finset.card :=
have s ⊆ (span ↑(ht.to_finset) : submodule α β), by simp; assumption,
let ⟨u, hust, hsu, eq⟩ := exists_of_linear_independent_of_finite_span hs this in
have finite s, from finite_subset u.finite_to_set hsu,
⟨this, by rw [←eq]; exact (finset.card_le_of_subset $ finset.coe_subset.mp $ by simp [hsu])⟩

lemma exists_left_inverse_linear_map_of_injective {f : β →ₗ γ}
  (hf_inj : f.ker = ⊥) : ∃g:γ →ₗ β, g.comp f = linear_map.id :=
begin
  rcases exists_is_basis β with ⟨B, hB⟩,
  have : linear_independent (f '' B) :=
    hB.1.image (by simp [hf_inj]),
  rcases exists_subset_is_basis this with ⟨C, BC, hC⟩,
  haveI : inhabited β := ⟨0⟩,
  refine ⟨hC.constr (inv_fun f), hB.ext $ λ b bB, _⟩,
  rw image_subset_iff at BC,
  simp [constr_basis hC (BC bB)],
  exact left_inverse_inv_fun (linear_map.ker_eq_bot.1 hf_inj) _
end

lemma exists_right_inverse_linear_map_of_surjective {f : β →ₗ γ}
  (hf_surj : f.range = ⊤) : ∃g:γ →ₗ β, f.comp g = linear_map.id :=
begin
  rcases exists_is_basis γ with ⟨C, hC⟩,
  haveI : inhabited β := ⟨0⟩,
  refine ⟨hC.constr (inv_fun f), hC.ext $ λ c cC, _⟩,
  simp [constr_basis hC cC],
  exact right_inverse_inv_fun (linear_map.range_eq_top.1 hf_surj) _
end

open submodule linear_map
theorem quotient_prod_linear_equiv (p : submodule α β) :
  nonempty ((p.quotient × p) ≃ₗ β) :=
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
end.

end vector_space
