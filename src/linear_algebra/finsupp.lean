/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl

Linear structures on function with finit support `α →₀ β` and multivariate polynomials.
-/
import data.finsupp data.mv_polynomial
import linear_algebra.dimension
noncomputable theory

local attribute [instance, priority 0] classical.prop_decidable

open lattice set linear_map submodule

namespace finsupp

section module
variables {α : Type*} {β : Type*} {γ : Type*}
variables [decidable_eq α] [decidable_eq β] [ring γ] [add_comm_group β] [module γ β]

instance : module γ (α →₀ β) := finsupp.to_module α β

def lsingle (a : α) : β →ₗ[γ] (α →₀ β) :=
⟨single a, assume a b, single_add, assume c b, (smul_single _ _ _).symm⟩

def lapply (a : α) : (α →₀ β) →ₗ[γ] β := ⟨λg, g a, assume a b, rfl, assume a b, rfl⟩

section lmap_domain
variables {α' : Type*} [decidable_eq α']

def lmap_domain (i : α → α') : (α →₀ β) →ₗ[γ] (α' →₀ β) :=
⟨map_domain i, assume a b, map_domain_add, map_domain_smul⟩

lemma lmap_domain_apply (i : α → α') (f : α →₀ β) :
  (lmap_domain i : (α →₀ β) →ₗ[γ] (α' →₀ β)) f = map_domain i f := rfl

end lmap_domain

protected def dom_lcongr
  {α₁ : Type*} {α₂ : Type*} [decidable_eq α₁] [decidable_eq α₂] (e : α₁ ≃ α₂) :
  (α₁ →₀ β) ≃ₗ[γ] (α₂ →₀ β) :=
(finsupp.dom_congr e).to_linear_equiv
begin
  change is_linear_map γ (lmap_domain e : (α₁ →₀ β) →ₗ[γ] (α₂ →₀ β)),
  exact linear_map.is_linear _
end

section lsubtype_domain
variables (s : set α) [decidable_pred (λx, x ∈ s)]

def lsubtype_domain : (α →₀ β) →ₗ[γ] (s →₀ β) :=
⟨subtype_domain (λx, x ∈ s), assume a b, subtype_domain_add, assume c a, ext $ assume a, rfl⟩

lemma lsubtype_domain_apply (f : α →₀ β) :
  (lsubtype_domain s : (α →₀ β) →ₗ[γ] (s →₀ β)) f = subtype_domain (λx, x ∈ s) f := rfl

end lsubtype_domain

lemma lsingle_apply (a : α) (b : β) : (lsingle a : β →ₗ[γ] (α →₀ β)) b = single a b  :=
rfl

lemma lapply_apply (a : α) (f : α →₀ β) : (lapply a : (α →₀ β) →ₗ[γ] β) f = f a  :=
rfl

lemma ker_lsingle (a : α) : (lsingle a : β →ₗ[γ] (α →₀ β)).ker = ⊥ :=
ker_eq_bot.2 (injective_single a)

lemma lsingle_range_le_ker_lapply (s t : set α) (h : disjoint s t) :
  (⨆a∈s, (lsingle a : β →ₗ[γ] (α →₀ β)).range) ≤ (⨅a∈t, ker (lapply a)) :=
begin
  refine supr_le (assume a₁, supr_le $ assume h₁, range_le_iff_comap.2 _),
  simp only [(ker_comp _ _).symm, eq_top_iff, le_def', mem_ker, comap_infi, mem_infi],
  assume b hb a₂ h₂,
  have : a₁ ≠ a₂ := assume eq, h ⟨h₁, eq.symm ▸ h₂⟩,
  exact single_eq_of_ne this
end

lemma infi_ker_lapply_le_bot : (⨅a, ker (lapply a : (α →₀ β) →ₗ[γ] β)) ≤ ⊥ :=
begin
  simp only [le_def', mem_infi, mem_ker, mem_bot, lapply_apply],
  exact assume a h, finsupp.ext h
end

lemma supr_lsingle_range : (⨆a, (lsingle a : β →ₗ[γ] (α →₀ β)).range) = ⊤ :=
begin
  refine (eq_top_iff.2 $ le_def'.2 $ assume f _, _),
  rw [← sum_single f],
  refine sum_mem _ (assume a ha, submodule.mem_supr_of_mem _ a $ set.mem_image_of_mem _ trivial)
end

lemma disjoint_lsingle_lsingle (s t : set α) (hs : disjoint s t) :
  disjoint (⨆a∈s, (lsingle a : β →ₗ[γ] (α →₀ β)).range) (⨆a∈t, (lsingle a).range) :=
begin
  refine disjoint_mono
    (lsingle_range_le_ker_lapply _ _ $ disjoint_compl s)
    (lsingle_range_le_ker_lapply _ _ $ disjoint_compl t)
    (le_trans (le_infi $ assume i, _) infi_ker_lapply_le_bot),
  classical,
  by_cases his : i ∈ s,
  { by_cases hit : i ∈ t,
    { exact (hs ⟨his, hit⟩).elim },
    exact inf_le_right_of_le (infi_le_of_le i $ infi_le _ hit) },
  exact inf_le_left_of_le (infi_le_of_le i $ infi_le _ his)
end

lemma span_single_image (s : set β) (a : α) :
  submodule.span γ (single a '' s) = (submodule.span γ s).map (lsingle a) :=
by rw ← span_image; refl

lemma linear_independent_single {f : α → set β}
  (hf : ∀a, linear_independent γ (f a)) : linear_independent γ (⋃a, single a '' f a) :=
begin
  refine linear_independent_Union_finite _ _ ,
  { refine assume a, @linear_independent.image _ _ _ _ _ _ _ _ _ (lsingle a) (hf a) _,
    rw ker_lsingle,
    exact disjoint_bot_right },
  { assume a s hs hat,
    have : ∀a, span γ (single a '' f a) ≤ range (lsingle a),
    { simp only [span_single_image],
      exact assume a, map_mono le_top },
    refine disjoint_mono _ _ (disjoint_lsingle_lsingle {a} s _),
    { simp only [supr_singleton, this] },
    { exact supr_le_supr (assume a, supr_le_supr (assume ha, this a)) },
    { rwa [disjoint_singleton_left] } }
end

section
variables (β γ)

def restrict_dom (s : set α) : submodule γ (α →₀ β) :=
begin
  refine ⟨ {p | ↑p.support ⊆ s }, _, _, _ ⟩,
  { simp only [subset_def, finset.mem_coe, set.mem_set_of_eq, mem_support_iff, zero_apply],
    assume h ha, exact (ha rfl).elim },
  { assume p q hp hq,
    refine subset.trans
      (subset.trans (finset.coe_subset.2 support_add) _) (union_subset hp hq),
    rw [finset.coe_union] },
  { assume a p hp,
    refine subset.trans (finset.coe_subset.2 support_smul) hp }
end

lemma mem_restrict_dom {s : set α} (p : α →₀ β) : p ∈ (restrict_dom β γ s) ↔ ↑p.support ⊆ s :=
iff.rfl

section
set_option class.instance_max_depth 37
def restrict_dom_equiv_finsupp (s : set α) [decidable_pred (λ (x : α), x ∈ s)] :
  (restrict_dom β γ s) ≃ₗ[γ] (s →₀ β) :=
(restrict_support_equiv s).to_linear_equiv
begin
  show is_linear_map γ ((lsubtype_domain s : (α →₀ β) →ₗ[γ] (s →₀ β)).comp
      (submodule.subtype (restrict_dom β γ s))),
  exact linear_map.is_linear _
end
end

end

end module

section vector_space
variables {α : Type*} {β : Type*} {γ : Type*}
variables [decidable_eq α] [decidable_eq β] [discrete_field γ] [add_comm_group β] [vector_space γ β]

open linear_map submodule

instance : vector_space γ (α →₀ β) :=
{ to_module := finsupp.module }

lemma is_basis_single {f : α → set β} (hf : ∀a, is_basis γ (f a)) :
  is_basis γ (⋃a, single a '' f a) :=
⟨linear_independent_single $ assume a, (hf a).1,
  by simp only [span_Union, span_single_image, (hf _).2, map_top, supr_lsingle_range]⟩

end vector_space

section dim
universes u v
variables {α : Type u} {β : Type u} {γ : Type v}
variables [decidable_eq α] [decidable_eq β] [discrete_field γ] [add_comm_group β] [vector_space γ β]

lemma dim_eq : vector_space.dim γ (α →₀ β) = cardinal.mk α * vector_space.dim γ β :=
begin
  rcases exists_is_basis γ β with ⟨bs, hbs⟩,
  rw [← hbs.mk_eq_dim, ← (is_basis_single (λa:α, hbs)).mk_eq_dim, cardinal.mk_Union_eq_sum_mk],
  { simp only [cardinal.mk_image_eq (injective_single.{u u} _), cardinal.sum_const] },
  { refine assume i j h, disjoint_image_image (assume b hb c hc, _),
    simp only [(≠), single_eq_single_iff, not_or_distrib, not_and_distrib],
    have : (0:β) ∉ bs := zero_not_mem_of_linear_independent (zero_ne_one : (0:γ) ≠ 1) hbs.1,
    exact ⟨or.inl h, or.inl (assume eq, this $ eq ▸ hb)⟩ }
end

end dim

end finsupp

namespace lc
universes u v w
variables (α : Type v) {β : Type u} {γ : Type w}
variables [ring α]
variables [add_comm_group β] [module α β]
variables [add_comm_group γ] [module α γ]

noncomputable def congr (s : set β) (t : set γ) (e : s ≃ t) : supported α s ≃ₗ[α] supported α t :=
begin
  show (finsupp.restrict_dom α α s) ≃ₗ[α] (finsupp.restrict_dom α α t),
  refine linear_equiv.trans (finsupp.restrict_dom_equiv_finsupp α α s)
    (linear_equiv.trans _ (finsupp.restrict_dom_equiv_finsupp α α t).symm),
  exact finsupp.dom_lcongr e
end

-- TODO: this is bad, we need to fix the decidability instances
noncomputable def supported_equiv [decidable_eq β] (s : set β) :
  lc.supported α s ≃ₗ[α] (s →₀ α) :=
begin
  have eq : _inst_6 = (λa b : β, classical.prop_decidable (a = b)) := subsingleton.elim _ _,
  unfreezeI, subst eq,
  refine (finsupp.restrict_dom_equiv_finsupp α α s)
end

end lc

section vector_space
universes u v
variables {α : Type u} {β γ : Type v}
variables [discrete_field α]
variables [add_comm_group β] [vector_space α β]
variables [add_comm_group γ] [vector_space α γ]

open vector_space

set_option class.instance_max_depth 100

lemma equiv_of_dim_eq_dim (h : dim α β = dim α γ) : nonempty (β ≃ₗ[α] γ) :=
begin
  rcases exists_is_basis α β with ⟨b, hb⟩,
  rcases exists_is_basis α γ with ⟨c, hc⟩,
  rw [← hb.mk_eq_dim, ← hc.mk_eq_dim] at h,
  rcases quotient.exact h with ⟨e⟩,
  exact ⟨ (module_equiv_lc hb).trans (linear_equiv.trans (lc.congr α b c e) (module_equiv_lc hc).symm) ⟩
end

lemma eq_bot_iff_dim_eq_zero (p : submodule α β) (h : dim α p = 0) : p = ⊥ :=
begin
  have : dim α p = dim α (⊥ : submodule α β) := by rwa [dim_bot],
  rcases equiv_of_dim_eq_dim this with ⟨e⟩,
  exact e.eq_bot_of_equiv _
end

lemma injective_of_surjective (f : β →ₗ[α] γ)
  (hβ : dim α β < cardinal.omega) (heq : dim α γ = dim α β) (hf : f.range = ⊤) : f.ker = ⊥ :=
have hk : dim α f.ker < cardinal.omega := lt_of_le_of_lt (dim_submodule_le _) hβ,
begin
  rcases cardinal.lt_omega.1 hβ with ⟨d₁, eq₁⟩,
  rcases cardinal.lt_omega.1 hk with ⟨d₂, eq₂⟩,
  have : 0 = d₂,
  { have := dim_eq_surjective f (linear_map.range_eq_top.1 hf),
    rw [heq, eq₁, eq₂, ← nat.cast_add, cardinal.nat_cast_inj] at this,
    exact nat.add_left_cancel this },
  refine eq_bot_iff_dim_eq_zero _ _,
  rw [eq₂, ← this, nat.cast_zero]
end

end vector_space

section vector_space
universes u

open vector_space
set_option class.instance_max_depth 100

lemma cardinal_mk_eq_cardinal_mk_field_pow_dim
  {α β : Type u} [discrete_field α] [add_comm_group β] [vector_space α β]
  (h : dim α β < cardinal.omega) : cardinal.mk β = cardinal.mk α ^ dim α β  :=
begin
  rcases exists_is_basis α β with ⟨s, hs⟩,
  have : nonempty (fintype s),
  { rwa [← cardinal.lt_omega_iff_fintype, hs.mk_eq_dim] },
  cases this with hsf, letI := hsf,
  calc cardinal.mk β = cardinal.mk (↥(lc.supported α s)) :
    quotient.sound ⟨(module_equiv_lc hs).to_equiv⟩
    ... = cardinal.mk (s →₀ α) :
    begin
      refine quotient.sound ⟨@linear_equiv.to_equiv α _ _ _ _ _ _ _ _⟩,
      convert @lc.supported_equiv α β _ _ _ _ s,
      { funext, exact subsingleton.elim _ _ },
    end
    ... = cardinal.mk (s → α) : quotient.sound ⟨finsupp.equiv_fun_on_fintype⟩
    ... = _ : by rw [← hs.mk_eq_dim, cardinal.power_def]
end

lemma cardinal_lt_omega_of_dim_lt_omega
  {α β : Type u} [discrete_field α] [add_comm_group β] [vector_space α β] [fintype α]
  (h : dim α β < cardinal.omega) : cardinal.mk β < cardinal.omega :=
begin
  rw [cardinal_mk_eq_cardinal_mk_field_pow_dim h],
  exact cardinal.power_lt_omega (cardinal.lt_omega_iff_fintype.2 ⟨infer_instance⟩) h
end

end vector_space

namespace mv_polynomial
universes u v
variables {σ : Type u} {α : Type v} [decidable_eq σ]

instance [discrete_field α] : vector_space α (mv_polynomial σ α) :=
finsupp.vector_space

section
variables (σ α) [discrete_field α] (m : ℕ)
def restrict_total_degree : submodule α (mv_polynomial σ α) :=
finsupp.restrict_dom _ _ {n | n.sum (λn e, e) ≤ m }

lemma mem_restrict_total_degree (p : mv_polynomial σ α) :
  p ∈ restrict_total_degree σ α m ↔ p.total_degree ≤ m :=
begin
  rw [total_degree, finset.sup_le_iff],
  refl
end

end

noncomputable instance decidable_restrict_degree (m : ℕ) :
  decidable_pred (λn, n ∈ {n : σ →₀ ℕ | ∀i, n i ≤ m }) :=
assume n, classical.prop_decidable _

section
variables (σ α)
def restrict_degree (m : ℕ) [discrete_field α] : submodule α (mv_polynomial σ α) :=
finsupp.restrict_dom _ _ {n | ∀i, n i ≤ m }
end

lemma mem_restrict_degree [discrete_field α] (p : mv_polynomial σ α) (n : ℕ) :
  p ∈ restrict_degree σ α n ↔ (∀s ∈ p.support, ∀i, (s : σ →₀ ℕ) i ≤ n) :=
begin
  rw [restrict_degree, finsupp.mem_restrict_dom],
  refl
end

lemma mem_restrict_degree_iff_sup [discrete_field α] (p : mv_polynomial σ α) (n : ℕ) :
  p ∈ restrict_degree σ α n ↔ ∀i, p.degrees.count i ≤ n :=
begin
  simp only [mem_restrict_degree, degrees, multiset.count_sup, finsupp.count_to_multiset,
    finset.sup_le_iff],
  exact ⟨assume h n s hs, h s hs n, assume h s hs n, h n s hs⟩
end

lemma map_range_eq_map {β : Type*}
  [decidable_eq α] [comm_ring α] [decidable_eq β] [comm_ring β] (p : mv_polynomial σ α)
  (f : α → β) [is_semiring_hom f]:
  finsupp.map_range f (is_semiring_hom.map_zero f) p = p.map f :=
begin
  rw [← finsupp.sum_single p, finsupp.sum, finsupp.map_range_finset_sum,
    ← finset.sum_hom (map f)],
  { refine finset.sum_congr rfl (assume n _, _),
    rw [finsupp.map_range_single, ← monomial, ← monomial, map_monomial] },
  apply_instance
end

section
variables (σ α)
lemma is_basis_monomials [discrete_field α] :
  is_basis α (range (λs, monomial s 1) : set (mv_polynomial σ α)) :=
suffices is_basis α (⋃i, (monomial i : α → mv_polynomial σ α) '' {1}),
  by simpa only [range_eq_Union, image_singleton],
finsupp.is_basis_single (assume s, is_basis_singleton_one α)
end

end mv_polynomial

namespace mv_polynomial
universe u
variables (σ : Type u) (α : Type u) [decidable_eq σ] [discrete_field α]

lemma dim_mv_polynomial : vector_space.dim α (mv_polynomial σ α) = cardinal.mk (σ →₀ ℕ) :=
begin
  rw [← (is_basis_monomials σ α).mk_eq_dim, ← set.image_univ, cardinal.mk_image_eq,
    cardinal.mk_univ],
  assume a b h,
  rcases (finsupp.single_eq_single_iff _ _ _ _).1 h with ⟨rfl, _⟩ | ⟨h, _⟩,
  { refl },
  { exact (zero_ne_one.symm h).elim }
end

end mv_polynomial
