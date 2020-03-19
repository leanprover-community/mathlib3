import analysis.convex.basic order.zorn

universes u v

open set linear_map
open_locale classical

set_option class.instance_max_depth 60

namespace linear_equiv

variables  {R : Type*} [ring R] {E : Type*} [add_comm_group E] [module R E]
  {E' : Type*} [add_comm_group E'] [module R E'] {F : Type*} [add_comm_group F] [module R F]
  {F' : Type*} [add_comm_group F'] [module R F']

protected def prod (e : E ≃ₗ[R] F) (e' : E' ≃ₗ[R] F') :
  (E × E') ≃ₗ[R] F × F' :=
{ add := λ x y, prod.ext (e.map_add _ _) (e'.map_add _ _),
  smul := λ c x, prod.ext (e.map_smul c _) (e'.map_smul c _),
  .. equiv.prod_congr e.to_equiv e'.to_equiv }

lemma prod_symm (e : E ≃ₗ[R] F) (e' : E' ≃ₗ[R] F') : (e.prod e').symm = e.symm.prod e'.symm := rfl

lemma prod_apply (e : E ≃ₗ[R] F) (e' : E' ≃ₗ[R] F') (p : E × E') :
  e.prod e' p = (e p.1, e' p.2) := rfl

protected lemma bijective (e : E ≃ₗ[R] F) : function.bijective e := e.to_equiv.bijective
protected lemma injective (e : E ≃ₗ[R] F) : function.injective e := e.to_equiv.injective
protected lemma surjective (e : E ≃ₗ[R] F) : function.surjective e := e.to_equiv.surjective

@[simp] lemma refl_apply (x : E) : (refl E : E ≃ₗ[R] E) x = x := rfl

end linear_equiv

namespace submodule

section ring

variables {R : Type u} [ring R] {E : Type v} [add_comm_group E] [module R E]

@[simp] lemma of_le_refl {p : submodule R E} (h : p ≤ p) : of_le h = id :=
linear_map.ext $ λ ⟨x, hx⟩, rfl

@[simp] lemma of_le_comp {p₁ p₂ p₃ : submodule R E} (h₁₂ : p₁ ≤ p₂) (h₂₃ : p₂ ≤ p₃) :
  (of_le h₂₃).comp (of_le h₁₂) = of_le (le_trans h₁₂ h₂₃) :=
linear_map.ext $ λ ⟨x, hx⟩, rfl

/-- If two submomdules are disjoint, then their supremum is isomorphic to their product. -/
noncomputable def sup_equiv_prod {s t : submodule R E} (hst : disjoint s t) :
  ↥(s ⊔ t) ≃ₗ[R] (s × t) :=
begin
  refine (linear_equiv.of_bijective _ _ _).symm,
  { exact (of_le (le_sup_left : s ≤ s ⊔ t)).copair (of_le le_sup_right) },
  { apply ker_eq_bot'.2,
    rintros ⟨x, y⟩ hxy,
    simp only [copair_apply, subtype.coe_ext, coe_add, coe_of_le, coe_zero] at hxy,
    simp only [prod.ext_iff, prod.fst_zero, prod.snd_zero, subtype.coe_ext, coe_zero],
    rw disjoint_def at hst,
    exact ⟨hst x x.2 $ (eq_neg_iff_add_eq_zero.2 hxy).symm ▸ t.neg_mem y.2,
      hst y (neg_eq_iff_add_eq_zero.2 hxy ▸ s.neg_mem x.2) y.2⟩ },
  { rw range_eq_top,
    rintros ⟨x, hx⟩,
    rcases mem_sup.1 hx with ⟨y, hy, z, hz, rfl⟩,
    exact ⟨⟨⟨y, hy⟩, ⟨z, hz⟩⟩, rfl⟩ }
end

@[simp] lemma sup_equiv_prod_symm_inl {s t : submodule R E} (hst : disjoint s t) (x : s) :
  (sup_equiv_prod hst).symm (inl R s t x) = (of_le (le_sup_left : s ≤ s ⊔ t)) x :=
by rw [sup_equiv_prod, linear_equiv.symm_symm, linear_equiv.of_bijective_apply,
  ← linear_map.comp_apply, linear_map.copair_inl]

@[simp] lemma sup_equiv_prod_symm_inr {s t : submodule R E} (hst : disjoint s t) (x : t) :
  (sup_equiv_prod hst).symm (inr R s t x) = (of_le (le_sup_right : t ≤ s ⊔ t)) x :=
by rw [sup_equiv_prod, linear_equiv.symm_symm, linear_equiv.of_bijective_apply,
  ← linear_map.comp_apply, linear_map.copair_inr]

@[simp] lemma sup_equiv_prod_left {s t : submodule R E} (hst : disjoint s t)
  (x : s ⊔ t) (hx : (x : E) ∈ s) :
  sup_equiv_prod hst x = inl R s t ⟨x, hx⟩ :=
(sup_equiv_prod hst).symm.injective $ subtype.coe_ext.2 $
by rw [(sup_equiv_prod hst).symm_apply_apply, sup_equiv_prod_symm_inl, coe_of_le, subtype.coe_mk]

@[simp] lemma sup_equiv_prod_right {s t : submodule R E} (hst : disjoint s t)
  (x : s ⊔ t) (hx : (x : E) ∈ t) :
  sup_equiv_prod hst x = inr R s t ⟨x, hx⟩ :=
(sup_equiv_prod hst).symm.injective $ subtype.coe_ext.2 $
by rw [(sup_equiv_prod hst).symm_apply_apply, sup_equiv_prod_symm_inr, coe_of_le, subtype.coe_mk]

end ring

section division_ring

variables {K : Type*} [division_ring K] {E : Type*} [add_comm_group E] [module K E]

lemma disjoint_span_singleton {s : submodule K E} {x : E} :
  disjoint s (span K {x}) ↔ (x ∈ s → x = 0) :=
begin
  refine disjoint_def.trans ⟨λ H hx, H x hx $ subset_span $ mem_singleton x, _⟩,
  assume H y hy hyx,
  obtain ⟨c, hc⟩ := mem_span_singleton.1 hyx,
  subst y,
  by_cases hc : c = 0, by simp only [hc, zero_smul],
  rw [s.smul_mem_iff hc] at hy,
  rw [H hy, smul_zero]
end

variable (K)

/-- If `x` is a non-zero element of a module over a `division_ring`, then
`span K {x}` is isomorphic to `K` -/
noncomputable def span_singleton_equiv {x : E} (hx : x ≠ 0) :
  ↥(span K ({x} : set E)) ≃ₗ[K] K :=
begin
  refine (linear_equiv.of_bijective _ _ _).symm,
  exact smul_right 1 ⟨x, subset_span $ mem_singleton x⟩,
  { refine ker_eq_bot'.2 (λ c hc, _),
    rw [smul_right_apply, one_app, smul_eq_zero, subtype.ext] at hc,
    exact hc.elim id (λ hx', (hx hx').elim) },
  { refine range_eq_top.2 (λ y, _),
    obtain ⟨c, hc⟩ := mem_span_singleton.1 y.2,
    use c,
    rwa [smul_right_apply, one_app, subtype.ext] }
end

variable {K}

lemma span_singleton_equiv_symm_apply {x : E} (hx : x ≠ 0) (c : K) :
  (span_singleton_equiv K hx).symm c = c • ⟨x, subset_span $ mem_singleton x⟩ :=
by rw [span_singleton_equiv, linear_equiv.symm_symm, linear_equiv.of_bijective_apply,
  smul_right_apply, one_app]

/-- If `s` is a submodule of `E` and `x ∉ s`, then `s ⊔ span K {x}` is isomorphic to `s × K`. -/
noncomputable def sup_span_singleton_equiv (s : submodule K E) {x : E} (hx : x ∉ s) :
  ↥(s ⊔ span K {x}) ≃ₗ[K] s × K :=
(sup_equiv_prod (disjoint_span_singleton.2 $ λ hx', absurd hx' hx)).trans $
  (linear_equiv.refl s).prod $ span_singleton_equiv K $ λ hx', hx $ hx'.symm ▸ s.zero_mem

lemma sup_span_singleton_equiv_left (s : submodule K E) {x : E} (hx : x ∉ s)
  (y : s ⊔ span K {x}) (hy : (y : E) ∈ s) :
  sup_span_singleton_equiv s hx y = inl K s K ⟨y, hy⟩ :=
by rw [sup_span_singleton_equiv, linear_equiv.trans_apply, sup_equiv_prod_left,
  linear_equiv.prod_apply, inl_apply, linear_equiv.refl_apply, linear_equiv.map_zero, inl_apply]

lemma sup_span_singleton_equiv_symm_apply (s : submodule K E) {x : E} (hx : x ∉ s) (y : s × K) :
  ((sup_span_singleton_equiv s hx).symm y : E) = y.fst + y.snd • x := rfl
  
end division_ring

end submodule

structure linear_pmap (R : Type*) [ring R] (E : Type*) [add_comm_group E] [module R E]
  (F : Type*) [add_comm_group F] [module R F] :=
(domain : submodule R E)
(to_fun : domain →ₗ[R] F)

namespace linear_pmap

variables {R : Type*} [ring R] {E : Type*} [add_comm_group E] [module R E]
  {F : Type*} [add_comm_group F] [module R F]

open submodule

instance : has_coe_to_fun (linear_pmap R E F) :=
⟨λ f : linear_pmap R E F, f.domain → F, λ f, f.to_fun⟩

@[simp] lemma to_fun_eq_coe (f : linear_pmap R E F) (x : f.domain) :
  f.to_fun x = f x := rfl

lemma map_add (f : linear_pmap R E F) (x y : f.domain) : f (x + y) = f x + f y :=
f.to_fun.map_add x y

lemma map_smul (f : linear_pmap R E F) (c : R) (x : f.domain) : f (c • x) = c • f x :=
f.to_fun.map_smul c x

@[simp] lemma mk_apply (p : submodule R E) (f : p →ₗ[R] F) (x : p) :
  mk p f x = f x := rfl

instance : partial_order (linear_pmap R E F) :=
{ le := λ f g, f.domain ≤ g.domain ∧ ∀ (x : E) (hf : x ∈ f.domain) (hg : x ∈ g.domain),
    f ⟨x, hf⟩ = g ⟨x, hg⟩,
  le_refl := λ f, ⟨le_refl f.domain, λ x h₁ h₂, rfl⟩,
  le_trans := λ f g h ⟨fg_le, fg_eq⟩ ⟨gh_le, gh_eq⟩,
    ⟨le_trans fg_le gh_le, λ x hf hh, by rw [fg_eq x hf (fg_le hf), gh_eq]⟩,
  le_antisymm :=
    begin
      rintros ⟨f_dom, f_fun⟩ ⟨g_dom, g_fun⟩ ⟨hfg_le, hfg_eq⟩ ⟨hgf_le, hgf_eq⟩,
      have : f_dom = g_dom, from le_antisymm hfg_le hgf_le,
      subst g_dom,
      have : f_fun = g_fun, from linear_map.ext (λ ⟨x, hx⟩, hfg_eq _ _ _),
      subst g_fun
    end }

lemma domain_mono : monotone (@domain R _ E _ _ F _ _) := λ p q, and.left

/-- Glue a collection of partially defined linear maps to a linear map defined on `Sup`
of these submodules. -/
lemma chain_Sup_bound (c : set (linear_pmap R E F)) (hc : directed_on (≤) c) :
  ∃ f : ↥(Sup (domain '' c)) →ₗ[R] F, (⟨_, f⟩ : linear_pmap R E F) ∈ upper_bounds c :=
begin
  cases c.eq_empty_or_nonempty with ceq cne, { subst c, simp },
  have hdir : directed_on (≤) (domain '' c),
    from (directed_on_image _).2 (hc.mono _ domain_mono),
  have P : Π x : Sup (domain '' c), {p : c // (x : E) ∈ p.val.domain },
  { rintros x,
    apply classical.indefinite_description,
    have := (mem_Sup_of_directed (cne.image _) hdir).1 x.2,
    rwa [bex_image_iff, set_coe.exists'] at this },
  set f : Sup (domain '' c) → F := λ x, (P x).val.val ⟨x, (P x).property⟩,
  have f_eq : ∀ (p : c) (x : Sup (domain '' c)) (hx : (x : E) ∈ p.1.1), f x = p.1 ⟨x, hx⟩,
  { intros p x hx,
    rcases hc (P x).1.1 (P x).1.2 p.1 p.2 with ⟨q, hqc, hxq, hpq⟩,
    exact (hxq.right _ _ (hpq.1 hx)).trans (hpq.right _ _ _).symm },
  refine ⟨⟨f, _, _⟩, _⟩,
  { intros x y,
    rcases hc (P x).1.1 (P x).1.2 (P y).1.1 (P y).1.2 with ⟨p, hpc, hpx, hpy⟩,
    replace hpx := hpx.left (P x).2,
    replace hpy := hpy.left (P y).2,
    rw [f_eq ⟨p, hpc⟩ x hpx, f_eq ⟨p, hpc⟩ y hpy, f_eq ⟨p, hpc⟩ (x + y) (add_mem _ hpx hpy),
      ← map_add],
    refl },
  { intros c x,
    rw [f_eq (P x).1 (c • x) (smul_mem _ c (P x).2), ← map_smul],
    refl },
  { intros p hpc,
    refine ⟨le_Sup $ mem_image_of_mem domain hpc, λ x hxp hxf, eq.symm _⟩,
    exact f_eq ⟨p, hpc⟩ ⟨x, hxf⟩ hxp }
end

end linear_pmap

variables (E : Type*) [add_comm_group E] [vector_space ℝ E]
  {F : Type*} [add_comm_group F] [vector_space ℝ F]
  {G : Type*} [add_comm_group G] [vector_space ℝ G]

structure convex_cone :=
(carrier : set E)
(smul_mem' : ∀ ⦃c : ℝ⦄, 0 < c → ∀ ⦃x : E⦄, x ∈ carrier → c • x ∈ carrier)
(add_mem' : ∀ ⦃x⦄ (hx : x ∈ carrier) ⦃y⦄ (hy : y ∈ carrier), x + y ∈ carrier)

variable {E}

namespace convex_cone

variables (S T : convex_cone E)

instance : has_coe (convex_cone E) (set E) := ⟨convex_cone.carrier⟩

instance : has_mem E (convex_cone E) := ⟨λ m S, m ∈ S.carrier⟩

instance : has_le (convex_cone E) := ⟨λ S T, S.carrier ⊆ T.carrier⟩

instance : has_lt (convex_cone E) := ⟨λ S T, S.carrier ⊂ T.carrier⟩

@[simp, elim_cast] lemma mem_coe {x : E} : x ∈ (S : set E) ↔ x ∈ S := iff.rfl

/-- Two `convex_cone`s are equal if the underlying subsets are equal. -/
theorem ext' {S T : convex_cone E} (h : (S : set E) = T) : S = T :=
by cases S; cases T; congr'

/-- Two `convex_cone`s are equal if and only if the underlying subsets are equal. -/
protected theorem ext'_iff {S T : convex_cone E}  : (S : set E) = T ↔ S = T :=
⟨ext', λ h, h ▸ rfl⟩

/-- Two `convex_cone`s are equal if they have the same elements. -/
@[ext] theorem ext {S T : convex_cone E} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := ext' $ set.ext h

lemma smul_mem {c : ℝ} {x : E} (hc : 0 < c) (hx : x ∈ S) : c • x ∈ S := S.smul_mem' hc hx

lemma add_mem ⦃x⦄ (hx : x ∈ S) ⦃y⦄ (hy : y ∈ S) : x + y ∈ S := S.add_mem' hx hy

lemma smul_mem_iff {c : ℝ} (hc : 0 < c) {x : E} :
  c • x ∈ S ↔ x ∈ S :=
⟨λ h, by simpa only [smul_smul, inv_mul_cancel (ne_of_gt hc), one_smul]
  using S.smul_mem (inv_pos hc) h, λ h, S.smul_mem hc h⟩

lemma convex : convex (S : set E) :=
convex_iff_forall_pos.2 $ λ x y hx hy a b ha hb hab,
S.add_mem (S.smul_mem ha hx) (S.smul_mem hb hy)

instance : has_inf (convex_cone E) :=
⟨λ S T, ⟨S ∩ T, λ c hc x hx, ⟨S.smul_mem hc hx.1, T.smul_mem hc hx.2⟩,
  λ x hx y hy, ⟨S.add_mem hx.1 hy.1, T.add_mem hx.2 hy.2⟩⟩⟩

lemma coe_inf : ((S ⊓ T : convex_cone E) : set E) = ↑S ∩ ↑T := rfl

lemma mem_inf {x} : x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T := iff.rfl

instance : has_Inf (convex_cone E) :=
⟨λ S, ⟨⋂ s ∈ S, ↑s,
  λ c hc x hx, mem_bInter $ λ s hs, s.smul_mem hc $ by apply mem_bInter_iff.1 hx s hs,
  λ x hx y hy, mem_bInter $ λ s hs, s.add_mem (by apply mem_bInter_iff.1 hx s hs)
    (by apply mem_bInter_iff.1 hy s hs)⟩⟩

lemma mem_Inf {x : E} {S : set (convex_cone E)} : x ∈ Inf S ↔ ∀ s ∈ S, x ∈ s := mem_bInter_iff

instance : has_bot (convex_cone E) := ⟨⟨∅, λ c hc x, false.elim, λ x, false.elim⟩⟩

lemma mem_bot (x : E) : x ∈ (⊥ : convex_cone E) = false := rfl

instance : has_top (convex_cone E) := ⟨⟨univ, λ c hc x hx, mem_univ _, λ x hx y hy, mem_univ _⟩⟩

lemma mem_top (x : E) : x ∈ (⊤ : convex_cone E) := mem_univ x

instance : complete_lattice (convex_cone E) :=
{ le           := (≤),
  lt           := (<),
  bot          := (⊥),
  bot_le       := λ S x, false.elim,
  top          := (⊤),
  le_top       := λ S x hx, mem_top x,
  inf          := (⊓),
  Inf          := has_Inf.Inf,
  sup          := λ a b, Inf {x | a ≤ x ∧ b ≤ x},
  Sup          := λ s, Inf {T | ∀ S ∈ s, S ≤ T},
  le_sup_left  := λ a b, λ x hx, mem_Inf.2 $ λ s hs, hs.1 hx,
  le_sup_right := λ a b, λ x hx, mem_Inf.2 $ λ s hs, hs.2 hx,
  sup_le       := λ a b c ha hb x hx, mem_Inf.1 hx c ⟨ha, hb⟩,
  le_inf       := λ a b c ha hb x hx, ⟨ha hx, hb hx⟩,
  inf_le_left  := λ a b x, and.left,
  inf_le_right := λ a b x, and.right,
  le_Sup       := λ s p hs x hx, mem_Inf.2 $ λ t ht, ht p hs hx,
  Sup_le       := λ s p hs x hx, mem_Inf.1 hx p hs,
  le_Inf       := λ s a ha x hx, mem_Inf.2 $ λ t ht, ha t ht hx,
  Inf_le       := λ s a ha x hx, mem_Inf.1 hx _ ha,
  .. partial_order.lift (coe : convex_cone E → set E) (λ a b, ext') (by apply_instance) }

/-- Image of a convex cone under an `ℝ`-linear map is a convex cone. -/
def map (f : E →ₗ[ℝ] F) (S : convex_cone E) : convex_cone F :=
{ carrier := f '' S,
  smul_mem' := λ c hc y ⟨x, hx, hy⟩, hy ▸ f.map_smul c x ▸ mem_image_of_mem f (S.smul_mem hc hx),
  add_mem' := λ y₁ ⟨x₁, hx₁, hy₁⟩ y₂ ⟨x₂, hx₂, hy₂⟩, hy₁ ▸ hy₂ ▸ f.map_add x₁ x₂ ▸
    mem_image_of_mem f (S.add_mem hx₁ hx₂) }

lemma map_map (g : F →ₗ[ℝ] G) (f : E →ₗ[ℝ] F) (S : convex_cone E) :
  (S.map f).map g = S.map (g.comp f) :=
ext' $ image_image g f S

@[simp] lemma map_id : S.map linear_map.id = S := ext' $ image_id _

/-- Preimage of a convex cone under an `ℝ`-linear map is a convex cone. -/
def comap (f : E →ₗ[ℝ] F) (S : convex_cone F) : convex_cone E :=
{ carrier := f ⁻¹' S,
  smul_mem' := λ c hc x hx, by { rw [mem_preimage, f.map_smul c], exact S.smul_mem hc hx },
  add_mem' := λ x hx y hy, by { rw [mem_preimage, f.map_add], exact S.add_mem hx hy } }

@[simp] lemma comap_id : S.comap linear_map.id = S := ext' preimage_id

lemma comap_comap (g : F →ₗ[ℝ] G) (f : E →ₗ[ℝ] F) (S : convex_cone G) :
  (S.comap g).comap f = S.comap (g.comp f) :=
ext' $ preimage_comp.symm

@[simp] lemma mem_comap {f : E →ₗ[ℝ] F} {S : convex_cone F} {x : E} :
  x ∈ S.comap f ↔ f x ∈ S := iff.rfl

end convex_cone

/-- Cone over a `convex` set is a `convex_cone`. -/
lemma convex.to_cone (s : set E) (hs : convex s) :
  convex_cone E :=
convex_cone.mk {x : E | ∃ (c : ℝ) (hC : 0 < c), c • x ∈ s}
begin
  rintros c c_pos x ⟨c', c'_pos, hc'⟩,
  refine ⟨c' / c, div_pos c'_pos c_pos, _⟩,
  rwa [smul_smul, div_mul_cancel _ (ne_of_gt c_pos)]
end
begin
  rintros x ⟨cx, cx_pos, hcx⟩ y ⟨cy, cy_pos, hcy⟩,
  refine ⟨cx * cy / (cy + cx), div_pos (mul_pos cx_pos cy_pos) (add_pos cy_pos cx_pos), _⟩,
  rw [smul_add, ← mul_div_assoc', mul_comm, mul_smul, div_mul_comm, mul_smul],
  exact convex_iff_div.1 hs hcx hcy (le_of_lt cy_pos) (le_of_lt cx_pos) (add_pos cy_pos cx_pos)
end

-- Hide lemmas / definition for M. Riesz extension theorem into a namespace
namespace riesz_extension

/-- Induction step in M. Riesz extension theorem: given a convex cone `s` in `E × ℝ` such that
`s` meets every hyperplane `{(x, y) | y=const}` and a linear function `f : E → ℝ`
nonnegative on `s`, one can extend it to a linear function `g = f x + c * y` on `E × ℝ`
such that `g` is nonnegative on `s` as well.

The statement of this lemma closely reflects the mathematical meaning of the only nontrivial
step in the proof of M. Riesz extension theorem. The rest of the proof repacks this lemma
into a form suitable for our `zorn_partial_order` lemma.
 -/
lemma step' (s : convex_cone (E × ℝ))
  (hs : ∀ y : ℝ, ∃ x : E, (x, y) ∈ s)
  (f : E →ₗ[ℝ] ℝ) (hf : ∀ x : E, (x, (0:ℝ)) ∈ s → 0 ≤ f x) :
  ∃ c : ℝ, ∀ (x : E × ℝ) (hx : x ∈ s), 0 ≤ f x.1 + c * x.2 :=
begin
  obtain ⟨c, le_c, c_le⟩ : ∃ c, (∀ x, (-x, -(1:ℝ)) ∈ s → f x ≤ c) ∧ (∀ x, (x, (1:ℝ)) ∈ s → c ≤ f x),
  { set Sp := f '' {x : E | (x, (1:ℝ)) ∈ s},
    set Sn := f '' {x : E | (-x, -(1:ℝ)) ∈ s},
    suffices : (upper_bounds Sn ∩ lower_bounds Sp).nonempty,
      by simpa only [set.nonempty, upper_bounds, lower_bounds, ball_image_iff] using this,
    refine exists_between_of_forall_le (nonempty.image f _) (nonempty.image f (hs 1)) _,
    { rcases (hs (-1)) with ⟨x, hx⟩,
      rw [← neg_neg x] at hx,
      exact ⟨_, hx⟩ },
    rintros a ⟨xn, hxn, rfl⟩ b ⟨xp, hxp, rfl⟩,
    have := s.add_mem hxp hxn,
    rw [prod.mk_add_mk, add_neg_self] at this,
    replace := hf _ this,
    rwa [f.map_add, f.map_neg, ← sub_eq_add_neg, sub_nonneg] at this },
  use -c,
  rintros ⟨x, y⟩ hp,
  rw [← neg_mul_eq_neg_mul, ← sub_eq_add_neg, sub_nonneg, mul_comm],
  rcases lt_trichotomy 0 y with hy|hy|hy,
  { have : (y⁻¹ • x, (1:ℝ)) ∈ s,
      by rwa [← s.smul_mem_iff hy, prod.smul_mk, smul_smul, smul_eq_mul,
        mul_inv_cancel (ne_of_gt hy), one_smul, mul_one],
    replace := c_le _ this,
    rwa [← mul_le_mul_left hy, f.map_smul _, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel (ne_of_gt hy), one_mul] at this },
  { subst y,
    rw [zero_mul],
    exact hf x hp },
  { have : (-(y⁻¹ • x), (-1:ℝ)) ∈ s,
      by rwa [← s.smul_mem_iff (neg_pos.2 hy), prod.smul_mk, neg_smul, smul_neg, neg_smul, smul_neg,
        neg_neg, neg_neg, smul_smul, smul_eq_mul, mul_one, mul_inv_cancel (ne_of_lt hy), one_smul],
    replace := le_c _ this,
    rwa [← mul_le_mul_left (neg_pos.2 hy), f.map_smul _, smul_eq_mul, ← neg_mul_eq_neg_mul,
      ← neg_mul_eq_neg_mul, neg_le_neg_iff, ← mul_assoc, mul_inv_cancel (ne_of_lt hy), one_mul]
      at this }
end

/-- Induction step in M. Riesz extension theorem. This version says `g ∘ inl = f` instead
of `g (x, y) = f x + c * y`. -/
lemma step (s : convex_cone (E × ℝ))
  (hs : ∀ y : ℝ, ∃ x : E, (x, y) ∈ s)
  (f : E →ₗ[ℝ] ℝ) (hf : ∀ x : E, (x, (0:ℝ)) ∈ s → 0 ≤ f x) :
  ∃ g : E × ℝ →ₗ[ℝ] ℝ, g.comp (inl ℝ E ℝ) = f ∧ ∀ x ∈ s, 0 ≤ g x :=
let ⟨c, hc⟩ := step' s hs f hf in ⟨f.copair (c • 1), f.copair_inl _, hc⟩

open submodule

variables (s : convex_cone E) (p : linear_pmap ℝ E ℝ)

lemma step_pmap (hp_nonneg : ∀ x : p.domain, (x : E) ∈ s → 0 ≤ p x)
  (hp_dense : ∀ y, ∃ x : p.domain, (x : E) + y ∈ s) (hp : p.domain ≠ ⊤) :
  ∃ q, p < q ∧ ∀ x : q.domain, (x : E) ∈ s → 0 ≤ q x :=
begin
  rcases exists_of_lt (lt_top_iff_ne_top.2 hp) with ⟨y, hy', hy⟩, clear hy',
  set e := sup_span_singleton_equiv p.domain hy,
  set t := (s.comap $ (submodule.subtype $ p.domain ⊔ span ℝ {y}).comp $
    (e.symm : (p.domain × ℝ) →ₗ[ℝ] ↥(p.domain ⊔ span ℝ {y}))),
  have hst : ∀ {x : p.domain × ℝ}, x ∈ t ↔ (e.symm x : E) ∈ s,
    from λ x, by rw [convex_cone.mem_comap, comp_apply, linear_equiv.coe_apply, subtype_apply],
  obtain ⟨g, hgp, hgt⟩ := step t _ p.to_fun _,
  { refine ⟨⟨p.domain ⊔ span ℝ {y}, g.comp e⟩, lt_iff_le_not_le.2 ⟨⟨le_sup_left, _⟩, λ h, _⟩, _⟩,
    { intros x hxp hxsup,
      rw [linear_pmap.mk_apply, comp_apply, linear_equiv.coe_apply,
        sup_span_singleton_equiv_left, ← comp_apply, hgp, linear_pmap.to_fun_eq_coe],
      refl },
    { replace h : span ℝ {y} ≤ p.domain := le_trans le_sup_right h.left,
      exact hy (h $ subset_span $ mem_singleton y) },
    { intros x hxs,
      rcases e.symm.surjective x with ⟨x, rfl⟩,
      rw [linear_pmap.mk_apply, comp_apply, linear_equiv.coe_apply, e.apply_symm_apply],
      exact hgt _ (hst.mpr hxs) } },
  { intro c,
    obtain ⟨x, hx⟩ := hp_dense (c • y),
    use x,
    rwa [hst, sup_span_singleton_equiv_symm_apply] },
  { refine λ x hx, hp_nonneg _ _,
    rwa [hst, sup_span_singleton_equiv_symm_apply, zero_smul, add_zero] at hx }
end

@[nolint ge_or_gt]
theorem exists_top (p : linear_pmap ℝ E ℝ)
  (hp_nonneg : ∀ x : p.domain, (x : E) ∈ s → 0 ≤ p x)
  (hp_dense : ∀ y, ∃ x : p.domain, (x : E) + y ∈ s) :
  ∃ q ≥ p, q.domain = ⊤ ∧ ∀ x : q.domain, (x : E) ∈ s → 0 ≤ q x :=
begin
  replace hp_nonneg : p ∈ { p | _ }, by { rw mem_set_of_eq, exact hp_nonneg },
  obtain ⟨q, hqs, hpq, hq⟩ := zorn.zorn_partial_order₀ _ _ _ hp_nonneg,
  { refine ⟨q, hpq, _, hqs⟩,
    contrapose! hq,
    rcases step_pmap s q hqs _ hq with ⟨r, hqr, hr⟩,
    { exact ⟨r, hr, le_of_lt hqr, ne_of_gt hqr⟩ },
    { exact λ y, let ⟨x, hx⟩ := hp_dense y in ⟨of_le hpq.left x, hx⟩ } },
  { intros c hcs c_chain y hy,
    clear hp_nonneg hp_dense p,
    have cne : c.nonempty := ⟨y, hy⟩,
    rcases linear_pmap.chain_Sup_bound c c_chain.directed_on with ⟨f, hf⟩,
    refine ⟨⟨_, f⟩, _, hf⟩,
    rintros ⟨x, hx⟩ hxs,
    have hdir : directed_on (≤) (linear_pmap.domain '' c),
      from (directed_on_image _).2 (c_chain.directed_on.mono _ linear_pmap.domain_mono),
    rcases (mem_Sup_of_directed (cne.image _) hdir).1 hx with ⟨_, ⟨p, hpc, rfl⟩, hpx⟩,
    rw ← (hf hpc).right x hpx hx,
    apply hcs hpc,
    exact hxs }
end

end riesz_extension

theorem riesz_extension (s : convex_cone E) (p : submodule ℝ E) (f : p →ₗ[ℝ] ℝ)
  (nonneg : ∀ x : p, (x : E) ∈ s → 0 ≤ f x) (dense : ∀ y, ∃ x : p, (x : E) + y ∈ s) :
  ∃ g : E →ₗ[ℝ] ℝ, (∀ x : p, f x = g x) ∧ (∀ x ∈ s, 0 ≤ g x) :=
begin
  rcases riesz_extension.exists_top s ⟨p, f⟩ nonneg dense with ⟨⟨g_dom, g⟩, ⟨hpg, hfg⟩, htop, hgs⟩,
  clear hpg,
  dsimp at hfg hgs htop ⊢,
  refine ⟨g.comp (linear_equiv.of_top _ htop).symm, _, _⟩;
    simp only [comp_apply, linear_equiv.coe_apply, linear_equiv.of_top_symm_apply],
  { exact λ ⟨x, hx⟩, hfg _ _ _ },
  { intros x hx,
    apply hgs,
    exact hx }
end
