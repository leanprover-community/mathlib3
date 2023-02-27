/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov
-/
import group_theory.quotient_group
import linear_algebra.span

/-!
# Quotients by submodules

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

* If `p` is a submodule of `M`, `M ⧸ p` is the quotient of `M` with respect to `p`:
  that is, elements of `M` are identified if their difference is in `p`. This is itself a module.

-/

-- For most of this file we work over a noncommutative ring
section ring

namespace submodule

variables {R M : Type*} {r : R} {x y : M} [ring R] [add_comm_group M] [module R M]
variables (p p' : submodule R M)

open linear_map quotient_add_group

/-- The equivalence relation associated to a submodule `p`, defined by `x ≈ y` iff `-x + y ∈ p`.

Note this is equivalent to `y - x ∈ p`, but defined this way to be be defeq to the `add_subgroup`
version, where commutativity can't be assumed. -/
def quotient_rel : setoid M :=
quotient_add_group.left_rel p.to_add_subgroup

lemma quotient_rel_r_def {x y : M} : @setoid.r _ (p.quotient_rel) x y ↔ x - y ∈ p :=
iff.trans (by { rw [left_rel_apply, sub_eq_add_neg, neg_add, neg_neg], refl }) neg_mem_iff

/-- The quotient of a module `M` by a submodule `p ⊆ M`. -/
instance has_quotient : has_quotient M (submodule R M) := ⟨λ p, quotient (quotient_rel p)⟩

namespace quotient

/-- Map associating to an element of `M` the corresponding element of `M/p`,
when `p` is a submodule of `M`. -/
def mk {p : submodule R M} : M → M ⧸ p := quotient.mk'

@[simp] theorem mk_eq_mk {p : submodule R M} (x : M) :
  (@_root_.quotient.mk _ (quotient_rel p) x) = mk x := rfl
@[simp] theorem mk'_eq_mk {p : submodule R M} (x : M) : (quotient.mk' x : M ⧸ p) = mk x := rfl
@[simp] theorem quot_mk_eq_mk {p : submodule R M} (x : M) : (quot.mk _ x : M ⧸ p) = mk x := rfl

protected theorem eq' {x y : M} : (mk x : M ⧸ p) = mk y ↔ -x + y ∈ p := quotient_add_group.eq

protected theorem eq {x y : M} : (mk x : M ⧸ p) = mk y ↔ x - y ∈ p :=
(p^.quotient.eq').trans (left_rel_apply.symm.trans p.quotient_rel_r_def)

instance : has_zero (M ⧸ p) := ⟨mk 0⟩
instance : inhabited (M ⧸ p) := ⟨0⟩

@[simp] theorem mk_zero : mk 0 = (0 : M ⧸ p) := rfl

@[simp] theorem mk_eq_zero : (mk x : M ⧸ p) = 0 ↔ x ∈ p :=
by simpa using (quotient.eq p : mk x = 0 ↔ _)

instance add_comm_group : add_comm_group (M ⧸ p) :=
quotient_add_group.quotient.add_comm_group p.to_add_subgroup

@[simp] theorem mk_add : (mk (x + y) : M ⧸ p) = mk x + mk y := rfl

@[simp] theorem mk_neg : (mk (-x) : M ⧸ p) = -mk x := rfl

@[simp] theorem mk_sub : (mk (x - y) : M ⧸ p) = mk x - mk y := rfl

section has_smul

variables {S : Type*} [has_smul S R] [has_smul S M] [is_scalar_tower S R M] (P : submodule R M)

instance has_smul' : has_smul S (M ⧸ P) :=
⟨λ a, quotient.map' ((•) a) $ λ x y h, left_rel_apply.mpr $
  by simpa [smul_sub] using P.smul_mem (a • 1 : R) (left_rel_apply.mp h)⟩

/-- Shortcut to help the elaborator in the common case. -/
instance has_smul : has_smul R (M ⧸ P) :=
quotient.has_smul' P

@[simp] theorem mk_smul (r : S) (x : M) : (mk (r • x) : M ⧸ p) = r • mk x := rfl

instance smul_comm_class (T : Type*) [has_smul T R] [has_smul T M] [is_scalar_tower T R M]
  [smul_comm_class S T M] : smul_comm_class S T (M ⧸ P) :=
{ smul_comm := λ x y, quotient.ind' $ by exact λ z, congr_arg mk (smul_comm _ _ _) }

instance is_scalar_tower (T : Type*) [has_smul T R] [has_smul T M] [is_scalar_tower T R M]
  [has_smul S T] [is_scalar_tower S T M] : is_scalar_tower S T (M ⧸ P) :=
{ smul_assoc := λ x y, quotient.ind' $ by exact λ z, congr_arg mk (smul_assoc _ _ _) }

instance is_central_scalar [has_smul Sᵐᵒᵖ R] [has_smul Sᵐᵒᵖ M] [is_scalar_tower Sᵐᵒᵖ R M]
  [is_central_scalar S M] : is_central_scalar S (M ⧸ P) :=
{ op_smul_eq_smul := λ x, quotient.ind' $ by exact λ z, congr_arg mk $ op_smul_eq_smul _ _ }

end has_smul

section module

variables {S : Type*}

instance mul_action' [monoid S] [has_smul S R] [mul_action S M] [is_scalar_tower S R M]
  (P : submodule R M) : mul_action S (M ⧸ P) :=
function.surjective.mul_action mk (surjective_quot_mk _) P^.quotient.mk_smul

instance mul_action (P : submodule R M) : mul_action R (M ⧸ P) :=
quotient.mul_action' P

instance smul_zero_class' [has_smul S R] [smul_zero_class S M]
  [is_scalar_tower S R M]
  (P : submodule R M) : smul_zero_class S (M ⧸ P) :=
zero_hom.smul_zero_class ⟨mk, mk_zero _⟩ P^.quotient.mk_smul

instance smul_zero_class (P : submodule R M) : smul_zero_class R (M ⧸ P) :=
quotient.smul_zero_class' P

instance distrib_smul' [has_smul S R] [distrib_smul S M]
  [is_scalar_tower S R M]
  (P : submodule R M) : distrib_smul S (M ⧸ P) :=
function.surjective.distrib_smul
  ⟨mk, rfl, λ _ _, rfl⟩ (surjective_quot_mk _) P^.quotient.mk_smul

instance distrib_smul (P : submodule R M) : distrib_smul R (M ⧸ P) :=
quotient.distrib_smul' P

instance distrib_mul_action' [monoid S] [has_smul S R] [distrib_mul_action S M]
  [is_scalar_tower S R M]
  (P : submodule R M) : distrib_mul_action S (M ⧸ P) :=
function.surjective.distrib_mul_action
  ⟨mk, rfl, λ _ _, rfl⟩ (surjective_quot_mk _) P^.quotient.mk_smul

instance distrib_mul_action (P : submodule R M) : distrib_mul_action R (M ⧸ P) :=
quotient.distrib_mul_action' P

instance module' [semiring S] [has_smul S R] [module S M] [is_scalar_tower S R M]
  (P : submodule R M) : module S (M ⧸ P) :=
function.surjective.module _
  ⟨mk, rfl, λ _ _, rfl⟩ (surjective_quot_mk _) P^.quotient.mk_smul

instance module (P : submodule R M) : module R (M ⧸ P) :=
quotient.module' P

variables (S)

/-- The quotient of `P` as an `S`-submodule is the same as the quotient of `P` as an `R`-submodule,
where `P : submodule R M`.
-/
def restrict_scalars_equiv [ring S] [has_smul S R] [module S M] [is_scalar_tower S R M]
  (P : submodule R M) :
  (M ⧸ P.restrict_scalars S) ≃ₗ[S] M ⧸ P :=
{ map_add' := λ x y, quotient.induction_on₂' x y (λ x' y', rfl),
  map_smul' := λ c x, quotient.induction_on' x (λ x', rfl),
  ..quotient.congr_right $ λ _ _, iff.rfl }

@[simp] lemma restrict_scalars_equiv_mk
  [ring S] [has_smul S R] [module S M] [is_scalar_tower S R M] (P : submodule R M)
  (x : M) : restrict_scalars_equiv S P (mk x) = mk x :=
rfl

@[simp] lemma restrict_scalars_equiv_symm_mk
  [ring S] [has_smul S R] [module S M] [is_scalar_tower S R M] (P : submodule R M)
  (x : M) : (restrict_scalars_equiv S P).symm (mk x) = mk x :=
rfl


end module

lemma mk_surjective : function.surjective (@mk _ _ _ _ _ p) :=
by { rintros ⟨x⟩, exact ⟨x, rfl⟩ }

lemma nontrivial_of_lt_top (h : p < ⊤) : nontrivial (M ⧸ p) :=
begin
  obtain ⟨x, _, not_mem_s⟩ := set_like.exists_of_lt h,
  refine ⟨⟨mk x, 0, _⟩⟩,
  simpa using not_mem_s
end

end quotient

instance quotient_bot.infinite [infinite M] : infinite (M ⧸ (⊥ : submodule R M)) :=
infinite.of_injective submodule.quotient.mk $ λ x y h, sub_eq_zero.mp $
  (submodule.quotient.eq ⊥).mp h

instance quotient_top.unique : unique (M ⧸ (⊤ : submodule R M)) :=
{ default := 0,
  uniq := λ x, quotient.induction_on' x $ λ x, (submodule.quotient.eq ⊤).mpr submodule.mem_top }

instance quotient_top.fintype : fintype (M ⧸ (⊤ : submodule R M)) :=
fintype.of_subsingleton 0

variables {p}

lemma subsingleton_quotient_iff_eq_top : subsingleton (M ⧸ p) ↔ p = ⊤ :=
begin
  split,
  { rintro h,
    refine eq_top_iff.mpr (λ x _, _),
    have this : x - 0 ∈ p := (submodule.quotient.eq p).mp (by exactI subsingleton.elim _ _),
    rwa sub_zero at this },
  { rintro rfl,
    apply_instance }
end

lemma unique_quotient_iff_eq_top : nonempty (unique (M ⧸ p)) ↔ p = ⊤ :=
⟨λ ⟨h⟩, subsingleton_quotient_iff_eq_top.mp (@@unique.subsingleton h),
 by { rintro rfl, exact ⟨quotient_top.unique⟩ }⟩

variables (p)

noncomputable instance quotient.fintype [fintype M] (S : submodule R M) :
  fintype (M ⧸ S) :=
@@quotient.fintype _ _ (λ _ _, classical.dec _)

lemma card_eq_card_quotient_mul_card [fintype M] (S : submodule R M) [decidable_pred (∈ S)]  :
  fintype.card M = fintype.card S * fintype.card (M ⧸ S) :=
by { rw [mul_comm, ← fintype.card_prod],
     exact fintype.card_congr add_subgroup.add_group_equiv_quotient_times_add_subgroup }

section

variables {M₂ : Type*} [add_comm_group M₂] [module R M₂]

lemma quot_hom_ext ⦃f g : M ⧸ p →ₗ[R] M₂⦄ (h : ∀ x, f (quotient.mk x) = g (quotient.mk x)) :
  f = g :=
linear_map.ext $ λ x, quotient.induction_on' x h

/-- The map from a module `M` to the quotient of `M` by a submodule `p` as a linear map. -/
def mkq : M →ₗ[R] M ⧸ p :=
{ to_fun := quotient.mk, map_add' := by simp, map_smul' := by simp }

@[simp] theorem mkq_apply (x : M) : p.mkq x = quotient.mk x := rfl

lemma mkq_surjective (A : submodule R M) : function.surjective A.mkq :=
by rintro ⟨x⟩; exact ⟨x, rfl⟩

end

variables {R₂ M₂ : Type*} [ring R₂] [add_comm_group M₂] [module R₂ M₂] {τ₁₂ : R →+* R₂}

/-- Two `linear_map`s from a quotient module are equal if their compositions with
`submodule.mkq` are equal.

See note [partially-applied ext lemmas]. -/
@[ext]
lemma linear_map_qext ⦃f g : M ⧸ p →ₛₗ[τ₁₂] M₂⦄ (h : f.comp p.mkq = g.comp p.mkq) : f = g :=
linear_map.ext $ λ x, quotient.induction_on' x $ (linear_map.congr_fun h : _)

/-- The map from the quotient of `M` by a submodule `p` to `M₂` induced by a linear map `f : M → M₂`
vanishing on `p`, as a linear map. -/
def liftq (f : M →ₛₗ[τ₁₂] M₂) (h : p ≤ f.ker) : M ⧸ p →ₛₗ[τ₁₂] M₂ :=
{ map_smul' := by rintro a ⟨x⟩; exact f.map_smulₛₗ a x,
  ..quotient_add_group.lift p.to_add_subgroup f.to_add_monoid_hom h }

@[simp] theorem liftq_apply (f : M →ₛₗ[τ₁₂] M₂) {h} (x : M) :
  p.liftq f h (quotient.mk x) = f x := rfl

@[simp] theorem liftq_mkq (f : M →ₛₗ[τ₁₂] M₂) (h) : (p.liftq f h).comp p.mkq = f :=
by ext; refl

/--Special case of `liftq` when `p` is the span of `x`. In this case, the condition on `f` simply
becomes vanishing at `x`.-/
def liftq_span_singleton (x : M) (f : M →ₛₗ[τ₁₂] M₂) (h : f x = 0) : (M ⧸ R ∙ x) →ₛₗ[τ₁₂] M₂ :=
(R ∙ x).liftq f $ by rw [span_singleton_le_iff_mem, linear_map.mem_ker, h]

@[simp] lemma liftq_span_singleton_apply (x : M) (f : M →ₛₗ[τ₁₂] M₂) (h : f x = 0) (y : M) :
liftq_span_singleton x f h (quotient.mk y) = f y := rfl

@[simp] theorem range_mkq : p.mkq.range = ⊤ :=
eq_top_iff'.2 $ by rintro ⟨x⟩; exact ⟨x, rfl⟩

@[simp] theorem ker_mkq : p.mkq.ker = p :=
by ext; simp

lemma le_comap_mkq (p' : submodule R (M ⧸ p)) : p ≤ comap p.mkq p' :=
by simpa using (comap_mono bot_le : p.mkq.ker ≤ comap p.mkq p')

@[simp] theorem mkq_map_self : map p.mkq p = ⊥ :=
by rw [eq_bot_iff, map_le_iff_le_comap, comap_bot, ker_mkq]; exact le_rfl

@[simp] theorem comap_map_mkq : comap p.mkq (map p.mkq p') = p ⊔ p' :=
by simp [comap_map_eq, sup_comm]

@[simp] theorem map_mkq_eq_top : map p.mkq p' = ⊤ ↔ p ⊔ p' = ⊤ :=
by simp only [map_eq_top_iff p.range_mkq, sup_comm, ker_mkq]

variables (q : submodule R₂ M₂)

/-- The map from the quotient of `M` by submodule `p` to the quotient of `M₂` by submodule `q` along
`f : M → M₂` is linear. -/
def mapq (f : M →ₛₗ[τ₁₂] M₂) (h : p ≤ comap f q) :
  (M ⧸ p) →ₛₗ[τ₁₂] (M₂ ⧸ q) :=
p.liftq (q.mkq.comp f) $ by simpa [ker_comp] using h

@[simp] theorem mapq_apply (f : M →ₛₗ[τ₁₂] M₂) {h} (x : M) :
  mapq p q f h (quotient.mk x) = quotient.mk (f x) := rfl

theorem mapq_mkq (f : M →ₛₗ[τ₁₂] M₂) {h} : (mapq p q f h).comp p.mkq = q.mkq.comp f :=
by ext x; refl

@[simp] lemma mapq_zero (h : p ≤ q.comap (0 : M →ₛₗ[τ₁₂] M₂) := by simp) :
  p.mapq q (0 : M →ₛₗ[τ₁₂] M₂) h = 0 :=
by { ext, simp, }

/-- Given submodules `p ⊆ M`, `p₂ ⊆ M₂`, `p₃ ⊆ M₃` and maps `f : M → M₂`, `g : M₂ → M₃` inducing
`mapq f : M ⧸ p → M₂ ⧸ p₂` and `mapq g : M₂ ⧸ p₂ → M₃ ⧸ p₃` then
`mapq (g ∘ f) = (mapq g) ∘ (mapq f)`. -/
lemma mapq_comp {R₃ M₃ : Type*} [ring R₃] [add_comm_group M₃] [module R₃ M₃]
  (p₂ : submodule R₂ M₂) (p₃ : submodule R₃ M₃)
  {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃} [ring_hom_comp_triple τ₁₂ τ₂₃ τ₁₃]
  (f : M →ₛₗ[τ₁₂] M₂) (g : M₂ →ₛₗ[τ₂₃] M₃) (hf : p ≤ p₂.comap f) (hg : p₂ ≤ p₃.comap g)
  (h := (hf.trans (comap_mono hg))) :
  p.mapq p₃ (g.comp f) h = (p₂.mapq p₃ g hg).comp (p.mapq p₂ f hf) :=
by { ext, simp, }

@[simp] lemma mapq_id (h : p ≤ p.comap linear_map.id := by { rw comap_id, exact le_refl _ }) :
  p.mapq p linear_map.id h = linear_map.id :=
by { ext, simp, }

lemma mapq_pow {f : M →ₗ[R] M} (h : p ≤ p.comap f) (k : ℕ)
  (h' : p ≤ p.comap (f^k) := p.le_comap_pow_of_le_comap h k) :
  p.mapq p (f^k) h' = (p.mapq p f h)^k :=
begin
  induction k with k ih,
  { simp [linear_map.one_eq_id], },
  { simp only [linear_map.iterate_succ, ← ih],
    apply p.mapq_comp, },
end

theorem comap_liftq (f : M →ₛₗ[τ₁₂] M₂) (h) :
  q.comap (p.liftq f h) = (q.comap f).map (mkq p) :=
le_antisymm
  (by rintro ⟨x⟩ hx; exact ⟨_, hx, rfl⟩)
  (by rw [map_le_iff_le_comap, ← comap_comp, liftq_mkq]; exact le_rfl)

theorem map_liftq [ring_hom_surjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) (h) (q : submodule R (M ⧸ p)) :
  q.map (p.liftq f h) = (q.comap p.mkq).map f :=
le_antisymm
  (by rintro _ ⟨⟨x⟩, hxq, rfl⟩; exact ⟨x, hxq, rfl⟩)
  (by rintro _ ⟨x, hxq, rfl⟩; exact ⟨quotient.mk x, hxq, rfl⟩)

theorem ker_liftq (f : M →ₛₗ[τ₁₂] M₂) (h) :
  ker (p.liftq f h) = (ker f).map (mkq p) := comap_liftq _ _ _ _

theorem range_liftq [ring_hom_surjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) (h) :
  range (p.liftq f h) = range f :=
by simpa only [range_eq_map] using map_liftq _ _ _ _

theorem ker_liftq_eq_bot (f : M →ₛₗ[τ₁₂] M₂) (h) (h' : ker f ≤ p) : ker (p.liftq f h) = ⊥ :=
by rw [ker_liftq, le_antisymm h h', mkq_map_self]

/-- The correspondence theorem for modules: there is an order isomorphism between submodules of the
quotient of `M` by `p`, and submodules of `M` larger than `p`. -/
def comap_mkq.rel_iso :
  submodule R (M ⧸ p) ≃o {p' : submodule R M // p ≤ p'} :=
{ to_fun    := λ p', ⟨comap p.mkq p', le_comap_mkq p _⟩,
  inv_fun   := λ q, map p.mkq q,
  left_inv  := λ p', map_comap_eq_self $ by simp,
  right_inv := λ ⟨q, hq⟩, subtype.ext_val $ by simpa [comap_map_mkq p],
  map_rel_iff'      := λ p₁ p₂, comap_le_comap_iff $ range_mkq _ }

/-- The ordering on submodules of the quotient of `M` by `p` embeds into the ordering on submodules
of `M`. -/
def comap_mkq.order_embedding :
  submodule R (M ⧸ p) ↪o submodule R M :=
(rel_iso.to_rel_embedding $ comap_mkq.rel_iso p).trans (subtype.rel_embedding _ _)

@[simp] lemma comap_mkq_embedding_eq (p' : submodule R (M ⧸ p)) :
  comap_mkq.order_embedding p p' = comap p.mkq p' := rfl

lemma span_preimage_eq [ring_hom_surjective τ₁₂] {f : M →ₛₗ[τ₁₂] M₂} {s : set M₂} (h₀ : s.nonempty)
  (h₁ : s ⊆ range f) :
  span R (f ⁻¹' s) = (span R₂ s).comap f :=
begin
  suffices : (span R₂ s).comap f ≤ span R (f ⁻¹' s),
  { exact le_antisymm (span_preimage_le f s) this, },
  have hk : ker f ≤ span R (f ⁻¹' s),
  { let y := classical.some h₀, have hy : y ∈ s, { exact classical.some_spec h₀, },
    rw ker_le_iff, use [y, h₁ hy], rw ← set.singleton_subset_iff at hy,
    exact set.subset.trans subset_span (span_mono (set.preimage_mono hy)), },
  rw ← left_eq_sup at hk, rw f.range_coe at h₁,
  rw [hk, ←linear_map.map_le_map_iff, map_span, map_comap_eq, set.image_preimage_eq_of_subset h₁],
  exact inf_le_right,
end

/-- If `P` is a submodule of `M` and `Q` a submodule of `N`,
and `f : M ≃ₗ N` maps `P` to `Q`, then `M ⧸ P` is equivalent to `N ⧸ Q`. -/
@[simps] def quotient.equiv {N : Type*} [add_comm_group N] [module R N]
  (P : submodule R M) (Q : submodule R N)
  (f : M ≃ₗ[R] N) (hf : P.map f = Q) : (M ⧸ P) ≃ₗ[R] N ⧸ Q :=
{ to_fun := P.mapq Q (f : M →ₗ[R] N) (λ x hx, hf ▸ submodule.mem_map_of_mem hx),
  inv_fun := Q.mapq P (f.symm : N →ₗ[R] M) (λ x hx, begin
    rw [← hf, submodule.mem_map] at hx,
    obtain ⟨y, hy, rfl⟩ := hx,
    simpa
  end),
  left_inv := λ x, quotient.induction_on' x (by simp),
  right_inv := λ x, quotient.induction_on' x (by simp),
  .. P.mapq Q (f : M →ₗ[R] N) (λ x hx, hf ▸ submodule.mem_map_of_mem hx) }

@[simp] lemma quotient.equiv_symm {R M N : Type*} [comm_ring R]
  [add_comm_group M] [module R M] [add_comm_group N] [module R N]
  (P : submodule R M) (Q : submodule R N)
  (f : M ≃ₗ[R] N) (hf : P.map f = Q) :
  (quotient.equiv P Q f hf).symm =
    quotient.equiv Q P f.symm ((submodule.map_symm_eq_iff f).mpr hf) :=
rfl

@[simp] lemma quotient.equiv_trans {N O : Type*} [add_comm_group N] [module R N]
  [add_comm_group O] [module R O]
  (P : submodule R M) (Q : submodule R N) (S : submodule R O)
  (e : M ≃ₗ[R] N) (f : N ≃ₗ[R] O)
  (he : P.map e = Q) (hf : Q.map f = S) (hef : P.map (e.trans f) = S) :
  quotient.equiv P S (e.trans f) hef = (quotient.equiv P Q e he).trans (quotient.equiv Q S f hf) :=
begin
  ext,
  -- `simp` can deal with `hef` depending on `e` and `f`
  simp only [quotient.equiv_apply, linear_equiv.trans_apply, linear_equiv.coe_trans],
  -- `rw` can deal with `mapq_comp` needing extra hypotheses coming from the RHS
  rw [mapq_comp, linear_map.comp_apply]
end

end submodule

open submodule

namespace linear_map

section ring

variables {R M R₂ M₂ R₃ M₃ : Type*}
variables [ring R] [ring R₂] [ring R₃]
variables [add_comm_monoid M] [add_comm_group M₂] [add_comm_monoid M₃]
variables [module R M] [module R₂ M₂] [module R₃ M₃]
variables {τ₁₂ : R →+* R₂} {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃}
variables [ring_hom_comp_triple τ₁₂ τ₂₃ τ₁₃] [ring_hom_surjective τ₁₂]

lemma range_mkq_comp (f : M →ₛₗ[τ₁₂] M₂) : f.range.mkq.comp f = 0 :=
linear_map.ext $ λ x, by simp

lemma ker_le_range_iff {f : M →ₛₗ[τ₁₂] M₂} {g : M₂ →ₛₗ[τ₂₃] M₃} :
  g.ker ≤ f.range ↔ f.range.mkq.comp g.ker.subtype = 0 :=
by rw [←range_le_ker_iff, submodule.ker_mkq, submodule.range_subtype]

/-- An epimorphism is surjective. -/
lemma range_eq_top_of_cancel {f : M →ₛₗ[τ₁₂] M₂}
  (h : ∀ (u v : M₂ →ₗ[R₂] M₂ ⧸ f.range), u.comp f = v.comp f → u = v) : f.range = ⊤ :=
begin
  have h₁ : (0 : M₂ →ₗ[R₂] M₂ ⧸ f.range).comp f = 0 := zero_comp _,
  rw [←submodule.ker_mkq f.range, ←h 0 f.range.mkq (eq.trans h₁ (range_mkq_comp _).symm)],
  exact ker_zero
end

end ring

end linear_map

open linear_map

namespace submodule

variables {R M : Type*} {r : R} {x y : M} [ring R] [add_comm_group M] [module R M]
variables (p p' : submodule R M)

/-- If `p = ⊥`, then `M / p ≃ₗ[R] M`. -/
def quot_equiv_of_eq_bot (hp : p = ⊥) : (M ⧸ p) ≃ₗ[R] M :=
linear_equiv.of_linear (p.liftq id $ hp.symm ▸ bot_le) p.mkq (liftq_mkq _ _ _) $
  p.quot_hom_ext $ λ x, rfl

@[simp] lemma quot_equiv_of_eq_bot_apply_mk (hp : p = ⊥) (x : M) :
  p.quot_equiv_of_eq_bot hp (quotient.mk x) = x := rfl

@[simp] lemma quot_equiv_of_eq_bot_symm_apply (hp : p = ⊥) (x : M) :
  (p.quot_equiv_of_eq_bot hp).symm x = quotient.mk x := rfl

@[simp] lemma coe_quot_equiv_of_eq_bot_symm (hp : p = ⊥) :
  ((p.quot_equiv_of_eq_bot hp).symm : M →ₗ[R] M ⧸ p) = p.mkq := rfl

/-- Quotienting by equal submodules gives linearly equivalent quotients. -/
def quot_equiv_of_eq (h : p = p') : (M ⧸ p) ≃ₗ[R] M ⧸ p' :=
{ map_add' := by { rintros ⟨x⟩ ⟨y⟩, refl }, map_smul' := by { rintros x ⟨y⟩, refl },
  ..@quotient.congr _ _ (quotient_rel p) (quotient_rel p') (equiv.refl _) $
    λ a b, by { subst h, refl } }

@[simp]
lemma quot_equiv_of_eq_mk (h : p = p') (x : M) :
  submodule.quot_equiv_of_eq p p' h (submodule.quotient.mk x) = submodule.quotient.mk x :=
rfl

@[simp] lemma quotient.equiv_refl (P : submodule R M) (Q : submodule R M)
  (hf : P.map (linear_equiv.refl R M : M →ₗ[R] M) = Q) :
  quotient.equiv P Q (linear_equiv.refl R M) hf = quot_equiv_of_eq _ _ (by simpa using hf) :=
rfl

end submodule

end ring

section comm_ring

variables {R M M₂ : Type*} {r : R} {x y : M} [comm_ring R]
  [add_comm_group M] [module R M] [add_comm_group M₂] [module R M₂]
  (p : submodule R M) (q : submodule R M₂)

namespace submodule

/-- Given modules `M`, `M₂` over a commutative ring, together with submodules `p ⊆ M`, `q ⊆ M₂`,
the natural map $\{f ∈ Hom(M, M₂) | f(p) ⊆ q \} \to Hom(M/p, M₂/q)$ is linear. -/
def mapq_linear : compatible_maps p q →ₗ[R] (M ⧸ p) →ₗ[R] (M₂ ⧸ q) :=
{ to_fun    := λ f, mapq _ _ f.val f.property,
  map_add'  := λ x y, by { ext, refl, },
  map_smul' := λ c f, by { ext, refl, } }

end submodule

end comm_ring
