/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov
-/
import linear_algebra.basic

/-!
# Quotients by submodules

* If `p` is a submodule of `M`, `submodule.quotient p` is the quotient of `M` with respect to `p`:
  that is, elements of `M` are identified if their difference is in `p`. This is itself a module.

-/

-- For most of this file we work over a noncommutative ring
section ring

namespace submodule

variables {R M : Type*} {r : R} {x y : M} [ring R] [add_comm_group M] [module R M]
variables (p p' : submodule R M)

open linear_map

-- TODO(Mario): Factor through add_subgroup
/-- The equivalence relation associated to a submodule `p`, defined by `x ≈ y` iff `y - x ∈ p`. -/
def quotient_rel : setoid M :=
⟨λ x y, x - y ∈ p, λ x, by simp,
 λ x y h, by simpa using neg_mem _ h,
 λ x y z h₁ h₂, by simpa [sub_eq_add_neg, add_left_comm, add_assoc] using add_mem _ h₁ h₂⟩

/-- The quotient of a module `M` by a submodule `p ⊆ M`. -/
def quotient : Type* := quotient (quotient_rel p)

namespace quotient

/-- Map associating to an element of `M` the corresponding element of `M/p`,
when `p` is a submodule of `M`. -/
def mk {p : submodule R M} : M → quotient p := quotient.mk'

@[simp] theorem mk_eq_mk {p : submodule R M} (x : M) :
  (@_root_.quotient.mk _ (quotient_rel p) x) = mk x := rfl
@[simp] theorem mk'_eq_mk {p : submodule R M} (x : M) : (quotient.mk' x : quotient p) = mk x := rfl
@[simp] theorem quot_mk_eq_mk {p : submodule R M} (x : M) : (quot.mk _ x : quotient p) = mk x := rfl

protected theorem eq {x y : M} : (mk x : quotient p) = mk y ↔ x - y ∈ p := quotient.eq'

instance : has_zero (quotient p) := ⟨mk 0⟩
instance : inhabited (quotient p) := ⟨0⟩

@[simp] theorem mk_zero : mk 0 = (0 : quotient p) := rfl

@[simp] theorem mk_eq_zero : (mk x : quotient p) = 0 ↔ x ∈ p :=
by simpa using (quotient.eq p : mk x = 0 ↔ _)

instance : has_add (quotient p) :=
⟨λ a b, quotient.lift_on₂' a b (λ a b, mk (a + b)) $
  λ a₁ a₂ b₁ b₂ h₁ h₂, (quotient.eq p).2 $
    by simpa [sub_eq_add_neg, add_left_comm, add_comm] using add_mem p h₁ h₂⟩

@[simp] theorem mk_add : (mk (x + y) : quotient p) = mk x + mk y := rfl

instance : has_neg (quotient p) :=
⟨λ a, quotient.lift_on' a (λ a, mk (-a)) $
 λ a b h, (quotient.eq p).2 $ by simpa using neg_mem p h⟩

@[simp] theorem mk_neg : (mk (-x) : quotient p) = -mk x := rfl

instance : has_sub (quotient p) :=
⟨λ a b, quotient.lift_on₂' a b (λ a b, mk (a - b)) $
  λ a₁ a₂ b₁ b₂ h₁ h₂, (quotient.eq p).2 $
  by simpa [sub_eq_add_neg, add_left_comm, add_comm] using add_mem p h₁ (neg_mem p h₂)⟩

@[simp] theorem mk_sub : (mk (x - y) : quotient p) = mk x - mk y := rfl

instance : add_comm_group (quotient p) :=
{ zero := (0 : quotient p),
  add := (+),
  neg := has_neg.neg,
  sub := has_sub.sub,
  add_assoc := by { rintros ⟨x⟩ ⟨y⟩ ⟨z⟩, simp only [←mk_add p, quot_mk_eq_mk, add_assoc] },
  zero_add := by { rintro ⟨x⟩, simp only [←mk_zero p, ←mk_add p, quot_mk_eq_mk, zero_add] },
  add_zero := by { rintro ⟨x⟩, simp only [←mk_zero p, ←mk_add p, add_zero, quot_mk_eq_mk] },
  add_comm := by { rintros ⟨x⟩ ⟨y⟩, simp only [←mk_add p, quot_mk_eq_mk, add_comm] },
  add_left_neg := by { rintro ⟨x⟩,
    simp only [←mk_zero p, ←mk_add p, ←mk_neg p, quot_mk_eq_mk, add_left_neg] },
  sub_eq_add_neg := by { rintros ⟨x⟩ ⟨y⟩,
    simp only [←mk_add p, ←mk_neg p, ←mk_sub p, sub_eq_add_neg, quot_mk_eq_mk] },
  nsmul := λ n x, quotient.lift_on' x (λ x, mk (n • x)) $
     λ x y h, (quotient.eq p).2 $ by simpa [smul_sub] using smul_of_tower_mem p n h,
  nsmul_zero' := by { rintros ⟨⟩, simp only [mk_zero, quot_mk_eq_mk, zero_smul], refl },
  nsmul_succ' := by { rintros n ⟨⟩,
    simp only [nat.succ_eq_one_add, add_nsmul, mk_add, quot_mk_eq_mk, one_nsmul], refl },
  gsmul := λ n x, quotient.lift_on' x (λ x, mk (n • x)) $
     λ x y h, (quotient.eq p).2 $ by simpa [smul_sub] using smul_of_tower_mem p n h,
  gsmul_zero' := by { rintros ⟨⟩, simp only [mk_zero, quot_mk_eq_mk, zero_smul], refl },
  gsmul_succ' := by { rintros n ⟨⟩,
    simp [nat.succ_eq_add_one, add_nsmul, mk_add, quot_mk_eq_mk, one_nsmul, add_smul, add_comm],
    refl },
  gsmul_neg' := by { rintros n ⟨x⟩, simp_rw [gsmul_neg_succ_of_nat, gsmul_coe_nat], refl }, }

instance : has_scalar R (quotient p) :=
⟨λ a x, quotient.lift_on' x (λ x, mk (a • x)) $
 λ x y h, (quotient.eq p).2 $ by simpa [smul_sub] using smul_mem p a h⟩

@[simp] theorem mk_smul : (mk (r • x) : quotient p) = r • mk x := rfl

@[simp] theorem mk_nsmul (n : ℕ) : (mk (n • x) : quotient p) = n • mk x := rfl

instance : module R (quotient p) :=
module.of_core $ by refine {smul := (•), ..};
  repeat {rintro ⟨⟩ <|> intro}; simp [smul_add, add_smul, smul_smul,
    -mk_add, (mk_add p).symm, -mk_smul, (mk_smul p).symm]

lemma mk_surjective : function.surjective (@mk _ _ _ _ _ p) :=
by { rintros ⟨x⟩, exact ⟨x, rfl⟩ }

lemma nontrivial_of_lt_top (h : p < ⊤) : nontrivial (p.quotient) :=
begin
  obtain ⟨x, _, not_mem_s⟩ := set_like.exists_of_lt h,
  refine ⟨⟨mk x, 0, _⟩⟩,
  simpa using not_mem_s
end

end quotient

section

variables {M₂ : Type*} [add_comm_group M₂] [module R M₂]

lemma quot_hom_ext ⦃f g : quotient p →ₗ[R] M₂⦄ (h : ∀ x, f (quotient.mk x) = g (quotient.mk x)) :
  f = g :=
linear_map.ext $ λ x, quotient.induction_on' x h

/-- The map from a module `M` to the quotient of `M` by a submodule `p` as a linear map. -/
def mkq : M →ₗ[R] p.quotient :=
{ to_fun := quotient.mk, map_add' := by simp, map_smul' := by simp }

@[simp] theorem mkq_apply (x : M) : p.mkq x = quotient.mk x := rfl

end

variables {R₂ M₂ : Type*} [ring R₂] [add_comm_group M₂] [module R₂ M₂] {τ₁₂ : R →+* R₂}

/-- Two `linear_map`s from a quotient module are equal if their compositions with
`submodule.mkq` are equal.

See note [partially-applied ext lemmas]. -/
@[ext]
lemma linear_map_qext ⦃f g : p.quotient →ₛₗ[τ₁₂] M₂⦄ (h : f.comp p.mkq = g.comp p.mkq) : f = g :=
linear_map.ext $ λ x, quotient.induction_on' x $ (linear_map.congr_fun h : _)

/-- The map from the quotient of `M` by a submodule `p` to `M₂` induced by a linear map `f : M → M₂`
vanishing on `p`, as a linear map. -/
def liftq (f : M →ₛₗ[τ₁₂] M₂) (h : p ≤ f.ker) : p.quotient →ₛₗ[τ₁₂] M₂ :=
{ to_fun := λ x, _root_.quotient.lift_on' x f $
    λ a b (ab : a - b ∈ p), eq_of_sub_eq_zero $ by simpa using h ab,
  map_add' := by rintro ⟨x⟩ ⟨y⟩; exact f.map_add x y,
  map_smul' := by rintro a ⟨x⟩; exact f.map_smulₛₗ a x }

@[simp] theorem liftq_apply (f : M →ₛₗ[τ₁₂] M₂) {h} (x : M) :
  p.liftq f h (quotient.mk x) = f x := rfl

@[simp] theorem liftq_mkq (f : M →ₛₗ[τ₁₂] M₂) (h) : (p.liftq f h).comp p.mkq = f :=
by ext; refl

@[simp] theorem range_mkq : p.mkq.range = ⊤ :=
eq_top_iff'.2 $ by rintro ⟨x⟩; exact ⟨x, rfl⟩

@[simp] theorem ker_mkq : p.mkq.ker = p :=
by ext; simp

lemma le_comap_mkq (p' : submodule R p.quotient) : p ≤ comap p.mkq p' :=
by simpa using (comap_mono bot_le : p.mkq.ker ≤ comap p.mkq p')

@[simp] theorem mkq_map_self : map p.mkq p = ⊥ :=
by rw [eq_bot_iff, map_le_iff_le_comap, comap_bot, ker_mkq]; exact le_refl _

@[simp] theorem comap_map_mkq : comap p.mkq (map p.mkq p') = p ⊔ p' :=
by simp [comap_map_eq, sup_comm]

@[simp] theorem map_mkq_eq_top : map p.mkq p' = ⊤ ↔ p ⊔ p' = ⊤ :=
by simp only [map_eq_top_iff p.range_mkq, sup_comm, ker_mkq]

variables (q : submodule R₂ M₂)

/-- The map from the quotient of `M` by submodule `p` to the quotient of `M₂` by submodule `q` along
`f : M → M₂` is linear. -/
def mapq (f : M →ₛₗ[τ₁₂] M₂) (h : p ≤ comap f q) :
  p.quotient →ₛₗ[τ₁₂] q.quotient :=
p.liftq (q.mkq.comp f) $ by simpa [ker_comp] using h

@[simp] theorem mapq_apply (f : M →ₛₗ[τ₁₂] M₂) {h} (x : M) :
  mapq p q f h (quotient.mk x) = quotient.mk (f x) := rfl

theorem mapq_mkq (f : M →ₛₗ[τ₁₂] M₂) {h} : (mapq p q f h).comp p.mkq = q.mkq.comp f :=
by ext x; refl

theorem comap_liftq (f : M →ₛₗ[τ₁₂] M₂) (h) :
  q.comap (p.liftq f h) = (q.comap f).map (mkq p) :=
le_antisymm
  (by rintro ⟨x⟩ hx; exact ⟨_, hx, rfl⟩)
  (by rw [map_le_iff_le_comap, ← comap_comp, liftq_mkq]; exact le_refl _)

theorem map_liftq [ring_hom_surjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) (h) (q : submodule R (quotient p)) :
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
  submodule R p.quotient ≃o {p' : submodule R M // p ≤ p'} :=
{ to_fun    := λ p', ⟨comap p.mkq p', le_comap_mkq p _⟩,
  inv_fun   := λ q, map p.mkq q,
  left_inv  := λ p', map_comap_eq_self $ by simp,
  right_inv := λ ⟨q, hq⟩, subtype.ext_val $ by simpa [comap_map_mkq p],
  map_rel_iff'      := λ p₁ p₂, comap_le_comap_iff $ range_mkq _ }

/-- The ordering on submodules of the quotient of `M` by `p` embeds into the ordering on submodules
of `M`. -/
def comap_mkq.order_embedding :
  submodule R p.quotient ↪o submodule R M :=
(rel_iso.to_rel_embedding $ comap_mkq.rel_iso p).trans (subtype.rel_embedding _ _)

@[simp] lemma comap_mkq_embedding_eq (p' : submodule R p.quotient) :
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
  rw [hk, ← map_le_map_iff, map_span, map_comap_eq, set.image_preimage_eq_of_subset h₁],
  exact inf_le_right,
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
  (h : ∀ (u v : M₂ →ₗ[R₂] f.range.quotient), u.comp f = v.comp f → u = v) : f.range = ⊤ :=
begin
  have h₁ : (0 : M₂ →ₗ[R₂] f.range.quotient).comp f = 0 := zero_comp _,
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
def quot_equiv_of_eq_bot (hp : p = ⊥) : p.quotient ≃ₗ[R] M :=
linear_equiv.of_linear (p.liftq id $ hp.symm ▸ bot_le) p.mkq (liftq_mkq _ _ _) $
  p.quot_hom_ext $ λ x, rfl

@[simp] lemma quot_equiv_of_eq_bot_apply_mk (hp : p = ⊥) (x : M) :
  p.quot_equiv_of_eq_bot hp (quotient.mk x) = x := rfl

@[simp] lemma quot_equiv_of_eq_bot_symm_apply (hp : p = ⊥) (x : M) :
  (p.quot_equiv_of_eq_bot hp).symm x = quotient.mk x := rfl

@[simp] lemma coe_quot_equiv_of_eq_bot_symm (hp : p = ⊥) :
  ((p.quot_equiv_of_eq_bot hp).symm : M →ₗ[R] p.quotient) = p.mkq := rfl

/-- Quotienting by equal submodules gives linearly equivalent quotients. -/
def quot_equiv_of_eq (h : p = p') : p.quotient ≃ₗ[R] p'.quotient :=
{ map_add' := by { rintros ⟨x⟩ ⟨y⟩, refl }, map_smul' := by { rintros x ⟨y⟩, refl },
  ..@quotient.congr _ _ (quotient_rel p) (quotient_rel p') (equiv.refl _) $
    λ a b, by { subst h, refl } }

@[simp]
lemma quot_equiv_of_eq_mk (h : p = p') (x : M) :
  submodule.quot_equiv_of_eq p p' h (submodule.quotient.mk x) = submodule.quotient.mk x :=
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
def mapq_linear : compatible_maps p q →ₗ[R] p.quotient →ₗ[R] q.quotient :=
{ to_fun    := λ f, mapq _ _ f.val f.property,
  map_add'  := λ x y, by { ext, refl, },
  map_smul' := λ c f, by { ext, refl, } }

end submodule

end comm_ring
