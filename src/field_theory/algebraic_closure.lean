-- /-
-- Copyright (c) 2019 Chris Hughes. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Chris Hughes, Johan Commelin
-- -/

-- import algebra.direct_limit
-- import set_theory.schroeder_bernstein
-- import field_theory.algebraic

-- noncomputable theory
-- open_locale classical

-- universes u v w
-- open polynomial zorn set function
-- variables {K : Type u} [discrete_field K]

-- /- Turn down the instance priority for subtype.decidable_eq and use classical.dec_eq everywhere,
--   to avoid diamonds -/
-- local attribute [instance, priority 0] subtype.decidable_eq

-- lemma injective_eq {α : Sort*} : injective (eq : α → α → Prop) :=
-- λ _ _ h, h.symm ▸ rfl

-- @[instance] lemma equiv.is_ring_hom {α β : Type*} [ring β] (e : α ≃ β) :
--   @is_ring_hom β α _ (equiv.ring e) e.symm :=
-- by split; simp [equiv.mul_def, equiv.add_def, equiv.one_def]

-- instance equiv.is_ring_hom.symm {α β : Type*} [ring β] (e : α ≃ β) :
--   @is_ring_hom α β (equiv.ring e) _ e :=
-- by split; simp [equiv.mul_def, equiv.add_def, equiv.one_def]

-- def equiv.add_equiv {α β : Type*} [has_add β] (e : α ≃ β) :
--   @add_equiv α β e.has_add _ :=
-- { map_add' := λ x y, e.apply_symm_apply _,
--   ..e }

-- def equiv.mul_equiv {α β : Type*} [has_mul β] (e : α ≃ β) :
--   @mul_equiv α β e.has_mul _ :=
-- { map_mul' := λ x y, e.apply_symm_apply _,
--   ..e }

-- def equiv.ring_equiv {α β : Type*} [has_mul β] [has_add β] (e : α ≃ β) :
--   @ring_equiv α β e.has_mul e.has_add _ _ :=
-- { map_add' := λ x y, e.apply_symm_apply _,
--   map_mul' := λ x y, e.apply_symm_apply _,
--   ..e }

-- lemma exists_root_of_equiv {α β : Type*} [comm_ring α] [comm_ring β] (e : α ≃+* β)
--   {f : polynomial α} {x : β} (hx : f.eval₂ e x = 0) :
--   f.eval (e.symm x) = 0 :=
-- begin
--   have e_inj : function.injective e := e.to_equiv.injective,
--   apply e_inj,
--   rw [← eval₂_hom e, e.apply_symm_apply, is_ring_hom.map_zero e, hx],
-- end

-- namespace alg_hom
-- variables {α : Type u} {β : Type v} {γ : Type w} [comm_ring α] [ring β] [ring γ]
--   [algebra α β] [algebra α γ] (f : β →ₐ[α] γ)

-- def inverse (g : γ → β) (h₁ : left_inverse g f) (h₂ : right_inverse g f) : γ →ₐ[α] β :=
-- by dsimp [left_inverse, function.right_inverse] at h₁ h₂; exact
-- { to_fun := g,
--   hom := show is_ring_hom g, from
--   { map_add := λ x y, by rw [← h₁ (g x + g y), f.map_add, h₂, h₂],
--     map_mul := λ x y, by rw [← h₁ (g x * g y), f.map_mul, h₂, h₂],
--     map_one := by rw [← h₁ 1, f.map_one] },
--   commutes' := λ a, by rw [← h₁ (algebra_map β a), f.commutes] }

-- instance quotient.algebra (I : ideal α) : algebra α I.quotient :=
-- algebra.of_ring_hom (ideal.quotient.mk I) (ideal.quotient.is_ring_hom_mk I)

-- def induced_quotient_map (I J : ideal α) (h : I ≤ J) :
--   I.quotient →ₐ[α] J.quotient :=
-- { to_fun := ideal.quotient.lift I (ideal.quotient.mk J) $
--   by { intros i hi, erw submodule.quotient.mk_eq_zero, exact h hi },
--   commutes' := λ a, by { erw ideal.quotient.lift_mk, refl } }

-- end alg_hom

-- set_option old_structure_cmd true

-- structure alg_equiv (α β γ : Type*) [comm_ring α] [ring β] [ring γ]
--   [algebra α β] [algebra α γ] extends alg_hom α β γ, equiv β γ

-- set_option old_structure_cmd false

-- infix ` ≃ₐ `:25 := alg_equiv _
-- notation A ` ≃ₐ[`:25 R `] ` B := alg_equiv R A B

-- namespace alg_equiv
-- variables {α : Type u} {β : Type v} {γ : Type w} [comm_ring α] [ring β] [ring γ]
--   [algebra α β] [algebra α γ]

-- protected def refl : β ≃ₐ[α] β :=
-- { hom := is_ring_hom.id,
--   commutes' := λ b, rfl,
--   .. equiv.refl β }

-- protected def symm (e : β ≃ₐ[α] γ) : γ ≃ₐ[α] β :=
-- { .. e.to_alg_hom.inverse e.inv_fun e.left_inv e.right_inv,
--   .. e.to_equiv.symm }

-- -- TODO: trans

-- end alg_equiv

-- namespace adjoin_root
-- variables {α : Type*} [comm_ring α] [decidable_eq α] (f : polynomial α)

-- instance : algebra α (adjoin_root f) :=
-- algebra.of_ring_hom coe $ by apply_instance

-- lemma fg_of_monic (hf : f.monic) : submodule.fg (⊤ : submodule α (adjoin_root f)) :=
-- begin
--   refine ⟨(finset.range (f.nat_degree + 1)).image (λ i, adjoin_root.mk (X^i)), _⟩,
--   rw submodule.eq_top_iff',
--   intro a,
--   apply quotient.induction_on' a,
--   intro p, show mk p ∈ _,
--   rw [← mod_by_monic_add_div p hf, is_ring_hom.map_add mk, is_ring_hom.map_mul mk],
--   { refine submodule.add_mem _ _ _,
--     { apply_instance },
--     { rw [(p %ₘ f).as_sum, ← finset.sum_hom mk],
--       { refine submodule.sum_mem _ _,
--         intros i hi,
--         rw [is_ring_hom.map_mul mk],
--         { show algebra_map _ (coeff (p %ₘ f) i) * _ ∈ _,
--           rw ← algebra.smul_def,
--           refine submodule.smul_mem _ _ (submodule.subset_span _),
--           rw [finset.mem_coe, finset.mem_image],
--           refine ⟨i, _, rfl⟩,
--           rw finset.mem_range at hi ⊢,
--           refine lt_of_lt_of_le hi (nat.succ_le_succ _),
--           by_cases (p %ₘ f) = 0, { simp [h] },
--           rw ← with_bot.coe_le_coe,
--           rw ← degree_eq_nat_degree h,
--           apply le_trans (degree_mod_by_monic_le p hf),
--           exact degree_le_nat_degree },
--         { apply_instance } },
--       { apply_instance } },
--     { convert submodule.zero_mem _,
--       convert zero_mul _ using 2,
--       erw [submodule.quotient.mk_eq_zero _],
--       apply submodule.subset_span,
--       exact mem_singleton _ } },
--   all_goals { apply_instance }
-- end

-- open submodule

-- def adjoin_root_of_monic (f : polynomial K) :
--   adjoin_root (f * C (leading_coeff f)⁻¹) →ₐ[K] adjoin_root f :=
-- { to_fun := ideal.quotient.lift _ mk $ λ g hg,
--   begin
--     erw quotient.mk_eq_zero,
--     rw ideal.mem_span_singleton' at hg ⊢,
--     rcases hg with ⟨g, rfl⟩, rw [mul_comm f, ← mul_assoc],
--     exact ⟨_, rfl⟩,
--   end,
--   hom := ideal.quotient.is_ring_hom,
--   commutes' := λ g, rfl }

-- lemma fg {f : polynomial K} (hf : f ≠ 0) : submodule.fg (⊤ : submodule K (adjoin_root f)) :=
-- begin
--   let φ := adjoin_root_of_monic f,
--   have trick := fg_of_monic _ (monic_mul_leading_coeff_inv hf),
--   convert fg_map trick, swap, exact φ.to_linear_map,
--   { refine (submodule.eq_top_iff'.mpr _).symm,
--     intros x, apply quotient.induction_on' x, clear x,
--     intro g,
--     rw mem_map,
--     use [mk g, mem_top, rfl] }
-- end
-- .

-- lemma is_integral {f : polynomial K} (hf : f ≠ 0) (x : adjoin_root f) : is_integral K x :=
-- begin
--   refine is_integral_of_mem_of_fg ⊤ _ x algebra.mem_top,
--   convert fg hf,
--   rw eq_top_iff', intro y, exact algebra.mem_top,
-- end

-- end adjoin_root

-- section thing

-- local attribute [instance] classical.dec

-- private lemma thing_aux {X : Type u} {Y : Type v} {Z : Type w} (fxy : X ↪ Y) (fxz : X ↪ Z)
--   (hYZ : (Z ↪ Y) → false) : ↥-range fxy.1 ↪ ↥-range fxz.1 :=
-- classical.choice $ or.resolve_left embedding.total $
--   λ ⟨f⟩, hYZ $
--     calc Z ↪ range fxz ⊕ ↥-range fxz :
--       (equiv.set.sum_compl _).symm.to_embedding
--     ... ↪ range fxy ⊕ ↥-range fxy :
--       embedding.sum_congr
--         (((equiv.set.range _ fxz.2).symm.to_embedding).trans
--           (equiv.set.range _ fxy.2).to_embedding)
--         f
--     ... ↪ Y : (equiv.set.sum_compl _).to_embedding

-- private def thing {X : Type u} {Y : Type v} {Z : Type w} (fxy : X ↪ Y) (fxz : X ↪ Z)
--   (hYZ : (Z ↪ Y) → false) : Y ↪ Z :=
-- calc Y ↪ range fxy ⊕ ↥-range fxy : (equiv.set.sum_compl _).symm.to_embedding
-- ... ↪ range fxz ⊕ ↥-range fxz : embedding.sum_congr
--   ((equiv.set.range _ fxy.2).symm.to_embedding.trans
--     (equiv.set.range _ fxz.2).to_embedding)
--   (thing_aux fxy fxz hYZ)
-- ... ↪ Z : (equiv.set.sum_compl _).to_embedding

-- private lemma thing_commutes {X : Type u} {Y : Type v} {Z : Type w}  (fxy : X ↪ Y) (fxz : X ↪ Z)
--   (hYZ : (Z ↪ Y) → false) (x : X) : thing fxy fxz hYZ (fxy x) = fxz x :=
-- have (⟨fxy x, mem_range_self _⟩ : range fxy) = equiv.set.range _ fxy.2 x, from rfl,
-- begin
--   dsimp only [thing, embedding.trans_apply, equiv.trans_apply, function.comp,
--     equiv.to_embedding_coe_fn],
--   simp only [equiv.set.sum_compl_symm_apply_of_mem (mem_range_self _),
--     embedding.sum_congr_apply_inl, equiv.set.sum_compl_apply_inl,
--     embedding.trans_apply, equiv.to_embedding_coe_fn, this, equiv.symm_apply_apply],
--   refl
-- end

-- end thing

-- class is_algebraically_closed (K : Type u) [nonzero_comm_ring K] [decidable_eq K] :=
-- (exists_root : ∀ f : polynomial K, 0 < degree f → ∃ x, is_root f x)

-- section is_algebraically_closed

-- lemma is_algebraically_closed_of_irreducible_has_root
--   (h : ∀ f : polynomial K, irreducible f → ∃ x, is_root f x) :
--   is_algebraically_closed K :=
-- ⟨λ f hf0, let ⟨g, hg⟩ := is_noetherian_ring.exists_irreducible_factor
--   (show ¬ is_unit f, from λ h, by rw [is_unit_iff_degree_eq_zero] at h;
--     rw h at hf0; exact lt_irrefl _ hf0)
--   (λ h, by rw ← degree_eq_bot at h;
--     rw h at hf0; exact absurd hf0 dec_trivial) in
--   let ⟨x, hx⟩ := h g hg.1 in
--   let ⟨i, hi⟩ := hg.2 in
--   ⟨x, by rw [hi, is_root.def, eval_mul, show _ = _, from hx, zero_mul]⟩⟩

-- variables (L : Type*) [nonzero_comm_ring L] [decidable_eq L] [is_algebraically_closed L]

-- lemma exists_root (f : polynomial L) (hf : 0 < f.degree) :
--   ∃ x, is_root f x :=
-- is_algebraically_closed.exists_root f hf

-- -- /- An algebraic extension of -/
-- -- lemma equiv_of_algebraic

-- end is_algebraically_closed

-- --move this
-- namespace polynomial
-- variables (R : Type u) (A : Type v)
-- variables [comm_ring R] [comm_ring A] [algebra R A]
-- variables [decidable_eq R] (x : A)

-- @[simp] lemma aeval_X : aeval R A x X = x := eval₂_X _ x

-- @[simp] lemma aeval_C (r : R) : aeval R A x (C r) = algebra_map A r := eval₂_C _ x

-- end polynomial

-- namespace algebraic_closure

-- section classical

-- local attribute [instance, priority 1] classical.dec

-- /-- The `big_type` with cardinality strictly larger than any algebraic extension -/
-- private def big_type (K : Type u) [discrete_field K] := set (ℕ × polynomial K)

-- private def algebraic_embedding_aux {L : Type*} [discrete_field L] [algebra K L]
--   (h : ∀ l : L, is_integral K l) (x : L) : ℕ × polynomial K :=
-- let f := classical.some (h x) in
-- ⟨list.index_of x (quotient.out ((f.map (algebra_map L)).roots.1)), f⟩

-- private lemma algebraic_embedding_aux_injective
--   {L : Type*} [discrete_field L] [algebra K L]
--   (h : ∀ l : L, is_integral K l) : injective (algebraic_embedding_aux h) :=
-- λ x y hxy,
-- let f := classical.some (h x) in
-- let g := classical.some (h y) in
-- have hf : monic f ∧ aeval K L x f = 0, from classical.some_spec (h x),
-- have hg : monic g ∧ aeval K L y g = 0, from classical.some_spec (h y),
-- have hfg : f = g, from (prod.ext_iff.1 hxy).2,
-- have hfg' : list.index_of x (quotient.out ((f.map (algebra_map L)).roots.1)) =
--     list.index_of y (quotient.out ((f.map (algebra_map L)).roots.1)),
--   from (prod.ext_iff.1 hxy).1.trans (hfg.symm ▸ rfl),
-- have hx : x ∈ quotient.out ((f.map (algebra_map L)).roots.1),
--   from multiset.mem_coe.1 begin
--     show x ∈ quotient.mk _,
--     rw [quotient.out_eq, ← finset.mem_def, mem_roots (mt (map_eq_zero (algebra_map L)).1
--       (ne_zero_of_monic hf.1)), is_root.def, eval_map, ← aeval_def, hf.2],
--   end,
-- have hy : y ∈ quotient.out ((g.map (algebra_map L)).roots.1),
--   from multiset.mem_coe.1 begin
--     show y ∈ quotient.mk _,
--     rw [quotient.out_eq, ← finset.mem_def, mem_roots (mt (map_eq_zero (algebra_map L)).1
--       (ne_zero_of_monic hg.1)), is_root.def, eval_map, ← aeval_def, hg.2],
--   end,
-- (list.index_of_inj hx (by rwa hfg)).1 hfg'

-- private def algebraic_embedding_big_type {L : Type*} [discrete_field L] [algebra K L]
--   (h : ∀ l : L, is_integral K l) : L ↪ big_type K :=
-- ⟨_, injective_comp injective_eq $ algebraic_embedding_aux_injective h⟩

-- private def algebraic_embedding {L : Type*} [discrete_field L] [algebra K L]
--   (h : ∀ l : L, is_integral K l) : L ↪ ℕ × polynomial K :=
-- ⟨_, algebraic_embedding_aux_injective h⟩

-- private def bembedding (K : Type u) [discrete_field K] : K ↪ big_type K :=
-- ⟨λ a, show set _, from {(0, X - C a)}, λ a b, by simp [C_inj]⟩

-- instance range_bembedding.discrete_field : discrete_field (set.range (bembedding K)) :=
-- equiv.discrete_field (equiv.set.range _ (bembedding K).2).symm

-- private structure extension (K : Type u) [discrete_field K] : Type u :=
-- (carrier : set (big_type K))
-- [field : discrete_field ↥carrier]
-- [algebra : algebra K ↥carrier]
-- (algebraic : ∀ x : carrier, is_integral K x)

-- attribute [instance] extension.field extension.algebra

-- private def base_extension (K : Type u) [discrete_field K] : extension K :=
-- { carrier := set.range (bembedding K),
--   algebra := algebra.of_ring_hom (equiv.set.range _ (bembedding K).2).symm.symm
--     (by apply_instance),
--   algebraic :=
--   begin
--     rintro ⟨_, x, rfl⟩,
--     refine ⟨X + C (-x), monic_X_add_C (-x), _⟩,
--     rw [alg_hom.map_add, C_neg, alg_hom.map_neg, polynomial.aeval_X, polynomial.aeval_C],
--     exact add_neg_self _
--   end }

-- -- /-- not used but might help with sorries -/
-- -- private def extension.of_algebraic {L : Type v} [discrete_field L] [algebra K L]
-- --   (hL : ∀ x : L, is_integral K x) : extension K :=
-- -- { carrier := set.range (algebraic_embedding_big_type hL),
-- --   field := equiv.discrete_field (equiv.set.range _ (algebraic_embedding_big_type hL).2).symm,
-- --   algebra := sorry, -- a field isomorphic to an algebra is an algebra
-- --   algebraic := sorry -- a field isomorphic to an algebraic extension is algebraic
-- --   }

-- @[simp] lemma inclusion_refl {α : Type*} {s : set α} (h : s ⊆ s) : inclusion h = id :=
-- funext $ λ x, by { cases x, refl }

-- @[simp] lemma inclusion_trans {α : Type*} {s t u : set α} (hst : s ⊆ t) (htu : t ⊆ u) :
--   inclusion (set.subset.trans hst htu) = inclusion htu ∘ inclusion hst :=
-- funext $ λ x, by { cases x, refl }

-- instance : preorder (extension K) :=
-- { le := λ L M, ∃ hLM : L.carrier ⊆ M.carrier, (is_ring_hom (inclusion hLM) ∧
--     (inclusion hLM ∘ (algebra_map L.carrier : K → L.carrier) = algebra_map M.carrier)),
--   le_refl := λ L,
--     begin
--       use set.subset.refl L.carrier,
--       rw inclusion_refl,
--       exact ⟨is_ring_hom.id, comp.left_id _⟩
--     end,
--   le_trans := λ L M N ⟨hLM₁, hLM₂, hLM₃⟩ ⟨hMN₁, hMN₂, hMN₃⟩,
--     begin
--       use set.subset.trans hLM₁ hMN₁,
--       rw inclusion_trans, resetI,
--       refine ⟨is_ring_hom.comp _ _, _⟩,
--       rw [comp.assoc, hLM₃, hMN₃]
--     end }

-- lemma le_def {L M : extension K} :
--   L ≤ M ↔ ∃ hLM : L.carrier ⊆ M.carrier, (is_ring_hom (inclusion hLM) ∧
--     (inclusion hLM ∘ (algebra_map L.carrier : K → L.carrier) = algebra_map M.carrier)) := iff.rfl

-- lemma subset_of_le {L M : extension K} (h : L ≤ M) : L.carrier ⊆ M.carrier :=
-- by { rw le_def at h, rcases h with ⟨_,_,_⟩, assumption }

-- lemma ring_hom_of_le {L M : extension K} (h : L ≤ M) :
--   is_ring_hom (inclusion $ subset_of_le h) :=
-- by { rw le_def at h, rcases h with ⟨_,_,_⟩, assumption }

-- lemma compat {L M : extension K} (h : L ≤ M) :
--   inclusion (subset_of_le h) ∘ (algebra_map L.carrier : K → L.carrier) = algebra_map M.carrier :=
-- by { rw le_def at h, rcases h with ⟨_,_,_⟩, assumption }

-- local attribute [instance] ring_hom_of_le

-- private structure chain' (c : set (extension K)) : Prop :=
-- (chain : chain (≤) c)

-- local attribute [class] chain'

-- private lemma is_chain (c : set (extension K)) [chain' c]: chain (≤) c :=
-- chain'.chain (by apply_instance)

-- section chain

-- variables (c : set (extension K)) [hcn : nonempty c]
-- include c  hcn

-- variable [hcn' : chain' c]
-- include hcn'

-- instance chain_directed_order : directed_order c :=
-- ⟨λ ⟨i, hi⟩ ⟨j, hj⟩, let ⟨k, hkc, hk⟩ := chain.directed_on
--   (is_chain c) i hi j hj in ⟨⟨k, hkc⟩, hk⟩⟩

-- private def chain_map (i j : c) (hij : i ≤ j) : i.1.carrier → j.1.carrier :=
-- inclusion (exists.elim hij (λ h _, h))

-- instance chain_field_hom (i j : c) (hij : i ≤ j) : is_field_hom (chain_map c i j hij) :=
-- ring_hom_of_le hij

-- instance chain_directed_system : directed_system (λ i : c, i.1.carrier) (chain_map c) :=
-- begin
--   split; intros; simp only [chain_map],
--   { exact congr_fun (inclusion_refl _) x },
--   { exact (congr_fun (inclusion_trans _ _) x).symm }
-- end

-- private def chain_limit : Type u := ring.direct_limit (λ i : c, i.1.carrier) (chain_map c)

-- private lemma of_eq_of (x : big_type K) (i j : c) (hi : x ∈ i.1.carrier) (hj : x ∈ j.1.carrier) :
--   ring.direct_limit.of (λ i : c, i.1.carrier) (chain_map c) i ⟨x, hi⟩ =
--   ring.direct_limit.of (λ i : c, i.1.carrier) (chain_map c) j ⟨x, hj⟩ :=
-- have hij : i ≤ j ∨ j ≤ i,
--   from show i.1 ≤ j.1 ∨ j.1 ≤ i.1, from chain.total (is_chain c) i.2 j.2,
-- hij.elim
--   (λ hij, begin
--     rw ← @ring.direct_limit.of_f c _ _ _ (λ i : c, i.1.carrier) _ _ (chain_map c) _
--       _ _ _ hij,
--     simp [chain_map, inclusion]
--   end)
--   (λ hij, begin
--     rw ← @ring.direct_limit.of_f c _ _ _ (λ i : c, i.1.carrier) _ _ (chain_map c) _
--       _ _ _ hij,
--     simp [chain_map, inclusion]
--   end)

-- private lemma injective_aux (i j : c)
--   (x y : ⋃ i : c, i.1.carrier) (hx : x.1 ∈ i.1.carrier) (hy : y.1 ∈ j.1.carrier) :
--   ring.direct_limit.of (λ i : c, i.1.carrier) (chain_map c) i ⟨x, hx⟩ =
--   ring.direct_limit.of (λ i : c, i.1.carrier) (chain_map c) j ⟨y, hy⟩ →
--   x = y :=
-- have hij : i ≤ j ∨ j ≤ i,
--   from show i.1 ≤ j.1 ∨ j.1 ≤ i.1, from chain.total (is_chain c) i.2 j.2,
-- have hinj : ∀ (i j : c) (hij : i ≤ j), injective (chain_map c i j hij),
--   from λ _ _ _, is_field_hom.injective _,
-- hij.elim
--   (λ hij h, begin
--     rw ← @ring.direct_limit.of_f c _ _ _ (λ i : c, i.1.carrier) _ _ (chain_map c) _
--       _ _ _ hij at h,
--     simpa [chain_map, inclusion, subtype.coe_ext.symm] using ring.direct_limit.of_inj hinj j h,
--   end)
--   (λ hji h, begin
--     rw ← @ring.direct_limit.of_f c _ _ _ (λ i : c, i.1.carrier) _ _ (chain_map c) _
--       _ _ _ hji at h,
--     simpa [chain_map, inclusion, subtype.coe_ext.symm] using ring.direct_limit.of_inj hinj i h,
--   end)

-- private def equiv_direct_limit : (⋃ (i : c), i.1.carrier) ≃
--   ring.direct_limit (λ i : c, i.1.carrier) (chain_map c) :=
-- @equiv.of_bijective (⋃ i : c, i.1.carrier)
--   (ring.direct_limit (λ i : c, i.1.carrier) (chain_map c))
--   (λ x, ring.direct_limit.of _ _ (classical.some (set.mem_Union.1 x.2))
--     ⟨_, classical.some_spec (set.mem_Union.1 x.2)⟩)
--   ⟨λ x y, injective_aux _ _ _ _ _ _ _,
--     λ x, let ⟨i, ⟨y, hy⟩, hy'⟩ := ring.direct_limit.exists_of x in
--       ⟨⟨y, _, ⟨i, rfl⟩, hy⟩, begin
--         convert hy',
--         exact of_eq_of _ _ _ _ _ _
--       end⟩⟩

-- instance Union_field : discrete_field (⋃ i : c, i.1.carrier) :=
-- @equiv.discrete_field _ _ (equiv_direct_limit c)
--   (field.direct_limit.discrete_field _ _)

-- set_option class.instance_max_depth 50

-- instance is_field_hom_Union (i : c) : is_field_hom
--   (inclusion (set.subset_Union (λ i : c, i.1.carrier) i)) :=
-- suffices inclusion (set.subset_Union (λ i : c, i.1.carrier) i) =
--     ((equiv_direct_limit c).symm ∘
--     ring.direct_limit.of (λ i : c, i.1.carrier) (chain_map c) i),
--   by rw this; exact is_ring_hom.comp _ _,
-- funext $ λ ⟨_, _⟩,
--   (equiv_direct_limit c).injective $
--     by rw [function.comp_app, equiv.apply_symm_apply];
--       exact of_eq_of _ _ _ _ _ _

-- def Union_algebra (L : c) : algebra K (⋃ i : c, i.1.carrier) :=
-- algebra.of_ring_hom ((inclusion (set.subset_Union (λ i : c, i.1.carrier) L)) ∘ algebra_map _)
-- (by { refine @is_ring_hom.comp _ _ _ _ _ _ _ _ _ _ })

-- lemma Union_compat (L : c) (M : c) :
--   (inclusion (set.subset_Union (λ i : c, i.1.carrier) M)) ∘
--     (algebra_map (M.val.carrier) : K → M.val.carrier) =
--   by haveI := Union_algebra c L; exact algebra_map (↥⋃ (i : ↥c), (i.val).carrier) :=
-- begin
--   rcases chain.directed_on (is_chain c) L.1 L.2 M.1 M.2 with ⟨N, hN, hLN, hMN⟩,
--   rw show (inclusion (set.subset_Union (λ i : c, i.1.carrier) M)) =
--     ((inclusion (set.subset_Union (λ i : c, i.1.carrier) ⟨N, hN⟩)) ∘
--     inclusion (subset_of_le hMN)),
--   { funext x, refl },
--   rw comp.assoc,
--   rw show inclusion (subset_of_le hMN) ∘ (algebra_map _ : K → (M.val).carrier) =
--     inclusion (subset_of_le hLN) ∘ algebra_map _,
--   { rw [compat, ← compat] },
--   rw ← comp.assoc,
--   rw ← show (inclusion (set.subset_Union (λ i : c, i.1.carrier) L)) =
--     ((inclusion (set.subset_Union (λ i : c, i.1.carrier) ⟨N, hN⟩)) ∘
--     inclusion (subset_of_le hLN)),
--   { funext x, refl },
--   refl
-- end

-- end chain

-- private def maximal_extension_chain (c : set (extension K)) (hc : chain (≤) c) :
--   { ub : extension K // ∀ L, L ∈ c → L ≤ ub } :=
-- if h : nonempty c
--   then
--   let L := classical.some (classical.exists_true_of_nonempty h) in
--   by letI : chain' c := ⟨hc⟩; exact
--     ⟨{ carrier := ⋃ (i : c), i.1.carrier,
--         algebra := Union_algebra c L,
--         algebraic :=
--         begin
--           rintro ⟨x, hx⟩,
--           rw mem_Union at hx,
--           cases hx with L' hx,
--           rcases (L'.val).algebraic ⟨x, hx⟩ with ⟨p, pmonic, hp⟩,
--           use [p, pmonic],
--           rw aeval_def at hp ⊢,
--           replace hp := congr_arg (inclusion (set.subset_Union (λ i : c, i.1.carrier) L')) hp,
--           convert hp using 1; symmetry,
--           { rw p.hom_eval₂ _ (inclusion _) _,
--             congr' 1,
--             { exact Union_compat c L L' },
--             { apply_instance, },
--             { apply is_ring_hom.is_semiring_hom, } },
--           { refine is_ring_hom.map_zero _ },
--         end },
--     λ e he, ⟨by convert subset_Union _ (⟨e, he⟩ : c); refl,
--       algebraic_closure.is_field_hom_Union c ⟨e, he⟩, Union_compat c L ⟨e, he⟩⟩⟩
--   else ⟨base_extension K, λ a ha, (h ⟨⟨a, ha⟩⟩).elim⟩

-- section adjoin_root
-- variables {L : extension K} (f : polynomial L.carrier) [hif : irreducible f]
-- include hif

-- open algebra

-- instance adjoin_root_algebraic_closure.field :
--   discrete_field (adjoin_root f) := adjoin_root.field

-- instance adjoin_root_algebraic_closure.is_ring_hom :
--   is_ring_hom (@adjoin_root.of _ _ _ f) := adjoin_root.is_ring_hom

-- private def adjoin_root.of_embedding : L.carrier ↪ adjoin_root f :=
-- ⟨adjoin_root.of, @is_field_hom.injective _ _ _ _ _ $ adjoin_root_algebraic_closure.is_ring_hom f⟩

-- variable (K)

-- def aux_instance : algebra K (adjoin_root f) :=
-- algebra.of_ring_hom (adjoin_root.of ∘ algebra_map _) (is_ring_hom.comp _ _)

-- local attribute [instance] aux_instance

-- lemma adjoin_root.algebraic (x : adjoin_root f) : is_integral K x :=
-- is_integral_trans L.algebraic x $ adjoin_root.is_integral hif.ne_zero x

-- private def adjoin_root_extension_map : adjoin_root f ↪ big_type K :=
-- thing (adjoin_root.of_embedding f) ⟨subtype.val, subtype.val_injective⟩
--   (λ i, let e : big_type K ↪ ℕ × polynomial K := i.trans
--       (algebraic_embedding (adjoin_root.algebraic K f)) in
--     cantor_injective e.1 e.2)

-- private lemma adjoin_root_extension_map_apply (x : L.carrier) :
--   (adjoin_root_extension_map K f) (@adjoin_root.of _ _ _ f x) = x.val :=
-- thing_commutes _ _ _ _

-- instance range_adjoin_root_extension_map.discrete_field :
--   discrete_field (set.range (@adjoin_root_extension_map K _ _ f _)) :=
-- equiv.discrete_field (equiv.set.range _ (embedding.inj _)).symm

-- private def adjoin_root_extension : extension K :=
-- { carrier := set.range (@adjoin_root_extension_map K _ _ f _),
--   algebra := algebra.of_ring_hom
--     ((equiv.set.range _ (embedding.inj' (adjoin_root_extension_map K f))).symm.symm ∘
--       algebra_map _) (is_ring_hom.comp _ _),
--   algebraic :=
--   begin
--     rintro ⟨_, x, rfl⟩,
--     rcases adjoin_root.algebraic K f x with ⟨p, pmonic, hp⟩,
--     use [p, pmonic],
--     rw [aeval_def] at hp ⊢,
--     replace hp := congr_arg
--       ((equiv.set.range _ (embedding.inj' (adjoin_root_extension_map K f))).symm.symm) hp,
--     convert hp using 1,
--     symmetry,
--     convert polynomial.hom_eval₂ _ _ _ _,
--     all_goals {apply_instance}
--   end }

-- variable {L}
-- private lemma subset_adjoin_root_extension : L.carrier ⊆ (adjoin_root_extension K f).carrier :=
-- λ x h, ⟨adjoin_root.of_embedding f ⟨x, h⟩, thing_commutes _ _ _ _⟩

-- private lemma adjoin_root_inclusion_eq : inclusion (subset_adjoin_root_extension K f) =
--   ((equiv.set.range _ (adjoin_root_extension_map K f).2).symm.symm ∘ adjoin_root.of_embedding f) :=
-- funext $ λ ⟨_, _⟩, subtype.eq $ eq.symm $ adjoin_root_extension_map_apply _ _ _

-- private lemma le_adjoin_root_extension : L ≤ adjoin_root_extension K f :=
-- ⟨subset_adjoin_root_extension K f,
--   begin
--     rw [adjoin_root_inclusion_eq]; dsimp [adjoin_root.of_embedding],
--     exact ⟨is_ring_hom.comp _ _, rfl⟩
--   end⟩

-- private def equiv_adjoin_root_of_le (h : adjoin_root_extension K f ≤ L) :
--   L.carrier ≃+* adjoin_root f :=
-- have left_inv : left_inverse (inclusion h.fst ∘ (equiv.set.range _
--     (adjoin_root_extension_map K f).2)) adjoin_root.of,
-- from λ _, by simp [adjoin_root_extension_map_apply, inclusion],
-- have hom : is_ring_hom (coe : L.carrier → adjoin_root f), by apply_instance,
-- { to_fun := coe,
--   inv_fun := inclusion h.fst ∘ (equiv.set.range _ (adjoin_root_extension_map K f).2),
--   left_inv := left_inv,
--   right_inv := right_inverse_of_injective_of_left_inverse
--     (injective_comp (inclusion_injective _) (equiv.injective _))
--     left_inv,
--   map_add' := hom.map_add,
--   map_mul' := hom.map_mul }

-- private def adjoin_root_equiv_adjoin_root_extension :
--   adjoin_root f ≃+* (adjoin_root_extension K f).carrier :=
-- (equiv.set.range _ (adjoin_root_extension_map K f).2).symm.ring_equiv.symm

-- end adjoin_root

-- private lemma exists_algebraic_closure (K : Type u) [discrete_field K] :
--   ∃ m : extension K, ∀ a, m ≤ a → a ≤ m :=
-- zorn (λ c hc, (maximal_extension_chain c hc).exists_of_subtype) (λ _ _ _, le_trans)

-- private def closed_extension (K : Type u) [discrete_field K] :=
-- classical.some (exists_algebraic_closure K)

-- def algebraic_closure (K : Type u) [discrete_field K] : Type u :=
-- ((classical.some (exists_algebraic_closure K))).carrier

-- end classical

-- section is_algebraically_closed
-- /- In this section we prove the algebraic closure is algebraically closed -/

-- local attribute [reducible] algebraic_closure

-- variables (f : polynomial (algebraic_closure K)) [hif : irreducible f]
-- include hif

-- variable (K)

-- def algebraic_closure_equiv_adjoin_root : algebraic_closure K ≃+* adjoin_root f :=
-- equiv_adjoin_root_of_le K f $
--   classical.some_spec (exists_algebraic_closure K) _ (le_adjoin_root_extension _ _)

-- instance ring_equiv.is_semiring_hom {α β : Type*} [ring α] [ring β] (e : α ≃+* β) :
--   is_semiring_hom (e : α → β) :=
-- is_ring_hom.is_semiring_hom _

-- omit hif

-- private def is_algebraically_closed_aux : is_algebraically_closed (algebraic_closure K) :=
-- is_algebraically_closed_of_irreducible_has_root $
-- λ f hf, let e := by exactI algebraic_closure_equiv_adjoin_root K f in
-- ⟨_, exists_root_of_equiv e (adjoin_root.eval₂_root f)⟩

-- end is_algebraically_closed

-- /- To avoid diamonds, the `decidable_eq` instance is set to `classical.dec_eq`,
--   as opposed to the (noncomputable, but not def-eq to `classical.dec_eq`) instance given by
--   `(closed_extension K).field` -/
-- instance : discrete_field (algebraic_closure K) :=
-- { has_decidable_eq := classical.dec_eq _,
--   ..(closed_extension K).field }

-- instance : algebra K (algebraic_closure K) := (closed_extension K).algebra

-- instance : is_algebraically_closed (algebraic_closure K) :=
-- by convert is_algebraically_closed_aux K

-- protected def is_integral : ∀ x : algebraic_closure K, is_integral K x :=
-- (closed_extension K).algebraic

-- attribute [irreducible] algebraic_closure closed_extension algebraic_closure.algebra

-- namespace lift
-- /- In this section, the homomorphism from any algebraic extension into an algebraically
--   closed extension is proven to exist. The assumption that M is algebraically closed could probably
--   easily be switched to an assumption that M contains all the roots of polynomials in K -/
-- variables {L : Type v} {M : Type w} [discrete_field L] [algebra K L]
--   [discrete_field M] [algebra K M] [is_algebraically_closed M] (hL : ∀ x : L, is_integral K x)

-- variables (K L M)
-- include hL

-- /-- This structure is used to prove the existence of a homomorphism from any algebraic extension
-- into an algebraic closure -/
-- private structure subfield_with_hom :=
-- (carrier : subalgebra K L)
-- (emb : (@alg_hom K _ M _ _ _ (subalgebra.algebra carrier) _))

-- variables {K L M hL}

-- namespace subfield_with_hom
-- variables {E₁ E₂ E₃ : subfield_with_hom K L M hL}

-- instance : has_le (subfield_with_hom K L M hL) :=
-- { le := λ E₁ E₂, ∃ h : E₁.carrier ≤ E₂.carrier, E₂.emb ∘ inclusion h = E₁.emb }

-- lemma le_def : E₁ ≤ E₂ ↔ ∃ h : E₁.carrier ≤ E₂.carrier, E₂.emb ∘ inclusion h = E₁.emb := iff.rfl

-- lemma subalgebra_le_of_le (h : E₁ ≤ E₂) : E₁.carrier ≤ E₂.carrier :=
-- by { rw le_def at h, cases h, assumption }

-- lemma compat (h : E₁ ≤ E₂) : E₂.emb ∘ inclusion (subalgebra_le_of_le h) = E₁.emb :=
-- by { rw le_def at h, cases h, assumption }

-- instance : preorder (subfield_with_hom K L M hL) :=
-- { le := λ E₁ E₂, ∃ h : E₁.carrier ≤ E₂.carrier, E₂.emb ∘ inclusion h = E₁.emb,
--   le_refl := λ E, ⟨le_refl _, by rw [inclusion_refl, comp.right_id]⟩,
--   le_trans := λ E₁ E₂ E₃ h₁₂ h₂₃, ⟨le_trans (subalgebra_le_of_le h₁₂) (subalgebra_le_of_le h₂₃),
--   begin
--     erw inclusion_trans (subalgebra_le_of_le h₁₂) (subalgebra_le_of_le h₂₃),
--     rw [← comp.assoc, compat, compat]
--   end⟩ }

-- end subfield_with_hom

-- open lattice

-- def maximal_subfield_with_hom_chain (c : set (subfield_with_hom K L M hL)) (hc : chain (≤) c) :
--   ∃ ub : subfield_with_hom K L M hL, ∀ N, N ∈ c → N ≤ ub :=
-- let ub : subfield_with_hom K L M hL :=
-- { carrier := Sup (subfield_with_hom.carrier '' c),
--   emb := sorry } in
-- ⟨ub, λ N hN,
-- begin
--   refine ⟨lattice.le_Sup ⟨N, hN, rfl⟩, _⟩,
--   sorry
-- end⟩

-- variables (hL M)

-- lemma exists_maximal_subfield_with_hom : ∃ E : subfield_with_hom K L M hL,
--   ∀ N, E ≤ N → N ≤ E :=
-- zorn (maximal_subfield_with_hom_chain) (λ _ _ _, le_trans)

-- def maximal_subfield_with_hom : subfield_with_hom K L M hL :=
-- classical.some (exists_maximal_subfield_with_hom M hL)

-- lemma maximal_subfield_with_hom_is_maximal :
--   ∀ (N : subfield_with_hom K L M hL),
--     (maximal_subfield_with_hom M hL) ≤ N → N ≤ (maximal_subfield_with_hom M hL) :=
-- classical.some_spec (exists_maximal_subfield_with_hom M hL)

-- lemma emb_injective (E : subfield_with_hom K L M hL) :
--   injective E.emb :=
-- begin
--   sorry
--   -- let tmpa : _ := _, let tmpb : _ := _,
--   -- refine @is_field_hom.injective _ M tmpa _ _ tmpb,
--   -- swap,
--   -- { sorry },
--   -- { exact { .. E.emb.hom } }
-- end

-- lemma maximal_subfield_with_hom_surj :
--   surjective (maximal_subfield_with_hom M hL).carrier.val :=
-- begin
--   intros x, refine ⟨⟨x, _⟩, rfl⟩,
--   replace hx := (maximal_subfield_with_hom M hL).carrier.is_integral x (hL x),
--   let p := minimal_polynomial hx,
--   have H := exists_root M (p.map (maximal_subfield_with_hom M hL).emb) _,
--   swap,
--   { calc 0 < degree p :
--     begin
--       sorry -- minimal_polynomial.degree_pos gives diamonds
--     end
--        ... = degree (p.map (maximal_subfield_with_hom M hL).emb) :
--     begin
--       symmetry,
--       -- refine @polynomial.degree_map' _ _ _ _ _ _ p _ (by exact is_ring_hom.is_semiring_hom _) _,
--       sorry,
--     end },
--   let y := classical.some H,
--   let f := algebra.adjoin_singleton_desc x hx
--     (maximal_subfield_with_hom M hL).emb y (classical.some_spec H),
--   let tmpa : subalgebra _ L := algebra.adjoin _ ({x} : set L),
--   let tmpb : _ := _,
--   let N : subfield_with_hom K L M hL :=
--   { carrier := subalgebra.under (maximal_subfield_with_hom M hL).carrier tmpa,
--     emb :=
--     { to_fun := f,
--       hom := algebra.adjoin_singleton_desc.is_ring_hom _ _ _ _ _,
--       commutes' := tmpb } },
--   have hN : x ∈ N.carrier := algebra.subset_adjoin (mem_singleton x),
--   refine subfield_with_hom.subalgebra_le_of_le (maximal_subfield_with_hom_is_maximal M hL N _) hN,
--   { refine ⟨λ l hl, ring.subset_closure (mem_union_left _ _), _⟩,
--     { rw mem_range, refine ⟨⟨l, hl⟩, rfl⟩ },
--     { sorry } },
--   { sorry }
-- end

-- end lift

-- variables {L : Type v} {M : Type w} [discrete_field L] [algebra K L]
--   [discrete_field M] [algebra K M] [is_algebraically_closed M] (hL : ∀ x : L, is_integral K x)

-- variables (K L M)
-- include hL

-- /-- A (random) hom from an algebraic extension of K into an algebraic closure -/
-- def lift : L →ₐ[K] M :=
-- (lift.maximal_subfield_with_hom M hL).emb.comp $ alg_equiv.to_alg_hom $ alg_equiv.symm
-- { ..(lift.maximal_subfield_with_hom M hL).carrier.val,
--   ..equiv.of_bijective
--     ⟨subtype.val_injective, lift.maximal_subfield_with_hom_surj _ _⟩ }

-- end algebraic_closure
-- Copyright (c) 2020 Kenny Lau. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Kenny Lau
-- -/

-- import algebra.direct_limit
-- import field_theory.splitting_field

-- /-!
-- # Algebraic Closure

-- In this file we define the typeclass for algebraically closed fields and algebraic closures.
-- We also construct an algebraic closure for any field.

-- ## Main Definitions

-- - `is_alg_closed k` is the typeclass saying `k` is an algebraically closed field, i.e. every
-- polynomial in `k` splits.

-- - `is_alg_closure k K` is the typeclass saying `K` is an algebraic closure of `k`.

-- - `algebraic_closure k` is an algebraic closure of `k` (in the same universe).
--   It is constructed by taking the polynomial ring generated by indeterminates `x_f`
--   corresponding to monic irreducible polynomials `f` with coefficients in `k`, and quotienting
--   out by a maximal ideal containing every `f(x_f)`, and then repeating this step countably
--   many times. See Exercise 1.13 in Atiyah--Macdonald.

-- ## TODO

-- Show that any algebraic extension embeds into any algebraically closed extension (via Zorn's lemma).

-- ## Tags

-- algebraic closure, algebraically closed

-- -/

-- universes u v w
-- noncomputable theory
-- open_locale classical big_operators
-- open polynomial

-- variables (k : Type u) [field k]

-- /-- Typeclass for algebraically closed fields.

-- To show `polynomial.splits p f` for an arbitrary ring homomorphism `f`,
-- see `is_alg_closed.splits_codomain` and `is_alg_closed.splits_domain`.
-- -/
-- class is_alg_closed : Prop :=
-- (splits : ∀ p : polynomial k, p.splits $ ring_hom.id k)

-- /-- Every polynomial splits in the field extension `f : K →+* k` if `k` is algebraically closed.

-- See also `is_alg_closed.splits_domain` for the case where `K` is algebraically closed.
-- -/
-- theorem is_alg_closed.splits_codomain {k K : Type*} [field k] [is_alg_closed k] [field K]
--   {f : K →+* k} (p : polynomial K) : p.splits f :=
-- by { convert is_alg_closed.splits (p.map f), simp [splits_map_iff] }

-- /-- Every polynomial splits in the field extension `f : K →+* k` if `K` is algebraically closed.

-- See also `is_alg_closed.splits_codomain` for the case where `k` is algebraically closed.
-- -/
-- theorem is_alg_closed.splits_domain {k K : Type*} [field k] [is_alg_closed k] [field K]
--   {f : k →+* K} (p : polynomial k) : p.splits f :=
-- polynomial.splits_of_splits_id _ $ is_alg_closed.splits _

-- namespace is_alg_closed

-- theorem of_exists_root (H : ∀ p : polynomial k, p.monic → irreducible p → ∃ x, p.eval x = 0) :
--   is_alg_closed k :=
-- ⟨λ p, or.inr $ λ q hq hqp,
--  have irreducible (q * C (leading_coeff q)⁻¹),
--    by { rw ← coe_norm_unit_of_ne_zero hq.ne_zero,
--         exact (associated_normalize _).irreducible hq },
--  let ⟨x, hx⟩ := H (q * C (leading_coeff q)⁻¹) (monic_mul_leading_coeff_inv hq.ne_zero) this in
--  degree_mul_leading_coeff_inv q hq.ne_zero ▸ degree_eq_one_of_irreducible_of_root this hx⟩

-- lemma degree_eq_one_of_irreducible [is_alg_closed k] {p : polynomial k} (h_nz : p ≠ 0)
--   (hp : irreducible p) :
--   p.degree = 1 :=
-- degree_eq_one_of_irreducible_of_splits h_nz hp (is_alg_closed.splits_codomain _)

-- lemma algebra_map_surjective_of_is_integral {k K : Type*} [field k] [domain K]
--   [hk : is_alg_closed k] [algebra k K] (hf : algebra.is_integral k K) :
--   function.surjective (algebra_map k K) :=
-- begin
--   refine λ x, ⟨-((minpoly k x).coeff 0), _⟩,
--   have hq : (minpoly k x).leading_coeff = 1 := minpoly.monic (hf x),
--   have h : (minpoly k x).degree = 1 := degree_eq_one_of_irreducible k
--     (minpoly.ne_zero (hf x)) (minpoly.irreducible (hf x)),
--   have : (aeval x (minpoly k x)) = 0 := minpoly.aeval k x,
--   rw [eq_X_add_C_of_degree_eq_one h, hq, C_1, one_mul,
--     aeval_add, aeval_X, aeval_C, add_eq_zero_iff_eq_neg] at this,
--   exact (ring_hom.map_neg (algebra_map k K) ((minpoly k x).coeff 0)).symm ▸ this.symm,
-- end

-- lemma algebra_map_surjective_of_is_integral' {k K : Type*} [field k] [integral_domain K]
--   [hk : is_alg_closed k] (f : k →+* K) (hf : f.is_integral) : function.surjective f :=
-- @algebra_map_surjective_of_is_integral k K _ _ _ f.to_algebra hf

-- lemma algebra_map_surjective_of_is_algebraic {k K : Type*} [field k] [domain K]
--   [hk : is_alg_closed k] [algebra k K] (hf : algebra.is_algebraic k K) :
--   function.surjective (algebra_map k K) :=
-- algebra_map_surjective_of_is_integral ((is_algebraic_iff_is_integral' k).mp hf)

-- end is_alg_closed

-- /-- Typeclass for an extension being an algebraic closure. -/
-- class is_alg_closure (K : Type v) [field K] [algebra k K] : Prop :=
-- (alg_closed : is_alg_closed K)
-- (algebraic : algebra.is_algebraic k K)

-- theorem is_alg_closure_iff (K : Type v) [field K] [algebra k K] :
--   is_alg_closure k K ↔ is_alg_closed K ∧ algebra.is_algebraic k K :=
-- ⟨λ h, ⟨h.1, h.2⟩, λ h, ⟨h.1, h.2⟩⟩

-- namespace algebraic_closure

-- open mv_polynomial

-- /-- The subtype of monic irreducible polynomials -/
-- @[reducible] def monic_irreducible : Type u :=
-- { f : polynomial k // monic f ∧ irreducible f }

-- /-- Sends a monic irreducible polynomial `f` to `f(x_f)` where `x_f` is a formal indeterminate. -/
-- def eval_X_self (f : monic_irreducible k) : mv_polynomial (monic_irreducible k) k :=
-- polynomial.eval₂ mv_polynomial.C (X f) f

-- /-- The span of `f(x_f)` across monic irreducible polynomials `f` where `x_f` is an
-- indeterminate. -/
-- def span_eval : ideal (mv_polynomial (monic_irreducible k) k) :=
-- ideal.span $ set.range $ eval_X_self k

-- /-- Given a finset of monic irreducible polynomials, construct an algebra homomorphism to the
-- splitting field of the product of the polynomials sending each indeterminate `x_f` represented by
-- the polynomial `f` in the finset to a root of `f`. -/
-- def to_splitting_field (s : finset (monic_irreducible k)) :
--   mv_polynomial (monic_irreducible k) k →ₐ[k] splitting_field (∏ x in s, x : polynomial k) :=
-- mv_polynomial.aeval $ λ f,
--   if hf : f ∈ s
--   then root_of_splits _
--     ((splits_prod_iff _ $ λ (j : monic_irreducible k) _, j.2.2.ne_zero).1
--       (splitting_field.splits _) f hf)
--     (mt is_unit_iff_degree_eq_zero.2 f.2.2.not_unit)
--   else 37

-- theorem to_splitting_field_eval_X_self {s : finset (monic_irreducible k)} {f} (hf : f ∈ s) :
--   to_splitting_field k s (eval_X_self k f) = 0 :=
-- by { rw [to_splitting_field, eval_X_self, ← alg_hom.coe_to_ring_hom, hom_eval₂,
--          alg_hom.coe_to_ring_hom, mv_polynomial.aeval_X, dif_pos hf,
--          ← algebra_map_eq, alg_hom.comp_algebra_map],
--   exact map_root_of_splits _ _ _ }

-- theorem span_eval_ne_top : span_eval k ≠ ⊤ :=
-- begin
--   rw [ideal.ne_top_iff_one, span_eval, ideal.span, ← set.image_univ,
--     finsupp.mem_span_image_iff_total],
--   rintros ⟨v, _, hv⟩,
--   replace hv := congr_arg (to_splitting_field k v.support) hv,
--   rw [alg_hom.map_one, finsupp.total_apply, finsupp.sum, alg_hom.map_sum, finset.sum_eq_zero] at hv,
--   { exact zero_ne_one hv },
--   intros j hj,
--   rw [smul_eq_mul, alg_hom.map_mul, to_splitting_field_eval_X_self k hj, mul_zero]
-- end

-- /-- A random maximal ideal that contains `span_eval k` -/
-- def max_ideal : ideal (mv_polynomial (monic_irreducible k) k) :=
-- classical.some $ ideal.exists_le_maximal _ $ span_eval_ne_top k

-- instance max_ideal.is_maximal : (max_ideal k).is_maximal :=
-- (classical.some_spec $ ideal.exists_le_maximal _ $ span_eval_ne_top k).1

-- theorem le_max_ideal : span_eval k ≤ max_ideal k :=
-- (classical.some_spec $ ideal.exists_le_maximal _ $ span_eval_ne_top k).2

-- /-- The first step of constructing `algebraic_closure`: adjoin a root of all monic polynomials -/
-- def adjoin_monic : Type u :=
-- (max_ideal k).quotient

-- instance adjoin_monic.field : field (adjoin_monic k) :=
-- ideal.quotient.field _

-- instance adjoin_monic.inhabited : inhabited (adjoin_monic k) := ⟨37⟩

-- /-- The canonical ring homomorphism to `adjoin_monic k`. -/
-- def to_adjoin_monic : k →+* adjoin_monic k :=
-- (ideal.quotient.mk _).comp C

-- instance adjoin_monic.algebra : algebra k (adjoin_monic k) :=
-- (to_adjoin_monic k).to_algebra

-- theorem adjoin_monic.algebra_map : algebra_map k (adjoin_monic k) = (ideal.quotient.mk _).comp C :=
-- rfl

-- theorem adjoin_monic.is_integral (z : adjoin_monic k) : is_integral k z :=
-- let ⟨p, hp⟩ := ideal.quotient.mk_surjective z in hp ▸
-- mv_polynomial.induction_on p (λ x, is_integral_algebra_map) (λ p q, is_integral_add)
--   (λ p f ih, @is_integral_mul _ _ _ _ _ _ (ideal.quotient.mk _ _) ih ⟨f, f.2.1,
--     by { erw [adjoin_monic.algebra_map, ← hom_eval₂,
--               ideal.quotient.eq_zero_iff_mem],
--       exact le_max_ideal k (ideal.subset_span ⟨f, rfl⟩) }⟩)

-- theorem adjoin_monic.exists_root {f : polynomial k} (hfm : f.monic) (hfi : irreducible f) :
--   ∃ x : adjoin_monic k, f.eval₂ (to_adjoin_monic k) x = 0 :=
-- ⟨ideal.quotient.mk _ $ X (⟨f, hfm, hfi⟩ : monic_irreducible k),
--  by { rw [to_adjoin_monic, ← hom_eval₂, ideal.quotient.eq_zero_iff_mem],
--       exact le_max_ideal k (ideal.subset_span $ ⟨_, rfl⟩) }⟩

-- /-- The `n`th step of constructing `algebraic_closure`, together with its `field` instance. -/
-- def step_aux (n : ℕ) : Σ α : Type u, field α :=
-- nat.rec_on n ⟨k, infer_instance⟩ $ λ n ih, ⟨@adjoin_monic ih.1 ih.2, @adjoin_monic.field ih.1 ih.2⟩

-- /-- The `n`th step of constructing `algebraic_closure`. -/
-- def step (n : ℕ) : Type u :=
-- (step_aux k n).1

-- instance step.field (n : ℕ) : field (step k n) :=
-- (step_aux k n).2

-- instance step.inhabited (n) : inhabited (step k n) := ⟨37⟩

-- /-- The canonical inclusion to the `0`th step. -/
-- def to_step_zero : k →+* step k 0 :=
-- ring_hom.id k

-- /-- The canonical ring homomorphism to the next step. -/
-- def to_step_succ (n : ℕ) : step k n →+* step k (n + 1) :=
-- @to_adjoin_monic (step k n) (step.field k n)

-- instance step.algebra_succ (n) : algebra (step k n) (step k (n + 1)) :=
-- (to_step_succ k n).to_algebra

-- theorem to_step_succ.exists_root {n} {f : polynomial (step k n)}
--   (hfm : f.monic) (hfi : irreducible f) :
--   ∃ x : step k (n + 1), f.eval₂ (to_step_succ k n) x = 0 :=
-- @adjoin_monic.exists_root _ (step.field k n) _ hfm hfi

-- /-- The canonical ring homomorphism to a step with a greater index. -/
-- def to_step_of_le (m n : ℕ) (h : m ≤ n) : step k m →+* step k n :=
-- { to_fun := nat.le_rec_on h (λ n, to_step_succ k n),
--   map_one' := begin
--     induction h with n h ih, { exact nat.le_rec_on_self 1 },
--     rw [nat.le_rec_on_succ h, ih, ring_hom.map_one]
--   end,
--   map_mul' := λ x y, begin
--     induction h with n h ih, { simp_rw nat.le_rec_on_self },
--     simp_rw [nat.le_rec_on_succ h, ih, ring_hom.map_mul]
--   end,
--   map_zero' := begin
--     induction h with n h ih, { exact nat.le_rec_on_self 0 },
--     rw [nat.le_rec_on_succ h, ih, ring_hom.map_zero]
--   end,
--   map_add' := λ x y, begin
--     induction h with n h ih, { simp_rw nat.le_rec_on_self },
--     simp_rw [nat.le_rec_on_succ h, ih, ring_hom.map_add]
--   end }

-- @[simp] lemma coe_to_step_of_le (m n : ℕ) (h : m ≤ n) :
--   (to_step_of_le k m n h : step k m → step k n) = nat.le_rec_on h (λ n, to_step_succ k n) :=
-- rfl

-- instance step.algebra (n) : algebra k (step k n) :=
-- (to_step_of_le k 0 n n.zero_le).to_algebra

-- instance step.scalar_tower (n) : is_scalar_tower k (step k n) (step k (n + 1)) :=
-- is_scalar_tower.of_algebra_map_eq $ λ z,
--   @nat.le_rec_on_succ (step k) 0 n n.zero_le (n + 1).zero_le (λ n, to_step_succ k n) z

-- theorem step.is_integral (n) : ∀ z : step k n, is_integral k z :=
-- nat.rec_on n (λ z, is_integral_algebra_map) $ λ n ih z,
--   is_integral_trans ih _ (adjoin_monic.is_integral (step k n) z : _)

-- instance to_step_of_le.directed_system :
--   directed_system (step k) (λ i j h, to_step_of_le k i j h) :=
-- ⟨λ i x h, nat.le_rec_on_self x, λ i₁ i₂ i₃ h₁₂ h₂₃ x, (nat.le_rec_on_trans h₁₂ h₂₃ x).symm⟩

-- end algebraic_closure

-- /-- The canonical algebraic closure of a field, the direct limit of adding roots to the field for
-- each polynomial over the field. -/
-- def algebraic_closure : Type u :=
-- ring.direct_limit (algebraic_closure.step k) (λ i j h, algebraic_closure.to_step_of_le k i j h)

-- namespace algebraic_closure

-- instance : field (algebraic_closure k) :=
-- field.direct_limit.field _ _

-- instance : inhabited (algebraic_closure k) := ⟨37⟩

-- /-- The canonical ring embedding from the `n`th step to the algebraic closure. -/
-- def of_step (n : ℕ) : step k n →+* algebraic_closure k :=
-- ring.direct_limit.of _ _ _

-- instance algebra_of_step (n) : algebra (step k n) (algebraic_closure k) :=
-- (of_step k n).to_algebra

-- theorem of_step_succ (n : ℕ) : (of_step k (n + 1)).comp (to_step_succ k n) = of_step k n :=
-- ring_hom.ext $ λ x, show ring.direct_limit.of (step k) (λ i j h, to_step_of_le k i j h) _ _ = _,
--   by { convert ring.direct_limit.of_f n.le_succ x, ext x, exact (nat.le_rec_on_succ' x).symm }

-- theorem exists_of_step (z : algebraic_closure k) : ∃ n x, of_step k n x = z :=
-- ring.direct_limit.exists_of z

-- -- slow
-- theorem exists_root {f : polynomial (algebraic_closure k)}
--   (hfm : f.monic) (hfi : irreducible f) :
--   ∃ x : algebraic_closure k, f.eval x = 0 :=
-- begin
--   have : ∃ n p, polynomial.map (of_step k n) p = f,
--   { convert ring.direct_limit.polynomial.exists_of f },
--   unfreezingI { obtain ⟨n, p, rfl⟩ := this },
--   rw monic_map_iff at hfm,
--   have := hfm.irreducible_of_irreducible_map (of_step k n) p hfi,
--   obtain ⟨x, hx⟩ := to_step_succ.exists_root k hfm this,
--   refine ⟨of_step k (n + 1) x, _⟩,
--   rw [← of_step_succ k n, eval_map, ← hom_eval₂, hx, ring_hom.map_zero]
-- end

-- instance : is_alg_closed (algebraic_closure k) :=
-- is_alg_closed.of_exists_root _ $ λ f, exists_root k

-- instance {R : Type*} [comm_semiring R] [alg : algebra R k] :
--   algebra R (algebraic_closure k) :=
-- ((of_step k 0).comp (@algebra_map _ _ _ _ alg)).to_algebra

-- lemma algebra_map_def {R : Type*} [comm_semiring R] [alg : algebra R k] :
--   algebra_map R (algebraic_closure k) = ((of_step k 0 : k →+* _).comp (@algebra_map _ _ _ _ alg)) :=
-- rfl

-- instance {R S : Type*} [comm_semiring R] [comm_semiring S]
--   [algebra R S] [algebra S k] [algebra R k] [is_scalar_tower R S k] :
--   is_scalar_tower R S (algebraic_closure k) :=
-- is_scalar_tower.of_algebra_map_eq (λ x,
--   ring_hom.congr_arg _ (is_scalar_tower.algebra_map_apply R S k x : _))

-- /-- Canonical algebra embedding from the `n`th step to the algebraic closure. -/
-- def of_step_hom (n) : step k n →ₐ[k] algebraic_closure k :=
-- { commutes' := λ x, ring.direct_limit.of_f n.zero_le x,
--   .. of_step k n }

-- theorem is_algebraic : algebra.is_algebraic k (algebraic_closure k) :=
-- λ z, (is_algebraic_iff_is_integral _).2 $ let ⟨n, x, hx⟩ := exists_of_step k z in
-- hx ▸ is_integral_alg_hom (of_step_hom k n) (step.is_integral k n x)

-- instance : is_alg_closure k (algebraic_closure k) :=
-- ⟨algebraic_closure.is_alg_closed k, is_algebraic k⟩

-- end algebraic_closure

-- /--
-- Every element `f` in a nontrivial finite-dimensional algebra `A`
-- over an algebraically closed field `K`
-- has non-empty spectrum:
-- that is, there is some `c : K` so `f - c • 1` is not invertible.
-- -/
-- -- We will use this both to show eigenvalues exist, and to prove Schur's lemma.
-- lemma exists_spectrum_of_is_alg_closed_of_finite_dimensional (𝕜 : Type*) [field 𝕜] [is_alg_closed 𝕜]
--   {A : Type*} [nontrivial A] [ring A] [algebra 𝕜 A] [I : finite_dimensional 𝕜 A] (f : A) :
--   ∃ c : 𝕜, ¬ is_unit (f - algebra_map 𝕜 A c) :=
-- begin
--   obtain ⟨p, ⟨h_mon, h_eval_p⟩⟩ := is_integral_of_noetherian I f,
--   have nu : ¬ is_unit (aeval f p), { rw [←aeval_def] at h_eval_p, rw h_eval_p, simp, },
--   rw [eq_prod_roots_of_monic_of_splits_id h_mon (is_alg_closed.splits p),
--     ←multiset.prod_to_list, alg_hom.map_list_prod] at nu,
--   replace nu := mt list.prod_is_unit nu,
--   simp only [not_forall, exists_prop, aeval_C, multiset.mem_to_list,
--     list.mem_map, aeval_X, exists_exists_and_eq_and, multiset.mem_map, alg_hom.map_sub] at nu,
--   exact ⟨nu.some, nu.some_spec.2⟩,
-- end
