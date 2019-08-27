/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import algebra.direct_limit
import set_theory.schroeder_bernstein
import field_theory.minimal_polynomial

universes u v w
open polynomial zorn set function
variables {K : Type u} [discrete_field K]
noncomputable theory

/- Turn down the instance priority for subtype.decidable_eq and use classical.dec_eq everywhere,
  to avoid diamonds -/
local attribute [instance, priority 0] subtype.decidable_eq

lemma injective_eq {α : Sort*} : injective (eq : α → α → Prop) :=
λ _ _ h, h.symm ▸ rfl

@[instance] lemma equiv.is_ring_hom {α β : Type*} [ring β] (e : α ≃ β) :
  @is_ring_hom β α _ (equiv.ring e) e.symm :=
by split; simp [equiv.mul_def, equiv.add_def, equiv.one_def]

instance equiv.is_ring_hom.symm {α β : Type*} [ring β] (e : α ≃ β) :
  @is_ring_hom α β (equiv.ring e) _ e :=
by split; simp [equiv.mul_def, equiv.add_def, equiv.one_def]

def equiv.ring_equiv {α β : Type*} [ring β] (e : α ≃ β) :
  @ring_equiv α β (equiv.ring e) _ :=
{ hom := by apply_instance, ..e }

lemma exists_root_of_equiv {α β : Type*} [comm_ring α] [comm_ring β] [decidable_eq α]
  [decidable_eq β] (e : α ≃r β) {f : polynomial α} {x : β} (hx : f.eval₂ e.to_equiv x = 0) :
  f.eval (e.symm.to_equiv x) = 0 :=
begin
  letI : is_ring_hom e.to_equiv := e.hom,
  rw [← e.to_equiv.injective.eq_iff,
    ← eval₂_hom e.to_equiv, ring_equiv.to_equiv_symm,
    equiv.apply_symm_apply, is_ring_hom.map_zero e.to_equiv, hx],
end

namespace polynomial
variables {α : Type*} {β : Type*} {γ : Type*}
variables [decidable_eq α] [comm_semiring α] [comm_semiring β] [comm_semiring γ]
variables (f : α → β) (g : β → γ) [is_semiring_hom f] [is_semiring_hom g] (p : polynomial α) (x : β)

lemma hom_eval₂ : g (p.eval₂ f x) = p.eval₂ (g ∘ f) (g x) :=
begin
  apply polynomial.induction_on p; clear p,
  { intros a, rw [eval₂_C, eval₂_C] },
  { intros p q hp hq, simp only [hp, hq, eval₂_add, is_semiring_hom.map_add g] },
  { intros n a ih,
    simp only [pow_succ', is_semiring_hom.map_mul g, (mul_assoc _ _ _).symm,
      eval₂_C, eval₂_mul, eval₂_X] at ih ⊢,
    rw ih }
end


end polynomial

namespace alg_hom
variables {α : Type u} {β : Type v} {γ : Type w} [comm_ring α] [ring β] [ring γ]
  [algebra α β] [algebra α γ] (f : β →ₐ[α] γ)

def inverse (g : γ → β) (h₁ : left_inverse g f) (h₂ : right_inverse g f) : γ →ₐ[α] β :=
by dsimp [left_inverse, function.right_inverse] at h₁ h₂; exact
{ to_fun := g,
  hom := show is_ring_hom g, from
  { map_add := λ x y, by rw [← h₁ (g x + g y), f.map_add, h₂, h₂],
    map_mul := λ x y, by rw [← h₁ (g x * g y), f.map_mul, h₂, h₂],
    map_one := by rw [← h₁ 1, f.map_one] },
  commutes' := λ a, by rw [← h₁ (algebra_map β a), f.commutes] }

instance quotient.algebra (I : ideal α) : algebra α I.quotient :=
algebra.of_ring_hom (ideal.quotient.mk I) (ideal.quotient.is_ring_hom_mk I)

def induced_quotient_map (I J : ideal α) (h : I ≤ J) :
  I.quotient →ₐ[α] J.quotient :=
{ to_fun := ideal.quotient.lift I (ideal.quotient.mk J) $
  by { intros i hi, erw submodule.quotient.mk_eq_zero, exact h hi },
  commutes' := λ a, by { erw ideal.quotient.lift_mk, refl } }

end alg_hom

set_option old_structure_cmd true

structure alg_equiv (α β γ : Type*) [comm_ring α] [ring β] [ring γ]
  [algebra α β] [algebra α γ] extends alg_hom α β γ, equiv β γ

set_option old_structure_cmd false

infix ` ≃ₐ `:25 := alg_equiv _
notation A ` ≃ₐ[`:25 R `] ` B := alg_equiv R A B

namespace alg_equiv
variables {α : Type u} {β : Type v} {γ : Type w} [comm_ring α] [ring β] [ring γ]
  [algebra α β] [algebra α γ]

protected def refl : β ≃ₐ[α] β :=
{ hom := is_ring_hom.id,
  commutes' := λ b, rfl,
  .. equiv.refl β }

protected def symm (e : β ≃ₐ[α] γ) : γ ≃ₐ[α] β :=
{ .. e.to_alg_hom.inverse e.inv_fun e.left_inv e.right_inv,
  .. e.to_equiv.symm }

-- TODO: trans

end alg_equiv

namespace adjoin_root
variables {α : Type*} [comm_ring α] [decidable_eq α] (f : polynomial α)

instance : algebra α (adjoin_root f) :=
algebra.of_ring_hom coe $ by apply_instance

lemma fg_of_monic (hf : f.monic) : submodule.fg (⊤ : submodule α (adjoin_root f)) :=
begin
  refine ⟨(finset.range (f.nat_degree + 1)).image (λ i, adjoin_root.mk (X^i)), _⟩,
  rw submodule.eq_top_iff',
  intro a,
  apply quotient.induction_on' a,
  intro p, show mk p ∈ _,
  rw [← mod_by_monic_add_div p hf, is_ring_hom.map_add mk, is_ring_hom.map_mul mk],
  { refine submodule.add_mem _ _ _,
    { apply_instance },
    { rw [(p %ₘ f).as_sum, ← finset.sum_hom mk],
      { refine submodule.sum_mem _ _,
        intros i hi,
        rw [is_ring_hom.map_mul mk],
        { show algebra_map _ (coeff (p %ₘ f) i) * _ ∈ _,
          rw ← algebra.smul_def,
          refine submodule.smul_mem _ _ (submodule.subset_span _),
          rw [finset.mem_coe, finset.mem_image],
          refine ⟨i, _, rfl⟩,
          rw finset.mem_range at hi ⊢,
          refine lt_of_lt_of_le hi (nat.succ_le_succ _),
          by_cases (p %ₘ f) = 0, { simp [h] },
          rw ← with_bot.coe_le_coe,
          rw ← degree_eq_nat_degree h,
          apply le_trans (degree_mod_by_monic_le p hf),
          exact degree_le_nat_degree },
        { apply_instance } },
      { apply_instance } },
    { convert submodule.zero_mem _,
      convert zero_mul _ using 2,
      erw [submodule.quotient.mk_eq_zero _],
      apply submodule.subset_span,
      exact mem_singleton _ } },
  all_goals { apply_instance }
end

lemma fg {f : polynomial K} (hf : f ≠ 0) : submodule.fg (⊤ : submodule K (adjoin_root f)) :=
begin
  have := fg_of_monic _ (monic_mul_leading_coeff_inv hf),
  convert submodule.fg_map this, swap,
  { apply alg_hom.to_linear_map,
    sorry
    -- I would like to use alg_hom.induced_quotient_map here
     },
  sorry
end

end adjoin_root

section thing

local attribute [instance] classical.dec

private lemma thing_aux {X : Type u} {Y : Type v} {Z : Type w} (fxy : X ↪ Y) (fxz : X ↪ Z)
  (hYZ : (Z ↪ Y) → false) : ↥-range fxy.1 ↪ ↥-range fxz.1 :=
classical.choice $ or.resolve_left embedding.total $
  λ ⟨f⟩, hYZ $
    calc Z ↪ range fxz ⊕ ↥-range fxz :
      (equiv.set.sum_compl _).symm.to_embedding
    ... ↪ range fxy ⊕ ↥-range fxy :
      embedding.sum_congr
        (((equiv.set.range _ fxz.2).symm.to_embedding).trans
          (equiv.set.range _ fxy.2).to_embedding)
        f
    ... ↪ Y : (equiv.set.sum_compl _).to_embedding

private def thing {X : Type u} {Y : Type v} {Z : Type w} (fxy : X ↪ Y) (fxz : X ↪ Z)
  (hYZ : (Z ↪ Y) → false) : Y ↪ Z :=
calc Y ↪ range fxy ⊕ ↥-range fxy : (equiv.set.sum_compl _).symm.to_embedding
... ↪ range fxz ⊕ ↥-range fxz : embedding.sum_congr
  ((equiv.set.range _ fxy.2).symm.to_embedding.trans
    (equiv.set.range _ fxz.2).to_embedding)
  (thing_aux fxy fxz hYZ)
... ↪ Z : (equiv.set.sum_compl _).to_embedding

private lemma thing_commutes {X : Type u} {Y : Type v} {Z : Type w}  (fxy : X ↪ Y) (fxz : X ↪ Z)
  (hYZ : (Z ↪ Y) → false) (x : X) : thing fxy fxz hYZ (fxy x) = fxz x :=
have (⟨fxy x, mem_range_self _⟩ : range fxy) = equiv.set.range _ fxy.2 x, from rfl,
begin
  dsimp only [thing, embedding.trans_apply, equiv.trans_apply, function.comp,
    equiv.to_embedding_coe_fn],
  simp only [equiv.set.sum_compl_symm_apply_of_mem (mem_range_self _),
    embedding.sum_congr_apply_inl, equiv.set.sum_compl_apply_inl,
    embedding.trans_apply, equiv.to_embedding_coe_fn, this, equiv.symm_apply_apply],
  refl
end

end thing

class is_algebraically_closed (K : Type u) [nonzero_comm_ring K] [decidable_eq K] :=
(exists_root : ∀ f : polynomial K, 0 < degree f → ∃ x, is_root f x)

section is_algebraically_closed

lemma is_algebraically_closed_of_irreducible_has_root
  (h : ∀ f : polynomial K, irreducible f → ∃ x, is_root f x) :
  is_algebraically_closed K :=
⟨λ f hf0, let ⟨g, hg⟩ := is_noetherian_ring.exists_irreducible_factor
  (show ¬ is_unit f, from λ h, by rw [is_unit_iff_degree_eq_zero] at h;
    rw h at hf0; exact lt_irrefl _ hf0)
  (λ h, by rw ← degree_eq_bot at h;
    rw h at hf0; exact absurd hf0 dec_trivial) in
  let ⟨x, hx⟩ := h g hg.1 in
  let ⟨i, hi⟩ := hg.2 in
  ⟨x, by rw [hi, is_root.def, eval_mul, show _ = _, from hx, zero_mul]⟩⟩

-- /- An algebraic extension of -/
-- lemma equiv_of_algebraic

end is_algebraically_closed

--move this
namespace polynomial
variables (R : Type u) (A : Type v)
variables [comm_ring R] [comm_ring A] [algebra R A]
variables [decidable_eq R] (x : A)

@[simp] lemma aeval_X : aeval R A x X = x := eval₂_X _ x

@[simp] lemma aeval_C (r : R) : aeval R A x (C r) = algebra_map A r := eval₂_C _ x

end polynomial

namespace algebraic_closure

section classical

local attribute [instance, priority 1] classical.dec

/-- The `big_type` with cardinality strictly larger than any algebraic extension -/
private def big_type (K : Type u) [discrete_field K] := set (ℕ × polynomial K)

private def algebraic_embedding_aux {L : Type*} [discrete_field L] [algebra K L]
  (h : ∀ l : L, is_integral K l) (x : L) : ℕ × polynomial K :=
let f := classical.some (h x) in
⟨list.index_of x (quotient.out ((f.map (algebra_map L)).roots.1)), f⟩

private lemma algebraic_embedding_aux_injective
  {L : Type*} [discrete_field L] [algebra K L]
  (h : ∀ l : L, is_integral K l) : injective (algebraic_embedding_aux h) :=
λ x y hxy,
let f := classical.some (h x) in
let g := classical.some (h y) in
have hf : monic f ∧ aeval K L x f = 0, from classical.some_spec (h x),
have hg : monic g ∧ aeval K L y g = 0, from classical.some_spec (h y),
have hfg : f = g, from (prod.ext_iff.1 hxy).2,
have hfg' : list.index_of x (quotient.out ((f.map (algebra_map L)).roots.1)) =
    list.index_of y (quotient.out ((f.map (algebra_map L)).roots.1)),
  from (prod.ext_iff.1 hxy).1.trans (hfg.symm ▸ rfl),
have hx : x ∈ quotient.out ((f.map (algebra_map L)).roots.1),
  from multiset.mem_coe.1 begin
    show x ∈ quotient.mk _,
    rw [quotient.out_eq, ← finset.mem_def, mem_roots (mt (map_eq_zero (algebra_map L)).1
      (ne_zero_of_monic hf.1)), is_root.def, eval_map, ← aeval_def, hf.2],
  end,
have hy : y ∈ quotient.out ((g.map (algebra_map L)).roots.1),
  from multiset.mem_coe.1 begin
    show y ∈ quotient.mk _,
    rw [quotient.out_eq, ← finset.mem_def, mem_roots (mt (map_eq_zero (algebra_map L)).1
      (ne_zero_of_monic hg.1)), is_root.def, eval_map, ← aeval_def, hg.2],
  end,
(list.index_of_inj hx (by rwa hfg)).1 hfg'

private def algebraic_embedding_big_type {L : Type*} [discrete_field L] [algebra K L]
  (h : ∀ l : L, is_integral K l) : L ↪ big_type K :=
⟨_, injective_comp injective_eq $ algebraic_embedding_aux_injective h⟩

private def algebraic_embedding {L : Type*} [discrete_field L] [algebra K L]
  (h : ∀ l : L, is_integral K l) : L ↪ ℕ × polynomial K :=
⟨_, algebraic_embedding_aux_injective h⟩

private def bembedding (K : Type u) [discrete_field K] : K ↪ big_type K :=
⟨λ a, show set _, from {(0, X - C a)}, λ a b, by simp [C_inj]⟩

instance range_bembedding.discrete_field : discrete_field (set.range (bembedding K)) :=
equiv.discrete_field (equiv.set.range _ (bembedding K).2).symm

private structure extension (K : Type u) [discrete_field K] : Type u :=
(carrier : set (big_type K))
[field : discrete_field ↥carrier]
[algebra : algebra K ↥carrier]
(algebraic : ∀ x : carrier, is_integral K x)

attribute [instance] extension.field extension.algebra

private def base_extension (K : Type u) [discrete_field K] : extension K :=
{ carrier := set.range (bembedding K),
  algebra := algebra.of_ring_hom (equiv.set.range _ (bembedding K).2).symm.symm
    (by apply_instance),
  algebraic :=
  begin
    rintro ⟨_, x, rfl⟩,
    refine ⟨X + C (-x), monic_X_add_C (-x), _⟩,
    rw [alg_hom.map_add, C_neg, alg_hom.map_neg, polynomial.aeval_X, polynomial.aeval_C],
    exact add_neg_self _
  end }

/-- not used but might help with sorries -/
private def extension.of_algebraic {L : Type v} [discrete_field L] [algebra K L]
  (hL : ∀ x : L, is_integral K x) : extension K :=
{ carrier := set.range (algebraic_embedding_big_type hL),
  field := equiv.discrete_field (equiv.set.range _ (algebraic_embedding_big_type hL).2).symm,
  algebra := sorry, -- a field isomorphic to an algebra is an algebra
  algebraic := sorry -- a field isomorphic to an algebraic extension is algebraic
  }

instance : preorder (extension K) :=
{ le := λ L M, ∃ hLM : L.carrier ⊆ M.carrier, is_ring_hom (inclusion hLM),
  le_refl := λ _, ⟨set.subset.refl _, by convert is_ring_hom.id; ext; simp⟩,
  le_trans := λ L M N ⟨hLM₁, hLM₂⟩ ⟨hMN₁, hMN₂⟩, ⟨set.subset.trans hLM₁ hMN₁,
    by resetI; convert is_ring_hom.comp (inclusion hLM₁) (inclusion hMN₁)⟩ }

private structure chain' (c : set (extension K)) : Prop :=
(chain : chain (≤) c)

local attribute [class] chain'

private lemma is_chain (c : set (extension K)) [chain' c]: chain (≤) c :=
chain'.chain (by apply_instance)

section chain

variables (c : set (extension K)) [hcn : nonempty c]
include c  hcn

variable [hcn' : chain' c]
include hcn'

instance chain_directed_order : directed_order c :=
⟨λ ⟨i, hi⟩ ⟨j, hj⟩, let ⟨k, hkc, hk⟩ := chain.directed_on
  (is_chain c) i hi j hj in ⟨⟨k, hkc⟩, hk⟩⟩

private def chain_map (i j : c) (hij : i ≤ j) : i.1.carrier → j.1.carrier :=
inclusion (exists.elim hij (λ h _, h))

instance chain_field_hom (i j : c) (hij : i ≤ j) : is_field_hom (chain_map c i j hij) :=
exists.elim hij (λ _, id)

instance chain_directed_system : directed_system (λ i : c, i.1.carrier) (chain_map c) :=
by split; intros; simp [chain_map]

private def chain_limit : Type u := ring.direct_limit (λ i : c, i.1.carrier) (chain_map c)

private lemma of_eq_of (x : big_type K) (i j : c) (hi : x ∈ i.1.carrier) (hj : x ∈ j.1.carrier) :
  ring.direct_limit.of (λ i : c, i.1.carrier) (chain_map c) i ⟨x, hi⟩ =
  ring.direct_limit.of (λ i : c, i.1.carrier) (chain_map c) j ⟨x, hj⟩ :=
have hij : i ≤ j ∨ j ≤ i,
  from show i.1 ≤ j.1 ∨ j.1 ≤ i.1, from chain.total (is_chain c) i.2 j.2,
hij.elim
  (λ hij, begin
    rw ← @ring.direct_limit.of_f c _ _ _ (λ i : c, i.1.carrier) _ _ (chain_map c) _
      _ _ _ hij,
    simp [chain_map, inclusion]
  end)
  (λ hij, begin
    rw ← @ring.direct_limit.of_f c _ _ _ (λ i : c, i.1.carrier) _ _ (chain_map c) _
      _ _ _ hij,
    simp [chain_map, inclusion]
  end)

private lemma injective_aux (i j : c)
  (x y : ⋃ i : c, i.1.carrier) (hx : x.1 ∈ i.1.carrier) (hy : y.1 ∈ j.1.carrier) :
  ring.direct_limit.of (λ i : c, i.1.carrier) (chain_map c) i ⟨x, hx⟩ =
  ring.direct_limit.of (λ i : c, i.1.carrier) (chain_map c) j ⟨y, hy⟩ →
  x = y :=
have hij : i ≤ j ∨ j ≤ i,
  from show i.1 ≤ j.1 ∨ j.1 ≤ i.1, from chain.total (is_chain c) i.2 j.2,
have hinj : ∀ (i j : c) (hij : i ≤ j), injective (chain_map c i j hij),
  from λ _ _ _, is_field_hom.injective _,
hij.elim
  (λ hij h, begin
    rw ← @ring.direct_limit.of_f c _ _ _ (λ i : c, i.1.carrier) _ _ (chain_map c) _
      _ _ _ hij at h,
    simpa [chain_map, inclusion, subtype.coe_ext.symm] using ring.direct_limit.of_inj hinj j h,
  end)
  (λ hji h, begin
    rw ← @ring.direct_limit.of_f c _ _ _ (λ i : c, i.1.carrier) _ _ (chain_map c) _
      _ _ _ hji at h,
    simpa [chain_map, inclusion, subtype.coe_ext.symm] using ring.direct_limit.of_inj hinj i h,
  end)

private def equiv_direct_limit : (⋃ (i : c), i.1.carrier) ≃
  ring.direct_limit (λ i : c, i.1.carrier) (chain_map c) :=
@equiv.of_bijective (⋃ i : c, i.1.carrier)
  (ring.direct_limit (λ i : c, i.1.carrier) (chain_map c))
  (λ x, ring.direct_limit.of _ _ (classical.some (set.mem_Union.1 x.2))
    ⟨_, classical.some_spec (set.mem_Union.1 x.2)⟩)
  ⟨λ x y, injective_aux _ _ _ _ _ _ _,
    λ x, let ⟨i, ⟨y, hy⟩, hy'⟩ := ring.direct_limit.exists_of x in
      ⟨⟨y, _, ⟨i, rfl⟩, hy⟩, begin
        convert hy',
        exact of_eq_of _ _ _ _ _ _
      end⟩⟩

instance Union_field : discrete_field (⋃ i : c, i.1.carrier) :=
@equiv.discrete_field _ _ (equiv_direct_limit c)
  (field.direct_limit.discrete_field _ _)

set_option class.instance_max_depth 50

instance is_field_hom_Union (i : c) : is_field_hom
  (inclusion (set.subset_Union (λ i : c, i.1.carrier) i)) :=
suffices inclusion (set.subset_Union (λ i : c, i.1.carrier) i) =
    ((equiv_direct_limit c).symm ∘
    ring.direct_limit.of (λ i : c, i.1.carrier) (chain_map c) i),
  by rw this; exact is_ring_hom.comp _ _,
funext $ λ ⟨_, _⟩,
  (equiv_direct_limit c).injective $
    by rw [function.comp_app, equiv.apply_symm_apply];
      exact of_eq_of _ _ _ _ _ _

end chain

--def maximal_extension (c : set (extension K)) (hc : chain (≤) c) : extension K :=

private def maximal_extension_chain (c : set (extension K)) (hc : chain (≤) c) :
  { ub : extension K // ∀ L, L ∈ c → L ≤ ub } :=
if h : nonempty c
  then
  let L := classical.some (classical.exists_true_of_nonempty h) in
  by letI : chain' c := ⟨hc⟩; exact
    ⟨{ carrier := ⋃ (i : c), i.1.carrier,
        algebra :=
          algebra.of_ring_hom ((inclusion (set.subset_Union (λ i : c, i.1.carrier) L)) ∘ algebra_map _)
          (by { refine @is_ring_hom.comp _ _ _ _ _ _ _ _ _ _ }),
        algebraic :=
        begin
          rintro ⟨x, hx⟩,
          rw mem_Union at hx,
          cases hx with L' hx,
          rcases (L'.val).algebraic ⟨x, hx⟩ with ⟨p, pmonic, hp⟩,
          use [p, pmonic],
          rw aeval_def at hp ⊢,
          sorry,
        end }, -- Field is isomorphic to direct limit of some algebraic extensions
    λ e he, ⟨by convert subset_Union _ (⟨e, he⟩ : c); refl,
      algebraic_closure.is_field_hom_Union c ⟨e, he⟩⟩⟩
  else ⟨base_extension K, λ a ha, (h ⟨⟨a, ha⟩⟩).elim⟩

section adjoin_root
variables {L : extension K} (f : polynomial L.carrier) [hif : irreducible f]
include hif

instance adjoin_root_algebraic_closure.field :
  discrete_field (adjoin_root f) := adjoin_root.field

instance adjoin_root_algebraic_closure.is_ring_hom :
  is_ring_hom (@adjoin_root.of _ _ _ f) := adjoin_root.is_ring_hom

private def adjoin_root.of_embedding : L.carrier ↪ adjoin_root f :=
⟨adjoin_root.of, @is_field_hom.injective _ _ _ _ _ $ adjoin_root_algebraic_closure.is_ring_hom f⟩

variable (K)

def aux_instance : algebra K (adjoin_root f) :=
algebra.of_ring_hom (adjoin_root.of ∘ algebra_map _) (is_ring_hom.comp _ _)

local attribute [instance] aux_instance

lemma adjoin_root.algebraic (x : adjoin_root f) : is_integral K x :=
begin
  sorry
end

private def adjoin_root_extension_map : adjoin_root f ↪ big_type K :=
thing (adjoin_root.of_embedding f) ⟨subtype.val, subtype.val_injective⟩
  (λ i, let e : big_type K ↪ ℕ × polynomial K := i.trans
      (algebraic_embedding (adjoin_root.algebraic K f)) in
    cantor_injective e.1 e.2)

private lemma adjoin_root_extension_map_apply (x : L.carrier) :
  (adjoin_root_extension_map K f) (@adjoin_root.of _ _ _ f x) = x.val :=
thing_commutes _ _ _ _

instance range_adjoin_root_extension_map.discrete_field :
  discrete_field (set.range (@adjoin_root_extension_map K _ _ f _)) :=
equiv.discrete_field (equiv.set.range _ (embedding.inj _)).symm

private def adjoin_root_extension : extension K :=
{ carrier := set.range (@adjoin_root_extension_map K _ _ f _),
  algebra := algebra.of_ring_hom
    ((equiv.set.range _ (embedding.inj' (adjoin_root_extension_map K f))).symm.symm ∘
      algebra_map _) (is_ring_hom.comp _ _),
  algebraic :=
  begin
    rintro ⟨_, x, rfl⟩,
    rcases adjoin_root.algebraic K f x with ⟨p, pmonic, hp⟩,
    use [p, pmonic],
    rw [aeval_def] at hp ⊢,
    replace hp := congr_arg
      ((equiv.set.range _ (embedding.inj' (adjoin_root_extension_map K f))).symm.symm) hp,
    convert hp using 1,
    symmetry,
    convert polynomial.hom_eval₂ _ _ _ _,
    all_goals {apply_instance}
  end }

variable {L}
private lemma subset_adjoin_root_extension : L.carrier ⊆ (adjoin_root_extension K f).carrier :=
λ x h, ⟨adjoin_root.of_embedding f ⟨x, h⟩, thing_commutes _ _ _ _⟩

private lemma adjoin_root_inclusion_eq : inclusion (subset_adjoin_root_extension K f) =
  ((equiv.set.range _ (adjoin_root_extension_map K f).2).symm.symm ∘ adjoin_root.of_embedding f) :=
funext $ λ ⟨_, _⟩, subtype.eq $ eq.symm $ adjoin_root_extension_map_apply _ _ _

private lemma le_adjoin_root_extension : L ≤ adjoin_root_extension K f :=
⟨subset_adjoin_root_extension K f,
  by rw [adjoin_root_inclusion_eq]; dsimp [adjoin_root.of_embedding]; exact is_ring_hom.comp _ _⟩

private def equiv_adjoin_root_of_le (h : adjoin_root_extension K f ≤ L) :
  L.carrier ≃r adjoin_root f :=
have left_inv : left_inverse (inclusion h.fst ∘ (equiv.set.range _
    (adjoin_root_extension_map K f).2)) adjoin_root.of,
  from λ _, by simp [adjoin_root_extension_map_apply, inclusion],
{ to_fun := coe,
  inv_fun := inclusion h.fst ∘ (equiv.set.range _ (adjoin_root_extension_map K f).2),
  left_inv := left_inv,
  right_inv := right_inverse_of_injective_of_left_inverse
    (injective_comp (inclusion_injective _) (equiv.injective _))
    left_inv,
  hom := by apply_instance }

private def adjoin_root_equiv_adjoin_root_extension : adjoin_root f ≃r (adjoin_root_extension K f).carrier :=
(equiv.set.range _ (adjoin_root_extension_map K f).2).symm.ring_equiv.symm

end adjoin_root

private lemma exists_algebraic_closure (K : Type u) [discrete_field K] :
  ∃ m : extension K, ∀ a, m ≤ a → a ≤ m :=
zorn (λ c hc, (maximal_extension_chain c hc).exists_of_subtype) (λ _ _ _, le_trans)

private def closed_extension (K : Type u) [discrete_field K] :=
classical.some (exists_algebraic_closure K)

def algebraic_closure (K : Type u) [discrete_field K] : Type u :=
((classical.some (exists_algebraic_closure K))).carrier

end classical

section is_algebraically_closed
/- In this section we prove the algebraic closure is algebraically closed -/

local attribute [reducible] algebraic_closure

variables (f : polynomial (algebraic_closure K)) [hif : irreducible f]
include hif

variable (K)

def algebraic_closure_equiv_adjoin_root : algebraic_closure K ≃r adjoin_root f :=
equiv_adjoin_root_of_le K f $
  classical.some_spec (exists_algebraic_closure K) _ (le_adjoin_root_extension _ _)

instance ring_equiv.is_semiring_hom {α β : Type*} [ring α] [ring β] (e : α ≃r β) :
  is_semiring_hom (e.to_equiv : α → β) :=
is_ring_hom.is_semiring_hom _

omit hif

private def is_algebraically_closed_aux : is_algebraically_closed (algebraic_closure K) :=
is_algebraically_closed_of_irreducible_has_root $
λ f hf, let e := by exactI algebraic_closure_equiv_adjoin_root K f in
⟨_, exists_root_of_equiv e (adjoin_root.eval₂_root f)⟩

end is_algebraically_closed

/- To avoid diamonds, the `decidable_eq` instance is set to `classical.dec_eq`,
  as opposed to the (noncomputable, but not def-eq to `classical.dec_eq`) instance given by
  `(closed_extension K).field` -/
instance : discrete_field (algebraic_closure K) :=
{ has_decidable_eq := classical.dec_eq _,
  ..(closed_extension K).field }

instance : algebra K (algebraic_closure K) := (closed_extension K).algebra

instance : is_algebraically_closed (algebraic_closure K) :=
by convert is_algebraically_closed_aux K

protected def is_integral : ∀ x : algebraic_closure K, is_integral K x :=
(closed_extension K).algebraic

attribute [irreducible] algebraic_closure closed_extension algebraic_closure.algebra

section lift
/- In this section, the homomorphism from any algebraic extension into an algebraically
  closed extension is proven to exist. The assumption that M is algebraically closed could probably
  easily be switched to an assumption that M contains all the roots of polynomials in K -/
variables {L : Type v} {M : Type w} [discrete_field L] [algebra K L]
  [discrete_field M] [algebra K M] [is_algebraically_closed M] (hL : ∀ x : L, is_integral K x)

/-- This structure is used to prove the existence of a homomorphism from any algebraic extension
  into an algebraic closure -/
variables (K L M)
include hL

private structure subfield_and_hom extends extension K :=
( to_algebraically_closed : carrier →ₐ[K] M )
( to_field : carrier →ₐ[K] L )

variables {K L M}

instance subfield_and_hom.preorder : preorder (subfield_and_hom K L M hL) :=
preorder.lift subfield_and_hom.to_extension (by apply_instance)

private def maximal_subfield_and_hom_chain (c : set (subfield_and_hom K L M hL)) (hc : chain (≤) c) :
  ∃ ub : subfield_and_hom K L M hL, ∀ N, N ∈ c → N ≤ ub :=
let ub := (maximal_extension_chain (subfield_and_hom.to_extension '' c) (chain.image (≤) _ _ (λ _ _, id) hc)) in
⟨{ to_algebraically_closed := sorry, --field in question is direct limit of a bunch of fields with
      --algebra homs into M
    to_field := sorry, -- direct limit of a bunch of subfields is also a subfield
    ..ub.1 },
   λ n hN, ub.2 _ (mem_image_of_mem _ hN)⟩

private lemma exists_maximal_subfield_and_hom : ∃ N : subfield_and_hom K L M hL,
  ∀ O, N ≤ O → O ≤ N :=
zorn (maximal_subfield_and_hom_chain _) (λ _ _ _, le_trans)

variable (M)

private def maximal_subfield_and_hom : subfield_and_hom K L M hL :=
classical.some (exists_maximal_subfield_and_hom hL)

instance akgh : algebra (maximal_subfield_and_hom M hL).carrier L :=
algebra.of_ring_hom (maximal_subfield_and_hom M hL).to_field (by apply_instance)

-- Given K:L:M, if M is algebraic over K it is algebraic over L (names are different)
private lemma is_integral_over_maximal (x : L) : is_integral (maximal_subfield_and_hom M hL).carrier x := sorry

variables (f : polynomial (maximal_subfield_and_hom M hL).carrier) [hif : irreducible f]
  {x : L} (hxf : f.eval₂ (maximal_subfield_and_hom M hL).to_field x = 0)

include hif hxf

private def adjoin_root_subfield_and_hom : subfield_and_hom K L M hL :=
{ to_algebraically_closed := sorry, -- should be adjoin_root.lift composed with an isomorphism
  to_field := sorry, --
  ..adjoin_root_extension K f }

private lemma le_adjoin_root_subfield_and_hom : maximal_subfield_and_hom M hL ≤
  adjoin_root_subfield_and_hom M hL f hxf :=
le_adjoin_root_extension _ _

private def maximal_subfield_and_hom_equiv_adjoin_root :=
equiv_adjoin_root_of_le K f $
  classical.some_spec (exists_maximal_subfield_and_hom hL) _
    (le_adjoin_root_subfield_and_hom M hL f hxf)

omit hif hxf

private lemma surjective_maximal_subfield_and_hom_to_field :
  function.surjective (maximal_subfield_and_hom M hL).to_field :=
λ x, let hx := is_integral_over_maximal M hL x in
by letI := minimal_polynomial.irreducible hx; exact
⟨_, minimal_polynomial.root hx
  (exists_root_of_equiv (maximal_subfield_and_hom_equiv_adjoin_root M hL _
    (minimal_polynomial.aeval hx)) (adjoin_root.eval₂_root _))⟩

private def equiv_maximal_subfield_and_hom :
  (maximal_subfield_and_hom M hL).carrier ≃ₐ[K] L :=
{ ..(maximal_subfield_and_hom M hL).to_field,
  ..equiv.of_bijective
    ⟨is_field_hom.injective _, surjective_maximal_subfield_and_hom_to_field _ _⟩ }

/-- The hom from an algebraic extension of K into an algebraic closure -/
def lift : L →ₐ[K] M :=
(maximal_subfield_and_hom M hL).to_algebraically_closed.comp
(equiv_maximal_subfield_and_hom M hL).symm.to_alg_hom

end lift

end algebraic_closure
