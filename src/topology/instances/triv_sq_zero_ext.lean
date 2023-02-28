/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.triv_sq_zero_ext
import topology.algebra.infinite_sum.basic
import topology.algebra.module.basic

/-!
# Topology on `triv_sq_zero_ext R M`

The type `triv_sq_zero_ext R M` inherits the topology from `R × M`.

Note that this is not the topology induced by the seminorm on the dual numbers suggested by
[this Math.SE answer](https://math.stackexchange.com/a/1056378/1896), which instead induces
the topology pulled back through the projection map `triv_sq_zero_ext.fst : tsze R M → R`.
Obviously, that topology is not Hausdorff and using it would result in `exp` converging to more than
one value.

## Main results

* `triv_sq_zero_ext.topological_ring`: the ring operations are continuous

-/

variables {α S R M : Type*}

local notation `tsze` := triv_sq_zero_ext

namespace triv_sq_zero_ext
variables [topological_space R] [topological_space M]

instance : topological_space (tsze R M) :=
topological_space.induced fst ‹_› ⊓ topological_space.induced snd ‹_›

instance [t2_space R] [t2_space M] : t2_space (tsze R M) :=
prod.t2_space

lemma nhds_def (x : tsze R M) : nhds x = (nhds x.fst).prod (nhds x.snd) :=
by cases x; exact nhds_prod_eq
lemma nhds_inl [has_zero M] (x : R) : nhds (inl x : tsze R M) = (nhds x).prod (nhds 0) := nhds_def _
lemma nhds_inr [has_zero R] (m : M) : nhds (inr m : tsze R M) = (nhds 0).prod (nhds m) := nhds_def _

lemma continuous_fst : continuous (fst : tsze R M → R) := continuous_fst
lemma continuous_snd : continuous (snd : tsze R M → M) := continuous_snd

lemma continuous_inl [has_zero M] : continuous (inl : R → tsze R M) :=
continuous_id.prod_mk continuous_const
lemma continuous_inr [has_zero R] : continuous (inr : M → tsze R M) :=
continuous_const.prod_mk continuous_id

lemma embedding_inl [has_zero M] : embedding (inl : R → tsze R M) :=
embedding_of_embedding_compose continuous_inl continuous_fst embedding_id
lemma embedding_inr [has_zero R] : embedding (inr : M → tsze R M) :=
embedding_of_embedding_compose continuous_inr continuous_snd embedding_id

variables (R M)

/-- `triv_sq_zero_ext.fst` as a continuous linear map. -/
@[simps]
def fst_clm [comm_semiring R] [add_comm_monoid M] [module R M] : tsze R M →L[R] R :=
{ to_fun := fst,
  .. continuous_linear_map.fst R R M }

/-- `triv_sq_zero_ext.snd` as a continuous linear map. -/
@[simps]
def snd_clm [comm_semiring R] [add_comm_monoid M] [module R M] : tsze R M →L[R] M :=
{ to_fun := snd,
  cont := continuous_snd,
  .. continuous_linear_map.snd R R M }

/-- `triv_sq_zero_ext.inl` as a continuous linear map. -/
@[simps]
def inl_clm [comm_semiring R] [add_comm_monoid M] [module R M] : R →L[R] tsze R M :=
{ to_fun := inl,
  .. continuous_linear_map.inl R R M }

/-- `triv_sq_zero_ext.inr` as a continuous linear map. -/
@[simps]
def inr_clm [comm_semiring R] [add_comm_monoid M] [module R M] : M →L[R] tsze R M :=
{ to_fun := inr,
  .. continuous_linear_map.inr R R M }

variables {R M}

instance [has_add R] [has_add M]
  [has_continuous_add R] [has_continuous_add M] :
  has_continuous_add (tsze R M) :=
prod.has_continuous_add

instance [has_mul R] [has_add M] [has_smul R M] [has_smul Rᵐᵒᵖ M]
  [has_continuous_mul R] [has_continuous_smul R M] [has_continuous_smul Rᵐᵒᵖ M]
  [has_continuous_add M] :
  has_continuous_mul (tsze R M) :=
⟨((continuous_fst.comp _root_.continuous_fst).mul (continuous_fst.comp _root_.continuous_snd))
  .prod_mk $
    ((continuous_fst.comp _root_.continuous_fst).smul
     (continuous_snd.comp _root_.continuous_snd)).add
    ((mul_opposite.continuous_op.comp $ continuous_fst.comp $ _root_.continuous_snd).smul
     (continuous_snd.comp _root_.continuous_fst))⟩

instance [has_neg R] [has_neg M]
  [has_continuous_neg R] [has_continuous_neg M] :
  has_continuous_neg (tsze R M) :=
prod.has_continuous_neg

/-- This is not an instance due to complaints by the `fails_quickly` linter. At any rate, we only
really care about the `topological_ring` instance below. -/
lemma topological_semiring [semiring R] [add_comm_monoid M] [module R M] [module Rᵐᵒᵖ M]
  [topological_semiring R] [has_continuous_add M]
  [has_continuous_smul R M] [has_continuous_smul Rᵐᵒᵖ M] :
  -- note: lean times out looking for the non_assoc_semiring instance without this hint
  @topological_semiring (tsze R M) _ (non_assoc_semiring.to_non_unital_non_assoc_semiring _) :=
{}

instance [ring R] [add_comm_group M] [module R M] [module Rᵐᵒᵖ M]
  [topological_ring R] [topological_add_group M]
  [has_continuous_smul R M] [has_continuous_smul Rᵐᵒᵖ M] :
  topological_ring (tsze R M) :=
{}

instance [has_smul S R] [has_smul S M]
  [has_continuous_const_smul S R] [has_continuous_const_smul S M] :
  has_continuous_const_smul S (tsze R M) :=
prod.has_continuous_const_smul

instance [topological_space S] [has_smul S R] [has_smul S M]
  [has_continuous_smul S R] [has_continuous_smul S M] :
  has_continuous_smul S (tsze R M) :=
prod.has_continuous_smul

variables (M)

lemma has_sum_inl [add_comm_monoid R] [add_comm_monoid M] {f : α → R} {a : R} (h : has_sum f a) :
  has_sum (λ x, inl (f x)) (inl a : tsze R M) :=
h.map (⟨inl, inl_zero _, inl_add _⟩ : R →+ tsze R M) continuous_inl

lemma has_sum_inr [add_comm_monoid R] [add_comm_monoid M] {f : α → M} {a : M} (h : has_sum f a) :
  has_sum (λ x, inr (f x)) (inr a : tsze R M) :=
h.map (⟨inr, inr_zero _, inr_add _⟩ : M →+ tsze R M) continuous_inr

lemma has_sum_fst [add_comm_monoid R] [add_comm_monoid M] {f : α → tsze R M} {a : tsze R M}
  (h : has_sum f a) : has_sum (λ x, fst (f x)) (fst a) :=
h.map (⟨fst, fst_zero, fst_add⟩ : tsze R M →+ R) continuous_fst

lemma has_sum_snd [add_comm_monoid R] [add_comm_monoid M] {f : α → tsze R M} {a : tsze R M}
  (h : has_sum f a) : has_sum (λ x, snd (f x)) (snd a) :=
h.map (⟨snd, snd_zero, snd_add⟩ : tsze R M →+ M) continuous_snd

end triv_sq_zero_ext
