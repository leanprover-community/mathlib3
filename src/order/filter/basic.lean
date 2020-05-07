/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/
import order.zorn
import order.copy
import data.set.finite

/-! # Theory of filters on sets

## Main definitions

* `filter` : filters on a set;
* `at_top`, `at_bot`, `cofinite`, `principal` : specific filters;
* `map`, `comap`, `prod` : operations on filters;
* `tendsto` : limit with respect to filters;
* `eventually` : `f.eventually p` means `{x | p x} ∈ f`;
* `frequently` : `f.frequently p` means `{x | ¬p x} ∉ f`.
* `filter_upwards [h₁, ..., hₙ]` : takes a list of proofs `hᵢ : sᵢ ∈ f`, and replaces a goal `s ∈ f`
  with `∀ x, x ∈ s₁ → ... → x ∈ sₙ → x ∈ s`;

Filters on a type `X` are sets of sets of `X` satisfying three conditions. They are mostly used to
abstract two related kinds of ideas:
* *limits*, including finite or infinite limits of sequences, finite or infinite limits of functions
  at a point or at infinity, etc...
* *things happening eventually*, including things happening for large enough `n : ℕ`, or near enough
  a point `x`, or for close enough pairs of points, or things happening almost everywhere in the
  sense of measure theory. Dually, filters can also express the idea of *things happening often*:
  for arbitrarily large `n`, or at a point in any neighborhood of given a point etc...

In this file, we define the type `filter X` of filters on `X`, and endow it with a complete lattice
structure. This structure is lifted from the lattice structure on `set (set X)` using the Galois
insertion which maps a filter to its elements in one direction, and an arbitrary set of sets to
the smallest filter containing it in the other direction.
We also prove `filter` is a monadic functor, with a push-forward operation
`filter.map` and a pull-back operation `filter.comap` that form a Galois connections for the
order on filters.
Finally we describe a product operation `filter X → filter Y → filter (X × Y)`.

The examples of filters appearing in the description of the two motivating ideas are:
* `(at_top : filter ℕ)` : made of sets of `ℕ` containing `{n | n ≥ N}` for some `N`
* `𝓝 x` : made of neighborhoods of `x` in a topological space (defined in topology.basic)
* `𝓤 X` : made of entourages of a uniform space (those space are generalizations of metric spaces
  defined in topology.uniform_space.basic)
* `μ.a_e` : made of sets whose complement has zero measure with respect to `μ` (defined in
  measure_theory.measure_space)

The general notion of limit of a map with respect to filters on the source and target types
is `filter.tendsto`. It is defined in terms of the order and the push-forward operation.
The predicate "happening eventually" is `filter.eventually`, and "happening often" is
`filter.frequently`, whose definitions are immediate after `filter` is defined (but they come
rather late in this file in order to immediately relate them to the lattice structure).

For instance, anticipating on topology.basic, the statement: "if a sequence `u` converges to
some `x` and `u n` belongs to a set `M` for `n` large enough then `x` is in the closure of
`M`" is formalized as: `tendsto u at_top (𝓝 x) → (∀ᶠ n in at_top, u n ∈ M) → x ∈ closure M`,
which is a special case of `mem_closure_of_tendsto` from topology.basic.

## Notations

* `∀ᶠ x in f, p x` : `f.eventually p`;
* `∃ᶠ x in f, p x` : `f.frequently p`.
* `f ×ᶠ g` : `filter.prod f g`, localized in `filter`.

## References

*  [N. Bourbaki, *General Topology*][bourbaki1966]

Important note: Bourbaki requires that a filter on `X` cannot contain all sets of `X`, which
we do *not* require. This gives `filter X` better formal properties, in particular a bottom element
`⊥` for its lattice structure, at the cost of including the assumption
`f ≠ ⊥` in a number of lemmas and definitions.
-/

open set

universes u v w x y

open_locale classical

/-- A filter `F` on a type `α` is a collection of sets of `α` which contains the whole `α`,
is upwards-closed, and is stable under intersection. We do not forbid this collection to be
all sets of `α`. -/
structure filter (α : Type*) :=
(sets                   : set (set α))
(univ_sets              : set.univ ∈ sets)
(sets_of_superset {x y} : x ∈ sets → x ⊆ y → y ∈ sets)
(inter_sets {x y}       : x ∈ sets → y ∈ sets → x ∩ y ∈ sets)

/-- If `F` is a filter on `α`, and `U` a subset of `α` then we can write `U ∈ F` as on paper. -/
@[reducible]
instance {α : Type*}: has_mem (set α) (filter α) := ⟨λ U F, U ∈ F.sets⟩

namespace filter
variables {α : Type u} {f g : filter α} {s t : set α}

lemma filter_eq : ∀{f g : filter α}, f.sets = g.sets → f = g
| ⟨a, _, _, _⟩ ⟨._, _, _, _⟩ rfl := rfl

lemma filter_eq_iff : f = g ↔ f.sets = g.sets :=
⟨congr_arg _, filter_eq⟩

protected lemma ext_iff : f = g ↔ ∀ s, s ∈ f ↔ s ∈ g :=
by rw [filter_eq_iff, ext_iff]

@[ext]
protected lemma ext : (∀ s, s ∈ f ↔ s ∈ g) → f = g :=
filter.ext_iff.2

lemma univ_mem_sets : univ ∈ f :=
f.univ_sets

lemma mem_sets_of_superset : ∀{x y : set α}, x ∈ f → x ⊆ y → y ∈ f :=
f.sets_of_superset

lemma inter_mem_sets : ∀{s t}, s ∈ f → t ∈ f → s ∩ t ∈ f :=
f.inter_sets

lemma univ_mem_sets' (h : ∀ a, a ∈ s) : s ∈ f :=
mem_sets_of_superset univ_mem_sets (assume x _, h x)

lemma mp_sets (hs : s ∈ f) (h : {x | x ∈ s → x ∈ t} ∈ f) : t ∈ f :=
mem_sets_of_superset (inter_mem_sets hs h) $ assume x ⟨h₁, h₂⟩, h₂ h₁

lemma congr_sets (h : {x | x ∈ s ↔ x ∈ t} ∈ f) : s ∈ f ↔ t ∈ f :=
⟨λ hs, mp_sets hs (mem_sets_of_superset h (λ x, iff.mp)),
 λ hs, mp_sets hs (mem_sets_of_superset h (λ x, iff.mpr))⟩

lemma Inter_mem_sets {β : Type v} {s : β → set α} {is : set β} (hf : finite is) :
  (∀i∈is, s i ∈ f) → (⋂i∈is, s i) ∈ f :=
finite.induction_on hf
  (assume hs, by simp only [univ_mem_sets, mem_empty_eq, Inter_neg, Inter_univ, not_false_iff])
  (assume i is _ hf hi hs,
    have h₁ : s i ∈ f, from hs i (by simp),
    have h₂ : (⋂x∈is, s x) ∈ f, from hi $ assume a ha, hs _ $ by simp only [ha, mem_insert_iff, or_true],
    by simp [inter_mem_sets h₁ h₂])

lemma sInter_mem_sets_of_finite {s : set (set α)} (hfin : finite s) (h_in : ∀ U ∈ s, U ∈ f) :
  ⋂₀ s ∈ f :=
by { rw sInter_eq_bInter, exact Inter_mem_sets hfin h_in }

lemma Inter_mem_sets_of_fintype {β : Type v} {s : β → set α} [fintype β] (h : ∀i, s i ∈ f) :
  (⋂i, s i) ∈ f :=
by simpa using Inter_mem_sets finite_univ (λi hi, h i)

lemma exists_sets_subset_iff : (∃t ∈ f, t ⊆ s) ↔ s ∈ f :=
⟨assume ⟨t, ht, ts⟩, mem_sets_of_superset ht ts, assume hs, ⟨s, hs, subset.refl _⟩⟩

lemma monotone_mem_sets {f : filter α} : monotone (λs, s ∈ f) :=
assume s t hst h, mem_sets_of_superset h hst

end filter

namespace tactic.interactive
open tactic interactive

/-- `filter_upwards [h1, ⋯, hn]` replaces a goal of the form `s ∈ f`
and terms `h1 : t1 ∈ f, ⋯, hn : tn ∈ f` with `∀x, x ∈ t1 → ⋯ → x ∈ tn → x ∈ s`.

`filter_upwards [h1, ⋯, hn] e` is a short form for `{ filter_upwards [h1, ⋯, hn], exact e }`.
-/
meta def filter_upwards
  (s : parse types.pexpr_list)
  (e' : parse $ optional types.texpr) : tactic unit :=
do
  s.reverse.mmap (λ e, eapplyc `filter.mp_sets >> eapply e),
  eapplyc `filter.univ_mem_sets',
  match e' with
  | some e := interactive.exact e
  | none := skip
  end

end tactic.interactive

namespace filter
variables {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x}

section principal

/-- The principal filter of `s` is the collection of all supersets of `s`. -/
def principal (s : set α) : filter α :=
{ sets             := {t | s ⊆ t},
  univ_sets        := subset_univ s,
  sets_of_superset := assume x y hx hy, subset.trans hx hy,
  inter_sets       := assume x y, subset_inter }

instance : inhabited (filter α) :=
⟨principal ∅⟩

@[simp] lemma mem_principal_sets {s t : set α} : s ∈ principal t ↔ t ⊆ s := iff.rfl

lemma mem_principal_self (s : set α) : s ∈ principal s := subset.refl _

end principal

section join

/-- The join of a filter of filters is defined by the relation `s ∈ join f ↔ {t | s ∈ t} ∈ f`. -/
def join (f : filter (filter α)) : filter α :=
{ sets             := {s | {t : filter α | s ∈ t} ∈ f},
  univ_sets        := by simp only [univ_mem_sets, mem_set_of_eq]; exact univ_mem_sets,
  sets_of_superset := assume x y hx xy,
    mem_sets_of_superset hx $ assume f h, mem_sets_of_superset h xy,
  inter_sets       := assume x y hx hy,
    mem_sets_of_superset (inter_mem_sets hx hy) $ assume f ⟨h₁, h₂⟩, inter_mem_sets h₁ h₂ }

@[simp] lemma mem_join_sets {s : set α} {f : filter (filter α)} :
  s ∈ join f ↔ {t | s ∈ t} ∈ f := iff.rfl

end join

section lattice

instance : partial_order (filter α) :=
{ le            := λf g, ∀ ⦃U : set α⦄, U ∈ g → U ∈ f,
  le_antisymm   := assume a b h₁ h₂, filter_eq $ subset.antisymm h₂ h₁,
  le_refl       := assume a, subset.refl _,
  le_trans      := assume a b c h₁ h₂, subset.trans h₂ h₁ }

theorem le_def {f g : filter α} : f ≤ g ↔ ∀ x ∈ g, x ∈ f := iff.rfl

/-- `generate_sets g s`: `s` is in the filter closure of `g`. -/
inductive generate_sets (g : set (set α)) : set α → Prop
| basic {s : set α}      : s ∈ g → generate_sets s
| univ                   : generate_sets univ
| superset {s t : set α} : generate_sets s → s ⊆ t → generate_sets t
| inter {s t : set α}    : generate_sets s → generate_sets t → generate_sets (s ∩ t)

/-- `generate g` is the smallest filter containing the sets `g`. -/
def generate (g : set (set α)) : filter α :=
{ sets             := generate_sets g,
  univ_sets        := generate_sets.univ,
  sets_of_superset := assume x y, generate_sets.superset,
  inter_sets       := assume s t, generate_sets.inter }

lemma sets_iff_generate {s : set (set α)} {f : filter α} : f ≤ filter.generate s ↔ s ⊆ f.sets :=
iff.intro
  (assume h u hu, h $ generate_sets.basic $ hu)
  (assume h u hu, hu.rec_on h univ_mem_sets
    (assume x y _ hxy hx, mem_sets_of_superset hx hxy)
    (assume x y _ _ hx hy, inter_mem_sets hx hy))


lemma mem_generate_iff (s : set $ set α) {U : set α} : U ∈ generate s ↔ ∃ t ⊆ s, finite t ∧ ⋂₀ t ⊆ U :=
begin
  split ; intro h,
  { induction h with V V_in V W V_in hVW hV V W V_in W_in hV hW,
    { use {V},
      simp [V_in] },
    { use ∅,
      simp [subset.refl, univ] },
    { rcases hV with ⟨t, hts, htfin, hinter⟩,
      exact ⟨t, hts, htfin, subset.trans hinter hVW⟩ },
    { rcases hV with ⟨t, hts, htfin, htinter⟩,
      rcases hW with ⟨z, hzs, hzfin, hzinter⟩,
      refine ⟨t ∪ z, union_subset hts hzs, finite_union htfin hzfin, _⟩,
      rw sInter_union,
      exact inter_subset_inter htinter hzinter } },
  { rcases h with ⟨t, ts, tfin, h⟩,
    apply generate_sets.superset _ h,
    revert ts,
    apply finite.induction_on tfin,
    { intro h,
      rw sInter_empty,
      exact generate_sets.univ },
    { intros V r hV rfin hinter h,
      cases insert_subset.mp h with V_in r_sub,
      rw [insert_eq V r, sInter_union],
      apply generate_sets.inter _ (hinter r_sub),
      rw sInter_singleton,
      exact generate_sets.basic V_in } },
end

/-- `mk_of_closure s hs` constructs a filter on `α` whose elements set is exactly
`s : set (set α)`, provided one gives the assumption `hs : (generate s).sets = s`. -/
protected def mk_of_closure (s : set (set α)) (hs : (generate s).sets = s) : filter α :=
{ sets             := s,
  univ_sets        := hs ▸ (univ_mem_sets : univ ∈ generate s),
  sets_of_superset := assume x y, hs ▸ (mem_sets_of_superset : x ∈ generate s → x ⊆ y → y ∈ generate s),
  inter_sets       := assume x y, hs ▸ (inter_mem_sets : x ∈ generate s → y ∈ generate s → x ∩ y ∈ generate s) }

lemma mk_of_closure_sets {s : set (set α)} {hs : (generate s).sets = s} :
  filter.mk_of_closure s hs = generate s :=
filter.ext $ assume u,
show u ∈ (filter.mk_of_closure s hs).sets ↔ u ∈ (generate s).sets, from hs.symm ▸ iff.rfl

/-- Galois insertion from sets of sets into filters. -/
def gi_generate (α : Type*) :
  @galois_insertion (set (set α)) (order_dual (filter α)) _ _ filter.generate filter.sets :=
{ gc        := assume s f, sets_iff_generate,
  le_l_u    := assume f u h, generate_sets.basic h,
  choice    := λs hs, filter.mk_of_closure s (le_antisymm hs $ sets_iff_generate.1 $ le_refl _),
  choice_eq := assume s hs, mk_of_closure_sets }

/-- The infimum of filters is the filter generated by intersections
  of elements of the two filters. -/
instance : has_inf (filter α) := ⟨λf g : filter α,
{ sets             := {s | ∃ (a ∈ f) (b ∈ g), a ∩ b ⊆ s },
  univ_sets        := ⟨_, univ_mem_sets, _, univ_mem_sets, inter_subset_left _ _⟩,
  sets_of_superset := assume x y ⟨a, ha, b, hb, h⟩ xy, ⟨a, ha, b, hb, subset.trans h xy⟩,
  inter_sets       := assume x y ⟨a, ha, b, hb, hx⟩ ⟨c, hc, d, hd, hy⟩,
    ⟨_, inter_mem_sets ha hc, _, inter_mem_sets hb hd,
      calc a ∩ c ∩ (b ∩ d) = (a ∩ b) ∩ (c ∩ d) : by ac_refl
        ... ⊆ x ∩ y : inter_subset_inter hx hy⟩ }⟩

@[simp] lemma mem_inf_sets {f g : filter α} {s : set α} :
  s ∈ f ⊓ g ↔ ∃t₁∈f, ∃t₂∈g, t₁ ∩ t₂ ⊆ s := iff.rfl

lemma mem_inf_sets_of_left {f g : filter α} {s : set α} (h : s ∈ f) : s ∈ f ⊓ g :=
⟨s, h, univ, univ_mem_sets, inter_subset_left _ _⟩

lemma mem_inf_sets_of_right {f g : filter α} {s : set α} (h : s ∈ g) : s ∈ f ⊓ g :=
⟨univ, univ_mem_sets, s, h, inter_subset_right _ _⟩

lemma inter_mem_inf_sets {α : Type u} {f g : filter α} {s t : set α}
  (hs : s ∈ f) (ht : t ∈ g) : s ∩ t ∈ f ⊓ g :=
inter_mem_sets (mem_inf_sets_of_left hs) (mem_inf_sets_of_right ht)

instance : has_top (filter α) :=
⟨{ sets            := {s | ∀x, x ∈ s},
  univ_sets        := assume x, mem_univ x,
  sets_of_superset := assume x y hx hxy a, hxy (hx a),
  inter_sets       := assume x y hx hy a, mem_inter (hx _) (hy _) }⟩

lemma mem_top_sets_iff_forall {s : set α} : s ∈ (⊤ : filter α) ↔ (∀x, x ∈ s) :=
iff.rfl

@[simp] lemma mem_top_sets {s : set α} : s ∈ (⊤ : filter α) ↔ s = univ :=
by rw [mem_top_sets_iff_forall, eq_univ_iff_forall]

section complete_lattice

/- We lift the complete lattice along the Galois connection `generate` / `sets`. Unfortunately,
  we want to have different definitional equalities for the lattice operations. So we define them
  upfront and change the lattice operations for the complete lattice instance. -/

private def original_complete_lattice : complete_lattice (filter α) :=
@order_dual.complete_lattice _ (gi_generate α).lift_complete_lattice

local attribute [instance] original_complete_lattice

instance : complete_lattice (filter α) := original_complete_lattice.copy
  /- le  -/ filter.partial_order.le rfl
  /- top -/ (filter.has_top).1
  (top_unique $ assume s hs, by have := univ_mem_sets ; finish)
  /- bot -/ _ rfl
  /- sup -/ _ rfl
  /- inf -/ (filter.has_inf).1
  begin
    ext f g : 2,
    exact le_antisymm
      (le_inf (assume s, mem_inf_sets_of_left) (assume s, mem_inf_sets_of_right))
      (assume s ⟨a, ha, b, hb, hs⟩, show s ∈ complete_lattice.inf f g, from
      mem_sets_of_superset (inter_mem_sets
        (@inf_le_left (filter α) _ _ _ _ ha)
        (@inf_le_right (filter α) _ _ _ _ hb)) hs)
  end
  /- Sup -/ (join ∘ principal) (by ext s x; exact (@mem_bInter_iff _ _ s filter.sets x).symm)
  /- Inf -/ _ rfl

end complete_lattice

lemma bot_sets_eq : (⊥ : filter α).sets = univ := rfl

lemma sup_sets_eq {f g : filter α} : (f ⊔ g).sets = f.sets ∩ g.sets :=
(gi_generate α).gc.u_inf

lemma Sup_sets_eq {s : set (filter α)} : (Sup s).sets = (⋂f∈s, (f:filter α).sets) :=
(gi_generate α).gc.u_Inf

lemma supr_sets_eq {f : ι → filter α} : (supr f).sets = (⋂i, (f i).sets) :=
(gi_generate α).gc.u_infi

lemma generate_empty : filter.generate ∅ = (⊤ : filter α) :=
(gi_generate α).gc.l_bot

lemma generate_univ : filter.generate univ = (⊥ : filter α) :=
mk_of_closure_sets.symm

lemma generate_union {s t : set (set α)} :
  filter.generate (s ∪ t) = filter.generate s ⊓ filter.generate t :=
(gi_generate α).gc.l_sup

lemma generate_Union {s : ι → set (set α)} :
  filter.generate (⋃ i, s i) = (⨅ i, filter.generate (s i)) :=
(gi_generate α).gc.l_supr

@[simp] lemma mem_bot_sets {s : set α} : s ∈ (⊥ : filter α) :=
trivial

@[simp] lemma mem_sup_sets {f g : filter α} {s : set α} :
  s ∈ f ⊔ g ↔ s ∈ f ∧ s ∈ g :=
iff.rfl

@[simp] lemma mem_Sup_sets {x : set α} {s : set (filter α)} :
  x ∈ Sup s ↔ (∀f∈s, x ∈ (f:filter α)) :=
iff.rfl

@[simp] lemma mem_supr_sets {x : set α} {f : ι → filter α} :
  x ∈ supr f ↔ (∀i, x ∈ f i) :=
by simp only [supr_sets_eq, iff_self, mem_Inter]

lemma infi_eq_generate (s : ι → filter α) : infi s = generate (⋃ i, (s i).sets) :=
show generate _ = generate _, from congr_arg _ supr_range

lemma mem_infi_iff {ι} {s : ι → filter α} {U : set α} : (U ∈ ⨅ i, s i) ↔
  ∃ I : set ι, finite I ∧ ∃ V : {i | i ∈ I} → set α, (∀ i, V i ∈ s i) ∧ (⋂ i, V i) ⊆ U :=
begin
  rw [infi_eq_generate, mem_generate_iff],
  split,
  { rintro ⟨t, tsub, tfin, tinter⟩,
    rcases eq_finite_Union_of_finite_subset_Union tfin tsub with ⟨I, Ifin, σ, σfin, σsub, rfl⟩,
    rw sInter_Union at tinter,
    let V := λ i, ⋂₀ σ i,
    have V_in : ∀ i, V i ∈ s i,
    { rintro ⟨i, i_in⟩,
      apply sInter_mem_sets_of_finite (σfin _),
      apply σsub },
    exact ⟨I, Ifin, V, V_in, tinter⟩ },
  { rintro ⟨I, Ifin, V, V_in, h⟩,
    refine ⟨range V, _, _, h⟩,
    { rintro _ ⟨i, rfl⟩,
      rw mem_Union,
      use [i, V_in i] },
    { haveI : fintype {i : ι | i ∈ I} := finite.fintype Ifin,
      exact finite_range _ } },
end

@[simp] lemma le_principal_iff {s : set α} {f : filter α} : f ≤ principal s ↔ s ∈ f :=
show (∀{t}, s ⊆ t → t ∈ f) ↔ s ∈ f,
  from ⟨assume h, h (subset.refl s), assume hs t ht, mem_sets_of_superset hs ht⟩

lemma principal_mono {s t : set α} : principal s ≤ principal t ↔ s ⊆ t :=
by simp only [le_principal_iff, iff_self, mem_principal_sets]

lemma monotone_principal : monotone (principal : set α → filter α) :=
λ _ _, principal_mono.2

@[simp] lemma principal_eq_iff_eq {s t : set α} : principal s = principal t ↔ s = t :=
by simp only [le_antisymm_iff, le_principal_iff, mem_principal_sets]; refl

@[simp] lemma join_principal_eq_Sup {s : set (filter α)} : join (principal s) = Sup s := rfl

lemma principal_univ : principal (univ : set α) = ⊤ :=
top_unique $ by simp only [le_principal_iff, mem_top_sets, eq_self_iff_true]

lemma principal_empty : principal (∅ : set α) = ⊥ :=
bot_unique $ assume s _, empty_subset _

/-! ### Lattice equations -/

lemma empty_in_sets_eq_bot {f : filter α} : ∅ ∈ f ↔ f = ⊥ :=
⟨assume h, bot_unique $ assume s _, mem_sets_of_superset h (empty_subset s),
  assume : f = ⊥, this.symm ▸ mem_bot_sets⟩

lemma nonempty_of_mem_sets {f : filter α} (hf : f ≠ ⊥) {s : set α} (hs : s ∈ f) :
  s.nonempty :=
s.eq_empty_or_nonempty.elim (λ h, absurd hs (h.symm ▸ mt empty_in_sets_eq_bot.mp hf)) id

lemma nonempty_of_ne_bot {f : filter α} (hf : f ≠ ⊥) : nonempty α :=
nonempty_of_exists $ nonempty_of_mem_sets hf univ_mem_sets

lemma filter_eq_bot_of_not_nonempty {f : filter α} (ne : ¬ nonempty α) : f = ⊥ :=
empty_in_sets_eq_bot.mp $ univ_mem_sets' $ assume x, false.elim (ne ⟨x⟩)

lemma forall_sets_nonempty_iff_ne_bot {f : filter α} :
  (∀ (s : set α), s ∈ f → s.nonempty) ↔ f ≠ ⊥ :=
⟨λ h hf, empty_not_nonempty (h ∅ $ hf.symm ▸ mem_bot_sets), nonempty_of_mem_sets⟩

lemma mem_sets_of_eq_bot {f : filter α} {s : set α} (h : f ⊓ principal (-s) = ⊥) : s ∈ f :=
have ∅ ∈ f ⊓ principal (- s), from h.symm ▸ mem_bot_sets,
let ⟨s₁, hs₁, s₂, (hs₂ : -s ⊆ s₂), (hs : s₁ ∩ s₂ ⊆ ∅)⟩ := this in
by filter_upwards [hs₁] assume a ha, classical.by_contradiction $ assume ha', hs ⟨ha, hs₂ ha'⟩

lemma inf_ne_bot_iff {f g : filter α} :
  f ⊓ g ≠ ⊥ ↔ ∀ {U V}, U ∈ f → V ∈ g → set.nonempty (U ∩ V) :=
begin
  rw ← forall_sets_nonempty_iff_ne_bot,
  simp_rw mem_inf_sets,
  split ; intro h,
  { intros U V U_in V_in,
    exact h (U ∩ V) ⟨U, U_in, V, V_in, subset.refl _⟩ },
  { rintros S ⟨U, U_in, V, V_in, hUV⟩,
    cases h U_in V_in with a ha,
    use [a, hUV ha] }
end

lemma eq_Inf_of_mem_sets_iff_exists_mem {S : set (filter α)} {l : filter α}
  (h : ∀ {s}, s ∈ l ↔ ∃ f ∈ S, s ∈ f) : l = Inf S :=
le_antisymm (le_Inf $ λ f hf s hs, h.2 ⟨f, hf, hs⟩)
  (λ s hs, let ⟨f, hf, hs⟩ := h.1 hs in (Inf_le hf : Inf S ≤ f) hs)

lemma eq_infi_of_mem_sets_iff_exists_mem {f : ι → filter α} {l : filter α}
  (h : ∀ {s}, s ∈ l ↔ ∃ i, s ∈ f i) :
  l = infi f :=
eq_Inf_of_mem_sets_iff_exists_mem $ λ s, h.trans exists_range_iff.symm

lemma eq_binfi_of_mem_sets_iff_exists_mem {f : ι → filter α} {p : ι  → Prop} {l : filter α}
  (h : ∀ {s}, s ∈ l ↔ ∃ i (_ : p i), s ∈ f i) :
  l = ⨅ i (_ : p i), f i :=
begin
  rw [infi_subtype'],
  apply eq_infi_of_mem_sets_iff_exists_mem,
  intro s,
  exact h.trans ⟨λ ⟨i, pi, si⟩, ⟨⟨i, pi⟩, si⟩, λ ⟨⟨i, pi⟩, si⟩, ⟨i, pi, si⟩⟩
end

lemma infi_sets_eq {f : ι → filter α} (h : directed (≥) f) (ne : nonempty ι) :
  (infi f).sets = (⋃ i, (f i).sets) :=
let ⟨i⟩ := ne, u := { filter .
    sets             := (⋃ i, (f i).sets),
    univ_sets        := by simp only [mem_Union]; exact ⟨i, univ_mem_sets⟩,
    sets_of_superset := by simp only [mem_Union, exists_imp_distrib];
                        intros x y i hx hxy; exact ⟨i, mem_sets_of_superset hx hxy⟩,
    inter_sets       :=
    begin
      simp only [mem_Union, exists_imp_distrib],
      assume x y a hx b hy,
      rcases h a b with ⟨c, ha, hb⟩,
      exact ⟨c, inter_mem_sets (ha hx) (hb hy)⟩
    end } in
have u = infi f, from eq_infi_of_mem_sets_iff_exists_mem (λ s, by simp only [mem_Union]),
congr_arg filter.sets this.symm

lemma mem_infi {f : ι → filter α} (h : directed (≥) f) (ne : nonempty ι) (s) :
  s ∈ infi f ↔ ∃ i, s ∈ f i :=
by simp only [infi_sets_eq h ne, mem_Union]

@[nolint ge_or_gt] -- Intentional use of `≥`
lemma binfi_sets_eq {f : β → filter α} {s : set β}
  (h : directed_on (f ⁻¹'o (≥)) s) (ne : s.nonempty) :
  (⨅ i∈s, f i).sets = (⋃ i ∈ s, (f i).sets) :=
let ⟨i, hi⟩ := ne in
calc (⨅ i ∈ s, f i).sets  = (⨅ t : {t // t ∈ s}, (f t.val)).sets : by rw [infi_subtype]; refl
  ... = (⨆ t : {t // t ∈ s}, (f t.val).sets) : infi_sets_eq
    (assume ⟨x, hx⟩ ⟨y, hy⟩, match h x hx y hy with ⟨z, h₁, h₂, h₃⟩ := ⟨⟨z, h₁⟩, h₂, h₃⟩ end)
    ⟨⟨i, hi⟩⟩
  ... = (⨆ t ∈ {t | t ∈ s}, (f t).sets) : by rw [supr_subtype]; refl

@[nolint ge_or_gt] -- Intentional use of `≥`
lemma mem_binfi {f : β → filter α} {s : set β}
  (h : directed_on (f ⁻¹'o (≥)) s) (ne : s.nonempty) {t : set α} :
  t ∈ (⨅ i∈s, f i) ↔ ∃ i ∈ s, t ∈ f i :=
by simp only [binfi_sets_eq h ne, mem_bUnion_iff]

lemma infi_sets_eq_finite (f : ι → filter α) :
  (⨅i, f i).sets = (⋃t:finset (plift ι), (⨅i∈t, f (plift.down i)).sets) :=
begin
  rw [infi_eq_infi_finset, infi_sets_eq],
  exact (directed_of_sup $ λs₁ s₂ hs, infi_le_infi $ λi, infi_le_infi_const $ λh, hs h),
  apply_instance
end

lemma mem_infi_finite {f : ι → filter α} (s) :
  s ∈ infi f ↔ s ∈ ⋃t:finset (plift ι), (⨅i∈t, f (plift.down i)).sets :=
show  s ∈ (infi f).sets ↔ s ∈ ⋃t:finset (plift ι), (⨅i∈t, f (plift.down i)).sets,
by rw infi_sets_eq_finite

@[simp] lemma sup_join {f₁ f₂ : filter (filter α)} : (join f₁ ⊔ join f₂) = join (f₁ ⊔ f₂) :=
filter_eq $ set.ext $ assume x,
  by simp only [supr_sets_eq, join, mem_sup_sets, iff_self, mem_set_of_eq]

@[simp] lemma supr_join {ι : Sort w} {f : ι → filter (filter α)} :
  (⨆x, join (f x)) = join (⨆x, f x) :=
filter_eq $ set.ext $ assume x,
  by simp only [supr_sets_eq, join, iff_self, mem_Inter, mem_set_of_eq]

instance : bounded_distrib_lattice (filter α) :=
{ le_sup_inf :=
  begin
    assume x y z s,
    simp only [and_assoc, mem_inf_sets, mem_sup_sets, exists_prop, exists_imp_distrib, and_imp],
    intros hs t₁ ht₁ t₂ ht₂ hts,
    exact ⟨s ∪ t₁,
      x.sets_of_superset hs $ subset_union_left _ _,
      y.sets_of_superset ht₁ $ subset_union_right _ _,
      s ∪ t₂,
      x.sets_of_superset hs $ subset_union_left _ _,
      z.sets_of_superset ht₂ $ subset_union_right _ _,
      subset.trans (@le_sup_inf (set α) _ _ _ _) (union_subset (subset.refl _) hts)⟩
  end,
  ..filter.complete_lattice }

/- the complementary version with ⨆i, f ⊓ g i does not hold! -/
lemma infi_sup_eq {f : filter α} {g : ι → filter α} : (⨅ x, f ⊔ g x) = f ⊔ infi g :=
begin
  refine le_antisymm _ (le_infi $ assume i, sup_le_sup_left (infi_le _ _) _),
  rintros t ⟨h₁, h₂⟩,
  rw [infi_sets_eq_finite] at h₂,
  simp only [mem_Union, (finset.inf_eq_infi _ _).symm] at h₂,
  rcases h₂ with ⟨s, hs⟩,
  suffices : (⨅i, f ⊔ g i) ≤ f ⊔ s.inf (λi, g i.down), { exact this ⟨h₁, hs⟩ },
  refine finset.induction_on s _ _,
  { exact le_sup_right_of_le le_top },
  { rintros ⟨i⟩ s his ih,
    rw [finset.inf_insert, sup_inf_left],
    exact le_inf (infi_le _ _) ih }
end

lemma mem_infi_sets_finset {s : finset α} {f : α → filter β} :
  ∀t, t ∈ (⨅a∈s, f a) ↔ (∃p:α → set β, (∀a∈s, p a ∈ f a) ∧ (⋂a∈s, p a) ⊆ t) :=
show ∀t, t ∈ (⨅a∈s, f a) ↔ (∃p:α → set β, (∀a∈s, p a ∈ f a) ∧ (⨅a∈s, p a) ≤ t),
begin
  simp only [(finset.inf_eq_infi _ _).symm],
  refine finset.induction_on s _ _,
  { simp only [finset.not_mem_empty, false_implies_iff, finset.inf_empty, top_le_iff,
      imp_true_iff, mem_top_sets, true_and, exists_const],
    intros; refl },
  { intros a s has ih t,
    simp only [ih, finset.forall_mem_insert, finset.inf_insert, mem_inf_sets,
      exists_prop, iff_iff_implies_and_implies, exists_imp_distrib, and_imp, and_assoc] {contextual := tt},
    split,
    { intros t₁ ht₁ t₂ p hp ht₂ ht,
      existsi function.update p a t₁,
      have : ∀a'∈s, function.update p a t₁ a' = p a',
        from assume a' ha',
        have a' ≠ a, from assume h, has $ h ▸ ha',
        function.update_noteq this _ _,
      have eq : s.inf (λj, function.update p a t₁ j) = s.inf (λj, p j) :=
        finset.inf_congr rfl this,
      simp only [this, ht₁, hp, function.update_same, true_and, imp_true_iff, eq] {contextual := tt},
      exact subset.trans (inter_subset_inter (subset.refl _) ht₂) ht },
    assume p hpa hp ht,
    exact ⟨p a, hpa, (s.inf p), ⟨⟨p, hp, le_refl _⟩, ht⟩⟩ }
end

/-- If `f : ι → filter α` is directed, `ι` is not empty, and `∀ i, f i ≠ ⊥`, then `infi f ≠ ⊥`.
See also `infi_ne_bot_of_directed` for a version assuming `nonempty α` instead of `nonempty ι`. -/
lemma infi_ne_bot_of_directed' {f : ι → filter α} (hn : nonempty ι)
  (hd : directed (≥) f) (hb : ∀i, f i ≠ ⊥) : (infi f) ≠ ⊥ :=
begin
  intro h,
  have he: ∅  ∈ (infi f), from h.symm ▸ (mem_bot_sets : ∅ ∈ (⊥ : filter α)),
  obtain ⟨i, hi⟩ : ∃i, ∅ ∈ f i,
    from (mem_infi hd hn ∅).1 he,
  exact hb i (empty_in_sets_eq_bot.1 hi)
end

/-- If `f : ι → filter α` is directed, `α` is not empty, and `∀ i, f i ≠ ⊥`, then `infi f ≠ ⊥`.
See also `infi_ne_bot_of_directed'` for a version assuming `nonempty ι` instead of `nonempty α`. -/
lemma infi_ne_bot_of_directed {f : ι → filter α}
  (hn : nonempty α) (hd : directed (≥) f) (hb : ∀i, f i ≠ ⊥) : (infi f) ≠ ⊥ :=
if hι : nonempty ι then infi_ne_bot_of_directed' hι hd hb else
assume h : infi f = ⊥,
have univ ⊆ (∅ : set α),
begin
  rw [←principal_mono, principal_univ, principal_empty, ←h],
  exact (le_infi $ assume i, false.elim $ hι ⟨i⟩)
end,
let ⟨x⟩ := hn in this (mem_univ x)

lemma infi_ne_bot_iff_of_directed' {f : ι → filter α}
  (hn : nonempty ι) (hd : directed (≥) f) : (infi f) ≠ ⊥ ↔ (∀i, f i ≠ ⊥) :=
⟨assume ne_bot i, ne_bot_of_le_ne_bot ne_bot (infi_le _ i),
  infi_ne_bot_of_directed' hn hd⟩

lemma infi_ne_bot_iff_of_directed {f : ι → filter α}
  (hn : nonempty α) (hd : directed (≥) f) : (infi f) ≠ ⊥ ↔ (∀i, f i ≠ ⊥) :=
⟨assume ne_bot i, ne_bot_of_le_ne_bot ne_bot (infi_le _ i),
  infi_ne_bot_of_directed hn hd⟩

lemma mem_infi_sets {f : ι → filter α} (i : ι) : ∀{s}, s ∈ f i → s ∈ ⨅i, f i :=
show (⨅i, f i) ≤ f i, from infi_le _ _

@[elab_as_eliminator]
lemma infi_sets_induct {f : ι → filter α} {s : set α} (hs : s ∈ infi f) {p : set α → Prop}
  (uni : p univ)
  (ins : ∀{i s₁ s₂}, s₁ ∈ f i → p s₂ → p (s₁ ∩ s₂))
  (upw : ∀{s₁ s₂}, s₁ ⊆ s₂ → p s₁ → p s₂) : p s :=
begin
  rw [mem_infi_finite] at hs,
  simp only [mem_Union, (finset.inf_eq_infi _ _).symm] at hs,
  rcases hs with ⟨is, his⟩,
  revert s,
  refine finset.induction_on is _ _,
  { assume s hs, rwa [mem_top_sets.1 hs] },
  { rintros ⟨i⟩ js his ih s hs,
    rw [finset.inf_insert, mem_inf_sets] at hs,
    rcases hs with ⟨s₁, hs₁, s₂, hs₂, hs⟩,
    exact upw hs (ins hs₁ (ih hs₂)) }
end

/- principal equations -/

@[simp] lemma inf_principal {s t : set α} : principal s ⊓ principal t = principal (s ∩ t) :=
le_antisymm
  (by simp; exact ⟨s, subset.refl s, t, subset.refl t, by simp⟩)
  (by simp [le_inf_iff, inter_subset_left, inter_subset_right])

@[simp] lemma sup_principal {s t : set α} : principal s ⊔ principal t = principal (s ∪ t) :=
filter_eq $ set.ext $
  by simp only [union_subset_iff, union_subset_iff, mem_sup_sets, forall_const, iff_self, mem_principal_sets]

@[simp] lemma supr_principal {ι : Sort w} {s : ι → set α} : (⨆x, principal (s x)) = principal (⋃i, s i) :=
filter_eq $ set.ext $ assume x, by simp only [supr_sets_eq, mem_principal_sets, mem_Inter];
exact (@supr_le_iff (set α) _ _ _ _).symm

@[simp] lemma principal_eq_bot_iff {s : set α} : principal s = ⊥ ↔ s = ∅ :=
empty_in_sets_eq_bot.symm.trans $ mem_principal_sets.trans subset_empty_iff

lemma principal_ne_bot_iff {s : set α} : principal s ≠ ⊥ ↔ s.nonempty :=
(not_congr principal_eq_bot_iff).trans ne_empty_iff_nonempty

lemma is_compl_principal (s : set α) : is_compl (principal s) (principal (-s)) :=
⟨by simp only [inf_principal, inter_compl_self, principal_empty, le_refl],
  by simp only [sup_principal, union_compl_self, principal_univ, le_refl]⟩

lemma inf_principal_eq_bot {f : filter α} {s : set α} (hs : -s ∈ f) : f ⊓ principal s = ⊥ :=
empty_in_sets_eq_bot.mp ⟨_, hs, s, mem_principal_self s, assume x ⟨h₁, h₂⟩, h₁ h₂⟩

theorem mem_inf_principal (f : filter α) (s t : set α) :
  s ∈ f ⊓ principal t ↔ {x | x ∈ t → x ∈ s} ∈ f :=
begin
  simp only [← le_principal_iff, (is_compl_principal s).le_left_iff, disjoint, inf_assoc,
    inf_principal, imp_iff_not_or],
  rw [← disjoint, ← (is_compl_principal (t ∩ -s)).le_right_iff, compl_inter, compl_compl],
  refl
end

@[simp] lemma infi_principal_finset {ι : Type w} (s : finset ι) (f : ι → set α) :
  (⨅i∈s, principal (f i)) = principal (⋂i∈s, f i) :=
begin
  ext t,
  simp [mem_infi_sets_finset],
  split,
  { rintros ⟨p, hp, ht⟩,
    calc (⋂ (i : ι) (H : i ∈ s), f i) ≤ (⋂ (i : ι) (H : i ∈ s), p i) :
      infi_le_infi (λi, infi_le_infi (λhi, mem_principal_sets.1 (hp i hi)))
    ... ≤ t : ht },
  { assume h,
    exact ⟨f, λi hi, subset.refl _, h⟩ }
end

@[simp] lemma infi_principal_fintype {ι : Type w} [fintype ι] (f : ι → set α) :
  (⨅i, principal (f i)) = principal (⋂i, f i) :=
by simpa using infi_principal_finset finset.univ f

end lattice

/-! ### Eventually -/

/-- `f.eventually p` or `∀ᶠ x in f, p x` mean that `{x | p x} ∈ f`. E.g., `∀ᶠ x in at_top, p x`
means that `p` holds true for sufficiently large `x`. -/
protected def eventually (p : α → Prop) (f : filter α) : Prop := {x | p x} ∈ f

notation `∀ᶠ` binders ` in ` f `, ` r:(scoped p, filter.eventually p f) := r

lemma eventually_iff {f : filter α} {P : α → Prop} : (∀ᶠ x in f, P x) ↔ {x | P x} ∈ f :=
iff.rfl

lemma eventually_of_mem {f : filter α} {P : α → Prop} {U : set α} (hU : U ∈ f) (h : ∀ x ∈ U, P x) :
  ∀ᶠ x in f, P x :=
mem_sets_of_superset hU h

protected lemma eventually.and {p q : α → Prop} {f : filter α} :
  f.eventually p → f.eventually q → ∀ᶠ x in f, p x ∧ q x :=
inter_mem_sets

@[simp]
lemma eventually_true (f : filter α) : ∀ᶠ x in f, true := univ_mem_sets

lemma eventually_of_forall {p : α → Prop} (f : filter α) (hp : ∀ x, p x) :
  ∀ᶠ x in f, p x :=
univ_mem_sets' hp

@[simp] lemma eventually_false_iff_eq_bot {f : filter α} :
  (∀ᶠ x in f, false) ↔ f = ⊥ :=
empty_in_sets_eq_bot

@[simp] lemma eventually_const {f : filter α} (hf : f ≠ ⊥) {p : Prop} :
  (∀ᶠ x in f, p) ↔ p :=
classical.by_cases (λ h : p, by simp [h]) (λ h, by simp [h, hf])

lemma eventually.mp {p q : α → Prop} {f : filter α} (hp : ∀ᶠ x in f, p x)
  (hq : ∀ᶠ x in f, p x → q x) :
  ∀ᶠ x in f, q x :=
mp_sets hp hq

lemma eventually.mono {p q : α → Prop} {f : filter α} (hp : ∀ᶠ x in f, p x)
  (hq : ∀ x, p x → q x) :
  ∀ᶠ x in f, q x :=
hp.mp (f.eventually_of_forall hq)

@[simp] lemma eventually_and {p q : α → Prop} {f : filter α} :
  (∀ᶠ x in f, p x ∧ q x) ↔ (∀ᶠ x in f, p x) ∧ (∀ᶠ x in f, q x) :=
⟨λ h, ⟨h.mono $ λ _, and.left, h.mono $ λ _, and.right⟩, λ h, h.1.and h.2⟩

lemma eventually.congr {f : filter α} {p q : α → Prop} (h' : ∀ᶠ x in f, p x)
  (h : ∀ᶠ x in f, p x ↔ q x) : ∀ᶠ x in f, q x :=
h'.mp (h.mono $ λ x hx, hx.mp)

lemma eventually_congr {f : filter α} {p q : α → Prop} (h : ∀ᶠ x in f, p x ↔ q x) :
  (∀ᶠ x in f, p x) ↔ (∀ᶠ x in f, q x) :=
⟨λ hp, hp.congr h, λ hq, hq.congr $ by simpa only [iff.comm] using h⟩

@[simp] lemma eventually_or_distrib_left {f : filter α} {p : Prop} {q : α → Prop} :
  (∀ᶠ x in f, p ∨ q x) ↔ (p ∨ ∀ᶠ x in f, q x) :=
classical.by_cases (λ h : p, by simp [h]) (λ h, by simp [h])

@[simp] lemma eventually_or_distrib_right {f : filter α} {p : α → Prop} {q : Prop} :
  (∀ᶠ x in f, p x ∨ q) ↔ ((∀ᶠ x in f, p x) ∨ q) :=
by simp only [or_comm _ q, eventually_or_distrib_left]

@[simp] lemma eventually_imp_distrib_left {f : filter α} {p : Prop} {q : α → Prop} :
  (∀ᶠ x in f, p → q x) ↔ (p → ∀ᶠ x in f, q x) :=
by simp only [imp_iff_not_or, eventually_or_distrib_left]

@[simp]
lemma eventually_bot {p : α → Prop} : ∀ᶠ x in ⊥, p x := ⟨⟩

@[simp]
lemma eventually_top {p : α → Prop} : (∀ᶠ x in ⊤, p x) ↔ (∀ x, p x) :=
iff.rfl

lemma eventually_sup {p : α → Prop} {f g : filter α} :
  (∀ᶠ x in f ⊔ g, p x) ↔ (∀ᶠ x in f, p x) ∧ (∀ᶠ x in g, p x) :=
iff.rfl

@[simp]
lemma eventually_Sup {p : α → Prop} {fs : set (filter α)} :
  (∀ᶠ x in Sup fs, p x) ↔ (∀ f ∈ fs, ∀ᶠ x in f, p x) :=
iff.rfl

@[simp]
lemma eventually_supr {p : α → Prop} {fs : β → filter α} :
  (∀ᶠ x in (⨆ b, fs b), p x) ↔ (∀ b, ∀ᶠ x in fs b, p x) :=
mem_supr_sets

@[simp]
lemma eventually_principal {a : set α} {p : α → Prop} :
  (∀ᶠ x in principal a, p x) ↔ (∀ x ∈ a, p x) :=
iff.rfl

/-! ### Frequently -/

/-- `f.frequently p` or `∃ᶠ x in f, p x` mean that `{x | ¬p x} ∉ f`. E.g., `∃ᶠ x in at_top, p x`
means that there exist arbitrarily large `x` for which `p` holds true. -/
protected def frequently (p : α → Prop) (f : filter α) : Prop := ¬∀ᶠ x in f, ¬p x

notation `∃ᶠ` binders ` in ` f `, ` r:(scoped p, filter.frequently p f) := r

lemma eventually.frequently {f : filter α} (hf : f ≠ ⊥) {p : α → Prop} (h : ∀ᶠ x in f, p x) :
  ∃ᶠ x in f, p x :=
begin
  assume h',
  have := h.and h',
  simp only [and_not_self, eventually_false_iff_eq_bot] at this,
  exact hf this
end

lemma frequently.mp {p q : α → Prop} {f : filter α} (h : ∃ᶠ x in f, p x)
  (hpq : ∀ᶠ x in f, p x → q x) :
  ∃ᶠ x in f, q x :=
mt (λ hq, hq.mp $ hpq.mono $ λ x, mt) h

lemma frequently.mono {p q : α → Prop} {f : filter α} (h : ∃ᶠ x in f, p x)
  (hpq : ∀ x, p x → q x) :
  ∃ᶠ x in f, q x :=
h.mp (f.eventually_of_forall hpq)

lemma frequently.and_eventually {p q : α → Prop} {f : filter α}
  (hp : ∃ᶠ x in f, p x) (hq : ∀ᶠ x in f, q x) :
  ∃ᶠ x in f, p x ∧ q x :=
begin
  refine mt (λ h, hq.mp $ h.mono _) hp,
  assume x hpq hq hp,
  exact hpq ⟨hp, hq⟩
end

lemma frequently.exists {p : α → Prop} {f : filter α} (hp : ∃ᶠ x in f, p x) : ∃ x, p x :=
begin
  by_contradiction H,
  replace H : ∀ᶠ x in f, ¬ p x, from f.eventually_of_forall (not_exists.1 H),
  exact hp H
end

lemma eventually.exists {p : α → Prop} {f : filter α} (hp : ∀ᶠ x in f, p x) (hf : f ≠ ⊥) :
  ∃ x, p x :=
(hp.frequently hf).exists

lemma frequently_iff_forall_eventually_exists_and {p : α → Prop} {f : filter α} :
  (∃ᶠ x in f, p x) ↔ ∀ {q : α → Prop}, (∀ᶠ x in f, q x) → ∃ x, p x ∧ q x :=
⟨assume hp q hq, (hp.and_eventually hq).exists,
  assume H hp, by simpa only [and_not_self, exists_false] using H hp⟩

lemma frequently_iff {f : filter α} {P : α → Prop} :
  (∃ᶠ x in f, P x) ↔ ∀ {U}, U ∈ f → ∃ x ∈ U, P x :=
begin
  rw frequently_iff_forall_eventually_exists_and,
  split ; intro h,
  { intros U U_in,
    simpa [exists_prop, and_comm] using h U_in },
  { intros H H',
    simpa [and_comm] using h H' },
end

@[simp] lemma not_eventually {p : α → Prop} {f : filter α} :
  (¬ ∀ᶠ x in f, p x) ↔ (∃ᶠ x in f, ¬ p x) :=
by simp [filter.frequently]

@[simp] lemma not_frequently {p : α → Prop} {f : filter α} :
  (¬ ∃ᶠ x in f, p x) ↔ (∀ᶠ x in f, ¬ p x) :=
by simp only [filter.frequently, not_not]

@[simp] lemma frequently_true_iff_ne_bot (f : filter α) : (∃ᶠ x in f, true) ↔ f ≠ ⊥ :=
by simp [filter.frequently, -not_eventually, eventually_false_iff_eq_bot]

@[simp] lemma frequently_false (f : filter α) : ¬ ∃ᶠ x in f, false := by simp

@[simp] lemma frequently_const {f : filter α} (hf : f ≠ ⊥) {p : Prop} :
  (∃ᶠ x in f, p) ↔ p :=
classical.by_cases (λ h : p, by simp [*]) (λ h, by simp [*])

@[simp] lemma frequently_or_distrib {f : filter α} {p q : α → Prop} :
  (∃ᶠ x in f, p x ∨ q x) ↔ (∃ᶠ x in f, p x) ∨ (∃ᶠ x in f, q x) :=
by simp only [filter.frequently, ← not_and_distrib, not_or_distrib, eventually_and]

lemma frequently_or_distrib_left {f : filter α} (hf : f ≠ ⊥) {p : Prop} {q : α → Prop} :
  (∃ᶠ x in f, p ∨ q x) ↔ (p ∨ ∃ᶠ x in f, q x) :=
by simp [hf]

lemma frequently_or_distrib_right {f : filter α} (hf : f ≠ ⊥) {p : α → Prop} {q : Prop} :
  (∃ᶠ x in f, p x ∨ q) ↔ (∃ᶠ x in f, p x) ∨ q :=
by simp [hf]

@[simp] lemma frequently_imp_distrib {f : filter α} {p q : α → Prop} :
  (∃ᶠ x in f, p x → q x) ↔ ((∀ᶠ x in f, p x) → ∃ᶠ x in f, q x) :=
by simp [imp_iff_not_or, not_eventually, frequently_or_distrib]

lemma frequently_imp_distrib_left {f : filter α} (hf : f ≠ ⊥) {p : Prop} {q : α → Prop} :
  (∃ᶠ x in f, p → q x) ↔ (p → ∃ᶠ x in f, q x) :=
by simp [hf]

lemma frequently_imp_distrib_right {f : filter α} (hf : f ≠ ⊥) {p : α → Prop} {q : Prop} :
  (∃ᶠ x in f, p x → q) ↔ ((∀ᶠ x in f, p x) → q) :=
by simp [hf]

@[simp] lemma eventually_imp_distrib_right {f : filter α} {p : α → Prop} {q : Prop} :
  (∀ᶠ x in f, p x → q) ↔ ((∃ᶠ x in f, p x) → q) :=
by simp only [imp_iff_not_or, eventually_or_distrib_right, not_frequently]

@[simp] lemma frequently_bot {p : α → Prop} : ¬ ∃ᶠ x in ⊥, p x := by simp

@[simp]
lemma frequently_top {p : α → Prop} : (∃ᶠ x in ⊤, p x) ↔ (∃ x, p x) :=
by simp [filter.frequently]

lemma inf_ne_bot_iff_frequently_left {f g : filter α} :
  f ⊓ g ≠ ⊥ ↔ ∀ {p : α → Prop}, (∀ᶠ x in f, p x) → ∃ᶠ x in g, p x :=
begin
  rw filter.inf_ne_bot_iff,
  split ; intro h,
  { intros U U_in H,
    rcases h U_in H with ⟨x, hx, hx'⟩,
    exact hx' hx},
  { intros U V U_in V_in,
    classical,
    by_contra H,
    exact h U_in (mem_sets_of_superset V_in $ λ v v_in v_in', H ⟨v, v_in', v_in⟩) }
end

lemma inf_ne_bot_iff_frequently_right {f g : filter α} :
  f ⊓ g ≠ ⊥ ↔ ∀ {p : α → Prop}, (∀ᶠ x in g, p x) → ∃ᶠ x in f, p x :=
by { rw inf_comm, exact filter.inf_ne_bot_iff_frequently_left }

@[simp]
lemma frequently_principal {a : set α} {p : α → Prop} :
  (∃ᶠ x in principal a, p x) ↔ (∃ x ∈ a, p x) :=
by simp [filter.frequently, not_forall]

lemma frequently_sup {p : α → Prop} {f g : filter α} :
  (∃ᶠ x in f ⊔ g, p x) ↔ (∃ᶠ x in f, p x) ∨ (∃ᶠ x in g, p x) :=
by simp only [filter.frequently, eventually_sup, not_and_distrib]

@[simp]
lemma frequently_Sup {p : α → Prop} {fs : set (filter α)} :
  (∃ᶠ x in Sup fs, p x) ↔ (∃ f ∈ fs, ∃ᶠ x in f, p x) :=
by simp [filter.frequently, -not_eventually, not_forall]

@[simp]
lemma frequently_supr {p : α → Prop} {fs : β → filter α} :
  (∃ᶠ x in (⨆ b, fs b), p x) ↔ (∃ b, ∃ᶠ x in fs b, p x) :=
by simp [filter.frequently, -not_eventually, not_forall]

/-! ### Push-forwards, pull-backs, and the monad structure -/

section map

/-- The forward map of a filter -/
def map (m : α → β) (f : filter α) : filter β :=
{ sets             := preimage m ⁻¹' f.sets,
  univ_sets        := univ_mem_sets,
  sets_of_superset := assume s t hs st, mem_sets_of_superset hs $ preimage_mono st,
  inter_sets       := assume s t hs ht, inter_mem_sets hs ht }

@[simp] lemma map_principal {s : set α} {f : α → β} :
  map f (principal s) = principal (set.image f s) :=
filter_eq $ set.ext $ assume a, image_subset_iff.symm

variables {f : filter α} {m : α → β} {m' : β → γ} {s : set α} {t : set β}

@[simp] lemma eventually_map {P : β → Prop} :
  (∀ᶠ b in map m f, P b) ↔ ∀ᶠ a in f, P (m a) :=
iff.rfl

@[simp] lemma frequently_map {P : β → Prop} :
  (∃ᶠ b in map m f, P b) ↔ ∃ᶠ a in f, P (m a) :=
iff.rfl

@[simp] lemma mem_map : t ∈ map m f ↔ {x | m x ∈ t} ∈ f := iff.rfl

lemma image_mem_map (hs : s ∈ f) : m '' s ∈ map m f :=
f.sets_of_superset hs $ subset_preimage_image m s

lemma range_mem_map : range m ∈ map m f :=
by rw ←image_univ; exact image_mem_map univ_mem_sets

lemma mem_map_sets_iff : t ∈ map m f ↔ (∃s∈f, m '' s ⊆ t) :=
iff.intro
  (assume ht, ⟨set.preimage m t, ht, image_preimage_subset _ _⟩)
  (assume ⟨s, hs, ht⟩, mem_sets_of_superset (image_mem_map hs) ht)

@[simp] lemma map_id : filter.map id f = f :=
filter_eq $ rfl

@[simp] lemma map_compose : filter.map m' ∘ filter.map m = filter.map (m' ∘ m) :=
funext $ assume _, filter_eq $ rfl

@[simp] lemma map_map : filter.map m' (filter.map m f) = filter.map (m' ∘ m) f :=
congr_fun (@@filter.map_compose m m') f

end map

section comap

/-- The inverse map of a filter -/
def comap (m : α → β) (f : filter β) : filter α :=
{ sets             := { s | ∃t∈ f, m ⁻¹' t ⊆ s },
  univ_sets        := ⟨univ, univ_mem_sets, by simp only [subset_univ, preimage_univ]⟩,
  sets_of_superset := assume a b ⟨a', ha', ma'a⟩ ab,
    ⟨a', ha', subset.trans ma'a ab⟩,
  inter_sets       := assume a b ⟨a', ha₁, ha₂⟩ ⟨b', hb₁, hb₂⟩,
    ⟨a' ∩ b', inter_mem_sets ha₁ hb₁, inter_subset_inter ha₂ hb₂⟩ }

@[simp] lemma eventually_comap {f : filter β} {φ : α → β} {P : α → Prop} :
  (∀ᶠ a in comap φ f, P a) ↔ ∀ᶠ b in f, ∀ a, φ a = b → P a :=
begin
  split ; intro h,
  { rcases h with ⟨t, t_in, ht⟩,
    apply mem_sets_of_superset t_in,
    rintros y y_in _ rfl,
    apply ht y_in },
  { exact ⟨_, h, λ _ x_in, x_in _ rfl⟩ }
end

@[simp] lemma frequently_comap {f : filter β} {φ : α → β} {P : α → Prop} :
  (∃ᶠ a in comap φ f, P a) ↔ ∃ᶠ b in f, ∃ a, φ a = b ∧ P a :=
begin
  classical,
  erw [← not_iff_not, not_not, not_not, filter.eventually_comap],
  simp only [not_exists, not_and],
end

end comap

/-- The monadic bind operation on filter is defined the usual way in terms of `map` and `join`.

Unfortunately, this `bind` does not result in the expected applicative. See `filter.seq` for the
applicative instance. -/
def bind (f : filter α) (m : α → filter β) : filter β := join (map m f)

/-- The applicative sequentiation operation. This is not induced by the bind operation. -/
def seq (f : filter (α → β)) (g : filter α) : filter β :=
⟨{ s | ∃u∈ f, ∃t∈ g, (∀m∈u, ∀x∈t, (m : α → β) x ∈ s) },
  ⟨univ, univ_mem_sets, univ, univ_mem_sets, by simp only [forall_prop_of_true, mem_univ, forall_true_iff]⟩,
  assume s₀ s₁ ⟨t₀, t₁, h₀, h₁, h⟩ hst, ⟨t₀, t₁, h₀, h₁, assume x hx y hy, hst $ h _ hx _ hy⟩,
  assume s₀ s₁ ⟨t₀, ht₀, t₁, ht₁, ht⟩ ⟨u₀, hu₀, u₁, hu₁, hu⟩,
    ⟨t₀ ∩ u₀, inter_mem_sets ht₀ hu₀, t₁ ∩ u₁, inter_mem_sets ht₁ hu₁,
      assume x ⟨hx₀, hx₁⟩ x ⟨hy₀, hy₁⟩, ⟨ht _ hx₀ _ hy₀, hu _ hx₁ _ hy₁⟩⟩⟩

/-- `pure x` is the set of sets that contain `x`. It is equal to `principal {x}` but
with this definition we have `s ∈ pure a` defeq `a ∈ s`. -/
instance : has_pure filter :=
⟨λ (α : Type u) x,
  { sets := {s | x ∈ s},
    inter_sets := λ s t, and.intro,
    sets_of_superset := λ s t hs hst, hst hs,
    univ_sets := trivial }⟩

instance : has_bind filter := ⟨@filter.bind⟩

instance : has_seq filter := ⟨@filter.seq⟩

instance : functor filter := { map := @filter.map }

lemma pure_sets (a : α) : (pure a : filter α).sets = {s | a ∈ s} := rfl

@[simp] lemma mem_pure_sets {a : α} {s : set α} : s ∈ (pure a : filter α) ↔ a ∈ s := iff.rfl

lemma pure_eq_principal (a : α) : (pure a : filter α) = principal {a} :=
filter.ext $ λ s, by simp only [mem_pure_sets, mem_principal_sets, singleton_subset_iff]

@[simp] lemma map_pure (f : α → β) (a : α) : map f (pure a) = pure (f a) :=
filter.ext $ λ s, iff.rfl

@[simp] lemma join_pure (f : filter α) : join (pure f) = f := filter.ext $ λ s, iff.rfl

@[simp] lemma pure_bind (a : α) (m : α → filter β) :
  bind (pure a) m = m a :=
by simp only [has_bind.bind, bind, map_pure, join_pure]

section
-- this section needs to be before applicative, otherwise the wrong instance will be chosen
/-- The monad structure on filters. -/
protected def monad : monad filter := { map := @filter.map }

local attribute [instance] filter.monad
protected lemma is_lawful_monad : is_lawful_monad filter :=
{ id_map     := assume α f, filter_eq rfl,
  pure_bind  := assume α β, pure_bind,
  bind_assoc := assume α β γ f m₁ m₂, filter_eq rfl,
  bind_pure_comp_eq_map := assume α β f x, filter.ext $ λ s,
    by simp only [has_bind.bind, bind, functor.map, mem_map, mem_join_sets, mem_set_of_eq,
      function.comp, mem_pure_sets] }
end

instance : applicative filter := { map := @filter.map, seq := @filter.seq }

instance : alternative filter :=
{ failure := λα, ⊥,
  orelse  := λα x y, x ⊔ y }

@[simp] lemma map_def {α β} (m : α → β) (f : filter α) : m <$> f = map m f := rfl

@[simp] lemma bind_def {α β} (f : filter α) (m : α → filter β) : f >>= m = bind f m := rfl

/- map and comap equations -/
section map
variables {f f₁ f₂ : filter α} {g g₁ g₂ : filter β} {m : α → β} {m' : β → γ} {s : set α} {t : set β}

@[simp] theorem mem_comap_sets : s ∈ comap m g ↔ ∃t∈ g, m ⁻¹' t ⊆ s := iff.rfl

theorem preimage_mem_comap (ht : t ∈ g) : m ⁻¹' t ∈ comap m g :=
⟨t, ht, subset.refl _⟩

lemma comap_id : comap id f = f :=
le_antisymm (assume s, preimage_mem_comap) (assume s ⟨t, ht, hst⟩, mem_sets_of_superset ht hst)

lemma comap_comap_comp {m : γ → β} {n : β → α} : comap m (comap n f) = comap (n ∘ m) f :=
le_antisymm
  (assume c ⟨b, hb, (h : preimage (n ∘ m) b ⊆ c)⟩, ⟨preimage n b, preimage_mem_comap hb, h⟩)
  (assume c ⟨b, ⟨a, ha, (h₁ : preimage n a ⊆ b)⟩, (h₂ : preimage m b ⊆ c)⟩,
    ⟨a, ha, show preimage m (preimage n a) ⊆ c, from subset.trans (preimage_mono h₁) h₂⟩)

@[simp] theorem comap_principal {t : set β} : comap m (principal t) = principal (m ⁻¹' t) :=
filter_eq $ set.ext $ assume s,
  ⟨assume ⟨u, (hu : t ⊆ u), (b : preimage m u ⊆ s)⟩, subset.trans (preimage_mono hu) b,
    assume : preimage m t ⊆ s, ⟨t, subset.refl t, this⟩⟩

lemma map_le_iff_le_comap : map m f ≤ g ↔ f ≤ comap m g :=
⟨assume h s ⟨t, ht, hts⟩, mem_sets_of_superset (h ht) hts, assume h s ht, h ⟨_, ht, subset.refl _⟩⟩

lemma gc_map_comap (m : α → β) : galois_connection (map m) (comap m) :=
assume f g, map_le_iff_le_comap

lemma map_mono : monotone (map m) := (gc_map_comap m).monotone_l
lemma comap_mono : monotone (comap m) := (gc_map_comap m).monotone_u

@[simp] lemma map_bot : map m ⊥ = ⊥ := (gc_map_comap m).l_bot
@[simp] lemma map_sup : map m (f₁ ⊔ f₂) = map m f₁ ⊔ map m f₂ := (gc_map_comap m).l_sup
@[simp] lemma map_supr {f : ι → filter α} : map m (⨆i, f i) = (⨆i, map m (f i)) :=
(gc_map_comap m).l_supr

@[simp] lemma comap_top : comap m ⊤ = ⊤ := (gc_map_comap m).u_top
@[simp] lemma comap_inf : comap m (g₁ ⊓ g₂) = comap m g₁ ⊓ comap m g₂ := (gc_map_comap m).u_inf
@[simp] lemma comap_infi {f : ι → filter β} : comap m (⨅i, f i) = (⨅i, comap m (f i)) :=
(gc_map_comap m).u_infi

lemma le_comap_top (f : α → β) (l : filter α) : l ≤ comap f ⊤ :=
by rw [comap_top]; exact le_top

lemma map_comap_le : map m (comap m g) ≤ g := (gc_map_comap m).l_u_le _
lemma le_comap_map : f ≤ comap m (map m f) := (gc_map_comap m).le_u_l _

@[simp] lemma comap_bot : comap m ⊥ = ⊥ :=
bot_unique $ assume s _, ⟨∅, by simp only [mem_bot_sets], by simp only [empty_subset, preimage_empty]⟩

lemma comap_supr {ι} {f : ι → filter β} {m : α → β} :
  comap m (supr f) = (⨆i, comap m (f i)) :=
le_antisymm
  (assume s hs,
    have ∀i, ∃t, t ∈ f i ∧ m ⁻¹' t ⊆ s, by simpa only [mem_comap_sets, exists_prop, mem_supr_sets] using mem_supr_sets.1 hs,
    let ⟨t, ht⟩ := classical.axiom_of_choice this in
    ⟨⋃i, t i, mem_supr_sets.2 $ assume i, (f i).sets_of_superset (ht i).1 (subset_Union _ _),
      begin
        rw [preimage_Union, Union_subset_iff],
        assume i,
        exact (ht i).2
      end⟩)
  (supr_le $ assume i, comap_mono $ le_supr _ _)

lemma comap_Sup {s : set (filter β)} {m : α → β} : comap m (Sup s) = (⨆f∈s, comap m f) :=
by simp only [Sup_eq_supr, comap_supr, eq_self_iff_true]

lemma comap_sup : comap m (g₁ ⊔ g₂) = comap m g₁ ⊔ comap m g₂ :=
le_antisymm
  (assume s ⟨⟨t₁, ht₁, hs₁⟩, ⟨t₂, ht₂, hs₂⟩⟩,
    ⟨t₁ ∪ t₂,
      ⟨g₁.sets_of_superset ht₁ (subset_union_left _ _), g₂.sets_of_superset ht₂ (subset_union_right _ _)⟩,
      union_subset hs₁ hs₂⟩)
  ((@comap_mono _ _ m).le_map_sup _ _)

lemma map_comap {f : filter β} {m : α → β} (hf : range m ∈ f) : (f.comap m).map m = f :=
le_antisymm
  map_comap_le
  (assume t' ⟨t, ht, sub⟩, by filter_upwards [ht, hf]; rintros x hxt ⟨y, rfl⟩; exact sub hxt)

lemma comap_map {f : filter α} {m : α → β} (h : ∀ x y, m x = m y → x = y) :
  comap m (map m f) = f :=
have ∀s, preimage m (image m s) = s,
  from assume s, preimage_image_eq s h,
le_antisymm
  (assume s hs, ⟨
    image m s,
    f.sets_of_superset hs $ by simp only [this, subset.refl],
    by simp only [this, subset.refl]⟩)
  le_comap_map

lemma le_of_map_le_map_inj' {f g : filter α} {m : α → β} {s : set α}
  (hsf : s ∈ f) (hsg : s ∈ g) (hm : ∀x∈s, ∀y∈s, m x = m y → x = y)
  (h : map m f ≤ map m g) : f ≤ g :=
assume t ht, by filter_upwards [hsf, h $ image_mem_map (inter_mem_sets hsg ht)]
assume a has ⟨b, ⟨hbs, hb⟩, h⟩,
have b = a, from hm _ hbs _ has h,
this ▸ hb

lemma le_of_map_le_map_inj_iff {f g : filter α} {m : α → β} {s : set α}
  (hsf : s ∈ f) (hsg : s ∈ g) (hm : ∀x∈s, ∀y∈s, m x = m y → x = y) :
  map m f ≤ map m g ↔ f ≤ g :=
iff.intro (le_of_map_le_map_inj' hsf hsg hm) (λ h, map_mono h)

lemma eq_of_map_eq_map_inj' {f g : filter α} {m : α → β} {s : set α}
  (hsf : s ∈ f) (hsg : s ∈ g) (hm : ∀x∈s, ∀y∈s, m x = m y → x = y)
  (h : map m f = map m g) : f = g :=
le_antisymm
  (le_of_map_le_map_inj' hsf hsg hm $ le_of_eq h)
  (le_of_map_le_map_inj' hsg hsf hm $ le_of_eq h.symm)

lemma map_inj {f g : filter α} {m : α → β} (hm : ∀ x y, m x = m y → x = y) (h : map m f = map m g) :
  f = g :=
have comap m (map m f) = comap m (map m g), by rw h,
by rwa [comap_map hm, comap_map hm] at this

theorem le_map_comap_of_surjective' {f : α → β} {l : filter β} {u : set β} (ul : u ∈ l)
    (hf : ∀ y ∈ u, ∃ x, f x = y) :
  l ≤ map f (comap f l) :=
assume s ⟨t, tl, ht⟩,
have t ∩ u ⊆ s, from
  assume x ⟨xt, xu⟩,
  exists.elim (hf x xu) $ λ a faeq,
  by { rw ←faeq, apply ht, change f a ∈ t, rw faeq, exact xt },
mem_sets_of_superset (inter_mem_sets tl ul) this

theorem map_comap_of_surjective' {f : α → β} {l : filter β} {u : set β} (ul : u ∈ l)
    (hf : ∀ y ∈ u, ∃ x, f x = y)  :
  map f (comap f l) = l :=
le_antisymm map_comap_le (le_map_comap_of_surjective' ul hf)

theorem le_map_comap_of_surjective {f : α → β} (hf : function.surjective f) (l : filter β) :
  l ≤ map f (comap f l) :=
le_map_comap_of_surjective' univ_mem_sets (λ y _, hf y)

theorem map_comap_of_surjective {f : α → β} (hf : function.surjective f) (l : filter β) :
  map f (comap f l) = l :=
le_antisymm map_comap_le (le_map_comap_of_surjective hf l)

lemma comap_ne_bot {f : filter β} {m : α → β} (hm : ∀t∈ f, ∃a, m a ∈ t) :
  comap m f ≠ ⊥ :=
forall_sets_nonempty_iff_ne_bot.mp $ assume s ⟨t, ht, t_s⟩,
  set.nonempty.mono t_s (hm t ht)

lemma comap_ne_bot_of_range_mem {f : filter β} {m : α → β}
  (hf : f ≠ ⊥) (hm : range m ∈ f) : comap m f ≠ ⊥ :=
comap_ne_bot $ assume t ht,
  let ⟨_, ha, a, rfl⟩ := nonempty_of_mem_sets hf (inter_mem_sets ht hm)
  in ⟨a, ha⟩

lemma comap_inf_principal_ne_bot_of_image_mem {f : filter β} {m : α → β}
  (hf : f ≠ ⊥) {s : set α} (hs : m '' s ∈ f) : (comap m f ⊓ principal s) ≠ ⊥ :=
begin
  refine compl_compl s ▸ mt mem_sets_of_eq_bot _,
  rintros ⟨t, ht, hts⟩,
  rcases nonempty_of_mem_sets hf (inter_mem_sets hs ht) with ⟨_, ⟨x, hxs, rfl⟩, hxt⟩,
  exact absurd hxs (hts hxt)
end

lemma comap_ne_bot_of_surj {f : filter β} {m : α → β}
  (hf : f ≠ ⊥) (hm : function.surjective m) : comap m f ≠ ⊥ :=
comap_ne_bot_of_range_mem hf $ univ_mem_sets' hm

lemma comap_ne_bot_of_image_mem {f : filter β} {m : α → β} (hf : f ≠ ⊥)
  {s : set α} (hs : m '' s ∈ f) : comap m f ≠ ⊥ :=
ne_bot_of_le_ne_bot (comap_inf_principal_ne_bot_of_image_mem hf hs) inf_le_left

@[simp] lemma map_eq_bot_iff : map m f = ⊥ ↔ f = ⊥ :=
⟨by rw [←empty_in_sets_eq_bot, ←empty_in_sets_eq_bot]; exact id,
  assume h, by simp only [h, eq_self_iff_true, map_bot]⟩

lemma map_ne_bot (hf : f ≠ ⊥) : map m f ≠ ⊥ :=
assume h, hf $ by rwa [map_eq_bot_iff] at h

lemma map_ne_bot_iff (f : α → β) {F : filter α} : map f F ≠ ⊥ ↔ F ≠ ⊥ :=
by rw [not_iff_not, map_eq_bot_iff]

lemma sInter_comap_sets (f : α → β) (F : filter β) :
  ⋂₀(comap f F).sets = ⋂ U ∈ F, f ⁻¹' U :=
begin
  ext x,
  suffices : (∀ (A : set α) (B : set β), B ∈ F → f ⁻¹' B ⊆ A → x ∈ A) ↔
    ∀ (B : set β), B ∈ F → f x ∈ B,
  by simp only [mem_sInter, mem_Inter, mem_comap_sets, this, and_imp, mem_comap_sets, exists_prop, mem_sInter,
    iff_self, mem_Inter, mem_preimage, exists_imp_distrib],
  split,
  { intros h U U_in,
    simpa only [set.subset.refl, forall_prop_of_true, mem_preimage] using h (f ⁻¹' U) U U_in },
  { intros h V U U_in f_U_V,
    exact f_U_V (h U U_in) },
end
end map

lemma map_cong {m₁ m₂ : α → β} {f : filter α} (h : {x | m₁ x = m₂ x} ∈ f) :
  map m₁ f = map m₂ f :=
have ∀(m₁ m₂ : α → β) (h : {x | m₁ x = m₂ x} ∈ f), map m₁ f ≤ map m₂ f,
begin
  intros  m₁ m₂ h s hs,
  show {x | m₁ x ∈ s} ∈ f,
  filter_upwards [h, hs],
  simp only [subset_def, mem_preimage, mem_set_of_eq, forall_true_iff] {contextual := tt}
end,
le_antisymm (this m₁ m₂ h) (this m₂ m₁ $ mem_sets_of_superset h $ assume x, eq.symm)

-- this is a generic rule for monotone functions:
lemma map_infi_le {f : ι → filter α} {m : α → β} :
  map m (infi f) ≤ (⨅ i, map m (f i)) :=
le_infi $ assume i, map_mono $ infi_le _ _

lemma map_infi_eq {f : ι → filter α} {m : α → β} (hf : directed (≥) f) (hι : nonempty ι) :
  map m (infi f) = (⨅ i, map m (f i)) :=
le_antisymm
  map_infi_le
  (assume s (hs : preimage m s ∈ infi f),
    have ∃i, preimage m s ∈ f i,
      by simp only [infi_sets_eq hf hι, mem_Union] at hs; assumption,
    let ⟨i, hi⟩ := this in
    have (⨅ i, map m (f i)) ≤ principal s, from
      infi_le_of_le i $ by simp only [le_principal_iff, mem_map]; assumption,
    by simp only [filter.le_principal_iff] at this; assumption)

lemma map_binfi_eq {ι : Type w} {f : ι → filter α} {m : α → β} {p : ι → Prop}
  (h : directed_on (f ⁻¹'o (≥)) {x | p x}) (ne : ∃i, p i) :
  map m (⨅i (h : p i), f i) = (⨅i (h: p i), map m (f i)) :=
let ⟨i, hi⟩ := ne in
calc map m (⨅i (h : p i), f i) = map m (⨅i:subtype p, f i.val) : by simp only [infi_subtype, eq_self_iff_true]
  ... = (⨅i:subtype p, map m (f i.val)) : map_infi_eq
    (assume ⟨x, hx⟩ ⟨y, hy⟩, match h x hx y hy with ⟨z, h₁, h₂, h₃⟩ := ⟨⟨z, h₁⟩, h₂, h₃⟩ end)
    ⟨⟨i, hi⟩⟩
  ... = (⨅i (h : p i), map m (f i)) : by simp only [infi_subtype, eq_self_iff_true]

lemma map_inf_le {f g : filter α} {m : α → β} : map m (f ⊓ g) ≤ map m f ⊓ map m g :=
(@map_mono _ _ m).map_inf_le f g

lemma map_inf' {f g : filter α} {m : α → β} {t : set α} (htf : t ∈ f) (htg : t ∈ g)
  (h : ∀x∈t, ∀y∈t, m x = m y → x = y) : map m (f ⊓ g) = map m f ⊓ map m g :=
begin
  refine le_antisymm map_inf_le (assume s hs, _),
  simp only [map, mem_inf_sets, exists_prop, mem_map, mem_preimage, mem_inf_sets] at hs ⊢,
  rcases hs with ⟨t₁, h₁, t₂, h₂, hs⟩,
  refine ⟨m '' (t₁ ∩ t), _, m '' (t₂ ∩ t), _, _⟩,
  { filter_upwards [h₁, htf] assume a h₁ h₂, mem_image_of_mem _ ⟨h₁, h₂⟩ },
  { filter_upwards [h₂, htg] assume a h₁ h₂, mem_image_of_mem _ ⟨h₁, h₂⟩ },
  { rw [image_inter_on],
    { refine image_subset_iff.2 _,
      exact λ x ⟨⟨h₁, _⟩, h₂, _⟩, hs ⟨h₁, h₂⟩ },
    { exact λ x ⟨_, hx⟩ y ⟨_, hy⟩, h x hx y hy } }
end

lemma map_inf {f g : filter α} {m : α → β} (h : function.injective m) :
  map m (f ⊓ g) = map m f ⊓ map m g :=
map_inf' univ_mem_sets univ_mem_sets (assume x _ y _ hxy, h hxy)

lemma map_eq_comap_of_inverse {f : filter α} {m : α → β} {n : β → α}
  (h₁ : m ∘ n = id) (h₂ : n ∘ m = id) : map m f = comap n f :=
le_antisymm
  (assume b ⟨a, ha, (h : preimage n a ⊆ b)⟩, f.sets_of_superset ha $
    calc a = preimage (n ∘ m) a : by simp only [h₂, preimage_id, eq_self_iff_true]
      ... ⊆ preimage m b : preimage_mono h)
  (assume b (hb : preimage m b ∈ f),
    ⟨preimage m b, hb, show preimage (m ∘ n) b ⊆ b, by simp only [h₁]; apply subset.refl⟩)

lemma map_swap_eq_comap_swap {f : filter (α × β)} : prod.swap <$> f = comap prod.swap f :=
map_eq_comap_of_inverse prod.swap_swap_eq prod.swap_swap_eq

lemma le_map {f : filter α} {m : α → β} {g : filter β} (h : ∀s∈ f, m '' s ∈ g) :
  g ≤ f.map m :=
assume s hs, mem_sets_of_superset (h _ hs) $ image_preimage_subset _ _

protected lemma push_pull (f : α → β) (F : filter α) (G : filter β) :
  map f (F ⊓ comap f G) = map f F ⊓ G :=
begin
  apply le_antisymm,
  { calc map f (F ⊓ comap f G) ≤ map f F ⊓ (map f $ comap f G) : map_inf_le
      ... ≤ map f F ⊓ G : inf_le_inf_left (map f F) map_comap_le },
  { rintros U ⟨V, V_in, W, ⟨Z, Z_in, hZ⟩, h⟩,
    rw ← image_subset_iff at h,
    use [f '' V, image_mem_map V_in, Z, Z_in],
    refine subset.trans _ h,
    have : f '' (V ∩ f ⁻¹' Z) ⊆ f '' (V ∩ W),
      from  image_subset _ (inter_subset_inter_right _ ‹_›),
    rwa set.push_pull at this }
end

protected lemma push_pull' (f : α → β) (F : filter α) (G : filter β) :
  map f (comap f G ⊓ F) = G ⊓ map f F :=
by simp only [filter.push_pull, inf_comm]

section applicative

lemma singleton_mem_pure_sets {a : α} : {a} ∈ (pure a : filter α) :=
mem_singleton a

lemma pure_inj : function.injective (pure : α → filter α) :=
assume a b hab, (filter.ext_iff.1 hab {x | a = x}).1 rfl

@[simp] lemma pure_ne_bot {α : Type u} {a : α} : pure a ≠ (⊥ : filter α) :=
mt empty_in_sets_eq_bot.2 $ not_mem_empty a

@[simp] lemma le_pure_iff {f : filter α} {a : α} : f ≤ pure a ↔ {a} ∈ f :=
⟨λ h, h singleton_mem_pure_sets,
  λ h s hs, mem_sets_of_superset h $ singleton_subset_iff.2 hs⟩

lemma mem_seq_sets_def {f : filter (α → β)} {g : filter α} {s : set β} :
  s ∈ f.seq g ↔ (∃u ∈ f, ∃t ∈ g, ∀x∈u, ∀y∈t, (x : α → β) y ∈ s) :=
iff.rfl

lemma mem_seq_sets_iff {f : filter (α → β)} {g : filter α} {s : set β} :
  s ∈ f.seq g ↔ (∃u ∈ f, ∃t ∈ g, set.seq u t ⊆ s) :=
by simp only [mem_seq_sets_def, seq_subset, exists_prop, iff_self]

lemma mem_map_seq_iff {f : filter α} {g : filter β} {m : α → β → γ} {s : set γ} :
  s ∈ (f.map m).seq g ↔ (∃t u, t ∈ g ∧ u ∈ f ∧ ∀x∈u, ∀y∈t, m x y ∈ s) :=
iff.intro
  (assume ⟨t, ht, s, hs, hts⟩, ⟨s, m ⁻¹' t, hs, ht, assume a, hts _⟩)
  (assume ⟨t, s, ht, hs, hts⟩, ⟨m '' s, image_mem_map hs, t, ht, assume f ⟨a, has, eq⟩, eq ▸ hts _ has⟩)

lemma seq_mem_seq_sets {f : filter (α → β)} {g : filter α} {s : set (α → β)} {t : set α}
  (hs : s ∈ f) (ht : t ∈ g) : s.seq t ∈ f.seq g :=
⟨s, hs, t, ht, assume f hf a ha, ⟨f, hf, a, ha, rfl⟩⟩

lemma le_seq {f : filter (α → β)} {g : filter α} {h : filter β}
  (hh : ∀t ∈ f, ∀u ∈ g, set.seq t u ∈ h) : h ≤ seq f g :=
assume s ⟨t, ht, u, hu, hs⟩, mem_sets_of_superset (hh _ ht _ hu) $
  assume b ⟨m, hm, a, ha, eq⟩, eq ▸ hs _ hm _ ha

lemma seq_mono {f₁ f₂ : filter (α → β)} {g₁ g₂ : filter α}
  (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) : f₁.seq g₁ ≤ f₂.seq g₂ :=
le_seq $ assume s hs t ht, seq_mem_seq_sets (hf hs) (hg ht)

@[simp] lemma pure_seq_eq_map (g : α → β) (f : filter α) : seq (pure g) f = f.map g :=
begin
  refine le_antisymm  (le_map $ assume s hs, _) (le_seq $ assume s hs t ht, _),
  { rw ← singleton_seq, apply seq_mem_seq_sets _ hs,
    exact singleton_mem_pure_sets },
  { refine sets_of_superset (map g f) (image_mem_map ht) _,
    rintros b ⟨a, ha, rfl⟩, exact ⟨g, hs, a, ha, rfl⟩ }
end

@[simp] lemma seq_pure (f : filter (α → β)) (a : α) : seq f (pure a) = map (λg:α → β, g a) f :=
begin
  refine le_antisymm (le_map $ assume s hs, _) (le_seq $ assume s hs t ht, _),
  { rw ← seq_singleton,
    exact seq_mem_seq_sets hs singleton_mem_pure_sets },
  { refine sets_of_superset (map (λg:α→β, g a) f) (image_mem_map hs) _,
    rintros b ⟨g, hg, rfl⟩, exact ⟨g, hg, a, ht, rfl⟩ }
end

@[simp] lemma seq_assoc (x : filter α) (g : filter (α → β)) (h : filter (β → γ)) :
  seq h (seq g x) = seq (seq (map (∘) h) g) x :=
begin
  refine le_antisymm (le_seq $ assume s hs t ht, _) (le_seq $ assume s hs t ht, _),
  { rcases mem_seq_sets_iff.1 hs with ⟨u, hu, v, hv, hs⟩,
    rcases mem_map_sets_iff.1 hu with ⟨w, hw, hu⟩,
    refine mem_sets_of_superset _
      (set.seq_mono (subset.trans (set.seq_mono hu (subset.refl _)) hs) (subset.refl _)),
    rw ← set.seq_seq,
    exact seq_mem_seq_sets hw (seq_mem_seq_sets hv ht) },
  { rcases mem_seq_sets_iff.1 ht with ⟨u, hu, v, hv, ht⟩,
    refine mem_sets_of_superset _ (set.seq_mono (subset.refl _) ht),
    rw set.seq_seq,
    exact seq_mem_seq_sets (seq_mem_seq_sets (image_mem_map hs) hu) hv }
end

lemma prod_map_seq_comm (f : filter α) (g : filter β) :
  (map prod.mk f).seq g = seq (map (λb a, (a, b)) g) f :=
begin
  refine le_antisymm (le_seq $ assume s hs t ht, _) (le_seq $ assume s hs t ht, _),
  { rcases mem_map_sets_iff.1 hs with ⟨u, hu, hs⟩,
    refine mem_sets_of_superset _ (set.seq_mono hs (subset.refl _)),
    rw ← set.prod_image_seq_comm,
    exact seq_mem_seq_sets (image_mem_map ht) hu },
  { rcases mem_map_sets_iff.1 hs with ⟨u, hu, hs⟩,
    refine mem_sets_of_superset _ (set.seq_mono hs (subset.refl _)),
    rw set.prod_image_seq_comm,
    exact seq_mem_seq_sets (image_mem_map ht) hu }
end

instance : is_lawful_functor (filter : Type u → Type u) :=
{ id_map   := assume α f, map_id,
  comp_map := assume α β γ f g a, map_map.symm }

instance : is_lawful_applicative (filter : Type u → Type u) :=
{ pure_seq_eq_map := assume α β, pure_seq_eq_map,
  map_pure        := assume α β, map_pure,
  seq_pure        := assume α β, seq_pure,
  seq_assoc       := assume α β γ, seq_assoc }

instance : is_comm_applicative (filter : Type u → Type u) :=
⟨assume α β f g, prod_map_seq_comm f g⟩

lemma {l} seq_eq_filter_seq {α β : Type l} (f : filter (α → β)) (g : filter α) :
  f <*> g = seq f g := rfl

end applicative

/- bind equations -/
section bind
@[simp] lemma mem_bind_sets {s : set β} {f : filter α} {m : α → filter β} :
  s ∈ bind f m ↔ ∃t ∈ f, ∀x ∈ t, s ∈ m x :=
calc s ∈ bind f m ↔ {a | s ∈ m a} ∈ f : by simp only [bind, mem_map, iff_self, mem_join_sets, mem_set_of_eq]
                     ... ↔ (∃t ∈ f, t ⊆ {a | s ∈ m a}) : exists_sets_subset_iff.symm
                     ... ↔ (∃t ∈ f, ∀x ∈ t, s ∈ m x) : iff.rfl

lemma bind_mono {f : filter α} {g h : α → filter β} (h₁ : {a | g a ≤ h a} ∈ f) :
  bind f g ≤ bind f h :=
assume x h₂, show (_ ∈ f), by filter_upwards [h₁, h₂] assume s gh' h', gh' h'

lemma bind_sup {f g : filter α} {h : α → filter β} :
  bind (f ⊔ g) h = bind f h ⊔ bind g h :=
by simp only [bind, sup_join, map_sup, eq_self_iff_true]

lemma bind_mono2 {f g : filter α} {h : α → filter β} (h₁ : f ≤ g) :
  bind f h ≤ bind g h :=
assume s h', h₁ h'

lemma principal_bind {s : set α} {f : α → filter β} :
  (bind (principal s) f) = (⨆x ∈ s, f x) :=
show join (map f (principal s)) = (⨆x ∈ s, f x),
  by simp only [Sup_image, join_principal_eq_Sup, map_principal, eq_self_iff_true]

end bind

section list_traverse
/- This is a separate section in order to open `list`, but mostly because of universe
   equality requirements in `traverse` -/

open list

lemma sequence_mono :
  ∀(as bs : list (filter α)), forall₂ (≤) as bs → sequence as ≤ sequence bs
| []      []      forall₂.nil         := le_refl _
| (a::as) (b::bs) (forall₂.cons h hs) := seq_mono (map_mono h) (sequence_mono as bs hs)

variables {α' β' γ' : Type u} {f : β' → filter α'} {s : γ' → set α'}

lemma mem_traverse_sets :
  ∀(fs : list β') (us : list γ'),
    forall₂ (λb c, s c ∈ f b) fs us → traverse s us ∈ traverse f fs
| []      []      forall₂.nil         := mem_pure_sets.2 $ mem_singleton _
| (f::fs) (u::us) (forall₂.cons h hs) := seq_mem_seq_sets (image_mem_map h) (mem_traverse_sets fs us hs)

lemma mem_traverse_sets_iff (fs : list β') (t : set (list α')) :
  t ∈ traverse f fs ↔
    (∃us:list (set α'), forall₂ (λb (s : set α'), s ∈ f b) fs us ∧ sequence us ⊆ t) :=
begin
  split,
  { induction fs generalizing t,
    case nil { simp only [sequence, mem_pure_sets, imp_self, forall₂_nil_left_iff,
      exists_eq_left, set.pure_def, singleton_subset_iff, traverse_nil] },
    case cons : b fs ih t {
      assume ht,
      rcases mem_seq_sets_iff.1 ht with ⟨u, hu, v, hv, ht⟩,
      rcases mem_map_sets_iff.1 hu with ⟨w, hw, hwu⟩,
      rcases ih v hv with ⟨us, hus, hu⟩,
      exact ⟨w :: us, forall₂.cons hw hus, subset.trans (set.seq_mono hwu hu) ht⟩ } },
  { rintros ⟨us, hus, hs⟩,
    exact mem_sets_of_superset (mem_traverse_sets _ _ hus) hs }
end

end list_traverse

/-! ### Limits -/

/-- `tendsto` is the generic "limit of a function" predicate.
  `tendsto f l₁ l₂` asserts that for every `l₂` neighborhood `a`,
  the `f`-preimage of `a` is an `l₁` neighborhood. -/
def tendsto (f : α → β) (l₁ : filter α) (l₂ : filter β) := l₁.map f ≤ l₂

lemma tendsto_def {f : α → β} {l₁ : filter α} {l₂ : filter β} :
  tendsto f l₁ l₂ ↔ ∀ s ∈ l₂, f ⁻¹' s ∈ l₁ := iff.rfl

lemma tendsto.eventually {f : α → β} {l₁ : filter α} {l₂ : filter β} {p : β → Prop}
  (hf : tendsto f l₁ l₂) (h : ∀ᶠ y in l₂, p y) :
  ∀ᶠ x in l₁, p (f x) :=
hf h

lemma tendsto_iff_comap {f : α → β} {l₁ : filter α} {l₂ : filter β} :
  tendsto f l₁ l₂ ↔ l₁ ≤ l₂.comap f :=
map_le_iff_le_comap

lemma tendsto_congr' {f₁ f₂ : α → β} {l₁ : filter α} {l₂ : filter β}
  (hl : {x | f₁ x = f₂ x} ∈ l₁) :  tendsto f₁ l₁ l₂ ↔ tendsto f₂ l₁ l₂ :=
by rw [tendsto, tendsto, map_cong hl]

lemma tendsto.congr' {f₁ f₂ : α → β} {l₁ : filter α} {l₂ : filter β}
  (hl : {x | f₁ x = f₂ x} ∈ l₁) (h : tendsto f₁ l₁ l₂) : tendsto f₂ l₁ l₂ :=
(tendsto_congr' hl).1 h

theorem tendsto_congr {f₁ f₂ : α → β} {l₁ : filter α} {l₂ : filter β}
  (h : ∀ x, f₁ x = f₂ x) : tendsto f₁ l₁ l₂ ↔ tendsto f₂ l₁ l₂ :=
tendsto_congr' (univ_mem_sets' h)

theorem tendsto.congr {f₁ f₂ : α → β} {l₁ : filter α} {l₂ : filter β}
  (h : ∀ x, f₁ x = f₂ x) : tendsto f₁ l₁ l₂ → tendsto f₂ l₁ l₂ :=
(tendsto_congr h).1

lemma tendsto_id' {x y : filter α} : x ≤ y → tendsto id x y :=
by simp only [tendsto, map_id, forall_true_iff] {contextual := tt}

lemma tendsto_id {x : filter α} : tendsto id x x := tendsto_id' $ le_refl x

lemma tendsto.comp {f : α → β} {g : β → γ} {x : filter α} {y : filter β} {z : filter γ}
  (hg : tendsto g y z) (hf : tendsto f x y) : tendsto (g ∘ f) x z :=
calc map (g ∘ f) x = map g (map f x) : by rw [map_map]
  ... ≤ map g y : map_mono hf
  ... ≤ z : hg

lemma tendsto_le_left {f : α → β} {x y : filter α} {z : filter β}
  (h : y ≤ x) : tendsto f x z → tendsto f y z :=
le_trans (map_mono h)

lemma tendsto_le_right {f : α → β} {x : filter α} {y z : filter β}
  (h₁ : y ≤ z) (h₂ : tendsto f x y) : tendsto f x z :=
le_trans h₂ h₁

lemma tendsto.ne_bot {f : α → β} {x : filter α} {y : filter β} (h : tendsto f x y) (hx : x ≠ ⊥) :
  y ≠ ⊥ :=
ne_bot_of_le_ne_bot (map_ne_bot hx) h

lemma tendsto_map {f : α → β} {x : filter α} : tendsto f x (map f x) := le_refl (map f x)

lemma tendsto_map' {f : β → γ} {g : α → β} {x : filter α} {y : filter γ}
  (h : tendsto (f ∘ g) x y) : tendsto f (map g x) y :=
by rwa [tendsto, map_map]

lemma tendsto_map'_iff {f : β → γ} {g : α → β} {x : filter α} {y : filter γ} :
  tendsto f (map g x) y ↔ tendsto (f ∘ g) x y :=
by rw [tendsto, map_map]; refl

lemma tendsto_comap {f : α → β} {x : filter β} : tendsto f (comap f x) x :=
map_comap_le

lemma tendsto_comap_iff {f : α → β} {g : β → γ} {a : filter α} {c : filter γ} :
  tendsto f a (c.comap g) ↔ tendsto (g ∘ f) a c :=
⟨assume h, tendsto_comap.comp h, assume h, map_le_iff_le_comap.mp $ by rwa [map_map]⟩

lemma tendsto_comap'_iff {m : α → β} {f : filter α} {g : filter β} {i : γ → α}
  (h : range i ∈ f) : tendsto (m ∘ i) (comap i f) g ↔ tendsto m f g :=
by rw [tendsto, ← map_compose]; simp only [(∘), map_comap h, tendsto]

lemma comap_eq_of_inverse {f : filter α} {g : filter β} {φ : α → β} (ψ : β → α)
  (eq : ψ ∘ φ = id) (hφ : tendsto φ f g) (hψ : tendsto ψ g f) : comap φ g = f :=
begin
  refine le_antisymm (le_trans (comap_mono $ map_le_iff_le_comap.1 hψ) _) (map_le_iff_le_comap.1 hφ),
  rw [comap_comap_comp, eq, comap_id],
  exact le_refl _
end

lemma map_eq_of_inverse {f : filter α} {g : filter β} {φ : α → β} (ψ : β → α)
  (eq : φ ∘ ψ = id) (hφ : tendsto φ f g) (hψ : tendsto ψ g f) : map φ f = g :=
begin
  refine le_antisymm hφ (le_trans _ (map_mono hψ)),
  rw [map_map, eq, map_id],
  exact le_refl _
end

lemma tendsto_inf {f : α → β} {x : filter α} {y₁ y₂ : filter β} :
  tendsto f x (y₁ ⊓ y₂) ↔ tendsto f x y₁ ∧ tendsto f x y₂ :=
by simp only [tendsto, le_inf_iff, iff_self]

lemma tendsto_inf_left {f : α → β} {x₁ x₂ : filter α} {y : filter β}
  (h : tendsto f x₁ y) : tendsto f (x₁ ⊓ x₂) y  :=
le_trans (map_mono inf_le_left) h

lemma tendsto_inf_right {f : α → β} {x₁ x₂ : filter α} {y : filter β}
  (h : tendsto f x₂ y) : tendsto f (x₁ ⊓ x₂) y  :=
le_trans (map_mono inf_le_right) h

lemma tendsto.inf {f : α → β} {x₁ x₂ : filter α} {y₁ y₂ : filter β}
  (h₁ : tendsto f x₁ y₁) (h₂ : tendsto f x₂ y₂) : tendsto f (x₁ ⊓ x₂) (y₁ ⊓ y₂) :=
tendsto_inf.2 ⟨tendsto_inf_left h₁, tendsto_inf_right h₂⟩

lemma tendsto_infi {f : α → β} {x : filter α} {y : ι → filter β} :
  tendsto f x (⨅i, y i) ↔ ∀i, tendsto f x (y i) :=
by simp only [tendsto, iff_self, le_infi_iff]

lemma tendsto_infi' {f : α → β} {x : ι → filter α} {y : filter β} (i : ι) :
  tendsto f (x i) y → tendsto f (⨅i, x i) y :=
tendsto_le_left (infi_le _ _)

lemma tendsto_principal {f : α → β} {l : filter α} {s : set β} :
  tendsto f l (principal s) ↔ ∀ᶠ a in l, f a ∈ s :=
by simp only [tendsto, le_principal_iff, mem_map, iff_self, filter.eventually]

lemma tendsto_principal_principal {f : α → β} {s : set α} {t : set β} :
  tendsto f (principal s) (principal t) ↔ ∀a∈s, f a ∈ t :=
by simp only [tendsto, image_subset_iff, le_principal_iff, map_principal, mem_principal_sets]; refl

lemma tendsto_pure {f : α → β} {a : filter α} {b : β} :
  tendsto f a (pure b) ↔ {x | f x = b} ∈ a :=
by simp only [tendsto, le_pure_iff, mem_map, mem_singleton_iff]

lemma tendsto_pure_pure (f : α → β) (a : α) :
  tendsto f (pure a) (pure (f a)) :=
tendsto_pure.2 rfl

lemma tendsto_const_pure {a : filter α} {b : β} : tendsto (λx, b) a (pure b) :=
tendsto_pure.2 $ univ_mem_sets' $ λ _, rfl

lemma tendsto_if {l₁ : filter α} {l₂ : filter β}
    {f g : α → β} {p : α → Prop} [decidable_pred p]
    (h₀ : tendsto f (l₁ ⊓ principal p) l₂)
    (h₁ : tendsto g (l₁ ⊓ principal { x | ¬ p x }) l₂) :
  tendsto (λ x, if p x then f x else g x) l₁ l₂ :=
begin
  revert h₀ h₁, simp only [tendsto_def, mem_inf_principal],
  intros h₀ h₁ s hs,
  apply mem_sets_of_superset (inter_mem_sets (h₀ s hs) (h₁ s hs)),
  rintros x ⟨hp₀, hp₁⟩, simp only [mem_preimage],
  by_cases h : p x,
  { rw if_pos h, exact hp₀ h },
  rw if_neg h, exact hp₁ h
end

/-! ### Products of filters -/

section prod
variables {s : set α} {t : set β} {f : filter α} {g : filter β}
/- The product filter cannot be defined using the monad structure on filters. For example:

  F := do {x ← seq, y ← top, return (x, y)}
  hence:
    s ∈ F  ↔  ∃n, [n..∞] × univ ⊆ s

  G := do {y ← top, x ← seq, return (x, y)}
  hence:
    s ∈ G  ↔  ∀i:ℕ, ∃n, [n..∞] × {i} ⊆ s

  Now ⋃i, [i..∞] × {i}  is in G but not in F.

  As product filter we want to have F as result.
-/

/-- Product of filters. This is the filter generated by cartesian products
  of elements of the component filters. -/
protected def prod (f : filter α) (g : filter β) : filter (α × β) :=
f.comap prod.fst ⊓ g.comap prod.snd

localized "infix ` ×ᶠ `:60 := filter.prod" in filter

lemma prod_mem_prod {s : set α} {t : set β} {f : filter α} {g : filter β}
  (hs : s ∈ f) (ht : t ∈ g) : set.prod s t ∈ f ×ᶠ g :=
inter_mem_inf_sets (preimage_mem_comap hs) (preimage_mem_comap ht)

lemma mem_prod_iff {s : set (α×β)} {f : filter α} {g : filter β} :
  s ∈ f ×ᶠ g ↔ (∃ t₁ ∈ f, ∃ t₂ ∈ g, set.prod t₁ t₂ ⊆ s) :=
begin
  simp only [filter.prod],
  split,
  exact assume ⟨t₁, ⟨s₁, hs₁, hts₁⟩, t₂, ⟨s₂, hs₂, hts₂⟩, h⟩,
    ⟨s₁, hs₁, s₂, hs₂, subset.trans (inter_subset_inter hts₁ hts₂) h⟩,
  exact assume ⟨t₁, ht₁, t₂, ht₂, h⟩,
    ⟨prod.fst ⁻¹' t₁, ⟨t₁, ht₁, subset.refl _⟩, prod.snd ⁻¹' t₂, ⟨t₂, ht₂, subset.refl _⟩, h⟩
end

lemma tendsto_fst {f : filter α} {g : filter β} : tendsto prod.fst (f ×ᶠ g) f :=
tendsto_inf_left tendsto_comap

lemma tendsto_snd {f : filter α} {g : filter β} : tendsto prod.snd (f ×ᶠ g) g :=
tendsto_inf_right tendsto_comap

lemma tendsto.prod_mk {f : filter α} {g : filter β} {h : filter γ} {m₁ : α → β} {m₂ : α → γ}
  (h₁ : tendsto m₁ f g) (h₂ : tendsto m₂ f h) : tendsto (λx, (m₁ x, m₂ x)) f (g ×ᶠ h) :=
tendsto_inf.2 ⟨tendsto_comap_iff.2 h₁, tendsto_comap_iff.2 h₂⟩

lemma eventually.prod_inl {la : filter α} {p : α → Prop} (h : ∀ᶠ x in la, p x) (lb : filter β) :
  ∀ᶠ x in la ×ᶠ lb, p (x : α × β).1 :=
tendsto_fst.eventually h

lemma eventually.prod_inr {lb : filter β} {p : β → Prop} (h : ∀ᶠ x in lb, p x) (la : filter α) :
  ∀ᶠ x in la ×ᶠ lb, p (x : α × β).2 :=
tendsto_snd.eventually h

lemma eventually.prod_mk {la : filter α} {pa : α → Prop} (ha : ∀ᶠ x in la, pa x)
  {lb : filter β} {pb : β → Prop} (hb : ∀ᶠ y in lb, pb y) :
  ∀ᶠ p in la ×ᶠ lb, pa (p : α × β).1 ∧ pb p.2 :=
(ha.prod_inl lb).and (hb.prod_inr la)

lemma prod_infi_left {f : ι → filter α} {g : filter β} (i : ι) :
  (⨅i, f i) ×ᶠ g = (⨅i, (f i) ×ᶠ g) :=
by rw [filter.prod, comap_infi, infi_inf i]; simp only [filter.prod, eq_self_iff_true]

lemma prod_infi_right {f : filter α} {g : ι → filter β} (i : ι) :
  f ×ᶠ (⨅i, g i) = (⨅i, f ×ᶠ (g i)) :=
by rw [filter.prod, comap_infi, inf_infi i]; simp only [filter.prod, eq_self_iff_true]

lemma prod_mono {f₁ f₂ : filter α} {g₁ g₂ : filter β} (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) :
  f₁ ×ᶠ g₁ ≤ f₂ ×ᶠ g₂ :=
inf_le_inf (comap_mono hf) (comap_mono hg)

lemma prod_comap_comap_eq {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
  {f₁ : filter α₁} {f₂ : filter α₂} {m₁ : β₁ → α₁} {m₂ : β₂ → α₂} :
  (comap m₁ f₁) ×ᶠ (comap m₂ f₂) = comap (λp:β₁×β₂, (m₁ p.1, m₂ p.2)) (f₁ ×ᶠ f₂) :=
by simp only [filter.prod, comap_comap_comp, eq_self_iff_true, comap_inf]

lemma prod_comm' : f ×ᶠ g = comap (prod.swap) (g ×ᶠ f) :=
by simp only [filter.prod, comap_comap_comp, (∘), inf_comm, prod.fst_swap,
  eq_self_iff_true, prod.snd_swap, comap_inf]

lemma prod_comm : f ×ᶠ g = map (λp:β×α, (p.2, p.1)) (g ×ᶠ f) :=
by rw [prod_comm', ← map_swap_eq_comap_swap]; refl

lemma prod_map_map_eq {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
  {f₁ : filter α₁} {f₂ : filter α₂} {m₁ : α₁ → β₁} {m₂ : α₂ → β₂} :
  (map m₁ f₁) ×ᶠ (map m₂ f₂) = map (λp:α₁×α₂, (m₁ p.1, m₂ p.2)) (f₁ ×ᶠ f₂) :=
le_antisymm
  (assume s hs,
    let ⟨s₁, hs₁, s₂, hs₂, h⟩ := mem_prod_iff.mp hs in
    filter.sets_of_superset _ (prod_mem_prod (image_mem_map hs₁) (image_mem_map hs₂)) $
      calc set.prod (m₁ '' s₁) (m₂ '' s₂) = (λp:α₁×α₂, (m₁ p.1, m₂ p.2)) '' set.prod s₁ s₂ :
          set.prod_image_image_eq
        ... ⊆ _ : by rwa [image_subset_iff])
  ((tendsto.comp (le_refl _) tendsto_fst).prod_mk (tendsto.comp (le_refl _) tendsto_snd))

lemma map_prod (m : α × β → γ) (f : filter α) (g : filter β) :
  map m (f.prod g) = (f.map (λa b, m (a, b))).seq g :=
begin
  simp [filter.ext_iff, mem_prod_iff, mem_map_seq_iff],
  assume s,
  split,
  exact assume ⟨t, ht, s, hs, h⟩, ⟨s, hs, t, ht, assume x hx y hy, @h ⟨x, y⟩ ⟨hx, hy⟩⟩,
  exact assume ⟨s, hs, t, ht, h⟩, ⟨t, ht, s, hs, assume ⟨x, y⟩ ⟨hx, hy⟩, h x hx y hy⟩
end

lemma prod_eq {f : filter α} {g : filter β} : f.prod g = (f.map prod.mk).seq g  :=
have h : _ := map_prod id f g, by rwa [map_id] at h

lemma prod_inf_prod {f₁ f₂ : filter α} {g₁ g₂ : filter β} :
  (f₁ ×ᶠ g₁) ⊓ (f₂ ×ᶠ g₂) = (f₁ ⊓ f₂) ×ᶠ (g₁ ⊓ g₂) :=
by simp only [filter.prod, comap_inf, inf_comm, inf_assoc, inf_left_comm]

@[simp] lemma prod_bot {f : filter α} : f ×ᶠ (⊥ : filter β) = ⊥ := by simp [filter.prod]
@[simp] lemma bot_prod {g : filter β} : (⊥ : filter α) ×ᶠ g = ⊥ := by simp [filter.prod]

@[simp] lemma prod_principal_principal {s : set α} {t : set β} :
  (principal s) ×ᶠ (principal t) = principal (set.prod s t) :=
by simp only [filter.prod, comap_principal, principal_eq_iff_eq, comap_principal, inf_principal]; refl

@[simp] lemma prod_pure_pure {a : α} {b : β} : (pure a) ×ᶠ (pure b) = pure (a, b) :=
by simp [pure_eq_principal]

lemma prod_eq_bot {f : filter α} {g : filter β} : f ×ᶠ g = ⊥ ↔ (f = ⊥ ∨ g = ⊥) :=
begin
  split,
  { assume h,
    rcases mem_prod_iff.1 (empty_in_sets_eq_bot.2 h) with ⟨s, hs, t, ht, hst⟩,
    rw [subset_empty_iff, set.prod_eq_empty_iff] at hst,
    cases hst with s_eq t_eq,
    { left, exact empty_in_sets_eq_bot.1 (s_eq ▸ hs) },
    { right, exact empty_in_sets_eq_bot.1 (t_eq ▸ ht) } },
  { rintros (rfl | rfl),
    exact bot_prod,
    exact prod_bot }
end

lemma prod_ne_bot {f : filter α} {g : filter β} : f ×ᶠ g ≠ ⊥ ↔ (f ≠ ⊥ ∧ g ≠ ⊥) :=
by rw [(≠), prod_eq_bot, not_or_distrib]

lemma tendsto_prod_iff {f : α × β → γ} {x : filter α} {y : filter β} {z : filter γ} :
  filter.tendsto f (x ×ᶠ y) z ↔
  ∀ W ∈ z, ∃ U ∈ x,  ∃ V ∈ y, ∀ x y, x ∈ U → y ∈ V → f (x, y) ∈ W :=
by simp only [tendsto_def, mem_prod_iff, prod_sub_preimage_iff, exists_prop, iff_self]

end prod

/-! ### at_top and at_bot filters on preorded sets, monoids and groups. -/

/-- `at_top` is the filter representing the limit `→ ∞` on an ordered set.
  It is generated by the collection of up-sets `{b | a ≤ b}`.
  (The preorder need not have a top element for this to be well defined,
  and indeed is trivial when a top element exists.) -/
def at_top [preorder α] : filter α := ⨅ a, principal {b | a ≤ b}

/-- `at_bot` is the filter representing the limit `→ -∞` on an ordered set.
  It is generated by the collection of down-sets `{b | b ≤ a}`.
  (The preorder need not have a bottom element for this to be well defined,
  and indeed is trivial when a bottom element exists.) -/
def at_bot [preorder α] : filter α := ⨅ a, principal {b | b ≤ a}

lemma mem_at_top [preorder α] (a : α) : {b : α | a ≤ b} ∈ @at_top α _ :=
mem_infi_sets a $ subset.refl _

@[simp] lemma at_top_ne_bot [nonempty α] [semilattice_sup α] : (at_top : filter α) ≠ ⊥ :=
infi_ne_bot_of_directed (by apply_instance)
  (assume a b, ⟨a ⊔ b, by simp only [ge, le_principal_iff, forall_const, set_of_subset_set_of,
    mem_principal_sets, and_self, sup_le_iff, forall_true_iff] {contextual := tt}⟩)
  (assume a, principal_ne_bot_iff.2 nonempty_Ici)

@[simp, nolint ge_or_gt]
lemma mem_at_top_sets [nonempty α] [semilattice_sup α] {s : set α} :
  s ∈ (at_top : filter α) ↔ ∃a:α, ∀b≥a, b ∈ s :=
let ⟨a⟩ := ‹nonempty α› in
iff.intro
  (assume h, infi_sets_induct h ⟨a, by simp only [forall_const, mem_univ, forall_true_iff]⟩
    (assume a s₁ s₂ ha ⟨b, hb⟩, ⟨a ⊔ b,
      assume c hc, ⟨ha $ le_trans le_sup_left hc, hb _ $ le_trans le_sup_right hc⟩⟩)
    (assume s₁ s₂ h ⟨a, ha⟩, ⟨a, assume b hb, h $ ha _ hb⟩))
  (assume ⟨a, h⟩, mem_infi_sets a $ assume x, h x)

@[nolint ge_or_gt]
lemma eventually_at_top {α} [semilattice_sup α] [nonempty α] {p : α → Prop} :
  (∀ᶠ x in at_top, p x) ↔ (∃ a, ∀ b ≥ a, p b) :=
by simp only [filter.eventually, filter.mem_at_top_sets, mem_set_of_eq]

@[nolint ge_or_gt]
lemma eventually.exists_forall_of_at_top {α} [semilattice_sup α] [nonempty α] {p : α → Prop}
  (h : ∀ᶠ x in at_top, p x) : ∃ a, ∀ b ≥ a, p b :=
eventually_at_top.mp h

@[nolint ge_or_gt]
lemma frequently_at_top {α} [semilattice_sup α] [nonempty α] {p : α → Prop} :
  (∃ᶠ x in at_top, p x) ↔ (∀ a, ∃ b ≥ a, p b) :=
by simp only [filter.frequently, eventually_at_top, not_exists, not_forall, not_not]

@[nolint ge_or_gt]
lemma frequently_at_top' {α} [semilattice_sup α] [nonempty α] [no_top_order α] {p : α → Prop} :
  (∃ᶠ x in at_top, p x) ↔ (∀ a, ∃ b > a, p b) :=
begin
  rw frequently_at_top,
  split ; intros h a,
  { cases no_top a with a' ha',
    rcases h a' with ⟨b, hb, hb'⟩,
    exact ⟨b, lt_of_lt_of_le ha' hb, hb'⟩ },
  { rcases h a with ⟨b, hb, hb'⟩,
    exact ⟨b, le_of_lt hb, hb'⟩ },
end

@[nolint ge_or_gt]
lemma frequently.forall_exists_of_at_top {α} [semilattice_sup α] [nonempty α] {p : α → Prop}
  (h : ∃ᶠ x in at_top, p x) : ∀ a, ∃ b ≥ a, p b :=
frequently_at_top.mp h

lemma map_at_top_eq [nonempty α] [semilattice_sup α] {f : α → β} :
  at_top.map f = (⨅a, principal $ f '' {a' | a ≤ a'}) :=
calc map f (⨅a, principal {a' | a ≤ a'}) = (⨅a, map f $ principal {a' | a ≤ a'}) :
    map_infi_eq (assume a b, ⟨a ⊔ b, by simp only [ge, le_principal_iff, forall_const, set_of_subset_set_of,
      mem_principal_sets, and_self, sup_le_iff, forall_true_iff] {contextual := tt}⟩)
      (by apply_instance)
  ... = (⨅a, principal $ f '' {a' | a ≤ a'}) : by simp only [map_principal, eq_self_iff_true]

lemma tendsto_at_top [preorder β] (m : α → β) (f : filter α) :
  tendsto m f at_top ↔ (∀b, {a | b ≤ m a} ∈ f) :=
by simp only [at_top, tendsto_infi, tendsto_principal]; refl

lemma tendsto_at_top_mono' [preorder β] (l : filter α) ⦃f₁ f₂ : α → β⦄ (h : {x | f₁ x ≤ f₂ x} ∈ l) :
  tendsto f₁ l at_top → tendsto f₂ l at_top :=
assume h₁, (tendsto_at_top _ _).2 $ λ b, mp_sets ((tendsto_at_top _ _).1 h₁ b)
  (monotone_mem_sets (λ a ha ha₁, le_trans ha₁ ha) h)

lemma tendsto_at_top_mono [preorder β] (l : filter α) :
  monotone (λ f : α → β, tendsto f l at_top) :=
λ f₁ f₂ h, tendsto_at_top_mono' l $ univ_mem_sets' h

@[nolint ge_or_gt] -- see Note [nolint_ge]
lemma map_at_top_inf_ne_bot_iff [semilattice_sup α] [nonempty α] {F : filter β} {u : α → β} :
  (map u at_top) ⊓ F ≠ ⊥ ↔ ∀ U ∈ F, ∀ N, ∃ n ≥ N, u n ∈ U :=
by simp_rw [inf_ne_bot_iff_frequently_right, frequently_map, frequently_at_top] ; trivial

section ordered_add_monoid

variables [ordered_cancel_add_comm_monoid β] (l : filter α) {f g : α → β}

lemma tendsto_at_top_add_nonneg_left' (hf : {x | 0 ≤ f x} ∈ l) (hg : tendsto g l at_top) :
  tendsto (λ x, f x + g x) l at_top :=
tendsto_at_top_mono' l (monotone_mem_sets (λ x, le_add_of_nonneg_left) hf) hg

lemma tendsto_at_top_add_nonneg_left (hf : ∀ x, 0 ≤ f x) (hg : tendsto g l at_top) :
  tendsto (λ x, f x + g x) l at_top :=
tendsto_at_top_add_nonneg_left' l (univ_mem_sets' hf) hg

lemma tendsto_at_top_add_nonneg_right' (hf : tendsto f l at_top) (hg : {x | 0 ≤ g x} ∈ l) :
  tendsto (λ x, f x + g x) l at_top :=
tendsto_at_top_mono' l (monotone_mem_sets (λ x, le_add_of_nonneg_right) hg) hf

lemma tendsto_at_top_add_nonneg_right (hf : tendsto f l at_top) (hg : ∀ x, 0 ≤ g x) :
  tendsto (λ x, f x + g x) l at_top :=
tendsto_at_top_add_nonneg_right' l hf (univ_mem_sets' hg)

lemma tendsto_at_top_of_add_const_left (C : β) (hf : tendsto (λ x, C + f x) l at_top) :
  tendsto f l at_top :=
(tendsto_at_top _ l).2 $ assume b,
  monotone_mem_sets (λ x, le_of_add_le_add_left) ((tendsto_at_top _ _).1 hf (C + b))

lemma tendsto_at_top_of_add_const_right (C : β) (hf : tendsto (λ x, f x + C) l at_top) :
  tendsto f l at_top :=
(tendsto_at_top _ l).2 $ assume b,
  monotone_mem_sets (λ x, le_of_add_le_add_right) ((tendsto_at_top _ _).1 hf (b + C))

lemma tendsto_at_top_of_add_bdd_above_left' (C) (hC : {x | f x ≤ C} ∈ l)
  (h : tendsto (λ x, f x + g x) l at_top) :
  tendsto g l at_top :=
tendsto_at_top_of_add_const_left l C
  (tendsto_at_top_mono' l (monotone_mem_sets (λ x (hx : f x ≤ C), add_le_add_right hx (g x)) hC) h)

lemma tendsto_at_top_of_add_bdd_above_left (C) (hC : ∀ x, f x ≤ C) :
  tendsto (λ x, f x + g x) l at_top → tendsto g l at_top :=
tendsto_at_top_of_add_bdd_above_left' l C (univ_mem_sets' hC)

lemma tendsto_at_top_of_add_bdd_above_right' (C) (hC : {x | g x ≤ C} ∈ l)
  (h : tendsto (λ x, f x + g x) l at_top) :
  tendsto f l at_top :=
tendsto_at_top_of_add_const_right l C
  (tendsto_at_top_mono' l (monotone_mem_sets (λ x (hx : g x ≤ C), add_le_add_left hx (f x)) hC) h)

lemma tendsto_at_top_of_add_bdd_above_right (C) (hC : ∀ x, g x ≤ C) :
  tendsto (λ x, f x + g x) l at_top → tendsto f l at_top :=
tendsto_at_top_of_add_bdd_above_right' l C (univ_mem_sets' hC)

end ordered_add_monoid

section ordered_group

variables [ordered_add_comm_group β] (l : filter α) {f g : α → β}

lemma tendsto_at_top_add_left_of_le' (C : β) (hf : {x | C ≤ f x} ∈ l) (hg : tendsto g l at_top) :
  tendsto (λ x, f x + g x) l at_top :=
@tendsto_at_top_of_add_bdd_above_left' _ _ _ l (λ x, -(f x)) (λ x, f x + g x) (-C)
  (by simp [hf]) (by simp [hg])

lemma tendsto_at_top_add_left_of_le (C : β) (hf : ∀ x, C ≤ f x) (hg : tendsto g l at_top) :
  tendsto (λ x, f x + g x) l at_top :=
tendsto_at_top_add_left_of_le' l C (univ_mem_sets' hf) hg

lemma tendsto_at_top_add_right_of_le' (C : β) (hf : tendsto f l at_top) (hg : {x | C ≤ g x} ∈ l) :
  tendsto (λ x, f x + g x) l at_top :=
@tendsto_at_top_of_add_bdd_above_right' _ _ _ l (λ x, f x + g x) (λ x, -(g x)) (-C)
  (by simp [hg]) (by simp [hf])

lemma tendsto_at_top_add_right_of_le (C : β) (hf : tendsto f l at_top) (hg : ∀ x, C ≤ g x) :
  tendsto (λ x, f x + g x) l at_top :=
tendsto_at_top_add_right_of_le' l C hf (univ_mem_sets' hg)

lemma tendsto_at_top_add_const_left (C : β) (hf : tendsto f l at_top) :
  tendsto (λ x, C + f x) l at_top :=
tendsto_at_top_add_left_of_le' l C (univ_mem_sets' $ λ _, le_refl C) hf

lemma tendsto_at_top_add_const_right (C : β) (hf : tendsto f l at_top) :
  tendsto (λ x, f x + C) l at_top :=
tendsto_at_top_add_right_of_le' l C hf (univ_mem_sets' $ λ _, le_refl C)

end ordered_group

open_locale filter

@[nolint ge_or_gt]
lemma tendsto_at_top' [nonempty α] [semilattice_sup α] (f : α → β) (l : filter β) :
  tendsto f at_top l ↔ (∀s ∈ l, ∃a, ∀b≥a, f b ∈ s) :=
by simp only [tendsto_def, mem_at_top_sets]; refl

@[nolint ge_or_gt]
theorem tendsto_at_top_principal [nonempty β] [semilattice_sup β] {f : β → α} {s : set α} :
  tendsto f at_top (principal s) ↔ ∃N, ∀n≥N, f n ∈ s :=
by rw [tendsto_iff_comap, comap_principal, le_principal_iff, mem_at_top_sets]; refl

/-- A function `f` grows to infinity independent of an order-preserving embedding `e`. -/
lemma tendsto_at_top_embedding {α β γ : Type*} [preorder β] [preorder γ]
  {f : α → β} {e : β → γ} {l : filter α}
  (hm : ∀b₁ b₂, e b₁ ≤ e b₂ ↔ b₁ ≤ b₂) (hu : ∀c, ∃b, c ≤ e b) :
  tendsto (e ∘ f) l at_top ↔ tendsto f l at_top :=
begin
  rw [tendsto_at_top, tendsto_at_top],
  split,
  { assume hc b,
    filter_upwards [hc (e b)] assume a, (hm b (f a)).1 },
  { assume hb c,
    rcases hu c with ⟨b, hc⟩,
    filter_upwards [hb b] assume a ha, le_trans hc ((hm b (f a)).2 ha) }
end

lemma tendsto_at_top_at_top [nonempty α] [semilattice_sup α] [preorder β] (f : α → β) :
  tendsto f at_top at_top ↔ ∀ b : β, ∃ i : α, ∀ a : α, i ≤ a → b ≤ f a :=
iff.trans tendsto_infi $ forall_congr $ assume b, tendsto_at_top_principal

@[nolint ge_or_gt]
lemma tendsto_at_top_at_bot [nonempty α] [decidable_linear_order α] [preorder β] (f : α → β) :
  tendsto f at_top at_bot ↔ ∀ (b : β), ∃ (i : α), ∀ (a : α), i ≤ a → b ≥ f a :=
@tendsto_at_top_at_top α (order_dual β) _ _ _ f

lemma tendsto_at_top_at_top_of_monotone [nonempty α] [semilattice_sup α] [preorder β]
  {f : α → β} (hf : monotone f) :
  tendsto f at_top at_top ↔ ∀ b : β, ∃ a : α, b ≤ f a :=
(tendsto_at_top_at_top f).trans $ forall_congr $ λ b, exists_congr $ λ a,
  ⟨λ h, h a (le_refl a), λ h a' ha', le_trans h $ hf ha'⟩

alias tendsto_at_top_at_top_of_monotone ← monotone.tendsto_at_top_at_top

lemma tendsto_finset_range : tendsto finset.range at_top at_top :=
finset.range_mono.tendsto_at_top_at_top.2 finset.exists_nat_subset_range

lemma monotone.tendsto_at_top_finset [nonempty β] [semilattice_sup β]
  {f : β → finset α} (h : monotone f) (h' : ∀ x : α, ∃ n, x ∈ f n) :
  tendsto f at_top at_top :=
begin
  classical,
  apply (tendsto_at_top_at_top_of_monotone h).2,
  choose N hN using h',
  assume b,
  have : bdd_above ↑(b.image N) := finset.bdd_above _,
  rcases this with ⟨n, hn⟩,
  refine ⟨n, _⟩,
  assume i ib,
  have : N i ∈ ↑(finset.image N b),
    by { rw finset.mem_coe, exact finset.mem_image_of_mem _ ib },
  exact (h (hn this)) (hN i)
end

lemma tendsto_finset_image_at_top_at_top {i : β → γ} {j : γ → β} (h : ∀x, j (i x) = x) :
  tendsto (finset.image j) at_top at_top :=
have j ∘ i = id, from funext h,
(finset.image_mono j).tendsto_at_top_at_top.2 $ assume s,
  ⟨s.image i, by simp only [finset.image_image, this, finset.image_id, le_refl]⟩

lemma prod_at_top_at_top_eq {β₁ β₂ : Type*} [nonempty β₁] [nonempty β₂] [semilattice_sup β₁]
  [semilattice_sup β₂] : (@at_top β₁ _) ×ᶠ (@at_top β₂ _) = @at_top (β₁ × β₂) _ :=
by inhabit β₁; inhabit β₂;
  simp [at_top, prod_infi_left (default β₁), prod_infi_right (default β₂), infi_prod];
    exact infi_comm

lemma prod_map_at_top_eq {α₁ α₂ β₁ β₂ : Type*} [nonempty β₁] [nonempty β₂]
  [semilattice_sup β₁] [semilattice_sup β₂] (u₁ : β₁ → α₁) (u₂ : β₂ → α₂) :
  (map u₁ at_top) ×ᶠ (map u₂ at_top) = map (prod.map u₁ u₂) at_top :=
by rw [prod_map_map_eq, prod_at_top_at_top_eq, prod.map_def]

/-- A function `f` maps upwards closed sets (at_top sets) to upwards closed sets when it is a
Galois insertion. The Galois "insertion" and "connection" is weakened to only require it to be an
insertion and a connetion above `b'`. -/
lemma map_at_top_eq_of_gc [semilattice_sup α] [semilattice_sup β] {f : α → β} (g : β → α) (b' : β)
  (hf : monotone f) (gc : ∀a, ∀b≥b', f a ≤ b ↔ a ≤ g b) (hgi : ∀b≥b', b ≤ f (g b)) :
  map f at_top = at_top :=
begin
  rw [@map_at_top_eq α _ ⟨g b'⟩],
  refine le_antisymm
    (le_infi $ assume b, infi_le_of_le (g (b ⊔ b')) $ principal_mono.2 $ image_subset_iff.2 _)
    (le_infi $ assume a, infi_le_of_le (f a ⊔ b') $ principal_mono.2 _),
  { assume a ha, exact (le_trans le_sup_left $ le_trans (hgi _ le_sup_right) $ hf ha) },
  { assume b hb,
    have hb' : b' ≤ b := le_trans le_sup_right hb,
    exact ⟨g b, (gc _ _ hb').1 (le_trans le_sup_left hb),
      le_antisymm ((gc _ _ hb').2 (le_refl _)) (hgi _ hb')⟩ }
end

lemma map_add_at_top_eq_nat (k : ℕ) : map (λa, a + k) at_top = at_top :=
map_at_top_eq_of_gc (λa, a - k) k
  (assume a b h, add_le_add_right h k)
  (assume a b h, (nat.le_sub_right_iff_add_le h).symm)
  (assume a h, by rw [nat.sub_add_cancel h])

lemma map_sub_at_top_eq_nat (k : ℕ) : map (λa, a - k) at_top = at_top :=
map_at_top_eq_of_gc (λa, a + k) 0
  (assume a b h, nat.sub_le_sub_right h _)
  (assume a b _, nat.sub_le_right_iff_le_add)
  (assume b _, by rw [nat.add_sub_cancel])

lemma tendsto_add_at_top_nat (k : ℕ) : tendsto (λa, a + k) at_top at_top :=
le_of_eq (map_add_at_top_eq_nat k)

lemma tendsto_sub_at_top_nat (k : ℕ) : tendsto (λa, a - k) at_top at_top :=
le_of_eq (map_sub_at_top_eq_nat k)

lemma tendsto_add_at_top_iff_nat {f : ℕ → α} {l : filter α} (k : ℕ) :
  tendsto (λn, f (n + k)) at_top l ↔ tendsto f at_top l :=
show tendsto (f ∘ (λn, n + k)) at_top l ↔ tendsto f at_top l,
  by rw [← tendsto_map'_iff, map_add_at_top_eq_nat]

lemma map_div_at_top_eq_nat (k : ℕ) (hk : k > 0) : map (λa, a / k) at_top = at_top :=
map_at_top_eq_of_gc (λb, b * k + (k - 1)) 1
  (assume a b h, nat.div_le_div_right h)
  (assume a b _,
    calc a / k ≤ b ↔ a / k < b + 1 : by rw [← nat.succ_eq_add_one, nat.lt_succ_iff]
      ... ↔ a < (b + 1) * k : nat.div_lt_iff_lt_mul _ _ hk
      ... ↔ _ :
      begin
        cases k,
        exact (lt_irrefl _ hk).elim,
        simp [mul_add, add_mul, nat.succ_add, nat.lt_succ_iff]
      end)
  (assume b _,
    calc b = (b * k) / k : by rw [nat.mul_div_cancel b hk]
      ... ≤ (b * k + (k - 1)) / k : nat.div_le_div_right $ nat.le_add_right _ _)

/-! ### The cofinite filter -/

/-- The cofinite filter is the filter of subsets whose complements are finite. -/
def cofinite : filter α :=
{ sets             := {s | finite (- s)},
  univ_sets        := by simp only [compl_univ, finite_empty, mem_set_of_eq],
  sets_of_superset := assume s t (hs : finite (-s)) (st: s ⊆ t),
    finite_subset hs $ compl_subset_compl.2 st,
  inter_sets       := assume s t (hs : finite (-s)) (ht : finite (-t)),
    by simp only [compl_inter, finite_union, ht, hs, mem_set_of_eq] }

@[simp] lemma mem_cofinite {s : set α} : s ∈ (@cofinite α) ↔ finite (-s) := iff.rfl

lemma cofinite_ne_bot [infinite α] : @cofinite α ≠ ⊥ :=
mt empty_in_sets_eq_bot.mpr $ by { simp only [mem_cofinite, compl_empty], exact infinite_univ }

lemma frequently_cofinite_iff_infinite {p : α → Prop} :
  (∃ᶠ x in cofinite, p x) ↔ set.infinite {x | p x} :=
by simp only [filter.frequently, filter.eventually, mem_cofinite, compl_set_of, not_not,
  set.infinite]

lemma set.infinite_iff_frequently_cofinite {α : Type u} {s : set α} :
  set.infinite s ↔ (∃ᶠ x in cofinite, x ∈ s) :=
frequently_cofinite_iff_infinite.symm

/-- For natural numbers the filters `cofinite` and `at_top` coincide. -/
lemma nat.cofinite_eq_at_top : @cofinite ℕ = at_top :=
begin
  ext s,
  simp only [mem_cofinite, mem_at_top_sets],
  split,
  { assume hs,
    use (hs.to_finset.sup id) + 1,
    assume b hb,
    by_contradiction hbs,
    have := hs.to_finset.subset_range_sup_succ (finite.mem_to_finset.2 hbs),
    exact not_lt_of_le hb (finset.mem_range.1 this) },
  { rintros ⟨N, hN⟩,
    apply finite_subset (finite_lt_nat N),
    assume n hn,
    change n < N,
    exact lt_of_not_ge (λ hn', hn $ hN n hn') }
end

/-! ### Ultrafilters -/

section ultrafilter
open zorn

variables {f g : filter α}

/-- An ultrafilter is a minimal (maximal in the set order) proper filter. -/
def is_ultrafilter (f : filter α) := f ≠ ⊥ ∧ ∀g, g ≠ ⊥ → g ≤ f → f ≤ g

lemma ultrafilter_unique (hg : is_ultrafilter g) (hf : f ≠ ⊥) (h : f ≤ g) : f = g :=
le_antisymm h (hg.right _ hf h)

lemma le_of_ultrafilter {g : filter α} (hf : is_ultrafilter f) (h : f ⊓ g ≠ ⊥) :
  f ≤ g :=
le_of_inf_eq $ ultrafilter_unique hf h inf_le_left

/-- Equivalent characterization of ultrafilters:
  A filter f is an ultrafilter if and only if for each set s,
  -s belongs to f if and only if s does not belong to f. -/
lemma ultrafilter_iff_compl_mem_iff_not_mem :
  is_ultrafilter f ↔ (∀ s, -s ∈ f ↔ s ∉ f) :=
⟨assume hf s,
   ⟨assume hns hs,
      hf.1 $ empty_in_sets_eq_bot.mp $ by convert f.inter_sets hs hns; rw [inter_compl_self],
    assume hs,
      have f ≤ principal (-s), from
        le_of_ultrafilter hf $ assume h, hs $ mem_sets_of_eq_bot $
          by simp only [h, eq_self_iff_true, compl_compl],
      by simp only [le_principal_iff] at this; assumption⟩,
 assume hf,
   ⟨mt empty_in_sets_eq_bot.mpr ((hf ∅).mp (by convert f.univ_sets; rw [compl_empty])),
    assume g hg g_le s hs, classical.by_contradiction $ mt (hf s).mpr $
      assume : - s ∈ f,
        have s ∩ -s ∈ g, from inter_mem_sets hs (g_le this),
        by simp only [empty_in_sets_eq_bot, hg, inter_compl_self] at this; contradiction⟩⟩

lemma mem_or_compl_mem_of_ultrafilter (hf : is_ultrafilter f) (s : set α) :
  s ∈ f ∨ - s ∈ f :=
classical.or_iff_not_imp_left.2 (ultrafilter_iff_compl_mem_iff_not_mem.mp hf s).mpr

lemma mem_or_mem_of_ultrafilter {s t : set α} (hf : is_ultrafilter f) (h : s ∪ t ∈ f) :
  s ∈ f ∨ t ∈ f :=
(mem_or_compl_mem_of_ultrafilter hf s).imp_right
  (assume : -s ∈ f, by filter_upwards [this, h] assume x hnx hx, hx.resolve_left hnx)

lemma mem_of_finite_sUnion_ultrafilter {s : set (set α)} (hf : is_ultrafilter f) (hs : finite s)
  : ⋃₀ s ∈ f → ∃t∈s, t ∈ f :=
finite.induction_on hs (by simp only [empty_in_sets_eq_bot, hf.left, mem_empty_eq, sUnion_empty,
  forall_prop_of_false, exists_false, not_false_iff, exists_prop_of_false]) $
λ t s' ht' hs' ih, by simp only [exists_prop, mem_insert_iff, set.sUnion_insert]; exact
assume h, (mem_or_mem_of_ultrafilter hf h).elim
  (assume : t ∈ f, ⟨t, or.inl rfl, this⟩)
  (assume h, let ⟨t, hts', ht⟩ := ih h in ⟨t, or.inr hts', ht⟩)

lemma mem_of_finite_Union_ultrafilter {is : set β} {s : β → set α}
  (hf : is_ultrafilter f) (his : finite is) (h : (⋃i∈is, s i) ∈ f) : ∃i∈is, s i ∈ f :=
have his : finite (image s is), from finite_image s his,
have h : (⋃₀ image s is) ∈ f, from by simp only [sUnion_image, set.sUnion_image]; assumption,
let ⟨t, ⟨i, hi, h_eq⟩, (ht : t ∈ f)⟩ := mem_of_finite_sUnion_ultrafilter hf his h in
⟨i, hi, h_eq.symm ▸ ht⟩

lemma ultrafilter_map {f : filter α} {m : α → β} (h : is_ultrafilter f) : is_ultrafilter (map m f) :=
by rw ultrafilter_iff_compl_mem_iff_not_mem at ⊢ h; exact assume s, h (m ⁻¹' s)

lemma ultrafilter_pure {a : α} : is_ultrafilter (pure a) :=
begin
  rw ultrafilter_iff_compl_mem_iff_not_mem, intro s,
  rw [mem_pure_sets, mem_pure_sets], exact iff.rfl
end

lemma ultrafilter_bind {f : filter α} (hf : is_ultrafilter f) {m : α → filter β}
  (hm : ∀ a, is_ultrafilter (m a)) : is_ultrafilter (f.bind m) :=
begin
  simp only [ultrafilter_iff_compl_mem_iff_not_mem] at ⊢ hf hm, intro s,
  dsimp [bind, join, map, preimage],
  simp only [hm], apply hf
end

/-- The ultrafilter lemma: Any proper filter is contained in an ultrafilter. -/
lemma exists_ultrafilter (h : f ≠ ⊥) : ∃u, u ≤ f ∧ is_ultrafilter u :=
let
  τ                := {f' // f' ≠ ⊥ ∧ f' ≤ f},
  r : τ → τ → Prop := λt₁ t₂, t₂.val ≤ t₁.val,
  ⟨a, ha⟩          := nonempty_of_mem_sets h univ_mem_sets,
  top : τ          := ⟨f, h, le_refl f⟩,
  sup : Π(c:set τ), chain r c → τ :=
    λc hc, ⟨⨅a:{a:τ // a ∈ insert top c}, a.val.val,
      infi_ne_bot_of_directed ⟨a⟩
        (directed_of_chain $ chain_insert hc $ assume ⟨b, _, hb⟩ _ _, or.inl hb)
        (assume ⟨⟨a, ha, _⟩, _⟩, ha),
      infi_le_of_le ⟨top, mem_insert _ _⟩ (le_refl _)⟩
in
have ∀c (hc: chain r c) a (ha : a ∈ c), r a (sup c hc),
  from assume c hc a ha, infi_le_of_le ⟨a, mem_insert_of_mem _ ha⟩ (le_refl _),
have (∃ (u : τ), ∀ (a : τ), r u a → r a u),
  from exists_maximal_of_chains_bounded (assume c hc, ⟨sup c hc, this c hc⟩) (assume f₁ f₂ f₃ h₁ h₂, le_trans h₂ h₁),
let ⟨uτ, hmin⟩ := this in
⟨uτ.val, uτ.property.right, uτ.property.left, assume g hg₁ hg₂,
  hmin ⟨g, hg₁, le_trans hg₂ uτ.property.right⟩ hg₂⟩

/-- Construct an ultrafilter extending a given filter.
  The ultrafilter lemma is the assertion that such a filter exists;
  we use the axiom of choice to pick one. -/
noncomputable def ultrafilter_of (f : filter α) : filter α :=
if h : f = ⊥ then ⊥ else classical.epsilon (λu, u ≤ f ∧ is_ultrafilter u)

lemma ultrafilter_of_spec (h : f ≠ ⊥) : ultrafilter_of f ≤ f ∧ is_ultrafilter (ultrafilter_of f) :=
begin
  have h' := classical.epsilon_spec (exists_ultrafilter h),
  simp only [ultrafilter_of, dif_neg, h, dif_neg, not_false_iff],
  simp only at h',
  assumption
end

lemma ultrafilter_of_le : ultrafilter_of f ≤ f :=
if h : f = ⊥ then by simp only [ultrafilter_of, dif_pos, h, dif_pos, eq_self_iff_true, le_bot_iff]; exact le_refl _
  else (ultrafilter_of_spec h).left

lemma ultrafilter_ultrafilter_of (h : f ≠ ⊥) : is_ultrafilter (ultrafilter_of f) :=
(ultrafilter_of_spec h).right

lemma ultrafilter_of_ultrafilter (h : is_ultrafilter f) : ultrafilter_of f = f :=
ultrafilter_unique h (ultrafilter_ultrafilter_of h.left).left ultrafilter_of_le

/-- A filter equals the intersection of all the ultrafilters which contain it. -/
lemma sup_of_ultrafilters (f : filter α) : f = ⨆ (g) (u : is_ultrafilter g) (H : g ≤ f), g :=
begin
  refine le_antisymm _ (supr_le $ λ g, supr_le $ λ u, supr_le $ λ H, H),
  intros s hs,
  -- If s ∉ f.sets, we'll apply the ultrafilter lemma to the restriction of f to -s.
  by_contradiction hs',
  let j : (-s) → α := subtype.val,
  have j_inv_s : j ⁻¹' s = ∅, by
    erw [←preimage_inter_range, subtype.val_range, inter_compl_self, preimage_empty],
  let f' := comap j f,
  have : f' ≠ ⊥,
  { apply mt empty_in_sets_eq_bot.mpr,
    rintro ⟨t, htf, ht⟩,
    suffices : t ⊆ s, from absurd (f.sets_of_superset htf this) hs',
    rw [subset_empty_iff] at ht,
    have : j '' (j ⁻¹' t) = ∅, by rw [ht, image_empty],
    erw [image_preimage_eq_inter_range, subtype.val_range, ←subset_compl_iff_disjoint,
      set.compl_compl] at this,
    exact this },
  rcases exists_ultrafilter this with ⟨g', g'f', u'⟩,
  simp only [supr_sets_eq, mem_Inter] at hs,
  have := hs (g'.map subtype.val) (ultrafilter_map u') (map_le_iff_le_comap.mpr g'f'),
  rw [←le_principal_iff, map_le_iff_le_comap, comap_principal, j_inv_s, principal_empty,
    le_bot_iff] at this,
  exact absurd this u'.1
end

/-- The `tendsto` relation can be checked on ultrafilters. -/
lemma tendsto_iff_ultrafilter (f : α → β) (l₁ : filter α) (l₂ : filter β) :
  tendsto f l₁ l₂ ↔ ∀ g, is_ultrafilter g → g ≤ l₁ → g.map f ≤ l₂ :=
⟨assume h g u gx, le_trans (map_mono gx) h,
 assume h, by rw [sup_of_ultrafilters l₁]; simpa only [tendsto, map_supr, supr_le_iff]⟩

/-- The ultrafilter monad. The monad structure on ultrafilters is the
  restriction of the one on filters. -/
def ultrafilter (α : Type u) : Type u := {f : filter α // is_ultrafilter f}

/-- Push-forward for ultra-filters. -/
def ultrafilter.map (m : α → β) (u : ultrafilter α) : ultrafilter β :=
⟨u.val.map m, ultrafilter_map u.property⟩

/-- The principal ultra-filter associated to a point `x`. -/
def ultrafilter.pure (x : α) : ultrafilter α := ⟨pure x, ultrafilter_pure⟩

/-- Monadic bind for ultra-filters, coming from the one on filters
defined in terms of map and join.-/
def ultrafilter.bind (u : ultrafilter α) (m : α → ultrafilter β) : ultrafilter β :=
⟨u.val.bind (λ a, (m a).val), ultrafilter_bind u.property (λ a, (m a).property)⟩

instance ultrafilter.has_pure : has_pure ultrafilter := ⟨@ultrafilter.pure⟩
instance ultrafilter.has_bind : has_bind ultrafilter := ⟨@ultrafilter.bind⟩
instance ultrafilter.functor : functor ultrafilter := { map := @ultrafilter.map }
instance ultrafilter.monad : monad ultrafilter := { map := @ultrafilter.map }

instance ultrafilter.inhabited [inhabited α] : inhabited (ultrafilter α) := ⟨pure (default _)⟩

/-- The ultra-filter extending the cofinite filter. -/
noncomputable def hyperfilter : filter α := ultrafilter_of cofinite

lemma hyperfilter_le_cofinite : @hyperfilter α ≤ cofinite :=
ultrafilter_of_le

lemma is_ultrafilter_hyperfilter [infinite α] : is_ultrafilter (@hyperfilter α) :=
(ultrafilter_of_spec cofinite_ne_bot).2

theorem nmem_hyperfilter_of_finite [infinite α] {s : set α} (hf : s.finite) :
  s ∉ @hyperfilter α :=
λ hy,
have hx : -s ∉ hyperfilter :=
  λ hs, (ultrafilter_iff_compl_mem_iff_not_mem.mp is_ultrafilter_hyperfilter s).mp hs hy,
have ht : -s ∈ cofinite.sets := by show -s ∈ {s | _}; rwa [set.mem_set_of_eq, compl_compl],
hx $ hyperfilter_le_cofinite ht

theorem compl_mem_hyperfilter_of_finite [infinite α] {s : set α} (hf : set.finite s) :
  -s ∈ @hyperfilter α :=
(ultrafilter_iff_compl_mem_iff_not_mem.mp is_ultrafilter_hyperfilter s).mpr $
nmem_hyperfilter_of_finite hf

theorem mem_hyperfilter_of_finite_compl [infinite α] {s : set α} (hf : set.finite (-s)) :
  s ∈ @hyperfilter α :=
s.compl_compl ▸ compl_mem_hyperfilter_of_finite hf

section

local attribute [instance] filter.monad filter.is_lawful_monad

instance ultrafilter.is_lawful_monad : is_lawful_monad ultrafilter :=
{ id_map := assume α f, subtype.eq (id_map f.val),
  pure_bind := assume α β a f, subtype.eq (pure_bind a (subtype.val ∘ f)),
  bind_assoc := assume α β γ f m₁ m₂, subtype.eq (filter_eq rfl),
  bind_pure_comp_eq_map := assume α β f x, subtype.eq (bind_pure_comp_eq_map f x.val) }

end

lemma ultrafilter.eq_iff_val_le_val {u v : ultrafilter α} : u = v ↔ u.val ≤ v.val :=
⟨assume h, by rw h; exact le_refl _,
 assume h, by rw subtype.ext; apply ultrafilter_unique v.property u.property.1 h⟩

lemma exists_ultrafilter_iff (f : filter α) : (∃ (u : ultrafilter α), u.val ≤ f) ↔ f ≠ ⊥ :=
⟨assume ⟨u, uf⟩, ne_bot_of_le_ne_bot u.property.1 uf,
 assume h, let ⟨u, uf, hu⟩ := exists_ultrafilter h in ⟨⟨u, hu⟩, uf⟩⟩

end ultrafilter

end filter
