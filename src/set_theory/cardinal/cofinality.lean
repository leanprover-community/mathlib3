/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios
-/

import set_theory.cardinal.ordinal
import set_theory.ordinal.fixed_point

/-!
# Cofinality

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains the definition of cofinality of an ordinal number and regular cardinals

## Main Definitions

* `ordinal.cof o` is the cofinality of the ordinal `o`.
  If `o` is the order type of the relation `<` on `α`, then `o.cof` is the smallest cardinality of a
  subset `s` of α that is *cofinal* in `α`, i.e. `∀ x : α, ∃ y ∈ s, ¬ y < x`.
* `cardinal.is_limit c` means that `c` is a (weak) limit cardinal: `c ≠ 0 ∧ ∀ x < c, succ x < c`.
* `cardinal.is_strong_limit c` means that `c` is a strong limit cardinal:
  `c ≠ 0 ∧ ∀ x < c, 2 ^ x < c`.
* `cardinal.is_regular c` means that `c` is a regular cardinal: `ℵ₀ ≤ c ∧ c.ord.cof = c`.
* `cardinal.is_inaccessible c` means that `c` is strongly inaccessible:
  `ℵ₀ < c ∧ is_regular c ∧ is_strong_limit c`.

## Main Statements

* `ordinal.infinite_pigeonhole_card`: the infinite pigeonhole principle
* `cardinal.lt_power_cof`: A consequence of König's theorem stating that `c < c ^ c.ord.cof` for
  `c ≥ ℵ₀`
* `cardinal.univ_inaccessible`: The type of ordinals in `Type u` form an inaccessible cardinal
  (in `Type v` with `v > u`). This shows (externally) that in `Type u` there are at least `u`
  inaccessible cardinals.

## Implementation Notes

* The cofinality is defined for ordinals.
  If `c` is a cardinal number, its cofinality is `c.ord.cof`.

## Tags

cofinality, regular cardinals, limits cardinals, inaccessible cardinals,
infinite pigeonhole principle
-/

noncomputable theory

open function cardinal set order
open_locale classical cardinal ordinal

universes u v w
variables {α : Type*} {r : α → α → Prop}

/-! ### Cofinality of orders -/

namespace order

/-- Cofinality of a reflexive order `≼`. This is the smallest cardinality
  of a subset `S : set α` such that `∀ a, ∃ b ∈ S, a ≼ b`. -/
def cof (r : α → α → Prop) : cardinal :=
Inf {c | ∃ S : set α, (∀ a, ∃ b ∈ S, r a b) ∧ #S = c}

/-- The set in the definition of `order.cof` is nonempty. -/
theorem cof_nonempty (r : α → α → Prop) [is_refl α r] :
  {c | ∃ S : set α, (∀ a, ∃ b ∈ S, r a b) ∧ #S = c}.nonempty :=
⟨_, set.univ, λ a, ⟨a, ⟨⟩, refl _⟩, rfl⟩

lemma cof_le (r : α → α → Prop) {S : set α} (h : ∀ a, ∃ b ∈ S, r a b) : cof r ≤ #S :=
cInf_le' ⟨S, h, rfl⟩

lemma le_cof {r : α → α → Prop} [is_refl α r] (c : cardinal) :
  c ≤ cof r ↔ ∀ {S : set α}, (∀ a, ∃ b ∈ S, r a b) → c ≤ #S :=
begin
  rw [cof, le_cInf_iff'' (cof_nonempty r)],
  use λ H S h, H _ ⟨S, h, rfl⟩,
  rintro H d ⟨S, h, rfl⟩,
  exact H h
end

end order

theorem rel_iso.cof_le_lift {α : Type u} {β : Type v} {r : α → α → Prop} {s}
  [is_refl β s] (f : r ≃r s) :
  cardinal.lift.{max u v} (order.cof r) ≤ cardinal.lift.{max u v} (order.cof s) :=
begin
  rw [order.cof, order.cof, lift_Inf, lift_Inf,
    le_cInf_iff'' (nonempty_image_iff.2 (order.cof_nonempty s))],
  rintros - ⟨-, ⟨u, H, rfl⟩, rfl⟩,
  apply cInf_le',
  refine ⟨_, ⟨f.symm '' u, λ a, _, rfl⟩,
    lift_mk_eq.{u v (max u v)}.2 ⟨((f.symm).to_equiv.image u).symm⟩⟩,
  rcases H (f a) with ⟨b, hb, hb'⟩,
  refine ⟨f.symm b, mem_image_of_mem _ hb, f.map_rel_iff.1 _⟩,
  rwa rel_iso.apply_symm_apply
end

theorem rel_iso.cof_eq_lift {α : Type u} {β : Type v} {r s}
  [is_refl α r] [is_refl β s] (f : r ≃r s) :
  cardinal.lift.{max u v} (order.cof r) = cardinal.lift.{max u v} (order.cof s) :=
(rel_iso.cof_le_lift f).antisymm (rel_iso.cof_le_lift f.symm)

theorem rel_iso.cof_le {α β : Type u} {r : α → α → Prop} {s} [is_refl β s] (f : r ≃r s) :
  order.cof r ≤ order.cof s :=
lift_le.1 (rel_iso.cof_le_lift f)

theorem rel_iso.cof_eq {α β : Type u} {r s} [is_refl α r] [is_refl β s] (f : r ≃r s) :
  order.cof r = order.cof s :=
lift_inj.1 (rel_iso.cof_eq_lift f)

/-- Cofinality of a strict order `≺`. This is the smallest cardinality of a set `S : set α` such
that `∀ a, ∃ b ∈ S, ¬ b ≺ a`. -/
def strict_order.cof (r : α → α → Prop) : cardinal :=
order.cof (swap r)ᶜ

/-- The set in the definition of `order.strict_order.cof` is nonempty. -/
theorem strict_order.cof_nonempty (r : α → α → Prop) [is_irrefl α r] :
  {c | ∃ S : set α, unbounded r S ∧ #S = c}.nonempty :=
@order.cof_nonempty α _ (is_refl.swap rᶜ)

/-! ### Cofinality of ordinals -/

namespace ordinal

/-- Cofinality of an ordinal. This is the smallest cardinal of a
  subset `S` of the ordinal which is unbounded, in the sense
  `∀ a, ∃ b ∈ S, a ≤ b`. It is defined for all ordinals, but
  `cof 0 = 0` and `cof (succ o) = 1`, so it is only really
  interesting on limit ordinals (when it is an infinite cardinal). -/
def cof (o : ordinal.{u}) : cardinal.{u} :=
o.lift_on (λ a, strict_order.cof a.r)
begin
  rintros ⟨α, r, wo₁⟩ ⟨β, s, wo₂⟩ ⟨⟨f, hf⟩⟩,
  haveI := wo₁, haveI := wo₂,
  apply @rel_iso.cof_eq _ _ _ _ _ _ ,
  { split, exact λ a b, not_iff_not.2 hf },
  { exact ⟨(is_well_order.is_irrefl r).1⟩ },
  { exact ⟨(is_well_order.is_irrefl s).1⟩ }
end

lemma cof_type (r : α → α → Prop) [is_well_order α r] : (type r).cof = strict_order.cof r := rfl

theorem le_cof_type [is_well_order α r] {c} : c ≤ cof (type r) ↔ ∀ S, unbounded r S → c ≤ #S :=
(le_cInf_iff'' (strict_order.cof_nonempty r)).trans ⟨λ H S h, H _ ⟨S, h, rfl⟩,
  by { rintros H d ⟨S, h, rfl⟩, exact H _ h }⟩

theorem cof_type_le [is_well_order α r] {S : set α} (h : unbounded r S) : cof (type r) ≤ #S :=
le_cof_type.1 le_rfl S h

theorem lt_cof_type [is_well_order α r] {S : set α} : #S < cof (type r) → bounded r S :=
by simpa using not_imp_not.2 cof_type_le

theorem cof_eq (r : α → α → Prop) [is_well_order α r] : ∃ S, unbounded r S ∧ #S = cof (type r) :=
Inf_mem (strict_order.cof_nonempty r)

theorem ord_cof_eq (r : α → α → Prop) [is_well_order α r] :
  ∃ S, unbounded r S ∧ type (subrel r S) = (cof (type r)).ord :=
let ⟨S, hS, e⟩ := cof_eq r, ⟨s, _, e'⟩ := cardinal.ord_eq S,
    T : set α := {a | ∃ aS : a ∈ S, ∀ b : S, s b ⟨_, aS⟩ → r b a} in
begin
  resetI, suffices,
  { refine ⟨T, this,
      le_antisymm _ (cardinal.ord_le.2 $ cof_type_le this)⟩,
    rw [← e, e'],
    refine (rel_embedding.of_monotone (λ a : T, (⟨a, let ⟨aS, _⟩ := a.2 in aS⟩ : S)) (λ a b h, _))
      .ordinal_type_le,
    rcases a with ⟨a, aS, ha⟩, rcases b with ⟨b, bS, hb⟩,
    change s ⟨a, _⟩ ⟨b, _⟩,
    refine ((trichotomous_of s _ _).resolve_left (λ hn, _)).resolve_left _,
    { exact asymm h (ha _ hn) },
    { intro e, injection e with e, subst b,
      exact irrefl _ h } },
  { intro a,
    have : {b : S | ¬ r b a}.nonempty := let ⟨b, bS, ba⟩ := hS a in ⟨⟨b, bS⟩, ba⟩,
    let b := (is_well_founded.wf).min _ this,
    have ba : ¬r b a := (is_well_founded.wf).min_mem _ this,
    refine ⟨b, ⟨b.2, λ c, not_imp_not.1 $ λ h, _⟩, ba⟩,
    rw [show ∀b:S, (⟨b, b.2⟩:S) = b, by intro b; cases b; refl],
    exact (is_well_founded.wf).not_lt_min _ this
      (is_order_connected.neg_trans h ba) }
end

/-! ### Cofinality of suprema and least strict upper bounds -/

private theorem card_mem_cof {o} : ∃ {ι} (f : ι → ordinal), lsub.{u u} f = o ∧ #ι = o.card :=
⟨_, _, lsub_typein o, mk_ordinal_out o⟩

/-- The set in the `lsub` characterization of `cof` is nonempty. -/
theorem cof_lsub_def_nonempty (o) :
  {a : cardinal | ∃ {ι} (f : ι → ordinal), lsub.{u u} f = o ∧ #ι = a}.nonempty :=
⟨_, card_mem_cof⟩

theorem cof_eq_Inf_lsub (o : ordinal.{u}) :
  cof o = Inf {a : cardinal | ∃ {ι : Type u} (f : ι → ordinal), lsub.{u u} f = o ∧ #ι = a} :=
begin
  refine le_antisymm (le_cInf (cof_lsub_def_nonempty o) _) (cInf_le' _),
  { rintros a ⟨ι, f, hf, rfl⟩,
    rw ←type_lt o,
    refine (cof_type_le (λ a, _)).trans (@mk_le_of_injective _ _
      (λ s : (typein ((<) : o.out.α → o.out.α → Prop))⁻¹' (set.range f), classical.some s.prop)
      (λ s t hst, let H := congr_arg f hst in by rwa [classical.some_spec s.prop,
        classical.some_spec t.prop, typein_inj, subtype.coe_inj] at H)),
    have := typein_lt_self a,
    simp_rw [←hf, lt_lsub_iff] at this,
    cases this with i hi,
    refine ⟨enum (<) (f i) _, _, _⟩,
    { rw [type_lt, ←hf], apply lt_lsub },
    { rw [mem_preimage, typein_enum], exact mem_range_self i },
    { rwa [←typein_le_typein, typein_enum] } },
  { rcases cof_eq (<) with ⟨S, hS, hS'⟩,
    let f : S → ordinal := λ s, typein (<) s.val,
    refine ⟨S, f, le_antisymm (lsub_le (λ i, typein_lt_self i)) (le_of_forall_lt (λ a ha, _)),
      by rwa type_lt o at hS'⟩,
    rw ←type_lt o at ha,
    rcases hS (enum (<) a ha) with ⟨b, hb, hb'⟩,
    rw [←typein_le_typein, typein_enum] at hb',
    exact hb'.trans_lt (lt_lsub.{u u} f ⟨b, hb⟩) }
end

@[simp] theorem lift_cof (o) : (cof o).lift = cof o.lift :=
begin
  refine induction_on o _,
  introsI α r _,
  apply le_antisymm,
  { refine le_cof_type.2 (λ S H, _),
    have : (#(ulift.up ⁻¹' S)).lift ≤ #S,
    { rw [← cardinal.lift_umax, ← cardinal.lift_id' (#S)],
      exact mk_preimage_of_injective_lift ulift.up _ ulift.up_injective },
    refine (cardinal.lift_le.2 $ cof_type_le _).trans this,
    exact λ a, let ⟨⟨b⟩, bs, br⟩ := H ⟨a⟩ in ⟨b, bs, br⟩ },
  { rcases cof_eq r with ⟨S, H, e'⟩,
    have : #(ulift.down ⁻¹' S) ≤ (#S).lift :=
     ⟨⟨λ ⟨⟨x⟩, h⟩, ⟨⟨x, h⟩⟩,
       λ ⟨⟨x⟩, h₁⟩ ⟨⟨y⟩, h₂⟩ e, by simp at e; congr; injections⟩⟩,
    rw e' at this,
    unfreezingI { refine (cof_type_le _).trans this },
    exact λ ⟨a⟩, let ⟨b, bs, br⟩ := H a in ⟨⟨b⟩, bs, br⟩ }
end

theorem cof_le_card (o) : cof o ≤ card o :=
by { rw cof_eq_Inf_lsub, exact cInf_le' card_mem_cof }

theorem cof_ord_le (c : cardinal) : c.ord.cof ≤ c :=
by simpa using cof_le_card c.ord

theorem ord_cof_le (o : ordinal.{u}) : o.cof.ord ≤ o :=
(ord_le_ord.2 (cof_le_card o)).trans (ord_card_le o)

theorem exists_lsub_cof (o : ordinal) : ∃ {ι} (f : ι → ordinal), lsub.{u u} f = o ∧ #ι = cof o :=
by { rw cof_eq_Inf_lsub, exact Inf_mem (cof_lsub_def_nonempty o) }

theorem cof_lsub_le {ι} (f : ι → ordinal) : cof (lsub.{u u} f) ≤ #ι :=
by { rw cof_eq_Inf_lsub, exact cInf_le' ⟨ι, f, rfl, rfl⟩ }

theorem cof_lsub_le_lift {ι} (f : ι → ordinal) : cof (lsub f) ≤ cardinal.lift.{v u} (#ι) :=
begin
  rw ←mk_ulift,
  convert cof_lsub_le (λ i : ulift ι, f i.down),
  exact lsub_eq_of_range_eq.{u (max u v) max u v}
    (set.ext (λ x, ⟨λ ⟨i, hi⟩, ⟨ulift.up i, hi⟩, λ ⟨i, hi⟩, ⟨_, hi⟩⟩))
end

theorem le_cof_iff_lsub {o : ordinal} {a : cardinal} :
  a ≤ cof o ↔ ∀ {ι} (f : ι → ordinal), lsub.{u u} f = o → a ≤ #ι :=
begin
  rw cof_eq_Inf_lsub,
  exact (le_cInf_iff'' (cof_lsub_def_nonempty o)).trans ⟨λ H ι f hf, H _ ⟨ι, f, hf, rfl⟩,
    λ H b ⟨ι, f, hf, hb⟩, ( by { rw ←hb, exact H _ hf} )⟩
end

theorem lsub_lt_ord_lift {ι} {f : ι → ordinal} {c : ordinal} (hι : cardinal.lift (#ι) < c.cof)
  (hf : ∀ i, f i < c) : lsub.{u v} f < c :=
lt_of_le_of_ne (lsub_le hf) (λ h, by { subst h, exact (cof_lsub_le_lift f).not_lt hι })

theorem lsub_lt_ord {ι} {f : ι → ordinal} {c : ordinal} (hι : #ι < c.cof) :
  (∀ i, f i < c) → lsub.{u u} f < c :=
lsub_lt_ord_lift (by rwa (#ι).lift_id)

theorem cof_sup_le_lift {ι} {f : ι → ordinal} (H : ∀ i, f i < sup f) : cof (sup f) ≤ (#ι).lift :=
by { rw ←sup_eq_lsub_iff_lt_sup at H, rw H, exact cof_lsub_le_lift f }

theorem cof_sup_le {ι} {f : ι → ordinal} (H : ∀ i, f i < sup.{u u} f) : cof (sup.{u u} f) ≤ #ι :=
by { rw ←(#ι).lift_id, exact cof_sup_le_lift H }

theorem sup_lt_ord_lift {ι} {f : ι → ordinal} {c : ordinal} (hι : cardinal.lift (#ι) < c.cof)
  (hf : ∀ i, f i < c) : sup.{u v} f < c :=
(sup_le_lsub.{u v} f).trans_lt (lsub_lt_ord_lift hι hf)

theorem sup_lt_ord {ι} {f : ι → ordinal} {c : ordinal} (hι : #ι < c.cof) :
  (∀ i, f i < c) → sup.{u u} f < c :=
sup_lt_ord_lift (by rwa (#ι).lift_id)

theorem supr_lt_lift {ι} {f : ι → cardinal} {c : cardinal} (hι : cardinal.lift (#ι) < c.ord.cof)
  (hf : ∀ i, f i < c) : supr f < c :=
begin
  rw [←ord_lt_ord, supr_ord (cardinal.bdd_above_range _)],
  refine sup_lt_ord_lift hι (λ i, _),
  rw ord_lt_ord,
  apply hf
end

theorem supr_lt {ι} {f : ι → cardinal} {c : cardinal} (hι : #ι < c.ord.cof) :
  (∀ i, f i < c) → supr f < c :=
supr_lt_lift (by rwa (#ι).lift_id)

theorem nfp_family_lt_ord_lift {ι} {f : ι → ordinal → ordinal} {c} (hc : ℵ₀ < cof c)
  (hc' : (#ι).lift < cof c) (hf : ∀ i (b < c), f i b < c) {a} (ha : a < c) :
  nfp_family.{u v} f a < c :=
begin
  refine sup_lt_ord_lift ((cardinal.lift_le.2 (mk_list_le_max ι)).trans_lt _) (λ l, _),
  { rw lift_max,
    apply max_lt _ hc',
    rwa cardinal.lift_aleph_0 },
  { induction l with i l H,
    { exact ha },
    { exact hf _ _ H } }
end

theorem nfp_family_lt_ord {ι} {f : ι → ordinal → ordinal} {c} (hc : ℵ₀ < cof c)
  (hc' : #ι < cof c) (hf : ∀ i (b < c), f i b < c) {a} : a < c → nfp_family.{u u} f a < c :=
nfp_family_lt_ord_lift hc (by rwa (#ι).lift_id) hf

theorem nfp_bfamily_lt_ord_lift {o : ordinal} {f : Π a < o, ordinal → ordinal} {c} (hc : ℵ₀ < cof c)
  (hc' : o.card.lift < cof c) (hf : ∀ i hi (b < c), f i hi b < c) {a} :
  a < c → nfp_bfamily.{u v} o f a < c :=
nfp_family_lt_ord_lift hc (by rwa mk_ordinal_out) (λ i, hf _ _)

theorem nfp_bfamily_lt_ord {o : ordinal} {f : Π a < o, ordinal → ordinal} {c} (hc : ℵ₀ < cof c)
  (hc' : o.card < cof c) (hf : ∀ i hi (b < c), f i hi b < c) {a} :
  a < c → nfp_bfamily.{u u} o f a < c :=
nfp_bfamily_lt_ord_lift hc (by rwa o.card.lift_id) hf

theorem nfp_lt_ord {f : ordinal → ordinal} {c} (hc : ℵ₀ < cof c) (hf : ∀ i < c, f i < c) {a} :
  a < c → nfp f a < c :=
nfp_family_lt_ord_lift hc (by simpa using cardinal.one_lt_aleph_0.trans hc) (λ _, hf)

theorem exists_blsub_cof (o : ordinal) : ∃ (f : Π a < (cof o).ord, ordinal), blsub.{u u} _ f = o :=
begin
  rcases exists_lsub_cof o with ⟨ι, f, hf, hι⟩,
  rcases cardinal.ord_eq ι with ⟨r, hr, hι'⟩,
  rw ←@blsub_eq_lsub' ι r hr at hf,
  rw [←hι, hι'],
  exact ⟨_, hf⟩
end

theorem le_cof_iff_blsub {b : ordinal} {a : cardinal} :
  a ≤ cof b ↔ ∀ {o} (f : Π a < o, ordinal), blsub.{u u} o f = b → a ≤ o.card :=
le_cof_iff_lsub.trans ⟨λ H o f hf, by simpa using H _ hf, λ H ι f hf, begin
  rcases cardinal.ord_eq ι with ⟨r, hr, hι'⟩,
  rw ←@blsub_eq_lsub' ι r hr at hf,
  simpa using H _ hf
end⟩

theorem cof_blsub_le_lift {o} (f : Π a < o, ordinal) :
  cof (blsub o f) ≤ cardinal.lift.{v u} (o.card) :=
by { convert cof_lsub_le_lift _, exact (mk_ordinal_out o).symm }

theorem cof_blsub_le {o} (f : Π a < o, ordinal) : cof (blsub.{u u} o f) ≤ o.card :=
by { rw ←(o.card).lift_id, exact cof_blsub_le_lift f }

theorem blsub_lt_ord_lift {o : ordinal} {f : Π a < o, ordinal} {c : ordinal}
  (ho : o.card.lift < c.cof) (hf : ∀ i hi, f i hi < c) : blsub.{u v} o f < c :=
lt_of_le_of_ne (blsub_le hf) (λ h, ho.not_le
  (by simpa [←supr_ord, hf, h] using cof_blsub_le_lift.{u} f))

theorem blsub_lt_ord {o : ordinal} {f : Π a < o, ordinal} {c : ordinal} (ho : o.card < c.cof)
  (hf : ∀ i hi, f i hi < c) : blsub.{u u} o f < c :=
blsub_lt_ord_lift (by rwa (o.card).lift_id) hf

theorem cof_bsup_le_lift {o : ordinal} {f : Π a < o, ordinal} (H : ∀ i h, f i h < bsup o f) :
  cof (bsup o f) ≤ o.card.lift :=
by { rw ←bsup_eq_blsub_iff_lt_bsup at H, rw H, exact cof_blsub_le_lift f }

theorem cof_bsup_le {o : ordinal} {f : Π a < o, ordinal} :
  (∀ i h, f i h < bsup.{u u} o f) → cof (bsup.{u u} o f) ≤ o.card :=
by { rw ←(o.card).lift_id, exact cof_bsup_le_lift }

theorem bsup_lt_ord_lift {o : ordinal} {f : Π a < o, ordinal} {c : ordinal}
  (ho : o.card.lift < c.cof) (hf : ∀ i hi, f i hi < c) : bsup.{u v} o f < c :=
(bsup_le_blsub f).trans_lt (blsub_lt_ord_lift ho hf)

theorem bsup_lt_ord {o : ordinal} {f : Π a < o, ordinal} {c : ordinal} (ho : o.card < c.cof) :
  (∀ i hi, f i hi < c) → bsup.{u u} o f < c :=
bsup_lt_ord_lift (by rwa (o.card).lift_id)

/-! ### Basic results -/

@[simp] theorem cof_zero : cof 0 = 0 :=
(cof_le_card 0).antisymm (cardinal.zero_le _)

@[simp] theorem cof_eq_zero {o} : cof o = 0 ↔ o = 0 :=
⟨induction_on o $ λ α r _ z, by exactI
  let ⟨S, hl, e⟩ := cof_eq r in type_eq_zero_iff_is_empty.2 $
  ⟨λ a, let ⟨b, h, _⟩ := hl a in
    (mk_eq_zero_iff.1 (e.trans z)).elim' ⟨_, h⟩⟩,
λ e, by simp [e]⟩

theorem cof_ne_zero {o} : cof o ≠ 0 ↔ o ≠ 0 := cof_eq_zero.not

@[simp] theorem cof_succ (o) : cof (succ o) = 1 :=
begin
  apply le_antisymm,
  { refine induction_on o (λ α r _, _),
    change cof (type _) ≤ _,
    rw [← (_ : #_ = 1)], apply cof_type_le,
    { refine λ a, ⟨sum.inr punit.star, set.mem_singleton _, _⟩,
      rcases a with a|⟨⟨⟨⟩⟩⟩; simp [empty_relation] },
    { rw [cardinal.mk_fintype, set.card_singleton], simp } },
  { rw [← cardinal.succ_zero, succ_le_iff],
    simpa [lt_iff_le_and_ne, cardinal.zero_le] using
      λ h, succ_ne_zero o (cof_eq_zero.1 (eq.symm h)) }
end

@[simp] theorem cof_eq_one_iff_is_succ {o} : cof.{u} o = 1 ↔ ∃ a, o = succ a :=
⟨induction_on o $ λ α r _ z, begin
  resetI,
  rcases cof_eq r with ⟨S, hl, e⟩, rw z at e,
  cases mk_ne_zero_iff.1 (by rw e; exact one_ne_zero) with a,
  refine ⟨typein r a, eq.symm $ quotient.sound
    ⟨rel_iso.of_surjective (rel_embedding.of_monotone _
      (λ x y, _)) (λ x, _)⟩⟩,
  { apply sum.rec; [exact subtype.val, exact λ _, a] },
  { rcases x with x|⟨⟨⟨⟩⟩⟩; rcases y with y|⟨⟨⟨⟩⟩⟩;
      simp [subrel, order.preimage, empty_relation],
    exact x.2 },
  { suffices : r x a ∨ ∃ (b : punit), ↑a = x, {simpa},
    rcases trichotomous_of r x a with h|h|h,
    { exact or.inl h },
    { exact or.inr ⟨punit.star, h.symm⟩ },
    { rcases hl x with ⟨a', aS, hn⟩,
      rw (_ : ↑a = a') at h, {exact absurd h hn},
      refine congr_arg subtype.val (_ : a = ⟨a', aS⟩),
      haveI := le_one_iff_subsingleton.1 (le_of_eq e),
      apply subsingleton.elim } }
end, λ ⟨a, e⟩, by simp [e]⟩

/-- A fundamental sequence for `a` is an increasing sequence of length `o = cof a` that converges at
    `a`. We provide `o` explicitly in order to avoid type rewrites. -/
def is_fundamental_sequence (a o : ordinal.{u}) (f : Π b < o, ordinal.{u}) : Prop :=
o ≤ a.cof.ord ∧ (∀ {i j} (hi hj), i < j → f i hi < f j hj) ∧ blsub.{u u} o f = a

namespace is_fundamental_sequence
variables {a o : ordinal.{u}} {f : Π b < o, ordinal.{u}}

protected theorem cof_eq (hf : is_fundamental_sequence a o f) : a.cof.ord = o :=
hf.1.antisymm' $ by { rw ←hf.2.2, exact (ord_le_ord.2 (cof_blsub_le f)).trans (ord_card_le o) }

protected theorem strict_mono (hf : is_fundamental_sequence a o f) {i j} :
  ∀ hi hj, i < j → f i hi < f j hj :=
hf.2.1

theorem blsub_eq (hf : is_fundamental_sequence a o f) : blsub.{u u} o f = a :=
hf.2.2

theorem ord_cof (hf : is_fundamental_sequence a o f) :
  is_fundamental_sequence a a.cof.ord (λ i hi, f i (hi.trans_le (by rw hf.cof_eq))) :=
by { have H := hf.cof_eq, subst H, exact hf }

theorem id_of_le_cof (h : o ≤ o.cof.ord) : is_fundamental_sequence o o (λ a _, a) :=
⟨h, λ _ _ _ _, id, blsub_id o⟩

protected theorem zero {f : Π b < (0 : ordinal), ordinal} :
  is_fundamental_sequence 0 0 f :=
⟨by rw [cof_zero, ord_zero], λ i j hi, (ordinal.not_lt_zero i hi).elim, blsub_zero f⟩

protected theorem succ : is_fundamental_sequence (succ o) 1 (λ _ _, o) :=
begin
  refine ⟨_, λ i j hi hj h, _, blsub_const ordinal.one_ne_zero o⟩,
  { rw [cof_succ, ord_one] },
  { rw lt_one_iff_zero at hi hj,
    rw [hi, hj] at h,
    exact h.false.elim }
end

protected theorem monotone (hf : is_fundamental_sequence a o f) {i j : ordinal} (hi : i < o)
  (hj : j < o) (hij : i ≤ j) : f i hi ≤ f j hj :=
begin
  rcases lt_or_eq_of_le hij with hij | rfl,
  { exact (hf.2.1 hi hj hij).le },
  { refl }
end

theorem trans {a o o' : ordinal.{u}} {f : Π b < o, ordinal.{u}}
  (hf : is_fundamental_sequence a o f) {g : Π b < o', ordinal.{u}}
  (hg : is_fundamental_sequence o o' g) :
  is_fundamental_sequence a o' (λ i hi, f (g i hi) (by { rw ←hg.2.2, apply lt_blsub })) :=
begin
  refine ⟨_, λ i j _ _ h, hf.2.1 _ _ (hg.2.1 _ _ h), _⟩,
  { rw hf.cof_eq,
    exact hg.1.trans (ord_cof_le o) },
  { rw @blsub_comp.{u u u} o _ f (@is_fundamental_sequence.monotone _ _ f hf),
    exact hf.2.2 }
end

end is_fundamental_sequence

/-- Every ordinal has a fundamental sequence. -/
theorem exists_fundamental_sequence (a : ordinal.{u}) :
  ∃ f, is_fundamental_sequence a a.cof.ord f :=
begin
  rsuffices ⟨o, f, hf⟩ : ∃ o f, is_fundamental_sequence a o f,
  { exact ⟨_, hf.ord_cof⟩ },
  rcases exists_lsub_cof a with ⟨ι, f, hf, hι⟩,
  rcases ord_eq ι with ⟨r, wo, hr⟩,
  haveI := wo,
  let r' := subrel r {i | ∀ j, r j i → f j < f i},
  let hrr' : r' ↪r r := subrel.rel_embedding _ _,
  haveI := hrr'.is_well_order,
  refine ⟨_, _, hrr'.ordinal_type_le.trans _, λ i j _ h _, (enum r' j h).prop _ _,
    le_antisymm (blsub_le (λ i hi, lsub_le_iff.1 hf.le _)) _⟩,
  { rw [←hι, hr] },
  { change r (hrr'.1 _ ) (hrr'.1 _ ),
    rwa [hrr'.2, @enum_lt_enum _ r'] },
  { rw [←hf, lsub_le_iff],
    intro i,
    rsuffices ⟨i', hi', hfg⟩ : ∃ i' hi', f i ≤ bfamily_of_family' r' (λ i, f i) i' hi',
    { exact hfg.trans_lt (lt_blsub _ _ _) },
    by_cases h : ∀ j, r j i → f j < f i,
    { refine ⟨typein r' ⟨i, h⟩, typein_lt_type _ _, _⟩,
      rw bfamily_of_family'_typein,
      refl },
    { push_neg at h,
      cases wo.wf.min_mem _ h with hji hij,
      refine ⟨typein r' ⟨_, λ k hkj, lt_of_lt_of_le _ hij⟩, typein_lt_type _ _, _⟩,
      { by_contra' H,
        exact (wo.wf.not_lt_min _ h ⟨is_trans.trans _ _ _ hkj hji, H⟩) hkj },
      { rwa bfamily_of_family'_typein } } }
end

@[simp] theorem cof_cof (a : ordinal.{u}) : cof (cof a).ord = cof a :=
begin
  cases exists_fundamental_sequence a with f hf,
  cases exists_fundamental_sequence a.cof.ord with g hg,
  exact ord_injective ((hf.trans hg).cof_eq.symm)
end

protected theorem is_normal.is_fundamental_sequence {f : ordinal.{u} → ordinal.{u}}
  (hf : is_normal f) {a o} (ha : is_limit a) {g} (hg : is_fundamental_sequence a o g) :
  is_fundamental_sequence (f a) o (λ b hb, f (g b hb)) :=
begin
  refine ⟨_, λ i j _ _ h, hf.strict_mono (hg.2.1 _ _ h), _⟩,
  { rcases exists_lsub_cof (f a) with ⟨ι, f', hf', hι⟩,
    rw [←hg.cof_eq, ord_le_ord, ←hι],
    suffices : lsub.{u u} (λ i, (Inf {b : ordinal | f' i ≤ f b})) = a,
    { rw ←this,
      apply cof_lsub_le },
    have H : ∀ i, ∃ b < a, f' i ≤ f b := λ i, begin
      have := lt_lsub.{u u} f' i,
      rwa [hf', ←is_normal.blsub_eq.{u u} hf ha, lt_blsub_iff] at this
    end,
    refine (lsub_le (λ i, _)).antisymm (le_of_forall_lt (λ b hb, _)),
    { rcases H i with ⟨b, hb, hb'⟩,
      exact lt_of_le_of_lt (cInf_le' hb') hb },
    { have := hf.strict_mono hb,
      rw [←hf', lt_lsub_iff] at this,
      cases this with i hi,
      rcases H i with ⟨b, _, hb⟩,
      exact ((le_cInf_iff'' ⟨b, hb⟩).2 (λ c hc, hf.strict_mono.le_iff_le.1 (hi.trans hc))).trans_lt
        (lt_lsub _ i) } },
  { rw @blsub_comp.{u u u} a _ (λ b _, f b) (λ i j hi hj h, hf.strict_mono.monotone h) g hg.2.2,
    exact is_normal.blsub_eq.{u u} hf ha }
end

theorem is_normal.cof_eq {f} (hf : is_normal f) {a} (ha : is_limit a) : cof (f a) = cof a :=
let ⟨g, hg⟩ := exists_fundamental_sequence a in
  ord_injective (hf.is_fundamental_sequence ha hg).cof_eq

theorem is_normal.cof_le {f} (hf : is_normal f) (a) : cof a ≤ cof (f a) :=
begin
  rcases zero_or_succ_or_limit a with rfl | ⟨b, rfl⟩ | ha,
  { rw cof_zero,
    exact zero_le _ },
  { rw [cof_succ, cardinal.one_le_iff_ne_zero, cof_ne_zero, ←ordinal.pos_iff_ne_zero],
    exact (ordinal.zero_le (f b)).trans_lt (hf.1 b) },
  { rw hf.cof_eq ha }
end

@[simp] theorem cof_add (a b : ordinal) : b ≠ 0 → cof (a + b) = cof b :=
λ h, begin
  rcases zero_or_succ_or_limit b with rfl | ⟨c, rfl⟩ | hb,
  { contradiction },
  { rw [add_succ, cof_succ, cof_succ] },
  { exact (add_is_normal a).cof_eq hb }
end

theorem aleph_0_le_cof {o} : ℵ₀ ≤ cof o ↔ is_limit o :=
begin
  rcases zero_or_succ_or_limit o with rfl|⟨o,rfl⟩|l,
  { simp [not_zero_is_limit, cardinal.aleph_0_ne_zero] },
  { simp [not_succ_is_limit, cardinal.one_lt_aleph_0] },
  { simp [l], refine le_of_not_lt (λ h, _),
    cases cardinal.lt_aleph_0.1 h with n e,
    have := cof_cof o,
    rw [e, ord_nat] at this,
    cases n,
    { simp at e, simpa [e, not_zero_is_limit] using l },
    { rw [nat_cast_succ, cof_succ] at this,
      rw [← this, cof_eq_one_iff_is_succ] at e,
      rcases e with ⟨a, rfl⟩,
      exact not_succ_is_limit _ l } }
end

@[simp] theorem aleph'_cof {o : ordinal} (ho : o.is_limit) : (aleph' o).ord.cof = o.cof :=
aleph'_is_normal.cof_eq ho

@[simp] theorem aleph_cof {o : ordinal} (ho : o.is_limit) : (aleph o).ord.cof = o.cof :=
aleph_is_normal.cof_eq ho

@[simp] theorem cof_omega : cof ω = ℵ₀ :=
(aleph_0_le_cof.2 omega_is_limit).antisymm' $ by { rw ←card_omega, apply cof_le_card }

theorem cof_eq' (r : α → α → Prop) [is_well_order α r] (h : is_limit (type r)) :
  ∃ S : set α, (∀ a, ∃ b ∈ S, r a b) ∧ #S = cof (type r) :=
let ⟨S, H, e⟩ := cof_eq r in
⟨S, λ a,
  let a' := enum r _ (h.2 _ (typein_lt_type r a)) in
  let ⟨b, h, ab⟩ := H a' in
  ⟨b, h, (is_order_connected.conn a b a' $ (typein_lt_typein r).1
    (by { rw typein_enum, exact lt_succ (typein _ _) })).resolve_right ab⟩,
e⟩

@[simp] theorem cof_univ : cof univ.{u v} = cardinal.univ :=
le_antisymm (cof_le_card _) begin
  refine le_of_forall_lt (λ c h, _),
  rcases lt_univ'.1 h with ⟨c, rfl⟩,
  rcases @cof_eq ordinal.{u} (<) _ with ⟨S, H, Se⟩,
  rw [univ, ← lift_cof, ← cardinal.lift_lift, cardinal.lift_lt, ← Se],
  refine lt_of_not_ge (λ h, _),
  cases cardinal.lift_down h with a e,
  refine quotient.induction_on a (λ α e, _) e,
  cases quotient.exact e with f,
  have f := equiv.ulift.symm.trans f,
  let g := λ a, (f a).1,
  let o := succ (sup.{u u} g),
  rcases H o with ⟨b, h, l⟩,
  refine l (lt_succ_iff.2 _),
  rw ← show g (f.symm ⟨b, h⟩) = b, by dsimp [g]; simp,
  apply le_sup
end

/-! ### Infinite pigeonhole principle -/

/-- If the union of s is unbounded and s is smaller than the cofinality,
  then s has an unbounded member -/
theorem unbounded_of_unbounded_sUnion (r : α → α → Prop) [wo : is_well_order α r] {s : set (set α)}
  (h₁ : unbounded r $ ⋃₀ s) (h₂ : #s < strict_order.cof r) : ∃ x ∈ s, unbounded r x :=
begin
  by_contra' h,
  simp_rw not_unbounded_iff at h,
  let f : s → α := λ x : s, wo.wf.sup x (h x.1 x.2),
  refine h₂.not_le (le_trans (cInf_le' ⟨range f, λ x, _, rfl⟩) mk_range_le),
  rcases h₁ x with ⟨y, ⟨c, hc, hy⟩, hxy⟩,
  exact ⟨f ⟨c, hc⟩, mem_range_self _, λ hxz, hxy (trans (wo.wf.lt_sup _ hy) hxz)⟩
end

/-- If the union of s is unbounded and s is smaller than the cofinality,
  then s has an unbounded member -/
theorem unbounded_of_unbounded_Union {α β : Type u} (r : α → α → Prop) [wo : is_well_order α r]
  (s : β → set α)
  (h₁ : unbounded r $ ⋃ x, s x) (h₂ : #β < strict_order.cof r) : ∃ x : β, unbounded r (s x) :=
begin
  rw ←sUnion_range at h₁,
  rcases unbounded_of_unbounded_sUnion r h₁ (mk_range_le.trans_lt h₂) with ⟨_, ⟨x, rfl⟩, u⟩,
  exact ⟨x, u⟩
end

/-- The infinite pigeonhole principle -/
theorem infinite_pigeonhole {β α : Type u} (f : β → α) (h₁ : ℵ₀ ≤ #β)
  (h₂ : #α < (#β).ord.cof) : ∃ a : α, #(f ⁻¹' {a}) = #β :=
begin
  have : ∃ a, #β ≤ #(f ⁻¹' {a}),
  { by_contra' h,
    apply mk_univ.not_lt,
    rw [←preimage_univ, ←Union_of_singleton, preimage_Union],
    exact mk_Union_le_sum_mk.trans_lt ((sum_le_supr _).trans_lt $ mul_lt_of_lt h₁
      (h₂.trans_le $ cof_ord_le _) (supr_lt h₂ h)) },
  cases this with x h,
  refine ⟨x, h.antisymm' _⟩,
  rw le_mk_iff_exists_set,
  exact ⟨_, rfl⟩
end

/-- Pigeonhole principle for a cardinality below the cardinality of the domain -/
theorem infinite_pigeonhole_card {β α : Type u} (f : β → α) (θ : cardinal) (hθ : θ ≤ #β)
  (h₁ : ℵ₀ ≤ θ) (h₂ : #α < θ.ord.cof) : ∃ a : α, θ ≤ #(f ⁻¹' {a}) :=
begin
  rcases le_mk_iff_exists_set.1 hθ with ⟨s, rfl⟩,
  cases infinite_pigeonhole (f ∘ subtype.val : s → α) h₁ h₂ with a ha,
  use a, rw [←ha, @preimage_comp _ _ _ subtype.val f],
  exact mk_preimage_of_injective _ _ subtype.val_injective
end

theorem infinite_pigeonhole_set {β α : Type u} {s : set β} (f : s → α) (θ : cardinal)
  (hθ : θ ≤ #s) (h₁ : ℵ₀ ≤ θ) (h₂ : #α < θ.ord.cof) :
    ∃ (a : α) (t : set β) (h : t ⊆ s), θ ≤ #t ∧ ∀ {{x}} (hx : x ∈ t), f ⟨x, h hx⟩ = a :=
begin
  cases infinite_pigeonhole_card f θ hθ h₁ h₂ with a ha,
  refine ⟨a, {x | ∃ h, f ⟨x, h⟩ = a}, _, _, _⟩,
  { rintro x ⟨hx, hx'⟩, exact hx },
  { refine ha.trans (ge_of_eq $ quotient.sound ⟨equiv.trans _
      (equiv.subtype_subtype_equiv_subtype_exists _ _).symm⟩),
    simp only [coe_eq_subtype, mem_singleton_iff, mem_preimage, mem_set_of_eq] },
  rintro x ⟨hx, hx'⟩, exact hx'
end

end ordinal

/-! ### Regular and inaccessible cardinals -/

namespace cardinal
open ordinal

local infixr (name := cardinal.pow) ^ := @pow cardinal.{u} cardinal cardinal.has_pow

/-- A cardinal is a limit if it is not zero or a successor
  cardinal. Note that `ℵ₀` is a limit cardinal by this definition. -/
def is_limit (c : cardinal) : Prop :=
c ≠ 0 ∧ ∀ x < c, succ x < c

theorem is_limit.ne_zero {c} (h : is_limit c) : c ≠ 0 :=
h.1

theorem is_limit.succ_lt {x c} (h : is_limit c) : x < c → succ x < c :=
h.2 x

theorem is_limit.aleph_0_le {c} (h : is_limit c) : ℵ₀ ≤ c :=
begin
  by_contra' h',
  rcases lt_aleph_0.1 h' with ⟨_ | n, rfl⟩,
  { exact h.1.irrefl },
  { simpa using h.2 n }
end

/-- A cardinal is a strong limit if it is not zero and it is
  closed under powersets. Note that `ℵ₀` is a strong limit by this definition. -/
def is_strong_limit (c : cardinal) : Prop :=
c ≠ 0 ∧ ∀ x < c, 2 ^ x < c

theorem is_strong_limit.ne_zero {c} (h : is_strong_limit c) : c ≠ 0 :=
h.1

theorem is_strong_limit.two_power_lt {x c} (h : is_strong_limit c) : x < c → 2 ^ x < c :=
h.2 x

theorem is_strong_limit_aleph_0 : is_strong_limit ℵ₀ :=
⟨aleph_0_ne_zero, λ x hx, begin
  rcases lt_aleph_0.1 hx with ⟨n, rfl⟩,
  exact_mod_cast nat_lt_aleph_0 (pow 2 n)
end⟩

theorem is_strong_limit.is_limit {c} (H : is_strong_limit c) : is_limit c :=
⟨H.1, λ x h, (succ_le_of_lt $ cantor x).trans_lt (H.2 _ h)⟩

theorem is_limit_aleph_0 : is_limit ℵ₀ :=
is_strong_limit_aleph_0.is_limit

theorem is_strong_limit_beth {o : ordinal} (H : ∀ a < o, succ a < o) : is_strong_limit (beth o) :=
begin
  rcases eq_or_ne o 0 with rfl | h,
  { rw beth_zero,
    exact is_strong_limit_aleph_0 },
  { refine ⟨beth_ne_zero o, λ a ha, _⟩,
    rw beth_limit ⟨h, H⟩ at ha,
    rcases exists_lt_of_lt_csupr' ha with ⟨⟨i, hi⟩, ha⟩,
    have := power_le_power_left two_ne_zero ha.le,
    rw ←beth_succ at this,
    exact this.trans_lt (beth_lt.2 (H i hi)) }
end

theorem mk_bounded_subset {α : Type*} (h : ∀ x < #α, 2 ^ x < #α) {r : α → α → Prop}
  [is_well_order α r] (hr : (#α).ord = type r) : #{s : set α // bounded r s} = #α :=
begin
  rcases eq_or_ne (#α) 0 with ha | ha,
  { rw ha,
    haveI := mk_eq_zero_iff.1 ha,
    rw mk_eq_zero_iff,
    split,
    rintro ⟨s, hs⟩,
    exact (not_unbounded_iff s).2 hs (unbounded_of_is_empty s) },
  have h' : is_strong_limit (#α) := ⟨ha, h⟩,
  have ha := h'.is_limit.aleph_0_le,
  apply le_antisymm,
  { have : {s : set α | bounded r s} = ⋃ i, 𝒫 {j | r j i} := set_of_exists _,
    rw [←coe_set_of, this],
    convert mk_Union_le_sum_mk.trans ((sum_le_supr _).trans (mul_le_max_of_aleph_0_le_left ha)),
    apply (max_eq_left _).symm, apply csupr_le' (λ i, _),
    rw mk_powerset,
    apply (h'.two_power_lt _).le,
    rw [coe_set_of, card_typein, ←lt_ord, hr],
    apply typein_lt_type },
  { refine @mk_le_of_injective α _ (λ x, subtype.mk {x} _) _,
    { apply bounded_singleton,
      rw ←hr,
      apply ord_is_limit ha },
    { intros a b hab,
      simpa only [singleton_eq_singleton_iff] using hab } }
end

theorem mk_subset_mk_lt_cof {α : Type*} (h : ∀ x < #α, 2 ^ x < #α) :
  #{s : set α // #s < cof (#α).ord} = #α :=
begin
  rcases eq_or_ne (#α) 0 with ha | ha,
  { rw ha,
    simp [λ s, (cardinal.zero_le s).not_lt] },
  have h' : is_strong_limit (#α) := ⟨ha, h⟩,
  rcases ord_eq α with ⟨r, wo, hr⟩,
  haveI := wo,
  apply le_antisymm,
  { nth_rewrite_rhs 0 ←mk_bounded_subset h hr,
    apply mk_le_mk_of_subset (λ s hs, _),
    rw hr at hs,
    exact lt_cof_type hs },
  { refine @mk_le_of_injective α _ (λ x, subtype.mk {x} _) _,
    { rw mk_singleton,
      exact one_lt_aleph_0.trans_le (aleph_0_le_cof.2 (ord_is_limit h'.is_limit.aleph_0_le)) },
    { intros a b hab,
      simpa only [singleton_eq_singleton_iff] using hab } }
end

/-- A cardinal is regular if it is infinite and it equals its own cofinality. -/
def is_regular (c : cardinal) : Prop :=
ℵ₀ ≤ c ∧ c ≤ c.ord.cof

lemma is_regular.aleph_0_le {c : cardinal} (H : c.is_regular) : ℵ₀ ≤ c :=
H.1

lemma is_regular.cof_eq {c : cardinal} (H : c.is_regular) : c.ord.cof = c :=
(cof_ord_le c).antisymm H.2

lemma is_regular.pos {c : cardinal} (H : c.is_regular) : 0 < c :=
aleph_0_pos.trans_le H.1

lemma is_regular.ord_pos {c : cardinal} (H : c.is_regular) : 0 < c.ord :=
by { rw cardinal.lt_ord, exact H.pos }

theorem is_regular_cof {o : ordinal} (h : o.is_limit) : is_regular o.cof :=
⟨aleph_0_le_cof.2 h, (cof_cof o).ge⟩

theorem is_regular_aleph_0 : is_regular ℵ₀ :=
⟨le_rfl, by simp⟩

theorem is_regular_succ {c : cardinal.{u}} (h : ℵ₀ ≤ c) : is_regular (succ c) :=
⟨h.trans (le_succ c), succ_le_of_lt begin
  cases quotient.exists_rep (@succ cardinal _ _ c) with α αe, simp at αe,
  rcases ord_eq α with ⟨r, wo, re⟩, resetI,
  have := ord_is_limit (h.trans (le_succ _)),
  rw [← αe, re] at this ⊢,
  rcases cof_eq' r this with ⟨S, H, Se⟩,
  rw [← Se],
  apply lt_imp_lt_of_le_imp_le (λ h, mul_le_mul_right' h c),
  rw [mul_eq_self h, ← succ_le_iff, ← αe, ← sum_const'],
  refine le_trans _ (sum_le_sum (λ x, card (typein r x)) _ (λ i, _)),
  { simp only [← card_typein, ← mk_sigma],
    exact ⟨embedding.of_surjective (λ x, x.2.1)
      (λ a, let ⟨b, h, ab⟩ := H a in ⟨⟨⟨_, h⟩, _, ab⟩, rfl⟩)⟩ },
  { rw [← lt_succ_iff, ← lt_ord, ← αe, re],
    apply typein_lt_type }
end⟩

theorem is_regular_aleph_one : is_regular (aleph 1) :=
by { rw ←succ_aleph_0, exact is_regular_succ le_rfl }

theorem is_regular_aleph'_succ {o : ordinal} (h : ω ≤ o) : is_regular (aleph' (succ o)) :=
by { rw aleph'_succ, exact is_regular_succ (aleph_0_le_aleph'.2 h) }

theorem is_regular_aleph_succ (o : ordinal) : is_regular (aleph (succ o)) :=
by { rw aleph_succ, exact is_regular_succ (aleph_0_le_aleph o) }

/--
A function whose codomain's cardinality is infinite but strictly smaller than its domain's
has a fiber with cardinality strictly great than the codomain.
-/
theorem infinite_pigeonhole_card_lt {β α : Type u} (f : β → α)
  (w : #α < #β) (w' : ℵ₀ ≤ #α) :
  ∃ a : α, #α < #(f ⁻¹' {a}) :=
begin
  simp_rw [← succ_le_iff],
  exact ordinal.infinite_pigeonhole_card f (succ (#α)) (succ_le_of_lt w)
    (w'.trans (lt_succ _).le)
    ((lt_succ _).trans_le (is_regular_succ w').2.ge),
end

/--
A function whose codomain's cardinality is infinite but strictly smaller than its domain's
has an infinite fiber.
-/
theorem exists_infinite_fiber {β α : Type*} (f : β → α)
  (w : #α < #β) (w' : _root_.infinite α) :
  ∃ a : α, _root_.infinite (f ⁻¹' {a}) :=
begin
  simp_rw [cardinal.infinite_iff] at ⊢ w',
  cases infinite_pigeonhole_card_lt f w w' with a ha,
  exact ⟨a, w'.trans ha.le⟩,
end

/--
If an infinite type `β` can be expressed as a union of finite sets,
then the cardinality of the collection of those finite sets
must be at least the cardinality of `β`.
-/
lemma le_range_of_union_finset_eq_top
  {α β : Type*} [infinite β] (f : α → finset β) (w : (⋃ a, (f a : set β)) = ⊤) :
  #β ≤ #(range f) :=
begin
  have k : _root_.infinite (range f),
  { rw infinite_coe_iff,
    apply mt (union_finset_finite_of_range_finite f),
    rw w,
    exact infinite_univ, },
  by_contradiction h,
  simp only [not_le] at h,
  let u : Π b, ∃ a, b ∈ f a := λ b, by simpa using (w.ge : _) (set.mem_univ b),
  let u' : β → range f := λ b, ⟨f (u b).some, by simp⟩,
  have v' : ∀ a, u' ⁻¹' {⟨f a, by simp⟩} ≤ f a, begin rintros a p m,
    simp at m,
    rw ←m,
    apply (λ b, (u b).some_spec),
  end,
  obtain ⟨⟨-, ⟨a, rfl⟩⟩, p⟩ := exists_infinite_fiber u' h k,
  exact (@infinite.of_injective _ _ p (inclusion (v' a)) (inclusion_injective _)).false,
end

theorem lsub_lt_ord_lift_of_is_regular {ι} {f : ι → ordinal} {c} (hc : is_regular c)
  (hι : cardinal.lift (#ι) < c) : (∀ i, f i < c.ord) → ordinal.lsub f < c.ord :=
lsub_lt_ord_lift (by rwa hc.cof_eq)

theorem lsub_lt_ord_of_is_regular {ι} {f : ι → ordinal} {c} (hc : is_regular c) (hι : #ι < c) :
  (∀ i, f i < c.ord) → ordinal.lsub f < c.ord :=
lsub_lt_ord (by rwa hc.cof_eq)

theorem sup_lt_ord_lift_of_is_regular {ι} {f : ι → ordinal} {c} (hc : is_regular c)
  (hι : cardinal.lift (#ι) < c) : (∀ i, f i < c.ord) → ordinal.sup f < c.ord :=
sup_lt_ord_lift (by rwa hc.cof_eq)

theorem sup_lt_ord_of_is_regular {ι} {f : ι → ordinal} {c} (hc : is_regular c) (hι : #ι < c) :
  (∀ i, f i < c.ord) → ordinal.sup f < c.ord :=
sup_lt_ord (by rwa hc.cof_eq)

theorem blsub_lt_ord_lift_of_is_regular {o : ordinal} {f : Π a < o, ordinal} {c} (hc : is_regular c)
  (ho : cardinal.lift o.card < c) : (∀ i hi, f i hi < c.ord) → ordinal.blsub o f < c.ord :=
blsub_lt_ord_lift (by rwa hc.cof_eq)

theorem blsub_lt_ord_of_is_regular {o : ordinal} {f : Π a < o, ordinal} {c} (hc : is_regular c)
  (ho : o.card < c) : (∀ i hi, f i hi < c.ord) → ordinal.blsub o f < c.ord :=
blsub_lt_ord (by rwa hc.cof_eq)

theorem bsup_lt_ord_lift_of_is_regular {o : ordinal} {f : Π a < o, ordinal} {c} (hc : is_regular c)
  (hι : cardinal.lift o.card < c) : (∀ i hi, f i hi < c.ord) → ordinal.bsup o f < c.ord :=
bsup_lt_ord_lift (by rwa hc.cof_eq)

theorem bsup_lt_ord_of_is_regular {o : ordinal} {f : Π a < o, ordinal} {c} (hc : is_regular c)
  (hι : o.card < c) : (∀ i hi, f i hi < c.ord) → ordinal.bsup o f < c.ord :=
bsup_lt_ord (by rwa hc.cof_eq)

theorem supr_lt_lift_of_is_regular {ι} {f : ι → cardinal} {c} (hc : is_regular c)
  (hι : cardinal.lift (#ι) < c) : (∀ i, f i < c) → supr f < c :=
supr_lt_lift (by rwa hc.cof_eq)

theorem supr_lt_of_is_regular {ι} {f : ι → cardinal} {c} (hc : is_regular c) (hι : #ι < c) :
  (∀ i, f i < c) → supr f < c :=
supr_lt (by rwa hc.cof_eq)

theorem sum_lt_lift_of_is_regular {ι : Type u} {f : ι → cardinal} {c : cardinal} (hc : is_regular c)
  (hι : cardinal.lift.{v u} (#ι) < c) (hf : ∀ i, f i < c) : sum f < c :=
(sum_le_supr_lift _).trans_lt $ mul_lt_of_lt hc.1 hι (supr_lt_lift_of_is_regular hc hι hf)

theorem sum_lt_of_is_regular {ι : Type u} {f : ι → cardinal} {c : cardinal} (hc : is_regular c)
  (hι : #ι < c) : (∀ i, f i < c) → sum f < c :=
sum_lt_lift_of_is_regular.{u u} hc (by rwa lift_id)

theorem nfp_family_lt_ord_lift_of_is_regular {ι} {f : ι → ordinal → ordinal} {c} (hc : is_regular c)
  (hι : (#ι).lift < c) (hc' : c ≠ ℵ₀) (hf : ∀ i (b < c.ord), f i b < c.ord) {a} (ha : a < c.ord) :
  nfp_family.{u v} f a < c.ord :=
by { apply nfp_family_lt_ord_lift _ _ hf ha; rwa hc.cof_eq, exact lt_of_le_of_ne hc.1 hc'.symm }

theorem nfp_family_lt_ord_of_is_regular {ι} {f : ι → ordinal → ordinal} {c} (hc : is_regular c)
  (hι : #ι < c) (hc' : c ≠ ℵ₀) {a} (hf : ∀ i (b < c.ord), f i b < c.ord) :
  a < c.ord → nfp_family.{u u} f a < c.ord :=
nfp_family_lt_ord_lift_of_is_regular hc (by rwa lift_id) hc' hf

theorem nfp_bfamily_lt_ord_lift_of_is_regular {o : ordinal} {f : Π a < o, ordinal → ordinal} {c}
  (hc : is_regular c) (ho : o.card.lift < c) (hc' : c ≠ ℵ₀)
  (hf : ∀ i hi (b < c.ord), f i hi b < c.ord) {a} : a < c.ord → nfp_bfamily.{u v} o f a < c.ord :=
nfp_family_lt_ord_lift_of_is_regular hc (by rwa mk_ordinal_out) hc' (λ i, hf _ _)

theorem nfp_bfamily_lt_ord_of_is_regular {o : ordinal} {f : Π a < o, ordinal → ordinal} {c}
  (hc : is_regular c) (ho : o.card < c) (hc' : c ≠ ℵ₀) (hf : ∀ i hi (b < c.ord), f i hi b < c.ord)
  {a} : a < c.ord → nfp_bfamily.{u u} o f a < c.ord :=
nfp_bfamily_lt_ord_lift_of_is_regular hc (by rwa lift_id) hc' hf

theorem nfp_lt_ord_of_is_regular {f : ordinal → ordinal} {c} (hc : is_regular c) (hc' : c ≠ ℵ₀)
  (hf : ∀ i < c.ord, f i < c.ord) {a} : (a < c.ord) → nfp f a < c.ord :=
nfp_lt_ord (by { rw hc.cof_eq, exact lt_of_le_of_ne hc.1 hc'.symm }) hf

theorem deriv_family_lt_ord_lift {ι} {f : ι → ordinal → ordinal} {c} (hc : is_regular c)
  (hι : (#ι).lift < c) (hc' : c ≠ ℵ₀) (hf : ∀ i (b < c.ord), f i b < c.ord) {a} :
  a < c.ord → deriv_family.{u v} f a < c.ord :=
begin
  have hω : ℵ₀ < c.ord.cof,
  { rw hc.cof_eq, exact lt_of_le_of_ne hc.1 hc'.symm },
  apply a.limit_rec_on,
  { rw deriv_family_zero,
    exact nfp_family_lt_ord_lift hω (by rwa hc.cof_eq) hf },
  { intros b hb hb',
    rw deriv_family_succ,
    exact nfp_family_lt_ord_lift hω (by rwa hc.cof_eq) hf
      ((ord_is_limit hc.1).2 _ (hb ((lt_succ b).trans hb'))) },
  { intros b hb H hb',
    rw deriv_family_limit f hb,
    exact bsup_lt_ord_of_is_regular hc (ord_lt_ord.1 ((ord_card_le b).trans_lt hb'))
      (λ o' ho', H o' ho' (ho'.trans hb')) }
end

theorem deriv_family_lt_ord {ι} {f : ι → ordinal → ordinal} {c} (hc : is_regular c)
  (hι : #ι < c) (hc' : c ≠ ℵ₀) (hf : ∀ i (b < c.ord), f i b < c.ord) {a} :
  a < c.ord → deriv_family.{u u} f a < c.ord :=
deriv_family_lt_ord_lift hc (by rwa lift_id) hc' hf

theorem deriv_bfamily_lt_ord_lift {o : ordinal} {f : Π a < o, ordinal → ordinal} {c}
  (hc : is_regular c) (hι : o.card.lift < c) (hc' : c ≠ ℵ₀)
  (hf : ∀ i hi (b < c.ord), f i hi b < c.ord) {a} :
  a < c.ord → deriv_bfamily.{u v} o f a < c.ord :=
deriv_family_lt_ord_lift hc (by rwa mk_ordinal_out) hc' (λ i, hf _ _)

theorem deriv_bfamily_lt_ord {o : ordinal} {f : Π a < o, ordinal → ordinal} {c} (hc : is_regular c)
  (hι : o.card < c) (hc' : c ≠ ℵ₀) (hf : ∀ i hi (b < c.ord), f i hi b < c.ord)
  {a} : a < c.ord → deriv_bfamily.{u u} o f a < c.ord :=
deriv_bfamily_lt_ord_lift hc (by rwa lift_id) hc' hf

theorem deriv_lt_ord {f : ordinal.{u} → ordinal} {c} (hc : is_regular c) (hc' : c ≠ ℵ₀)
  (hf : ∀ i < c.ord, f i < c.ord) {a} : a < c.ord → deriv f a < c.ord :=
deriv_family_lt_ord_lift hc
  (by simpa using cardinal.one_lt_aleph_0.trans (lt_of_le_of_ne hc.1 hc'.symm))
  hc' (λ _, hf)

/-- A cardinal is inaccessible if it is an uncountable regular strong limit cardinal. -/
def is_inaccessible (c : cardinal) :=
ℵ₀ < c ∧ is_regular c ∧ is_strong_limit c

theorem is_inaccessible.mk {c} (h₁ : ℵ₀ < c) (h₂ : c ≤ c.ord.cof) (h₃ : ∀ x < c, 2 ^ x < c) :
  is_inaccessible c :=
⟨h₁, ⟨h₁.le, h₂⟩, (aleph_0_pos.trans h₁).ne', h₃⟩

/- Lean's foundations prove the existence of ℵ₀ many inaccessible cardinals -/
theorem univ_inaccessible : is_inaccessible (univ.{u v}) :=
is_inaccessible.mk
  (by simpa using lift_lt_univ' ℵ₀)
  (by simp)
  (λ c h, begin
    rcases lt_univ'.1 h with ⟨c, rfl⟩,
    rw ← lift_two_power.{u (max (u+1) v)},
    apply lift_lt_univ'
  end)

theorem lt_power_cof {c : cardinal.{u}} : ℵ₀ ≤ c → c < c ^ cof c.ord :=
quotient.induction_on c $ λ α h, begin
  rcases ord_eq α with ⟨r, wo, re⟩, resetI,
  have := ord_is_limit h,
  rw [mk_def, re] at this ⊢,
  rcases cof_eq' r this with ⟨S, H, Se⟩,
  have := sum_lt_prod (λ a:S, #{x // r x a}) (λ _, #α) (λ i, _),
  { simp only [cardinal.prod_const, cardinal.lift_id, ← Se, ← mk_sigma, power_def] at this ⊢,
    refine lt_of_le_of_lt _ this,
    refine ⟨embedding.of_surjective _ _⟩,
    { exact λ x, x.2.1 },
    { exact λ a, let ⟨b, h, ab⟩ := H a in ⟨⟨⟨_, h⟩, _, ab⟩, rfl⟩ } },
  { have := typein_lt_type r i,
    rwa [← re, lt_ord] at this }
end

theorem lt_cof_power {a b : cardinal} (ha : ℵ₀ ≤ a) (b1 : 1 < b) :
  a < cof (b ^ a).ord :=
begin
  have b0 : b ≠ 0 := (zero_lt_one.trans b1).ne',
  apply lt_imp_lt_of_le_imp_le (power_le_power_left $ power_ne_zero a b0),
  rw [←power_mul, mul_eq_self ha],
  exact lt_power_cof (ha.trans $ (cantor' _ b1).le),
end

end cardinal
