/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import set_theory.ordinal.arithmetic
import topology.order.basic

/-!
### Topology of ordinals

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We prove some miscellaneous results involving the order topology of ordinals.

### Main results

* `ordinal.is_closed_iff_sup` / `ordinal.is_closed_iff_bsup`: A set of ordinals is closed iff it's
  closed under suprema.
* `ordinal.is_normal_iff_strict_mono_and_continuous`: A characterization of normal ordinal
  functions.
* `ordinal.enum_ord_is_normal_iff_is_closed`: The function enumerating the ordinals of a set is
  normal iff the set is closed.
-/

noncomputable theory

universes u v

open cardinal order

namespace ordinal

variables {s : set ordinal.{u}} {a : ordinal.{u}}

instance : topological_space ordinal.{u} :=
preorder.topology ordinal.{u}

instance : order_topology ordinal.{u} :=
⟨rfl⟩

theorem is_open_singleton_iff : is_open ({a} : set ordinal) ↔ ¬ is_limit a :=
begin
  refine ⟨λ h ha, _, λ ha, _⟩,
  { obtain ⟨b, c, hbc, hbc'⟩ := (mem_nhds_iff_exists_Ioo_subset'
      ⟨0, ordinal.pos_iff_ne_zero.2 ha.1⟩ ⟨_, lt_succ a⟩).1 (h.mem_nhds rfl),
    have hba := ha.2 b hbc.1,
    exact hba.ne (hbc' ⟨lt_succ b, hba.trans hbc.2⟩) },
  { rcases zero_or_succ_or_limit a with rfl | ⟨b, hb⟩ | ha',
    { convert is_open_gt' (1 : ordinal),
      ext,
      exact ordinal.lt_one_iff_zero.symm },
    { convert @is_open_Ioo _ _ _ _ b (a + 1),
      ext c,
      refine ⟨λ hc, _, _⟩,
      { rw set.mem_singleton_iff.1 hc,
        refine ⟨_, lt_succ a⟩,
        rw hb,
        exact lt_succ b },
      { rintro ⟨hc, hc'⟩,
        apply le_antisymm (le_of_lt_succ hc'),
        rw hb,
        exact succ_le_of_lt hc } },
    { exact (ha ha').elim } }
end

theorem is_open_iff : is_open s ↔ ∀ o ∈ s, is_limit o → ∃ a < o, set.Ioo a o ⊆ s :=
begin
  classical,
  refine ⟨_, λ h, _⟩,
  { rw is_open_iff_generate_intervals,
    intros h o hos ho,
    have ho₀ := ordinal.pos_iff_ne_zero.2 ho.1,
    induction h with t ht t u ht hu ht' hu' t ht H,
    { rcases ht with ⟨a, rfl | rfl⟩,
      { exact ⟨a, hos, λ b hb, hb.1⟩ },
      { exact ⟨0, ho₀, λ b hb, hb.2.trans hos⟩ } },
    { exact ⟨0, ho₀, λ b _, set.mem_univ b⟩ },
    { rcases ht' hos.1 with ⟨a, ha, ha'⟩,
      rcases hu' hos.2 with ⟨b, hb, hb'⟩,
      exact ⟨_, max_lt ha hb, λ c hc, ⟨
        ha' ⟨(le_max_left a b).trans_lt hc.1, hc.2⟩,
        hb' ⟨(le_max_right a b).trans_lt hc.1, hc.2⟩⟩⟩ },
    { rcases hos with ⟨u, hu, hu'⟩,
      rcases H u hu hu' with ⟨a, ha, ha'⟩,
      exact ⟨a, ha, λ b hb, ⟨u, hu, ha' hb⟩⟩ } },
  { let f : s → set ordinal := λ o,
      if ho : is_limit o.val
      then set.Ioo (classical.some (h o.val o.prop ho)) (o + 1)
      else {o.val},
    have : ∀ a, is_open (f a) := λ a, begin
      change is_open (dite _ _ _),
      split_ifs,
      { exact is_open_Ioo },
      { rwa is_open_singleton_iff }
    end,
    convert is_open_Union this,
    ext o,
    refine ⟨λ ho, set.mem_Union.2 ⟨⟨o, ho⟩, _⟩, _⟩,
    { split_ifs with ho',
      { refine ⟨_, lt_succ o⟩,
        cases classical.some_spec (h o ho ho') with H,
        exact H },
      { exact set.mem_singleton o } },
    { rintro ⟨t, ⟨a, ht⟩, hoa⟩,
      change dite _ _ _ = t at ht,
      split_ifs at ht with ha;
      subst ht,
      { cases classical.some_spec (h a.val a.prop ha) with H has,
        rcases lt_or_eq_of_le (le_of_lt_succ hoa.2) with hoa' | rfl,
        { exact has ⟨hoa.1, hoa'⟩ },
        { exact a.prop } },
      { convert a.prop } } }
end

theorem mem_closure_iff_sup : a ∈ closure s ↔ ∃ {ι : Type u} [nonempty ι] (f : ι → ordinal),
  (∀ i, f i ∈ s) ∧ sup.{u u} f = a :=
begin
  refine mem_closure_iff.trans ⟨λ h, _, _⟩,
  { by_cases has : a ∈ s,
    { exact ⟨punit, by apply_instance, λ _, a, λ _, has, sup_const a⟩ },
    { have H := λ b (hba : b < a), h _ (@is_open_Ioo _ _ _ _ b (a + 1)) ⟨hba, lt_succ a⟩,
      let f : a.out.α → ordinal := λ i, classical.some (H (typein (<) i) (typein_lt_self i)),
      have hf : ∀ i, f i ∈ set.Ioo (typein (<) i) (a + 1) ∩ s :=
        λ i, classical.some_spec (H _ _),
      rcases eq_zero_or_pos a with rfl | ha₀,
      { rcases h _ (is_open_singleton_iff.2 not_zero_is_limit) rfl with ⟨b, hb, hb'⟩,
        rw set.mem_singleton_iff.1 hb at *,
        exact (has hb').elim },
      refine ⟨_, out_nonempty_iff_ne_zero.2 (ordinal.pos_iff_ne_zero.1 ha₀), f,
        λ i, (hf i).2, le_antisymm (sup_le (λ i, le_of_lt_succ (hf i).1.2)) _⟩,
      by_contra' h,
      cases H _ h with b hb,
      rcases eq_or_lt_of_le (le_of_lt_succ hb.1.2) with rfl | hba,
      { exact has hb.2 },
      { have : b < f (enum (<) b (by rwa type_lt)) := begin
          have := (hf (enum (<) b (by rwa type_lt))).1.1,
          rwa typein_enum at this
        end,
        have : b ≤ sup.{u u} f := this.le.trans (le_sup f _),
        exact this.not_lt hb.1.1 } } },
  { rintro ⟨ι, ⟨i⟩, f, hf, rfl⟩ t ht hat,
    cases eq_zero_or_pos (sup.{u u} f) with ha₀ ha₀,
    { rw ha₀ at hat,
      use [0, hat],
      convert hf i,
      exact (sup_eq_zero_iff.1 ha₀ i).symm },
    rcases (mem_nhds_iff_exists_Ioo_subset' ⟨0, ha₀⟩ ⟨_, lt_succ _⟩).1 (ht.mem_nhds hat) with
      ⟨b, c, ⟨hab, hac⟩, hbct⟩,
    cases lt_sup.1 hab with i hi,
    exact ⟨_, hbct ⟨hi, (le_sup.{u u} f i).trans_lt hac⟩, hf i⟩ }
end

theorem mem_closed_iff_sup (hs : is_closed s) :
  a ∈ s ↔ ∃ {ι : Type u} (hι : nonempty ι) (f : ι → ordinal),
  (∀ i, f i ∈ s) ∧ sup.{u u} f = a :=
by rw [←mem_closure_iff_sup, hs.closure_eq]

theorem mem_closure_iff_bsup :
  a ∈ closure s ↔ ∃ {o : ordinal} (ho : o ≠ 0) (f : Π a < o, ordinal),
  (∀ i hi, f i hi ∈ s) ∧ bsup.{u u} o f = a :=
mem_closure_iff_sup.trans ⟨
  λ ⟨ι, ⟨i⟩, f, hf, ha⟩, ⟨_, λ h, (type_eq_zero_iff_is_empty.1 h).elim i, bfamily_of_family f,
    λ i hi, hf _, by rwa bsup_eq_sup⟩,
  λ ⟨o, ho, f, hf, ha⟩, ⟨_, out_nonempty_iff_ne_zero.2 ho, family_of_bfamily o f,
    λ i, hf _ _, by rwa sup_eq_bsup⟩⟩

theorem mem_closed_iff_bsup (hs : is_closed s) :
  a ∈ s ↔ ∃ {o : ordinal} (ho : o ≠ 0) (f : Π a < o, ordinal),
  (∀ i hi, f i hi ∈ s) ∧ bsup.{u u} o f = a :=
by rw [←mem_closure_iff_bsup, hs.closure_eq]

theorem is_closed_iff_sup :
  is_closed s ↔ ∀ {ι : Type u} (hι : nonempty ι) (f : ι → ordinal),
  (∀ i, f i ∈ s) → sup.{u u} f ∈ s :=
begin
  use λ hs ι hι f hf, (mem_closed_iff_sup hs).2 ⟨ι, hι, f, hf, rfl⟩,
  rw ←closure_subset_iff_is_closed,
  intros h x hx,
  rcases mem_closure_iff_sup.1 hx with ⟨ι, hι, f, hf, rfl⟩,
  exact h hι f hf
end

theorem is_closed_iff_bsup :
  is_closed s ↔ ∀ {o : ordinal} (ho : o ≠ 0) (f : Π a < o, ordinal),
  (∀ i hi, f i hi ∈ s) → bsup.{u u} o f ∈ s :=
begin
  rw is_closed_iff_sup,
  refine ⟨λ H o ho f hf, H (out_nonempty_iff_ne_zero.2 ho) _ _, λ  H ι hι f hf, _⟩,
  { exact λ i, hf _ _ },
  { rw ←bsup_eq_sup,
    apply H (type_ne_zero_iff_nonempty.2 hι),
    exact λ i hi, hf _ }
end

theorem is_limit_of_mem_frontier (ha : a ∈ frontier s) : is_limit a :=
begin
  simp only [frontier_eq_closure_inter_closure, set.mem_inter_iff, mem_closure_iff] at ha,
  by_contra h,
  rw ←is_open_singleton_iff at h,
  rcases ha.1 _ h rfl with ⟨b, hb, hb'⟩,
  rcases ha.2 _ h rfl with ⟨c, hc, hc'⟩,
  rw set.mem_singleton_iff at *,
  subst hb, subst hc,
  exact hc' hb'
end

theorem is_normal_iff_strict_mono_and_continuous (f : ordinal.{u} → ordinal.{u}) :
  is_normal f ↔ strict_mono f ∧ continuous f :=
begin
  refine ⟨λ h, ⟨h.strict_mono, _⟩, _⟩,
  { rw continuous_def,
    intros s hs,
    rw is_open_iff at *,
    intros o ho ho',
    rcases hs _ ho (h.is_limit ho') with ⟨a, ha, has⟩,
    rw [←is_normal.bsup_eq.{u u} h ho', lt_bsup] at ha,
    rcases ha with ⟨b, hb, hab⟩,
    exact ⟨b, hb, λ c hc,
      set.mem_preimage.2 (has ⟨hab.trans (h.strict_mono hc.1), h.strict_mono hc.2⟩)⟩ },
  { rw is_normal_iff_strict_mono_limit,
    rintro ⟨h, h'⟩,
    refine ⟨h, λ o ho a h, _⟩,
    suffices : o ∈ (f ⁻¹' set.Iic a), from set.mem_preimage.1 this,
    rw mem_closed_iff_sup (is_closed.preimage h' (@is_closed_Iic _ _ _ _  a)),
    exact ⟨_, out_nonempty_iff_ne_zero.2 ho.1, typein (<),
      λ i, h _ (typein_lt_self i), sup_typein_limit ho.2⟩ }
end

theorem enum_ord_is_normal_iff_is_closed (hs : s.unbounded (<)) :
  is_normal (enum_ord s) ↔ is_closed s :=
begin
  have Hs := enum_ord_strict_mono hs,
  refine ⟨λ h, is_closed_iff_sup.2 (λ ι hι f hf, _),
    λ h, (is_normal_iff_strict_mono_limit _).2 ⟨Hs, λ a ha o H, _⟩⟩,
  { let g : ι → ordinal.{u} := λ i, (enum_ord_order_iso hs).symm ⟨_, hf i⟩,
    suffices : enum_ord s (sup.{u u} g) = sup.{u u} f,
    { rw ←this, exact enum_ord_mem hs _ },
    rw @is_normal.sup.{u u u} _ h ι g hι,
    congr, ext,
    change ((enum_ord_order_iso hs) _).val = f x,
    rw order_iso.apply_symm_apply },
  { rw is_closed_iff_bsup at h,
    suffices : enum_ord s a ≤ bsup.{u u} a (λ b < a, enum_ord s b), from this.trans (bsup_le H),
    cases enum_ord_surjective hs _ (h ha.1 (λ b hb, enum_ord s b) (λ b hb, enum_ord_mem hs b))
      with b hb,
    rw ←hb,
    apply Hs.monotone,
    by_contra' hba,
    apply (Hs (lt_succ b)).not_le,
    rw hb,
    exact le_bsup.{u u} _ _ (ha.2 _ hba) }
end

end ordinal
