/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import set_theory.ordinal_arithmetic
import topology.algebra.ordered.basic

noncomputable theory

universes u v

namespace ordinal

instance : topological_space ordinal.{u} :=
preorder.topology ordinal.{u}

instance : order_topology ordinal.{u} :=
⟨rfl⟩

theorem is_open_singleton_iff {o : ordinal} : is_open ({o} : set ordinal) ↔ ¬ is_limit o :=
begin
  refine ⟨λ h ho, _, λ ho, _⟩,
  { obtain ⟨a, b, hab, hab'⟩ := (mem_nhds_iff_exists_Ioo_subset'
      ⟨0, ordinal.pos_iff_ne_zero.2 ho.1⟩ ⟨_, lt_succ_self o⟩).1 (h.mem_nhds rfl),
    have hao := ho.2 a hab.1,
    exact hao.ne (hab' ⟨lt_succ_self a, hao.trans hab.2⟩) },
  { rcases zero_or_succ_or_limit o with rfl | ⟨a, ha⟩ | ho',
    { convert is_open_gt' (1 : ordinal),
      ext,
      exact ordinal.lt_one_iff.symm },
    { convert @is_open_Ioo _ _ _ _ a (o + 1),
      ext b,
      refine ⟨λ hb, _, _⟩,
      { rw set.mem_singleton_iff.1 hb,
        refine ⟨_, lt_succ_self o⟩,
        rw ha,
        exact lt_succ_self a },
      { rintro ⟨hb, hb'⟩,
        apply le_antisymm (lt_succ.1 hb'),
        rw ha,
        exact ordinal.succ_le.2 hb } },
    { exact (ho ho').elim } }
end

theorem is_open_iff (s : set ordinal) :
  is_open s ↔ (∀ o ∈ s, is_limit o → ∃ a < o, set.Ioo a o ⊆ s) :=
begin
  classical,
  refine ⟨_, λ h, _⟩, {
    rw is_open_iff_generate_intervals,
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
      { refine ⟨_, lt_succ_self o⟩,
        cases classical.some_spec (h o ho ho') with H,
        exact H },
      { exact set.mem_singleton o } },
    { rintro ⟨t, ⟨a, ht⟩, hoa⟩,
      change dite _ _ _ = t at ht,
      split_ifs at ht with ha;
      subst ht,
      { cases classical.some_spec (h a.val a.prop ha) with H has,
        rcases lt_or_eq_of_le (lt_succ.1 hoa.2) with hoa' | rfl,
        { exact has ⟨hoa.1, hoa'⟩ },
        { exact a.prop } },
      { convert a.prop } } }
end

theorem mem_closure_iff_sup {s : set ordinal.{u}} {a : ordinal.{u}} :
  a ∈ closure s ↔ ∃ {ι : Type u} [nonempty ι] (f : ι → ordinal.{u}),
  (∀ i, f i ∈ s) ∧ sup.{u u} f = a :=
begin
  refine mem_closure_iff.trans ⟨λ h, _, _⟩,
  { by_cases has : a ∈ s,
    { exact ⟨punit, by apply_instance, λ _, a, λ _, has, sup_const a⟩ },
    { have H := λ b (hba : b < a), h _ (@is_open_Ioo _ _ _ _ b (a + 1)) ⟨hba, lt_succ_self a⟩,
      let f : a.out.α → ordinal := λ i, classical.some (H (typein a.out.r i) (typein_lt_self i)),
      have hf : ∀ i, f i ∈ set.Ioo (typein a.out.r i) (a + 1) ∩ s :=
        λ i, classical.some_spec (H _ _),
      rcases eq_zero_or_pos a with rfl | ha₀,
      { rcases h _ (is_open_singleton_iff.2 not_zero_is_limit) rfl with ⟨b, hb, hb'⟩,
        rw set.mem_singleton_iff.1 hb at *,
        exact (has hb').elim },
      refine ⟨_, out_nonempty_iff_ne_zero.2 (ordinal.pos_iff_ne_zero.1 ha₀), f,
        λ i, (hf i).2, le_antisymm (sup_le.2 (λ i, lt_succ.1 (hf i).1.2)) _⟩,
      by_contra' h,
      cases H _ h with b hb,
      rcases eq_or_lt_of_le (lt_succ.1 hb.1.2) with rfl | hba,
      { exact has hb.2 },
      { have : b < f (enum a.out.r b (by rwa type_out)) := begin
          have := (hf (enum a.out.r b (by rwa type_out))).1.1,
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
    rcases (mem_nhds_iff_exists_Ioo_subset' ⟨0, ha₀⟩ ⟨_, lt_succ_self _⟩).1 (ht.mem_nhds hat) with
      ⟨b, c, habc, hbct⟩,
    have := habc.1,
    cases lt_sup.1 this with i hi,
    exact ⟨_, hbct ⟨hi, (le_sup.{u u} f i).trans_lt habc.2⟩, hf i⟩ }
end

theorem mem_closed_iff_sup {s : set ordinal.{u}} {a : ordinal.{u}} (hs : is_closed s) :
  a ∈ s ↔ ∃ {ι : Type u} [nonempty ι] (f : ι → ordinal.{u}),
  (∀ i, f i ∈ s) ∧ sup.{u u} f = a :=
by rw [←mem_closure_iff_sup, hs.closure_eq]

theorem mem_closure_iff_bsup {s : set ordinal.{u}} {a : ordinal.{u}} :
  a ∈ closure s ↔ ∃ {o : ordinal} (ho : o ≠ 0) (f : Π a < o, ordinal.{u}),
  (∀ i hi, f i hi ∈ s) ∧ bsup.{u u} o f = a :=
mem_closure_iff_sup.trans ⟨
  λ ⟨ι, ⟨i⟩, f, hf, ha⟩, ⟨_, λ h, (type_eq_zero_iff_is_empty.1 h).elim i, bfamily_of_family f,
    λ i hi, hf _, by rwa ←sup_eq_bsup⟩,
  λ ⟨o, ho, f, hf, ha⟩, ⟨_, out_nonempty_iff_ne_zero.2 ho, family_of_bfamily o f,
    λ i, hf _ _, by rwa ←bsup_eq_sup⟩⟩

theorem mem_closed_iff_bsup {s : set ordinal.{u}} {a : ordinal.{u}} (hs : is_closed s) :
  a ∈ s ↔ ∃ {o : ordinal} (ho : o ≠ 0) (f : Π a < o, ordinal.{u}),
  (∀ i hi, f i hi ∈ s) ∧ bsup.{u u} o f = a :=
by rw [←mem_closure_iff_bsup, hs.closure_eq]

theorem is_limit_of_mem_frontier {s : set ordinal} {o : ordinal} (ho : o ∈ frontier s) :
  is_limit o :=
begin
  simp only [frontier_eq_closure_inter_closure, set.mem_inter_iff, mem_closure_iff] at ho,
  by_contra h,
  rw ←is_open_singleton_iff at h,
  rcases ho.1 _ h rfl with ⟨a, ha, ha'⟩,
  rcases ho.2 _ h rfl with ⟨b, hb, hb'⟩,
  rw set.mem_singleton_iff at *,
  subst ha, subst hb,
  exact hb' ha'
end

theorem is_normal_iff_strict_mono_and_continuous (f : ordinal.{u} → ordinal.{u}) :
  is_normal f ↔ (strict_mono f ∧ continuous f) :=
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
  { rintro ⟨h, h'⟩,
    refine ⟨λ o, h (lt_succ_self o), λ o ho a, ⟨λ ha b hb, (h hb).le.trans ha, λ h, _⟩⟩,
    suffices : o ∈ (f ⁻¹' set.Iic a), from set.mem_preimage.1 this,
    rw mem_closed_iff_sup (is_closed.preimage h' (@is_closed_Iic _ _ _ _  a)),
    exact ⟨_, out_nonempty_iff_ne_zero.2 ho.1, typein o.out.r,
      λ i, h _ (typein_lt_self i), sup_typein_limit ho.2⟩ }
end

end ordinal
