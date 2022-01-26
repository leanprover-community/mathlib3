import set_theory.cardinal_ordinal

universes u v
noncomputable theory

-- This should go on another PR.

namespace ordinal

/-- The minimum excluded ordinal in a family of ordinals. -/
def mex {ι} (f : ι → ordinal) : ordinal :=
omin (set.range f)ᶜ ⟨_, lsub_nmem_range f⟩

theorem mex_le_of_nmem {ι} {f : ι → ordinal} {a} (ha : ∀ i, f i ≠ a) : mex f ≤ a :=
by { apply omin_le, simp [ha] }

theorem mem_of_lt_mex {ι} {f : ι → ordinal} {a} (ha : a < mex f) : ∃ i, f i = a :=
by { by_contra' ha', exact not_le_of_lt ha (mex_le_of_nmem ha') }

theorem mex_le_lsub {ι} (f : ι → ordinal) : mex f ≤ lsub f :=
omin_le (lsub_nmem_range f)

theorem mex_lt_card_succ {ι} (f : ι → ordinal) : mex f < (cardinal.mk ι).succ.ord :=
begin
  by_contra' h,
  apply not_le_of_lt (cardinal.lt_succ_self (cardinal.mk ι)),
  let g : (cardinal.mk ι).succ.ord.out.α → ι :=
    λ a, classical.some (mem_of_lt_mex ((typein_lt_self a).trans_le h)),
  have hg : function.injective g := begin
    intros a b h',
    have H : ∀ x, f (g x) = typein _ x :=
      λ x, classical.some_spec (mem_of_lt_mex ((typein_lt_self x).trans_le h)),
    apply_fun f at h',
    rwa [H, H, typein_inj] at h'
  end,
  convert cardinal.mk_le_of_injective hg,
  rw cardinal.mk_ord_out
end

end ordinal

open cardinal
namespace ordinal

/-- The `Ωᵥ` function as defined by Buchholz. -/
-- Todo: generalize
def Omega : ℕ → cardinal.{0}
| 0       := 1
| (v + 1) := aleph (v + 1)

theorem Omega_pos : Π v, 0 < Omega v
| 0       := cardinal.zero_lt_one
| (v + 1) := aleph_pos _

-- Omega is principal additive

/-- The type of all Buchholz expressions. These may consist of
* ordinals less than `Ωᵥ`
* sums of two other Buchholz expressions
* some function `Ψᵤ` applied to a Buchholz expression -/
inductive buchholz_exp' (v : ℕ) : Type 0
| lt_Omega' (a : (Omega v).ord.out.α) : buchholz_exp'
| add       (a b : buchholz_exp') : buchholz_exp'
| psi       (u : ℕ) (a : buchholz_exp') : buchholz_exp'

namespace buchholz_exp'

/-- A Buchholz expression from an ordinal less than `Ωᵥ`. -/
def lt_Omega {v : ℕ} {a : ordinal} (ha : a < (Omega v).ord) : buchholz_exp' v :=
buchholz_exp'.lt_Omega' (enum (Omega v).ord.out.r a (by rwa type_out))

instance (v : ℕ) : has_zero (buchholz_exp' v) :=
⟨lt_Omega (ord_lt_ord.2 (Omega_pos v))⟩

/-- The value of a well-formed Buchholz expression when interpreted as an ordinal. -/
noncomputable def value {o : ordinal} {v : ℕ} (Ψ : Π a, a < o → ℕ → ordinal) :
  buchholz_exp' v → ordinal
| (lt_Omega' a)  := typein (Omega v).ord.out.r a
| (add a b)      := a.value + b.value
| (psi u a)      := if ha : a.value < o then Ψ _ ha u else 0

theorem lt_Omega_value {o : ordinal} {v : ℕ} {a : ordinal} (ha : a < (Omega v).ord)
  (Ψ : Π a, a < o → ℕ → ordinal) : (lt_Omega ha).value Ψ = a :=
typein_enum _ _

theorem zero_value {o : ordinal} (ho : o = 0) {v : ℕ} (Ψ : Π a, a < o → ℕ → ordinal) :
  Π (e : buchholz_exp' v), e.value Ψ < (Omega v).ord
| (lt_Omega' a)  := typein_lt_self _
| (add a b)      := sorry
| (psi u a)      := begin
  unfold value,
  split_ifs,
  { simp_rw ho at h,
    -- exfalso, ordinal.not_zero_lt,
    sorry },
  rw ←ord_zero,
  exact ord_lt_ord.2 (Omega_pos v)
end

/-- The height of a Buchholz expression, thought of as a syntax tree. -/
noncomputable def height {v : ℕ} : buchholz_exp' v → ℕ
| (lt_Omega' a) := 0
| (add a b)     := max (height a) (height b) + 1
| (psi u a)     := height a + 1

theorem lt_Omega'_of_height {v : ℕ} {e : buchholz_exp' v} (he : height e = 0) :
  ∃ a, e = lt_Omega' a :=
begin
  induction e with a,
  use a,
  all_goals { simpa only [height] }
end

/-- A denumerable family of Buchholz expressions. -/
private def add_iterate (n : ℕ) : buchholz_exp' 0 :=
(add (psi 0 0))^[n] 0

private theorem add_iterate.inj : function.injective add_iterate :=
begin
  intros m n h,
  induction m with m hm generalizing n; cases n,
  all_goals { simp only [add_iterate, function.iterate_succ'] at h },
  any_goals { cases h },
  rw hm (add.inj h).right
end

theorem aleph_le_card (v : ℕ) : aleph v ≤ mk (buchholz_exp' v) :=
begin
  induction v with v hv,
  { convert cardinal.mk_le_of_injective add_iterate.inj, simp },
  { convert cardinal.mk_le_of_injective (@lt_Omega'.inj (v + 1)),
    exact (cardinal.mk_ord_out _).symm }
end

private theorem card_of_height (v : ℕ) : Π h, mk {e : buchholz_exp' v | e.height = h} ≤ Omega v
| 0 := begin
  let f : ↥{e : buchholz_exp' v | e.height = 0} → (Omega v).ord.out.α :=
    λ e, classical.some (lt_Omega'_of_height e.prop),
  have hf : function.injective f := begin
    intros e₁ e₂ h,
    apply_fun lt_Omega' at h,
    have H := λ e : ↥{e : buchholz_exp' v | e.height = 0},
      classical.some_spec (lt_Omega'_of_height e.prop),
    rwa [←H, ←H, ←subtype.ext_iff] at h
  end,
  convert cardinal.mk_le_of_injective hf,
  exact (cardinal.mk_ord_out _).symm
end
| (h + 1) := begin
  sorry
end

private theorem card_eq_Union_height (v : ℕ) :
  mk (buchholz_exp' v) = mk (⋃ h, {e : buchholz_exp' v | e.height = h}) :=
begin
  let f : buchholz_exp' v → ⋃ h, {e : buchholz_exp' v | e.height = h} :=
    λ e', ⟨e', by { rw set.mem_Union, exact ⟨e'.height, rfl⟩ }⟩,
  refine le_antisymm
    (@mk_le_of_injective _ _ f (λ e₁ e₂ h, _))
    (@mk_le_of_surjective _ _ f (λ a, ⟨a, _⟩)),
  { simp only [subtype.mk_eq_mk] at h, exact h },
  { simp only [f, subtype.coe_eta] }
end

theorem card_eq_aleph (v : ℕ) : mk (buchholz_exp' v) = cardinal.aleph v :=
begin
  apply le_antisymm,
  { sorry },
  { induction v with v hv,
    { convert cardinal.mk_le_of_injective add_iterate.inj, simp },
    { convert cardinal.mk_le_of_injective (@lt_Omega'.inj (v + 1)),
      exact (cardinal.mk_ord_out _).symm } }
end

/-- A well-formed Buchholz expression is one where `Ψ` is only ever called with arguments with value
less than `o`. -/
def well_formed {o : ordinal} (v : ℕ) (Ψ : Π a, a < o → ℕ → ordinal) : set (buchholz_exp' v)
| (lt_Omega' a)  := tt
| (add a b)      := a.well_formed ∧ b.well_formed
| (psi u a)      := a.well_formed ∧ a.value Ψ < o

theorem lt_Omega'_is_well_formed {o : ordinal} (v : ℕ) (Ψ : Π a, a < o → ℕ → ordinal)
  (a : (Omega v).out.α) : lt_Omega' a ∈ well_formed v Ψ :=
(rfl : well_formed v Ψ (lt_Omega' a))

theorem lt_Omega_is_well_formed {o : ordinal} (v : ℕ) (Ψ : Π a, a < o → ℕ → ordinal)
  {a : ordinal} (ha : a < Omega v) : lt_Omega ha ∈ well_formed v Ψ :=
lt_Omega'_is_well_formed v Ψ _

end buchholz_exp'

/-- The type of well-formed Buchholz expressions. This corresponds to `C` in Buchholz's original
definition. -/
def buchholz_exp {o : ordinal} (v : ℕ) (Ψ : Π a, a < o → ℕ → ordinal) : Type 0 :=
buchholz_exp'.well_formed v Ψ

namespace buchholz_exp

/-- A well-formed Buchholz expression from an ordinal less than `Ωᵥ`. -/
def lt_Omega {o : ordinal} {v : ℕ} {a : ordinal} (ha : a < Omega v) (Ψ : Π a, a < o → ℕ → ordinal) :
  buchholz_exp v Ψ :=
⟨buchholz_exp'.lt_Omega ha, buchholz_exp'.lt_Omega_is_well_formed v Ψ ha⟩

/-- The value of a well-formed Buchholz expression when interpreted as an ordinal. -/
def value {o : ordinal} {v : ℕ} {Ψ : Π a, a < o → ℕ → ordinal} (a : buchholz_exp v Ψ) : ordinal :=
a.val.value Ψ

theorem low_value {o : ordinal} {v : ℕ} {a : ordinal} (ha : a < Omega v)
  (Ψ : Π a, a < o → ℕ → ordinal) : (lt_Omega ha Ψ).value = a :=
buchholz_exp'.lt_Omega_value ha Ψ

theorem zero_value {o : ordinal} (ho : o = 0) {v : ℕ} (Ψ : Π a, a < o → ℕ → ordinal)
  (e : buchholz_exp v Ψ) : e.value < Omega v :=
buchholz_exp'.zero_value ho Ψ _

end buchholz_exp

/-- Buchholz's `Ψ` function. -/
def buchholz : ordinal → ℕ → ordinal.{0} :=
wf.fix $ λ o Ψ v, mex (@buchholz_exp.value o v Ψ)

theorem buchholz_def' : Π o, buchholz o = λ v, mex (@buchholz_exp.value o v (λ a _, buchholz a)) :=
wf.fix_eq _

theorem buchholz_def (o : ordinal) (v : ℕ) :
  buchholz o v = mex (@buchholz_exp.value o v (λ a _, buchholz a)) :=
by rw buchholz_def'

theorem buchholz_zero (v : ℕ) : buchholz 0 v = Omega v :=
begin
  rw buchholz_def,
  apply le_antisymm ((mex_le_lsub _).trans (lsub_le.2 (buchholz_exp.zero_value rfl _))),
  by_contra' h,
  have h' : (buchholz_exp.lt_Omega h _).value < lsub buchholz_exp.value := lt_lsub _ _,
  rw buchholz_exp.low_value h _ at h',
  exact lt_irrefl _ h'
end

-- Buchholz is additive principal

theorem buchholz_lt_Omega (o : ordinal) (v : ℕ) : buchholz o v < Omega (v + 1) :=
begin
  apply wf.fix o,
end

end ordinal
