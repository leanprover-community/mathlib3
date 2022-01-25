import set_theory.cardinal_ordinal

noncomputable theory

namespace ordinal

/-- The `Ωᵥ` function as defined by Buchholz. -/
-- Todo: generalize
def Omega : ℕ → ordinal.{0}
| 0       := 1
| (v + 1) := (cardinal.aleph (v + 1)).ord

theorem Omega_pos : Π v, 0 < Omega v
| 0 := zero_lt_one
| (v + 1) := begin
  unfold Omega,
  rw [←cardinal.ord_zero, cardinal.ord_lt_ord],
  exact cardinal.aleph_pos _
end

-- Omega is principal additive

/-- The type of all Buchholz expressions. These may consist of
* ordinals less than `Ωᵥ`
* sums of two other Buchholz expressions
* some function `Ψᵤ` applied to a Buchholz expression -/
inductive buchholz_exp' (v : ℕ) : Type 0
| low' (a : (Omega v).out.α) : buchholz_exp'
| add  (a b : buchholz_exp') : buchholz_exp'
| psi  (u : ℕ) (a : buchholz_exp') : buchholz_exp'

namespace buchholz_exp'

/-- A Buchholz expression from an ordinal less than `Ωᵥ`. -/
def low {v : ℕ} {a : ordinal} (ha : a < Omega v) : buchholz_exp' v :=
buchholz_exp'.low' (enum (Omega v).out.r a (by rwa type_out))

/-- The value of a well-formed Buchholz expression when interpreted as an ordinal. -/
noncomputable def value {o : ordinal} {v : ℕ} (Ψ : Π a, a < o → ℕ → ordinal) :
  buchholz_exp' v → ordinal
| (low' a)  := typein (Omega v).out.r a
| (add a b) := a.value + b.value
| (psi u a) := if ha : a.value < o then Ψ _ ha u else 0

theorem low_value {o : ordinal} {v : ℕ} {a : ordinal} (ha : a < Omega v)
  (Ψ : Π a, a < o → ℕ → ordinal) : (low ha).value Ψ = a :=
typein_enum _ _

theorem zero_value {o : ordinal} (ho : o = 0) {v : ℕ} (Ψ : Π a, a < o → ℕ → ordinal) :
  Π (e : buchholz_exp' v), e.value Ψ < Omega v
| (low' a)  := typein_lt_self _
| (add a b) := sorry
| (psi u a) := begin
  unfold value,
  split_ifs,
  { simp_rw ho at h,
    -- exfalso, ordinal.not_zero_lt,
    sorry },
  exact Omega_pos _
end

/-- A well-formed Buchholz expression is one where `Ψ` is only ever called with arguments with value
less than `o`. -/
def well_formed {o : ordinal} (v : ℕ) (Ψ : Π a, a < o → ℕ → ordinal) : set (buchholz_exp' v)
| (low' a)  := tt
| (add a b) := a.well_formed ∧ b.well_formed
| (psi u a) := a.well_formed ∧ value Ψ a < o

theorem low'_is_well_formed {o : ordinal} (v : ℕ) (Ψ : Π a, a < o → ℕ → ordinal)
  (a : (Omega v).out.α) : low' a ∈ well_formed v Ψ :=
(rfl : well_formed v Ψ (low' a))

theorem low_is_well_formed {o : ordinal} (v : ℕ) (Ψ : Π a, a < o → ℕ → ordinal)
  {a : ordinal} (ha : a < Omega v) : low ha ∈ well_formed v Ψ :=
low'_is_well_formed v Ψ _

end buchholz_exp'

/-- The type of well-formed Buchholz expressions. This corresponds to `C` in Buchholz's original
definition. -/
def buchholz_exp {o : ordinal} (v : ℕ) (Ψ : Π a, a < o → ℕ → ordinal) : Type 0 :=
buchholz_exp'.well_formed v Ψ

namespace buchholz_exp

/-- A well-formed Buchholz expression from an ordinal less than `Ωᵥ`. -/
def low {o : ordinal} {v : ℕ} {a : ordinal} (ha : a < Omega v) (Ψ : Π a, a < o → ℕ → ordinal) :
  buchholz_exp v Ψ :=
⟨buchholz_exp'.low ha, buchholz_exp'.low_is_well_formed v Ψ ha⟩

/-- The value of a well-formed Buchholz expression when interpreted as an ordinal. -/
def value {o : ordinal} {v : ℕ} {Ψ : Π a, a < o → ℕ → ordinal} (a : buchholz_exp v Ψ) : ordinal :=
a.val.value Ψ

theorem low_value {o : ordinal} {v : ℕ} {a : ordinal} (ha : a < Omega v)
  (Ψ : Π a, a < o → ℕ → ordinal) : (low ha Ψ).value = a :=
buchholz_exp'.low_value ha Ψ

theorem zero_value {o : ordinal} (ho : o = 0) {v : ℕ} (Ψ : Π a, a < o → ℕ → ordinal)
  (e : buchholz_exp v Ψ) : e.value < Omega v :=
buchholz_exp'.zero_value ho Ψ _

end buchholz_exp

/-- Buchholz's `Ψ` function. -/
def buchholz : ordinal → ℕ → ordinal.{0} :=
wf.fix $ λ o Ψ v, lsub (@buchholz_exp.value o v Ψ)

theorem buchholz_def' : Π o, buchholz o = λ v, lsub (@buchholz_exp.value o v (λ a _, buchholz a)) :=
wf.fix_eq _

theorem buchholz_def (o : ordinal) (v : ℕ) :
  buchholz o v = lsub (@buchholz_exp.value o v (λ a _, buchholz a)) :=
by rw buchholz_def'

theorem buchholz_zero (v : ℕ) : buchholz 0 v = Omega v :=
begin
  rw buchholz_def,
  apply le_antisymm,
  { rw lsub_le_iff_lt,
    exact buchholz_exp.zero_value rfl _ },
  by_contra' h,
  have h' : (buchholz_exp.low h _).value < lsub buchholz_exp.value := lt_lsub _ _,
  rw buchholz_exp.low_value h _ at h',
  exact lt_irrefl _ h'
end

-- Buchholz is additive principal

theorem buchholz_lt_Omega (o : ordinal) (v : ℕ) : buchholz o v < Omega (v + 1) :=
begin
  apply wf.fix o,
end

end ordinal
