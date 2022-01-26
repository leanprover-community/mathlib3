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

theorem Omega_le_aleph : Π v, Omega v ≤ aleph v
| 0       := by { convert le_of_lt cardinal.one_lt_omega, exact aleph_zero }
| (v + 1) := le_of_eq rfl

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

theorem lt_Omega'_value {o : ordinal} {v : ℕ} (Ψ : Π a, a < o → ℕ → ordinal)
  (a : (Omega v).ord.out.α) : (lt_Omega' a).value Ψ = typein (Omega v).ord.out.r a :=
rfl

theorem lt_Omega_value {o : ordinal} {v : ℕ} (Ψ : Π a, a < o → ℕ → ordinal) {a : ordinal}
  (ha : a < (Omega v).ord) : (lt_Omega ha).value Ψ = a :=
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

theorem lt_Omega'_height {v : ℕ} (a) : height (@lt_Omega' v a) = 0 :=
rfl

theorem lt_Omega'_of_height {v : ℕ} {e : buchholz_exp' v} (he : height e = 0) :
  ∃ a, e = lt_Omega' a :=
begin
  induction e with a,
  use a,
  all_goals { simpa only [height] }
end

theorem add_or_psi_of_height {v : ℕ} {e : buchholz_exp' v} (he : 0 < height e) :
  (∃ a b, e = add a b) ∨ (∃ u a, e = psi u a) :=
begin
  induction e with _ a b _ u a,
  { rw lt_Omega'_height at he,
    exact (lt_irrefl 0 he).elim },
  { use [a, b] },
  { use [u, a] },
end

/-- An auxiliary definition which gives a denumerable family of well-formed Buchholz expressions. -/
def add_iterate (n : ℕ) : buchholz_exp' 0 :=
(add 0)^[n] 0

theorem add_iterate_succ (n : ℕ) : add_iterate n.succ = (add 0) ((add 0)^[n] 0) :=
by { unfold add_iterate, rw function.iterate_succ_apply' }

theorem add_iterate.inj : function.injective add_iterate :=
begin
  intros m n h,
  induction m with m hm generalizing n; cases n,
  all_goals { simp only [add_iterate, function.iterate_succ'] at h },
  any_goals { cases h },
  rw hm (add.inj h).right
end

private theorem card_of_height (v : ℕ) : Π h, mk {e : buchholz_exp' v | e.height = h} ≤ aleph v
| 0 := begin
  refine le_trans _ (Omega_le_aleph v),
  let f : ↥{e : buchholz_exp' v | e.height = 0} → (Omega v).ord.out.α :=
    λ e, classical.some (lt_Omega'_of_height e.prop),
  have hf : function.injective f := begin
    intros e₁ e₂ h,
    apply_fun lt_Omega' at h,
    have H := λ e : ↥{e : buchholz_exp' v | e.height = 0},
      classical.some_spec (lt_Omega'_of_height e.prop),
    rwa [←H, ←H, ←subtype.ext_iff] at h
  end,
  convert mk_le_of_injective hf,
  exact (mk_ord_out _).symm
end
| (h + 1) := begin
  let α : Type := {e : buchholz_exp' v | e.height = h},
  have hα : mk α ≤ aleph v := card_of_height h,
  let f : ↥{e : buchholz_exp' v | e.height = h + 1} → (α × α) ⊕ α :=
    λ e, begin
      cases e.val,
      sorry
    end,
  have hf : function.injective f := sorry,
  apply le_trans (mk_le_of_injective hf),
  simp,
  convert cardinal.add_le_add (mul_le_mul' hα hα) hα,
  rw [cardinal.mul_eq_self (omega_le_aleph v), cardinal.add_eq_self (omega_le_aleph v)]
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
  { rw card_eq_Union_height,
    apply le_trans (mk_Union_le _) _,
    rw [mk_nat],
    refine le_trans (mul_le_max _ _) (max_le (max_le (omega_le_aleph v) _) (omega_le_aleph v)),
    { rw cardinal.sup_le,
      exact λ h, le_trans (card_of_height v h) (Omega_le_aleph v) } },
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

theorem lt_Omega'_well_formed {o : ordinal} (v : ℕ) (Ψ : Π a, a < o → ℕ → ordinal)
  (a : (Omega v).ord.out.α) : lt_Omega' a ∈ well_formed v Ψ :=
(rfl : well_formed v Ψ (lt_Omega' a))

theorem lt_Omega_well_formed {o : ordinal} (v : ℕ) (Ψ : Π a, a < o → ℕ → ordinal)
  {a : ordinal} (ha : a < (Omega v).ord) : lt_Omega ha ∈ well_formed v Ψ :=
lt_Omega'_well_formed v Ψ _

theorem zero_well_formed {o : ordinal} (v : ℕ) (Ψ : Π a, a < o → ℕ → ordinal) :
  (0 : buchholz_exp' v) ∈ well_formed v Ψ :=
lt_Omega_well_formed v Ψ _

theorem add_well_formed {o : ordinal} (v : ℕ) (Ψ : Π a, a < o → ℕ → ordinal) {e₁ e₂}
  (he₁ : e₁ ∈ well_formed v Ψ) (he₂ : e₂ ∈ well_formed v Ψ) : add e₁ e₂ ∈ well_formed v Ψ :=
by split; assumption

theorem add_iterate_well_formed {o : ordinal} (Ψ : Π a, a < o → ℕ → ordinal) (n : ℕ) :
  (add_iterate n) ∈ well_formed 0 Ψ :=
begin
  have h := zero_well_formed 0 Ψ,
  induction n with n hn,
  { exact h },
  { rw add_iterate_succ, exact add_well_formed 0 Ψ h hn }
end

end buchholz_exp'

/-- The type of well-formed Buchholz expressions. This corresponds to `C` in Buchholz's original
definition. -/
def buchholz_exp {o : ordinal} (v : ℕ) (Ψ : Π a, a < o → ℕ → ordinal) : Type 0 :=
buchholz_exp'.well_formed v Ψ

namespace buchholz_exp

/-- A well-formed Buchholz expression from an ordinal less than `Ωᵥ`. -/
def lt_Omega' {o : ordinal} {v : ℕ} (Ψ : Π a, a < o → ℕ → ordinal) (a : (Omega v).ord.out.α) :
  buchholz_exp v Ψ :=
⟨_, buchholz_exp'.lt_Omega'_well_formed v Ψ a⟩

/-- A well-formed Buchholz expression from an ordinal less than `Ωᵥ`. -/
def lt_Omega {o : ordinal} {v : ℕ} {a : ordinal} (ha : a < (Omega v).ord)
  (Ψ : Π a, a < o → ℕ → ordinal) : buchholz_exp v Ψ :=
⟨_, buchholz_exp'.lt_Omega_well_formed v Ψ ha⟩

theorem lt_Omega'.inj {o : ordinal} (v : ℕ) (Ψ : Π a, a < o → ℕ → ordinal) :
  function.injective (@lt_Omega' o v Ψ) :=
λ a b h, buchholz_exp'.lt_Omega'.inj (subtype.mk.inj h)

/-- The value of a well-formed Buchholz expression when interpreted as an ordinal. -/
def value {o : ordinal} {v : ℕ} {Ψ : Π a, a < o → ℕ → ordinal} (a : buchholz_exp v Ψ) : ordinal :=
a.val.value Ψ

theorem lt_Omega_value {o : ordinal} {v : ℕ} (Ψ : Π a, a < o → ℕ → ordinal) {a : ordinal}
  (ha : a < (Omega v).ord) : (lt_Omega ha Ψ).value = a :=
buchholz_exp'.lt_Omega_value Ψ ha

theorem zero_value {o : ordinal} (ho : o = 0) {v : ℕ} (Ψ : Π a, a < o → ℕ → ordinal)
  (e : buchholz_exp v Ψ) : e.value < (Omega v).ord :=
buchholz_exp'.zero_value ho Ψ _

/-- An auxiliary definition which gives a denumerable family of Buchholz expressions. -/
def add_iterate {o : ordinal} (Ψ : Π a, a < o → ℕ → ordinal) (n : ℕ) : buchholz_exp 0 Ψ :=
⟨_, buchholz_exp'.add_iterate_well_formed Ψ n⟩

theorem add_iterate.inj {o : ordinal} (Ψ : Π a, a < o → ℕ → ordinal) :
  function.injective (add_iterate Ψ) :=
λ a b h, buchholz_exp'.add_iterate.inj (subtype.mk.inj h)

theorem card_eq_aleph {o : ordinal} {v : ℕ} (Ψ : Π a, a < o → ℕ → ordinal) :
  mk (buchholz_exp v Ψ) = cardinal.aleph v :=
begin
  apply le_antisymm,
  { rw ←buchholz_exp'.card_eq_aleph,
    exact mk_le_of_injective (λ a b h, subtype.ext_val h) },
  { induction v with v hv,
    { convert cardinal.mk_le_of_injective (add_iterate.inj Ψ), simp },
    { convert cardinal.mk_le_of_injective (lt_Omega'.inj (v + 1) Ψ),
      exact (cardinal.mk_ord_out _).symm } }
end

end buchholz_exp

/-- Buchholz's `Ψ` function. -/
def buchholz : ordinal → ℕ → ordinal.{0} :=
wf.fix $ λ o Ψ v, mex (@buchholz_exp.value o v Ψ)

theorem buchholz_def' : Π o, buchholz o = λ v, mex (@buchholz_exp.value o v (λ a _, buchholz a)) :=
wf.fix_eq _

theorem buchholz_def (o : ordinal) (v : ℕ) :
  buchholz o v = mex (@buchholz_exp.value o v (λ a _, buchholz a)) :=
by rw buchholz_def'

theorem buchholz_zero (v : ℕ) : buchholz 0 v = (Omega v).ord :=
begin
  rw buchholz_def,
  apply le_antisymm ((mex_le_lsub _).trans (lsub_le.2 (buchholz_exp.zero_value rfl _))),
  by_contra' h,
  -- this doesn't work since it uses `lsub` instead of `mex`.
  -- have h' : (buchholz_exp.lt_Omega h _).value < lsub buchholz_exp.value := lt_lsub _ _,
  -- rw buchholz_exp.low_value h _ at h',
  -- exact lt_irrefl _ h'
  sorry
end

-- Buchholz is additive principal

theorem buchholz_lt_Omega (o : ordinal) (v : ℕ) : buchholz o v < (Omega (v + 1)).ord :=
begin
  rw buchholz_def,
  convert mex_lt_card_succ.{0 0} buchholz_exp.value,
  rw [buchholz_exp.card_eq_aleph, ←aleph_succ],
  refl
end

end ordinal
