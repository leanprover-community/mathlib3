import combinatorics.hales_jewett
import group_theory.submonoid
import combinatorics.pigeonhole
import data.fintype.sort
import data.finsupp

open_locale big_operators classical
noncomputable theory

def order_emb_of_card_le {α β} [fintype α] [linear_order α] [fintype β] [linear_order β]
  (h : fintype.card α ≤ fintype.card β) : α ↪o β :=
(mono_equiv_of_fin α rfl).symm.to_rel_embedding.trans
    ((fin.cast_le h).trans $ mono_equiv_of_fin β rfl)

variables {α β M : Type*} [add_comm_monoid M] (i : α ↪ β) (v : α → M)

def extend_by_zero (b : β) : M := if h : ∃ a, i a = b then v h.some else 0

lemma extend_by_zero_apply (a : α) : extend_by_zero i v (i a) = v a :=
begin
  rw extend_by_zero,
  split_ifs,
  { congr, apply i.injective, exact h.some_spec, },
  { exfalso, apply h, exact ⟨a, rfl⟩, }
end

lemma extend_by_zero_eq_zero (b : β) (h : ¬ ∃ a, i a = b) : extend_by_zero i v b = 0 :=
by rw [extend_by_zero, dif_neg h]

end

variables {R : Type} [semiring R] (A : submonoid R)

structure MPC :=
(m : Type)
(fintype : fintype m)
(linear_order : linear_order m)
(p : set R)
(p_finite : p.finite)
(zero_mem : (0 : R) ∈ p)
(C : A)

variable {A}

attribute [instance] MPC.fintype MPC.linear_order

instance : inhabited (MPC A) := ⟨mk_MPC (default _) (fin 0)⟩

variables (mpc : MPC A)

section

variable (mpc' : MPC A)

structure MPC.inclusion : Type :=
(to_fun : mpc.m ↪o mpc'.m)
(scale : R)
(p_sub_scaling : ∀ r ∈ mpc.p, r * scale ∈ mpc'.p)
(C_scale : (mpc.C : R) * scale = mpc'.C)

end

structure MPC.comb (i : with_top mpc.m) :=
(to_fun : mpc.m → R)
(mem_p : ∀ j, to_fun j ∈ mpc.p)
(eq_C : ∀ j : mpc.m, i = some j → to_fun j = mpc.C)
(eq_zero : ∀ j : mpc.m, i < j → to_fun j = 0)

instance (i) : has_coe_to_fun (mpc.comb i) (λ _, mpc.m → R) :=
{ coe := λ d, d.to_fun }

def MPC.vec : Type := mpc.m → M

section

variables {M mpc} {mpc' : MPC A} (inc : mpc.inclusion mpc') (x : mpc.vec M) (x' : mpc'.vec M)

def MPC.vec.fun (i) (d : mpc.comb i) : M := ∑ j, d j • x j
def MPC.vec.row (i) : set M := set.range (x.fun i)
def MPC.vec.set : set M := ⋃ i, x.row (some i)

structure MPC.vec.inclusion : Type :=
(to_fun : mpc.m ↪o mpc'.m)
(row_sub : ∀ i, x.row i ⊆ x'.row (i.map to_fun))

def MPC.inclusion.map_vec : mpc.vec M :=
λ i, inc.scale • x' (inc.to_fun i)

def MPC.inclusion.inc : (inc.map_vec x').inclusion x' :=
{ to_fun := inc.to_fun,
  row_sub :=
    begin
      intros i m hm,
      rw [MPC.vec.row, set.mem_range] at *,
      obtain ⟨d, hm⟩ := hm,
      refine ⟨⟨extend_by_zero inc.to_fun.to_embedding (λ i, d.to_fun i * inc.scale), _,_, _⟩, _⟩,
      { intro j',
        by_cases h : ∃ j, inc.to_fun.to_embedding j = j',
        { rcases h with ⟨j, rfl⟩,
          rw extend_by_zero_apply,
          apply inclusion.p_sub_scaling,
          apply d.mem_p, },
        { rw extend_by_zero_eq_zero _ _ _ h, apply mpc'.zero_mem, } },
      { cases i,
        { rintros _ ⟨⟩, },
        simp_rw [option.map_some', (option.some_injective _).eq_iff],
        rintros _ ⟨⟩,
        erw extend_by_zero_apply,
        rw [d.eq_C _ rfl, inc.C_scale], },
      { intro j',
        by_cases h : ∃ j, inc.to_fun.to_embedding j = j',
        { rcases h with ⟨j, rfl⟩,
          rw extend_by_zero_apply,
          intro ij,
          rw d.eq_zero j,
          { apply zero_mul, },

        }
      }
    end }

end

theorem deuber (κ : Type) [fintype κ] :
  ∃ mpc' : MPC A,
    ∀ (x' : mpc'.vec M) (coloring : M → κ),
      ∃ (x : mpc.vec M) (k : κ) (inc : x.inclusion x'), x.set ⊆ coloring ⁻¹' {k} :=
begin
  suffices : ∀ r : ℕ, ∃ mpc' : MPC A, ∀ (x' : mpc'.vec M) (coloring : M → κ),
    ∃ (x : (mk_MPC mpc.to_PC (fin r)).vec M) (k : fin r → κ) (inc : x.inclusion x'),
      ∀ i : fin r, x.row (some i) ⊆ coloring ⁻¹' {k i},
  { let r := fintype.card κ * fintype.card mpc.m,
    refine Exists.imp (λ mpc', forall_imp $ λ x', _) (this r),
    refine forall_imp (λ coloring, _),
    clear this,
    rintros ⟨x₀, k₀, inc, h_col⟩,
    haveI : nonempty κ := nonempty.map coloring infer_instance,
    obtain ⟨k, hk : fintype.card mpc.m ≤ _⟩ := fintype.exists_le_card_fiber_of_mul_le_card k₀ _,
    work_on_goal 1 { simp only [fintype.card_fin] },

  }
end

/-
theorem deuber (κ : Type) [fintype κ] :
  ∃ mpc' : MPC A, ∀ x' (coloring : M → κ), ∃ x k,
    mpc.set x ⊆ mpc'.set x' ∩ coloring ⁻¹' {k} :=
begin
  suffices : ∀ r : ℕ, ∃ mpc' : MPC A, ∀ x' (coloring : M → κ), ∃ x (k : fin r → κ),
    { m := r, ..mpc}.set x ⊆ mpc'.set x' ∧
      ∀ i, { m := r, ..mpc}.line x i ⊆ coloring ⁻¹' {k i},
  { let m' := fintype.card κ * mpc.m,
    refine Exists.imp (λ mpc', forall_imp $ λ x', _) (this m'),
    refine forall_imp (λ coloring, _),
    clear this,
    rintros ⟨x₀, k₀, h_sub, h_col⟩,
    haveI : nonempty κ := nonempty.map coloring infer_instance,
    obtain ⟨k, hk : mpc.m ≤ _⟩ := fintype.exists_le_card_fiber_of_mul_le_card k₀ _,
    work_on_goal 1 { simp only [fintype.card_fin], },
    let fs := finset.univ.filter (λ x, k₀ x = k),
    let bla : fin mpc.m ↪o _ := (fin.cast_le hk).trans (fs.order_emb_of_fin rfl),
    refine ⟨x₀ ∘ bla, k, _⟩,
    intros r hr,
    rw [MPC.set, set.mem_Union] at hr,
    rcases hr with ⟨i, d, hr⟩,
    let mpc'' : MPC A := { m := m', ..mpc },
    suffices : r ∈ mpc''.line x₀ (bla i),
    { refine ⟨h_sub $ set.mem_Union.mpr ⟨_, this⟩, _⟩,
      convert h_col _ this,
      suffices fafa : bla i ∈ fs,
      { rw finset.mem_filter at fafa, exact fafa.2.symm, },
      apply fs.order_emb_of_fin_mem rfl, },
    set d' : fin mpc''.m → mpc''.p :=
      λ j, if h : j ∈ bla '' { j' | j' < i }
      then d h.some
      else ⟨0, mpc''.zero_mem⟩ with hd',
    use d',
    rw [←hr, MPC.fun, MPC.fun],
    congr' 1,
    have : ∑ j in finset.univ.filter (< i), (d j : R) • (x₀ ∘ bla) j =
      ∑ j in finset.univ.filter (< i), (λ j', (d' j' : R) • x₀ j') (bla.to_embedding j),
    { apply finset.sum_congr rfl, intros j hj, congr, rw hd', dsimp, split_ifs,
      { congr, apply bla.injective, exact h.some_spec.2.symm, },
      { exfalso, apply h, refine ⟨_, _, rfl⟩, rw finset.mem_filter at hj, exact hj.2 }, },
    rw this, clear this,
    rw ←finset.sum_map,
    symmetry,
    apply finset.sum_subset,
    { intros j hj, simp only [true_and, finset.mem_univ, finset.mem_filter],
      simp only [true_and, exists_prop, finset.mem_univ, finset.mem_map, finset.mem_filter] at hj,
      rcases hj with ⟨j, hj, rfl⟩,
      exact bla.lt_iff_lt.mpr hj, },
    { intros j hj nmem,
      rw hd',
      dsimp only,
      rw dif_neg,
      { apply zero_smul },
      rintros ⟨j, hj', rfl⟩,
      apply nmem,
      rw finset.mem_map,
      refine ⟨j, _, rfl⟩,
      rw finset.mem_filter,
      refine ⟨finset.mem_univ _, hj'⟩, }, },
  intro r,
  induction r with r ih,
  { use default _,
    intros,
    refine ⟨is_empty_elim, is_empty_elim, _, _⟩,
    { rintros m ⟨_, ⟨i, _⟩, hi⟩, exact is_empty_elim i, },
    exact is_empty_elim, },
  obtain ⟨mpc', h'⟩ := ih,
  obtain ⟨n, hn⟩ := combinatorics.extended_HJ_fin mpc.p κ (fin mpc'.m),
  refine ⟨⟨n + 1, _, _, mpc.C * mpc'.C⟩, _⟩,

end
-/
