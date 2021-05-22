import ring_theory.noetherian
import data.set.disjointed

variables (R M N : Type*) [ring R] [add_comm_group M] [module R M] (A B : submodule R M)
variables [add_comm_group N] [module R N] (C D : submodule R N)

/-- `M` as a submodule of `M × N`. -/
def submodule.fst : submodule R (M × N) := (⊥ : submodule R N).comap (linear_map.snd R M N)

@[simps] def submodule.fst_equiv : submodule.fst R M N ≃ₗ[R] M :=
{ to_fun := λ x, x.1.1,
  inv_fun := λ m, ⟨⟨m, 0⟩, by tidy⟩,
  map_add' := by simp,
  map_smul' := by simp,
  left_inv := by tidy,
  right_inv := by tidy, }

lemma submodule.fst_map_fst : (submodule.fst R M N).map (linear_map.fst R M N) = ⊤ :=
by tidy
lemma submodule.fst_map_snd : (submodule.fst R M N).map (linear_map.snd R M N) = ⊥ :=
by { tidy, exact 0, }

/-- `N` as a submodule of `M × N`. -/
def submodule.snd : submodule R (M × N) := (⊥ : submodule R M).comap (linear_map.fst R M N)

@[simps] def submodule.snd_equiv : submodule.snd R M N ≃ₗ[R] N :=
{ to_fun := λ x, x.1.2,
  inv_fun := λ n, ⟨⟨0, n⟩, by tidy⟩,
  map_add' := by simp,
  map_smul' := by simp,
  left_inv := by tidy,
  right_inv := by tidy, }

lemma submodule.snd_map_fst : (submodule.snd R M N).map (linear_map.fst R M N) = ⊥ :=
by { tidy, exact 0, }
lemma submodule.snd_map_snd : (submodule.snd R M N).map (linear_map.snd R M N) = ⊤ :=
by tidy

lemma submodule.fst_sup_snd : submodule.fst R M N ⊔ submodule.snd R M N = ⊤ :=
begin
  rw eq_top_iff,
  rintro ⟨m, n⟩ -,
  rw [show (m, n) = (m, 0) + (0, n), by simp],
  apply submodule.add_mem (submodule.fst R M N ⊔ submodule.snd R M N),
  { exact submodule.mem_sup_left (submodule.mem_comap.mpr (by simp)), },
  { exact submodule.mem_sup_right (submodule.mem_comap.mpr (by simp)), },
end

lemma submodule.fst_inf_snd : submodule.fst R M N ⊓ submodule.snd R M N = ⊥ := by tidy

open function
variables {R M N}

def g (f : M × N →ₗ[R] M) (i : injective f) (Kφ : Σ K : submodule R M, K ≃ₗ[R] M) : M × N →ₗ[R] M :=
(Kφ.1.subtype.comp Kφ.2.symm.to_linear_map).comp f

lemma g_injective (f : M × N →ₗ[R] M) (i : injective f) (Kφ : Σ K : submodule R M, K ≃ₗ[R] M) :
  injective (g f i Kφ) :=
(subtype.val_injective.comp Kφ.2.symm.injective).comp i

noncomputable theory

noncomputable def tunnel' (f : M × N →ₗ[R] M) (i : injective f) :
  ℕ → Σ (K : submodule R M), K ≃ₗ[R] M
| 0 := ⟨⊤, linear_equiv.of_top ⊤ rfl⟩
| (n+1) :=
⟨(submodule.fst R M N).map (g f i (tunnel' n)),
  ((submodule.fst R M N).equiv_map_of_injective _ (g_injective f i (tunnel' n))).symm.trans
    (submodule.fst_equiv R M N)⟩

def tunnel (f : M × N →ₗ[R] M) (i : injective f) : ℕ →ₘ order_dual (submodule R M) :=
⟨λ n, (tunnel' f i n).1, monotone_of_monotone_nat (λ n, begin dsimp [tunnel', g], rw submodule.map_comp, rw submodule.map_comp, apply submodule.map_subtype_le, end)⟩

def tailing (f : M × N →ₗ[R] M) (i : injective f) (n : ℕ) : submodule R M :=
(submodule.snd R M N).map (g f i (tunnel' f i n))

def tailing_linear_equiv (f : M × N →ₗ[R] M) (i : injective f) (n : ℕ) : tailing f i n ≃ₗ[R] N :=
((submodule.snd R M N).equiv_map_of_injective _ (g_injective f i (tunnel' f i n))).symm.trans
  (submodule.snd_equiv R M N)

lemma tailing_le_tunnel (f : M × N →ₗ[R] M) (i : injective f) (n : ℕ) :
  tailing f i n ≤ tunnel f i n :=
begin
  dsimp [tailing, g],
  rw [submodule.map_comp, submodule.map_comp],
  apply submodule.map_subtype_le,
end

-- TODO express using disjoint
lemma tailing_inf_tunnel_succ_eq_bot (f : M × N →ₗ[R] M) (i : injective f) (n : ℕ) :
  tailing f i n ⊓ tunnel f i (n+1) = ⊥ :=
begin
  dsimp [tailing, tunnel, tunnel'],
  rw [submodule.map_inf_eq_map_inf_comap, submodule.comap_map_eq_of_injective (g_injective _ _ _),
    inf_comm, submodule.fst_inf_snd, submodule.map_bot],
end

lemma tailing_sup_tunnel_succ_le_tunnel (f : M × N →ₗ[R] M) (i : injective f) (n : ℕ) :
  tailing f i n ⊔ tunnel f i (n+1) ≤ tunnel f i n :=
begin
  dsimp [tailing, tunnel, tunnel', g],
  rw [←submodule.map_sup, sup_comm, submodule.fst_sup_snd, submodule.map_comp, submodule.map_comp],
  apply submodule.map_subtype_le,
end

/-- The sequence of supremums of the first `n` elements of a sequence. -/
def partial_sups' {α : Type*} [semilattice_sup_bot α] (f : ℕ → α) : ℕ → α
| 0 := ⊥
| (n+1) := partial_sups' n ⊔ f n

/-- The monotone sequence of supremums of the first `n` elements of a sequence. -/
def partial_sups {α : Type*} [semilattice_sup_bot α] (f : ℕ → α) : ℕ →ₘ α :=
⟨partial_sups' f, monotone_of_monotone_nat (λ n, le_sup_left)⟩

lemma partial_sups_disjoint_of_disjoint {α : Type*} [bounded_distrib_lattice α]
  (f : ℕ → α) (w : pairwise (disjoint on f)) {m n : ℕ} (h : m < n) :
  disjoint (partial_sups f m) (f n) :=
begin
  induction m with m ih,
  exact disjoint_bot_left,
  dsimp [partial_sups, partial_sups'],
  rw disjoint_sup_left,
  exact ⟨ih (nat.lt_of_succ_lt h), w m n (nat.lt_of_succ_lt h).ne⟩
end

def tailings (f : M × N →ₗ[R] M) (i : injective f) : ℕ →ₘ submodule R M :=
partial_sups (tailing f i)

@[simp] lemma tailings_succ (f : M × N →ₗ[R] M) (i : injective f) (n : ℕ) :
  tailings f i (n+1) = tailings f i n ⊔ tailing f i n := rfl

variables {α : Type*}

theorem disjoint.disjoint_sup_left_of_disjoint_sup_right
  [bounded_lattice α] [is_modular_lattice α] {a b c : α}
  (h : disjoint b c) (hsup : disjoint a (b ⊔ c)) :
  disjoint (a ⊔ b) c :=
begin
  rw [disjoint.comm, sup_comm],
  apply disjoint.disjoint_sup_right_of_disjoint_sup_left,
  apply h.symm,
  rw [sup_comm, disjoint.comm] at hsup,
  exact hsup,
end

lemma tailings_inf_tunnel_eq_bot (f : M × N →ₗ[R] M) (i : injective f) (n : ℕ) :
  disjoint (tailings f i n) (tunnel f i n) :=
begin
  induction n with n ih,
  dsimp [disjoint, tailings, partial_sups, partial_sups'],
  rw bot_inf_eq,
  apply le_refl ⊥,
  simp,
  refine disjoint.disjoint_sup_left_of_disjoint_sup_right _ _,
  rw disjoint_iff,
  apply tailing_inf_tunnel_succ_eq_bot,
  apply disjoint.mono_right _ ih,
  apply tailing_sup_tunnel_succ_le_tunnel,
end

lemma tailings_inf_tailing_succ_eq_bot (f : M × N →ₗ[R] M) (i : injective f) (n : ℕ) :
  disjoint (tailings f i n) (tailing f i n) :=
disjoint.mono_right (tailing_le_tunnel f i _) (tailings_inf_tunnel_eq_bot f i _)

lemma eq_bot_of_disjoint_absorbs {α : Type*} [bounded_lattice α]
  {a b : α} (w : disjoint a b) (h : a ⊔ b = a) : b = ⊥ :=
begin
  rw disjoint_iff at w,
  rw [←w, right_eq_inf],
  rwa sup_eq_left at h,
end

/--
A sequence `f` of submodules of a noetherian module,
with `f n` disjoint from the supremum of `f 0`, ..., `f (n-1)`,
is eventually zero.
-/
lemma disjoint_partial_sups_eventually_bot [I : is_noetherian R M]
  (f : ℕ → submodule R M) (h : ∀ n, disjoint (partial_sups f n) (f n)) :
  ∃ n : ℕ, ∀ m, n ≤ m → f m = ⊥ :=
begin
  obtain ⟨n, w⟩ := monotone_stabilizes_iff_noetherian.mpr I (partial_sups f),
  exact ⟨n, (λ m p,
    eq_bot_of_disjoint_absorbs (h m) ((eq.symm (w (m + 1) (le_add_right p))).trans (w m p)))⟩
end
