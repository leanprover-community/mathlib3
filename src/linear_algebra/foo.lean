import ring_theory.noetherian
import data.set.disjointed
import linear_algebra.prod

lemma eq_bot_of_disjoint_absorbs {α : Type*} [bounded_lattice α]
  {a b : α} (w : disjoint a b) (h : a ⊔ b = a) : b = ⊥ :=
begin
  rw disjoint_iff at w,
  rw [←w, right_eq_inf],
  rwa sup_eq_left at h,
end

section
variables {α : Type*}

/-- The monotone sequence of supremums of the first `n` elements of a sequence. -/
def partial_sups [semilattice_sup_bot α] (f : ℕ → α) : ℕ →ₘ α :=
⟨nat.rec ⊥ (λ (n : ℕ) (a : α), a ⊔ f n), monotone_of_monotone_nat (λ n, le_sup_left)⟩

@[simp] lemma partial_sups_zero [semilattice_sup_bot α] (f : ℕ → α) : partial_sups f 0 = ⊥ := rfl
@[simp] lemma partial_sups_succ [semilattice_sup_bot α] (f : ℕ → α) (n : ℕ) :
  partial_sups f (n+1) = partial_sups f n ⊔ f n := rfl

lemma le_partial_sups [semilattice_sup_bot α] (f : ℕ → α) {m n : ℕ} (h : m < n) :
  f m ≤ partial_sups f n :=
begin
  induction n with n ih,
  { cases h, },
  { cases h with h h,
    { exact le_sup_right, },
    { exact (ih h).trans le_sup_left, } },
end

lemma partial_sups_le [semilattice_sup_bot α] (f : ℕ → α) (n : ℕ)
  (a : α) (w : ∀ m, m < n → f m ≤ a) : partial_sups f n ≤ a :=
begin
  induction n with n ih,
  { apply bot_le, },
  { exact sup_le (ih (λ m p, w m (nat.lt.step p))) (w n (lt_add_one n))}
end

lemma partial_sups_eq [semilattice_sup_bot α] (f : ℕ → α) (n : ℕ) :
  partial_sups f n = (finset.range n).sup f :=
begin
  induction n with n ih,
  { refl, },
  { dsimp [partial_sups] at ih ⊢,
    rw [finset.range_succ, finset.sup_insert, sup_comm, ih], },
end

-- Note this lemma requires a distributive lattice,
-- so is not useful (or true) in situations such as submodules.
lemma partial_sups_disjoint_of_disjoint [bounded_distrib_lattice α]
  (f : ℕ → α) (w : pairwise (disjoint on f)) {m n : ℕ} (h : m < n) :
  disjoint (partial_sups f m) (f n) :=
begin
  induction m with m ih,
  exact disjoint_bot_left,
  dsimp [partial_sups],
  rw disjoint_sup_left,
  exact ⟨ih (nat.lt_of_succ_lt h), w m n (nat.lt_of_succ_lt h).ne⟩
end

end

/-!
## Tunnels and tailings

Given a morphism `f : M × N →ₗ[R] M` which is `i : injective f`,
we can find an infinite decreasing `tunnel f i n` of copies of `M` inside `M`,
and sitting beside these, an infinite sequence of copies of `N`.

We picturesquely name these as `tailing f i n` for each individual copy of `N`,
and `tailings f i n` for the supremum of the first `n` copies:
they are the pieces left behind, sitting inside the tunnel.

By construction, each `tailing f i n` is disjoint from `tailings f i n`;
later, when we assume `M` is noetherian, this implies that `N` must be trivial,
and establishes the strong rank condition for any left-noetherian ring.
-/
section tunnel

-- (This doesn't work over a semiring: we need to use that `submodule R M` is a modular lattice,
-- which requires cancellation.)
variables {R : Type*} [ring R]
variables {M N : Type*} [add_comm_group M] [module R M] [add_comm_group N] [module R N]

open function

def g (f : M × N →ₗ[R] M) (i : injective f) (Kφ : Σ K : submodule R M, K ≃ₗ[R] M) : M × N →ₗ[R] M :=
(Kφ.1.subtype.comp Kφ.2.symm.to_linear_map).comp f

lemma g_injective (f : M × N →ₗ[R] M) (i : injective f) (Kφ : Σ K : submodule R M, K ≃ₗ[R] M) :
  injective (g f i Kφ) :=
(subtype.val_injective.comp Kφ.2.symm.injective).comp i

noncomputable theory

-- Even though we have `noncomputable theory`,
-- we get an error without another `noncomputable` here.
noncomputable def tunnel' (f : M × N →ₗ[R] M) (i : injective f) :
  ℕ → Σ (K : submodule R M), K ≃ₗ[R] M
| 0 := ⟨⊤, linear_equiv.of_top ⊤ rfl⟩
| (n+1) :=
⟨(submodule.fst R M N).map (g f i (tunnel' n)),
  ((submodule.fst R M N).equiv_map_of_injective _ (g_injective f i (tunnel' n))).symm.trans
    (submodule.fst_equiv R M N)⟩

def tunnel (f : M × N →ₗ[R] M) (i : injective f) : ℕ →ₘ order_dual (submodule R M) :=
⟨λ n, (tunnel' f i n).1, monotone_of_monotone_nat (λ n, begin
    dsimp [tunnel', g],
    rw [submodule.map_comp, submodule.map_comp],
    apply submodule.map_subtype_le,
  end)⟩

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

lemma tailing_disjoint_tunnel_succ (f : M × N →ₗ[R] M) (i : injective f) (n : ℕ) :
  disjoint (tailing f i n) (tunnel f i (n+1)) :=
begin
  rw disjoint_iff,
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

def tailings (f : M × N →ₗ[R] M) (i : injective f) : ℕ → submodule R M :=
partial_sups (tailing f i)

@[simp] lemma tailings_zero (f : M × N →ₗ[R] M) (i : injective f) : tailings f i 0 = ⊥ :=
rfl

@[simp] lemma tailings_succ (f : M × N →ₗ[R] M) (i : injective f) (n : ℕ) :
  tailings f i (n+1) = tailings f i n ⊔ tailing f i n :=
by simp [tailings]

lemma tailings_disjoint_tunnel (f : M × N →ₗ[R] M) (i : injective f) (n : ℕ) :
  disjoint (tailings f i n) (tunnel f i n) :=
begin
  induction n with n ih,
  { dsimp only [disjoint, tailings_zero],
    rw bot_inf_eq,
    apply le_refl ⊥, },
  { simp only [tailings_succ],
    refine disjoint.disjoint_sup_left_of_disjoint_sup_right _ _,
    apply tailing_disjoint_tunnel_succ,
    apply disjoint.mono_right _ ih,
    apply tailing_sup_tunnel_succ_le_tunnel, },
end

lemma tailings_disjoint_tailing (f : M × N →ₗ[R] M) (i : injective f) (n : ℕ) :
  disjoint (tailings f i n) (tailing f i n) :=
disjoint.mono_right (tailing_le_tunnel f i _) (tailings_disjoint_tunnel f i _)

end tunnel

open function
universes u v w

variables {R : Type u} [ring R]
variables {M : Type v} {N : Type w} [add_comm_group M] [module R M] [add_comm_group N] [module R N]

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

/--
If `M ⊕ N` embeds into `M`, for `M` noetherian over `R`, then `N` is trivial.
-/
def is_noetherian.equiv_punit_of_prod_injective [I : is_noetherian R M]
  (f : M × N →ₗ[R] M) (i : injective f) : N ≃ₗ[R] punit.{w+1} :=
begin
  apply nonempty.some,
  obtain ⟨n, w⟩ := disjoint_partial_sups_eventually_bot (tailing f i)
    (tailings_disjoint_tailing f i),
  specialize w n (le_refl n),
  apply nonempty.intro,
  refine (tailing_linear_equiv f i n).symm.trans _,
  rw w,
  exact submodule.submodule.bot_equiv_punit,
end
